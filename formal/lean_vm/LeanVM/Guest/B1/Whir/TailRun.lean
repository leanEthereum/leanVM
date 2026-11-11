/-
  LeanVM.Guest.B1.Whir.TailRun

  The closing sumcheck over the final lane's low part, as `opening_tail_round` runs it round by
  round.
-/

module

public import LeanVM.Guest.B1.Fs.TailRound
public import LeanVM.Guest.B1.Sumcheck.Run

/-!
# The closing rounds (G:1724-1732)

`tailRun pairs cap claim`: round by round, the two words `c0, c2` absorbed on the capacity, the
challenge `r` squeezed, the claim `c0 + r (claim + (1 + r) c2)` (`opening_tail_round`'s);
the challenges, the final claim and the capacity left. `sumcheck_tail_run`: `sumcheck claim 3`
over `n` plain rounds runs it. `tailRun_add`: the claim enters linearly, with the factor the
product of the challenges.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The closing rounds on the words `pairs`, from the capacity `cap` and the claim: the
challenges, the final claim, the capacity left. -/
def tailRun : List (E × E) → List E → E → List E × E × List E
  | [], cap, claim => ([], claim, cap)
  | (c0, c2) :: rest, cap, claim =>
    let s := (⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve
    let t := tailRun rest s.squeeze.2.cap (c0 + s.squeeze.1 * (claim + (1 + s.squeeze.1) * c2))
    (s.squeeze.1 :: t.1, t.2.1, t.2.2)

/-- The words of the closing rounds. -/
def tailWords (pairs : List (E × E)) : List E := pairs.flatMap fun p ↦ [p.1, p.2]

/-- **`sumcheck claim 3` over plain rounds runs the closing rounds.** -/
theorem sumcheck_tail_run : ∀ (pairs : List (E × E)) (cap : List E) (claim : E),
    RunsTo (sumcheck claim 3 (List.replicate pairs.length none)) ⟨cap, []⟩ (tailWords pairs)
      ((tailRun pairs cap claim).1, (tailRun pairs cap claim).2.1)
      ⟨(tailRun pairs cap claim).2.2, []⟩
  | [], cap, claim => runsTo_sumcheck_nil _ _ _
  | (c0, c2) :: rest, cap, claim => by
    have ih := sumcheck_tail_run rest
      ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.2.cap
      (c0 + ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1 *
        (claim + (1 + ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1) * c2))
    have h := runsTo_sumcheck_cons (runsTo_roundPolyNone ⟨cap, []⟩ claim c0 [c2] 3 rfl (by decide))
      (s1 := ((⟨cap, []⟩ : Fs).absorb c0 dsObserve).absorbAll [c2] dsObserve)
      (by
        rw [← tail_eval]
        exact ih)
    exact h

/-- **The claim enters the closing rounds linearly**, with the factor the product of their
challenges. -/
theorem tailRun_add : ∀ (pairs : List (E × E)) (cap : List E) (claim D : E),
    (tailRun pairs cap (claim + D)).2.1 = (tailRun pairs cap claim).2.1 +
      (tailRun pairs cap claim).1.prod * D ∧
      (tailRun pairs cap (claim + D)).1 = (tailRun pairs cap claim).1 ∧
      (tailRun pairs cap (claim + D)).2.2 = (tailRun pairs cap claim).2.2
  | [], _, _, _ => by simp [tailRun]
  | (c0, c2) :: rest, cap, claim, D => by
    set r := ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.1
    have e : c0 + r * (claim + D + (1 + r) * c2) = c0 + r * (claim + (1 + r) * c2) + r * D := by ring
    obtain ⟨h1, h2, h3⟩ := tailRun_add rest
      ((⟨cap, []⟩ : Fs).absorbAll [c0, c2] dsObserve).squeeze.2.cap
      (c0 + r * (claim + (1 + r) * c2)) (r * D)
    simp only [tailRun, List.prod_cons]
    rw [e, h1, h2, h3]
    refine ⟨by ring, rfl, rfl⟩

end
end LeanVM.Guest.B1.Whir
