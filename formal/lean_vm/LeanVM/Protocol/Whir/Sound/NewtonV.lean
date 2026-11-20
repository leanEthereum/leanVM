/-
  LeanVM.Protocol.Whir.Sound.NewtonV

  One-error near-tuple decoding over values.
-/

module

public import LeanVM.Protocol.Whir.Sound.NewtonDecoder
public import LeanVM.Protocol.Whir.Sound.DescentV

/-!
# One-error decoding over values

`newtonDecV`: `newtonDec`, each decoded lane evaluated on the domain from its Newton form
(`Newton.nEval`), the tuple kept if it disagrees with the word on at most one column of `S`; its
degree needs no check, one-error decoding returns degree at most `d` (`natDegree_decode1`). It is
`newtonDec`, evaluated (`newtonDecV_eq`), so a decoder over values (`newtonValsDecoder`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters Polynomial Newton

@[expose] public section

variable {n m : ℕ}

theorem decode1_len {d : ℕ} {pts : List (E × E)} {f : List E × List E}
    (h : decode1 d pts = some f) : f.1.length = f.2.length := by
  unfold decode1 at h
  simp only at h
  split_ifs at h <;> rw [Option.some.injEq] at h <;> subst h <;>
    · obtain ⟨h1, h2⟩ := nForm_fst (F := E) _
      rw [h1, h2, List.length_map]

/-- **One-error decoding over values.** -/
def newtonDecV (dom : Fin n ↪ E) (d : ℕ) (Q : (Fin (m + 1) → Bool) → Fin n → E)
    (S : Finset (Fin n)) : Option ((Fin (m + 1) → Bool) → Fin n → E) :=
  if d + 3 ≤ S.card then
    if h : ∀ v, (decode1 d (winPts dom d Q S v)).isSome then
      if (S.filter fun x ↦ ∃ v, nEval ((decode1 d (winPts dom d Q S v)).get (h v)).1
          ((decode1 d (winPts dom d Q S v)).get (h v)).2 (dom x) ≠ Q v x).card ≤ 1 then
        some fun v x ↦ nEval ((decode1 d (winPts dom d Q S v)).get (h v)).1
          ((decode1 d (winPts dom d Q S v)).get (h v)).2 (dom x)
      else none
    else none
  else none

theorem newtonDecV_eq (dom : Fin n ↪ E) (d : ℕ) (Q : (Fin (m + 1) → Bool) → Fin n → E)
    (S : Finset (Fin n)) : newtonDecV dom d Q S = (newtonDec dom d Q S).map (valsT dom) := by
  unfold newtonDecV newtonDec
  by_cases hS : d + 3 ≤ S.card
  · rw [ite_eq_left hS, ite_eq_left hS]
    by_cases h : ∀ v, (decode1 d (winPts dom d Q S v)).isSome
    · rw [dite_eq_left h, dite_eq_left h]
      have hev : ∀ v x, nEval ((decode1 d (winPts dom d Q S v)).get (h v)).1
          ((decode1 d (winPts dom d Q S v)).get (h v)).2 (dom x) =
          (nP ((decode1 d (winPts dom d Q S v)).get (h v)).1
            ((decode1 d (winPts dom d Q S v)).get (h v)).2).eval (dom x) := fun v x ↦
        (nEval_eq _ _ _ (by rw [decode1_len (Option.some_get (h v)).symm]; omega)).symm
      simp only [hev]
      have hdeg : DegLE d fun v ↦ nP ((decode1 d (winPts dom d Q S v)).get (h v)).1
          ((decode1 d (winPts dom d Q S v)).get (h v)).2 := fun v ↦
        natDegree_decode1 (by rw [winPts, List.length_map, length_window hS])
          (Option.some_get (h v)).symm
      by_cases hc : (S.filter fun x ↦ ∃ v, (nP ((decode1 d (winPts dom d Q S v)).get (h v)).1
          ((decode1 d (winPts dom d Q S v)).get (h v)).2).eval (dom x) ≠ Q v x).card ≤ 1
      · rw [ite_eq_left hc, ite_eq_left ⟨hdeg, hc⟩]
        rfl
      · rw [ite_eq_right hc, ite_eq_right fun hn ↦ hc hn.2]
        rfl
    · rw [dite_eq_right h, dite_eq_right h]
      rfl
  · rw [ite_eq_right hS, ite_eq_right hS]
    rfl

/-- **One-error decoding over values**, a decoder over values. -/
def newtonValsDecoder : ValsDecoder newtonNearDecoder := ⟨newtonDecV, newtonDecV_eq⟩

end
end LeanVM.Protocol.Whir.Sound
