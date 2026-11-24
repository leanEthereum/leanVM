/-
  LeanVM.Guest.B1.Terminal.KidsDepB

  `KidsDep`'s lifts within a bound (`CompleteAtB`): dependent callees, each within its bound, and a
  flat function with them within its frame, its buffers and its callees' bounds.
-/

module

public import LeanVM.Guest.B1.Terminal.KidsDep

/-!
# Dependent callees, placed, within a bound

`KidsDepB fs cert κ ks Bs`: callee `j` (a function of the results before it, `KidD`) has the bound
`Bs[j]`, on every result before it: entered, it is `CompleteAtB` within `Bs[j]`; skipped, its tail frame
`fs (tailKey f)` is at most `Bs[j]`. The callees then take at most `Bs.sum` words, and a
flat function with them at most `fs f + sizes.sum + Bs.sum`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **The dependent callees within their bounds**: callee `j`, on every result before it, entered
within `Bs[j]` words (`CompleteAtB`), skipped with its tail frame at most `Bs[j]`; one bound per
callee. -/
def KidsDepB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) : List KidD → List ℕ → Prop
  | k :: ks, b :: Bs => (∀ pv, ((k pv).taken = true →
        CompleteAtB fs cert κ (k pv).f (k pv).Lin (k pv).args (k pv).Out b) ∧
      ((k pv).taken = false → fs (tailKey (k pv).f) ≤ b)) ∧ KidsDepB fs cert κ ks Bs
  | [], [] => True
  | _, _ => False

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem KidsDepB.append {κ : ℕ} : ∀ {ks ks' : List KidD} {Bs Bs' : List ℕ},
    KidsDepB fs cert κ ks Bs → KidsDepB fs cert κ ks' Bs' → KidsDepB fs cert κ (ks ++ ks') (Bs ++ Bs')
  | [], _, [], _, _, h' => h'
  | _ :: _, _, _ :: _, _, ⟨h, hs⟩, h' => ⟨h, KidsDepB.append hs h'⟩
  | [], _, _ :: _, _, h, _ => by simp [KidsDepB] at h
  | _ :: _, _, [], _, h, _ => by simp [KidsDepB] at h

/-- **Callees with one bound `b`.** -/
theorem kidsDepB_replicate {κ : ℕ} {b : ℕ} : ∀ {ks : List KidD},
    (∀ k ∈ ks, ∀ pv, ((k pv).taken = true →
        CompleteAtB fs cert κ (k pv).f (k pv).Lin (k pv).args (k pv).Out b) ∧
      ((k pv).taken = false → fs (tailKey (k pv).f) ≤ b)) →
    KidsDepB fs cert κ ks (List.replicate ks.length b)
  | [], _ => trivial
  | k :: _, h => ⟨h k List.mem_cons_self, kidsDepB_replicate fun k' hk' => h k' (List.mem_cons_of_mem _ hk')⟩

theorem KidsDepB.length {κ : ℕ} : ∀ {ks : List KidD} {Bs : List ℕ}, KidsDepB fs cert κ ks Bs →
    ks.length = Bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, hs⟩ => by simp [hs.length]
  | [], _ :: _, h => by simp [KidsDepB] at h
  | _ :: _, [], h => by simp [KidsDepB] at h

end
end LeanVM.Guest.B1
