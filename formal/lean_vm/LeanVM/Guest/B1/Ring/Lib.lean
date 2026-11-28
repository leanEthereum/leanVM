/-
  LeanVM.Guest.B1.Ring.Lib

  The ring switch's proofs' generic lemmas: statement lists without `ret`, and a `mul_range` loop.
-/

module

public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Atoms

/-!
# Generic lemmas of the ring switch's proofs

`ringNoRetList_append`, `ringNoRetList_flatten_map`: lists of statements without `ret`;
`ringLoop_sound`: a `mul_range` loop's body holds at every step. (`main`'s `KeccakGkr/Lib.lean` holds the
same lemmas, which the Keccak GKR's stream restores.)
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-! ## Statement lists without `ret` -/

theorem ringNoRetList_append : ∀ (a b : List Stmt),
    Stmt.noRetList (a ++ b) = (Stmt.noRetList a && Stmt.noRetList b)
  | [], b => by simp [Stmt.noRetList]
  | s :: a, b => by
    simp only [List.cons_append, Stmt.noRetList, ringNoRetList_append a b, Bool.and_assoc]

theorem ringNoRetList_flatten_map (f : ℕ → List Stmt) (h : ∀ i, Stmt.noRetList (f i) = true) :
    ∀ l : List ℕ, Stmt.noRetList (l.map f).flatten = true
  | [] => rfl
  | i :: l => by
    rw [List.map_cons, List.flatten_cons, ringNoRetList_append, h i, ringNoRetList_flatten_map f h l]; rfl

/-! ## Loops -/

/-- **A `mul_range` loop, soundness**: if the helper's relation at depth `d + 1` at `x` gives the
body's meaning `B x` and, when `x·g ≠ N`, the call at `x·g` one level shallower, then from `g^k`
to `N = g^m` (`m` below the order of `g`) the body holds at every `g^j`, `k ≤ j < m`. -/
theorem ringLoop_sound {P : Core.Program} {f : String} {ps : List E} {N : E} {B : E → Prop} {m : ℕ}
    (hstep : ∀ d x, P.relN rd (d + 1) f (x :: ps) [] →
      B x ∧ (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: ps) []))
    (hN : N = gen ^ m) (hm : m < ordG) :
    ∀ k, P.Rel rd f (gen ^ k :: ps) [] → ∀ j, k ≤ j → j < m → B (gen ^ j) := by
  rintro k ⟨d, hd⟩
  induction d generalizing k with
  | zero => exact hd.elim
  | succ d ih =>
    obtain ⟨hB, hnext⟩ := hstep d _ hd
    intro j hkj hjm
    rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
    · exact hB
    · have hne : gen ^ k * gen + N ≠ 0 := by
        intro h0
        rw [gen_pow_add_eq_zero_iff, hN] at h0
        have := gen_pow_inj hm (by unfold ordG at hm; omega) h0
        omega
      have := hnext hne
      rw [gen_pow_mul_gen] at this
      exact ih (k + 1) this j hlt hjm

end
end LeanVM.Guest.B1.VerifySub
