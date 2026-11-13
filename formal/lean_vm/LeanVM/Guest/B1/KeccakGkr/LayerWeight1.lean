/-
  LeanVM.Guest.B1.KeccakGkr.LayerWeight1

  The first claim's weight at the local point in `keccak_layer` (G:2769-2776): a lane table times
  the bits of a word.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT

/-!
# The first claim's weight

`lanesEqT_holds`: the statements compute `(Σ_lane f[lane]·lanes[lane])·Π_t (1 + l_t (1 + g^(2^t)))`
from the lane weights `f` and the local point `l`; with `firstWeight_eq` (`Algebra`) that is the
claim's weights (`firstWeights`) against the equality weights of the local point.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem word_bitc {t : ℕ} (ht : t < 6) : word (2 ^ (2 ^ t) + 1) 0 = 1 + gen ^ 2 ^ t := by
  rw [word_eOfNat, show 2 ^ (2 ^ t) + 1 = 2 ^ (2 ^ t) ^^^ 1 by interval_cases t <;> decide,
    eOfNat_xor, eOfNat_one, ← word_eOfNat, word_two_pow (by interval_cases t <;> decide), add_comm]

/-- **The first claim's weight** (G:2769-2776). -/
theorem lanesEqT_holds {lp loc : V} {f : ℕ → ℕ} {B : ℕ} {fl lanes locPt : List E}
    (hfl : ∀ i < 25, σ (.n (f i)) = eqAt fl i) (hlanes : ReadsAt rd (σ lp) lanes)
    (hlen : lanes.length = 25) (hloc : ReadsAt rd (σ loc) locPt) (hlocL : locPt.length = 11)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (lanesEqT lp loc f B) next kret) :
    σ (.n (B + 109)) = (∑ l ∈ range 25, eqAt fl l * lanes.getD l 0) *
      ((List.range 6).map fun t ↦ 1 + (locPt.take 6).getD t 0 * (1 + gen ^ 2 ^ t)).prod ∧ next := by
  rw [lanesEqT, holdsList_append, holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨l0, m0, h⟩ := h
  rw [holdsList_range_flatten _ _ (fun _ ↦ rfl), holdsList_range_flatten _ _ (fun _ ↦ rfl)] at h
  obtain ⟨hL, hT, hn⟩ := h
  have lane : ∀ i < 25, ∀ {v : E}, LoadHolds rd (σ lp) i v → v = lanes.getD i 0 := by
    intro i hi v hv
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact loadHolds_unique hv (hlanes i (by omega))
  have acc : ∀ i ≤ 24, σ (.n (B + 1 + 3 * i)) =
      ∑ l ∈ range (i + 1), eqAt fl l * lanes.getD l 0 := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add, Finset.sum_range_one]
      rw [m0, hfl 0 (by omega), lane 0 (by omega) l0]
    | succ i ih =>
      intro hi
      have hs := hL i (by omega)
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
      obtain ⟨li, mi, ai⟩ := hs
      rw [show B + 1 + 3 * (i + 1) = B + 4 + 3 * i by omega, ai, mi, ih (by omega),
        hfl (i + 1) (by omega), lane (i + 1) (by omega) li, Finset.sum_range_succ _ (i + 1)]
  have hloc6 : ∀ t < 6, ∀ {v : E}, LoadHolds rd (σ loc) t v → v = (locPt.take 6).getD t 0 := by
    intro t ht v hv
    rw [List.getD_eq_getElem _ _ (by simp [hlocL]; omega), List.getElem_take]
    exact loadHolds_unique hv (hloc t (by omega))
  have prod : ∀ t ≤ 6, σ (.n (B + 73 + 6 * t)) = (∑ l ∈ range 25, eqAt fl l * lanes.getD l 0) *
      ((List.range t).map fun t ↦ 1 + (locPt.take 6).getD t 0 * (1 + gen ^ 2 ^ t)).prod := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [show B + 73 + 6 * 0 = B + 1 + 3 * 24 by omega, acc 24 le_rfl]
      simp
    | succ t ih =>
      intro ht
      have hs := hT t (by omega)
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hs
      obtain ⟨c1, lt, cw, mt, at', pt⟩ := hs
      rw [show B + 73 + 6 * (t + 1) = B + 79 + 6 * t by omega, pt, at', mt, cw, c1, ih (by omega),
        word_one, word_bitc (by omega), hloc6 t (by omega) lt, List.range_succ, List.map_append,
        List.prod_append]
      simp [mul_assoc]
  refine ⟨?_, hn⟩
  rw [show B + 109 = B + 73 + 6 * 6 by omega, prod 6 le_rfl]

end
end LeanVM.Guest.B1.VerifySub
