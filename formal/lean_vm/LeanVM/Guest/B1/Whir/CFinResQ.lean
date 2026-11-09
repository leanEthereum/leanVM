/-
  LeanVM.Guest.B1.Whir.CFinResQ

  The inline `residual_query`, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFinBases
public import LeanVM.Guest.B1.Whir.ResQuery

/-!
# The inline `residual_query`, honestly

`osResQ_complete`: the coordinates `t ..` of the product `Π (d_t + chain_t)`, the chain stepped by
the vanishing values. `osResQuery_complete`: the whole product from the position.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- One coordinate's values: the vanishing value, the chain stepped, the row's word, the factor,
the product. -/
def resQVals (vals : List E) (p : E) (D : ℕ → E) (t : ℕ) (pe : E) : List E :=
  let v := vals.getD (t - 1) 0
  let c := residualChain vals p (t - 1)
  [v, c + v, c * (c + v), D t, D t + c * (c + v), pe * (D t + c * (c + v))]

/-- The values of the coordinates `t ..`. -/
def resQF (vals : List E) (p : E) (D : ℕ → E) : ℕ → ℕ → ℕ → Val → ℕ → E
  | 0, _, _, _ => fun _ ↦ 0
  | n + 1, t, k, σ =>
    seqF σ k (k + 6) (fun j ↦ (resQVals vals p D t (σ (.n (k - 1)))).getD (j - k) 0)
      fun σ1 ↦ resQF vals p D n (t + 1) (k + 6) σ1

theorem osResQ_k (pos bd row vo : ℕ) : ∀ (n t pe k : ℕ),
    (osResQ pos bd row vo n t pe k).2.2 = k + 6 * n ∧
      (n = 0 → (osResQ pos bd row vo n t pe k).2.1 = pe) ∧
      (0 < n → (osResQ pos bd row vo n t pe k).2.1 = k + 6 * n - 1)
  | 0, _, _, _ => ⟨by simp [osResQ], fun _ ↦ rfl, fun h ↦ absurd h (by omega)⟩
  | n + 1, t, pe, k => by
    have := osResQ_k pos bd row vo n (t + 1) (k + 5) (k + 6)
    simp only [osResQ]
    refine ⟨by rw [this.1]; ring, fun h ↦ absurd h (by omega), fun _ ↦ ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [this.2.1 rfl]; omega
    · rw [this.2.2 hn]; omega

/-- **The coordinates `t ..` of the product, honestly**: from the chain at `t - 1` and the
product at `t` (the value just before `k`). -/
theorem osResQ_complete {pos bd row vo L : ℕ} {D : ℕ → E} : ∀ (n t k : ℕ) (σ : Val),
    1 ≤ t → t + n ≤ L → 6 ≤ k → pos < k → bd < k →
    σ (.n (if t = 1 then pos else k - 4)) = residualChain (osVals vo L) (σ (.n pos)) (t - 1) →
    σ (.n (k - 1)) = residualProd (osVals vo L) (σ (.n pos)) D t →
    (∀ s, t ≤ s → s < t + n → LoadHolds rd (σ (.n bd)) (row + s) (D s)) →
    BlkF C rd σ k (osResQ pos bd row vo n t (k - 1) k).2.2
      (resQF (osVals vo L) (σ (.n pos)) D n t k σ) (osResQ pos bd row vo n t (k - 1) k).1
      (fun σ' ↦ σ' (.n (osResQ pos bd row vo n t (k - 1) k).2.1) =
        residualProd (osVals vo L) (σ (.n pos)) D (t + n) ∧ AgreeBelow k σ σ')
  | 0, t, k, σ, _, _, hk, _, _, _, hpe, _ => by
    simp only [osResQ, resQF]
    exact BlkF.nil fun σ' ha ↦ ⟨by rw [ha _ (by omega), hpe, Nat.add_zero], ha⟩
  | n + 1, t, k, σ, ht, hL, hk, hpos, hbd, hch, hpe, hD => by
    set vals := osVals vo L with hvals
    set v := vals.getD (t - 1) 0 with hv
    set c := residualChain vals (σ (.n pos)) (t - 1) with hc
    have hvw : v = word (vanishVal (vo + t - 1)) 0 0 := by
      rw [hv, hvals, osVals_getD (by omega)]
      congr 2; omega
    have hchain : residualChain vals (σ (.n pos)) t = c * (c + v) := by
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      simp only [residualChain, hc, hv, Nat.add_sub_cancel]
    have e : osResQ pos bd row vo (n + 1) t (k - 1) k =
        ([.atom (.const (.n k) (word (vanishVal (vo + t - 1)) 0 0)),
          .atom (.add (.n (k + 1)) (.n (if t = 1 then pos else k - 4)) (.n k)),
          .atom (.mul (.n (k + 2)) (.n (if t = 1 then pos else k - 4)) (.n (k + 1))),
          .atom (.load (.n (k + 3)) (.n bd) (row + t)),
          .atom (.add (.n (k + 4)) (.n (k + 3)) (.n (k + 2))),
          .atom (.mul (.n (k + 5)) (.n (k - 1)) (.n (k + 4)))] ++
          (osResQ pos bd row vo n (t + 1) (k + 5) (k + 6)).1,
        (osResQ pos bd row vo n (t + 1) (k + 5) (k + 6)).2) := rfl
    rw [e]
    dsimp only
    simp only [resQF]
    have hk6 := (osResQ_k pos bd row vo n (t + 1) (k + 5) (k + 6)).1
    have hblk : BlkF C rd σ k (k + 6) (fun j ↦ (resQVals vals (σ (.n pos)) D t (σ (.n (k - 1)))).getD
        (j - k) 0)
        [.atom (.const (.n k) (word (vanishVal (vo + t - 1)) 0 0)),
          .atom (.add (.n (k + 1)) (.n (if t = 1 then pos else k - 4)) (.n k)),
          .atom (.mul (.n (k + 2)) (.n (if t = 1 then pos else k - 4)) (.n (k + 1))),
          .atom (.load (.n (k + 3)) (.n bd) (row + t)),
          .atom (.add (.n (k + 4)) (.n (k + 3)) (.n (k + 2))),
          .atom (.mul (.n (k + 5)) (.n (k - 1)) (.n (k + 4)))]
        (fun σ' ↦ σ' (.n (k + 2)) = residualChain vals (σ (.n pos)) t ∧
          σ' (.n (k + 5)) = residualProd vals (σ (.n pos)) D (t + 1) ∧ AgreeBelow k σ σ') := by
      intro σ' ha hr
      have V : ∀ j < 6, σ' (.n (k + j)) =
          (resQVals vals (σ (.n pos)) D t (σ (.n (k - 1)))).getD j 0 := fun j hj ↦ by
        rw [hr _ (by omega) (by omega)]; simp only [Nat.add_sub_cancel_left]
      have v0 := V 0 (by omega); have v1 := V 1 (by omega); have v2 := V 2 (by omega)
      have v3 := V 3 (by omega); have v4 := V 4 (by omega); have v5 := V 5 (by omega)
      simp only [resQVals, ← hv, ← hc, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2 v3 v4 v5
      have ech : σ' (.n (if t = 1 then pos else k - 4)) = c := by
        rw [ha _ (by split_ifs <;> omega), hch]
      have epe := ha (k - 1) (by omega)
      have ebd := ha bd hbd
      refine ⟨?_, by rw [v2, hchain], by rw [v5, hpe, residualProd, hchain], ha⟩
      simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
      refine ⟨by rw [v0, hvw], by rw [v1, ech, v0], by rw [v2, ech, v1], ?_,
        by rw [v4, v3, v2], by rw [v5, epe, v4]⟩
      rw [v3, ebd]; exact hD t le_rfl (by omega)
    refine BlkF.then (k1 := k + 6) (by omega) (by omega) hblk fun σ1 _ ⟨h2, h5, ha1⟩ ↦ ?_
    have hrec := osResQ_complete (pos := pos) (bd := bd) (row := row) (vo := vo) (L := L) (D := D)
      n (t + 1) (k + 6) σ1 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by
        have h1 : (t + 1 = 1) = False := eq_false (by omega)
        simp only [h1, ↓reduceIte, Nat.add_sub_cancel, show k + 6 - 4 = k + 2 by omega]
        rw [h2, ha1 pos hpos])
      (by rw [show k + 6 - 1 = k + 5 by omega, h5, ha1 pos hpos])
      (fun s h1 h2 ↦ by rw [ha1 bd hbd]; exact hD s (by omega) (by omega))
    rw [ha1 pos hpos, show k + 6 - 1 = k + 5 by omega] at hrec
    refine BlkF.mono hrec fun σ' ⟨hv', ha2⟩ ↦ ⟨by rw [hv', show t + 1 + n = t + (n + 1) by ring],
      fun i hi ↦ (ha2 i (by omega)).trans (ha1 i hi)⟩

/-- The values of the inline `residual_query`. -/
def resQueryF (vo n : ℕ) (pos k : ℕ) (σ : Val) (D : ℕ → E) : ℕ → E :=
  seqF σ k (k + 2) (fun j ↦ [D 0, D 0 + σ (.n pos)].getD (j - k) 0)
    fun σ1 ↦ resQF (osVals vo n) (σ1 (.n pos)) D (n - 1) 1 (k + 2) σ1

/-- **The inline `residual_query`, honestly.** -/
theorem osResQuery_complete {pos bd row vo n k : ℕ} {D : ℕ → E} (σ : Val) (hn : 1 ≤ n)
    (hk : 6 ≤ k) (hpos : pos < k) (hbd : bd < k)
    (hD : ∀ s < n, LoadHolds rd (σ (.n bd)) (row + s) (D s)) :
    BlkF C rd σ k (osResQuery pos bd row vo n k).2.2 (resQueryF vo n pos k σ D)
      (osResQuery pos bd row vo n k).1
      (fun σ' ↦ σ' (.n (osResQuery pos bd row vo n k).2.1) =
        residualProd (osVals vo n) (σ (.n pos)) D n ∧ AgreeBelow k σ σ') := by
  simp only [osResQuery]
  have hk2 := (osResQ_k pos bd row vo (n - 1) 1 (k + 1) (k + 2)).1
  have hA : BlkF C rd σ k (k + 2) (fun j ↦ [D 0, D 0 + σ (.n pos)].getD (j - k) 0)
      [.atom (.load (.n k) (.n bd) row), .atom (.add (.n (k + 1)) (.n k) (.n pos))]
      (fun σ' ↦ σ' (.n (k + 1)) = D 0 + σ (.n pos) ∧ AgreeBelow k σ σ') := by
    intro σ' ha hr
    have v0 := hr k le_rfl (by omega)
    have v1 := hr (k + 1) (by omega) (by omega)
    simp only [Nat.sub_self, Nat.add_sub_cancel_left, List.getD_cons_zero, List.getD_cons_succ] at v0 v1
    refine ⟨?_, v1, ha⟩
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
    refine ⟨by rw [v0, ha bd hbd]; simpa using hD 0 hn, by rw [v1, v0, ha pos hpos]⟩
  refine BlkF.then (k1 := k + 2) (by omega) (by omega) hA fun σ1 _ ⟨h1, ha1⟩ ↦ ?_
  have hrec := osResQ_complete (C := C) (rd := rd) (pos := pos) (bd := bd) (row := row) (vo := vo)
    (L := n) (D := D) (n - 1) 1 (k + 2) σ1 le_rfl (by omega) (by omega) (by omega) (by omega)
    (by simp [residualChain])
    (by rw [show k + 2 - 1 = k + 1 by omega, h1, ha1 pos hpos]; simp [residualProd, residualChain])
    (fun s h1 h2 ↦ by rw [ha1 bd hbd]; exact hD s (by omega))
  rw [show k + 2 - 1 = k + 1 by omega] at hrec
  refine BlkF.mono hrec fun σ' ⟨hv, ha2⟩ ↦ ⟨by rw [hv, ha1 pos hpos, show 1 + (n - 1) = n by omega],
    fun i hi ↦ (ha2 i (by omega)).trans (ha1 i hi)⟩

end
end LeanVM.Guest.B1.Whir
