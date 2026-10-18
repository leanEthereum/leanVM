/-
  LeanVM.Guest.B1.Main.AggEqtreeC

  The inlined `eqtree` of `aggregate_claims` (G:762-777) backward: the coordinates and the layers
  in memory give the block, on its honest valuation.
-/

module

public import LeanVM.Guest.B1.Main.AggStepsC

/-!
# `eqtree`, backward

`setEt σ b rs` sets `eqtree`'s values from `b`: the first coordinate, then each layer `t ≥ 1`'s
coordinate and its entries, the parent read and its two children (`setEtLayer`). `eqtree_complete`:
on a valuation that agrees with it, the block holds once the coordinates are at `pt·g^off` and
every layer is in `out`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- Entry `i` of layer `t` of the equality kernel of `rs`. -/
abbrev etK (rs : List E) (t i : ℕ) : E := (eqKernel (rs.take t)).getD i 0

/-- Layer `t ≥ 1`'s values. -/
def setEtLayer (σ : Val) (b t : ℕ) (rs : List E) : Val :=
  setb (setl σ (etBase b t) [rs.getD t 0, 1, 1 + rs.getD t 0]) (etBase b t + 3) (2 ^ t) 3
    fun i o => match o with
      | 0 => etK rs t i
      | 1 => etK rs t i * (1 + rs.getD t 0)
      | _ => etK rs t i * rs.getD t 0

/-- `eqtree`'s values from `b`. -/
def setEt (σ : Val) (b : ℕ) (rs : List E) : Val :=
  setEtLayer (setEtLayer (setEtLayer (setEtLayer (setEtLayer
    (setl σ b [rs.getD 0 0, 1, 1 + rs.getD 0 0]) b 1 rs) b 2 rs) b 3 rs) b 4 rs) b 5 rs

theorem etBase_eq (b : ℕ) : etBase b 1 = b + 3 ∧ etBase b 2 = b + 12 ∧ etBase b 3 = b + 27 ∧
    etBase b 4 = b + 54 ∧ etBase b 5 = b + 105 := by
  simp only [etBase]; omega

theorem setEtLayer_lt {σ : Val} {b t k : ℕ} {rs : List E} (h : k < etBase b t) :
    setEtLayer σ b t rs (.n k) = σ (.n k) := by
  rw [setEtLayer, setb_lt (by omega), setl, set_n_lt h]

theorem setEtLayer_ge {σ : Val} {b t k : ℕ} {rs : List E} (h : etBase b t + 3 + 2 ^ t * 3 ≤ k) :
    setEtLayer σ b t rs (.n k) = σ (.n k) := by
  rw [setEtLayer, setb_ge (by omega), setl, set_n_ge (by simp; omega)]

theorem setEtLayer_spec (σ : Val) (b t : ℕ) (rs : List E) :
    setEtLayer σ b t rs (.n (etBase b t)) = rs.getD t 0 ∧
      setEtLayer σ b t rs (.n (etBase b t + 1)) = 1 ∧
      setEtLayer σ b t rs (.n (etBase b t + 2)) = 1 + rs.getD t 0 ∧
      ∀ i < 2 ^ t, setEtLayer σ b t rs (.n (etBase b t + 3 + 3 * i)) = etK rs t i ∧
        setEtLayer σ b t rs (.n (etBase b t + 3 + 3 * i + 1)) = etK rs t i * (1 + rs.getD t 0) ∧
        setEtLayer σ b t rs (.n (etBase b t + 3 + 3 * i + 2)) = etK rs t i * rs.getD t 0 := by
  refine ⟨?_, ?_, ?_, fun i hi => ⟨?_, ?_, ?_⟩⟩
  · rw [setEtLayer, setb_lt (by omega)]; b1_look
  · rw [setEtLayer, setb_lt (by omega)]; b1_look
  · rw [setEtLayer, setb_lt (by omega)]; b1_look
  · rw [setEtLayer, show etBase b t + 3 + 3 * i = etBase b t + 3 + 3 * i + 0 by rfl,
      setb_in (by omega) hi]; rfl
  · rw [setEtLayer, setb_in (by omega) hi]; rfl
  · rw [setEtLayer, setb_in (by omega) hi]; rfl

/-- The values of `eqtree`'s layers in `setEt`. -/
def EtVals (σ : Val) (b : ℕ) (rs : List E) : Prop :=
  σ (.n b) = rs.getD 0 0 ∧ σ (.n (b + 1)) = 1 ∧ σ (.n (b + 2)) = 1 + rs.getD 0 0 ∧
    ∀ t < 5, σ (.n (etBase b (t + 1))) = rs.getD (t + 1) 0 ∧
      σ (.n (etBase b (t + 1) + 1)) = 1 ∧ σ (.n (etBase b (t + 1) + 2)) = 1 + rs.getD (t + 1) 0 ∧
      ∀ i < 2 ^ (t + 1), σ (.n (etBase b (t + 1) + 3 + 3 * i)) = etK rs (t + 1) i ∧
        σ (.n (etBase b (t + 1) + 3 + 3 * i + 1)) = etK rs (t + 1) i * (1 + rs.getD (t + 1) 0) ∧
        σ (.n (etBase b (t + 1) + 3 + 3 * i + 2)) = etK rs (t + 1) i * rs.getD (t + 1) 0

theorem etBase_bound (b t : ℕ) (ht : t < 5) :
    b ≤ etBase b (t + 1) ∧ etBase b (t + 1) + 3 + 3 * 2 ^ (t + 1) ≤ b + 204 := by
  interval_cases t <;> simp only [etBase] <;> omega

theorem etVals_congr {σ σ' : Val} {b : ℕ} {rs : List E}
    (h : ∀ i, b ≤ i → i < b + 204 → σ (.n i) = σ' (.n i)) (h' : EtVals σ' b rs) : EtVals σ b rs := by
  obtain ⟨e0, e1, e2, eL⟩ := h'
  refine ⟨by rw [h _ (by omega) (by omega)]; exact e0, by rw [h _ (by omega) (by omega)]; exact e1,
    by rw [h _ (by omega) (by omega)]; exact e2, fun t ht => ?_⟩
  obtain ⟨f0, f1, f2, fE⟩ := eL t ht
  obtain ⟨hB0, hB⟩ := etBase_bound b t ht
  refine ⟨by rw [h _ (by omega) (by omega)]; exact f0, by rw [h _ (by omega) (by omega)]; exact f1,
    by rw [h _ (by omega) (by omega)]; exact f2, fun i hi => ?_⟩
  obtain ⟨g0, g1, g2⟩ := fE i hi
  exact ⟨by rw [h _ (by omega) (by omega)]; exact g0, by rw [h _ (by omega) (by omega)]; exact g1,
    by rw [h _ (by omega) (by omega)]; exact g2⟩

/-- A side condition on `etBase` at a concrete layer. -/
macro "et_omega" : tactic =>
  `(tactic| (simp only [etBase, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at *; omega))

theorem setEt_vals (σ : Val) (b : ℕ) (rs : List E) : EtVals (setEt σ b rs) b rs := by
  refine ⟨?_, ?_, ?_, fun t ht => ?_⟩
  · simp (disch := et_omega) only [setEt, setEtLayer_lt]; b1_look
  · simp (disch := et_omega) only [setEt, setEtLayer_lt]; b1_look
  · simp (disch := et_omega) only [setEt, setEtLayer_lt]; b1_look
  interval_cases t
  all_goals
    refine ⟨?_, ?_, ?_, fun i hi => ⟨?_, ?_, ?_⟩⟩ <;>
    simp (disch := et_omega) only [setEt, setEtLayer_lt] <;>
    first
      | exact (setEtLayer_spec _ _ _ _).1 | exact (setEtLayer_spec _ _ _ _).2.1
      | exact (setEtLayer_spec _ _ _ _).2.2.1 | exact ((setEtLayer_spec _ _ _ _).2.2.2 i hi).1
      | exact ((setEtLayer_spec _ _ _ _).2.2.2 i hi).2.1
      | exact ((setEtLayer_spec _ _ _ _).2.2.2 i hi).2.2

theorem setEt_lt {σ : Val} {b k : ℕ} {rs : List E} (h : k < b) : setEt σ b rs (.n k) = σ (.n k) := by
  simp (disch := et_omega) only [setEt, setEtLayer_lt]
  b1_look

theorem setEt_ge {σ : Val} {b k : ℕ} {rs : List E} (h : b + 204 ≤ k) :
    setEt σ b rs (.n k) = σ (.n k) := by
  simp (disch := et_omega) only [setEt, setEtLayer_ge]
  b1_look

theorem etK_succ_lo (rs : List E) (t i : ℕ) (ht : t < rs.length) (hi : i < 2 ^ t) :
    etK rs (t + 1) i = etK rs t i * (1 + rs.getD t 0) := by
  rw [etK, eqKernel_take_succ _ _ ht,
    eqKernel_getD_lo _ _ (by rw [List.length_take, min_eq_left (by omega)]; exact hi)]

theorem etK_succ_hi (rs : List E) (t i : ℕ) (ht : t < rs.length) (hi : i < 2 ^ t) :
    etK rs (t + 1) (2 ^ t + i) = etK rs t i * rs.getD t 0 := by
  have hl : (rs.take t).length = t := by rw [List.length_take]; omega
  rw [etK, eqKernel_take_succ _ _ ht]
  have := eqKernel_getD_hi (rs.take t) (rs.getD t 0) (i := i) (by rw [hl]; exact hi)
  rwa [hl] at this

/-- **`eqtree`, backward**: on a valuation with `eqtree`'s values from `b`, the block holds once
the coordinates are at `pt·g^off` and the equality kernel's layers in `out`. -/
theorem eqtree_complete {σ : Val} (pt out : V) (off b : ℕ) (kret : List E → Prop) (rs : List E)
    (hl : rs.length = 6) (hv : EtVals σ b rs)
    (hr : ∀ t < 6, LoadHolds rd (σ pt) (off + t) (rs.getD t 0))
    (hout : ∀ t < 6, ∀ i < 2 ^ (t + 1), LoadHolds rd (σ out) (2 ^ (t + 1) - 2 + i) (etK rs (t + 1) i)) :
    Stmt.HoldsList C rd σ (eqtreeT pt off out b) True kret := by
  rw [eqtreeT, holdsList_append,
    holdsList_range_flatten 5 (fun t => etLayer pt off out b (t + 1)) (fun _ => noRetList_etLayer ..)]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one]
  obtain ⟨e0, e1, e2, eL⟩ := hv
  have k0 := etK_succ_lo rs 0 0 (by omega) (by norm_num)
  have k1 := etK_succ_hi rs 0 0 (by omega) (by norm_num)
  simp only [etK, List.take_zero, show eqKernel [] = [1] from rfl, List.getD_cons_zero, one_mul,
    pow_zero, Nat.add_zero, zero_add] at k0 k1
  refine ⟨by rw [e0]; simpa using hr 0 (by omega), e1, by rw [e2, e1, e0], ?_, ?_,
    fun t ht => ?_, trivial⟩
  · have := hout 0 (by norm_num) 0 (by norm_num)
    rw [etK, k0] at this
    rw [e2]; simpa using this
  · have := hout 0 (by norm_num) 1 (by norm_num)
    rw [etK, k1] at this
    rw [e0]; simpa using this
  rw [etLayer, holdsList_append, holdsList_range_flatten _ (etEntry out b (t + 1)) (fun _ => rfl)]
  simp only [etEntry, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one]
  obtain ⟨f0, f1, f2, fE⟩ := eL t ht
  refine ⟨by rw [f0]; exact hr _ (by omega), f1, by rw [f2, f1, f0], fun i hi => ?_, trivial⟩
  obtain ⟨g0, g1, g2⟩ := fE i hi
  have hp : 2 ^ (t + 1) ≤ 2 ^ (t + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : 2 ^ (t + 1 + 1) = 2 * 2 ^ (t + 1) := by rw [pow_succ]; ring
  rw [show etBase b (t + 1) + 4 + 3 * i = etBase b (t + 1) + 3 + 3 * i + 1 by omega,
    show etBase b (t + 1) + 5 + 3 * i = etBase b (t + 1) + 3 + 3 * i + 2 by omega]
  refine ⟨by rw [g0]; exact hout t (by omega) i hi, by rw [g1, g0, f2], ?_, by rw [g2, g0, f0], ?_,
    trivial⟩
  · rw [g1, ← etK_succ_lo rs (t + 1) i (by omega) hi]
    exact hout (t + 1) (by omega) i (by omega)
  · rw [g2, ← etK_succ_hi rs (t + 1) i (by omega) hi,
      show 2 ^ (t + 1 + 1) - 2 + 2 ^ (t + 1) + i = 2 ^ (t + 1 + 1) - 2 + (2 ^ (t + 1) + i) by omega]
    exact hout (t + 1) (by omega) _ (by omega)

end
end LeanVM.Guest.B1.Main
