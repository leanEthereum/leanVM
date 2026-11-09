/-
  LeanVM.Prover.Keccak.Pack

  The executable pack and segment rounds make the moves of the specification's `hPack`.
-/

module

public import LeanVM.Prover.Keccak.Rounds
public import LeanVM.Prover.Keccak.States

/-!
# The pack and segment rounds

`PackInv T P s r acc st`: after the challenges `acc`, the state's table lists the packs' states
at `s` extended multilinearly, its first coordinates bound to `acc`:
`st.get z j = Ŝ_j(acc ++ z)` (`Shat`), and the coordinates of `r` still to come.

* `packInv_start`: the table built from the masks and the instance weights;
* `packRound_eval`: the round polynomial evaluates as `scale · FP r (acc ++ [x])`;
* `packInv_fold`: the fold keeps the invariant;
* `corr_pack`: **the rounds make the moves of `hPack (FP T P s w r)`**, ending with the same
  scale and challenges.
-/

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Protocol.EndToEnd.Complete (coeffsOf)

@[expose] public section

variable (T : States) (P : ℕ) (s : E) (w r : List E)

/-- The pack rounds' invariant after the challenges `acc`. -/
def PackInv (acc : List E) (st : PackState) : Prop :=
  acc.length ≤ P + 1 ∧ st.rest = r.drop acc.length ∧
    ∀ z < 2 ^ (P + 1 - acc.length), ∀ j < 1600,
      st.get z j = Shat T P s j (acc ++ bitsE z (P + 1 - acc.length))

theorem affine_Shat (j : ℕ) : Affine (Shat T P s j) :=
  affine_mle (2 ^ (P + 1)) fun z ↦ Shat0 T P s z j

theorem polyEval_chiCoeffs (κ w l0 d0 l1 d1 l2 d2 x : E) :
    polyEval (chiCoeffs κ w l0 d0 l1 d1 l2 d2) x =
      w * (κ * (l0 + x * d0) + (κ + (l1 + x * d1)) * (l2 + x * d2)) := by
  simp only [chiCoeffs, polyEval_cons', polyEval_nil']
  ring

variable {T P s w r}

/-- The rows `2z`, `2z + 1` give the next coordinate's values. -/
theorem packInv_row {acc : List E} {st : PackState} (h : PackInv T P s r acc st)
    (hlt : acc.length < P + 1) {z : ℕ} (hz : z < 2 ^ (P + 1 - (acc.length + 1))) {j : ℕ}
    (hj : j < 1600) (x : E) :
    Shat T P s j (acc ++ x :: bitsE z (P + 1 - (acc.length + 1))) =
      st.get (2 * z) j + x * (st.get (2 * z) j + st.get (2 * z + 1) j) := by
  have hm : P + 1 - (acc.length + 1) + 1 = P + 1 - acc.length := by omega
  have h2 : 2 * z + 1 < 2 ^ (P + 1 - acc.length) := by rw [← hm, pow_succ]; omega
  rw [affine_bitsE (affine_Shat T P s j), hm, ← h.2.2 _ (by omega) j hj, ← h.2.2 _ h2 j hj]

theorem length_packRound (κ : E) (wA : Array E) (st : PackState) :
    (packRound κ wA st).length = 3 := by
  rw [packRound, length_scaleCoeffs]
  exact (polyEval_sumCoeffs 3 _ _ (fun _ _ ↦ by
    rw [length_scaleCoeffs]; exact (polyEval_sumCoeffs 3 _ _ (fun _ _ ↦ rfl) 0).1) 0).1

/-- **A pack round's polynomial** evaluates as the specification's family. -/
theorem packRound_eval (hr : r.length = P + 1) {acc : List E} {st : PackState}
    (h : PackInv T P s r acc st) (hlt : acc.length < P + 1) (x : E) :
    polyEval (packRound (kappaAt s) w.toArray st) x = st.scale * FP T P s w r (acc ++ [x]) := by
  have hrest := h.2.1
  have hrl : st.rest.length - 1 = P + 1 - (acc.length + 1) := by
    rw [hrest, List.length_drop, hr]; omega
  have htail : st.rest.tail = r.drop (acc.length + 1) := by rw [hrest, List.tail_drop]
  have hdl : (r.drop (acc.length + 1)).length = P + 1 - (acc.length + 1) := by
    rw [List.length_drop, hr]
  rw [packRound]
  simp only
  rw [polyEval_scaleCoeffs, (polyEval_sumCoeffs 3 _ _ (fun _ _ ↦ by
    rw [length_scaleCoeffs]; exact (polyEval_sumCoeffs 3 _ _ (fun _ _ ↦ rfl) 0).1) x).2, hrl, FP,
    List.length_append, List.length_singleton]
  refine congrArg (st.scale * ·) (Finset.sum_congr rfl fun z hz ↦ ?_)
  have hz' := Finset.mem_range.1 hz
  rw [polyEval_scaleCoeffs, (polyEval_sumCoeffs 3 _ _ (fun _ _ ↦ rfl) x).2, htail,
    eqTable_getD_lt _ (by rw [hdl]; exact hz'), gt]
  refine congrArg (eqAt (r.drop (acc.length + 1)) z * ·) (Finset.sum_congr rfl fun j hj ↦ ?_)
  have hj' := Finset.mem_range.1 hj
  have h1 := keccakAlong_lt 1 hj'
  have h2 := keccakAlong_lt 2 hj'
  rw [polyEval_chiCoeffs, array_getD_toArray]
  simp only [array_getD_ofFn_lt _ hj', array_getD_ofFn_lt _ h1, array_getD_ofFn_lt _ h2,
    List.append_assoc, List.singleton_append]
  rw [packInv_row h hlt hz' hj', packInv_row h hlt hz' h1, packInv_row h hlt hz' h2]

/-- **The fold keeps the invariant.** -/
theorem packInv_fold (hr : r.length = P + 1) {acc : List E} {st : PackState}
    (h : PackInv T P s r acc st) (hlt : acc.length < P + 1) (c : E) :
    PackInv T P s r (acc ++ [c]) (packFold st c) := by
  have hrest := h.2.1
  have hrl : st.rest.length - 1 = P + 1 - (acc.length + 1) := by
    rw [hrest, List.length_drop, hr]; omega
  refine ⟨by simp; omega, by simp [packFold, hrest, List.tail_drop], fun z hz j hj ↦ ?_⟩
  simp only [List.length_append, List.length_singleton] at hz ⊢
  show ((Array.ofFn (n := 2 ^ (st.rest.length - 1)) fun z ↦ Array.ofFn (n := 1600) fun j ↦
      st.get (2 * z.val) j.val + c * (st.get (2 * z.val) j.val + st.get (2 * z.val + 1) j.val)).getD
      z #[]).getD j 0 = _
  rw [array_getD_ofFn_lt _ (by rw [hrl]; exact hz), array_getD_ofFn_lt _ hj, List.append_assoc,
    List.singleton_append, packInv_row h hlt hz hj]

/-- **The pack rounds make the moves of `hPack`**, and end with its scale and challenges. -/
theorem corr_pack (hr : r.length = P + 1) : ∀ (rs acc : List E) (st : PackState),
    PackInv T P s r acc st → st.rest = rs →
    Corr (fun a b ↦ b.1 = a.2.scale ∧ b.2 = a.1 ∧ a.1.length = rs.length ∧
        PackInv T P s r (acc ++ a.1) a.2)
      (sumcheckBy (packRound (kappaAt s) w.toArray) packFold (rs.map some) st)
      (hPack (FP T P s w r) rs acc st.scale)
  | [], acc, st, h, _ => by
    exact corr_ret ⟨rfl, rfl, rfl, by simpa using h⟩
  | rk :: rs, acc, st, h, hrs => by
    have hlt : acc.length < P + 1 := by
      have h1 := h.2.1
      rw [hrs] at h1
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at h1
      exact List.cons_ne_nil _ _ h1
    have hco : coeffsOf 2 (fun x ↦ st.scale * FP T P s w r (acc ++ [x])) =
        packRound (kappaAt s) w.toArray st :=
      coeffsOf_eq (length_packRound _ _ _) (by norm_num) fun x ↦ packRound_eval hr h hlt x
    simp only [List.map_cons, sumcheckBy, hPack, hco, ← wire_eq]
    refine Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun c ↦ ?_
    have hsc : st.scale * (1 + rk + c) = (packFold st c).scale := by simp [packFold, hrs]
    rw [hsc]
    refine Corr.bind (fun a b hab ↦ ?_) _ _ (corr_pack hr rs (acc ++ [c]) (packFold st c)
      (packInv_fold hr h hlt c) (by simp [packFold, hrs]))
    obtain ⟨h1, h2, h3, h4⟩ := hab
    exact corr_ret ⟨h1, by rw [h2], by simp [h3], by simpa using h4⟩

/-- **The table before the pack rounds**: the packs' states at `s` from the masks. -/
theorem packInv_start {col' col : ℕ → K} (hcol : ColAgree P col' col) {d : ℕ} (hd : d < 12)
    (s : E) (point : List E) :
    PackInv (statesAt (P + 4) col (d + 1)) P s point []
      (packStart (layerMasks col' P (11 - d)) (keccakInstanceWeights s) point) := by
  refine ⟨by simp, by simp [packStart], fun z hz j hj ↦ ?_⟩
  simp only [List.length_nil, Nat.sub_zero, List.nil_append] at hz ⊢
  rw [Shat_bitsE _ _ _ _ hz, Shat0]
  show shatAt _ _ _ z j = _
  rw [shatAt, byteSums_getD _ (Nat.mod_lt _ (by norm_num)),
    byteSums_getD _ (Nat.mod_lt _ (by norm_num)),
    show 16 = 8 + 8 from rfl, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun t ht ↦ ?_
    have ht' := Finset.mem_range.1 ht
    rw [testBit_mod_256 _ ht', testBit_layerMasks hcol hd hz (by omega) hj, array_getD_toArray,
      keccakInstanceWeights_getD _ (by omega), ite_bitE, mul_comm]
  · refine Finset.sum_congr rfl fun t ht ↦ ?_
    have ht' := Finset.mem_range.1 ht
    rw [testBit_div_256 _ ht', testBit_layerMasks hcol hd hz (by omega) hj, array_getD_toArray,
      keccakInstanceWeights_getD _ (by omega), ite_bitE, mul_comm]

end
end LeanVM.Prover.KeccakGkr
