/-
  LeanVM.Prover.Keccak.Open

  The executable openings of `q_keccak` make the moves of the specification's `hOpen (Fo …)` and
  `hInput`.
-/

module

public import LeanVM.Prover.Keccak.Rounds
public import LeanVM.Prover.Keccak.States

/-!
# The openings

* `slotWords_getD`: the slot words at `inst` are the specification's step extensions;
* `corr_openOut`: the outputs' slot rounds on the slot weights and the slot words make the moves
  of `hSumcheck 3 (Fo …)`;
* `phiTable_getD`, `sliceTable_getD`: the claim restricted to an instance (`PhiI`) and the
  slices at a point (`sliceMle`), by byte tables and bit loops;
* `corr_input`: **the inputs' opening makes the moves of `hInput`**.
-/

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Protocol.EndToEnd.Complete (hSumcheck)

@[expose] public section

theorem hOpen_eq (F : List E → E) : hOpen F = hSumcheck 3 F (List.replicate 6 none) [] := by
  unfold hOpen
  rw [Script.bind_eq, Script.bind_ret]

theorem headD_getD {α : Type} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l <;> rfl

/-- A table listing `F` on the cube. -/
theorem tabInv_of (t : Array E) (F : List E → E) (n : ℕ) (hsz : t.size = 2 ^ n)
    (h : ∀ u < 2 ^ n, t.getD u 0 = F (bitsE u n)) : TabInv t F n [] :=
  ⟨by simp, by simpa using hsz, fun u hu ↦ by simpa using h u (by simpa using hu)⟩

theorem cubeSum_snoc (φ : List E → E) (n : ℕ) (pre : List E) (x : E) :
    cubeSum φ n (pre ++ [x]) = ∑ u ∈ range (2 ^ (n - (pre.length + 1))),
      φ (pre ++ x :: bitsE u (n - (pre.length + 1))) := by
  simp [cubeSum, List.append_assoc]

/-! ## The outputs -/

variable {P : ℕ} {col' col : ℕ → K}

theorem slotWords_getD (hcol : ColAgree P col' col) {inst : List E} (hi : inst.length = P + 4)
    {o : ℕ} (ho : o < 64) :
    (slotWords col' (P + 4) inst).getD o 0 =
      stepMle (P + 4) inst (fun x ↦ col (x + 2 ^ (P + 4) * o)) := by
  rw [slotWords, array_getD_ofFn_lt _ ho, sumRange_eq, stepMle]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' := Finset.mem_range.1 hx
  rw [eqTable_getD_lt _ (by rw [hi]; exact hx'), hcol _ (slot_lt hx' ho)]

/-- **The outputs' slot rounds make the moves of `hSumcheck 3 (Fo …)`.** -/
theorem corr_openOut (hcol : ColAgree P col' col) {inst segment lanesPt : List E}
    (hi : inst.length = P + 4) (hs : segment.length = 1) (hl : lanesPt.length = 5) :
    Corr (fun a b ↦ a.1 = b.1 ∧
        OpenInv 1 1 6 (fun _ ↦ Wo segment lanesPt) (fun _ ↦ Qo (P + 4) col inst) a.1 a.2 ∧
        b.2 = Fo (P + 4) col inst segment lanesPt b.1 ∧ a.1.length = 6)
      (sumcheckBy openRound openFold (List.replicate 6 none)
        ⟨1, [(Array.ofFn (n := 64) fun o ↦ if 25 ≤ o.val ∧ o.val < 50 then
            (eqKernel segment).getD 0 0 * (eqKernel lanesPt).getD (o.val - 25) 0 else 0,
          slotWords col' (P + 4) inst)]⟩)
      (hSumcheck 3 (Fo (P + 4) col inst segment lanesPt) (List.replicate 6 none) []) := by
  have hF : ∀ _ : ℕ, Affine (Wo segment lanesPt) := fun _ ↦
    affine_mle (2 ^ 6) fun o ↦ slotW (eqKernel segment) (firstWeights lanesPt) 1 1 o 0
  have hG : ∀ _ : ℕ, Affine (Qo (P + 4) col inst) := fun _ ↦
    affine_mle (2 ^ 6) fun o ↦ stepMle (P + 4) inst (fun x ↦ col (x + 2 ^ (P + 4) * o))
  refine Corr.mono (fun a b h ↦ ?_) _ _ (corr_sumcheckBy_lt 3 (by norm_num) (by norm_num) _
    openRound openFold
    (OpenInv 1 1 6 (fun _ ↦ Wo segment lanesPt) (fun _ ↦ Qo (P + 4) col inst)) 6
    (fun pre st h hlt ↦ ⟨(polyEval_openRound hF hG h hlt).1, fun x ↦ ?_⟩)
    (fun pre st c h hlt ↦ openInv_fold hF hG h hlt c) _ [] _ ⟨rfl, rfl, fun z hz ↦ ?_⟩
    (by simp))
  · obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [List.nil_append] at h2 h3
    exact ⟨h1, h2, h3, by simpa using h4⟩
  · rw [(polyEval_openRound hF hG h hlt).2, Fo, cubeSum_snoc, Finset.sum_range_one, one_mul]
  · have hz0 : z = 0 := by omega
    subst hz0
    refine ⟨tabInv_of _ _ 6 (by simp) fun u hu ↦ ?_, tabInv_of _ _ 6 (by simp [slotWords])
      fun u hu ↦ ?_⟩
    · show (Array.ofFn (n := 64) fun o ↦ if 25 ≤ o.val ∧ o.val < 50 then
          (eqKernel segment).getD 0 0 * (eqKernel lanesPt).getD (o.val - 25) 0 else 0).getD u 0 = _
      beta_reduce
      rw [array_getD_ofFn_lt _ hu, Wo, sum_eqAt_bitsE hu, slotW_out hs hl]
      simp only
      split_ifs with h
      · rw [eqKernel_getD, eqKernel_getD, hs, hl, ite_eq_left (by norm_num),
          ite_eq_left (by omega)]
      · rfl
    · show (slotWords col' (P + 4) inst).getD u 0 = _
      beta_reduce
      rw [slotWords_getD hcol hi hu, Qo, sum_eqAt_bitsE hu]

/-! ## The inputs -/

theorem phiTable_getD (hcol : ColAgree P col' col) (claim : KeccakClaim)
    (hpt : claim.point.length = P + 1) {i : ℕ} (hi : i < 16) :
    (phiTable col' P claim).getD i 0 = PhiI P col claim i := by
  rw [phiTable, array_getD_ofFn_lt _ hi, sumRange_eq, PhiI]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  have hm : z / 2 ^ P < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rw [pow_succ] at hz'
    linarith
  have hy : z % 2 ^ P < 2 ^ P := Nat.mod_lt _ (by positivity)
  have hx : i + 16 * (z % 2 ^ P) < 2 ^ (P + 4) := by rw [pow_add]; omega
  rw [eqTable_getD_lt _ (by rw [hpt]; exact hz'), sumRange_eq]
  refine congrArg (eqAt claim.point z * ·) ?_
  rw [show 1600 = 25 * 64 from rfl, sum_range_mul]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl' := Finset.mem_range.1 hl
  rw [array_getD_ofFn_lt _ hl', wordDot_laneTabs]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  have hb' := Finset.mem_range.1 hb
  have hj : 64 * l + b < 1600 := by omega
  rw [stAt, statesAt_12 P col _ _ hj, show (64 * l + b) / 64 = l by omega,
    show (64 * l + b) % 64 = b by omega, array_getD_toArray, ite_bitE,
    hcol _ (slot_lt hx (show 25 * (z / 2 ^ P) + l < 64 by omega)), BitVec.testBit_toNat]

theorem sliceTable_getD (hcol : ColAgree P col' col) {a : List E} (ha : a.length = P + 4)
    {o z : ℕ} (ho : o < 64) (hz : z < 64) :
    ((sliceTable col' (P + 4) a).getD o #[]).getD z 0 = sliceMle P col a o z := by
  rw [sliceTable, array_getD_ofFn_lt _ ho]
  rw [(foldl_addBits (2 ^ (P + 4)) 64 (fun x ↦ (eqTable a).getD x 0)
    (fun x ↦ (col' (x + 2 ^ (P + 4) * o)).toBitVec.toNat)).2 z hz, sliceMle]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' := Finset.mem_range.1 hx
  rw [eqTable_getD_lt _ (by rw [ha]; exact hx'), ite_bitE, hcol _ (slot_lt hx' ho),
    BitVec.testBit_toNat]

theorem slotWeightOf_eq (segs w : List E) (first count o z : ℕ) :
    slotWeightOf segs w.toArray first count o z = slotW segs w first count o z := by
  simp only [slotWeightOf, slotW, array_getD_toArray]

theorem getD_map_range {α : Type} (f : ℕ → α) {n z : ℕ} (hz : z < n) (d : α) :
    ((List.range n).map f).getD z d = f z := by
  simp [List.getD_eq_getElem?_getD, hz]

/-- **The inputs' opening makes the moves of `hInput`.** -/
theorem corr_input (hcol : ColAgree P col' col) (claim : KeccakClaim)
    (hshape : ClaimShape P claim) (outs : List ColumnClaim) :
    Corr (fun _ _ ↦ True) (inputProve col' P claim) (hInput P col claim outs) := by
  have hF : ∀ _ : ℕ, Affine (MuT claim.mu) := fun _ ↦ affine_mle (2 ^ 4) fun i ↦ claim.mu.getD i 0
  have hG : ∀ _ : ℕ, Affine (PhiT P col claim) := fun _ ↦
    affine_mle (2 ^ 4) fun i ↦ PhiI P col claim i
  unfold inputProve hInput
  simp only [Script.bind_eq, Script.ret_bind, hOpen_eq]
  refine Corr.bind (fun y y' hy ↦ ?_) _ _ (corr_sumcheckBy_lt 3 (by norm_num) (by norm_num)
    (Fl P col claim) openRound openFold
    (OpenInv 1 1 4 (fun _ ↦ MuT claim.mu) (fun _ ↦ PhiT P col claim)) 4
    (fun pre st h hlt ↦ ⟨(polyEval_openRound hF hG h hlt).1, fun x ↦ by
      rw [(polyEval_openRound hF hG h hlt).2, Fl, cubeSum_snoc, Finset.sum_range_one, one_mul]⟩)
    (fun pre st c h hlt ↦ openInv_fold hF hG h hlt c) _ [] _ ⟨rfl, rfl, fun z hz ↦ ?_⟩
    (by simp))
  · obtain ⟨h1, h2, h3, h4⟩ := hy
    simp only [List.nil_append] at h2 h3
    have hlow : y.1.length = 4 := by simpa using h4
    have hmu : (y.2.pairs.headD (#[], #[])).1.getD 0 0 = MuT claim.mu y.1 := by
      rw [headD_getD]; exact tabInv_full (h2.2.2 0 (by norm_num)).1 hlow
    have ha : (y.1 ++ claim.point.take P).length = P + 4 := by
      simp [hlow, hshape.2.1]; omega
    have hF' : ∀ z, Affine (Ws P claim z) := fun z ↦
      affine_mle (2 ^ 6) fun o ↦ slotW (eqKernel (claim.point.drop P)) claim.weights 0 2 o z
    have hG' : ∀ z, Affine (Qs P col (y.1 ++ claim.point.take P) z) := fun z ↦
      affine_mle (2 ^ 6) fun o ↦ sliceMle P col (y.1 ++ claim.point.take P) o z
    rw [hmu, ← h1]
    refine Corr.bind (fun x x' hx ↦ ?_) _ _ (corr_sumcheckBy_lt 3 (by norm_num) (by norm_num)
      (Fs P col claim y.1) openRound openFold
      (OpenInv (MuT claim.mu y.1) 64 6 (fun z ↦ Ws P claim z)
        (fun z ↦ Qs P col (y.1 ++ claim.point.take P) z)) 6
      (fun pre st h hlt ↦ ⟨(polyEval_openRound hF' hG' h hlt).1, fun x ↦ by
        rw [(polyEval_openRound hF' hG' h hlt).2, Fs, cubeSum_snoc, Finset.sum_comm,
          Finset.mul_sum]⟩)
      (fun pre st c h hlt ↦ openInv_fold hF' hG' h hlt c) _ [] _
      ⟨rfl, by simp, fun z hz ↦ ?_⟩ (by simp))
    · obtain ⟨h1', h2', h3', h4'⟩ := hx
      simp only [List.nil_append] at h2' h3'
      have hx6 : x.1.length = 6 := by simpa using h4'
      have hsl : x.2.pairs.map (fun p ↦ p.2.getD 0 0) =
          slicesOf P col (y.1 ++ claim.point.take P) x'.1 := by
        refine List.ext_getElem (by rw [List.length_map, h2'.2.1, slicesOf_length])
          fun z hz₁ hz₂ ↦ ?_
        have hz : z < 64 := by simpa [h2'.2.1] using hz₁
        rw [List.getElem_map, ← List.getD_eq_getElem _ (#[], #[]) (by simpa using hz₁),
          ← List.getD_eq_getElem _ 0 hz₂, slicesOf_getD _ _ _ _ hz, ← h1',
          tabInv_full (h2'.2.2 z hz).2 hx6]
      rw [← Script.bind_ret (Script.sendList (x.2.pairs.map fun p ↦ p.2.getD 0 0))]
      exact corr_sendList hsl trivial
    · rw [getD_map_range _ hz]
      refine ⟨tabInv_of _ _ 6 (by simp) fun o ho ↦ ?_, tabInv_of _ _ 6 (by simp) fun o ho ↦ ?_⟩
      · beta_reduce
        rw [array_getD_ofFn_lt _ ho, Ws, sum_eqAt_bitsE ho, slotWeightOf_eq]
        rfl
      · beta_reduce
        rw [array_getD_ofFn_lt _ ho, Qs, sum_eqAt_bitsE ho, sliceTable_getD hcol ha ho hz]
  · have hz0 : z = 0 := by omega
    subst hz0
    refine ⟨tabInv_of _ _ 4 (by simp) fun i hi ↦ ?_, tabInv_of _ _ 4 (by simp [phiTable])
      fun i hi ↦ ?_⟩
    · show (Array.ofFn (n := 16) fun i ↦ claim.mu.getD i.val 0).getD i 0 = _
      beta_reduce
      rw [array_getD_ofFn_lt _ hi, MuT, sum_eqAt_bitsE hi]
    · show (phiTable col' P claim).getD i 0 = _
      beta_reduce
      rw [phiTable_getD hcol claim hshape.2.1 hi, PhiT, sum_eqAt_bitsE hi]

end
end LeanVM.Prover.KeccakGkr
