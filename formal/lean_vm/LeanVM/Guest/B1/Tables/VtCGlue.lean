/-
  LeanVM.Guest.B1.Tables.VtCGlue

  `verify_tables`' completeness: the bus decomposition's four glue windows, forward
  (`VtGlue1` .. `VtGlue4`).
-/

module

public import LeanVM.Guest.B1.Tables.VtCGlueI
public import LeanVM.Guest.B1.Tables.VerifyTablesCKids
public import LeanVM.Guest.B1.Tables.VerifyTablesCLoops

/-!
# The glue windows, forward

`vt_glue1`: sums on `fp_w`. `vt_glue2`, `vt_glue3`: the memory's and the bytecode's index chains
(`__loop14`, `__loop16`, from the honest chain at the hinted pointer, `vtc_idxBody_honest`), their ends
stored at `block_index_mle`, and for the memory three words read by `fs_next` items
(`vtc_fs_vals`) and stored with `g^logMem`. `vt_glue4` is in `VtCGlue4`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-! ## Helpers -/

theorem vtc_reads_getD {rd : Reader} {p : E} {l : List E} {t : ℕ} (h : ReadsAt rd p l) (ht : t < l.length) :
    LoadHolds rd p t (l.getD t 0) := by
  rw [List.getD_eq_getElem _ _ ht]; exact h t ht

theorem vtc_idxW_length (point : List E) (κ : ℕ) : (idxChainW point κ).length = 42 := by
  simp [idxChainW]

theorem vtc_idxW_getD (point : List E) {κ t : ℕ} (ht : t < 42) (htk : t ≤ κ) :
    (idxChainW point κ).getD t 0 = ∏ j ∈ Finset.range t, (1 + point.getD j 0 * (1 + gen ^ 2 ^ j)) := by
  simp [idxChainW, List.getD_eq_getElem?_getD, ht, htk]

/-- **An index chain's iteration** on the honest chain at `pI`. -/
theorem vtc_idxBody_honest {rd : Reader} {pI zeta idxc : E} {point : List E} {κ j : ℕ}
    (hz : ReadsAt rd zeta point) (hidx : ∀ t < 34, LoadHolds rd idxc t (1 + gen ^ 2 ^ t))
    (hpI : ReadsAt rd pI (idxChainW point κ)) (hj : j < κ) (hκ : κ ≤ 34) (hjp : j < point.length) :
    IdxBody rd pI zeta idxc (gen ^ j) := by
  have L : ∀ t < 42, LoadHolds rd pI t ((idxChainW point κ).getD t 0) := fun t ht =>
    vtc_reads_getD hpI (by rw [vtc_idxW_length]; exact ht)
  have a1 : LoadHolds rd (pI * gen ^ j) 0 ((idxChainW point κ).getD j 0) :=
    loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact L j (by omega))
  have a2 : LoadHolds rd (zeta * gen ^ j) 0 (point.getD j 0) :=
    loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero, List.getD_eq_getElem _ _ hjp]; exact hz j hjp)
  have a3 : LoadHolds rd (idxc * gen ^ j) 0 (1 + gen ^ 2 ^ j) :=
    loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact hidx j (by omega))
  have a4 : LoadHolds rd (pI * gen ^ j) 1
      ((idxChainW point κ).getD j 0 * (1 + point.getD j 0 * (1 + gen ^ 2 ^ j))) := by
    refine loadHolds_gen_pow_mul.mpr ?_
    have := L (j + 1) (by omega)
    rwa [vtc_idxW_getD point (t := j + 1) (κ := κ) (by omega) (by omega), Finset.prod_range_succ,
      ← vtc_idxW_getD point (t := j) (κ := κ) (by omega) (by omega)] at this
  exact ⟨_, _, _, a1, a2, a3, a4⟩

/-- **An `fs_next` item's values**: the word read and the state after it. -/
theorem vtc_fs_vals {rd : Reader} {hv : ℕ → E} {σf : Val} {s0 s1 cur : V} {j b : ℕ}
    (h : FEq.Holds rd hv σf (.item (.fs s0 s1 cur j b))) {cv : Digest}
    (hcv : (σf s0, σf s1) = digestScalars cv) {w : E} (hw : LoadHolds rd (σf cur) j w) :
    σf (.n b) = w ∧ (σf (.n (b + 13)), σf (.n (b + 14))) = digestScalars (obsCv cv w) := by
  have hdec : decodeCv (σf s0) (σf s1) = cv :=
    digestScalars_injective ((decodeCv_spec ⟨cv, hcv⟩).symm.trans hcv)
  have e0 := h 0 (by simp [FItem.sets]) (by simp [FItem.vals])
  simp only [FItem.sets, FItem.vals, List.getElem_map, List.getElem_range, List.getElem_cons_zero,
    Nat.add_zero] at e0
  have ek : ∀ k < 14, σf (.n (b + (k + 1))) = fsVals w cv 1 k := fun k hk => by
    have := h (k + 1) (by simp [FItem.sets]; omega) (by simp [FItem.vals]; omega)
    simp only [FItem.sets, FItem.vals, List.getElem_map, List.getElem_range, List.getElem_cons_succ] at this
    rw [this, hdec, memAt_of_loadHolds hw]
  refine ⟨by rw [e0, memAt_of_loadHolds hw], ?_⟩
  rw [show b + 13 = b + (12 + 1) by ring, show b + 14 = b + (13 + 1) by ring, ek 12 (by omega),
    ek 13 (by omega)]
  rfl

theorem vtc_fs_ob {C : CallRel} {rd : Reader} {σf : Val} {s0 s1 cur : V} {j : ℕ} {cv : Digest} {w : E}
    (hcv : (σf s0, σf s1) = digestScalars cv) (hw : LoadHolds rd (σf cur) j w) :
    IOb.Holds C rd σf (.fs s0 s1 cur j) :=
  ⟨hw.1, isSome_of_loadHolds hw, cv, hcv⟩

theorem vtc_fpw_ob {C : CallRel} {rd : Reader} {σf : Val} {fpw : E} (h11 : σf (.n 11) = fpw)
    (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v) {i : ℕ} (hi : i < 16) :
    IOb.Holds C rd σf (.ob (.ld (.n 11) i)) := by
  simp only [IOb.Holds, Ob.Holds]
  rw [h11]
  obtain ⟨w, hw⟩ := hfpw i hi
  exact ⟨hw.1, isSome_of_loadHolds hw⟩

theorem vtc_ld_ob {C : CallRel} {rd : Reader} {σf : Val} {p : V} {off : ℕ} {w : E}
    (h : LoadHolds rd (σf p) off w) : IOb.Holds C rd σf (.ob (.ld p off)) :=
  ⟨h.1, isSome_of_loadHolds h⟩

/-! ## `1605 ..< 1616` -/

set_option maxRecDepth 100000 in
theorem vtcG1_ok : fOkI 1882 1893 [] vtcG1 = true := by decide +kernel

/-- **The first glue window completes.** -/
theorem vt_glue1 : VtGlue1 := by
  intro rd σ fpw h11 hfpw
  rw [← vtcG1_eq]
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) (fun _ => 0) vtcG1 vtcG1_ok σ
  generalize hσf : fRunI rd 1882 (fun _ => 0) [] σ vtcG1 = σf at Cm
  have hf : ∀ u, fRunI rd 1882 (fun _ => 0) [] σ vtcG1 u = σf u := fun u => by rw [hσf]
  have e11 : σf (.n 11) = fpw := by
    rw [fRunI_eq_of_def rd _ vtcG1_ok hf (by simp [fDef, vNum])]; exact h11
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl fun _ _ => trivial
  rw [vtcG1_obs]
  intro o ho
  simp only [vtcG1Ob, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> exact vtc_fpw_ob e11 hfpw (by norm_num)

/-! ## `1752 ..< 1808` -/

set_option maxRecDepth 100000 in
theorem vtcG3_ok : fOkI 2024 2077 [] vtcG3 = true := by decide +kernel

/-- The bytecode block's definitions used. -/
def vtcG3Eq : List FEq :=
  [.item (.hint (.alloc (.n 2029) 42)), .def (.const (.n 2030) (word 1 0 0)),
    .def (.const (.n 2031) (word 1 0 0)), .def (.add (.n 2032) (.n 2031) (.n 1997)),
    .def (.const (.n 2033) (word 1 0 0)), .def (.mul (.n 2034) (.n 2029) (.n 1997)),
    .ld (.n 2035) (.n 2034) 0]

set_option maxRecDepth 100000 in
theorem vtcG3_eqsB : vtcG3Eq.all (fun e => (fEqs 2024 [] vtcG3).any (feqEqb e)) = true := by decide +kernel

set_option maxHeartbeats 1000000 in
/-- **The bytecode block completes.** -/
theorem vt_glue3 : VtGlue3 := by
  intro rd σ fpw zeta idxc bim pI point h5 h11 h1817 h1852 h1997 h18 hz hidx hpI hbim hfpw
  rw [← vtcG3_eq]
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) (fun _ => pI) vtcG3 vtcG3_ok σ
  generalize hσf : fRunI rd 2024 (fun _ => pI) [] σ vtcG3 = σf at Cm
  have hf : ∀ u, fRunI rd 2024 (fun _ => pI) [] σ vtcG3 u = σf u := fun u => by rw [hσf]
  have E := fRunI_eqs rd (fun _ => pI) σf vtcG3 [] σ vtcG3_ok hf
  have FR : ∀ k < 2024, σf (.n k) = σ (.n k) := fun k hk =>
    fRunI_eq_of_def rd _ vtcG3_ok hf (by simp [fDef, vNum, hk])
  have hB := vtcG3_eqsB
  simp only [List.all_eq_true] at hB
  have Ed := fun e (he : e ∈ vtcG3Eq) => E e (mem_of_any feqEqb_sound (hB e he))
  simp only [vtcG3Eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at Ed
  obtain ⟨d29, d30, d31, d32, d33, d34, d35⟩ := Ed
  have e29 : σf (.n 2029) = pI := by
    have := d29 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
    simpa [FItem.sets, FItem.vals, hintCells] using this
  have e1997 : σf (.n 1997) = gen ^ 18 := by rw [FR 1997 (by omega), h1997]
  have L := fun t (ht : t < 42) => vtc_reads_getD (t := t) hpI (by rw [vtc_idxW_length]; exact ht)
  have M : LoadHolds rd (pI * gen ^ 18) 0 ((idxChainW point 18).getD 18 0) :=
    loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact L 18 (by omega))
  have e34 : σf (.n 2034) = pI * gen ^ 18 := by
    rw [show σf (.n 2034) = σf (.n 2029) * σf (.n 1997) from d34, e29, e1997]
  have e35 : σf (.n 2035) = (idxChainW point 18).getD 18 0 := by
    rw [show σf (.n 2035) = memAt rd (σf (.n 2034)) 0 from d35, e34, memAt_of_loadHolds M]
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl fun σ' h => ?_
  · rw [vtcG3_obs]
    intro o ho
    simp only [vtcG3Ob, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact vtc_fpw_ob (by rw [FR 11 (by omega), h11]) hfpw (by norm_num) | skip
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]
      rw [e29, show σf (.n 2030) = word 1 0 0 from d30, word_one]
      have := L 0 (by omega)
      rwa [vtc_idxW_getD point (t := 0) (κ := 18) (by omega) (by omega), Finset.prod_range_zero] at this
    · simp only [IOb.Holds, List.map_cons, List.map_nil]
      rw [show σf (.n 2032) = σf (.n 2031) + σf (.n 1997) from d32, show σf (.n 2031) = word 1 0 0 from d31,
        e1997, show σf (.n 2033) = word 1 0 0 from d33, e29, FR 5 (by omega), h5, FR 1817 (by omega), h1817,
        word_one]
      refine ⟨isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK 18), fun _ => ?_⟩
      exact idx_complete idx_ok.2 (by norm_num) rfl fun j hj =>
        vtc_idxBody_honest hz hidx hpI hj (by norm_num) (by omega)
    · simp only [IOb.Holds, Ob.Holds]; rw [e34]; exact ⟨M.1, isSome_of_loadHolds M⟩
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]
      rw [e35, FR 1852 (by omega), h1852]; exact hbim
  · rw [h]; exact e29

/-! ## `1644 ..< 1724` -/

set_option maxRecDepth 100000 in
theorem vtcG2_ok : fOkI 1920 1997 [] vtcG2 = true := by decide +kernel

/-- The memory block's definitions used. -/
def vtcG2Eq : List FEq :=
  [.item (.hint (.alloc (.n 1925) 42)), .def (.const (.n 1926) (word 1 0 0)),
    .def (.const (.n 1927) (word 1 0 0)), .def (.add (.n 1928) (.n 1927) (.n 1893)),
    .def (.const (.n 1929) (word 1 0 0)), .def (.mul (.n 1930) (.n 1925) (.n 1893)),
    .ld (.n 1931) (.n 1930) 0, .item (.fs (.n 19) (.n 20) (.n 2) 0 1937),
    .item (.fs (.n 1950) (.n 1951) (.n 2) 1 1955), .item (.fs (.n 1968) (.n 1969) (.n 2) 2 1973)]

set_option maxRecDepth 100000 in
theorem vtcG2_eqsB : vtcG2Eq.all (fun e => (fEqs 1920 [] vtcG2).any (feqEqb e)) = true := by decide +kernel

set_option maxHeartbeats 1000000 in
/-- **The memory block completes**, its log-size at most `32`. -/
theorem vt_glue2_of {rd : Reader} {σ : Val} {cur fpw pool cplen zeta idxc bim pI m0 m1 m2 : E}
    {point : List E} {logMem : ℕ} {cv : Digest}
    (h2 : σ (.n 2) = cur) (h5 : σ (.n 5) = zeta) (h11 : σ (.n 11) = fpw) (h13 : σ (.n 13) = pool)
    (h14 : σ (.n 14) = cplen) (h1817 : σ (.n 1817) = idxc) (h1852 : σ (.n 1852) = bim)
    (h1893 : σ (.n 1893) = gen ^ logMem) (hcv : (σ (.n 19), σ (.n 20)) = digestScalars cv)
    (hl0 : 0 < logMem) (hlp : logMem ≤ point.length) (hz : ReadsAt rd zeta point)
    (hidx : ∀ t < 34, LoadHolds rd idxc t (1 + gen ^ 2 ^ t)) (hpI : ReadsAt rd pI (idxChainW point logMem))
    (hbim : LoadHolds rd bim 1 ((idxChainW point logMem).getD logMem 0))
    (hfpw : ∀ i < 16, ∃ v, LoadHolds rd fpw i v) (hcur : ReadsAt rd cur [m0, m1, m2])
    (hpool : ReadsAt rd pool [m0, m1, m2]) (hcpl : ∀ j < 3, LoadHolds rd cplen j (gen ^ logMem))
    (hl32 : logMem ≤ 32) :
    Completes (coreProgram.Rel rd) rd 1920 1997 ((vtPre.drop 1644).take 80) σ (fun σ' =>
      σ' (.n 1925) = pI ∧ σ' (.n 1937) = m0 ∧ σ' (.n 1955) = m1 ∧ σ' (.n 1973) = m2 ∧
        (σ' (.n 1986), σ' (.n 1987)) = digestScalars (obsAll cv [m0, m1, m2])) := by
  rw [← vtcG2_eq]
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) (fun _ => pI) vtcG2 vtcG2_ok σ
  generalize hσf : fRunI rd 1920 (fun _ => pI) [] σ vtcG2 = σf at Cm
  have hf : ∀ u, fRunI rd 1920 (fun _ => pI) [] σ vtcG2 u = σf u := fun u => by rw [hσf]
  have E := fRunI_eqs rd (fun _ => pI) σf vtcG2 [] σ vtcG2_ok hf
  have FR : ∀ k < 1920, σf (.n k) = σ (.n k) := fun k hk =>
    fRunI_eq_of_def rd _ vtcG2_ok hf (by simp [fDef, vNum, hk])
  have hB := vtcG2_eqsB
  simp only [List.all_eq_true] at hB
  have Ed := fun e (he : e ∈ vtcG2Eq) => E e (mem_of_any feqEqb_sound (hB e he))
  simp only [vtcG2Eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at Ed
  obtain ⟨d25, d26, d27, d28, d29, d30, d31, f1, f2, f3⟩ := Ed
  have e25 : σf (.n 1925) = pI := by
    have := d25 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
    simpa [FItem.sets, FItem.vals, hintCells] using this
  have e1893 : σf (.n 1893) = gen ^ logMem := by rw [FR 1893 (by omega), h1893]
  have e2 : σf (.n 2) = cur := by rw [FR 2 (by omega), h2]
  have L : ∀ t < 42, LoadHolds rd pI t ((idxChainW point logMem).getD t 0) := fun t ht =>
    vtc_reads_getD hpI (by rw [vtc_idxW_length]; exact ht)
  have M : LoadHolds rd (pI * gen ^ logMem) 0 ((idxChainW point logMem).getD logMem 0) :=
    loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact L logMem (by omega))
  have e30 : σf (.n 1930) = pI * gen ^ logMem := by
    rw [show σf (.n 1930) = σf (.n 1925) * σf (.n 1893) from d30, e25, e1893]
  have e31 : σf (.n 1931) = (idxChainW point logMem).getD logMem 0 := by
    rw [show σf (.n 1931) = memAt rd (σf (.n 1930)) 0 from d31, e30, memAt_of_loadHolds M]
  have c0 : LoadHolds rd (σf (.n 2)) 0 m0 := by rw [e2]; simpa using hcur 0 (by simp)
  have c1 : LoadHolds rd (σf (.n 2)) 1 m1 := by rw [e2]; simpa using hcur 1 (by simp)
  have c2 : LoadHolds rd (σf (.n 2)) 2 m2 := by rw [e2]; simpa using hcur 2 (by simp)
  have hcv' : (σf (.n 19), σf (.n 20)) = digestScalars cv := by rw [FR 19 (by omega), FR 20 (by omega)]; exact hcv
  have F1 := vtc_fs_vals f1 hcv' c0
  have F2 := vtc_fs_vals f2 F1.2 c1
  have F3 := vtc_fs_vals f3 F2.2 c2
  have e13 : σf (.n 13) = pool := by rw [FR 13 (by omega), h13]
  have e14 : σf (.n 14) = cplen := by rw [FR 14 (by omega), h14]
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl fun σ' h => ?_
  · rw [vtcG2_obs]
    intro o ho
    simp only [vtcG2Ob, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals first | exact vtc_fpw_ob (by rw [FR 11 (by omega), h11]) hfpw (by norm_num) | skip
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]
      rw [e25, show σf (.n 1926) = word 1 0 0 from d26, word_one]
      have := L 0 (by omega)
      rwa [vtc_idxW_getD point (t := 0) (κ := logMem) (by omega) (by omega), Finset.prod_range_zero] at this
    · simp only [IOb.Holds, List.map_cons, List.map_nil]
      rw [show σf (.n 1928) = σf (.n 1927) + σf (.n 1893) from d28, show σf (.n 1927) = word 1 0 0 from d27,
        e1893, show σf (.n 1929) = word 1 0 0 from d29, e25, FR 5 (by omega), h5, FR 1817 (by omega), h1817,
        word_one]
      refine ⟨isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK logMem), fun _ => ?_⟩
      exact idx_complete idx_ok.1 hl0 rfl fun j hj => vtc_idxBody_honest hz hidx hpI hj (by omega) (by omega)
    · simp only [IOb.Holds, Ob.Holds]; rw [e30]; exact ⟨M.1, isSome_of_loadHolds M⟩
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]
      rw [e31, FR 1852 (by omega), h1852]; exact hbim
    · exact vtc_fs_ob hcv' c0
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]
      rw [e13, F1.1]; simpa using hpool 0 (by simp)
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]; rw [e14, e1893]; exact hcpl 0 (by omega)
    · exact vtc_fs_ob F1.2 c1
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]
      rw [e13, F2.1]; simpa using hpool 1 (by simp)
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]; rw [e14, e1893]; exact hcpl 1 (by omega)
    · exact vtc_fs_ob F2.2 c2
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]
      rw [e13, F3.1]; simpa using hpool 2 (by simp)
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]; rw [e14, e1893]; exact hcpl 2 (by omega)
  · rw [h]
    exact ⟨e25, F1.1, F2.1, F3.1, F3.2⟩

/-- **The memory block completes.** -/
theorem vt_glue2 : VtGlue2 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h2 h5 h11 h13 h14 h1817 h1852 h1893 hcv hl0 hlp hz hidx hpI hbim hfpw
    hcur hpool hcpl hl32 =>
  vt_glue2_of h2 h5 h11 h13 h14 h1817 h1852 h1893 hcv hl0 hlp hz hidx hpI hbim hfpw hcur hpool hcpl hl32

end
end LeanVM.Guest.B1.VerifySub
