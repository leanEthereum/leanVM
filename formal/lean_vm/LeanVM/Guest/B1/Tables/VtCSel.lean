/-
  LeanVM.Guest.B1.Tables.VtCSel

  `verify_tables`' completeness: a push or count block's selector, forward (`VtSelComplete`).
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesC0
public import LeanVM.Guest.B1.Tables.VerifyTablesCIface
public import LeanVM.Guest.B1.Tables.VerifyTablesCLoops

/-!
# A block's selector, forward (G:1572-1594)

`selT b v self` as items (`vtSelI`): the block's log-height `k` and `μ - k` range-checked, the
offset's bits hinted into `p12`, the two chains' buffers `p15`, `p16` hinted and started at `1`,
the selector loop on `μ - k` iterations, and the chains' ends read: the equality chain's is the
placement's `eqAbove` (`eqAbove_prod`), the rebuilt offset's is `g^off` since the bits are an
aligned offset's (`vtcs_goff`). `vt_sel_complete`: `VtSelComplete`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- A block's selector, as items. -/
def vtSelI (b v : ℕ) (self : String) : List FItem :=
  [.atom (.load (.n v) (.n 9) b), .atom (.const (.n (v + 1)) (word 8589934592 0 0)),
    .atom (.rangeCheck (.n v) (.n (v + 2)) (.n (v + 3)) (.n (v + 4)) (.n (v + 1))),
    .atom (.mul (.n 6) (.n (v + 5)) (.n v)), .atom (.const (.n (v + 6)) (word 8589934592 0 0)),
    .atom (.rangeCheck (.n (v + 5)) (.n (v + 7)) (.n (v + 8)) (.n (v + 9)) (.n (v + 6))),
    .atom (.mul (.n (v + 10)) (.n 5) (.n v)), .atom (.const (.n (v + 11)) (word 17179869184 0 0)),
    .hint (.allocDyn (.n (v + 12)) (.n (v + 11))), .atom (.load (.n (v + 13)) (.n 128) b),
    .hint (.bitsExp (.n (v + 13)) 34 (.heap (.n (v + 12)) 0 34)),
    .atom (.mul (.n (v + 14)) (.n (v + 12)) (.n v)), .hint (.alloc (.n (v + 15)) 42),
    .hint (.alloc (.n (v + 16)) 42), .atom (.const (.n (v + 17)) (word 1 0 0)),
    .atom (.load (.n (v + 17)) (.n (v + 15)) 0), .atom (.const (.n (v + 18)) (word 1 0 0)),
    .atom (.load (.n (v + 18)) (.n (v + 16)) 0), .atom (.const (.n (v + 19)) (word 1 0 0)),
    .atom (.add (.n (v + 20)) (.n (v + 19)) (.n (v + 5))), .atom (.const (.n (v + 21)) (word 1 0 0)),
    .callIf (.n (v + 20)) self
      [.n (v + 21), .n (v + 5), .n (v + 14), .n (v + 15), .n (v + 10), .n (v + 16), .n 10, .n v],
    .atom (.mul (.n (v + 22)) (.n (v + 15)) (.n (v + 5))), .atom (.load (.n (v + 23)) (.n (v + 22)) 0),
    .atom (.mul (.n (v + 24)) (.n (v + 16)) (.n (v + 5))), .atom (.load (.n (v + 25)) (.n (v + 24)) 0),
    .atom (.load (.n (v + 26)) (.n 128) b), .atom (.assertEq (.n (v + 25)) (.n (v + 26)))]

theorem vtSelI_stmts (b v : ℕ) (self : String) : (vtSelI b v self).flatMap FItem.stmts = selT b v self := rfl

/-- A block's selector's obligations. -/
def vtSelOb (b v : ℕ) (self : String) : List IOb :=
  [.ob (.ld (.n 9) b), .ob (.rc (.n v) (.n (v + 2))), .ob (.nz (.n v)), .ob (.rc (.n (v + 5)) (.n (v + 7))),
    .ob (.ld (.n 128) b), .ob (.holds (.load (.n (v + 17)) (.n (v + 15)) 0)),
    .ob (.holds (.load (.n (v + 18)) (.n (v + 16)) 0)),
    .callIf (.n (v + 20)) self
      [.n (v + 21), .n (v + 5), .n (v + 14), .n (v + 15), .n (v + 10), .n (v + 16), .n 10, .n v],
    .ob (.ld (.n (v + 22)) 0), .ob (.ld (.n (v + 24)) 0), .ob (.ld (.n 128) b),
    .ob (.holds (.assertEq (.n (v + 25)) (.n (v + 26))))]

/-- A block's selector's definitions. -/
def vtSelEq (b v : ℕ) : List FEq :=
  [.ld (.n v) (.n 9) b, .def (.const (.n (v + 1)) (word 8589934592 0 0)),
    .rc (.n v) (.n (v + 2)) (.n (v + 3)) (.n (v + 4)) (.n (v + 1)), .sv (.n (v + 5)) (.n 6) (.n v),
    .def (.const (.n (v + 6)) (word 8589934592 0 0)),
    .rc (.n (v + 5)) (.n (v + 7)) (.n (v + 8)) (.n (v + 9)) (.n (v + 6)),
    .def (.mul (.n (v + 10)) (.n 5) (.n v)), .item (.hint (.allocDyn (.n (v + 12)) (.n (v + 11)))),
    .ld (.n (v + 13)) (.n 128) b, .def (.mul (.n (v + 14)) (.n (v + 12)) (.n v)),
    .item (.hint (.alloc (.n (v + 15)) 42)), .item (.hint (.alloc (.n (v + 16)) 42)),
    .def (.const (.n (v + 17)) (word 1 0 0)), .def (.const (.n (v + 18)) (word 1 0 0)),
    .def (.const (.n (v + 19)) (word 1 0 0)), .def (.add (.n (v + 20)) (.n (v + 19)) (.n (v + 5))),
    .def (.const (.n (v + 21)) (word 1 0 0)), .def (.mul (.n (v + 22)) (.n (v + 15)) (.n (v + 5))),
    .ld (.n (v + 23)) (.n (v + 22)) 0, .def (.mul (.n (v + 24)) (.n (v + 16)) (.n (v + 5))),
    .ld (.n (v + 25)) (.n (v + 24)) 0, .ld (.n (v + 26)) (.n 128) b]

set_option maxRecDepth 100000 in
theorem vtSel_ok : ∀ i < 65,
    fOkI (selVal.getD i 0) (selVal.getD i 0 + 27) [] (vtSelI (selBlk.getD i 0) (selVal.getD i 0) (selNames.getD i "")) =
      true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtSel_obsB : ∀ i < 65, listEqb iobEqb
    (iObs (selVal.getD i 0) [] (vtSelI (selBlk.getD i 0) (selVal.getD i 0) (selNames.getD i "")))
    (vtSelOb (selBlk.getD i 0) (selVal.getD i 0) (selNames.getD i "")) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtSel_eqsB : ∀ i < 65, (vtSelEq (selBlk.getD i 0) (selVal.getD i 0)).all (fun e =>
    (fEqs (selVal.getD i 0) [] (vtSelI (selBlk.getD i 0) (selVal.getD i 0) (selNames.getD i ""))).any
      (feqEqb e)) = true := by decide +kernel

theorem vtSel_val : ∀ i < 65, 128 < selVal.getD i 0 := by decide

theorem vtSel_mem : ∀ i < 65, selNames.getD i "" ∈ selNames := fun i hi =>
  List.getD_eq_getElem selNames "" (by simpa [selNames] using hi) ▸ List.getElem_mem _

/-! ## Facts for the proof -/

theorem vtcs_get {rd : Reader} {p : E} {n t : ℕ} {f : ℕ → E} (h : ReadsAt rd p ((List.range n).map f))
    (ht : t < n) : LoadHolds rd p t (f t) := by
  have := h t (by simpa using ht)
  simpa using this

theorem vtcs_bitE_mul (c : Bool) : bitE c * bitE c = bitE c := by cases c <;> simp [bitE]

theorem vtcs_bitE_inj {a b : Bool} (h : bitE a = bitE b) : a = b := by
  cases a <;> cases b <;> simp [bitE] at h ⊢

/-- **An aligned offset's bits rebuild it**: over the coordinates from `k` up to `M`. -/
theorem vtcs_goff {M k off : ℕ} (hk : k ≤ M) (hoff : off < 2 ^ M) (hal : 2 ^ k ∣ off) :
    ∏ j ∈ Finset.range (M - k), (1 + bitE (off.testBit (k + j)) * (gen ^ 2 ^ (k + j) + 1)) = gen ^ off := by
  obtain ⟨off', hoff', hdvd, hprod, hbits⟩ := sel_rebuild (M := M) (κ := k)
    (b := fun j => bitE (off.testBit j)) hk (fun t _ => vtcs_bitE_mul _)
  rw [hprod]
  congr 1
  refine (Nat.eq_of_testBit_eq fun j => ?_).symm
  rcases Nat.lt_or_ge j k with h | h
  · have h1 := Nat.testBit_mod_two_pow off' k j
    have h2 := Nat.testBit_mod_two_pow off k j
    rw [Nat.mod_eq_zero_of_dvd hdvd, Nat.zero_testBit] at h1
    rw [Nat.mod_eq_zero_of_dvd hal, Nat.zero_testBit] at h2
    simp only [h, decide_true, Bool.true_and] at h1 h2
    rw [← h1, ← h2]
  · rcases Nat.lt_or_ge j M with h' | h'
    · have := hbits (j - k) (by omega)
      rw [show k + (j - k) = j by omega] at this
      exact vtcs_bitE_inj this
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hoff' (Nat.pow_le_pow_right (by decide) h')),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hoff (Nat.pow_le_pow_right (by decide) h'))]

/-- The equality chain's prefix products. -/
def vtcsC15 (off k : ℕ) (point : List E) (t : ℕ) : E :=
  ∏ j ∈ Finset.range t, (1 + bitE (off.testBit (k + j)) + point.getD (k + j) 0)

/-- The rebuilt offset's prefix products. -/
def vtcsC16 (off k : ℕ) (t : ℕ) : E :=
  ∏ j ∈ Finset.range t, (1 + bitE (off.testBit (k + j)) * (gen ^ 2 ^ (k + j) + 1))

theorem vtcs_isInK_one_add (a : ℕ) : IsInK (word 1 0 0 + gen ^ a) := by
  rw [word_one, ← pow_zero gen]; exact isInK_add (gen_pow_isInK 0) (gen_pow_isInK a)

/-- The oracle: the three pointers. -/
noncomputable def vtSelHv (v : ℕ) (p12 p15 p16 : E) (n : ℕ) : E :=
  if n = v + 12 then p12 else if n = v + 15 then p15 else if n = v + 16 then p16 else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **A push or count block's selector completes** (G:1572-1594). -/
theorem vt_sel_complete : VtSelComplete := by
  intro i hi κ hκ rd hlow σ zeta bk sq offP p12 p15 p16 point k off h5 h6 h9 h10 h128 hkμ hμ hoff hal
    hbk hoffL hz hsq h12 h15 h16
  have hst := stmtsEqb_sound (sel_blocks i hi)
  have hok := vtSel_ok i hi
  have hobs := listEqb_sound iobEqb_sound (vtSel_obsB i hi)
  have heqs := vtSel_eqsB i hi
  have hsok := sel_ok i hi
  have hvl : 128 < selVal.getD i 0 := vtSel_val i hi
  rw [← hst, ← vtSelI_stmts]
  generalize selBlk.getD i 0 = b at *
  generalize selVal.getD i 0 = v at *
  generalize selNames.getD i "" = self at *
  set μ := point.length with hμdef
  set m := μ - k with hm
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) (vtSelHv v p12 p15 p16) (vtSelI b v self) hok σ
  generalize hσf : fRunI rd v (vtSelHv v p12 p15 p16) [] σ (vtSelI b v self) = σf at Cm
  have hf : ∀ w, fRunI rd v (vtSelHv v p12 p15 p16) [] σ (vtSelI b v self) w = σf w := fun w => by rw [hσf]
  have E := fRunI_eqs rd (vtSelHv v p12 p15 p16) σf (vtSelI b v self) [] σ hok hf
  have FR : ∀ n < v, σf (.n n) = σ (.n n) := fun n hn =>
    fRunI_eq_of_def rd _ hok hf (by simp [fDef, vNum, hn])
  have hB := heqs
  simp only [List.all_eq_true] at hB
  have Ed := fun e (he : e ∈ vtSelEq b v) => E e (mem_of_any feqEqb_sound (hB e he))
  simp only [vtSelEq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at Ed
  obtain ⟨d0, d1, d2, d5, d6, d7, d10, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24,
    d25, d26⟩ := Ed
  have hk34 : k < 33 := by omega
  have h2k : 64 ≤ 2 ^ κ := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)
  have hg33 : word 8589934592 0 0 = gen ^ 33 := by
    rw [show (8589934592 : ℕ) = 2 ^ 33 by norm_num, word_two_pow (by norm_num)]
  have L12 : ∀ j < 34, LoadHolds rd p12 j (bitE (off.testBit j)) := fun j hj =>
    vtcs_get (f := fun j => bitE (off.testBit j)) h12 hj
  have L15 : ∀ t ≤ m, LoadHolds rd p15 t (vtcsC15 off k point t) := fun t ht =>
    vtcs_get (f := vtcsC15 off k point) h15 (by omega)
  have L16 : ∀ t ≤ m, LoadHolds rd p16 t (vtcsC16 off k t) := fun t ht =>
    vtcs_get (f := vtcsC16 off k) h16 (by omega)
  have Lz : ∀ j < μ, LoadHolds rd zeta j (point.getD j 0) := fun j hj => by
    rw [List.getD_eq_getElem _ _ hj]; exact hz j hj
  have e0 : σf (.n v) = gen ^ k := by
    rw [show σf (.n v) = memAt rd (σf (.n 9)) b from d0, FR 9 (by omega), h9, memAt_of_loadHolds hbk]
  have e1 : σf (.n (v + 1)) = gen ^ 33 := by rw [show σf (.n (v + 1)) = word 8589934592 0 0 from d1, hg33]
  have e2 : σf (.n (v + 2)) = gen ^ (33 - k) := by rw [d2.1, e1, e0]; exact gen_pow_div (by omega)
  have e5 : σf (.n (v + 5)) = gen ^ m := by
    rw [show σf (.n (v + 5)) = σf (.n 6) * (σf (.n v))⁻¹ from d5, FR 6 (by omega), h6, e0]
    exact gen_pow_div hkμ
  have e6 : σf (.n (v + 6)) = gen ^ 33 := by rw [show σf (.n (v + 6)) = word 8589934592 0 0 from d6, hg33]
  have e7 : σf (.n (v + 7)) = gen ^ (33 - m) := by rw [d7.1, e6, e5]; exact gen_pow_div (by omega)
  have e10 : σf (.n (v + 10)) = zeta * gen ^ k := by
    rw [show σf (.n (v + 10)) = σf (.n 5) * σf (.n v) from d10, FR 5 (by omega), h5, e0]
  have e12 : σf (.n (v + 12)) = p12 := by
    have := d12 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
    simp only [FItem.sets, FItem.vals, hintCells, List.getElem_cons_zero, List.map_cons, List.map_nil] at this
    rw [this]; simp [vtSelHv]
  have e15 : σf (.n (v + 15)) = p15 := by
    have := d15 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
    simp only [FItem.sets, FItem.vals, hintCells, List.getElem_cons_zero, List.map_cons, List.map_nil] at this
    rw [this]; simp [vtSelHv]
  have e16 : σf (.n (v + 16)) = p16 := by
    have := d16 0 (by show 0 < 1; omega) (by show 0 < 1; omega)
    simp only [FItem.sets, FItem.vals, hintCells, List.getElem_cons_zero, List.map_cons, List.map_nil] at this
    rw [this]; simp [vtSelHv]
  have e14 : σf (.n (v + 14)) = p12 * gen ^ k := by
    rw [show σf (.n (v + 14)) = σf (.n (v + 12)) * σf (.n v) from d14, e12, e0]
  have e17 : σf (.n (v + 17)) = 1 := by rw [show σf (.n (v + 17)) = word 1 0 0 from d17, word_one]
  have e18 : σf (.n (v + 18)) = 1 := by rw [show σf (.n (v + 18)) = word 1 0 0 from d18, word_one]
  have e20 : σf (.n (v + 20)) = word 1 0 0 + gen ^ m := by
    rw [show σf (.n (v + 20)) = σf (.n (v + 19)) + σf (.n (v + 5)) from d20,
      show σf (.n (v + 19)) = word 1 0 0 from d19, e5]
  have e21 : σf (.n (v + 21)) = 1 := by rw [show σf (.n (v + 21)) = word 1 0 0 from d21, word_one]
  have e22 : σf (.n (v + 22)) = p15 * gen ^ m := by
    rw [show σf (.n (v + 22)) = σf (.n (v + 15)) * σf (.n (v + 5)) from d22, e15, e5]
  have e24 : σf (.n (v + 24)) = p16 * gen ^ m := by
    rw [show σf (.n (v + 24)) = σf (.n (v + 16)) * σf (.n (v + 5)) from d24, e16, e5]
  have M15 : LoadHolds rd (p15 * gen ^ m) 0 (vtcsC15 off k point m) :=
    loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact L15 m le_rfl)
  have M16 : LoadHolds rd (p16 * gen ^ m) 0 (vtcsC16 off k m) :=
    loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact L16 m le_rfl)
  have e23 : σf (.n (v + 23)) = vtcsC15 off k point m := by
    rw [show σf (.n (v + 23)) = memAt rd (σf (.n (v + 22))) 0 from d23, e22, memAt_of_loadHolds M15]
  have e25 : σf (.n (v + 25)) = gen ^ off := by
    rw [show σf (.n (v + 25)) = memAt rd (σf (.n (v + 24))) 0 from d25, e24, memAt_of_loadHolds M16]
    exact vtcs_goff hkμ hoff hal
  have e26 : σf (.n (v + 26)) = gen ^ off := by
    rw [show σf (.n (v + 26)) = memAt rd (σf (.n 128)) b from d26, FR 128 (by omega), h128,
      memAt_of_loadHolds hoffL]
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl ?_
  · rw [hobs]
    intro o ho
    simp only [vtSelOb, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [IOb.Holds, Ob.Holds]
      rw [FR 9 (by omega), h9]; exact ⟨hbk.1, isSome_of_loadHolds hbk⟩
    · simp only [IOb.Holds, Ob.Holds]
      rw [e0, e2]
      have a := low_gen_pow hlow (i := k) (by omega)
      have c := low_gen_pow hlow (i := 33 - k) (by omega)
      exact ⟨gen_pow_ne_zero _, a.1, a.2, c.1, c.2⟩
    · simp only [IOb.Holds, Ob.Holds]; rw [e0]; exact gen_pow_ne_zero _
    · simp only [IOb.Holds, Ob.Holds]
      rw [e5, e7]
      have a := low_gen_pow hlow (i := m) (by omega)
      have c := low_gen_pow hlow (i := 33 - m) (by omega)
      exact ⟨gen_pow_ne_zero _, a.1, a.2, c.1, c.2⟩
    · simp only [IOb.Holds, Ob.Holds]
      rw [FR 128 (by omega), h128]; exact ⟨hoffL.1, isSome_of_loadHolds hoffL⟩
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]
      rw [e15, e17]; simpa [vtcsC15] using L15 0 (by omega)
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]
      rw [e16, e18]; simpa [vtcsC16] using L16 0 (by omega)
    · simp only [IOb.Holds]
      rw [e20]
      refine ⟨vtcs_isInK_one_add m, fun hne => ?_⟩
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · exfalso; apply hne; rw [h0, word_one, pow_zero]; exact e_add_self 1
        · exact h0
      simp only [List.map_cons, List.map_nil]
      rw [e21, e5, e14, e15, e10, e16, FR 10 (by omega), h10, e0]
      refine sel_complete hsok hm0 rfl fun j hj => ⟨bitE (off.testBit (k + j)), vtcsC15 off k point j,
        point.getD (k + j) 0, vtcsC16 off k j, gen ^ 2 ^ (k + j), ?_, vtcs_bitE_mul _, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact loadHolds_gen_pow_mul.mpr (loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact L12 _ (by omega)))
      · exact loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact L15 j (by omega))
      · exact loadHolds_gen_pow_mul.mpr (loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact Lz _ (by omega)))
      · refine loadHolds_gen_pow_mul.mpr ?_
        have := L15 (j + 1) (by omega)
        rwa [vtcsC15, Finset.prod_range_succ, ← vtcsC15] at this
      · exact loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact L16 j (by omega))
      · rw [← pow_add]
        exact loadHolds_gen_pow_mul.mpr (by rw [Nat.add_zero]; exact hsq _ (by omega))
      · refine loadHolds_gen_pow_mul.mpr ?_
        have := L16 (j + 1) (by omega)
        rwa [vtcsC16, Finset.prod_range_succ, ← vtcsC16] at this
    · simp only [IOb.Holds, Ob.Holds]; rw [e22]; exact ⟨M15.1, isSome_of_loadHolds M15⟩
    · simp only [IOb.Holds, Ob.Holds]; rw [e24]; exact ⟨M16.1, isSome_of_loadHolds M16⟩
    · simp only [IOb.Holds, Ob.Holds]
      rw [FR 128 (by omega), h128]; exact ⟨hoffL.1, isSome_of_loadHolds hoffL⟩
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]
      rw [e25, e26]; exact e_add_self _
  · intro σ' h
    rw [h]
    refine ⟨?_, e0, e12, e15, e16⟩
    rw [e23, eqAbove_prod (M := μ) point rfl]
    rfl

end
end LeanVM.Guest.B1.VerifySub
