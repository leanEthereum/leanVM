/-
  LeanVM.Guest.B1.Main.MainCoreThm

  `main_core`: what holds of `main`'s honest valuation.
-/

module

public import LeanVM.Guest.B1.Main.MainCore

/-!
# `main`'s honest valuation holds

The evaluated block's equations (`Fwd.ev_spec`) give the oracle's values and the products, sums
and constants the proof reads; the atoms hold block by block (`atoms_holds_stores`): the range
checks and the counts' `assert_gpow` on the memory defined below the counts (`rc_side`), the reads
of the last running count, the
published DA digest and the header, the equality checks on the honest words; then the stores:
the byte table, the first running count, the own DA digest (the checked claim's, by its chain
`chain_final`, or zeros) and the leaf's deferred claim.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd

@[expose] public section

set_option maxRecDepth 20000 in
/-- **`main`'s honest valuation holds** on a memory defined below `M` words, at least `17`, holding
`main`'s words, its counts below `M`. -/
theorem main_core {rd : Reader} {m : MainIn} {M : ℕ} (hl : Sig.MemOK rd M) (hM : 17 ≤ M)
    (hb : MainBounds M m)
    (hm : MainMem rd m) : MVals rd (mσ rd m) m := by
  have hok := mainc_ok
  unfold mainCOk at hok
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hok
  obtain ⟨⟨c', hchk⟩, hside⟩ := hok
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = mσ rd m := ⟨_, rfl⟩
  rw [← hσ]
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (mOrc m) mFlatE [] hchk
  have hG : ∀ s ∈ mFlatE, GoodS rd mStores (mOrc m) σ s := fun s hs => by rw [hσ]; exact hgs s hs
  have hgA : ∀ a ∈ atomsIn mFlat, Good rd mStores (mOrc m) σ a := fun a ha =>
    hG _ (atom_mem_of_atomsIn' ha)
  -- the located values
  have hD : ∀ a ∈ mDefAtoms, Good rd mStores (mOrc m) σ a := by
    intro a ha
    obtain ⟨b, hb', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp mDefAtoms_ok a ha)
    rw [atomEqb_sound he]
    exact hG _ (atom_mem_of_atomsIn' hb')
  have horc : ∀ j ∈ mOrcIdx, σ (.n j) = mOrc m j := by
    intro j hj
    obtain ⟨s, hs, hv⟩ := mOrcIdx_defs j hj
    obtain ⟨s', hs', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp mOrcStmts_ok s hs)
    rw [← stmtEqb_sound he] at hv
    exact goodS_defs (hG s' hs') _ hv
  have hO : ∀ {j : ℕ}, j ∈ mOrcIdx → σ (.n j) = mOrc m j := fun hj => horc _ hj
  have gM : ∀ (d x y : ℕ), x < d → y < d → Atom.mul (.n d) (.n x) (.n y) ∈ mDefAtoms →
      σ (.n d) = σ (.n x) * σ (.n y) := fun d x y hx hy h => good_mul' hx hy (hD _ h)
  have gA : ∀ (d x y : ℕ), Atom.add (.n d) (.n x) (.n y) ∈ mDefAtoms →
      σ (.n d) = σ (.n x) + σ (.n y) := fun d x y h => hD _ h
  have gC : ∀ (d : ℕ) (c : E), Atom.const (.n d) c ∈ mDefAtoms → σ (.n d) = c :=
    fun d c h => hD _ h
  have one : ∀ d, Atom.const (.n d) (word 1 0) ∈ mDefAtoms → σ (.n d) = 1 := fun d h => by
    rw [gC d _ h, word_one]
  have two : ∀ d, Atom.const (.n d) (word 2 0) ∈ mDefAtoms → σ (.n d) = gen := fun d h => by
    rw [gC d _ h, word_gen]
  have gd : ∀ d x y e, Atom.const (.n x) (word 1 0) ∈ mDefAtoms →
      Atom.add (.n d) (.n x) (.n y) ∈ mDefAtoms → σ (.n y) = gen ^ e → σ (.n d) = 1 + gen ^ e :=
    fun d x y e hx hd hy => by rw [gA d x y hd, one x hx, hy]
  -- the counts
  have v0 : σ (.n 0) = gen ^ m.nlx := by rw [hO (by decide)]; rfl
  have v1 : σ (.n 1) = gen ^ m.nxd := by rw [hO (by decide)]; rfl
  have v2 : σ (.n 2) = gen ^ m.nrx := by rw [hO (by decide)]; rfl
  have v3 : σ (.n 3) = gen ^ m.nls := by rw [hO (by decide)]; rfl
  have v4 : σ (.n 4) = gen ^ m.nsd := by rw [hO (by decide)]; rfl
  have v5 : σ (.n 5) = gen ^ m.nrs := by rw [hO (by decide)]; rfl
  have v6 : σ (.n 6) = gen ^ m.nc := by rw [hO (by decide)]; rfl
  have v7 : σ (.n 7) = gen ^ m.nd := by rw [hO (by decide)]; rfl
  have v40 : σ (.n 22) = gen ^ (m.nlx + m.nxd) := by
    rw [gM 22 0 1 (by norm_num) (by norm_num) (by decide +kernel), v0, v1, pow_add]
  have v41 : σ (.n 23) = gen ^ (m.nls + m.nsd) := by
    rw [gM 23 3 4 (by norm_num) (by norm_num) (by decide +kernel), v3, v4, pow_add]
  have v42 : σ (.n 24) = gen ^ m.total := by
    rw [gM 24 22 23 (by norm_num) (by norm_num) (by decide +kernel), v40, v41, ← pow_add]; rfl
  have v51 : σ (.n 30) = gen ^ (4 * (m.nlx + m.nxd)) := by
    rw [gM 30 29 29 (by norm_num) (by norm_num) (by decide +kernel),
      gM 29 22 22 (by norm_num) (by norm_num) (by decide +kernel), v40, ← pow_add, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have v54 : σ (.n 33) = gen ^ (4 * (m.nls + m.nsd)) := by
    rw [gM 33 32 32 (by norm_num) (by norm_num) (by decide +kernel),
      gM 32 23 23 (by norm_num) (by norm_num) (by decide +kernel), v41, ← pow_add, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have v67 : σ (.n 46) = m.a117 * gen ^ (m.nlx + m.nxd) := by
    rw [gM 46 45 22 (by norm_num) (by norm_num) (by decide +kernel), v40, hO (by decide)]
    simp [mOrc]
  have vDa : σ (.n 364) = m.aDa := by rw [hO (by decide)]; simp [mOrc]
  have v409 : σ (.n 398) = m.a409 := by rw [hO (by decide)]; simp [mOrc]
  have vpick : σ (.n 405) = gen ^ m.pick := by rw [hO (by decide)]; simp [mOrc]
  have v384 : σ (.n 363) = gen ^ (2 * (m.nc + 1)) := by
    rw [gM 363 362 362 (by norm_num) (by norm_num) (by decide +kernel),
      gM 362 6 361 (by norm_num) (by norm_num) (by decide +kernel), v6,
      two 361 (by decide +kernel), ← pow_succ, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have v387 : σ (.n 366) = m.aDa * gen ^ (2 * m.nc) := by
    rw [gM 366 364 365 (by norm_num) (by norm_num) (by decide +kernel),
      gM 365 6 6 (by norm_num) (by norm_num) (by decide +kernel), vDa, v6, ← pow_add, two_mul]
  have v389 : σ (.n 368) = gen ^ m.nd + gen := by
    rw [gA 368 7 367 (by decide +kernel), v7, two 367 (by decide +kernel)]
  have v415 : σ (.n 382) = gen ^ (2 * m.nc) := by
    rw [gM 382 6 6 (by norm_num) (by norm_num) (by decide +kernel), v6, ← pow_add, two_mul]
  have v421 : σ (.n 388) = gen ^ (24 * m.nc) := by
    rw [gM 388 387 387 (by norm_num) (by norm_num) (by decide +kernel),
      gM 387 386 386 (by norm_num) (by norm_num) (by decide +kernel),
      gM 386 385 385 (by norm_num) (by norm_num) (by decide +kernel),
      gM 385 384 6 (by norm_num) (by norm_num) (by decide +kernel),
      gM 384 6 6 (by norm_num) (by norm_num) (by decide +kernel), v6, ← pow_add, ← pow_add,
      ← pow_add, ← pow_add, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have v427 : σ (.n 394) = gen ^ (24 * m.nc) := by
    rw [gM 394 393 393 (by norm_num) (by norm_num) (by decide +kernel),
      gM 393 392 392 (by norm_num) (by norm_num) (by decide +kernel),
      gM 392 391 391 (by norm_num) (by norm_num) (by decide +kernel),
      gM 391 390 6 (by norm_num) (by norm_num) (by decide +kernel),
      gM 390 6 6 (by norm_num) (by norm_num) (by decide +kernel), v6, ← pow_add, ← pow_add,
      ← pow_add, ← pow_add, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have v430 : σ (.n 397) = gen ^ (m.nc + 1) := by
    rw [gM 397 6 396 (by norm_num) (by norm_num) (by decide +kernel), v6,
      two 396 (by decide +kernel), pow_succ]
  have v432 : σ (.n 399) = gen ^ (m.nrx + m.nrs) := by
    rw [gM 399 2 5 (by norm_num) (by norm_num) (by decide +kernel), v2, v5, pow_add]
  have v436 : σ (.n 403) = m.a409 * gen ^ m.nc := by
    rw [gM 403 398 6 (by norm_num) (by norm_num) (by decide +kernel), v409, v6]
  have v445 : σ (.n 412) = (gen ^ m.pick + gen ^ m.nc) * (gen ^ m.nd + 1) := by
    rw [gM 412 409 411 (by norm_num) (by norm_num) (by decide +kernel),
      gA 409 405 6 (by decide +kernel), gA 411 7 410 (by decide +kernel), vpick, v6, v7,
      one 410 (by decide +kernel)]
  have v448 : σ (.n 415) = m.aDa * gen ^ (2 * m.pick) := by
    rw [gM 415 364 414 (by norm_num) (by norm_num) (by decide +kernel),
      gM 414 405 405 (by norm_num) (by norm_num) (by decide +kernel), vDa, vpick, ← pow_add,
      two_mul]
  have v451 : σ (.n 418) = gen ^ m.nc + 1 := by
    rw [gA 418 6 417 (by decide +kernel), v6, one 417 (by decide +kernel)]
  have v480 : σ (.n 449) = 1 := one 449 (by decide +kernel)
  have v484 : σ (.n 453) = gen := by
    rw [gM 453 451 452 (by norm_num) (by norm_num) (by decide +kernel),
      one 451 (by decide +kernel), two 452 (by decide +kernel), one_mul]
  -- the reads
  have rdL : ∀ d p o v, Atom.load (.n d) (.n p) o ∈ mDefAtoms →
      Atom.load (.n d) (.n p) o ∉ mStoresL → LoadHolds rd (σ (.n p)) o v → σ (.n d) = v := by
    intro d p o v h hn hv
    rcases (hD _ h : Good rd mStores (mOrc m) σ (.load _ _ _)) with h | h
    · exact absurd (by rw [mStores_eq] at h; exact h) hn
    · rw [h, rdAt_of_load hv]
  have r437 : σ (.n 404) = gen ^ m.total :=
    rdL 404 403 0 _ (by decide +kernel) (by simp [mStoresL]) (by rw [v436]; exact hm.wN)
  have r476 : σ (.n 445) = (digestHalves m.dap).1 :=
    rdL 445 415 0 _ (by decide +kernel) (by simp [mStoresL]) (by
      rw [v448]; exact hm.dap 0 (by simp [digestCells]))
  have r477 : σ (.n 446) = (digestHalves m.dap).2 :=
    rdL 446 415 1 _ (by decide +kernel) (by simp [mStoresL]) (by
      rw [v448]; exact hm.dap 1 (by simp [digestCells]))
  have r481 : σ (.n 450) = (digestHalves m.sdg).1 :=
    rdL 450 449 0 _ (by decide +kernel) (by simp [mStoresL]) (by rw [v480]; exact hm.h0)
  have r485 : σ (.n 454) = (digestHalves m.sdg).2 :=
    rdL 454 453 0 _ (by decide +kernel) (by simp [mStoresL]) (by rw [v484]; exact hm.h1)
  -- the carried tags
  have htags : lxTagsV.map σ = lxTagWords := by
    apply List.ext_getElem (by simp [lxTagsV, lxTagWords, lxTagVals]; decide)
    intro j h1 h2
    have hj : j < 51 := by simpa [lxTagsV] using h1
    simp only [lxTagsV, List.getElem_map, List.getElem_range, lxTagWords]
    rw [gC (304 + j) _ (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [lxTagWords] using h2)]
    rfl
  -- the side conditions
  have hS : ∀ a ∈ atomsIn mFlat, a ∉ mStores → needsSide a = true →
      a.Holds rd σ ∨ Side rd mStores σ a := by
    intro a ha hnS hns
    right
    have hok := hside a ha
    rw [hns] at hok
    simp only [Bool.true_eq_false, false_or] at hok
    have hg := hgA a ha
    cases a with
    | rangeCheck x y t1 t2 k =>
      simp only [mSideOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨hp, hx⟩, hk⟩, hlt⟩ := hok
      rw [hx, hk] at hg ⊢
      rw [hk] at hlt
      simp only [rcPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hg ⊢ <;> rw [h2] at hlt
      · exact rc_side hl v6 (by rw [gC 14 (word 65536 0) (by decide +kernel), word_g16]) hb.nc
          (by omega) hlt hg
      · exact rc_side hl v7 (by rw [gC 18 (word 2 0) (by decide +kernel), word_g1]) hb.nd
          (by omega) hlt hg
      · exact rc_side hl vpick v6 hb.pick (by have := hb.nc; omega) hlt hg
    | load d p o =>
      simp only [mSideOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨hd, hp⟩, hl'⟩ := hok
      simp only [mLoadOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons,
        Prod.mk.injEq, List.not_mem_nil, or_false] at hl'
      rw [hd, hp] at hnS ⊢
      simp only [Side]
      simp only [hnS, ↓reduceIte]
      rcases hl' with (((⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩ |
          ⟨e1, e2, rfl⟩) | hs) | hs) | hs
      · rw [e2, v436]; exact ⟨hm.wN.1, by rw [hm.wN.2]; rfl⟩
      · rw [e2, v448]
        have h := hm.dap 0 (by simp [digestCells])
        exact ⟨h.1, by rw [h.2]; rfl⟩
      · rw [e2, v448]
        have h := hm.dap 1 (by simp [digestCells])
        exact ⟨h.1, by rw [h.2]; rfl⟩
      · rw [e2, v480]; exact ⟨hm.h0.1, by rw [hm.h0.2]; rfl⟩
      · rw [e2, v484]; exact ⟨hm.h1.1, by rw [hm.h1.2]; rfl⟩
      all_goals exfalso; apply hnS; rw [mStores_eq]
      · obtain ⟨⟨e1, e2⟩, e3⟩ := hs
        rw [e1, e2]
        simp only [mStoresL, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inl (Or.inl ⟨o, e3, rfl⟩))
      · rcases hs with ⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩ | ⟨e1, e2, rfl⟩ |
          ⟨e1, e2, rfl⟩ <;> rw [e1, e2] <;> simp [mStoresL]
      · obtain ⟨e1, ⟨e3, e2⟩ | ⟨rfl, e2⟩⟩ := hs
        · rw [e1, e2]
          simp only [mStoresL, List.mem_append, List.mem_map, List.mem_range]
          exact Or.inl (Or.inr ⟨o, e3, rfl⟩)
        · rw [e1, e2]; simp [mStoresL]
    | touch t p =>
      simp only [mSideOk, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons, Prod.mk.injEq,
        List.not_mem_nil, or_false] at hok
      obtain ⟨⟨-, hp⟩, hl'⟩ := hok
      rw [hp]
      simp only [Side]
      rcases hl' with ⟨-, e2⟩ | ⟨-, e2⟩ | ⟨-, e2⟩ | ⟨-, e2⟩ | ⟨-, e2⟩ | ⟨-, e2⟩ | ⟨-, e2⟩
      · rw [e2, v0]; exact ⟨gen_pow_isInK _, by rw [gpow_mul_zero]; exact hl _ hb.lx⟩
      · rw [e2, v1]; exact ⟨gen_pow_isInK _, by rw [gpow_mul_zero]; exact hl _ hb.xd⟩
      · rw [e2, v2]; exact ⟨gen_pow_isInK _, by rw [gpow_mul_zero]; exact hl _ hb.rx⟩
      · rw [e2, v3]; exact ⟨gen_pow_isInK _, by rw [gpow_mul_zero]; exact hl _ hb.ls⟩
      · rw [e2, v4]; exact ⟨gen_pow_isInK _, by rw [gpow_mul_zero]; exact hl _ hb.sd⟩
      · rw [e2, v5]; exact ⟨gen_pow_isInK _, by rw [gpow_mul_zero]; exact hl _ hb.rs⟩
      · rw [e2, v42]; exact ⟨gen_pow_isInK _, by rw [gpow_mul_zero]; exact hl _ hb.total⟩
    | assertEq x y =>
      simp only [mSideOk, decide_eq_true_eq, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hok
      simp only [Side]
      rw [e_add_eq_zero_iff]
      rcases hok with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [r437, v42]
      · rw [v445, gC 413 (word 0 0) (by decide +kernel), word_zero]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb.nd with h | h
        · rw [h, pow_zero, show (1 : E) + 1 = 0 from e_add_eq_zero_iff.mpr rfl, mul_zero]
        · rw [hb.pickD h, show gen ^ m.nc + gen ^ m.nc = 0 from e_add_eq_zero_iff.mpr rfl,
            zero_mul]
      · rw [r481, hO (by decide)]; simp [mOrc]
      · rw [r485, hO (by decide)]; simp [mOrc]
    | _ => simp [mSideOk] at hok
  -- the stores' words
  have hbyte : ∀ v < 256, σ (.n (48 + v)) = word v 0 := by
    intro v hv
    obtain ⟨b, hb', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp mByte_ok v (List.mem_range.mpr hv))
    have := hG _ (atom_mem_of_atomsIn' hb')
    rw [← atomEqb_sound he] at this
    exact this
  have hleafc : ∀ k < 23, σ (.n (420 + k)) = 0 := by
    intro k hk
    obtain ⟨b, hb', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp mLeafC_ok k (List.mem_range.mpr hk))
    have := hG _ (atom_mem_of_atomsIn' hb')
    rw [← atomEqb_sound he] at this
    rw [show σ (.n (420 + k)) = word 0 0 from this, word_zero]
  have hzc : ∀ d, Atom.const (.n d) (word 0 0) ∈ atomsIn mDaZ → σ (.n d) = 0 := by
    intro d h
    have h' := atom_mem_of_atomsIn' h
    have hs : Stmt.atom (.const (.n d) (word 0 0)) ∈ mFlat := by
      clear * - h'; simp only [mFlat, List.mem_append]; tauto
    have := hgA _ (mem_atomsIn' hs)
    exact (show σ (.n d) = word 0 0 from this).trans word_zero
  -- the blocks
  have hsubF : ∀ {P : List Stmt}, (∀ s ∈ P, s ∈ mFlat) → ∀ a ∈ atomsIn P, a ∈ atomsIn mFlat :=
    fun hP a ha => mem_atomsIn' (hP _ (atom_mem_of_atomsIn' ha))
  obtain ⟨sB, sDa, sDaZ, sLf, sAg⟩ := mStoresIn
  have blk : ∀ {P : List Stmt}, (∀ s ∈ P, s ∈ mFlat) →
      ((∀ a ∈ atomsIn P, a ∉ mStores → a.Holds rd σ) → ∀ a ∈ atomsIn P, a ∈ mStores →
        a.Holds rd σ) → ∀ a ∈ atomsIn P, a.Holds rd σ := by
    intro P hP hst
    have hsub := hsubF hP
    exact atoms_holds_stores (S := mStores) (fun a ha => hgA a (hsub a ha))
      (fun a ha hnS hns => hS a (hsub a ha) hnS hns) hst
  have hB1 : ∀ a ∈ atomsIn (mPre ++ mMid ++ mPost), a.Holds rd σ := by
    refine blk (fun s hs => by
      clear * - hs; simp only [List.mem_append] at hs; simp only [mFlat, List.mem_append]; tauto)
      (fun _ a ha haS => ?_)
    have := mem_storesIn sB ha haS
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at this
    rcases this with ⟨v, hv, rfl⟩ | rfl
    · show LoadHolds rd (σ (.n 47)) v (σ (.n (48 + v)))
      rw [hO (by decide), hbyte v hv]
      have := hm.bytes v (by simpa using hv)
      simpa [mOrc] using this
    · show LoadHolds rd (σ (.n 398)) 0 (σ (.n 399))
      rw [v409, v432]; exact hm.w0
  have mB1 : ∀ {P : List Stmt}, (∀ s ∈ P, s ∈ mPre ++ mMid ++ mPost) →
      ∀ a ∈ atomsIn P, a.Holds rd σ := fun hP a ha => hB1 a (mem_atomsIn' (hP _ (atom_mem_of_atomsIn' ha)))
  have hDa : m.nd = 1 → ∀ a ∈ atomsIn mDa, a.Holds rd σ := by
    intro h1
    have hl4 := hb.daR h1
    have hR : ∀ i ∈ [369, 370, 371], σ (.n i) = m.daR.getD (i - 369) 0 := by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> rw [hO (by decide)] <;> simp [mOrc]
    have hRl : [σ (.n 369), σ (.n 370), σ (.n 371), σ (.n 373)] = m.daR ++ [0] := by
      rw [hR 369 (by simp), hR 370 (by simp), hR 371 (by simp),
        gC 373 (word 0 0) (by decide +kernel), word_zero]
      match hd : m.daR, hl4 with
      | [a, b, c], _ => rfl
    refine blk (fun s hs => by clear * - hs; simp only [mFlat, List.mem_append]; tauto)
      (fun h1' a ha haS => ?_)
    · have hA' : ∀ b ∈ noStores mDa, b.Holds rd σ := fun b hb' =>
        h1' b (List.mem_filter.mp hb').1 (by simpa using (List.mem_filter.mp hb').2)
      obtain ⟨hsp, ho0, ho1⟩ := daSpec_ok
      have hd := chain_final hsp rfl hA' (pre := []) (n := 0) rfl
        (fun c => (cellsOfState_zero false c).symm)
      have hv : (daSpec.vals σ).take (daSpec.len / 16) =
          [σ (.n 369), σ (.n 370), σ (.n 371), σ (.n 373)] := by
        simp [daSpec, pairSpec, ChainSpec.vals, srcVal]
      rw [hv, List.nil_append, hRl, ho0, ho1] at hd
      have hown := hm.own
      simp only [MainIn.ownDa, h1, ↓reduceIte] at hown
      have := mem_storesIn sDa ha haS
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl
      · show LoadHolds rd (σ (.n 366)) 0 (σ (.n 378))
        have e := congrArg Prod.fst hd
        simp only at e
        rw [v387, e]; exact hown 0 (by simp [digestCells])
      · show LoadHolds rd (σ (.n 366)) 1 (σ (.n 379))
        have e := congrArg Prod.snd hd
        simp only at e
        rw [v387, e]; exact hown 1 (by simp [digestCells])
  have hDaZ : m.nd ≠ 1 → ∀ a ∈ atomsIn mDaZ, a.Holds rd σ := by
    intro h1
    refine blk (fun s hs => by clear * - hs; simp only [mFlat, List.mem_append]; tauto)
      (fun _ a ha haS => ?_)
    have hown := hm.own
    simp only [MainIn.ownDa, h1, ↓reduceIte] at hown
    obtain ⟨c0, c1⟩ := mDaZC_ok
    have z0 := hzc 380 (atomEqb_sound (List.any_eq_true.mp c0).choose_spec.2 ▸
      (List.any_eq_true.mp c0).choose_spec.1)
    have z1 := hzc 381 (atomEqb_sound (List.any_eq_true.mp c1).choose_spec.2 ▸
      (List.any_eq_true.mp c1).choose_spec.1)
    have := mem_storesIn sDaZ ha haS
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl
    · show LoadHolds rd (σ (.n 366)) 0 (σ (.n 380))
      rw [v387, z0]; exact hown 0 (by simp)
    · show LoadHolds rd (σ (.n 366)) 1 (σ (.n 381))
      rw [v387, z1]; exact hown 1 (by simp)
  have hLeaf : m.nc = 0 → ∀ a ∈ atomsIn mLeaf, a.Holds rd σ := by
    intro h0
    refine blk (fun s hs => by clear * - hs; simp only [mFlat, List.mem_append]; tauto)
      (fun _ a ha haS => ?_)
    have := mem_storesIn sLf ha haS
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at this
    rcases this with ⟨k, hk, rfl⟩ | rfl
    · show LoadHolds rd (σ (.n 416)) k (σ (.n (420 + k)))
      rw [hO (by decide), hleafc k hk]
      have := hm.leaf h0 k (by simp; omega)
      rw [List.getElem_append_left (by simp; omega), List.getElem_replicate] at this
      simpa [mOrc] using this
    · show LoadHolds rd (σ (.n 416)) 23 (σ (.n 419))
      rw [hO (by decide), hO (by decide)]
      have := hm.leaf h0 23 (by simp)
      simpa [mOrc] using this
  have hAgg : ∀ a ∈ atomsIn mAgg, a.Holds rd σ :=
    blk (fun s hs => by clear * - hs; simp only [mFlat, List.mem_append]; tauto)
      (fun _ a ha haS => by have := mem_storesIn sAg ha haS; simp at this)
  have v465 : σ (.n 444) = m.et * word 133823759239872512 0 := by
    rw [gM 444 28 443 (by norm_num) (by norm_num) (by decide +kernel),
      gC 443 (word 133823759239872512 0) (by decide +kernel), hO (by decide)]
    simp [mOrc]
  exact ⟨mB1 (by intro s hs; clear * - hs; simp only [List.mem_append]; tauto),
    mB1 (by intro s hs; clear * - hs; simp only [List.mem_append]; tauto),
    mB1 (by intro s hs; clear * - hs; simp only [List.mem_append]; tauto),
    hDa, hDaZ, hLeaf, hAgg, horc, v40, v41, v42, v51, v54,
    gd 40 39 1 _ (by decide +kernel) (by decide +kernel) v1, one 41 (by decide +kernel),
    gd 43 42 4 _ (by decide +kernel) (by decide +kernel) v4, one 44 (by decide +kernel),
    v67,
    gd 356 355 2 _ (by decide +kernel) (by decide +kernel) v2, one 357 (by decide +kernel),
    gd 359 358 5 _ (by decide +kernel) (by decide +kernel) v5, one 360 (by decide +kernel),
    v384, v387, v389, v415, v421, v427, v430, v432,
    gd 401 400 6 _ (by decide +kernel) (by decide +kernel) v6, one 402 (by decide +kernel),
    v436, v448, v451, v465, r476, r477, v480, v484, htags⟩

end
end LeanVM.Guest.B1.Main
