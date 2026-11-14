/-
  LeanVM.Guest.B1.VerifySub.CLoads

  `verify_sub`'s loads on an honest child read the caller's words or its own buffers.
-/

module

public import LeanVM.Guest.B1.VerifySub.CSig

/-!
# The loads' regions

`vs_loads`: on the honest valuation of an honest child, every load of `verify_sub`'s body reads
an address of the caller's words `Lin` (the exponent table, the deferred claim's cells) or of its
own buffers: the stream (the announced words, the ring map's nonce, `col_eval_words`),
`table_rows`, `dims_g`, `kappa_base`, `fp_w`, the ring map's challenges, `c_table`,
`claim_pool`, `ood_value`, `zeta`, `bc_point`. Every load is one of `vsSidePieces`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

theorem vs_regAt {σ : Val} {p : V} {x off : ℕ} (hp : σ p = ptr x) {R : ℕ → Prop}
    (hR : R (x + off)) : ∃ i, (σ p).limb 0 * addressOfIndex off = addressOfIndex i ∧ R i :=
  ⟨x + off, by rw [hp]; exact Main.addr_ofK x off, hR⟩

theorem vs_ringCoefficients_length (f g : List E) (hf : f.length = 8) (hg : g.length = 8) :
    (ringCoefficients f g).length = 64 := by
  rw [ringCoefficients_eq hf]
  simp [List.length_flatMap, hg]

/-- **Every load reads the caller's words or the own buffers.** -/
theorem vs_loads {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) (b sqE outE : ℕ) {Lin : Main.Layout}
    (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin) (hout : (outE, DeferredBytecodeClaim.cells c.freshClaim) ∈ Lin)
    {outs : List (List E × Main.Layout)} (O : VsOuts S (bases b (vsSizes S.d)) sqE outs)
    {rd : Reader} (hB : Main.MemL rd (bufL b (vsSizes S.d) S.ownW)) :
    ∀ q ∈ vsCPre.filterMap Stmt.loadS, ∃ i,
      (vsσ rd (vsW (bases b (vsSizes S.d)) outs) (vsArgs seed c sqE outE) q.1).limb 0 *
          addressOfIndex q.2 = addressOfIndex i ∧
        (Main.RegionL Lin i ∨ Main.RegionL (bufL b (vsSizes S.d) S.ownW) i) := by
  set bs := bases b (vsSizes S.d) with hbs
  set w := vsW bs outs with hw
  set σ := vsσ rd w (vsArgs seed c sqE outE) with hσ
  have hl : (vsArgs seed c sqE outE).length = 6 := rfl
  -- the regions
  have hown : ∀ i < 15, ∀ k < (S.ownW.getD i []).length,
      Main.RegionL Lin (bs.getD i 0 + k) ∨ Main.RegionL (bufL b (vsSizes S.d) S.ownW) (bs.getD i 0 + k) :=
    fun i hi k hk ↦ Or.inr (subOf_region (S.sub_own b hi) (Nat.le_add_right _ _) (by
      show _ < vb bs i + _; simp only [vb]; omega))
  have hlin : ∀ x xs, (x, xs) ∈ Lin → ∀ k < xs.length,
      Main.RegionL Lin (x + k) ∨ Main.RegionL (bufL b (vsSizes S.d) S.ownW) (x + k) :=
    fun x xs h k hk ↦ Or.inl ⟨(x, xs), h, by simp, by simp; omega⟩
  have hstr : ∀ k < (vsStreamW c.proof.stream).length,
      Main.RegionL Lin (bs.getD 1 0 + k) ∨ Main.RegionL (bufL b (vsSizes S.d) S.ownW) (bs.getD 1 0 + k) :=
    hown 1 (by norm_num)
  have pa : ∀ {i a : ℕ}, i < 15 → vsAllocVars.getD i 0 = a → σ (.n a) = ptr (bs.getD i 0) :=
    fun hi ha ↦ by
      rw [hσ, vs_w hl (by rw [← ha]; exact vs_allocVars_w _ (vsAllocVars_idx _ hi).1)]
      exact vsW_a hi ha
  have pr : ∀ {j k a : ℕ}, j < 16 → k < (vsRetVars.getD j []).length →
      (vsRetVars.getD j []).getD k 0 = a → a ∈ vsWVars → σ (.n a) = (outs.getD j ([], [])).1.getD k 0 :=
    fun hj hk ha hw' ↦ by rw [hσ, vs_w hl hw']; exact vsW_r hj hk ha
  -- the stream's length
  have hSl : 13 + S.xsG.length + S.xsT.length + S.xsK.length + 1 ≤ (vsStreamW c.proof.stream).length := by
    rw [S.stream_eq hbl]
    simp only [List.length_append, S.sizeWords_length, List.length_cons, List.length_nil]
    omega
  have hxl := (S.H_run hbl).2.2.2
  have hd := S.d_bounds hbl
  obtain ⟨-, -, -, -, hzl, -⟩ := S.gkr_inv hbl
  have hhs := S.hs_lt33 hbl
  have hSl0 := vs_streamW_length c.proof.stream
  have hSl0' : 8192 ≤ (vsStreamW c.proof.stream).length := hSl0
  -- the pointers
  have h64 : σ (.n 64) = gen ^ S.rate := by
    rw [pr (j := 0) (k := 0) (a := 64) (by norm_num) (by decide) rfl (by decide), O.o0]; rfl
  have h72 : σ (.n 72) = gen ^ S.logMem := by
    rw [pr (j := 1) (k := 0) (a := 72) (by norm_num) (by decide) rfl (by decide), O.o1]; rfl
  have hp4 : σ (.n 4) = ptr sqE := vsC_param hl (by norm_num)
  have hp5 : σ (.n 5) = ptr outE := vsC_param hl (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, -, h84, h85, h86⟩ :=
    vs_sizesV (rd := rd) (w := w) (args := vsArgs seed c sqE outE) hl S.hr1 S.hlm1
      (by rw [← h64, hσ, vs_w hl (by decide)]) (by rw [← h72, hσ, vs_w hl (by decide)])
  rw [← hσ] at h84 h85 h86
  have hdims : ReadsAt rd (w 71) (vsDimsW S.logMem S.hs) := by
    rw [hw, vsW_a (i := 3) (a := 71) (by norm_num) rfl]; exact (hB _ (vs_own_mem S b (i := 3) (by norm_num)))
  have hkb : ∀ s < 8, σ (.n (84 + s)) = gen ^ ([0, S.logMem] ++ S.hs).getD s 0 := by
    intro s hs
    rw [← S.kb_pow hbl hs]
    rcases s with _ | _ | t
    · exact h84
    · exact h85
    · rw [show 84 + (t + 2) = 86 + t by omega, h86 t (by omega),
        vs_rdAt_of_load (vs_rdg hdims (k := 1 + t) (by simp [vsDimsW, S.hs_length]; omega))]
      simp only [vsDimsW, List.getD_cons_succ, show 1 + t = t + 1 by omega]
  have h595 : σ (.n 595) = ptr (S.cK bs + S.xsK.length) := by
    rw [pr (j := 11) (k := 5) (a := 595) (by norm_num) (by decide) rfl (by decide), O.o11, vs_ptr_add]
    simp only [capOf, List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
  have h582 : σ (.n 582) = ptr (S.cT bs + (13 + (3 * S.nT + 1))) := by
    rw [pr (j := 10) (k := 9) (a := 582) (by norm_num) (by decide) rfl (by decide), O.o10, vs_ptr_add]
    simp only [Tables.VtHonest.retsH, Fs.squeeze, capOf, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
    rw [show ofK (addressOfIndex (S.vtB bs sqE (S.leavesB (outs.take 10))).cur) = ptr (S.cT bs)
      from rfl, mul_assoc, mul_assoc, ← pow_succ', ← pow_add]
    rfl
  have hcl : (DeferredBytecodeClaim.cells c.freshClaim).length = 24 := by
    rw [S.fresh_eq hbl]
    simp [DeferredBytecodeClaim.cells, S.slots_length, hzl]
    omega
  have hcT : S.cT bs = bs.getD 1 0 + (13 + S.xsG.length) := by
    simp only [ChildSegs.cT, ChildSegs.cG, vb]; omega
  have hcK : S.cK bs = bs.getD 1 0 + (13 + S.xsG.length + S.xsT.length) := by
    simp only [ChildSegs.cK, ChildSegs.cT, ChildSegs.cG, vb]; omega
  have own : ∀ {i a : ℕ}, i < 15 → vsAllocVars.getD i 0 = a → ∀ k < (S.ownW.getD i []).length,
      ∃ j, (σ (.n a)).limb 0 * addressOfIndex k = addressOfIndex j ∧
        (Main.RegionL Lin j ∨ Main.RegionL (bufL b (vsSizes S.d) S.ownW) j) :=
    fun hi ha k hk ↦ vs_regAt (pa hi ha) (hown _ hi k hk)
  -- the loads
  intro q hq
  obtain ⟨s, hs, hq'⟩ := List.mem_filterMap.1 hq
  cases s with
  | atom a =>
    cases a with
    | load d p off =>
      simp only [Stmt.loadS, Option.some.injEq] at hq'
      subst hq'
      obtain ⟨l, hl', ha⟩ := List.mem_flatten.1 (vs_side_mem hs rfl)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
      rcases hl' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl
      · obtain ⟨k, hk, he⟩ := List.mem_map.1 ha
        simp only [Atom.load.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        rw [List.mem_range] at hk
        exact own (i := 1) (by norm_num) rfl k (by show k < (vsStreamW c.proof.stream).length; omega)
      · obtain ⟨k, hk, he⟩ := List.mem_map.1 ha
        simp only [Atom.load.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        rw [List.mem_range] at hk
        exact own (i := 2) (by norm_num) rfl k (by show k < (S.rowsN.map eOfNat).length; simp [S.hrowsL]; omega)
      · simp [vsSPquot] at ha
      · simp [vsSPrng] at ha
      · simp only [vsSPdims, List.mem_cons, List.mem_map, List.mem_range, Atom.load.injEq] at ha
        have hl7 : (vsDimsW S.logMem S.hs).length = 7 := by simp [vsDimsW, S.hs_length]
        rcases ha with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨t, ht, ⟨-, rfl, rfl⟩⟩
        · exact own (i := 3) (by norm_num) rfl 0 (by show 0 < (vsDimsW S.logMem S.hs).length; omega)
        · exact own (i := 3) (by norm_num) rfl 6 (by show 6 < (vsDimsW S.logMem S.hs).length; omega)
        · exact own (i := 3) (by norm_num) rfl (1 + t) (by show _ < (vsDimsW S.logMem S.hs).length; omega)
      · obtain ⟨k, hk, he⟩ := List.mem_map.1 ha
        simp only [Atom.load.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        rw [List.mem_range] at hk
        exact own (i := 4) (by norm_num) rfl k (by
          show k < (vsKbW S.logMem S.hs).length; simp [vsKbW, S.hs_length]; omega)
      · obtain ⟨bk, hbk, he⟩ := List.mem_map.1 ha
        simp only [Atom.load.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        rw [List.mem_range] at hbk
        have hsrc : Tables.blockKappaSrc.getD bk 0 < 8 := blockKappaSrc_lt bk (by show bk < 153; omega)
        have he := kbase_le hhs (S.h30.trans (by norm_num)) (Tables.blockKappaSrc.getD bk 0)
        have hadj : Tables.blockKappaAdj bk ≤ 19 := by unfold Tables.blockKappaAdj; split <;> omega
        have h0 : Tables.blockKappaAdj bk ≠ 0 → Tables.blockKappaSrc.getD bk 0 = 0 := push_adj bk hbk
        refine vs_regAt (x := sqE + ([0, S.logMem] ++ S.hs).getD (Tables.blockKappaSrc.getD bk 0) 0)
          (by rw [hσ, vs_pushP hl hbk, ← hσ, hp4, hkb _ hsrc, vs_ptr_add]) ?_
        rw [Nat.add_assoc]
        refine hlin sqE expTabAllWords (hexp _ (by unfold vsExpLin; exact List.mem_singleton_self _))
          _ ?_
        rw [length_expTabAllWords]
        by_cases hz : Tables.blockKappaAdj bk = 0
        · omega
        · rw [h0 hz]; simp; omega
      · obtain ⟨i, hi, he⟩ := List.mem_map.1 ha
        simp only [Atom.load.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        rw [List.mem_range] at hi
        exact own (i := 8) (by norm_num) rfl i (by show i < S.wb.1.length; rw [S.wb_length hbl]; omega)
      · simp only [vsSPmaps, List.mem_cons, List.mem_map, List.mem_range, Atom.load.injEq] at ha
        rcases ha with ⟨-, rfl, rfl⟩ | ⟨i, hi, ⟨-, rfl, rfl⟩⟩
        · refine vs_regAt h595 ?_
          rw [hcK, Nat.add_zero, Nat.add_assoc]
          exact hstr _ (by omega)
        · exact own (i := 13) (by norm_num) rfl i (by show i < S.rchs.length; rw [S.rchs_length]; omega)
      · obtain ⟨bb, hbb, ha⟩ := List.mem_flatMap.1 ha
        obtain ⟨pp, hpp, he⟩ := List.mem_map.1 ha
        simp only [Atom.load.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        rw [List.mem_range] at hbb hpp
        exact own (i := 14) (by norm_num) rfl _ (by
          show _ < S.ctab.length
          rw [ChildSegs.ctab, vs_ringCoefficients_length _ _ (by simp [S.rchs_length, ringMapWidth])
            (by simp [S.rchs_length, ringMapWidth])]
          omega)
      · simp only [vsSPlam, List.mem_cons, List.mem_map, List.mem_range, Atom.load.injEq] at ha
        rcases ha with ⟨-, rfl, rfl⟩ | ⟨i, hi, ⟨-, rfl, rfl⟩⟩
        · exact own (i := 7) (by norm_num) rfl 0 (by show 0 < [S.oodV].length; simp)
        · have hk : vsKept i < 159 := by simp only [vsKept]; split <;> omega
          unfold vsClaimAt
          split_ifs with h
          · refine vs_regAt h582 ?_
            rw [hcT, Nat.add_assoc, Nat.add_assoc]
            exact hstr _ (by omega)
          · have hpool : S.H.poolW.length = 159 := by
              simp only [Tables.VtHonest.poolW, Tables.VtHonest.pcW, List.length_append,
                List.length_replicate, List.length_map, (S.H_run hbl).1.hx4]
              rfl
            exact own (i := 0) (by norm_num) rfl _ (by show _ < S.H.poolW.length; omega)
      · obtain ⟨k, hk, he⟩ := List.mem_map.1 ha
        simp only [Atom.load.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        rw [List.mem_range] at hk
        exact own (i := 5) (by norm_num) rfl k (by show k < S.rG.2.1.length; omega)
      · obtain ⟨k, hk, he⟩ := List.mem_map.1 ha
        simp only [Atom.load.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        rw [List.mem_range] at hk
        exact vs_regAt hp5 (hlin _ _ hout k (by omega))
      · obtain ⟨k, hk, he⟩ := List.mem_map.1 ha
        simp only [Atom.load.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        rw [List.mem_range] at hk
        exact own (i := 10) (by norm_num) rfl k (by show k < S.H.slots.length; rw [S.slots_length]; omega)
      · obtain ⟨k, hk, he⟩ := List.mem_map.1 ha
        simp only [Atom.load.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        rw [List.mem_range] at hk
        exact vs_regAt hp5 (hlin _ _ hout _ (by omega))
      · simp only [vsSPlast, List.mem_cons, List.not_mem_nil, or_false, Atom.load.injEq] at ha
        obtain ⟨-, rfl, rfl⟩ := ha
        exact vs_regAt hp5 (hlin _ _ hout _ (by omega))
    | _ => simp [Stmt.loadS] at hq'
  | _ => simp [Stmt.loadS] at hq'


end
end LeanVM.Guest.B1.VerifySub
