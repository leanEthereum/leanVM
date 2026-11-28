module

public import LeanVM.Guest.Complete.Agg.Loop0
public import LeanVM.Guest.Complete.Agg.Loop1A
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop0»

/-!
# `aggregate_claims_loop0`, placed

`a0_blockA`: `a0_block`'s valuation, its atoms holding (`SOk`) and its loads in `A0Reg` (the row and
the next, the child's words, the pointer tables' cells), at the child `j` with every pointer `ptrAt`
of its base. `agg_loop0_callAtA`: the loop placed from every counter by `loopF_callAtA`, its block
`lpBlk fs f (m - j)`, ending at its cursor, popping nothing, every node exact.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.Da

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

/-- `aggregate_claims_loop0`'s region at the child `j`: its row and the next, the child's public
input, fresh and carried words, the pointer tables' cells. -/
def A0Reg (iab ipi icf ilf icc ilc j : ℕ) (i : ℕ) : Prop :=
  (iab + j * 13 ≤ i ∧ i < iab + j * 13 + 26) ∨ (ipi + j * 2 ≤ i ∧ i < ipi + j * 2 + 2) ∨
    (icf + j * 55 ≤ i ∧ i < icf + j * 55 + 55) ∨ i = ilf + j + 0 ∨
    (icc + j * 26 ≤ i ∧ i < icc + j * 26 + 26) ∨ i = ilc + j + 0

set_option maxRecDepth 20000 in
/-- **`aggregate_claims_loop0`'s block at the child `j`, placed.** -/
theorem a0_blockA {rd : Reader} {j iab ipi icf ilf icc ilc : ℕ}
    {x N absorb cfresh lfT ccarried lcT cpi : E} {st : Fs}
    (hx : x = gen ^ j) (hab : absorb = ptrAt iab) (hcfE : cfresh = ptrAt icf) (hlfE : lfT = ptrAt ilf)
    (hccE : ccarried = ptrAt icc) (hlcE : lcT = ptrAt ilc) (hpiE : cpi = ptrAt ipi)
    (hst : StOk st)
    (hp4 : st.pend.length = 4) (hrow : ReadsAt rd (absorb * x ^ 13) (rowW st))
    (hnext : ReadsAt rd (absorb * x ^ 13 * gen ^ 13)
      (rowW (st.absorbAll (l25Words rd cpi cfresh ccarried x) dsObserve)))
    (hlf : LoadHolds rd (lfT * x) 0 (cfresh * x ^ 55))
    (hlc : LoadHolds rd (lcT * x) 0 (ccarried * x ^ 26))
    (hpi : ∀ o < 2, ∃ v, LoadHolds rd (cpi * x ^ 2) o v)
    (hfr : ∀ o < 55, ∃ v, LoadHolds rd (cfresh * x ^ 55) o v)
    (hca : ∀ o < 26, ∃ v, LoadHolds rd (ccarried * x ^ 26) o v) :
    ∃ σ : Val, (coreProgram.getD idx% «aggregate_claims_loop0» default).params.map σ =
        x :: N :: [absorb, cfresh, lfT, ccarried, lcT, cpi] ∧
      (∀ s ∈ loopPre (coreProgram.getD idx% «aggregate_claims_loop0» default), SOk rd σ s) ∧
      ∀ q' ∈ (loopPre (coreProgram.getD idx% «aggregate_claims_loop0» default)).filterMap stmtLoad?,
        ∃ i, (σ q'.1).limb 0 * addressOfIndex q'.2 = addressOfIndex i ∧ A0Reg iab ipi icf ilf icc ilc j i := by
  obtain ⟨hshape, hlen⟩ := a0_shape
  have hcok := a0c_ok
  simp only [a0COk, Bool.and_eq_true, Option.isSome_iff_exists, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at hcok
  obtain ⟨⟨⟨c', hchk⟩, hatoms⟩, hneeds⟩ := hcok
  have hdok := a0d_ok
  simp only [a0DOk, Bool.and_eq_true, decide_eq_true_eq] at hdok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hchkS, hnb⟩, hrin⟩, hcst⟩, hrst⟩, hsrc⟩, hm13⟩, hm59⟩, hm63⟩, hm50⟩,
    hm57⟩, hm51⟩, hm58⟩ := hdok
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hsrc hcst hrst
  set fn := coreProgram.getD idx% «aggregate_claims_loop0» default
  set A := atomsIn (loopPre fn)
  let args : List E := [x, N, absorb, cfresh, lfT, ccarried, lcT, cpi]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body) := ⟨_, rfl⟩
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
  rw [show args.length = 8 from rfl, ← hσ, a0_stores] at hgs
  have hg : ∀ a ∈ A, Good rd a0Stores (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (loopPre_mem (atom_mem_of_atomsIn ha))
  have hpar : fn.params = (List.range 8).map V.n := params_of_shape hshape hlen
  have par : ∀ i (hi : i < 8), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n (val% «aggregate_claims_loop0» "xc")) = x := par 0 (by omega)
  have hP : ∀ a ∈ A.filter pureB, a.Holds rd σ := pure_holds hg
  have p13 : σ (.n (val% «aggregate_claims_loop0» "row")) = absorb * x ^ 13 := by
    rw [monoIs_sound hm13 hP, par 2 (by omega), e0]; rfl
  have p59 : σ (.n (val% «aggregate_claims_loop0» "s9.u0.s1.t.s0#0")) = cpi * x ^ 2 := by
    rw [monoIs_sound hm59 hP, par 7 (by omega), e0]; rfl
  have p63 : σ (.n (val% «aggregate_claims_loop0» "s9.u1.s1.t.s0#0")) = cpi * x ^ 2 := by
    rw [monoIs_sound hm63 hP, par 7 (by omega), e0]; rfl
  have p50 : σ (.n (val% «aggregate_claims_loop0» "fresh")) = cfresh * x ^ 55 := by
    rw [monoIs_sound hm50 hP, par 3 (by omega), e0]; rfl
  have p57 : σ (.n (val% «aggregate_claims_loop0» "carried")) = ccarried * x ^ 26 := by
    rw [monoIs_sound hm57 hP, par 5 (by omega), e0]; rfl
  have p51 : σ (.n (val% «aggregate_claims_loop0» "s6#0")) = lfT * x := by
    rw [isMul_sound hm51 hP, par 4 (by omega), e0]; rfl
  have p58 : σ (.n (val% «aggregate_claims_loop0» "s8#0")) = lcT * x := by
    rw [isMul_sound hm58 hP, par 6 (by omega), e0]; rfl
  -- the atoms but the stores
  have hg' : ∀ a ∈ a0A, Good rd a0Stores (fun _ => 0) σ a := fun a ha => hg a (mem_a0A.mp ha).1
  have hnS : ∀ a ∈ a0A, a ∉ a0Stores := fun a ha => (mem_a0A.mp ha).2
  have hrowL : ∀ o < 13, LoadHolds rd (σ (.n (val% «aggregate_claims_loop0» "row"))) o
      ((rowW st).getD o 0) := fun o ho => by
    rw [p13, List.getD_eq_getElem _ _ (by rw [rowW_length hst]; exact ho)]
    exact hrow o (by rw [rowW_length hst]; exact ho)
  have hat' : ∀ a ∈ a0A, a.Holds rd σ := by
    refine atoms_holds hg' fun a ha hns => ?_
    rcases hneeds a ha with (h | h) | h
    · rw [hns] at h; exact absurd h (by simp)
    · cases a <;> simp only [isA0RowLoad, Bool.false_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rename_i d p o
      obtain ⟨rfl, ho⟩ := h
      exact Or.inl (load_of_good (hnS _ ha) (hg' _ ha) (hrowL o ho)).2
    · cases a <;> simp only [isA0WordLoad, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rename_i d p o
      refine Or.inr (side_load (hnS _ ha) (v := memAt rd (σ p) o) ?_)
      rcases h with ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, ho⟩) | ⟨rfl, ho⟩
      · obtain ⟨v, hv⟩ := hpi 0 (by omega)
        rw [p59, memAt_of_load hv]; exact hv
      · obtain ⟨v, hv⟩ := hpi 1 (by omega)
        rw [p63, memAt_of_load hv]; exact hv
      · obtain ⟨v, hv⟩ := hfr o ho
        rw [p50, memAt_of_load hv]; exact hv
      · obtain ⟨v, hv⟩ := hca o ho
        rw [p57, memAt_of_load hv]; exact hv
  -- the chain
  obtain ⟨-, hwl, -, hPk, -⟩ := DupSpec.check_facts hchkS hat'
  have hin := rowIn_sound hrin hat'
  rw [p13] at hin
  have hperm := rowRel_perm (rowRel_of_reads hst hrow)
  rw [← hin] at hperm
  have hch := DupSpec.chain hchkS hat' st hp4 hperm
  have hw : a0S.wvals σ = l25Words rd cpi cfresh ccarried x := by
    rw [DupSpec.wvals_eq, hnb, l25Words]
    refine List.map_congr_left fun w hw => ?_
    have hw84 := List.mem_range.mp hw
    have hs' := hsrc w hw84
    unfold l25Word
    by_cases ha : w < 2
    · rw [l25Src_lt2 ha, srcOk_some] at hs'
      have := memAt_of_load (load_sound hs' hat')
      rw [ite_pos' ha, ← this]
      rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl
      · rw [ite_pos' rfl, p59]
      · rw [ite_neg' (show ¬ (1 = 0) by omega), p63]
    by_cases hb : w < 57
    · rw [l25Src_fresh (by omega) hb, srcOk_some] at hs'
      rw [ite_neg' ha, ite_pos' hb, ← p50]
      exact (memAt_of_load (load_sound hs' hat')).symm
    by_cases hc : w < 83
    · rw [l25Src_carried (by omega) hc, srcOk_some] at hs'
      rw [ite_neg' ha, ite_neg' hb, ite_pos' hc, ← p57]
      exact (memAt_of_load (load_sound hs' hat')).symm
    · rw [l25Src_pad (by omega), srcOk_none] at hs'
      rw [ite_neg' ha, ite_neg' hb, ite_neg' hc, const_sound hs' hat', word_zero]
  rw [hw, hnb] at hch
  have hst' := stOk_absorbAll (l25Words rd cpi cfresh ccarried x) hst
  have hl' := rowW_length hst'
  have hnext' : ∀ k < 13, LoadHolds rd (σ (.n (val% «aggregate_claims_loop0» "row"))) (13 + k)
      ((rowW (st.absorbAll (l25Words rd cpi cfresh ccarried x) dsObserve)).getD k 0) := by
    intro k hk
    rw [p13, ← loadHolds_mul_gen_pow, List.getD_eq_getElem _ _ (by rw [hl']; exact hk)]
    exact hnext k (by rw [hl']; exact hk)
  -- the stores
  have hstores : ∀ a ∈ a0Stores, a.Holds rd σ := by
    intro a haS
    simp only [a0Stores, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
      List.mem_flatMap, List.not_mem_nil, or_false] at haS
    rcases haS with ((rfl | rfl) | ⟨i, hi, rfl⟩) | ⟨j, hj, rfl | rfl⟩
    · show LoadHolds rd (σ (.n (val% «aggregate_claims_loop0» "s6#0"))) 0
        (σ (.n (val% «aggregate_claims_loop0» "fresh")))
      rw [p51, p50]; exact hlf
    · show LoadHolds rd (σ (.n (val% «aggregate_claims_loop0» "s8#0"))) 0
        (σ (.n (val% «aggregate_claims_loop0» "carried")))
      rw [p58, p57]; exact hlc
    · show LoadHolds rd (σ (.n (val% «aggregate_claims_loop0» "row"))) (13 + i) (σ (.n (561 + i)))
      have e : σ (.n (561 + i)) =
          (rowW (st.absorbAll (l25Words rd cpi cfresh ccarried x) dsObserve)).getD i 0 := by
        rw [rowW_getD_cap hst' hi, hch, ← hcst i hi]
        simp [List.getD_eq_getElem?_getD, hi]
      rw [e]; exact hnext' i (by omega)
    all_goals
      have hwj : 80 + j < a0S.words.length := by rw [hwl, hnb]; omega
      have hpc := fsPackT_cells (hPk (80 + j) hwj)
      have hr := Keccak.rateCell_scalar ((a0S.blk σ (21 - 1)).map (·, dsObserve)) j
        (by simp [DupSpec.blk]; omega)
      have hbj : ((a0S.blk σ (21 - 1)).map (·, dsObserve))[j]'(by simp [DupSpec.blk]; omega) =
          (σ (a0S.wV (80 + j)), dsObserve) := by
        simp [DupSpec.blk]
      rw [hbj] at hr
      have hv := hr.trans hpc.symm
      simp only [Prod.ext_iff] at hv
      have r6 := hrst j hj
    · show LoadHolds rd (σ (.n (val% «aggregate_claims_loop0» "row"))) (18 + 2 * j) (σ (.n (a0Last j)))
      have e : σ (.n (a0Last j)) =
          (rowW (st.absorbAll (l25Words rd cpi cfresh ccarried x) dsObserve)).getD (5 + 2 * j) 0 := by
        rw [rowW_getD_rate hst' (by omega), hch, hv.1, ← r6]
      rw [e, show 18 + 2 * j = 13 + (5 + 2 * j) by omega]
      exact hnext' _ (by omega)
    · show LoadHolds rd (σ (.n (val% «aggregate_claims_loop0» "row"))) (19 + 2 * j)
        (σ (.n (a0Last j + 1)))
      have e : σ (.n (a0Last j + 1)) =
          (rowW (st.absorbAll (l25Words rd cpi cfresh ccarried x) dsObserve)).getD
            (5 + (2 * j + 1)) 0 := by
        rw [rowW_getD_rate hst' (by omega), hch, hv.2, ← r6]
      rw [e, show 19 + 2 * j = 13 + (5 + (2 * j + 1)) by omega]
      exact hnext' _ (by omega)
  have hat : ∀ a ∈ A, a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ a0Stores
    · exact hstores a haS
    · exact hat' a (mem_a0A.mpr ⟨ha, haS⟩)
  have hab' : σ (.n (val% «aggregate_claims_loop0» "row")) = ptrAt (iab + j * 13) := by
    rw [p13, hab, hx, ← pow_mul, ptrAt_mul_gen_pow]
  refine ⟨σ, ?_, fun s hs => ?_, fun q' hq => ?_⟩
  · rw [hpar]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
      List.map_nil]
    rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega),
      par 5 (by omega), par 6 (by omega), par 7 (by omega)]
    rfl
  · have := hatoms s hs
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    exact hat a (mem_atomsIn hs)
  · obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp hq
    cases s with
    | atom a =>
      cases a with
      | load d p o =>
        simp only [stmtLoad?, Option.some.injEq] at hq
        subst hq
        have ha : Atom.load d p o ∈ A := mem_atomsIn hs
        by_cases haS : Atom.load d p o ∈ a0Stores
        · simp only [a0Stores, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
            List.mem_flatMap, List.not_mem_nil, or_false, Atom.load.injEq] at haS
          rcases haS with ((⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩) | ⟨i, hi, -, rfl, rfl⟩) | ⟨i, hi, ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩⟩
          · exact ⟨ilf + j + 0, by rw [p51, hlfE, hx, ptrAt_mul_gen_pow, addr_ptrAt],
              Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
          · exact ⟨ilc + j + 0, by rw [p58, hlcE, hx, ptrAt_mul_gen_pow, addr_ptrAt],
              Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
          · exact ⟨iab + j * 13 + (13 + i), by rw [hab', addr_ptrAt], Or.inl ⟨by omega, by omega⟩⟩
          · exact ⟨iab + j * 13 + (18 + 2 * i), by rw [hab', addr_ptrAt], Or.inl ⟨by omega, by omega⟩⟩
          · exact ⟨iab + j * 13 + (19 + 2 * i), by rw [hab', addr_ptrAt], Or.inl ⟨by omega, by omega⟩⟩
        · rcases hneeds _ (mem_a0A.mpr ⟨ha, haS⟩) with (h | h) | h
          · simp [needsSide] at h
          · simp only [isA0RowLoad, Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨rfl, ho⟩ := h
            exact ⟨iab + j * 13 + o, by rw [hab', addr_ptrAt], Or.inl ⟨by omega, by omega⟩⟩
          · simp only [isA0WordLoad, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
            rcases h with ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, ho⟩) | ⟨rfl, ho⟩
            · exact ⟨ipi + j * 2 + 0, by rw [p59, hpiE, hx, ← pow_mul, ptrAt_mul_gen_pow, addr_ptrAt],
                Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
            · exact ⟨ipi + j * 2 + 1, by rw [p63, hpiE, hx, ← pow_mul, ptrAt_mul_gen_pow, addr_ptrAt],
                Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
            · exact ⟨icf + j * 55 + o, by rw [p50, hcfE, hx, ← pow_mul, ptrAt_mul_gen_pow, addr_ptrAt],
                Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))⟩
            · exact ⟨icc + j * 26 + o, by rw [p57, hccE, hx, ← pow_mul, ptrAt_mul_gen_pow, addr_ptrAt],
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))⟩
      | _ => simp [stmtLoad?] at hq
    | _ => simp [stmtLoad?] at hq

theorem a0_find : coreProgram.find? name% «aggregate_claims_loop0» =
    some (coreProgram.getD idx% «aggregate_claims_loop0» default) := find_of_idx l25_idx

theorem a0_loop : coreProgram.loop name% «aggregate_claims_loop0» = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem a0_plain : (loopPre (coreProgram.getD idx% «aggregate_claims_loop0» default)).all loopPlainB = true := by
  decide +kernel

/-- `aggregate_claims_loop0`'s words at the child `c`, at `ptrAt` bases: `a0_block`'s hypotheses. -/
def A0PreA (st : ℕ → Fs) (iab ipi icf ilf icc ilc : ℕ) (rd : Reader) (c : ℕ) : Prop :=
  StOk (st c) ∧ (st c).pend.length = 4 ∧ ReadsAt rd (ptrAt iab * (gen ^ c) ^ 13) (rowW (st c)) ∧
    ReadsAt rd (ptrAt iab * (gen ^ c) ^ 13 * gen ^ 13)
      (rowW ((st c).absorbAll (l25Words rd (ptrAt ipi) (ptrAt icf) (ptrAt icc) (gen ^ c)) dsObserve)) ∧
    LoadHolds rd (ptrAt ilf * gen ^ c) 0 (ptrAt icf * (gen ^ c) ^ 55) ∧
    LoadHolds rd (ptrAt ilc * gen ^ c) 0 (ptrAt icc * (gen ^ c) ^ 26) ∧
    (∀ o < 2, ∃ v, LoadHolds rd (ptrAt ipi * (gen ^ c) ^ 2) o v) ∧
    (∀ o < 55, ∃ v, LoadHolds rd (ptrAt icf * (gen ^ c) ^ 55) o v) ∧
    ∀ o < 26, ∃ v, LoadHolds rd (ptrAt icc * (gen ^ c) ^ 26) o v

/-- **`aggregate_claims_loop0` completes placed** from every counter `j < m`, on memories where
each child's words of its block hold (`A0PreA`), loading in a region holding each child's
`A0Reg`. -/
theorem agg_loop0_callAtA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k m : ℕ}
    (hm : m < 2 ^ 34) {st : ℕ → Fs} {iab ipi icf ilf icc ilc : ℕ} {R : ℕ → Prop} {Pre : Reader → Prop}
    (hpre : ∀ rd, Pre rd → ∀ c < m, A0PreA st iab ipi icf ilf icc ilc rd c)
    (hR : ∀ c < m, ∀ i, A0Reg iab ipi icf ilf icc ilc c i → R i) :
    ∀ j < m, ∀ fp c, fp + lpBlk fs name% «aggregate_claims_loop0» (m - j) ≤ c →
      CallAtA fs al cert k name% «aggregate_claims_loop0»
        (gen ^ j :: gen ^ m :: [ptrAt iab, ptrAt icf, ptrAt ilf, ptrAt icc, ptrAt ilc, ptrAt ipi])
        [] R (fun _ => False) (fun _ => True) Pre FreePost (lpBlk fs name% «aggregate_claims_loop0» (m - j)) fp c c :=
  fun j hj fp c hc =>
    (loopF_callAtA a0_find a0_shape.1 a0_loop a0_plain hm (hblk := fun j' hj' rd _ hp => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hpre rd hp j' hj'
      obtain ⟨σ, hpar, hok, hlo⟩ :=
        a0_blockA (N := gen ^ m) rfl rfl rfl rfl rfl rfl rfl h1 h2 h3 h4 h5 h6 h7 h8 h9
      exact ⟨σ, hpar, hok, fun q' hq => by
        obtain ⟨i, hi, hr⟩ := hlo q' hq
        exact ⟨i, hi, hR j' hj' i hr⟩⟩) j hj fp c hc).free agg_loop0_free.1 agg_loop0_free.2

end
end LeanVM.Guest.Complete.Agg
