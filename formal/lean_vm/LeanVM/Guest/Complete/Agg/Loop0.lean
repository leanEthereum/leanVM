module

public import LeanVM.Guest.Complete.Agg.Rows
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop0»

/-!
# `aggregate_claims_loop0`, completely

`a0_block`: the loop's block at the child `x` holds on its evaluated valuation (`Fwd.ev`) when its
row (`absorb·x^13`) holds the honest words of a sponge with four waiting scalars, the next row the
honest words of the sponge after the child's `84` words (`l25Words`), the pointer tables the
child's claims (`child_fresh·x^55`, `child_carried·x^26`), and the child's words are in memory. Its
atoms but its stores hold (their side conditions its loads, `a0COk`), so its chain is the
absorption (`DupSpec.chain`, as in `l25_step`), which its stores find. The archive's `l25_block`
over Hotwire's loop (`21` permutations).
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.Da

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

/-- A load of the row's word `o < 13`. -/
def isA0RowLoad : Atom → Bool
  | .load _ p o => decide (p = .n (val% «aggregate_claims_loop0» "row")) && decide (o < 13)
  | _ => false

/-- A load of a child's word: its public input's two cells, its claims' words. -/
def isA0WordLoad : Atom → Bool
  | .load _ p o =>
    (decide (p = .n (val% «aggregate_claims_loop0» "s9.u0.s1.t.s0#0")) && decide (o = 0)) ||
      (decide (p = .n (val% «aggregate_claims_loop0» "s9.u1.s1.t.s0#0")) && decide (o = 1)) ||
      (decide (p = .n (val% «aggregate_claims_loop0» "fresh")) && decide (o < 55)) ||
      (decide (p = .n (val% «aggregate_claims_loop0» "carried")) && decide (o < 26))
  | _ => false

/-- The `fs_pack` base of the next row's waiting scalar `j < 4`. -/
def a0Last (j : ℕ) : ℕ := [567, 570, 573, 575].getD j 0

/-- `aggregate_claims_loop0`'s stores: the pointer tables, then the next row's capacity and rate
cells. -/
def a0Stores : List Atom :=
  [.load (.n (val% «aggregate_claims_loop0» "fresh")) (.n (val% «aggregate_claims_loop0» "s6#0")) 0,
    .load (.n (val% «aggregate_claims_loop0» "carried")) (.n (val% «aggregate_claims_loop0» "s8#0")) 0] ++
    (List.range 5).map (fun i => .load (.n (561 + i)) (.n (val% «aggregate_claims_loop0» "row")) (13 + i)) ++
    (List.range 4).flatMap fun j =>
      [.load (.n (a0Last j)) (.n (val% «aggregate_claims_loop0» "row")) (18 + 2 * j),
        .load (.n (a0Last j + 1)) (.n (val% «aggregate_claims_loop0» "row")) (19 + 2 * j)]

/-- `aggregate_claims_loop0`'s atoms but its stores. -/
noncomputable def a0A : List Atom :=
  (atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop0» default))).filter fun a =>
    decide (a ∉ a0Stores)

/-- `aggregate_claims_loop0`'s chain, on its atoms but its stores. -/
noncomputable def a0S : DupSpec := ⟨keccakBlocks a0A, packsOf a0A⟩

theorem mem_a0A {a : Atom} :
    a ∈ a0A ↔ a ∈ atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop0» default)) ∧
      a ∉ a0Stores := by
  simp [a0A]

set_option maxRecDepth 100000 in
theorem a0_stores : storesOf 8 (coreProgram.getD idx% «aggregate_claims_loop0» default).body =
    a0Stores := by
  decide +kernel

/-- **`aggregate_claims_loop0`, evaluated**: its values defined in order, its atoms but its stores
holding from its row's and child's loads. -/
noncomputable def a0COk : Bool :=
  let fn := coreProgram.getD idx% «aggregate_claims_loop0» default
  (chk 8 fn.body).isSome && (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) &&
  a0A.all (fun a => !needsSide a || isA0RowLoad a || isA0WordLoad a)

/-- **`aggregate_claims_loop0`'s chain, on its atoms but its stores.** -/
noncomputable def a0DOk : Bool :=
  let A := a0A
  let P := (atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop0» default))).filter pureB
  a0S.check A && decide (a0S.nb = 21) && rowInOk A (.n (val% «aggregate_claims_loop0» "row")) (a0S.ins 0) &&
  (List.range 5).all (fun i => decide ((a0S.outs 20).getD (8 + i) default = .n (561 + i))) &&
  (List.range 4).all (fun j => decide (a0S.wB (80 + j) = a0Last j)) &&
  (List.range 84).all (fun w => srcOk A (a0S.wV w) (l25Src w)) &&
  monoIs P (.n (val% «aggregate_claims_loop0» "row")) (.n (val% «aggregate_claims_loop0» "absorb")) (.n (val% «aggregate_claims_loop0» "xc")) 13 &&
  monoIs P (.n (val% «aggregate_claims_loop0» "s9.u0.s1.t.s0#0")) (.n (val% «aggregate_claims_loop0» "child_pi")) (.n (val% «aggregate_claims_loop0» "xc")) 2 &&
  monoIs P (.n (val% «aggregate_claims_loop0» "s9.u1.s1.t.s0#0")) (.n (val% «aggregate_claims_loop0» "child_pi")) (.n (val% «aggregate_claims_loop0» "xc")) 2 &&
  monoIs P (.n (val% «aggregate_claims_loop0» "fresh")) (.n (val% «aggregate_claims_loop0» "child_fresh")) (.n (val% «aggregate_claims_loop0» "xc")) 55 &&
  monoIs P (.n (val% «aggregate_claims_loop0» "carried")) (.n (val% «aggregate_claims_loop0» "child_carried")) (.n (val% «aggregate_claims_loop0» "xc")) 26 &&
  isMul P (.n (val% «aggregate_claims_loop0» "s6#0")) (.n (val% «aggregate_claims_loop0» "fresh_row")) (.n (val% «aggregate_claims_loop0» "xc")) &&
  isMul P (.n (val% «aggregate_claims_loop0» "s8#0")) (.n (val% «aggregate_claims_loop0» "carried_row")) (.n (val% «aggregate_claims_loop0» "xc"))

set_option maxRecDepth 100000 in
theorem a0c_ok : a0COk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem a0d_ok : a0DOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem a0_shape : loopShapeF (coreProgram.getD idx% «aggregate_claims_loop0» default)
    name% «aggregate_claims_loop0» = true ∧
    (coreProgram.getD idx% «aggregate_claims_loop0» default).params.length = 8 := by decide +kernel

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **A child's absorption** (`aggregate_claims_loop0`), completely. -/
theorem a0_block {x N absorb cfresh lfT ccarried lcT cpi : E} {st : Fs} (hst : StOk st)
    (hp4 : st.pend.length = 4) (hrow : ReadsAt rd (absorb * x ^ 13) (rowW st))
    (hnext : ReadsAt rd (absorb * x ^ 13 * gen ^ 13)
      (rowW (st.absorbAll (l25Words rd cpi cfresh ccarried x) dsObserve)))
    (hlf : LoadHolds rd (lfT * x) 0 (cfresh * x ^ 55))
    (hlc : LoadHolds rd (lcT * x) 0 (ccarried * x ^ 26))
    (hpi : ∀ o < 2, ∃ v, LoadHolds rd (cpi * x ^ 2) o v)
    (hfr : ∀ o < 55, ∃ v, LoadHolds rd (cfresh * x ^ 55) o v)
    (hca : ∀ o < 26, ∃ v, LoadHolds rd (ccarried * x ^ 26) o v) :
    LoopBlock rd (coreProgram.getD idx% «aggregate_claims_loop0» default) x N
      [absorb, cfresh, lfT, ccarried, lcT, cpi] := by
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
  refine ⟨σ, ?_, fun s hs => ?_⟩
  · rw [hpar]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
      List.map_nil]
    rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega),
      par 5 (by omega), par 6 (by omega), par 7 (by omega)]
    rfl
  · have := hatoms s hs
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    exact ⟨hat a (mem_atomsIn hs), trivial⟩

end
end LeanVM.Guest.Complete.Agg
