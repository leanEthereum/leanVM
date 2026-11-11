/-
  LeanVM.Guest.B1.Main.AggL25Complete

  `__loop33` (a child's absorption), completely.
-/

module

public import LeanVM.Guest.B1.Main.AggL25CChk

/-!
# A child's absorption, completely

`l25_block`: `__loop33`'s block at the child `x` holds on the evaluated valuation (`Fwd.ev`) when
its row (`absorb·x^13`) holds the honest words of a sponge with four waiting scalars, the next
row the honest words of the sponge after the child's `52` words, the pointer tables the child's
claims, and the child's words are in memory. Its atoms but its stores hold (their side conditions
its loads and its packs' `assert_in_k`; the `KECCAK`s' inputs canonical from the row and the
packed cells), so its chain is the absorption (`DupSpec.chain`, as in `l25_step`), which its
stores find.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Da

@[expose] public section

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **A child's absorption** (`__loop33`). -/
theorem l25_block {x N absorb cfresh lfT ccarried lcT cpi : E} {st : Fs} (hst : StOk st)
    (hp4 : st.pend.length = 4) (hrow : ReadsAt rd (absorb * x ^ 13) (rowW st))
    (hnext : ReadsAt rd (absorb * x ^ 13 * gen ^ 13)
      (rowW (st.absorbAll (l25Words rd cpi cfresh ccarried x) dsObserve)))
    (hlf : LoadHolds rd (lfT * x) 0 (cfresh * x ^ 24))
    (hlc : LoadHolds rd (lcT * x) 0 (ccarried * x ^ 24))
    (hpi : ∀ o < 2, ∃ v, LoadHolds rd (cpi * x ^ 2) o v)
    (hfr : ∀ o < 24, ∃ v, LoadHolds rd (cfresh * x ^ 24) o v)
    (hca : ∀ o < 24, ∃ v, LoadHolds rd (ccarried * x ^ 24) o v) :
    LoopBlock rd (coreProgram.getD 401 default) x N [absorb, cfresh, lfT, ccarried, lcT, cpi] := by
  have hok := l25_ok
  simp only [l25Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    -⟩, -⟩ := hok
  have hcok := l25c_ok
  simp only [l25COk, Bool.and_eq_true, Option.isSome_iff_exists, List.all_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', List.mem_range] at hcok
  obtain ⟨⟨⟨⟨⟨c', hchk⟩, hatoms⟩, hcanA⟩, hneeds⟩, hrl⟩ := hcok
  have hdok := l25d_ok
  simp only [l25DOk, Bool.and_eq_true, decide_eq_true_eq] at hdok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpk, hchkS⟩, hnb⟩, hrin⟩, hcst⟩, hrst⟩, hsrc⟩, hm13⟩, hm59⟩, hm70⟩, hm50⟩,
    hm57⟩, hm51⟩, hm58⟩ := hdok
  simp only [List.all_eq_true, List.mem_range] at hsrc
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq, Bool.and_eq_true] at hcst hrst
  have hS := l25_stores
  set fn := coreProgram.getD 401 default
  set A := atomsIn (loopPre fn)
  let args : List E := [x, N, absorb, cfresh, lfT, ccarried, lcT, cpi]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body) := ⟨_, rfl⟩
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
  rw [show args.length = 8 from rfl, ← hσ, hS] at hgs
  have hg : ∀ a ∈ A, Good rd l25Stores (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (loopPre_mem (atom_mem_of_atomsIn ha))
  have hpar : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] := by
    rw [params_of_shape hshape hlen]; rfl
  have par : ∀ i (hi : i < 8), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = x := par 0 (by omega)
  have hP : ∀ a ∈ A.filter pureB, a.Holds rd σ := pure_holds hg
  have p13 : σ (.n 13) = absorb * x ^ 13 := by rw [monoIs_sound hm13 hP, par 2 (by omega), e0]; rfl
  have p59 : σ (.n 59) = cpi * x ^ 2 := by rw [monoIs_sound hm59 hP, par 7 (by omega), e0]; rfl
  have p70 : σ (.n 70) = cpi * x ^ 2 := by rw [monoIs_sound hm70 hP, par 7 (by omega), e0]; rfl
  have p50 : σ (.n 50) = cfresh * x ^ 24 := by
    rw [monoIs_sound hm50 hP, par 3 (by omega), e0]; rfl
  have p57 : σ (.n 57) = ccarried * x ^ 24 := by
    rw [monoIs_sound hm57 hP, par 5 (by omega), e0]; rfl
  have p51 : σ (.n 51) = lfT * x := by rw [isMul_sound hm51 hP, par 4 (by omega), e0]; rfl
  have p58 : σ (.n 58) = lcT * x := by rw [isMul_sound hm58 hP, par 6 (by omega), e0]; rfl
  -- the atoms but the stores
  have hg' : ∀ a ∈ l25A, Good rd l25Stores (fun _ => 0) σ a := fun a ha =>
    hg a (mem_l25A.mp ha).1
  have hnS : ∀ a ∈ l25A, a ∉ l25Stores := fun a ha => (mem_l25A.mp ha).2
  have hrowL : ∀ o < 13, LoadHolds rd (σ (.n 13)) o ((rowW st).getD o 0) := fun o ho => by
    rw [p13, List.getD_eq_getElem _ _ (by rw [rowW_length hst]; exact ho)]
    exact hrow o (by rw [rowW_length hst]; exact ho)
  have vrow : ∀ o < 13, σ (.n (14 + o)) = (rowW st).getD o 0 := fun o ho =>
    (load_of_good (hnS _ (hrl o ho)) (hg' _ (hrl o ho)) (hrowL o ho)).1
  have hpw : ∀ p ∈ packsOf l25A, packIn l25A p.1 p.2 = true := List.all_eq_true.mp hpk
  have hAc : ∀ i ∈ (List.range 13).map (14 + ·) ++
      (packsOf l25A).flatMap (fun p => [p.2 + 6, p.2 + 8]), IsCanonical128 (σ (.n i)) := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hi
      have ho' := List.mem_range.mp ho
      rw [vrow o ho']
      exact rowW_canonical hst _ (getD_mem (by rw [rowW_length hst]; exact ho'))
    · obtain ⟨p, hp, hi⟩ := List.mem_flatMap.mp hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact (pack_canon (hpw p hp) hg').1
      · exact (pack_canon (hpw p hp) hg').2
  have hat' : ∀ a ∈ l25A, a.Holds rd σ := by
    refine atoms_holds hidx hcanA hg' hAc fun a ha hns => ?_
    rcases hneeds a ha with ((h | h) | h) | h
    · rw [hns] at h; exact absurd h (by simp)
    · exact Or.inl (pack_inK hpk hg' h)
    · cases a <;> simp only [isL25RowLoad, Bool.false_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rename_i d p o
      obtain ⟨⟨rfl, rfl⟩, ho⟩ := h
      exact Or.inl (load_of_good (hnS _ ha) (hg' _ ha) (hrowL o ho)).2
    · cases a <;> simp only [isL25WordLoad, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rename_i d p o
      refine Or.inr (side_load (hnS _ ha) (v := memAt rd (σ p) o) ?_)
      rcases h with ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, ho⟩) | ⟨rfl, ho⟩
      · obtain ⟨v, hv⟩ := hpi 0 (by omega)
        rw [p59, memAt_of_load hv]; exact hv
      · obtain ⟨v, hv⟩ := hpi 1 (by omega)
        rw [p70, memAt_of_load hv]; exact hv
      · obtain ⟨v, hv⟩ := hfr o ho
        rw [p50, memAt_of_load hv]; exact hv
      · obtain ⟨v, hv⟩ := hca o ho
        rw [p57, memAt_of_load hv]; exact hv
  -- the chain
  obtain ⟨-, hwl, hK, -, -⟩ := DupSpec.check_facts hchkS hat'
  have hin := rowIn_sound hrin hat'
  rw [p13] at hin
  have hcan := (DupSpec.keccak_facts (hK 0 (by rw [hnb]; omega)).2.2).1
  rw [hin] at hcan
  have hperm := rowRel_perm (rowRel_of_reads hst hrow)
    (fun c hc => hcan c (List.mem_append_left _ hc))
  rw [← hin] at hperm
  have hch := DupSpec.chain hchkS hat' st hp4 hperm
  have hw : l25S.wvals σ = l25Words rd cpi cfresh ccarried x := by
    rw [DupSpec.wvals_eq, hnb, l25Words]
    refine List.map_congr_left fun w hw => ?_
    have hw52 := List.mem_range.mp hw
    have hs' := hsrc w hw52
    unfold l25Word
    by_cases ha : w < 2
    · rw [l25Src_lt2 ha, srcOk_some] at hs'
      have := memAt_of_load (load_sound hs' hat')
      rw [ite_pos' ha, ← this]
      rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl
      · rw [ite_pos' rfl, p59]
      · rw [ite_neg' (show ¬ (1 = 0) by omega), p70]
    by_cases hb : w < 26
    · rw [l25Src_fresh (by omega) hb, srcOk_some] at hs'
      rw [ite_neg' ha, ite_pos' hb, ← p50]
      exact (memAt_of_load (load_sound hs' hat')).symm
    by_cases hc : w < 50
    · rw [l25Src_carried (by omega) hc, srcOk_some] at hs'
      rw [ite_neg' ha, ite_neg' hb, ite_pos' hc, ← p57]
      exact (memAt_of_load (load_sound hs' hat')).symm
    · rw [l25Src_pad (by omega), srcOk_none] at hs'
      rw [ite_neg' ha, ite_neg' hb, ite_neg' hc, const_sound hs' hat', word_zero]
  rw [hw, hnb] at hch
  have hst' := stOk_absorbAll (l25Words rd cpi cfresh ccarried x) hst
  have hl' := rowW_length hst'
  have hnext' : ∀ k < 13, LoadHolds rd (σ (.n 13)) (13 + k)
      ((rowW (st.absorbAll (l25Words rd cpi cfresh ccarried x) dsObserve)).getD k 0) := by
    intro k hk
    rw [p13, ← loadHolds_mul_gen_pow, List.getD_eq_getElem _ _ (by rw [hl']; exact hk)]
    exact hnext k (by rw [hl']; exact hk)
  -- the stores
  have hstores : ∀ a ∈ l25Stores, a.Holds rd σ := by
    intro a haS
    simp only [l25Stores, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
      List.mem_flatMap, List.not_mem_nil, or_false] at haS
    rcases haS with ((rfl | rfl) | ⟨i, hi, rfl⟩) | ⟨j, hj, rfl | rfl⟩
    · show LoadHolds rd (σ (.n 51)) 0 (σ (.n 50))
      rw [p51, p50]; exact hlf
    · show LoadHolds rd (σ (.n 58)) 0 (σ (.n 57))
      rw [p58, p57]; exact hlc
    · show LoadHolds rd (σ (.n 13)) (13 + i) (σ (.n (692 + i)))
      have e : σ (.n (692 + i)) =
          (rowW (st.absorbAll (l25Words rd cpi cfresh ccarried x) dsObserve)).getD i 0 := by
        rw [rowW_getD_cap hst' hi, hch, ← hcst i hi]
        simp [List.getD_eq_getElem?_getD, hi]
      rw [e]; exact hnext' i (by omega)
    all_goals
      have hwj : 48 + j < l25S.words.length := by rw [hwl, hnb]; omega
      have hpc := pack_cells (hpw _ (getD_mem (d := default) hwj)) hg'
      have hr := Keccak.rateCell_scalar ((l25S.blk σ (13 - 1)).map (·, dsObserve)) j
        (by simp [DupSpec.blk]; omega)
      have hbj : ((l25S.blk σ (13 - 1)).map (·, dsObserve))[j]'(by simp [DupSpec.blk]; omega) =
          (σ (l25S.wV (48 + j)), dsObserve) := by
        simp [DupSpec.blk]
      rw [hbj] at hr
      have hv := hr.trans hpc.symm
      simp only [Prod.ext_iff] at hv
      obtain ⟨r6, r8⟩ := hrst j hj
    · show LoadHolds rd (σ (.n 13)) (18 + 2 * j) (σ (.n (704 + 10 * j)))
      have e : σ (.n (704 + 10 * j)) =
          (rowW (st.absorbAll (l25Words rd cpi cfresh ccarried x) dsObserve)).getD (5 + 2 * j) 0 := by
        rw [rowW_getD_rate hst' (by omega), hch, hv.1, ← r6]
        rfl
      rw [e, show 18 + 2 * j = 13 + (5 + 2 * j) by omega]
      exact hnext' _ (by omega)
    · show LoadHolds rd (σ (.n 13)) (19 + 2 * j) (σ (.n (706 + 10 * j)))
      have e : σ (.n (706 + 10 * j)) =
          (rowW (st.absorbAll (l25Words rd cpi cfresh ccarried x) dsObserve)).getD
            (5 + (2 * j + 1)) 0 := by
        rw [rowW_getD_rate hst' (by omega), hch, hv.2, ← r8]
        rfl
      rw [e, show 19 + 2 * j = 13 + (5 + (2 * j + 1)) by omega]
      exact hnext' _ (by omega)
  have hat : ∀ a ∈ A, a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ l25Stores
    · exact hstores a haS
    · exact hat' a (mem_l25A.mpr ⟨ha, haS⟩)
  refine ⟨σ, ?_, fun s hs => ?_⟩
  · rw [hpar]
    simp only [List.map_cons, List.map_nil]
    rw [e0, par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega),
      par 5 (by omega), par 6 (by omega), par 7 (by omega)]
    rfl
  · have := hatoms s hs
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    exact ⟨hat a (mem_atomsIn hs), trivial⟩

end
end LeanVM.Guest.B1.Main
