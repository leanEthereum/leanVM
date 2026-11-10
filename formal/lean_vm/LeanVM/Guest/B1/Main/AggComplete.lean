/-
  LeanVM.Guest.B1.Main.AggComplete

  `aggregate_claims`, completely: `m` children whose words the memory holds, the hints of an
  accepting batching and the memory an honest run leaves at its buffers give its core IR
  relation, the claim at `defer_stmt` the batching (TRIAGE G #97).
-/

module

public import LeanVM.Guest.B1.Main.AggMainCChk
public import LeanVM.Guest.B1.Main.AggL25Complete
public import LeanVM.Guest.B1.Main.AggL26Complete

/-!
# `aggregate_claims`, completely

The honest valuation is the body evaluated (`Fwd.ev`) on the arguments, the hints and the
sumcheck's returns its honest ones (`aggOrc`: the buffers `P`, `bc_star_hint`, the sumcheck's
final capacity and claim). Its atoms hold (their side conditions its loads, its packs'
`assert_in_k`, `λ`'s `assert_in_k` on the permutation's canonical cells, and the final check,
which `batch cs h = some out` is), its stores find the first record, weight and the claim; its
permutation and challenge are `λ` (`lamA`), its calls hold by their completeness: the absorbing
rows (`l25_block`), the records (`l26_block`), the sumcheck (`batch_sumcheck_holds`) and the
weights (`l27_block`).

`aggregate_claims_complete_mem` is pointer-parametric (any `AggPtrs` holding `AggMem`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Da LeanVM.Node

@[expose] public section

variable {rd : Reader}

/-- The oracle of `aggregate_claims`' hints and its sumcheck's returns `res`. -/
def aggOrc (P : AggPtrs) (h : BatchingHints) (res : (List E × E) × Fs) (j : ℕ) : E :=
  if j = 5 then P.msgs else if j = 6 then h.finalBytecodeValue else if j = 7 then P.lf
  else if j = 8 then P.lc else if j = 60 then P.absorb else if j = 111 then P.chain
  else if j = 120 then P.pt else if j = 127 then P.pt1 else if j = 199 then P.w
  else if j = 126 then res.1.2 else if 121 ≤ j ∧ j < 126 then res.2.cap.getD (j - 121) 0 else 0

theorem const_good {S : List Atom} {w : ℕ → E} {σ : Val} {atoms : List Atom} {x : V} {lo hi : ℕ}
    (h : atoms.any (isConstAt x lo hi) = true) (hg : ∀ a ∈ atoms, Good rd S w σ a) :
    σ x = word lo hi := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  have := hg a ha
  cases a <;> simp only [isConstAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨rfl, he⟩ := hp
  rw [← eEqb_sound he]
  exact this

/-- A guard's words: `1 + N` and the counter's `1`. -/
theorem guardOk_vals {σ : Val} {P : List Stmt} {gc : V} {f : String} {one N : V} {rest : List V}
    (h : guardOk P gc f one N rest = true) (hat : ∀ a ∈ atomsIn P, a.Holds rd σ) :
    σ gc = 1 + σ N ∧ σ one = 1 := by
  simp only [guardOk, Bool.and_eq_true] at h
  obtain ⟨⟨-, ha⟩, h1⟩ := h
  split at ha
  · rename_i p q hpq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨hp1, rfl⟩ := ha
    exact ⟨by rw [addOf_sound hpq hat, const_sound hp1 hat, word_one],
      by rw [const_sound h1 hat, word_one]⟩
  · exact absurd ha (by simp)

/-- The claim an accepting batching writes. -/
theorem batch_out {cs : List ChildClaims} {h : BatchingHints} {out : DeferredClaim}
    (hb : batch cs h = some out) :
    out = aggOut cs h ∧ (aggRun cs h).1.2 =
      h.finalBytecodeValue * Batch.batchedBytecodeWeight cs (aggLam cs).1 (aggRun cs h).1.1 := by
  rw [batch_fs] at hb
  split at hb
  · rename_i hc
    exact ⟨(Option.some.inj hb).symm, hc⟩
  · exact absurd hb (by simp)

theorem find_l25 : coreProgram.find? "__loop33" = some (coreProgram.getD 414 default) :=
  find_of_idx l25_idx (by rw [coreProgram_length]; omega)
theorem find_l26 : coreProgram.find? "__loop34" = some (coreProgram.getD 415 default) :=
  find_of_idx l26_idx (by rw [coreProgram_length]; omega)
theorem find_l27 : coreProgram.find? "__loop35" = some (coreProgram.getD 417 default) :=
  find_of_idx l27_idx (by rw [coreProgram_length]; omega)

theorem l25_shape' : loopShapeF (coreProgram.getD 414 default) "__loop33" = true := by
  have hok := l25_ok
  simp only [l25Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    -⟩, -⟩ := hok
  exact hshape

/-! ## The callees on the honest memory -/

section Kids

variable {cpi cfresh ccarried dst : E} {cs : List ChildClaims} {h : BatchingHints} {P : AggPtrs}

/-- The absorbing rows (`__loop33`), from its guard's counter `1`. -/
theorem agg_l25 (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (hmem : AggMem rd cfresh ccarried dst cs h P) :
    ∀ c < cs.length, LoopBlock rd (coreProgram.getD 414 default) (gen ^ c)
      (gen ^ cs.length) [P.absorb, cfresh, P.lf, ccarried, P.lc, cpi] := by
  intro c hc
  obtain ⟨-, -, -, -, -, -, hpi, hfr, hca⟩ := kid_reads (hcw c hc)
  have hnext := hmem.absorb (c + 1) hc
  rw [absSt_succ hc (hcw c hc), show P.absorb * (gen ^ (c + 1)) ^ 13 =
    P.absorb * (gen ^ c) ^ 13 * gen ^ 13 by ring] at hnext
  exact l25_block (absSt_ok _ _ _) (absSt_pend hcw c hc.le) (hmem.absorb c hc.le) hnext
    (hmem.lf c hc) (hmem.lc c hc) hpi hfr hca

/-- The records of `bc_chain` (`__loop34`). -/
theorem agg_l26 (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (hmem : AggMem rd cfresh ccarried dst cs h P) :
    ∀ c < cs.length, LoopBlock rd (coreProgram.getD 415 default) (gen ^ c)
      (gen ^ cs.length) [P.chain, P.lf, P.lc, lamA cs * lamA cs, lamA cs] := by
  intro c hc
  obtain ⟨-, -, -, -, hfv, hcv, -, -, -⟩ := kid_reads (hcw c hc)
  have hnext := hmem.chain (c + 1) hc
  rw [claimAt_succ hc, show P.chain * (gen ^ (c + 1)) ^ 2 = P.chain * (gen ^ c) ^ 2 * gen ^ 2 by
    ring, show lamA cs ^ (2 * (c + 1)) = lamA cs ^ (2 * c) * (lamA cs * lamA cs) by ring] at hnext
  exact l26_block (hmem.chain c hc.le) hnext (hmem.lf c hc) (hmem.lc c hc) hfv hcv

/-- The weights (`__loop35`). -/
theorem agg_l27 (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (hrl : h.sumcheckMessages.length = 23) (hmem : AggMem rd cfresh ccarried dst cs h P) :
    ∀ c < cs.length, LoopBlock rd (coreProgram.getD 417 default) (gen ^ c)
      (gen ^ cs.length) [P.lf, P.lc, P.pt1, P.chain, P.w, lamA cs] := by
  intro c hc
  have hptl : ((aggRun cs h).1.1.map (1 + ·)).length = 23 := by
    rw [List.length_map, aggRun, bsRun_len, hrl]
  obtain ⟨hpl, hql, hpf, hpc, -, -, -, -, -⟩ := kid_reads (hcw c hc)
  have hw1 := hmem.w (c + 1) hc
  rw [weightAt_succ hc, show P.w * gen ^ (c + 1) = P.w * gen ^ c * gen ^ 1 by ring,
    loadHolds_mul_gen_pow, ← map_one_add_twice (aggRun cs h).1.1] at hw1
  exact l27_block (hmem.lf c hc) (hmem.lc c hc) hpf hpc hmem.pt1 hpl hql hptl
    (hmem.chain c hc.le 0 (by simp)) (hmem.w c hc.le) hw1

/-- The sumcheck (`batch_sumcheck__L23`), from the permutation's capacity and the last record's
claim. -/
theorem agg_bs (hrl : h.sumcheckMessages.length = 23) (hmem : AggMem rd cfresh ccarried dst cs h P) :
    coreProgram.Rel rd "batch_sumcheck__L23"
      (capOf (aggAbs cs).perm ++ [P.msgs, claimAt cs cs.length, P.pt])
      ((aggRun cs h).2.cap ++ [(aggRun cs h).1.2]) := by
  have hrun : bsRun h.sumcheckMessages (claimAt cs cs.length)
      ⟨capOf (aggAbs cs).perm, []⟩ = aggRun cs h := by
    rw [aggRun, claimAt_last rfl, aggLam_snd]
  refine (batch_sumcheck_holds rd _ _).mpr ⟨capOf_canonical _, h.sumcheckMessages, hrl, hmem.msgs,
    ?_, ?_⟩
  · show ReadsAt rd P.pt (bsRun h.sumcheckMessages (claimAt cs cs.length)
      ⟨capOf (aggAbs cs).perm, []⟩).1.1
    rw [hrun]; exact hmem.pt
  · show _ = (bsRun h.sumcheckMessages (claimAt cs cs.length) ⟨capOf (aggAbs cs).perm, []⟩).2.cap ++
      [(bsRun h.sumcheckMessages (claimAt cs cs.length) ⟨capOf (aggAbs cs).perm, []⟩).1.2]
    rw [hrun]

end Kids

/-! ## The honest valuation -/

/-- `aggregate_claims`' honest valuation: its body evaluated on its arguments, the hints and the
sumcheck's returns `aggOrc`'s. -/
noncomputable def aggσ (rd : Reader) (m : ℕ) (cpi cfresh ccarried dst : E) (P : AggPtrs)
    (cs : List ChildClaims) (h : BatchingHints) : Val :=
  B1.Val.ofArgs (ev rd (aggOrc P h (aggRun cs h)) [gen ^ m, cpi, cfresh, ccarried, dst]
    (Fn.body Data.core33))

/-- **What `aggregate_claims`' honest valuation is**: its atoms hold, and its words. -/
structure AggVals (rd : Reader) (σ : Val) (m : ℕ) (cpi cfresh ccarried dst : E) (P : AggPtrs)
    (cs : List ChildClaims) (h : BatchingHints) : Prop where
  atoms : ∀ a ∈ atomsIn aggP, a.Holds rd σ
  e0 : σ (.n 0) = gen ^ m
  e1 : σ (.n 1) = cpi
  e2 : σ (.n 2) = cfresh
  e3 : σ (.n 3) = ccarried
  e4 : σ (.n 4) = dst
  v5 : σ (.n 5) = P.msgs
  v7 : σ (.n 7) = P.lf
  v8 : σ (.n 8) = P.lc
  v60 : σ (.n 60) = P.absorb
  v106 : σ (.n 106) = lamA cs
  v107 : σ (.n 107) = lamA cs * lamA cs
  v111 : σ (.n 111) = P.chain
  v120 : σ (.n 120) = P.pt
  v127 : σ (.n 127) = P.pt1
  v199 : σ (.n 199) = P.w
  p69 : σ (.n 69) = P.absorb * (gen ^ m) ^ 13
  p118 : σ (.n 118) = P.chain * (gen ^ m) ^ 2
  p204 : σ (.n 204) = P.w * gen ^ m
  g62 : σ (.n 62) = 1 + gen ^ m
  g63 : σ (.n 63) = 1
  g115 : σ (.n 115) = 1 + gen ^ m
  g116 : σ (.n 116) = 1
  g202 : σ (.n 202) = 1 + gen ^ m
  g203 : σ (.n 203) = 1
  bsArgs : [σ (.n 95), σ (.n 96), σ (.n 97), σ (.n 98), σ (.n 99), σ (.n 5), σ (.n 119),
    σ (.n 120)] = capOf (aggAbs cs).perm ++ [P.msgs, claimAt cs m, P.pt]
  bsRets : [σ (.n 121), σ (.n 122), σ (.n 123), σ (.n 124), σ (.n 125), σ (.n 126)] =
    (aggRun cs h).2.cap ++ [(aggRun cs h).1.2]

set_option maxRecDepth 20000 in
/-- **`aggregate_claims`' honest valuation** on `m` children whose words the memory holds, the
hints of an accepting batching and the honest memory at its buffers `P`. -/
theorem agg_core {m : ℕ} {cpi cfresh ccarried dst : E}
    {cs : List ChildClaims} (hcl : cs.length = m)
    {h : BatchingHints} {out : DeferredClaim} (hrl : h.sumcheckMessages.length = 23)
    (hb : batch cs h = some out) {P : AggPtrs} (hmem : AggMem rd cfresh ccarried dst cs h P) :
    AggVals rd (aggσ rd m cpi cfresh ccarried dst P cs h) m cpi cfresh ccarried dst P cs h := by
  subst hcl
  obtain ⟨hout, hfin⟩ := batch_out hb
  subst hout
  -- the checks
  have hok := agg_ok
  simp only [aggOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hparams⟩, hseed⟩, hp0⟩, hc23⟩, hp23⟩, hc33⟩, hp33⟩,
    hc43⟩, hp43⟩, -⟩, hg25⟩, -⟩, hk⟩, hrin⟩, hch⟩, hm107⟩, hc112⟩, -⟩, hc113⟩, -⟩, hg26⟩, -⟩, -⟩,
    -⟩, hpt1⟩, hc200⟩, -⟩, hg27⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hseed hpt1
  have hcok := aggc_ok
  simp only [aggCOk, Bool.and_eq_true, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hcanA⟩, hneeds⟩, hpk⟩, hll⟩, hhints⟩, hcallsAll⟩, hcallsIn⟩, hm69⟩,
    hm118⟩, hm204⟩, hm206⟩, hadd⟩ := hcok
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hneeds
  simp only [List.all_eq_true, List.mem_range] at hadd
  simp only [List.all_eq_true, decide_eq_true_eq] at hll hhints hcallsAll hcallsIn
  have hS := agg_stores
  have hbody := agg_shape
  -- the honest run
  obtain ⟨SF, hSF⟩ := bsRun_cap h.sumcheckMessages (Batch.batchedClaim cs (aggLam cs).1) (aggLam cs).2
    (by intro h0; rw [h0] at hrl; simp at hrl)
  have hres2 : (aggRun cs h).2 = ⟨capOf SF, []⟩ := hSF
  have hptl : (aggRun cs h).1.1.length = 23 := by rw [aggRun, bsRun_len, hrl]
  -- the valuation
  let w : ℕ → E := aggOrc P h (aggRun cs h)
  let args : List E := [gen ^ cs.length, cpi, cfresh, ccarried, dst]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = aggσ rd cs.length cpi cfresh ccarried dst P cs h := ⟨_, rfl⟩
  rw [← hσ]
  have hσ' : σ = B1.Val.ofArgs (ev rd w args (Fn.body Data.core33)) := hσ
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ']; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd w (Fn.body Data.core33) args hchk
  rw [show args.length = 5 from rfl, ← hσ', hS] at hgs
  have hmemP : ∀ s ∈ aggP, s ∈ Fn.body Data.core33 := fun s hs => by
    rw [hbody]; exact List.mem_append_left _ hs
  have hg : ∀ a ∈ atomsIn aggP, Good rd aggStores w σ a := fun a ha =>
    hgs (.atom a) (hmemP _ (atom_mem_of_atomsIn ha))
  have par : ∀ i (hi : i < 5), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ']; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = gen ^ cs.length := par 0 (by omega)
  have e1 : σ (.n 1) = cpi := par 1 (by omega)
  have e2 : σ (.n 2) = cfresh := par 2 (by omega)
  have e3 : σ (.n 3) = ccarried := par 3 (by omega)
  have e4 : σ (.n 4) = dst := par 4 (by omega)
  -- the hints and the sumcheck's returns
  have hint : ∀ a ∈ aggHintsA, Good rd aggStores w σ a := fun a ha => hg a (hhints a ha)
  simp only [aggHintsA, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Good] at hint
  obtain ⟨h5, h6, h7, h8, h60, h111, h120, h127, h199⟩ := hint
  have v5 : σ (.n 5) = P.msgs := by rw [h5]; rfl
  have v6 : σ (.n 6) = h.finalBytecodeValue := by rw [h6]; rfl
  have v7 : σ (.n 7) = P.lf := by rw [h7]; rfl
  have v8 : σ (.n 8) = P.lc := by rw [h8]; rfl
  have v60 : σ (.n 60) = P.absorb := by rw [h60]; rfl
  have v111 : σ (.n 111) = P.chain := by rw [h111]; rfl
  have v120 : σ (.n 120) = P.pt := by rw [h120]; rfl
  have v127 : σ (.n 127) = P.pt1 := by rw [h127]; rfl
  have v199 : σ (.n 199) = P.w := by rw [h199]; rfl
  have hret : GoodS rd aggStores w σ (.call "batch_sumcheck__L23"
      [.n 95, .n 96, .n 97, .n 98, .n 99, .n 5, .n 119, .n 120]
      [.n 121, .n 122, .n 123, .n 124, .n 125, .n 126]) := by
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp (hcallsIn (.call "batch_sumcheck__L23"
      [.n 95, .n 96, .n 97, .n 98, .n 99, .n 5, .n 119, .n 120]
      [.n 121, .n 122, .n 123, .n 124, .n 125, .n 126])
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    rw [← stmtEqb_sound he]
    exact hgs s (hmemP s hs)
  simp only [GoodS, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hret
  obtain ⟨r121, r122, r123, r124, r125, r126⟩ := hret
  have v126 : σ (.n 126) = (aggRun cs h).1.2 := by rw [r126]; rfl
  -- the products
  have hP : ∀ a ∈ (atomsIn aggP).filter pureB, a.Holds rd σ := pure_holds hg
  have p69 : σ (.n 69) = P.absorb * (gen ^ cs.length) ^ 13 := by
    rw [monoIs_sound hm69 hP, v60, e0]
  have p118 : σ (.n 118) = P.chain * (gen ^ cs.length) ^ 2 := by
    rw [monoIs_sound hm118 hP, v111, e0]
  have p204 : σ (.n 204) = P.w * gen ^ cs.length := by rw [isMul_sound hm204 hP, v199, e0]
  -- the loads
  have hg' : ∀ a ∈ aggA, Good rd aggStores w σ a := fun a ha => hg a (mem_aggA.mp ha).1
  have hnS : ∀ a ∈ aggA, a ∉ aggStores := fun a ha => (mem_aggA.mp ha).2
  have hokA := aggAbs_ok cs
  have hlast := hmem.absorb cs.length le_rfl
  rw [absSt_last rfl] at hlast
  have hchm := hmem.chain cs.length le_rfl
  have L70 : ∀ k (hk : k < 13), σ (.n (70 + k)) = (rowW (aggAbs cs)).getD k 0 ∧
      (Atom.load (.n (70 + k)) (.n 69) k).Holds rd σ := fun k hk => by
    have hm : Atom.load (.n (70 + k)) (.n 69) k ∈ aggA := hll _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [p69, List.getD_eq_getElem _ _ (by rw [rowW_length hokA]; exact hk)]
    exact hlast k (by rw [rowW_length hokA]; exact hk)
  have L119 : σ (.n 119) = claimAt cs cs.length ∧ (Atom.load (.n 119) (.n 118) 1).Holds rd σ := by
    have hm : Atom.load (.n 119) (.n 118) 1 ∈ aggA := hll _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_singleton_self _)))))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [p118]
    exact hchm 1 (by simp)
  have L129 : ∀ k (hk : k < 23), σ (.n (129 + 3 * k)) = (aggRun cs h).1.1.getD k 0 ∧
      (Atom.load (.n (129 + 3 * k)) (.n 120) k).Holds rd σ := fun k hk => by
    have hm : Atom.load (.n (129 + 3 * k)) (.n 120) k ∈ aggA := hll _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [v120, List.getD_eq_getElem _ _ (by rw [hptl]; exact hk)]
    exact hmem.pt k (by rw [hptl]; exact hk)
  have L205 : σ (.n 205) = weightAt cs h cs.length ∧ (Atom.load (.n 205) (.n 204) 0).Holds rd σ := by
    have hm : Atom.load (.n 205) (.n 204) 0 ∈ aggA := hll _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_singleton_self _)))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [p204]
    exact hmem.w cs.length le_rfl
  have L207 : ∀ k (hk : k < 23), σ (.n (207 + k)) = (aggRun cs h).1.1.getD k 0 ∧
      (Atom.load (.n (207 + k)) (.n 120) k).Holds rd σ := fun k hk => by
    have hm : Atom.load (.n (207 + k)) (.n 120) k ∈ aggA := hll _ (List.mem_append_right _
      (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [v120, List.getD_eq_getElem _ _ (by rw [hptl]; exact hk)]
    exact hmem.pt k (by rw [hptl]; exact hk)
  -- the permutation's atom
  have hkm : Atom.keccak aggKi aggKo false false ∈ atomsIn aggP := by
    obtain ⟨a, ha, he⟩ := List.any_eq_true.mp hk
    cases a <;> simp only [isKeccakAt, Bool.false_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at he
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := he
    exact ha
  have c88 : IsCanonical128 (σ (.n 88)) := by
    have := keccak_out_canon (hg _ hkm) (c := 1) (by omega)
    rwa [show aggKo.getD 1 default = .n 88 by rfl] at this
  have hAc : ∀ i ∈ (List.range 13).map (70 + ·), IsCanonical128 (σ (.n i)) := by
    intro i hi
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hi
    have ho' := List.mem_range.mp ho
    rw [(L70 o ho').1]
    exact rowW_canonical hokA _ (getD_mem (by rw [rowW_length hokA]; exact ho'))
  -- the atoms but the stores
  have hat' : ∀ a ∈ aggA, a.Holds rd σ := by
    refine atoms_holds hidx hcanA hg' hAc fun a ha hns => Or.inl ?_
    rcases hneeds a ha with (((hx | hx) | hx) | rfl) | rfl
    · rw [hns] at hx; exact absurd hx (by simp)
    · exact pack_inK hpk hg' hx
    · simp only [aggLoads, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with (((⟨k, hk, rfl⟩ | rfl) | ⟨k, hk, rfl⟩) | rfl) | ⟨k, hk, rfl⟩
      · exact (L70 k hk).2
      · exact L119.2
      · exact (L129 k hk).2
      · exact L205.2
      · exact (L207 k hk).2
    · exact chal_inK hch hg c88
    · show σ (.n 126) + σ (.n 206) = 0
      rw [isMul_sound hm206 hP, v126, v6, L205.1, weightAt_last rfl]
      exact e_add_eq_zero_iff.mpr hfin
  -- the stores
  have hst0 := absSt_ok cs.length cs 0
  have hrow0 := hmem.absorb 0 (Nat.zero_le _)
  rw [pow_zero, one_pow, mul_one] at hrow0
  have r0 : ∀ k < 13, LoadHolds rd (σ (.n 60)) k ((rowW (absSt cs.length cs 0)).getD k 0) :=
    fun k hk => by
      rw [v60, List.getD_eq_getElem _ _ (by rw [rowW_length hst0]; exact hk)]
      exact hrow0 k (by rw [rowW_length hst0]; exact hk)
  have hpack : ∀ j < 4, ∀ (x : V) (b : ℕ), packIn (atomsIn aggP) x b = true →
      σ x = [gen ^ cs.length, 0, 0, 0].getD j 0 →
      LoadHolds rd (σ (.n 60)) (5 + 2 * j) (σ (.n (b + 6))) ∧
        LoadHolds rd (σ (.n 60)) (6 + 2 * j) (σ (.n (b + 8))) := by
    intro j hj x b hpb hx
    have hpc := pack_cells hpb hg
    have hr := Keccak.rateCell_scalar (absSt cs.length cs 0).pend j (by rw [absSt_zero]; simp; omega)
    have hpj : (absSt cs.length cs 0).pend[j]'(by rw [absSt_zero]; simp; omega) =
        ([gen ^ cs.length, 0, 0, 0].getD j 0, dsObserve) := by
      simp only [absSt_zero]
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
    rw [hpj, ← hx, ← hpc] at hr
    simp only [Prod.ext_iff] at hr
    have a := r0 (5 + 2 * j) (by omega)
    have b' := r0 (5 + (2 * j + 1)) (by omega)
    rw [rowW_getD_rate hst0 (by omega), hr.1] at a
    rw [rowW_getD_rate hst0 (by omega), hr.2, show 5 + (2 * j + 1) = 6 + 2 * j by omega] at b'
    exact ⟨a, b'⟩
  have hch0 := hmem.chain 0 (Nat.zero_le _)
  rw [pow_zero, one_pow, mul_one] at hch0
  have hdst := hmem.dst
  have hdl : (aggOut cs h).cells.length = 24 := by simp [aggOut, DeferredClaim.cells, hptl]
  have hstores : ∀ a ∈ aggStores, a.Holds rd σ := by
    intro a haS
    simp only [aggStores, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at haS
    rcases haS with ((((((⟨i, hi, rfl⟩ | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
      (rfl | rfl)) | ⟨k, hk, rfl⟩) | rfl) | ⟨k, hk, rfl⟩) | rfl)
    · show LoadHolds rd (σ (.n 60)) i (σ (.n (9 + i)))
      have e := r0 i (by omega)
      rw [rowW_getD_cap hst0 hi, absSt_zero, ← seed_cells i hi, ← const_good (hseed i hi).1 hg] at e
      exact e
    · exact (hpack 0 (by omega) (.n 0) 14 hp0 (by rw [e0]; rfl)).1
    · exact (hpack 0 (by omega) (.n 0) 14 hp0 (by rw [e0]; rfl)).2
    · exact (hpack 1 (by omega) (.n 23) 24 hp23 (by rw [const_good hc23 hg, word_zero]; rfl)).1
    · exact (hpack 1 (by omega) (.n 23) 24 hp23 (by rw [const_good hc23 hg, word_zero]; rfl)).2
    · exact (hpack 2 (by omega) (.n 33) 34 hp33 (by rw [const_good hc33 hg, word_zero]; rfl)).1
    · exact (hpack 2 (by omega) (.n 33) 34 hp33 (by rw [const_good hc33 hg, word_zero]; rfl)).2
    · exact (hpack 3 (by omega) (.n 43) 44 hp43 (by rw [const_good hc43 hg, word_zero]; rfl)).1
    · exact (hpack 3 (by omega) (.n 43) 44 hp43 (by rw [const_good hc43 hg, word_zero]; rfl)).2
    · show LoadHolds rd (σ (.n 111)) 0 (σ (.n 112))
      have e := hch0 0 (by simp)
      rw [v111, const_good hc112 hg, word_one]
      simpa using e
    · show LoadHolds rd (σ (.n 111)) 1 (σ (.n 113))
      have e := hch0 1 (by simp)
      rw [v111, const_good hc113 hg, word_zero]
      simpa [claimAt_zero] using e
    · show LoadHolds rd (σ (.n 127)) k (σ (.n (130 + 3 * k)))
      have e := hmem.pt1 k (by rw [List.length_map, hptl]; exact hk)
      rw [List.getElem_map, ← List.getD_eq_getElem _ 0] at e
      rw [v127, add_sound (hadd k hk) hP, const_good (hpt1 k hk).1.1.1 hg, word_one, (L129 k hk).1]
      exact e
    · show LoadHolds rd (σ (.n 199)) 0 (σ (.n 200))
      have e := hmem.w 0 (Nat.zero_le _)
      rw [pow_zero, mul_one, weightAt_zero] at e
      rw [v199, const_good hc200 hg, word_zero]
      exact e
    · show LoadHolds rd (σ (.n 4)) k (σ (.n (207 + k)))
      have e := hdst k (by rw [hdl]; omega)
      rw [← List.getD_eq_getElem _ 0] at e
      rw [e4, (L207 k hk).1]
      have : (aggOut cs h).cells.getD k 0 = (aggRun cs h).1.1.getD k 0 := by
        rw [aggOut, DeferredClaim.cells, List.getD_append _ _ _ _ (by rw [hptl]; exact hk)]
      rw [this] at e
      exact e
    · show LoadHolds rd (σ (.n 4)) 23 (σ (.n 6))
      have e := hdst 23 (by rw [hdl]; omega)
      rw [← List.getD_eq_getElem _ 0] at e
      rw [e4, v6]
      have : (aggOut cs h).cells.getD 23 0 = h.finalBytecodeValue := by
        rw [aggOut, DeferredClaim.cells, List.getD_append_right _ _ _ _ (by rw [hptl]), hptl]
        rfl
      rw [this] at e
      exact e
  have hat : ∀ a ∈ atomsIn aggP, a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ aggStores
    · exact hstores a haS
    · exact hat' a (mem_aggA.mpr ⟨ha, haS⟩)
  obtain ⟨g62, g63⟩ := guardOk_vals hg25 hat
  obtain ⟨g115, g116⟩ := guardOk_vals hg26 hat
  obtain ⟨g202, g203⟩ := guardOk_vals hg27 hat
  -- the permutation and `λ`
  have hin := rowIn_sound hrin hat
  obtain ⟨hcan, hout1⟩ := DupSpec.keccak_facts (keccak_sound hk hat)
  rw [hin] at hcan hout1
  have hperm := rowRel_perm (rowRel_of_reads hokA (by rw [p69]; exact hlast))
    (fun c hc => hcan c (List.mem_append_left _ hc))
  rw [← hperm] at hout1
  have o : ∀ c (hc : c < 13), σ (.n (87 + c)) = cellsOfState (aggAbs cs).perm false ⟨c, hc⟩ :=
    fun c hc => by
      have := hout1 c hc
      rwa [show aggKo.getD c default = .n (87 + c) by
        simp [aggKo, List.getD_eq_getElem?_getD, hc]] at this
  have v106 : σ (.n 106) = lamA cs :=
    challengeT_value (chal_sound hch hat) (o 0 (by omega)) (o 1 (by omega))
  have hcap : [σ (.n 95), σ (.n 96), σ (.n 97), σ (.n 98), σ (.n 99)] = capOf (aggAbs cs).perm := by
    have o8 : σ (.n 95) = cellsOfState (aggAbs cs).perm false 8 := o 8 (by omega)
    have o9 : σ (.n 96) = cellsOfState (aggAbs cs).perm false 9 := o 9 (by omega)
    have o10 : σ (.n 97) = cellsOfState (aggAbs cs).perm false 10 := o 10 (by omega)
    have o11 : σ (.n 98) = cellsOfState (aggAbs cs).perm false 11 := o 11 (by omega)
    have o12 : σ (.n 99) = cellsOfState (aggAbs cs).perm false 12 := o 12 (by omega)
    rw [o8, o9, o10, o11, o12]
    rfl
  refine ⟨hat, e0, e1, e2, e3, e4, v5, v7, v8, v60, v106, by rw [isMul_sound hm107 hat, v106],
    v111, v120, v127, v199, p69, p118, p204, by rw [g62, e0], g63, by rw [g115, e0], g116,
    by rw [g202, e0], g203, ?_, ?_⟩
  · rw [← hcap, v5, L119.1, v120]; rfl
  · rw [r121, r122, r123, r124, r125, r126]
    show [(aggRun cs h).2.cap.getD 0 0, (aggRun cs h).2.cap.getD 1 0,
      (aggRun cs h).2.cap.getD 2 0, (aggRun cs h).2.cap.getD 3 0,
      (aggRun cs h).2.cap.getD 4 0, (aggRun cs h).1.2] = _
    rw [hres2]
    rfl

end
end LeanVM.Guest.B1.Main
