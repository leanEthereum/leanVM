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
public import LeanVM.Guest.B1.Sumcheck.Batch

/-!
# `aggregate_claims`, completely

The honest valuation is the body evaluated (`Fwd.ev`) on the arguments, the hints and the
sumcheck's returns its honest ones (`aggOrc`: the buffers `P`, `bc_star_hint`, the sumcheck's
final capacity and claim). Its atoms hold (their side conditions its loads and the final check,
which `batch cs h = some out` is), its stores find the first record, weight and the claim; its
permutations are the last absorbing row's and the nonce's, whose cell `0` is `λ` (`lamA`) and
cell `1` passes the proof of work (`agg_pow`); its calls hold by their completeness: the absorbing
rows (`l25_block`), the records (`l26_block`), the sumcheck (`agg_bs`, from
`batch_sumcheck_holds`), the weights (`l27_block`) and `grind_check__L2` (its arguments
`AggVals.grArgs`, for the caller's hypothesis).

`agg_core` is pointer-parametric (any `AggPtrs` holding `AggMem`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Da LeanVM.Node

@[expose] public section

variable {rd : Reader}

/-- The oracle of `aggregate_claims`' hints and its sumcheck's returns `res`. -/
def aggOrc (P : AggPtrs) (h : BatchingHints) (res : (List E × E) × Fs) (j : ℕ) : E :=
  if j = 6 then P.msgs else if j = 7 then h.finalBytecodeValue else if j = 8 then P.lf
  else if j = 9 then P.lc else if j = 33 then P.absorb else if j = 98 then P.chain
  else if j = 107 then P.pt else if j = 116 then P.pt1 else if j = 188 then P.w
  else if j = 115 then res.1.2 else if 110 ≤ j ∧ j < 115 then res.2.cap.getD (j - 110) 0 else 0

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

/-- The claim an accepting batching writes, its proof of work and its final check. -/
theorem batch_out {cs : List ChildClaims} {h : BatchingHints} {out : DeferredClaim}
    (hb : batch cs h = some out) :
    out = aggOut cs h ∧
      powOk Batch.batchLambdaGrindBits (Keccak.lane (aggN cs h.lambdaGrindNonce) 2) = true ∧
      (aggRun cs h).1.2 = h.finalBytecodeValue *
        Batch.batchedBytecodeWeight cs (aggLam cs h.lambdaGrindNonce).1 (aggRun cs h).1.1 := by
  rw [batch_fs] at hb
  split at hb
  · rename_i hp
    split at hb
    · rename_i hc
      exact ⟨(Option.some.inj hb).symm, hp, hc⟩
    · exact absurd hb (by simp)
  · exact absurd hb (by simp)

/-- **The nonce's permutation passes the proof of work**: `grind_check__L2`'s condition on its
cell `1`. -/
theorem agg_pow {cs : List ChildClaims} {n : E}
    (h : powOk Batch.batchLambdaGrindBits (Keccak.lane (aggN cs n) 2) = true) :
    ((cellsOfState (aggN cs n) false 1).limb 0).lane.toNat % 2 ^ 2 = 0 :=
  (grindOk_iff (s := aggAbs cs) (bits := 2) (by omega) n).mp (Or.inr h)

theorem find_l25 : coreProgram.find? "__loop33" = some (coreProgram.getD 430 default) :=
  find_of_idx l25_idx (by rw [coreProgram_length]; omega)
theorem find_l26 : coreProgram.find? "__loop34" = some (coreProgram.getD 432 default) :=
  find_of_idx l26_idx (by rw [coreProgram_length]; omega)
theorem find_l27 : coreProgram.find? "__loop35" = some (coreProgram.getD 434 default) :=
  find_of_idx l27_idx (by rw [coreProgram_length]; omega)

theorem l25_shape' : loopShapeF (coreProgram.getD 430 default) "__loop33" = true := by
  have hok := l25_ok
  simp only [l25Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    -⟩, -⟩ := hok
  exact hshape

/-- Words read from `p`, but the first, are read from `p · g`. -/
theorem readsAt_tail {p x : E} {xs : List E} (h : ReadsAt rd p (x :: xs)) : ReadsAt rd (p * gen) xs :=
  fun k hk => by
    rw [← pow_one gen, loadHolds_mul_gen_pow]
    have hk' : 1 + k < (x :: xs).length := by simp; omega
    have := h (1 + k) hk'
    rwa [show (x :: xs)[1 + k]'hk' = xs[k] by simp [Nat.add_comm]] at this

/-! ## The callees on the honest memory -/

section Kids

variable {cpi cfresh ccarried dst : E} {cs : List ChildClaims} {h : BatchingHints} {P : AggPtrs}

/-- The absorbing rows (`__loop33`), from its guard's counter `1`. -/
theorem agg_l25 (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (hmem : AggMem rd cfresh ccarried dst cs h P) :
    ∀ c < cs.length, LoopBlock rd (coreProgram.getD 430 default) (gen ^ c)
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
    ∀ c < cs.length, LoopBlock rd (coreProgram.getD 432 default) (gen ^ c)
      (gen ^ cs.length) [P.chain, P.lf, P.lc, lamA cs h * lamA cs h, lamA cs h] := by
  intro c hc
  obtain ⟨-, -, -, -, hfv, hcv, -, -, -⟩ := kid_reads (hcw c hc)
  have hnext := hmem.chain (c + 1) hc
  rw [claimAt_succ hc, show P.chain * (gen ^ (c + 1)) ^ 2 = P.chain * (gen ^ c) ^ 2 * gen ^ 2 by
    ring, show lamA cs h ^ (2 * (c + 1)) = lamA cs h ^ (2 * c) * (lamA cs h * lamA cs h) by ring]
    at hnext
  exact l26_block (hmem.chain c hc.le) hnext (hmem.lf c hc) (hmem.lc c hc) hfv hcv

/-- The weights (`__loop35`). -/
theorem agg_l27 (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    (hrl : h.sumcheckMessages.length = 23) (hmem : AggMem rd cfresh ccarried dst cs h P) :
    ∀ c < cs.length, LoopBlock rd (coreProgram.getD 434 default) (gen ^ c)
      (gen ^ cs.length) [P.lf, P.lc, P.pt1, P.chain, P.w, lamA cs h] := by
  intro c hc
  have hptl : ((aggRun cs h).1.1.map (1 + ·)).length = 23 := by
    rw [List.length_map, aggRun, bsRun_len, hrl]
  obtain ⟨hpl, hql, hpf, hpc, -, -, -, -, -⟩ := kid_reads (hcw c hc)
  have hw1 := hmem.w (c + 1) hc
  rw [weightAt_succ hc, show P.w * gen ^ (c + 1) = P.w * gen ^ c * gen ^ 1 by ring,
    loadHolds_mul_gen_pow, ← map_one_add_twice (aggRun cs h).1.1] at hw1
  exact l27_block (hmem.lf c hc) (hmem.lc c hc) hpf hpc hmem.pt1 hpl hql hptl
    (hmem.chain c hc.le 0 (by simp)) (hmem.w c hc.le) hw1

/-- The sumcheck (`batch_sumcheck__L23`), from the nonce's permutation's capacity and the last
record's claim. -/
theorem agg_bs (tabs : E) (hrl : h.sumcheckMessages.length = 23)
    (hmem : AggMem rd cfresh ccarried dst cs h P) :
    coreProgram.Rel rd "batch_sumcheck__L23"
      (capOf (aggN cs h.lambdaGrindNonce) ++ [P.msgs * gen, claimAt cs h cs.length, P.pt, tabs])
      ((aggRun cs h).2.cap ++ [(aggRun cs h).1.2]) := by
  have hrun : bsRun h.sumcheckMessages (claimAt cs h cs.length)
      ⟨capOf (aggN cs h.lambdaGrindNonce), []⟩ = aggRun cs h := by
    rw [aggRun, claimAt_last rfl, aggLam_snd]
  refine (batch_sumcheck_holds rd _ _).mpr ⟨h.sumcheckMessages, hrl, readsAt_tail hmem.msgs, ?_, ?_⟩
  · show ReadsAt rd P.pt (bsRun h.sumcheckMessages (claimAt cs h cs.length)
      ⟨capOf (aggN cs h.lambdaGrindNonce), []⟩).1.1
    rw [hrun]; exact hmem.pt
  · show _ = (bsRun h.sumcheckMessages (claimAt cs h cs.length)
      ⟨capOf (aggN cs h.lambdaGrindNonce), []⟩).2.cap ++
      [(bsRun h.sumcheckMessages (claimAt cs h cs.length)
        ⟨capOf (aggN cs h.lambdaGrindNonce), []⟩).1.2]
    rw [hrun]

end Kids

/-! ## The honest valuation -/

/-- `aggregate_claims`' honest valuation: its body evaluated on its arguments, the hints and the
sumcheck's returns `aggOrc`'s. -/
noncomputable def aggσ (rd : Reader) (m : ℕ) (cpi cfresh ccarried dst tabs : E) (P : AggPtrs)
    (cs : List ChildClaims) (h : BatchingHints) : Val :=
  B1.Val.ofArgs (ev rd (aggOrc P h (aggRun cs h)) [gen ^ m, cpi, cfresh, ccarried, dst, tabs]
    (Fn.body Data.core33))

/-- **What `aggregate_claims`' honest valuation is**: its atoms hold, and its words. -/
structure AggVals (rd : Reader) (σ : Val) (m : ℕ) (cpi cfresh ccarried dst tabs : E) (P : AggPtrs)
    (cs : List ChildClaims) (h : BatchingHints) : Prop where
  atoms : ∀ a ∈ atomsIn aggP, a.Holds rd σ
  e0 : σ (.n 0) = gen ^ m
  e1 : σ (.n 1) = cpi
  e2 : σ (.n 2) = cfresh
  e3 : σ (.n 3) = ccarried
  e4 : σ (.n 4) = dst
  e5 : σ (.n 5) = tabs
  v6 : σ (.n 6) = P.msgs
  v8 : σ (.n 8) = P.lf
  v9 : σ (.n 9) = P.lc
  v33 : σ (.n 33) = P.absorb
  v81 : σ (.n 81) = lamA cs h
  v94 : σ (.n 94) = lamA cs h * lamA cs h
  v98 : σ (.n 98) = P.chain
  v107 : σ (.n 107) = P.pt
  v116 : σ (.n 116) = P.pt1
  v188 : σ (.n 188) = P.w
  p42 : σ (.n 42) = P.absorb * (gen ^ m) ^ 13
  p105 : σ (.n 105) = P.chain * (gen ^ m) ^ 2
  p193 : σ (.n 193) = P.w * gen ^ m
  g35 : σ (.n 35) = 1 + gen ^ m
  g36 : σ (.n 36) = 1
  g102 : σ (.n 102) = 1 + gen ^ m
  g103 : σ (.n 103) = 1
  g191 : σ (.n 191) = 1 + gen ^ m
  g192 : σ (.n 192) = 1
  grArgs : [σ (.n 82), σ (.n 5)] = [cellsOfState (aggN cs h.lambdaGrindNonce) false 1, tabs]
  bsArgs : [σ (.n 89), σ (.n 90), σ (.n 91), σ (.n 92), σ (.n 93), σ (.n 109), σ (.n 106),
    σ (.n 107), σ (.n 5)] = capOf (aggN cs h.lambdaGrindNonce) ++ [P.msgs * gen, claimAt cs h m, P.pt, tabs]
  bsRets : [σ (.n 110), σ (.n 111), σ (.n 112), σ (.n 113), σ (.n 114), σ (.n 115)] =
    (aggRun cs h).2.cap ++ [(aggRun cs h).1.2]

set_option maxRecDepth 20000 in
/-- **`aggregate_claims`' honest valuation** on `m` children whose words the memory holds, the
hints of an accepting batching and the honest memory at its buffers `P`. -/
theorem agg_core {m : ℕ} {cpi cfresh ccarried dst tabs : E}
    {cs : List ChildClaims} (hcl : cs.length = m)
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    {h : BatchingHints} {out : DeferredClaim} (hrl : h.sumcheckMessages.length = 23)
    (hb : batch cs h = some out) {P : AggPtrs} (hmem : AggMem rd cfresh ccarried dst cs h P) :
    AggVals rd (aggσ rd m cpi cfresh ccarried dst tabs P cs h) m cpi cfresh ccarried dst tabs P cs h := by
  subst hcl
  obtain ⟨hout, -, hfin⟩ := batch_out hb
  subst hout
  -- the checks
  have hok := agg_ok
  simp only [aggOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hparams⟩, hseed⟩, hp0⟩, hz3⟩, -⟩,
    hg33⟩, -⟩, hk⟩, hrin⟩, hnA⟩, hkn⟩, -⟩, -⟩, hc99⟩, -⟩, hc100⟩, -⟩, hg34⟩,
    -⟩, -⟩, -⟩, -⟩, hpt1⟩, hc189⟩, -⟩, hg35⟩, -⟩, -⟩, -⟩, -⟩,
    -⟩, -⟩ := hok
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hseed hz3 hpt1
  have hcok := aggc_ok
  simp only [aggCOk, Bool.and_eq_true, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hneeds⟩, -⟩, hll⟩, hhints⟩, -⟩, hcallsIn⟩, hm42⟩,
    hm105⟩, hm193⟩, hm195⟩, hg109⟩, hm94⟩, hadd⟩ := hcok
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hneeds
  simp only [List.all_eq_true, List.mem_range] at hadd
  simp only [List.all_eq_true, decide_eq_true_eq] at hll hhints hcallsIn
  have hS := agg_stores
  have hbody := agg_shape
  -- the honest run
  obtain ⟨SF, hSF⟩ := bsRun_cap h.sumcheckMessages
    (Batch.batchedClaim cs (aggLam cs h.lambdaGrindNonce).1) (aggLam cs h.lambdaGrindNonce).2
    (by intro h0; rw [h0] at hrl; simp at hrl)
  have hres2 : (aggRun cs h).2 = ⟨capOf SF, []⟩ := hSF
  have hptl : (aggRun cs h).1.1.length = 23 := by rw [aggRun, bsRun_len, hrl]
  -- the valuation
  let w : ℕ → E := aggOrc P h (aggRun cs h)
  let args : List E := [gen ^ cs.length, cpi, cfresh, ccarried, dst, tabs]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = aggσ rd cs.length cpi cfresh ccarried dst tabs P cs h := ⟨_, rfl⟩
  rw [← hσ]
  have hσ' : σ = B1.Val.ofArgs (ev rd w args (Fn.body Data.core33)) := hσ
  obtain ⟨-, -, hgs⟩ := ev_spec rd w (Fn.body Data.core33) args hchk
  rw [show args.length = 6 from rfl, ← hσ', hS] at hgs
  have hmemP : ∀ s ∈ aggP, s ∈ Fn.body Data.core33 := fun s hs => by
    rw [hbody]; exact List.mem_append_left _ hs
  have hg : ∀ a ∈ atomsIn aggP, Good rd aggStores w σ a := fun a ha =>
    hgs (.atom a) (hmemP _ (atom_mem_of_atomsIn ha))
  have par : ∀ i (hi : i < 6), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ']; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = gen ^ cs.length := par 0 (by omega)
  have e1 : σ (.n 1) = cpi := par 1 (by omega)
  have e2 : σ (.n 2) = cfresh := par 2 (by omega)
  have e3 : σ (.n 3) = ccarried := par 3 (by omega)
  have e4 : σ (.n 4) = dst := par 4 (by omega)
  have e5 : σ (.n 5) = tabs := par 5 (by omega)
  -- the hints and the sumcheck's returns
  have hint : ∀ a ∈ aggHintsA, Good rd aggStores w σ a := fun a ha => hg a (hhints a ha)
  simp only [aggHintsA, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Good] at hint
  obtain ⟨h6, h7, h8, h9, h33, h98, h107, h116, h188⟩ := hint
  have v6 : σ (.n 6) = P.msgs := by rw [h6]; rfl
  have v7 : σ (.n 7) = h.finalBytecodeValue := by rw [h7]; rfl
  have v8 : σ (.n 8) = P.lf := by rw [h8]; rfl
  have v9 : σ (.n 9) = P.lc := by rw [h9]; rfl
  have v33 : σ (.n 33) = P.absorb := by rw [h33]; rfl
  have v98 : σ (.n 98) = P.chain := by rw [h98]; rfl
  have v107 : σ (.n 107) = P.pt := by rw [h107]; rfl
  have v116 : σ (.n 116) = P.pt1 := by rw [h116]; rfl
  have v188 : σ (.n 188) = P.w := by rw [h188]; rfl
  have hret : GoodS rd aggStores w σ (.call "batch_sumcheck__L23"
      [.n 89, .n 90, .n 91, .n 92, .n 93, .n 109, .n 106, .n 107, .n 5]
      [.n 110, .n 111, .n 112, .n 113, .n 114, .n 115]) := by
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp (hcallsIn (.call "batch_sumcheck__L23"
      [.n 89, .n 90, .n 91, .n 92, .n 93, .n 109, .n 106, .n 107, .n 5]
      [.n 110, .n 111, .n 112, .n 113, .n 114, .n 115])
      (by simp [aggCalls]))
    rw [← stmtEqb_sound he]
    exact hgs s (hmemP s hs)
  simp only [GoodS, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hret
  obtain ⟨r110, r111, r112, r113, r114, r115⟩ := hret
  have v115 : σ (.n 115) = (aggRun cs h).1.2 := by rw [r115]; rfl
  -- the products
  have hP : ∀ a ∈ (atomsIn aggP).filter pureB, a.Holds rd σ := pure_holds hg
  have p42 : σ (.n 42) = P.absorb * (gen ^ cs.length) ^ 13 := by
    rw [monoIs_sound hm42 hP, v33, e0]
  have p105 : σ (.n 105) = P.chain * (gen ^ cs.length) ^ 2 := by
    rw [monoIs_sound hm105 hP, v98, e0]
  have p193 : σ (.n 193) = P.w * gen ^ cs.length := by rw [isMul_sound hm193 hP, v188, e0]
  -- the loads
  have hg' : ∀ a ∈ aggA, Good rd aggStores w σ a := fun a ha => hg a (mem_aggA.mp ha).1
  have hnS : ∀ a ∈ aggA, a ∉ aggStores := fun a ha => (mem_aggA.mp ha).2
  have hokA := aggAbs_ok cs
  have hlast := hmem.absorb cs.length le_rfl
  rw [absSt_last rfl] at hlast
  have hchm := hmem.chain cs.length le_rfl
  have L43 : ∀ k (hk : k < 13), σ (.n (43 + k)) = (rowW (aggAbs cs)).getD k 0 ∧
      (Atom.load (.n (43 + k)) (.n 42) k).Holds rd σ := fun k hk => by
    have hm : Atom.load (.n (43 + k)) (.n 42) k ∈ aggA := hll _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))))))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [p42, List.getD_eq_getElem _ _ (by rw [rowW_length hokA]; exact hk)]
    exact hlast k (by rw [rowW_length hokA]; exact hk)
  have L73 : σ (.n 73) = h.lambdaGrindNonce ∧ (Atom.load (.n 73) (.n 6) 0).Holds rd σ := by
    have hm : Atom.load (.n 73) (.n 6) 0 ∈ aggA := hll _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_singleton_self _))))))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [v6]
    exact hmem.msgs 0 (by simp)
  have L106 : σ (.n 106) = claimAt cs h cs.length ∧ (Atom.load (.n 106) (.n 105) 1).Holds rd σ := by
    have hm : Atom.load (.n 106) (.n 105) 1 ∈ aggA := hll _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_singleton_self _)))))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [p105]
    exact hchm 1 (by simp)
  have L118 : ∀ k (hk : k < 23), σ (.n (118 + 3 * k)) = (aggRun cs h).1.1.getD k 0 ∧
      (Atom.load (.n (118 + 3 * k)) (.n 107) k).Holds rd σ := fun k hk => by
    have hm : Atom.load (.n (118 + 3 * k)) (.n 107) k ∈ aggA := hll _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [v107, List.getD_eq_getElem _ _ (by rw [hptl]; exact hk)]
    exact hmem.pt k (by rw [hptl]; exact hk)
  have L194 : σ (.n 194) = weightAt cs h cs.length ∧ (Atom.load (.n 194) (.n 193) 0).Holds rd σ := by
    have hm : Atom.load (.n 194) (.n 193) 0 ∈ aggA := hll _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_singleton_self _)))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [p193]
    exact hmem.w cs.length le_rfl
  have L196 : ∀ k (hk : k < 23), σ (.n (196 + k)) = (aggRun cs h).1.1.getD k 0 ∧
      (Atom.load (.n (196 + k)) (.n 107) k).Holds rd σ := fun k hk => by
    have hm : Atom.load (.n (196 + k)) (.n 107) k ∈ aggA := hll _ (List.mem_append_right _
      (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
    refine load_of_good (hnS _ hm) (hg' _ hm) ?_
    rw [v107, List.getD_eq_getElem _ _ (by rw [hptl]; exact hk)]
    exact hmem.pt k (by rw [hptl]; exact hk)
  -- the atoms but the stores
  have hat' : ∀ a ∈ aggA, a.Holds rd σ := by
    refine atoms_holds hg' fun a ha hns => Or.inl ?_
    rcases hneeds a ha with ((hx | hx) | rfl)
    · rw [hns] at hx; exact absurd hx (by simp)
    · simp only [aggLoads, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with (((((⟨k, hk, rfl⟩ | rfl) | rfl) | ⟨k, hk, rfl⟩) | rfl) | ⟨k, hk, rfl⟩)
      · exact (L43 k hk).2
      · exact L73.2
      · exact L106.2
      · exact (L118 k hk).2
      · exact L194.2
      · exact (L196 k hk).2
    · show σ (.n 115) + σ (.n 195) = 0
      rw [isMul_sound hm195 hP, v115, v7, L194.1, weightAt_last rfl]
      exact e_add_eq_zero_iff.mpr hfin
  -- the stores
  have hst0 := absSt_ok cs.length cs 0
  have hrow0 := hmem.absorb 0 (Nat.zero_le _)
  rw [pow_zero, one_pow, mul_one] at hrow0
  have r0 : ∀ k < 13, LoadHolds rd (σ (.n 33)) k ((rowW (absSt cs.length cs 0)).getD k 0) :=
    fun k hk => by
      rw [v33, List.getD_eq_getElem _ _ (by rw [rowW_length hst0]; exact hk)]
      exact hrow0 k (by rw [rowW_length hst0]; exact hk)
  have hpack : ∀ j < 4, ∀ (x : V), packIn (atomsIn aggP) x (15 + 3 * j) = true →
      σ x = [gen ^ cs.length, 0, 0, 0].getD j 0 →
      LoadHolds rd (σ (.n 33)) (5 + 2 * j) (σ (.n (15 + 3 * j))) ∧
        LoadHolds rd (σ (.n 33)) (6 + 2 * j) (σ (.n (16 + 3 * j))) := by
    intro j hj x hpb hx
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
    rw [rowW_getD_rate hst0 (by omega), hr.2, show 5 + (2 * j + 1) = 6 + 2 * j by omega,
      show 15 + 3 * j + 1 = 16 + 3 * j by omega] at b'
    exact ⟨a, b'⟩
  have hpackZ : ∀ j < 3, LoadHolds rd (σ (.n 33)) (5 + 2 * (j + 1)) (σ (.n (15 + 3 * (j + 1)))) ∧
      LoadHolds rd (σ (.n 33)) (6 + 2 * (j + 1)) (σ (.n (16 + 3 * (j + 1)))) := by
    intro j hj
    obtain ⟨hc, hp⟩ := hz3 j hj
    refine hpack (j + 1) (by omega) (.n (17 + 3 * j))
      (by rw [show 15 + 3 * (j + 1) = 18 + 3 * j by omega]; exact hp) ?_
    rw [const_good hc hg, word_zero]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> rfl
  have hch0 := hmem.chain 0 (Nat.zero_le _)
  rw [pow_zero, one_pow, mul_one] at hch0
  have hdst := hmem.dst
  have hdl : (aggOut cs h).cells.length = 24 := by simp [aggOut, DeferredClaim.cells, hptl]
  have hstores : ∀ a ∈ aggStores, a.Holds rd σ := by
    intro a haS
    simp only [aggStores, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
      List.mem_cons, List.not_mem_nil, or_false] at haS
    rcases haS with ((((((⟨i, hi, rfl⟩ | ⟨j, hj, rfl | rfl⟩) | (rfl | rfl)) | ⟨k, hk, rfl⟩) | rfl) |
      ⟨k, hk, rfl⟩) | rfl)
    · show LoadHolds rd (σ (.n 33)) i (σ (.n (10 + i)))
      have e := r0 i (by omega)
      rw [rowW_getD_cap hst0 hi, absSt_zero, ← seed_cells i hi, ← const_good (hseed i hi).1 hg] at e
      exact e
    · rcases (show j = 0 ∨ 0 < j by omega) with rfl | hj0
      · exact (hpack 0 (by omega) (.n 0) hp0 (by rw [e0]; rfl)).1
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        exact (hpackZ j' (by omega)).1
    · rcases (show j = 0 ∨ 0 < j by omega) with rfl | hj0
      · exact (hpack 0 (by omega) (.n 0) hp0 (by rw [e0]; rfl)).2
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        exact (hpackZ j' (by omega)).2
    · show LoadHolds rd (σ (.n 98)) 0 (σ (.n 99))
      have e := hch0 0 (by simp)
      rw [v98, const_good hc99 hg, word_one]
      simpa using e
    · show LoadHolds rd (σ (.n 98)) 1 (σ (.n 100))
      have e := hch0 1 (by simp)
      rw [v98, const_good hc100 hg, word_zero]
      simpa [claimAt_zero] using e
    · show LoadHolds rd (σ (.n 116)) k (σ (.n (119 + 3 * k)))
      have e := hmem.pt1 k (by rw [List.length_map, hptl]; exact hk)
      rw [List.getElem_map, ← List.getD_eq_getElem _ 0] at e
      rw [v116, add_sound (hadd k hk) hP, const_good (hpt1 k hk).1.1.1 hg, word_one, (L118 k hk).1]
      exact e
    · show LoadHolds rd (σ (.n 188)) 0 (σ (.n 189))
      have e := hmem.w 0 (Nat.zero_le _)
      rw [pow_zero, mul_one, weightAt_zero] at e
      rw [v188, const_good hc189 hg, word_zero]
      exact e
    · show LoadHolds rd (σ (.n 4)) k (σ (.n (196 + k)))
      have e := hdst k (by rw [hdl]; omega)
      rw [← List.getD_eq_getElem _ 0] at e
      rw [e4, (L196 k hk).1]
      have : (aggOut cs h).cells.getD k 0 = (aggRun cs h).1.1.getD k 0 := by
        rw [aggOut, DeferredClaim.cells, List.getD_append _ _ _ _ (by rw [hptl]; exact hk)]
      rw [this] at e
      exact e
    · show LoadHolds rd (σ (.n 4)) 23 (σ (.n 7))
      have e := hdst 23 (by rw [hdl]; omega)
      rw [← List.getD_eq_getElem _ 0] at e
      rw [e4, v7]
      have : (aggOut cs h).cells.getD 23 0 = h.finalBytecodeValue := by
        rw [aggOut, DeferredClaim.cells, List.getD_append_right _ _ _ _ (by rw [hptl]), hptl]
        rfl
      rw [this] at e
      exact e
  have hat : ∀ a ∈ atomsIn aggP, a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ aggStores
    · exact hstores a haS
    · exact hat' a (mem_aggA.mpr ⟨ha, haS⟩)
  obtain ⟨g35, g36⟩ := guardOk_vals hg33 hat
  obtain ⟨g102, g103⟩ := guardOk_vals hg34 hat
  obtain ⟨g191, g192⟩ := guardOk_vals hg35 hat
  -- the last row's permutation
  have hin := rowIn_sound hrin hat
  have hout1 := DupSpec.keccak_facts (keccak_sound hk hat)
  rw [hin, ← rowRel_perm (rowRel_of_reads hokA (by rw [p42]; exact hlast))] at hout1
  have o : ∀ c (hc : c < 13), σ (.n (60 + c)) = cellsOfState (aggAbs cs).perm false ⟨c, hc⟩ :=
    fun c hc => by
      have := hout1 c hc
      rwa [show aggKo.getD c default = .n (60 + c) by
        simp [aggKo, List.getD_eq_getElem?_getD, hc]] at this
  -- the nonce's permutation
  have hnh := allIn_holds hnA hat (coreProgram.Rel rd) (fun _ => True)
  rw [aggNonceA_eq, holdsList_append, holds_fsNonceT, holds_padRunT] at hnh
  obtain ⟨⟨-, hpk⟩, ⟨-, h77, h78, h79, h80⟩, -⟩ := hnh
  obtain ⟨h74, h75⟩ := hpk
  have hpendm : (aggAbs cs).pend.length = 4 := by
    rw [← absSt_last rfl]; exact absSt_pend (m := cs.length) hcw cs.length le_rfl
  have hnin : aggNi.map σ = [σ (.n 73), word 0 dsPowNonce, 0, 0, 0, 0, 0, 0] ++
      capOf (aggAbs cs).perm := by
    simp only [aggNi, permIns, List.take, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil, h74, h75, h77, h78, h79, h80, capOf, o 8 (by omega), o 9 (by omega),
      o 10 (by omega), o 11 (by omega), o 12 (by omega)]
    rfl
  have hnout := DupSpec.keccak_facts (keccak_sound hkn hat)
  rw [hnin, ← nonce_ins (s := aggAbs cs) hpendm, L73.1, ← aggN] at hnout
  have q : ∀ c (hc : c < 13), σ (.n (81 + c)) =
      cellsOfState (aggN cs h.lambdaGrindNonce) false ⟨c, hc⟩ :=
    fun c hc => by
      have := hnout c hc
      rwa [show aggNo.getD c default = .n (81 + c) by
        simp [aggNo, List.getD_eq_getElem?_getD, hc]] at this
  have v81 : σ (.n 81) = lamA cs h := by
    rw [q 0 (by omega), lamA, Keccak.challengeOf_cells]
    rfl
  have q1 : σ (.n 82) = cellsOfState (aggN cs h.lambdaGrindNonce) false 1 := q 1 (by omega)
  refine ⟨hat, e0, e1, e2, e3, e4, e5, v6, v8, v9, v33, v81,
    by rw [isMul_sound hm94 hP, v81], v98, v107, v116, v188, p42, p105, p193,
    by rw [g35, e0], g36, by rw [g102, e0], g103, by rw [g191, e0], g192, by rw [q1, e5], ?_, ?_⟩
  · rw [q 8 (by omega), q 9 (by omega), q 10 (by omega), q 11 (by omega), q 12 (by omega),
      genMul_sound hg109 hP, v6, L106.1, v107, e5]
    rfl
  · rw [r110, r111, r112, r113, r114, r115]
    show [(aggRun cs h).2.cap.getD 0 0, (aggRun cs h).2.cap.getD 1 0,
      (aggRun cs h).2.cap.getD 2 0, (aggRun cs h).2.cap.getD 3 0,
      (aggRun cs h).2.cap.getD 4 0, (aggRun cs h).1.2] = _
    rw [hres2]
    rfl

end
end LeanVM.Guest.B1.Main
