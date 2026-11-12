/-
  LeanVM.Guest.B1.Main.LoopsC

  `main`'s loops under a call relation that unfolds: the iterations' facts with the witness
  carrying calls (the signature checks, the child proof's check) in that relation.
-/

module

public import LeanVM.Guest.B1.Main.Loops
public import LeanVM.Guest.B1.Main.Frames
public import LeanVM.Guest.B1.Sig.XmssSegData

/-!
# `main`'s loops, under a call relation

G6's knowledge statement names the witnesses as functions of the execution's frames, so `main`'s
soundness is stated for any call relation `C` that **unfolds** (`Unfolds`: a call holds only when
the callee's body does at some valuation, its calls in `C`; `Check.RL` by `relL_iff`,
`coreProgram.Rel` by `rel_iff`) and lies below `coreProgram.Rel` (the deterministic callees'
statements then apply). `loop_stepC`, `loop_soundC`, `guard_soundC` are `loop_stepF`,
`loop_sound`, `guard_sound` under `C`; `RawXStepC`, `RawSStepC`, `KidStepC` keep the signature
checks and the child proof's check in `C`, the other calls in `coreProgram.Rel`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-- **A call relation of the program that unfolds**: a call holds only when the callee's body
holds at some valuation of its parameters, its own calls in the same relation. -/
def Unfolds (rd : Reader) (C : CallRel) : Prop :=
  ∀ f args rets, C f args rets → ∃ (fn : Fn) (σ : Val), coreProgram.find? f = some fn ∧
    fn.params.map σ = args ∧ Stmt.HoldsList C rd σ fn.body False (fun rs => rs = rets)

theorem unfolds_rel (rd : Reader) : Unfolds rd (coreProgram.Rel rd) := fun f args rets h => by
  obtain ⟨fn, hf, σ, hp, hb⟩ := (rel_iff coreProgram f args rets).mp h
  exact ⟨fn, σ, hf, hp, hb⟩

/-- A call relation unfolding at a frame map unfolds. -/
theorem unfolds_of_V {rd : Reader} {C : CallRel} {V : FrameMap} (h : UnfoldsV rd C V) :
    Unfolds rd C := fun f args rets hc => by
  obtain ⟨fn, hf, hp, hb⟩ := h f args rets hc
  exact ⟨fn, V f args rets, hf, hp, hb⟩

variable {rd : Reader} {C : CallRel}

/-- `loop_sound` under `C`. -/
theorem loop_soundC {f : String} {ps : List E} {N : E} {m : ℕ} {B : E → Prop}
    (hm : m < ordG) (hN : N = gen ^ m)
    (hstep : ∀ x, C f (x :: ps) [] → B x ∧ (x * gen + N ≠ 0 → C f (x * gen :: ps) []))
    (h : 1 + N ≠ 0 → C f (1 :: ps) []) : ∀ j < m, B (gen ^ j) := by
  have key : ∀ t k, k + t = m → C f (gen ^ k :: ps) [] → ∀ j, k ≤ j → j < m → B (gen ^ j) := by
    intro t
    induction t with
    | zero => intro k hk _ j h1 h2; omega
    | succ t ih =>
      intro k hk hrun j h1 h2
      obtain ⟨hB, hnext⟩ := hstep _ hrun
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hB
      · have hne : gen ^ k * gen + N ≠ 0 := by
          intro he
          rw [gen_pow_add_eq_zero_iff, hN] at he
          have := gen_pow_inj hm (by unfold ordG at hm; omega) he
          omega
        have := hnext hne
        rw [gen_pow_mul_gen] at this
        exact ih (k + 1) (by omega) this j hlt h2
  intro j hj
  have h1 := h (by rw [hN]; exact one_add_gen_pow_ne_zero (by omega) hm)
  rw [← pow_zero gen] at h1
  exact key m 0 (by omega) h1 j (Nat.zero_le j) hj

/-- `guard_sound` under `C`. -/
theorem guard_soundC {σ : Val} {P : List Stmt} {gc : V} {f : String} {one N : V}
    {rest : List V} (h : guardOk P gc f one N rest = true)
    (hall : ∀ s ∈ P, Stmt.Holds C rd σ s True (fun rs => rs = [])) :
    1 + σ N ≠ 0 → C f (1 :: σ N :: rest.map σ) [] := by
  simp only [guardOk, Bool.and_eq_true] at h
  obtain ⟨⟨hc, ha⟩, h1⟩ := h
  have hat := atoms_of_flat hall
  have hcall := callIf_of_flat hall hc
  split at ha
  · rename_i p q hpq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨hp1, rfl⟩ := ha
    intro hne
    have hgc : σ gc = 1 + σ q := by rw [addOf_sound hpq hat, const_sound hp1 hat, word_one]
    have := hcall.2 (by rw [hgc]; exact hne)
    rwa [List.map_cons, List.map_cons, const_sound h1 hat, word_one] at this
  · exact absurd ha (by simp)

/-- **A loop helper's body at a valuation**: its counter and other parameters, its block, and,
while `x·g ≠ N`, the call at `x·g`. -/
theorem loop_of_body {f : String} {fn : Fn} (hok : loopShapeF fn f = true) {x : E} {ps : List E}
    {σ : Val} (hp : fn.params.map σ = x :: ps)
    (hb : Stmt.HoldsList C rd σ fn.body False (fun rs => rs = [])) :
    σ (V.n 0) = x ∧ fn.params.tail.map σ = ps ∧
      (∀ s ∈ loopPre fn, Stmt.Holds C rd σ s True (fun rs => rs = [])) ∧
      (x * gen + ps.headD 0 ≠ 0 → C f (x * gen :: ps) []) := by
  simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨h2, hpar⟩, hok⟩ := hok
  unfold loopPre
  split at hok
  · rename_i pre c g args hsl
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hgf, hlen⟩, htail⟩, hg⟩, hc⟩ := hok
    obtain ⟨hbody, hflat⟩ := splitLoopF_eq hsl
    rw [hbody] at hb
    obtain ⟨hall, -, hcall⟩ := holds_loopBodyF hflat hb
    have hat := atoms_of_flat hall
    have hx0 : σ (V.n 0) = x := by
      have := congrArg List.head? hp
      rw [hpar] at this
      obtain ⟨k, hk⟩ : ∃ k, fn.params.length = k + 2 := ⟨fn.params.length - 2, by omega⟩
      rw [hk, List.range_succ_eq_map] at this
      simpa using this
    have hps : fn.params.tail.map σ = ps := by
      have := congrArg List.tail hp
      rwa [← List.map_tail] at this
    have hN : ps.headD 0 = σ (V.n 1) := by
      rw [← hps, hpar]
      obtain ⟨k, hk⟩ : ∃ k, fn.params.length = k + 2 := ⟨fn.params.length - 2, by omega⟩
      rw [hk, List.range_succ_eq_map, List.range_succ_eq_map]
      simp
    refine ⟨hx0, hps, by simpa [hsl] using hall, fun hne => ?_⟩
    split at hc
    · rename_i p q hpq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hp', rfl⟩ := hc
      have hcv : σ c = x * gen + ps.headD 0 := by
        rw [addOf_sound hpq hat, genMul_sound hp' hat, hx0, hN]
      have := hcall (by rw [hcv]; exact hne)
      have hargs : args.map σ = x * gen :: ps := by
        obtain ⟨a0, rest, rfl⟩ : ∃ a0 rest, args = a0 :: rest := by
          cases args with
          | nil => simp at hlen; omega
          | cons a0 rest => exact ⟨a0, rest, rfl⟩
        simp only [List.headD_cons] at hg
        simp only [List.tail_cons] at htail
        rw [List.map_cons, genMul_sound hg hat, hx0, htail, hps]
      rwa [hargs, hgf] at this
    · exact absurd hc (by simp)
  · exact absurd hok (by simp)

/-- `loop_stepF` under a call relation that unfolds. -/
theorem loop_stepC (hC : Unfolds rd C) {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShapeF fn f = true) {x : E} {ps : List E} (h : C f (x :: ps) []) :
    ∃ σ : Val, σ (V.n 0) = x ∧ fn.params.tail.map σ = ps ∧
      (∀ s ∈ loopPre fn, Stmt.Holds C rd σ s True (fun rs => rs = [])) ∧
      (x * gen + ps.headD 0 ≠ 0 → C f (x * gen :: ps) []) := by
  obtain ⟨fn', σ, hf', hp, hb⟩ := hC _ _ _ h
  rw [hf] at hf'
  cases hf'
  exact ⟨σ, loop_of_body hok hp hb⟩

/-- **`loop_stepF` at the frame map's valuation** `Vm f (x :: ps) []`. -/
theorem loop_stepV {Vm : FrameMap} (hVm : UnfoldsV rd C Vm) {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) (hok : loopShapeF fn f = true) {x : E} {ps : List E}
    (h : C f (x :: ps) []) :
    Vm f (x :: ps) [] (V.n 0) = x ∧ fn.params.tail.map (Vm f (x :: ps) []) = ps ∧
      (∀ s ∈ loopPre fn, Stmt.Holds C rd (Vm f (x :: ps) []) s True (fun rs => rs = [])) ∧
      (x * gen + ps.headD 0 ≠ 0 → C f (x * gen :: ps) []) := by
  obtain ⟨fn', hf', hp, hb⟩ := hVm _ _ _ h
  rw [hf] at hf'
  cases hf'
  exact loop_of_body hok hp hb

/-- **The body of a called function at the frame map's valuation.** -/
theorem body_ofV {Vm : FrameMap} (hVm : UnfoldsV rd C Vm) {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {args rets : List E} (h : C f args rets) :
    fn.params.map (Vm f args rets) = args ∧
      Stmt.HoldsList C rd (Vm f args rets) fn.body False (fun rs => rs = rets) := by
  obtain ⟨fn', hf', hp, hb⟩ := hVm _ _ _ h
  rw [hf] at hf'
  cases hf'
  exact ⟨hp, hb⟩

/-! ## The callees' contracts -/

theorem find_loop2 : coreProgram.find? "__loop2" = some Data.core36 :=
  Program.find?_of_indexOf? (j := 36) l3_idx rfl

/-- **`__loop2`'s run gives `Loop2Out`**, from the segment's statement: its body is the prelude,
the segment, the epilogue; the prelude's atoms hold first, the segment hands the epilogue on. -/
theorem loop2Out_of_body {sigOf : Val → LeanXmss.Signature} (hx : Sig.verify_lean_xmss_sound_Spec sigOf)
    {σ : Val} {args : List E} (hp : Data.core36.params.map σ = args)
    (hb : Stmt.HoldsList C rd σ Data.core36.body False (fun rs => rs = [])) :
    Loop2Out C rd args (sigOf σ) := by
  have hpre : Stmt.noRetList Sig.l2Pre = true := by
    unfold Sig.l2Pre; decide +kernel
  rw [Sig.loop2_split, holdsList_append] at hb
  rw [holdsList_noRet _ hpre] at hb
  obtain ⟨h1, h2⟩ := hx C rd σ Sig.l2Post False _ hb.2
  refine ⟨σ, hp, ?_, h2⟩
  rw [holdsList_append, holdsList_noRet _ hpre]
  exact ⟨hb.1, h1⟩

/-- **The callees' contracts with witness functions**, on the calls of `C`. -/
structure CalleesWC (bytecode : List K) (C : CallRel) (rd : Reader) (bb0 : E)
    (wX : List E → LeanXmss.Signature) (wS : E → Sphincs.Signature) (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → Proof) (wA : List E → BatchingHints) : Prop where
  /-- A raw leanXMSS iteration (`__loop2`, the leanXMSS check inline): its body around the
  segment, and the signature `wX args` verifying the claim at its signer (`Loop2Out`). -/
  xmss : ∀ args, C "__loop2" args [] → Loop2Out C rd args (wX args)
  /-- A leanSPHINCS check with the byte table `bb0` (`main`'s): the signature `wS p` verifies the
  claim at `p`. -/
  sphincs : ∀ p, C "verify_sig_lean_sphincs" [p, bb0] [] →
    Sig.ByteBits rd bb0 → Sig.SphincsOut rd p (wS p)
  /-- The DA check with the exponent table: the matrix `wD args rets` opens the returned claim,
  the root's cells and the challenge (`Da.MeaningDaVerify`). -/
  da : ∀ gsq rets, C "da_verify" [gsq] rets → Da.SquaresAt rd gsq →
    ∃ (root : Digest) (z : E), (wD [gsq] rets).Opens root z ∧ rets = digestCells root ++ [z]
  /-- A child proof's check with the exponent table: the proof `wV args`. -/
  sub : ∀ pi0 pi1 s0 s1 gsq out,
    C "verify_sub" [pi0, pi1, s0, s1, gsq, out] [] → ExpTables rd gsq ∧ ExpWinTab rd gsq →
    VerifySubOut bytecode rd [pi0, pi1, s0, s1, gsq, out] (wV [pi0, pi1, s0, s1, gsq, out])
  /-- The batching, for `n_children_g = g^m`, `1 ≤ m ≤ 16`, with the window tables at `tabs`,
  with the hints `wA args`. -/
  agg : ∀ ncg cpi cfresh ccarried dst tabs, C "aggregate_claims"
    [ncg, cpi, cfresh, ccarried, dst, tabs] [] → WinTabs rd tabs → ∀ m, 1 ≤ m → m ≤ 16 →
      ncg = gen ^ m →
      ∃ out : DeferredClaim, out.bytecodePoint.length = bytecodeVars ∧ ReadsAt rd dst out.cells ∧
        ∀ cs : List ChildClaims, cs.length = m →
          (∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) →
          batch cs (wA [ncg, cpi, cfresh, ccarried, dst, tabs]) = some out

/-! ## The iterations -/

/-- **A raw leanXMSS signature** at the counter `x` of `__loop2` on `x :: ps`: a slot `s` below
the region's bound holding the mark `x`, and, when the tags `ps[4 ..]` hold the chain indices,
the signature `sig` verifies the claim at slot `s`. -/
def RawXStepC (rd : Reader) (lxs cover lxt : E) (ps : List E) (x : E) (sig : LeanXmss.Signature) :
    Prop :=
  ∃ s, BelowLog lxs s ∧ LoadHolds rd cover s x ∧
    (Sig.LxTagsHold (fun j => ps.getD (4 + j) 0) → Sig.XmssOut rd (lxt * gen ^ (4 * s)) sig)

theorem l2Fn_params : l2Fn.params = (List.range 56).map V.n := by
  have hs := l3_ok
  simp only [l3Ok, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨hsh, hlen⟩, -⟩, -⟩, -⟩, -⟩ := hs
  simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hsh
  rw [hsh.1.2, hlen]

theorem l2_param_getD (σ : Val) {k : ℕ} (hk : k < 55) :
    (((List.range 56).map V.n).tail.map σ).getD k 0 = σ (.n (k + 1)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_tail, List.getElem?_map,
    List.getElem?_range (by omega)]
  rfl

/-- **A run of `__loop2` read as its meaning gives the raw leanXMSS signature's facts.** -/
theorem rawX_of_out {rd : Reader} {C : CallRel} (hm : MemOk rd) {x : E} {ps : List E}
    {sig : LeanXmss.Signature} (hout : Loop2Out C rd (x :: ps) sig) :
    ∀ N lxs cover lxt tags, ps = N :: lxs :: cover :: lxt :: tags →
      RawXStepC rd lxs cover lxt ps x sig := by
  have hok := l3_ok
  simp only [l3Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hshape, -⟩, hrc⟩, hm11⟩, hl⟩, hm14⟩ := hok
  obtain ⟨σ, hp, hb, hout⟩ := hout
  obtain ⟨hx, hps, hall, -⟩ := loop_of_body (fn := l2Fn) hshape hp hb
  intro N lxs cover lxt tags hN
  have hat := atoms_of_flat hall
  have hps' := hps
  rw [l2Fn_params, hN] at hps'
  simp only [List.range_succ_eq_map, List.map_cons, List.map_map, List.tail_cons,
    List.cons.injEq] at hps'
  obtain ⟨-, hlxs, hcover, hlxt, -⟩ := hps'
  obtain ⟨s, hs, hbl⟩ := rcBound_sound hm hrc hat
  refine ⟨s, by rwa [← hlxs], ?_, fun ht => ?_⟩
  · have := load_sound hl hat
    rw [isMul_sound hm11 hat, hs, hcover, hx] at this
    simpa using (loadHolds_mul_gen_pow rd _ s 0 _).mp this
  · have h65 : σ (.n 65) = lxt * gen ^ (4 * s) := by
      rw [monoIs_sound hm14 hat, hs, hlxt, ← pow_mul, mul_comm s 4]
    rw [← h65]
    refine hout fun i hi hc => ?_
    obtain ⟨h1, h2⟩ := Sig.lxTagSlot_spec i hi hc
    have e := ht i hi hc
    rw [← hps, l2Fn_params] at e
    show σ (.n (5 + (Sig.lxTagSlot i - 1))) = _
    rw [← e]
    show _ = (((List.range 56).map V.n).tail.map σ).getD (4 + (Sig.lxTagSlot i - 1)) 0
    rw [l2_param_getD σ (by omega), show 4 + (Sig.lxTagSlot i - 1) + 1 = 5 + (Sig.lxTagSlot i - 1) by omega]

/-- `__loop2`'s iteration at `x`: its run and, while `x·g ≠ N`, the run at `x·g`. -/
theorem l3_stepC {rd : Reader} {C : CallRel}
    (hX : ∀ args, C "__loop2" args [] → ∃ sig, Loop2Out C rd args sig) {x : E} {ps : List E}
    (h : C "__loop2" (x :: ps) []) :
    C "__loop2" (x :: ps) [] ∧ (x * gen + ps.headD 0 ≠ 0 → C "__loop2" (x * gen :: ps) []) := by
  have hok := l3_ok
  simp only [l3Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨σ, hp, hb, -⟩ := (hX _ h).choose_spec
  exact ⟨h, (loop_of_body (fn := l2Fn) hok.1.1.1.1.1 hp hb).2.2.2⟩


/-- **A raw leanSPHINCS signature** at the counter `x`: a slot `s` below the region's bound
holding the mark `n_raw_x · x` (at `cover · lx_slots · g^s`), and the signature check of the
claim at slot `s`. -/
def RawSStepC (C : CallRel) (rd : Reader) (lss cover lxs nrx lst bb x : E) : Prop :=
  ∃ s, BelowLog lss s ∧ LoadHolds rd (cover * (lxs * gen ^ s)) 0 (nrx * x) ∧
    C "verify_sig_lean_sphincs" [lst * gen ^ (4 * s), bb] []

/-- `__loop3`'s iteration on `[N, lss, sp_cover, nrx, lst, bb]`, its region
`sp_cover = cover · lx_slots`. -/
theorem l4_stepC {rd : Reader} {C : CallRel} (hC : Unfolds rd C) (hm : MemOk rd) {x : E} {ps : List E}
    (h : C "__loop3" (x :: ps) []) :
    (∀ N lss cover lxs nrx lst bb, ps = [N, lss, cover * lxs, nrx, lst, bb] →
      RawSStepC C rd lss cover lxs nrx lst bb x) ∧
      (x * gen + ps.headD 0 ≠ 0 → C "__loop3" (x * gen :: ps) []) := by
  have hf := find_of_idx l4_idx (by rw [coreProgram_length]; omega)
  have hok := l4_ok
  simp only [l4Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hrc⟩, hm13⟩, hm14⟩, hl⟩, hm17⟩, hcall⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepC hC hf hshape h
  refine ⟨fun N lss cover lxs nrx lst bb hN => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 37 default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6] := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, hlss, hspc, hnrx, hlst, hbb⟩ := hps
  obtain ⟨s, hs, hbl⟩ := rcBound_sound hm hrc hat
  refine ⟨s, by rwa [← hlss], ?_, ?_⟩
  · have := load_sound hl hat
    rw [isMul_sound hm14 hat, isMul_sound hm13 hat, hs, hspc, hnrx, hx, mul_assoc] at this
    exact this
  · have := call_of_flat hall hcall
    rwa [List.map_cons, List.map_cons, List.map_nil, monoIs_sound hm17 hat, hs, hlst, hbb,
      ← pow_mul, mul_comm s 4] at this

/-- **Child `x`'s facts**: its base `written[x]`, its counts `g^ex`, `g^es`, its two rebuilt claim
lists' digests (the leanXMSS list in the region `cover` below `lxs`, the leanSPHINCS list in the
region `spc` below `lss`), its DA digest's cells at `da_digests · x^2`, its statement's digest at
`child_pi · x^2`, its proof's check (in `C`), and `written[x · g] = base · g^(ex + es)`. -/
def KidStepC (C : CallRel) (rd : Reader) (written lxt cover lxs lst spc lss carried dadig s0 s1
    cpi gsq cfresh x : E) : Prop :=
  ∃ (base cx0 cx1 cs0 cs1 d0 d1 p0 p1 : E) (ex es : ℕ),
    LoadHolds rd (written * x) 0 base ∧ ex < 2 ^ 32 ∧ es < 2 ^ 32 ∧
    coreProgram.Rel rd "child_claim_list_digest" [lxt, cover, base, lxs, gen ^ ex] [cx0, cx1] ∧
    coreProgram.Rel rd "child_claim_list_digest" [lst, spc, base * gen ^ ex, lss, gen ^ es]
      [cs0, cs1] ∧
    LoadHolds rd (dadig * x ^ 2) 0 d0 ∧ LoadHolds rd (dadig * x ^ 2) 1 d1 ∧
    coreProgram.Rel rd "statement_digest" [s0, s1, cx0, cx1, cs0, cs1, d0, d1, carried * x ^ 24]
      [p0, p1] ∧
    LoadHolds rd (cpi * x ^ 2) 0 p0 ∧ LoadHolds rd (cpi * x ^ 2) 1 p1 ∧
    C "verify_sub" [p0, p1, s0, s1, gsq, cfresh * x ^ 24] [] ∧
    LoadHolds rd (written * x) 1 (base * (gen ^ ex * gen ^ es))

theorem l5_stepC {rd : Reader} {C : CallRel} (hC : Unfolds rd C)
    (hle : CallRel.Le C (coreProgram.Rel rd)) (hm : MemOk rd) {x : E} {ps : List E}
    (h : C "__loop4" (x :: ps) []) :
    (∀ N written lxt cover lxs lst spc lss carried dadig s0 s1 cpi gsq cfresh,
      ps = [N, written, lxt, cover, lxs, lst, spc, lss, carried, dadig, s0, s1, cpi, gsq,
        cfresh] →
      KidStepC C rd written lxt cover lxs lst spc lss carried dadig s0 s1 cpi gsq cfresh x) ∧
      (x * gen + ps.headD 0 ≠ 0 → C "__loop4" (x * gen :: ps) []) := by
  have hf := find_of_idx l5_idx (by rw [coreProgram_length]; omega)
  have hok := l5_ok
  simp only [l5Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen⟩, hm16⟩, hl17⟩, hg18⟩, hg19⟩, hm28⟩, hcx⟩,
    hm31⟩, hcs⟩, hm39⟩, hm41⟩, hl42⟩, hl43⟩, hsd⟩, hm47⟩, hl44⟩, hm48⟩, hl45⟩, hm54⟩, hvs⟩,
    hm55⟩, hm56⟩, hl55⟩ := hok
  obtain ⟨σ, hx, hps, hall, hnext⟩ := loop_stepC hC hf hshape h
  refine ⟨fun N written lxt cover lxs lst spc lss carried dadig s0 s1 cpi gsq cfresh hN
    => ?_, hnext⟩
  have hat := atoms_of_flat hall
  have hpar : (coreProgram.getD 38 default).params = (List.range 16).map V.n := by
    have hs := hshape
    simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen]
  rw [hpar, hN] at hps
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.tail_cons, List.cons.injEq, and_true] at hps
  obtain ⟨-, hwr, hlxt, hcov, hlxs, hlst, hspc, hlss, hcar, hdad, hs0, hs1, hcpi, hgsq,
    hcf⟩ := hps
  obtain ⟨ex, hex, hnx⟩ := load_gpow hm (touch_sound hg18 hat)
  obtain ⟨es, hes, hns⟩ := load_gpow hm (touch_sound hg19 hat)
  have h16 : σ (.n 16) = written * x := by rw [isMul_sound hm16 hat, hwr, hx]
  have h28 : σ (.n 22) = gen ^ ex * gen ^ es := by rw [isMul_sound hm28 hat, hnx, hns]
  refine ⟨σ (.n 17), σ (.n 23), σ (.n 24), σ (.n 26), σ (.n 27), σ (.n 36), σ (.n 37),
    σ (.n 38), σ (.n 39), ex, es, ?_, hex, hes, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := load_sound hl17 hat; rwa [h16] at this
  · have := hle _ _ _ (call_of_flat hall hcx)
    simpa [hlxt, hcov, hlxs, hnx] using this
  · have := hle _ _ _ (call_of_flat hall hcs)
    simpa [isMul_sound hm31 hat, hlst, hspc, hlss, hnx, hns] using this
  · have := load_sound hl42 hat; rwa [monoIs_sound hm41 hat, hdad, hx] at this
  · have := load_sound hl43 hat; rwa [monoIs_sound hm41 hat, hdad, hx] at this
  · have := hle _ _ _ (call_of_flat hall hsd)
    simpa [monoIs_sound hm39 hat, hs0, hs1, hcar, hx] using this
  · have := load_sound hl44 hat; rwa [monoIs_sound hm47 hat, hcpi, hx] at this
  · have := load_sound hl45 hat; rwa [monoIs_sound hm48 hat, hcpi, hx] at this
  · have := call_of_flat hall hvs
    simpa [monoIs_sound hm54 hat, hs0, hs1, hgsq, hcf, hx] using this
  · have := load_sound hl55 hat
    rwa [isMul_sound hm56 hat, isMul_sound hm55 hat, h28, hwr, hx] at this

end
end LeanVM.Guest.B1.Main
