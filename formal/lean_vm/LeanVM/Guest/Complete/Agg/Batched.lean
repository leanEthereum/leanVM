module

public import LeanVM.Guest.Complete.Agg.Rows
public import LeanVM.Guest.B1.Main.Aggregate
public import LeanVM.Guest.Complete.MainB1
public import LeanVM.Guest.Bytecode
public import LeanVM.Protocol.Relation.Link.Valid

/-!
# `aggregate_claims`' honest sponges and the batching it checks

* `absSt_zero`, `absSt_succ`, `absSt_pend`, `absSt_last` (restored from the archive's `AggCMath`):
  the absorbing rows' sponges step by step, each child's words as `aggregate_claims_loop0` reads
  them (`l25Words`), four scalars waiting on every row, the last row's sponge the batching's.
  They discharge `A0Pre`'s sponge hypotheses (`agg_loop0_completes`'s `hst`).
* `batched_of_run`: the converse of `runBatching_of_carried`. A batching the program accepts
  (`DeferredClaimBatched`'s run) passes the proof of work, has `deferredVariableCount bytecode`
  rounds, its final claim is the hinted value times the batched weight (the guest's one
  `assert`), and its outcome is the sumcheck's challenges with the hinted value.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main LeanVM.Node

@[expose] public section

variable {rd : Reader}

/-! ## The absorbing rows -/

theorem absSt_zero (m : ℕ) (cs : List ChildClaims) :
    absSt m cs 0 = ⟨capOf batchSeed, [gen ^ m, 0, 0, 0].map (·, dsObserve)⟩ := by
  rw [absSt, List.take_zero, List.flatMap_nil, List.append_nil, absorb_head]

theorem absSt_succ {cpi cfresh ccarried : E} {m c : ℕ} {cs : List ChildClaims}
    (hc : c < cs.length) (hcw : ChildWordsAt rd cpi cfresh ccarried c cs[c]) :
    absSt m cs (c + 1) =
      (absSt m cs c).absorbAll (l25Words rd cpi cfresh ccarried (gen ^ c)) dsObserve := by
  obtain ⟨-, -, -, -, hw⟩ := kid_words hcw
  rw [absSt, absSt, List.take_succ_eq_append_getElem hc, List.flatMap_append,
    List.flatMap_singleton, ← List.append_assoc, absorbAll_append, ← hw]

theorem absSt_pend {cpi cfresh ccarried : E} {m : ℕ} {cs : List ChildClaims}
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) :
    ∀ c ≤ cs.length, (absSt m cs c).pend.length = 4
  | 0, _ => by rw [absSt_zero]; rfl
  | c + 1, hc => by
    have ih := absSt_pend (m := m) hcw c (by omega)
    rw [absSt_succ (by omega) (hcw c (by omega)), pend_absorbAll _ _ _ (by omega) (by omega), ih]
    simp [l25Words]

theorem absSt_last {m : ℕ} {cs : List ChildClaims} (hcl : cs.length = m) :
    absSt m cs m = aggAbs cs := by
  rw [absSt, List.take_of_length_le (by omega), aggAbs, Batch.cellsBeforeChallenge, hcl]

/-- **The absorbing rows' sponges, as `A0Pre` takes them**: each a state's capacity with four
scalars waiting, the next row's the child's words absorbed. -/
theorem absSt_rows {cpi cfresh ccarried : E} {m : ℕ} {cs : List ChildClaims} (hcl : cs.length = m)
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) :
    ∀ c < m, (StOk (absSt m cs c) ∧ (absSt m cs c).pend.length = 4) ∧
      absSt m cs (c + 1) = (absSt m cs c).absorbAll (l25Words rd cpi cfresh ccarried (gen ^ c)) dsObserve :=
  fun c hc => ⟨⟨absSt_ok m cs c, absSt_pend hcw c (by omega)⟩, absSt_succ (by omega) (hcw c (by omega))⟩

/-! ## Runs through a step -/

theorem run_bind_of {α : Type} {p : VerifierProgram α} {s s1 : Fs} {xs : List E} {a : α}
    (h : RunsTo p s xs a s1) {sp : Sponge} (hs : s.Carries sp) (rest : List E)
    (os : List (List Opening)) (roots : List (Digest × ℕ × ℕ)) :
    ∃ sp1 : Sponge, s1.Carries sp1 ∧ ∀ {β : Type} (f : α → VerifierProgram β),
      runId (p >>= f) ⟨sp, xs ++ rest, os, roots⟩ = runId (f a) ⟨sp1, rest, os, roots⟩ := by
  obtain ⟨sp1, hs1, e1⟩ := h sp hs rest os roots
  exact ⟨sp1, hs1, fun f => by rw [prog_bind_eq, run_bind, e1]; rfl⟩

theorem run_bindG_of {α : Type} {p : VerifierProgram α} {cap : List E} {c : E} {s1 : Fs} {xs : List E}
    {a : α} (h : RunsFromG p cap c xs a s1) {sp : Sponge} (hs : Fs.CarriesGround cap c sp) (rest : List E)
    (os : List (List Opening)) (roots : List (Digest × ℕ × ℕ)) :
    ∃ sp1 : Sponge, s1.Carries sp1 ∧ ∀ {β : Type} (f : α → VerifierProgram β),
      runId (p >>= f) ⟨sp, xs ++ rest, os, roots⟩ = runId (f a) ⟨sp1, rest, os, roots⟩ := by
  obtain ⟨sp1, hs1, e1⟩ := h sp hs rest os roots
  exact ⟨sp1, hs1, fun f => by rw [prog_bind_eq, run_bind, e1]; rfl⟩

theorem run_none_bind {α β : Type} {p : VerifierProgram α} {st : VerifierProgramState}
    (h : runId p st = none) (f : α → VerifierProgram β) : runId (p >>= f) st = none := by
  rw [prog_bind_eq, run_bind, h]; rfl

theorem run_require_bind {β : Type} {c : Prop} {_ : Decidable c} (f : Unit → VerifierProgram β)
    (st : VerifierProgramState) :
    runId (VerifierProgram.require c >>= f) st = if c then runId (f ()) st else none := by
  unfold VerifierProgram.require
  split <;> rw [prog_bind_eq, run_bind] <;> rfl

/-- A proof of work of `bits ≠ 0` from a carried sponge: its continuation on the nonce's
permutation, ground, when the work passes; nothing otherwise. -/
theorem run_grind_bind {β : Type} {bits : ℕ} (hb : bits ≠ 0) (f : Unit → VerifierProgram β) {s : Fs}
    {sp : Sponge} (hs : s.Carries sp) (n : E) (rest : List E) (os : List (List Opening))
    (roots : List (Digest × ℕ × ℕ)) :
    runId (VerifierProgram.grindProofOfWork bits >>= f) ⟨sp, n :: rest, os, roots⟩ =
      if powOk bits (Keccak.lane (s.nonceState n) 2) = true then
        runId (f ()) ⟨⟨s.nonceState n, [], some (challengeOf (s.nonceState n))⟩, rest, os, roots⟩
      else none := by
  rw [VerifierProgram.grindProofOfWork, ite_neg' hb, prog_bind_eq, run_bind,
    run_grind_carried bits _ hs n rest os roots]
  split <;> rfl

/-! ## The rounds on a short stream -/

theorem run_pure_eq {α : Type} (a : α) (st : VerifierProgramState) :
    runId (pure a : VerifierProgram α) st = some (a, st) := rfl

theorem run_read_nil {β : Type} (f : E → VerifierProgram β) (sp : Sponge) (os : List (List Opening))
    (roots : List (Digest × ℕ × ℕ)) :
    runId (VerifierProgram.readScalar >>= f) ⟨sp, [], os, roots⟩ = none := by
  rw [prog_bind_eq, run_bind]; rfl

/-- **The sumcheck's rounds reject a stream of fewer rounds**, one word after them. -/
theorem rounds_short : ∀ (rounds : List (E × E)) (claim : E) (s : Fs) (sp : Sponge), s.Carries sp →
    ∀ (n : ℕ), rounds.length < n → ∀ (x : E) (os : List (List Opening)) (roots : List (Digest × ℕ × ℕ)),
      runId (Batch.sumcheckRoundsProgram claim n)
        ⟨sp, rounds.flatMap (fun g ↦ [g.1, g.2]) ++ [x], os, roots⟩ = none
  | [], claim, s, sp, hs, n, hn, x, os, roots => by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [Batch.sumcheckRoundsProgram_succ]
    obtain ⟨sp1, -, e1⟩ := run_bind_of (runsTo_readE s x) hs [] os roots
    rw [List.append_nil] at e1
    simp only [List.flatMap_nil, List.nil_append]
    rw [e1]
    exact run_read_nil _ sp1 os roots
  | (g1, gInf) :: rest, claim, s, sp, hs, n, hn, x, os, roots => by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [Batch.sumcheckRoundsProgram_succ]
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    obtain ⟨sp1, hs1, e1⟩ := run_bind_of (runsTo_readE s g1) hs
      (gInf :: (rest.flatMap (fun g ↦ [g.1, g.2]) ++ [x])) os roots
    rw [List.singleton_append] at e1
    rw [e1]
    obtain ⟨sp2, hs2, e2⟩ := run_bind_of (runsTo_readE (s.absorb g1 dsObserve) gInf) hs1
      (rest.flatMap (fun g ↦ [g.1, g.2]) ++ [x]) os roots
    rw [List.singleton_append] at e2
    rw [e2]
    obtain ⟨sp3, hs3, e3⟩ := run_bind_of (runsTo_sampleE ((s.absorb g1 dsObserve).absorb gInf dsObserve))
      hs2 (rest.flatMap (fun g ↦ [g.1, g.2]) ++ [x]) os roots
    rw [List.nil_append] at e3
    rw [e3]
    exact run_none_bind (rounds_short rest _ _ sp3 hs3 j (by simp at hn; omega) x os roots) _

/-! ## The batching, converse -/

/-- A run's verdict accepts only a run returning `true` with its stream consumed. -/
theorem verdict_of {r : Option (Bool × VerifierProgramState)}
    (hr : (match r with
      | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
      | _ => false) = true) : ∃ s, r = some (true, s) ∧ s.stream = [] := by
  rcases r with _ | ⟨_ | _, s⟩
  · exact absurd hr (by simp)
  · exact absurd hr (by simp)
  · simp only [Bool.and_eq_true, List.isEmpty_iff] at hr
    exact ⟨s, rfl, hr.1⟩

/-- **An accepted batching passes the guest's checks** (the converse of `runBatching_of_carried`):
the nonce's proof of work, `deferredVariableCount bytecode` rounds, the final claim the hinted
value times the batched weight, the outcome the sumcheck's challenges with the hinted value. -/
theorem batched_of_run {cs : List ChildClaims} {h : BatchingHints} {bytecode : List K}
    {d : DeferredBytecodeClaim}
    (hrun : Batch.runBatching (m := Id) keccakF1600 (Batch.nodeBatchingProgram (· = d) bytecode cs)
      ⟨Batch.batchingStream cs h, []⟩ = true) :
    powOk Batch.batchLambdaGrindBits (Keccak.lane (aggN cs h.lambdaGrindNonce) 2) = true ∧
      h.sumcheckMessages.length = deferredVariableCount bytecode ∧
      (aggRun cs h).1.2 = h.finalBytecodeValue *
        Batch.batchedBytecodeWeight cs (aggLam cs h.lambdaGrindNonce)
          (aggCols cs h.lambdaGrindNonce).1 (aggRun cs h).1.1 ∧
      d = ⟨(aggRun cs h).1.1, h.finalBytecodeValue⟩ := by
  have hb : Batch.batchLambdaGrindBits ≠ 0 := by decide
  rw [Guest.Batch.runBatching_deployed] at hrun
  simp only [Batch.runBatchingWithHash, runProofWithHash] at hrun
  change (match runId (Batch.nodeBatchingProgram (· = d) bytecode cs)
      ⟨⟨keccakF1600 (seedInput (keccak256 batchingLabel) (Vector.replicate 4 0)), [], none⟩,
        Batch.batchingStream cs h, [], []⟩ with
    | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
    | _ => false) = true at hrun
  rw [show keccakF1600 (seedInput (keccak256 batchingLabel) (Vector.replicate 4 0)) = batchSeed
    from rfl] at hrun
  obtain ⟨sF, hF, hFs⟩ := verdict_of hrun
  clear hrun
  rw [batchingStream_eq] at hF
  -- the children's cells
  unfold Batch.nodeBatchingProgram at hF
  obtain ⟨sp1, hs1, e1⟩ := run_bind_of (runsTo_readN aggS0 (Batch.cellsBeforeChallenge cs)) carries_aggS0
    ([h.lambdaGrindNonce] ++ (h.sumcheckMessages.flatMap (fun g ↦ [g.1, g.2]) ++ [h.finalBytecodeValue]))
    [] []
  rw [e1] at hF
  simp only [] at hF
  rw [run_require_bind] at hF
  simp only [↓reduceIte] at hF
  unfold Batch.batchingAfterChildren at hF
  -- the proof of work
  rw [List.singleton_append, run_grind_bind hb _ hs1,
    show (aggS0.absorbAll (Batch.cellsBeforeChallenge cs) dsObserve).nonceState h.lambdaGrindNonce =
      aggN cs h.lambdaGrindNonce from rfl] at hF
  by_cases hpow : powOk Batch.batchLambdaGrindBits (Keccak.lane (aggN cs h.lambdaGrindNonce) 2) = true
  swap
  · rw [ite_neg' hpow] at hF
    exact absurd hF (by simp)
  rw [ite_pos' hpow] at hF
  refine ⟨hpow, ?_⟩
  -- `λ` and the column challenges
  set N := aggN cs h.lambdaGrindNonce with hN
  simp only [] at hF
  obtain ⟨sp2, hs2, e2⟩ := run_bindG_of (runsFromG_sample (capOf N) (challengeOf N))
    (sp := ⟨N, [], some (challengeOf N)⟩) ⟨rfl, rfl, rfl⟩
    (h.sumcheckMessages.flatMap (fun g ↦ [g.1, g.2]) ++ [h.finalBytecodeValue]) [] []
  rw [List.nil_append] at e2
  rw [e2] at hF
  obtain ⟨sp3, hs3, e3⟩ := run_bind_of (runsTo_sampleN splitLog (⟨capOf N, []⟩ : Fs)) hs2
    (h.sumcheckMessages.flatMap (fun g ↦ [g.1, g.2]) ++ [h.finalBytecodeValue]) [] []
  rw [List.nil_append] at e3
  rw [e3] at hF
  -- the rounds
  set claim := Batch.batchedClaim cs (Batch.lambdaPowers (challengeOf N) cs.length)
    ((⟨capOf N, []⟩ : Fs).squeezeN splitLog).1 with hclaim
  set s3 := ((⟨capOf N, []⟩ : Fs).squeezeN splitLog).2 with hs3d
  rcases lt_trichotomy h.sumcheckMessages.length (deferredVariableCount bytecode) with hlt | heq | hgt
  · exfalso
    rw [run_none_bind (rounds_short h.sumcheckMessages claim s3 sp3 hs3 _ hlt h.finalBytecodeValue [] [])
      _] at hF
    exact absurd hF (by simp)
  · refine ⟨heq, ?_⟩
    rw [← heq] at hF
    obtain ⟨sp4, hs4, e4⟩ := run_bind_of (runsTo_rounds h.sumcheckMessages claim s3) hs3
      [h.finalBytecodeValue] [] []
    rw [e4] at hF
    obtain ⟨sp5, -, e5⟩ := run_bind_of (runsTo_readE (bsRun h.sumcheckMessages claim s3).2
      h.finalBytecodeValue) hs4 [] [] []
    rw [List.append_nil] at e5
    rw [e5] at hF
    rw [run_require_bind] at hF
    split at hF
    · rename_i hc
      exact ⟨hc.1, hc.2.symm⟩
    · exact absurd hF (by simp)
  · exfalso
    have htk : (h.sumcheckMessages.take (deferredVariableCount bytecode)).length =
        deferredVariableCount bytecode := List.length_take_of_le hgt.le
    obtain ⟨g, rest, hdrop⟩ : ∃ g rest, h.sumcheckMessages.drop (deferredVariableCount bytecode) = g :: rest := by
      cases hd : h.sumcheckMessages.drop (deferredVariableCount bytecode) with
      | nil => simp at hd; omega
      | cons g rest => exact ⟨g, rest, rfl⟩
    have hsplit : h.sumcheckMessages.flatMap (fun g ↦ [g.1, g.2]) ++ [h.finalBytecodeValue] =
        (h.sumcheckMessages.take (deferredVariableCount bytecode)).flatMap (fun g ↦ [g.1, g.2]) ++
          (g.1 :: (g.2 :: (rest.flatMap (fun g ↦ [g.1, g.2]) ++ [h.finalBytecodeValue]))) := by
      conv_lhs => rw [← List.take_append_drop (deferredVariableCount bytecode) h.sumcheckMessages, hdrop]
      simp
    rw [hsplit] at hF
    have hr := runsTo_rounds (h.sumcheckMessages.take (deferredVariableCount bytecode)) claim s3
    rw [htk] at hr
    obtain ⟨sp4, hs4, e4⟩ := run_bind_of hr hs3
      (g.1 :: (g.2 :: (rest.flatMap (fun g ↦ [g.1, g.2]) ++ [h.finalBytecodeValue]))) [] []
    rw [e4] at hF
    obtain ⟨sp5, -, e5⟩ := run_bind_of (runsTo_readE _ g.1) hs4
      (g.2 :: (rest.flatMap (fun g ↦ [g.1, g.2]) ++ [h.finalBytecodeValue])) [] []
    rw [List.singleton_append] at e5
    rw [e5] at hF
    rw [run_require_bind] at hF
    split at hF
    · simp only [run_pure_eq, Option.some.injEq, Prod.mk.injEq, true_and] at hF
      rw [← hF] at hFs
      exact absurd hFs (by simp)
    · exact absurd hF (by simp)

/-- **The guest's deferred claims have `25` variables**: `19` of instructions, `6` of columns. -/
theorem guest_deferredVariableCount : deferredVariableCount guestBytecode = 25 := by
  rw [deferredVariableCount, instructionVariableCount, guestBytecode, LeanVM.Protocol.Relation.length_bytecodeWords, guest_logSize,
    show (16 * 2 ^ 19) >>> bytecodeSlotBits = 2 ^ 19 by norm_num [bytecodeSlotBits, Nat.shiftRight_eq_div_pow],
    Nat.log2_two_pow]
  rfl

end
end LeanVM.Guest.Complete.Agg
