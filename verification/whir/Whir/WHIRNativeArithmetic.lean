import Whir.AccumulatedTerminalRefinement
import Whir.OperationalRefinement
import Whir.WHIRNativeGuards

namespace Whir.WHIRNativeArithmetic
open Concrete Protocol AccumulatedTerminalRefinement
set_option maxHeartbeats 1600000

/-- Only the source claim, the two transmitted coefficients, remaining dimension,
and native saved contexts occur in executable arithmetic state. -/
structure State where
  n : Nat
  claim : E
  message : Message E
  source : SourceState
  deriving Repr

def foldScalar (s : State) (r : E) (next : Message E) : State :=
  ⟨s.n - 1, s.message.eval s.claim r, next, s.source.step (.fold r)⟩

def batchScalar (s : State) (basis : Basis) (value beta : E) (intro : Message E) : State :=
  ⟨s.n, s.claim + beta * value, s.message.glue intro beta, s.source.step (.glue basis beta)⟩

def foldStep (cs : LevelChallenges) (p : LevelProof) (j : Nat) (s : State) : State :=
  foldScalar s cs.folds[j]! p.afterFold[j]!

def foldBlock (cs : LevelChallenges) (p : LevelProof) (s : State) : State :=
  runSteps (foldStep cs p) cs.folds.size 0 s

def oodStep (cs : LevelChallenges) (p : LevelProof) (j : Nat) (s : State × E) : State × E :=
  let beta := s.2 * cs.lambda
  (batchScalar s.1 (.ood cs.oodPoints[j]!) p.oods[j]!.value beta p.oods[j]!.intro, beta)

def oodBatch (cs : LevelChallenges) (p : LevelProof) (s : State) : State × E :=
  runSteps (oodStep cs p) p.oods.size 0 (s, E.one)

def queryBatch (n i : Nat) (cs : LevelChallenges) (p : LevelProof)
    (qs : Array Nat) (s : State × E) : State :=
  batchScalar s.1 (.query n qs cs.lambda)
    (enforced p.rows cs.folds (powers cs.lambda qs.size) (i == 0))
    (s.2 * cs.lambda) p.intro

/-- Merkle roots are only presence markers here. Public root shapes and actual
opened-row authentication are handled by the physical driver, not by oracle
lookup or dense-weight construction in this executable checker. -/
def verifyLevel (c : Config) (ch : Challenges) (proof : Opening)
    (i : Nat) (s : State) : Except String State := do
  let cs := ch.levels[i]!
  let p := proof.levels[i]!
  if p.afterFold.size != cs.folds.size || p.oods.size != cs.oodPoints.size then
    throw "round/OOD length"
  let s := foldBlock cs p s
  if i + 1 < c.folds.size then
    if !p.nextOracle.isSome then throw "missing commitment"
  else
    if p.nextOracle.isSome || proof.residual.size != 2 ^ s.n then throw "final length"
  let qs ← (deriveQueries (s.n + c.rates[i]!) c.queries[i]! cs.querySqueezes).elim
    (throw "query challenges") pure
  if p.rows.size != qs.size then throw "query length"
  return queryBatch s.n i cs p qs (oodBatch cs p s)

def tailStep (ch : Challenges) (proof : Opening) (j : Nat) (s : State) : State :=
  let next := if j + 1 < ch.tail.size then proof.tailMessages[j]! else s.message
  { s with claim := s.message.eval s.claim ch.tail[j]!, message := next }

def closeTail (ch : Challenges) (proof : Opening) (s : State) : State :=
  runSteps (tailStep ch proof) ch.tail.size 0 s

def nativeVerify (c : Config) (ch : Challenges) (lanes : Nat) (initialClaim : E)
    (callerAt : Array E → E) (proof : Opening) : Except String Unit := do
  if !ch.valid c || lanes == 0 || lanes > 2 ^ c.folds[0]! then
    throw "configuration/challenges/weight"
  if proof.levels.size != c.folds.size || proof.tailMessages.size + 1 != ch.tail.size then
    throw "proof length"
  let s ← runChecked (verifyLevel c ch proof) c.folds.size 0
    ⟨c.logN, initialClaim, proof.initial, ⟨[], []⟩⟩
  let final := closeTail ch proof s
  let callerPoint := rotatePoint c.folds[0]! (s.source.ris ++ ch.tail.toList).toArray
  let terminal := sourceTerminal (callerAt callerPoint) s.source.saved s.source.ris ch.tail.toList proof.residual
  if !(final.claim == terminal) then throw "terminal mismatch"
  return ()

/-- Local semantic relation used below. It is proved from initialization and
preserved by scalar operations; it is not an input to nativeVerify. -/
structure WeightInvariant (callerAt : Array E → E) (initialK : Nat) (s : State) (w : Array E) : Prop where
  size : w.size = 2 ^ s.n
  contexts : ∀ ctx ∈ s.source.saved,
    ctx.risStart ≤ s.source.ris.length ∧
      ctx.basis.Shape (s.source.ris.length + s.n - ctx.risStart)
  eval : ∀ point : List E, point.length = s.n →
    Concrete.mle w point.toArray =
      callerAt (rotatePoint initialK (s.source.ris ++ point).toArray) +
        nativeSaved s.source.saved s.source.ris point

/-- A low fold extends the unrotated transcript, never a context-local rotation. -/
theorem WeightInvariant.fold (callerAt : Array E → E) (k : Nat) (s : State) (w : Array E)
    (h : WeightInvariant callerAt k s w) (hn : 0 < s.n) (r : E) (next : Message E) :
    WeightInvariant callerAt k (foldScalar s r next) (foldLow w r) := by
  constructor
  · simp only [ArrayLayout.size_foldLow, h.size, foldScalar]
    have he : s.n = (s.n - 1) + 1 := by omega
    rw [he, pow_succ, Nat.mul_div_left _ (by decide : 0 < 2)]
    simp
  · intro ctx hc
    obtain ⟨hstart, hshape⟩ := h.contexts ctx hc
    constructor
    · simpa [foldScalar, SourceState.step] using hstart.trans (Nat.le_add_right _ 1)
    · simpa only [foldScalar, SourceState.step, List.length_append, List.length_singleton,
        show s.source.ris.length + 1 + (s.n - 1) = s.source.ris.length + s.n by omega] using hshape
  · intro point hp
    have hp' : point.length = s.n - 1 := hp
    have he := h.eval (r :: point) (by simp; omega)
    rw [show (r :: point).toArray = #[r] ++ point.toArray by simp,
      TerminalRefinement.mle_cons _ _ _ (by rw [h.size]; congr 1; simp; omega)] at he
    simpa [foldScalar, SourceState.step, nativeSaved, List.append_assoc] using he

theorem WeightInvariant.batch (callerAt : Array E → E) (k : Nat) (s : State) (w : Array E)
    (h : WeightInvariant callerAt k s w) (basis : Basis) (hb : basis.Shape s.n)
    (value beta : E) (intro : Message E) :
    WeightInvariant callerAt k (batchScalar s basis value beta intro) (weightGlue w basis.dense beta) := by
  constructor
  · simpa [batchScalar] using h.size
  · intro ctx hc
    simp only [batchScalar, SourceState.step, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact h.contexts ctx hc
    · exact ⟨le_rfl, by simpa [batchScalar, SourceState.step] using hb⟩
  · intro point hp
    change point.length = s.n at hp
    rw [AccumulatedTerminalAlgebra.mle_weightGlue _ _ _ _
      (by simpa [batchScalar] using h.size.trans (congrArg (2 ^ ·) hp.symm))
      ((basis.size_dense _ hb).trans h.size.symm)]
    rw [h.eval point hp, ← basis.native_eq_mle point (by simpa [hp] using hb)]
    simp [batchScalar, SourceState.step, nativeSaved, List.map_append,
      List.sum_append, add_assoc]

theorem runSteps_related {A B : Type*} (f : Nat → A → A) (g : Nat → B → B)
    (P : A → B → Prop) (count start : Nat) (a : A) (b : B) (hab : P a b)
    (step : ∀ j x y, start ≤ j → j < start + count → P x y → P (f j x) (g j y)) :
    P (runSteps f count start a) (runSteps g count start b) := by
  induction count generalizing start a b with
  | zero => exact hab
  | succ count ih =>
    apply ih (start + 1) (f start a) (g start b)
    · exact step start a b (by omega) (by omega) hab
    · intro j x y hlo hhi hp
      exact step j x y (by omega) (by omega) hp

def ScalarSame (s : State) (d : VerifierState E) : Prop :=
  s.claim = d.claim ∧ s.message = d.message

theorem same_fold (s : State) (d : VerifierState E) (h : ScalarSame s d)
    (block : Nat) (r : E) (next : Message E) :
    ScalarSame (foldScalar s r next) (d.fold block r next) := by
  simp [ScalarSame, foldScalar, VerifierState.fold, h.1, h.2]

theorem same_batch (s : State) (d : VerifierState E) (h : ScalarSame s d)
    (basis : Basis) (value beta : E) (intro : Message E) :
    ScalarSame (batchScalar s basis value beta intro) (d.batch basis.dense value beta intro) := by
  simp only [ScalarSame, batchScalar, VerifierState.batch]
  exact ⟨by rw [h.1], by rw [h.2]⟩

theorem foldBlock_same (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (s : State) (d : CheckedState) (h : ScalarSame s d.state) :
    ScalarSame (foldBlock cs p s) (Protocol.foldBlock block cs p d).state := by
  exact runSteps_related (foldStep cs p) (Protocol.foldStep block cs p)
    (fun s d => ScalarSame s d.state) _ _ _ _ h
    (by intro j s d _ _ h; exact same_fold s d.state h block _ _)

theorem foldSteps_n (cs : LevelChallenges) (p : LevelProof) (count start : Nat) (s : State) :
    (runSteps (foldStep cs p) count start s).n = s.n - count := by
  induction count generalizing start s with
  | zero => simp [runSteps]
  | succ count ih => simp [runSteps, ih, foldStep, foldScalar, Nat.sub_sub, Nat.add_comm]

theorem foldSteps_source (cs : LevelChallenges) (p : LevelProof)
    (count start : Nat) (s : State) :
    (runSteps (foldStep cs p) count start s).source =
      ⟨s.source.ris ++ (List.range' start count).map (fun j => cs.folds[j]!), s.source.saved⟩ := by
  induction count generalizing start s with
  | zero => simp only [runSteps, List.range'_zero, List.map_nil, List.append_nil]
  | succ count ih =>
    simp [runSteps, ih, foldStep, foldScalar, SourceState.step, List.range'_succ, List.append_assoc]

theorem foldBlock_source (cs : LevelChallenges) (p : LevelProof) (s : State) :
    (foldBlock cs p s).source = ⟨s.source.ris ++ cs.folds.toList, s.source.saved⟩ := by
  have mapped : (List.range cs.folds.size).map (fun i => cs.folds[i]!) = cs.folds.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      simp only [getElem!_pos cs.folds i (by simpa using hi')]
  rw [foldBlock, foldSteps_source, ← List.range_eq_range', mapped]

theorem foldBlock_n (cs : LevelChallenges) (p : LevelProof) (s : State) :
    (foldBlock cs p s).n = s.n - cs.folds.size := foldSteps_n cs p _ _ s

theorem lowFoldSteps_invariant (callerAt : Array E → E) (k : Nat)
    (cs : LevelChallenges) (p : LevelProof) (count start : Nat) (s : State) (d : CheckedState)
    (h : WeightInvariant callerAt k s d.state.weight) (bound : count ≤ s.n) :
    WeightInvariant callerAt k (runSteps (foldStep cs p) count start s)
      (runSteps (Protocol.foldStep 1 cs p) count start d).state.weight := by
  induction count generalizing start s d with
  | zero => exact h
  | succ count ih =>
    apply ih (start + 1) (foldStep cs p start s) (Protocol.foldStep 1 cs p start d)
    · simpa only [foldStep, Protocol.foldStep, VerifierState.fold, foldValues, BEq.rfl, ↓reduceIte] using
        h.fold callerAt k s d.state.weight (by omega) cs.folds[start]! p.afterFold[start]!
    · change count ≤ s.n - 1
      omega

theorem oodBatch_related (callerAt : Array E → E) (k : Nat)
    (cs : LevelChallenges) (p : LevelProof) (s : State) (d : VerifierState E)
    (same : ScalarSame s d) (inv : WeightInvariant callerAt k s d.weight)
    (shape : ∀ j < p.oods.size, cs.oodPoints[j]!.size = s.n) :
    let ns := oodBatch cs p s
    let ds := Protocol.oodBatch cs p d
    ns.2 = ds.2 ∧ ns.1.n = s.n ∧ ScalarSame ns.1 ds.1 ∧
      WeightInvariant callerAt k ns.1 ds.1.weight := by
  apply runSteps_related (oodStep cs p) (Protocol.oodStep cs p)
    (fun ns ds => ns.2 = ds.2 ∧ ns.1.n = s.n ∧ ScalarSame ns.1 ds.1 ∧
      WeightInvariant callerAt k ns.1 ds.1.weight) _ _ _ _
  · exact ⟨rfl, rfl, same, inv⟩
  · intro j ns ds _ hj h
    obtain ⟨hbeta, hn, hsame, hinv⟩ := h
    have hb : (Basis.ood cs.oodPoints[j]!).Shape ns.1.n := by
      exact (shape j (by omega)).trans hn.symm
    refine ⟨by simp [oodStep, Protocol.oodStep, hbeta], hn, ?_, ?_⟩
    · simpa [oodStep, Protocol.oodStep, hbeta, Basis.dense] using
        same_batch ns.1 ds.1 hsame (.ood cs.oodPoints[j]!) p.oods[j]!.value
          (ds.2 * cs.lambda) p.oods[j]!.intro
    · simpa [oodStep, Protocol.oodStep, VerifierState.batch, hbeta, Basis.dense] using
        hinv.batch callerAt k ns.1 ds.1.weight (.ood cs.oodPoints[j]!) hb
          p.oods[j]!.value (ds.2 * cs.lambda) p.oods[j]!.intro

theorem initial_fold_invariant (callerAt : Array E → E) (cs : LevelChallenges)
    (p : LevelProof) (s : State) (b : Array E) (n k : Nat)
    (sn : s.n = n + k) (sk : cs.folds.size = k) (empty : s.source = ⟨[], []⟩)
    (hb : b.size = 2 ^ (n + k))
    (caller : ∀ point : Array E, point.size = n + k → callerAt point = Concrete.mle b point) :
    WeightInvariant callerAt k (foldBlock cs p s)
      (cs.folds.foldl (fun b r => foldLane b (2 ^ n) r) b) := by
  have hn : (foldBlock cs p s).n = n := by rw [foldBlock_n, sn, sk]; omega
  have hs : (foldBlock cs p s).source = ⟨cs.folds.toList, []⟩ := by
    rw [foldBlock_source, empty]; simp
  constructor
  · rw [QueryRefinement.foldLane_blocks _ _ _ (by rw [sk, hb, pow_add, Nat.mul_comm]), hn]
    simp
  · simp [hs]
  · intro point hp
    have hp' : point.length = n := hp.trans hn
    rw [hs]
    simp only [nativeSaved, List.map_nil, List.sum_nil, add_zero]
    have hrot : rotatePoint k (cs.folds.toList ++ point).toArray = point.toArray ++ cs.folds := by
      have ha : (cs.folds.toList ++ point).toArray = cs.folds ++ point.toArray := by
        apply Array.toList_inj.mp
        simp
      rw [ha, ← sk]
      exact InitialTerminalRefinement.rotate_initial _ _
    rw [caller _ (by simp [ArrayLayout.size_rotatePoint, sk, hp', Nat.add_comm]), hrot]
    have he := InitialTerminalRefinement.mle_foldLane_initial b cs.folds point.toArray
      (by simpa [hp', sk] using hb)
    simpa [hp'] using he

theorem WeightInvariant.terminal (callerAt : Array E → E) (k : Nat) (s : State) (w residual : Array E)
    (h : WeightInvariant callerAt k s w) (tail : List E) (ht : tail.length = s.n) :
    Concrete.mle residual tail.toArray * Concrete.mle w tail.toArray =
      sourceTerminal (callerAt (rotatePoint k (s.source.ris ++ tail).toArray))
        s.source.saved s.source.ris tail residual := by
  have hs : nativeSaved s.source.saved s.source.ris tail =
      (s.source.saved.map (fun ctx => ctx.beta *
        ctx.basis.native (ctx.sourcePoint s.source.ris tail))).sum := by
    unfold nativeSaved
    congr 1
    apply List.map_congr_left
    intro ctx hc
    obtain ⟨hstart, hshape⟩ := h.contexts ctx hc
    have hdim := ctx.basis.dimension_eq _ hshape
    have hlen : ctx.basis.dimension - tail.length = (s.source.ris.drop ctx.risStart).length := by
      simp only [List.length_drop]
      omega
    simp only [Saved.sourcePoint, hlen, List.take_length]
    rw [List.drop_append_of_le_length hstart]
  rw [h.eval tail ht, hs, source_terms]
  unfold sourceTerminal
  ring

theorem closeTail_same (ch : Challenges) (proof : Opening) (s : State) (d : VerifierState E)
    (same : ScalarSame s d) :
    ScalarSame (closeTail ch proof s) (Protocol.closeTail ch proof d) := by
  apply runSteps_related (tailStep ch proof) (Protocol.tailStep ch proof) ScalarSame _ _ _ _ same
  intro j s d _ _ h
  simp [ScalarSame, tailStep, Protocol.tailStep, VerifierState.fold, h.1, h.2]

theorem tailSteps_weight (ch : Challenges) (proof : Opening)
    (count start : Nat) (d : VerifierState E) :
    (runSteps (Protocol.tailStep ch proof) count start d).weight =
      (List.range' start count).foldl (fun b j => foldLow b ch.tail[j]!) d.weight := by
  induction count generalizing start d with
  | zero => rfl
  | succ count ih =>
    simp only [runSteps, List.range'_succ, List.foldl_cons, ih,
      Protocol.tailStep, VerifierState.fold, foldValues, BEq.rfl, ↓reduceIte]

theorem closeTail_weight (ch : Challenges) (proof : Opening) (d : VerifierState E) :
    (Protocol.closeTail ch proof d).weight = ch.tail.foldl foldLow d.weight := by
  have mapped : (List.range ch.tail.size).map (fun i => ch.tail[i]!) = ch.tail.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      simp only [getElem!_pos ch.tail i (by simpa using hi')]
  rw [Protocol.closeTail, tailSteps_weight, ← List.range_eq_range', ← List.foldl_map,
    mapped, Array.foldl_toList]

private theorem except_pure {S : Type*} (s : S) : (pure s : Except String S) = .ok s := rfl
private theorem except_bind_ok {S T : Type} (s : S) (f : S → Except String T) :
    ((Except.ok s : Except String S) >>= f) = f s := rfl
private theorem except_bind_error {S T : Type} (e : String) (f : S → Except String T) :
    ((Except.error e : Except String S) >>= f) = Except.error e := rfl
private theorem except_throw {S : Type*} (e : String) : (throw e : Except String S) = .error e := rfl
attribute [local simp] except_pure except_bind_ok except_bind_error except_throw

theorem verifyLevel_success (c : Config) (ch : Challenges) (proof : Opening)
    (i : Nat) (s finish : State) (success : verifyLevel c ch proof i s = .ok finish) :
    let cs := ch.levels[i]!
    let p := proof.levels[i]!
    let folded := foldBlock cs p s
    p.afterFold.size = cs.folds.size ∧ p.oods.size = cs.oodPoints.size ∧
      (if i + 1 < c.folds.size then p.nextOracle.isSome = true
       else p.nextOracle.isSome = false ∧ proof.residual.size = 2 ^ folded.n) ∧
      ∃ qs, deriveQueries (folded.n + c.rates[i]!) c.queries[i]! cs.querySqueezes = some qs ∧
        p.rows.size = qs.size ∧ finish = queryBatch folded.n i cs p qs (oodBatch cs p folded) := by
  dsimp
  unfold verifyLevel at success
  generalize hf : foldBlock ch.levels[i]! proof.levels[i]! s = folded at success ⊢
  cases hn : proof.levels[i]!.nextOracle <;>
    cases hq : deriveQueries (folded.n + c.rates[i]!) c.queries[i]! ch.levels[i]!.querySqueezes
  all_goals
    simp only [hn, Option.elim, Option.isSome, except_pure,
      except_bind_error, except_throw] at success
    split_ifs at success <;> simp_all
  all_goals (split_ifs at success; simp_all)

theorem protocolLevel_of_checks (c : Config) (ch : Challenges) (proof : Opening)
    (i : Nat) (d : CheckedState) (qs : Array Nat)
    (rounds : proof.levels[i]!.afterFold.size = ch.levels[i]!.folds.size)
    (oods : proof.levels[i]!.oods.size = ch.levels[i]!.oodPoints.size)
    (boundary :
      let f := Protocol.foldBlock (if i == 0 then 2^(c.logN-c.folds[0]!) else 1)
        ch.levels[i]! proof.levels[i]! d
      if i + 1 < c.folds.size then
        ∃ next, proof.levels[i]!.nextOracle = some next ∧
          oracleValid next (2^(f.n-c.folds[i+1]!+c.rates[i+1]!)) (2^c.folds[i+1]!) = true
      else proof.levels[i]!.nextOracle.isSome = false ∧ proof.residual.size = 2^f.n)
    (query :
      deriveQueries ((Protocol.foldBlock (if i == 0 then 2^(c.logN-c.folds[0]!) else 1)
        ch.levels[i]! proof.levels[i]! d).n + c.rates[i]!) c.queries[i]!
        ch.levels[i]!.querySqueezes = some qs)
    (rows : proof.levels[i]!.rows.size = qs.size)
    (auth : ∀ j < qs.size, proof.levels[i]!.rows[j]! =
      (Protocol.foldBlock (if i == 0 then 2^(c.logN-c.folds[0]!) else 1)
        ch.levels[i]! proof.levels[i]! d).oracle[qs[j]!]!) :
    let f := Protocol.foldBlock (if i == 0 then 2^(c.logN-c.folds[0]!) else 1)
      ch.levels[i]! proof.levels[i]! d
    Protocol.verifyLevel c ch proof i d =
      .ok ⟨f.n, Protocol.queryBatch f.n i ch.levels[i]! proof.levels[i]! qs
        (Protocol.oodBatch ch.levels[i]! proof.levels[i]! f.state),
        proof.levels[i]!.nextOracle.getD #[]⟩ := by
  have ha := (OperationalRefinement.authentication_ok_iff
    (Protocol.foldBlock (if i == 0 then 2^(c.logN-c.folds[0]!) else 1)
      ch.levels[i]! proof.levels[i]! d).oracle qs proof.levels[i]!).mpr
        (by intro j hj; simp [auth j hj])
  dsimp only at boundary ⊢
  by_cases more : i + 1 < c.folds.size
  · rw [ite_eq_left more] at boundary
    obtain ⟨next, hn, hv⟩ := boundary
    simp_all [Protocol.verifyLevel]
  · rw [ite_eq_right more] at boundary
    have hn : proof.levels[i]!.nextOracle = none := by
      cases h : proof.levels[i]!.nextOracle <;> simp_all
    simp_all [Protocol.verifyLevel]

theorem foldBlock_oracle (block : Nat) (cs : LevelChallenges) (p : LevelProof) (d : CheckedState) :
    (Protocol.foldBlock block cs p d).oracle = d.oracle := by
  have aux (count start : Nat) (d : CheckedState) :
      (runSteps (Protocol.foldStep block cs p) count start d).oracle = d.oracle := by
    induction count generalizing start d with
    | zero => rfl
    | succ count ih => exact ih (start + 1) (Protocol.foldStep block cs p start d)
  exact aux _ _ _

/-- Ghost oracle table used solely in the refinement theorem. No native runtime
definition reads this function or any full oracle. -/
def oracleBefore (proof : Opening) (root : Oracle) (i : Nat) : Oracle :=
  if i = 0 then root else proof.levels[i-1]!.nextOracle.getD #[]

def RootShapes (c : Config) (proof : Opening) : Prop :=
  ∀ i, i < c.folds.size → i + 1 < c.folds.size →
    ∀ next, proof.levels[i]!.nextOracle = some next →
      oracleValid next (2^(CausalGame.remaining c i-c.folds[i+1]!+c.rates[i+1]!))
        (2^c.folds[i+1]!) = true

def AuthenticatedRows (c : Config) (ch : Challenges) (proof : Opening) (root : Oracle) : Prop :=
  ∀ i, i < c.folds.size → ∀ qs,
    deriveQueries (CausalGame.remaining c i+c.rates[i]!) c.queries[i]!
      ch.levels[i]!.querySqueezes = some qs →
    ∀ j, j < qs.size → proof.levels[i]!.rows[j]! = (oracleBefore proof root i)[qs[j]!]!

structure ReplayInvariant (c : Config) (callerAt : Array E → E) (b : Array E)
    (proof : Opening) (root : Oracle) (i : Nat) (s : State) (d : CheckedState) : Prop where
  native_n : s.n = WHIRNativeGuards.before c i
  dense_n : d.n = WHIRNativeGuards.before c i
  scalar : ScalarSame s d.state
  oracle : d.oracle = oracleBefore proof root i
  first_weight : i = 0 → d.state.weight = b
  first_source : i = 0 → s.source = ⟨[], []⟩
  weight : 0 < i → WeightInvariant callerAt c.folds[0]! s d.state.weight

theorem verifyLevel_refines (c : Config) (ch : Challenges) (proof : Opening)
    (callerAt : Array E → E) (b : Array E) (root : Oracle)
    (hc : ch.valid c = true) (hb : b.size = 2^c.logN)
    (caller : ∀ point : Array E, point.size = c.logN → callerAt point = Concrete.mle b point)
    (roots : RootShapes c proof) (authenticated : AuthenticatedRows c ch proof root)
    (i : Nat) (hi : i < c.folds.size) (s finish : State) (d : CheckedState)
    (inv : ReplayInvariant c callerAt b proof root i s d)
    (success : verifyLevel c ch proof i s = .ok finish) :
    ∃ df, Protocol.verifyLevel c ch proof i d = .ok df ∧
      ReplayInvariant c callerAt b proof root (i+1) finish df := by
  let cs := ch.levels[i]!
  let p := proof.levels[i]!
  let block := if i == 0 then 2^(c.logN-c.folds[0]!) else 1
  let nf := foldBlock cs p s
  let df := Protocol.foldBlock block cs p d
  have hconfig := WHIRNativeGuards.challenges_config c ch hc
  have hfold := WHIRNativeGuards.challenges_folds c ch hc i hi
  have hdims := (WHIRNativeGuards.config_remaining c hconfig i hi).2
  have hlevel := WHIRNativeGuards.config_level c hconfig i hi
  have hn : nf.n = CausalGame.remaining c i := by
    rw [foldBlock_n, inv.native_n, hfold]
    exact WHIRNativeGuards.before_step c i hi
  have hdn : df.n = CausalGame.remaining c i := by
    exact OracleReplay.foldBlock_dimensions block cs p d _ _
      (inv.dense_n.trans hdims.symm) hfold
  have hscalar : ScalarSame nf df.state := foldBlock_same block cs p s d inv.scalar
  have hweight : WeightInvariant callerAt c.folds[0]! nf df.state.weight := by
    by_cases hz : i = 0
    · have hsum : CausalGame.remaining c i + c.folds[0]! = c.logN := by
        simpa [hz, WHIRNativeGuards.before] using hdims
      have hblock : block = 2^(CausalGame.remaining c i) := by
        simp only [block, show (i == 0) = true by simp [hz], ↓reduceIte]
        congr 1
        omega
      rw [show df.state.weight = cs.folds.foldl (fun b r => foldLane b block r) d.state.weight from
        AccumulatedTerminalRefinement.foldBlock_weight_lane block cs p d]
      rw [hblock, inv.first_weight hz]
      exact initial_fold_invariant callerAt cs p s b _ _
        (by rw [hsum]; simpa [hz, WHIRNativeGuards.before] using inv.native_n)
        (hfold.trans (by rw [hz])) (inv.first_source hz)
        (by simpa [hsum] using hb) (by simpa [hsum] using caller)
    · have hblock : block = 1 := by simp [block, hz]
      simpa only [df, nf, Protocol.foldBlock, foldBlock, hblock] using
        lowFoldSteps_invariant callerAt c.folds[0]! cs p cs.folds.size 0 s d
          (inv.weight (by omega)) (by rw [hfold, inv.native_n]; exact hlevel.2.1.le)
  obtain ⟨hround, hood, hboundary, qs, hquery, hrows, hfinish⟩ :=
    verifyLevel_success c ch proof i s finish success
  change p.afterFold.size = cs.folds.size at hround
  change p.oods.size = cs.oodPoints.size at hood
  change deriveQueries (nf.n+c.rates[i]!) c.queries[i]! cs.querySqueezes = some qs at hquery
  change (if i+1 < c.folds.size then p.nextOracle.isSome = true
    else p.nextOracle.isSome = false ∧ proof.residual.size = 2^nf.n) at hboundary
  have hquery' : deriveQueries (CausalGame.remaining c i+c.rates[i]!) c.queries[i]!
      cs.querySqueezes = some qs := by simpa [hn] using hquery
  have hoods : ∀ j < p.oods.size, cs.oodPoints[j]!.size = nf.n := by
    intro j hj
    have hj' : j < cs.oodPoints.size := by omega
    rw [hn]
    apply WHIRNativeGuards.challenges_ood_point c ch hc i hi
    rw [getElem!_pos cs.oodPoints j hj']
    exact Array.getElem_mem hj'
  have hob := oodBatch_related callerAt c.folds[0]! cs p nf df.state hscalar hweight hoods
  dsimp only at hob
  let nb := oodBatch cs p nf
  let db := Protocol.oodBatch cs p df.state
  have hbeta : nb.2 = db.2 := hob.1
  have hqshape : (Basis.query nf.n qs cs.lambda).Shape nb.1.n := by
    change nf.n = nb.1.n ∧ nf.n ≤ 64
    have hdepth := hlevel.2.2.2.2
    exact ⟨hob.2.1.symm, by rw [hn]; omega⟩
  have hqinv : WeightInvariant callerAt c.folds[0]! (queryBatch nf.n i cs p qs nb)
      (Protocol.queryBatch df.n i cs p qs db).weight := by
    have h := hob.2.2.2.batch callerAt c.folds[0]! nb.1 db.1.weight
      (.query nf.n qs cs.lambda) hqshape
      (enforced p.rows cs.folds (powers cs.lambda qs.size) (i == 0))
      (db.2*cs.lambda) p.intro
    simpa [queryBatch, Protocol.queryBatch, VerifierState.batch, Basis.dense, hbeta, hn, hdn] using h
  have hqsame : ScalarSame (queryBatch nf.n i cs p qs nb)
      (Protocol.queryBatch df.n i cs p qs db) := by
    simpa [queryBatch, Protocol.queryBatch, Basis.dense, hbeta, hn, hdn] using
      same_batch nb.1 db.1 hob.2.2.1 (.query nf.n qs cs.lambda)
        (enforced p.rows cs.folds (powers cs.lambda qs.size) (i == 0)) (db.2*cs.lambda) p.intro
  let finishD : CheckedState := ⟨df.n, Protocol.queryBatch df.n i cs p qs db, p.nextOracle.getD #[]⟩
  refine ⟨finishD, ?_, ?_⟩
  · apply protocolLevel_of_checks c ch proof i d qs hround hood
    · dsimp only
      by_cases more : i+1 < c.folds.size
      · simp only [ite_eq_left more] at hboundary ⊢
        cases he : p.nextOracle with
        | none => simp [he] at hboundary
        | some next =>
          refine ⟨next, rfl, ?_⟩
          change oracleValid next (2^(df.n-c.folds[i+1]!+c.rates[i+1]!)) (2^c.folds[i+1]!) = true
          rw [hdn]
          exact roots i hi more next he
      · simp only [ite_eq_right more] at hboundary ⊢
        change p.nextOracle.isSome = false ∧ proof.residual.size = 2^df.n
        simpa only [hn, hdn] using hboundary
    · change deriveQueries (df.n+c.rates[i]!) c.queries[i]! cs.querySqueezes = some qs
      rw [hdn]
      exact hquery'
    · exact hrows
    · intro j hj
      rw [foldBlock_oracle, inv.oracle]
      exact authenticated i hi qs hquery' j hj
  · have hf : finish = queryBatch nf.n i cs p qs nb := hfinish
    rw [hf]
    constructor
    · change nb.1.n = WHIRNativeGuards.before c (i+1)
      exact hob.2.1.trans hn
    · exact hdn
    · exact hqsame
    · simp [finishD, oracleBefore, p]
    · omega
    · omega
    · intro _
      exact hqinv

theorem replay_refines (c : Config) (ch : Challenges) (proof : Opening)
    (callerAt : Array E → E) (b : Array E) (root : Oracle)
    (hc : ch.valid c = true) (hb : b.size = 2^c.logN)
    (caller : ∀ point : Array E, point.size = c.logN → callerAt point = Concrete.mle b point)
    (roots : RootShapes c proof) (authenticated : AuthenticatedRows c ch proof root)
    (count start : Nat) (bound : start + count ≤ c.folds.size)
    (s finish : State) (d : CheckedState)
    (inv : ReplayInvariant c callerAt b proof root start s d)
    (success : runChecked (verifyLevel c ch proof) count start s = .ok finish) :
    ∃ df, runChecked (Protocol.verifyLevel c ch proof) count start d = .ok df ∧
      ReplayInvariant c callerAt b proof root (start+count) finish df := by
  induction count generalizing start s d with
  | zero =>
    simp only [runChecked, Except.ok.injEq] at success
    subst finish
    exact ⟨d, rfl, inv⟩
  | succ count ih =>
    cases hstep : verifyLevel c ch proof start s with
    | error e => simp [runChecked, hstep] at success
    | ok next =>
      obtain ⟨nextD, hd, hr⟩ := verifyLevel_refines c ch proof callerAt b root hc hb caller
        roots authenticated start (by omega) s next d inv hstep
      obtain ⟨finishD, hf, hrel⟩ := ih (start+1) (by omega) next nextD hr
        (by simpa [runChecked, hstep] using success)
      refine ⟨finishD, by simpa [runChecked, hd] using hf, ?_⟩
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrel

theorem nativeVerify_success (c : Config) (ch : Challenges) (lanes : Nat)
    (initialClaim : E) (callerAt : Array E → E) (proof : Opening)
    (success : nativeVerify c ch lanes initialClaim callerAt proof = .ok ()) :
    ch.valid c = true ∧ proof.levels.size = c.folds.size ∧
      proof.tailMessages.size + 1 = ch.tail.size ∧
      ∃ s, runChecked (verifyLevel c ch proof) c.folds.size 0
        ⟨c.logN, initialClaim, proof.initial, ⟨[], []⟩⟩ = .ok s ∧
        (closeTail ch proof s).claim =
          sourceTerminal
            (callerAt (rotatePoint c.folds[0]! (s.source.ris ++ ch.tail.toList).toArray))
            s.source.saved s.source.ris ch.tail.toList proof.residual := by
  unfold nativeVerify at success
  cases hr : runChecked (verifyLevel c ch proof) c.folds.size 0
    ⟨c.logN, initialClaim, proof.initial, ⟨[], []⟩⟩ with
  | error e =>
    simp only [hr, except_bind_error] at success
    split_ifs at success <;> simp_all
  | ok s =>
    simp only [hr, except_bind_ok] at success
    split_ifs at success <;> simp_all

/-- Complete arithmetic refinement. The only external premises are public
initial/commitment shapes, actual row authentication, and the original caller
weight specification. All scalar, context, dimensional and terminal relations
are established by the checked native execution. -/
theorem nativeVerify_refines (c : Config) (ch : Challenges) (lanes : Nat)
    (initialClaim : E) (callerAt : Array E → E) (proof : Opening)
    (b : Array E) (root : Oracle)
    (weightShape : shapeValid c lanes b = true)
    (rootShape : oracleValid root (2^(c.logN-c.folds[0]!+c.rates[0]!)) lanes = true)
    (roots : RootShapes c proof) (authenticated : AuthenticatedRows c ch proof root)
    (caller : ∀ point : Array E, point.size = c.logN → callerAt point = Concrete.mle b point)
    (success : nativeVerify c ch lanes initialClaim callerAt proof = .ok ()) :
    Protocol.verify c ch lanes root b initialClaim proof = .ok () := by
  obtain ⟨hc, hlevels, htailMessages, s, hr, hterminal⟩ :=
    nativeVerify_success c ch lanes initialClaim callerAt proof success
  have hb : b.size = 2^c.logN := by
    have h := weightShape
    simp only [shapeValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact h.1.2
  let initial : State := ⟨c.logN, initialClaim, proof.initial, ⟨[], []⟩⟩
  let initialD : CheckedState := ⟨c.logN, ⟨b, initialClaim, proof.initial⟩, root⟩
  have hi : ReplayInvariant c callerAt b proof root 0 initial initialD := by
    constructor
    · simp [initial, WHIRNativeGuards.before]
    · simp [initialD, WHIRNativeGuards.before]
    · exact ⟨rfl, rfl⟩
    · simp [initialD, oracleBefore]
    · intro; rfl
    · intro; rfl
    · omega
  obtain ⟨d, hd, hf⟩ := replay_refines c ch proof callerAt b root hc hb caller
    roots authenticated c.folds.size 0 (by omega) initial s initialD hi hr
  simp only [Nat.zero_add] at hf
  have hpositive : 0 < c.folds.size := by
    have h := (WHIRNativeGuards.config_header c (WHIRNativeGuards.challenges_config c ch hc)).1
    omega
  have hw := hf.weight hpositive
  have ht : ch.tail.toList.length = s.n := by
    rw [hf.native_n]
    change ch.tail.size = c.logN - (c.folds.toList.take c.folds.size).sum
    rw [show c.folds.size = c.folds.toList.length from rfl, List.take_length]
    exact WHIRNativeGuards.challenges_tail c ch hc
  have hv := hw.terminal callerAt c.folds[0]! s d.state.weight proof.residual ch.tail.toList ht
  simp only [Array.toArray_toList] at hv
  have hmle : Concrete.mle d.state.weight ch.tail = (Protocol.closeTail ch proof d.state).weight[0]! := by
    rw [closeTail_weight]
    exact TerminalRefinement.mle_eq_foldLow_terminal _ _
      (by rw [hw.size]; congr 1; simpa using ht.symm)
  have hcheck : (Protocol.closeTail ch proof d.state).checkTerminal
      (Concrete.mle proof.residual ch.tail) = true := by
    apply beq_iff_eq.mpr
    rw [← hmle, hv]
    exact (closeTail_same ch proof s d.state hf.scalar).1.symm.trans hterminal
  have hinit : initializeVerifier c ch lanes root b initialClaim proof = .ok initialD := by
    simp [initializeVerifier, hc, weightShape, rootShape, hlevels, htailMessages, initialD]
  simp [Protocol.verify, hinit, Protocol.replayLevels, hd, checkClosing, hcheck]

/-- Literal source caller cutover: no evaluator-equality hypothesis is exposed. -/
def sourceNativeVerify {m : Nat} (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix) (lambda : E)
    (c : Config) (ch : Challenges) (lanes : Nat) (initialClaim : E) (proof : Opening) : Except String Unit :=
  nativeVerify c ch lanes initialClaim
    (SuccinctRingGroups.sourceStackWeightAt family points seed lambda) proof

theorem sourceNativeVerify_refines {m : Nat} (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix) (lambda : E)
    (c : Config) (ch : Challenges) (lanes : Nat) (initialClaim : E) (proof : Opening) (root : Oracle)
    (familyShape : SuccinctRingWeight.FamilyShape c.logN family)
    (pointShapes : ∀ i : Fin points.size, SuccinctPointWeight.Shape c.logN points[i])
    (weightShape : shapeValid c lanes
      (CausalGame.batchClaims (2^c.logN) (RingPCSGame.transformedClaims (2^c.logN) family points seed) lambda).weight = true)
    (rootShape : oracleValid root (2^(c.logN-c.folds[0]!+c.rates[0]!)) lanes = true)
    (roots : RootShapes c proof) (authenticated : AuthenticatedRows c ch proof root)
    (success : sourceNativeVerify family points seed lambda c ch lanes initialClaim proof = .ok ()) :
    Protocol.verify c ch lanes root
      (CausalGame.batchClaims (2^c.logN) (RingPCSGame.transformedClaims (2^c.logN) family points seed) lambda).weight
      initialClaim proof = .ok () := by
  apply nativeVerify_refines c ch lanes initialClaim
    (SuccinctRingGroups.sourceStackWeightAt family points seed lambda) proof _ root
    weightShape rootShape roots authenticated _ success
  intro point hp
  have h := SuccinctRingGroups.sourceStackWeightAt_eq_batch_mle family points seed lambda point
    (by simpa only [hp] using familyShape) (by simpa only [hp] using pointShapes)
  simpa only [hp] using h

/-- Source initial target accumulation, without constructing dense claim weights
merely to read their scalar projection. The family occupies power zero. -/
def initialClaim {m : Nat} (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix) (lambda : E) : E :=
  (points.foldl (fun s point => (s.1 + s.2 * RingPCSGame.pointValue point, s.2 * lambda))
    (RingPCSGame.familyTarget (fun j => (family j).slices) seed, lambda)).1

private def denseBatchStep (lambda : E) (s : CausalGame.Claim × E) (claim : CausalGame.Claim) :
    CausalGame.Claim × E :=
  (⟨weightGlue s.1.weight claim.weight s.2, s.1.value + s.2 * claim.value⟩, s.2 * lambda)

private theorem batchProjection (lambda : E) (claims : List CausalGame.Claim) (s : CausalGame.Claim × E) :
    ((claims.foldl (denseBatchStep lambda) s).1.value, (claims.foldl (denseBatchStep lambda) s).2) =
      claims.foldl (fun q claim => (q.1 + q.2 * claim.value, q.2 * lambda)) (s.1.value, s.2) := by
  induction claims generalizing s with
  | nil => rfl
  | cons claim claims ih =>
    simp only [List.foldl_cons, ih, denseBatchStep]

theorem batchClaims_value (width : Nat) (claims : Array CausalGame.Claim) (lambda : E) :
    (CausalGame.batchClaims width claims lambda).value =
      (claims.toList.foldl (fun s claim => (s.1 + s.2 * claim.value, s.2 * lambda)) (0, 1)).1 := by
  have hfold : CausalGame.batchClaims width claims lambda =
      (claims.foldl (denseBatchStep lambda) (⟨tab width (fun _ => 0), 0⟩, 1)).1 := by
    unfold CausalGame.batchClaims
    simp only [Array.forIn_pure_yield_eq_foldl, pure_bind]
    rfl
  rw [hfold, ← Array.foldl_toList]
  exact congrArg Prod.fst (batchProjection lambda claims.toList (⟨tab width (fun _ => 0), 0⟩, 1))

theorem initialClaim_eq_batch_value {m : Nat} (width : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (seed : RingPCSGame.Prefix) (lambda : E) :
    initialClaim family points seed lambda =
      (CausalGame.batchClaims width (RingPCSGame.transformedClaims width family points seed) lambda).value := by
  rw [batchClaims_value]
  simp only [RingPCSGame.transformedClaims, Array.toList_append,
    Array.toList_map, List.cons_append, List.nil_append, List.foldl_cons,
    RingPCSGame.familyPublic, zero_add, one_mul, List.foldl_map]
  rw [initialClaim, ← Array.foldl_toList]
  rfl

/-- Full executable caller-side arithmetic entry point: both the initial claim
and final caller weight are computed by source scalar routines only. -/
def sourceVerify {m : Nat} (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix) (lambda : E)
    (c : Config) (ch : Challenges) (lanes : Nat) (proof : Opening) : Except String Unit :=
  sourceNativeVerify family points seed lambda c ch lanes (initialClaim family points seed lambda) proof

theorem sourceVerify_refines {m : Nat} (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix) (lambda : E)
    (c : Config) (ch : Challenges) (lanes : Nat) (proof : Opening) (root : Oracle)
    (familyShape : SuccinctRingWeight.FamilyShape c.logN family)
    (pointShapes : ∀ i : Fin points.size, SuccinctPointWeight.Shape c.logN points[i])
    (weightShape : shapeValid c lanes
      (CausalGame.batchClaims (2^c.logN) (RingPCSGame.transformedClaims (2^c.logN) family points seed) lambda).weight = true)
    (rootShape : oracleValid root (2^(c.logN-c.folds[0]!+c.rates[0]!)) lanes = true)
    (roots : RootShapes c proof) (authenticated : AuthenticatedRows c ch proof root)
    (success : sourceVerify family points seed lambda c ch lanes proof = .ok ()) :
    let batched := CausalGame.batchClaims (2^c.logN)
      (RingPCSGame.transformedClaims (2^c.logN) family points seed) lambda
    Protocol.verify c ch lanes root batched.weight batched.value proof = .ok () := by
  have h := sourceNativeVerify_refines family points seed lambda c ch lanes
    (initialClaim family points seed lambda) proof root familyShape pointShapes
    weightShape rootShape roots authenticated success
  rwa [initialClaim_eq_batch_value (2^c.logN) family points seed lambda] at h

end Whir.WHIRNativeArithmetic
