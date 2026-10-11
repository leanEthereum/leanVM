import Whir.CountedCandidateCheck

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-! Arithmetic annotations for the actual checked causal verifier. Charges follow source loop lengths, not acceptance and not a user-provided cost model. Dense source columns use the certified countedColumn upper charge. Rejected trials are charged too. This is a field-operation bound, not machine time. -/
namespace Whir.ExtractorArithmeticCost
open Concrete Protocol CausalGame CountedCandidateCheck AuthenticatedResetSupport

/-- FoldPair has two additions and one multiplication; Message.eval has six operations. The output loop has weight.size/2 iterations. -/
def foldCharge (weight : Array E) : Nat := 3 * (weight.size / 2) + 6

def countedSteps {S : Type*} (step : Nat → S → S × Nat) : Nat → Nat → S × Nat → S × Nat
  | 0, _, s => s
  | count + 1, start, s =>
    let next := step start s.1
    countedSteps step count (start + 1) (next.1, s.2 + next.2)

theorem countedSteps_value {S : Type*} (step : Nat → S → S × Nat)
    (count start : Nat) (s : S × Nat) :
    (countedSteps step count start s).1 = runSteps (fun i v => (step i v).1) count start s.1 := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih =>
    simpa [countedSteps, runSteps] using
      (ih (start + 1) ((step start s.1).1, s.2 + (step start s.1).2))

def countedFoldBlock (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (s : CheckedState) : CheckedState × Nat :=
  countedSteps (fun j state => (foldStep block cs p j state, foldCharge state.state.weight))
    cs.folds.size 0 (s, 0)

@[simp] theorem countedFoldBlock_value (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (s : CheckedState) : (countedFoldBlock block cs p s).1 = foldBlock block cs p s := by
  simp [countedFoldBlock, countedSteps_value, foldBlock]

/-- eqTable's source map body evaluates (1+r), x*(1+r), x*r per old entry. -/
def tableCharge (point : Array E) : Nat := 3 * (2 ^ point.size - 1)

def tableStep (out : Array E) (r : E) : Array E × Nat :=
  ((out.map fun x => x * (1 + r)) ++ (out.map fun x => x * r), 3 * out.size)

def countedEqTable (point : Array E) : Array E × Nat := loop tableStep point.toList (#[1], 0)

theorem countedEqTable_value (point : Array E) : (countedEqTable point).1 = eqTable point := by
  unfold countedEqTable
  rw [loop_value]
  unfold eqTable
  simp only [Array.forIn_pure_yield_eq_foldl, pure_bind]
  rw [← Array.foldl_toList]
  rfl

private theorem table_loop_cost (xs : List E) (a : Array E) (cost : Nat) :
    (loop tableStep xs (a, cost)).2 = cost + 3 * a.size * (2 ^ xs.length - 1) := by
  induction xs generalizing a cost with
  | nil => simp [loop]
  | cons x xs ih =>
    simp only [loop, tableStep, ih, Array.size_append, Array.size_map, List.length_cons, Nat.pow_succ]
    have positive : 0 < 2 ^ xs.length := by positivity
    have hsub : 2 ^ xs.length * 2 - 1 = 2 * (2 ^ xs.length - 1) + 1 := by omega
    rw [hsub]
    ring

theorem countedEqTable_cost (point : Array E) : (countedEqTable point).2 = tableCharge point := by
  simp [countedEqTable, table_loop_cost, tableCharge]

/-- Each OOD multiplies lambda once, glues two message coefficients and the claim (six operations), and glues every weight entry (two operations). -/
def countedOodBatch (cs : LevelChallenges) (p : LevelProof) (s : VerifierState E) :
    (VerifierState E × E) × Nat :=
  countedSteps (fun j state =>
    (oodStep cs p j state, tableCharge cs.oodPoints[j]! + 2 * state.1.weight.size + 7))
    p.oods.size 0 ((s, E.one), 0)

@[simp] theorem countedOodBatch_value (cs : LevelChallenges) (p : LevelProof) (s : VerifierState E) :
    (countedOodBatch cs p s).1 = oodBatch cs p s := by
  simp [countedOodBatch, countedSteps_value, oodBatch]

/-- Source column cost certificate, with no inverse treated as unit cost. -/
def columnCharge (n : Nat) : Nat := 2 * n * n + 131 * n + 3 * 2 ^ n

theorem actualColumn_charge (n q : Nat) :
    (countedColumn n q).1 = column n q ∧ (countedColumn n q).2 ≤ columnCharge n :=
  ⟨countedColumn_value n q, countedColumn_cost n q⟩

/-- Source powers loop: one multiplication per query. inducedColumns executes one multiply and one addition per query per dense output coordinate. enforced builds one eq table and performs dot plus multiply/add for each supplied row. The upper charge uses the actual minimum dot length bound 2^folds.size. -/
def queryCharge (n : Nat) (cs : LevelChallenges) (p : LevelProof) (qs : Array Nat)
    (s : VerifierState E × E) : Nat :=
  qs.size + qs.size * (columnCharge n + 2 * 2 ^ n) +
    tableCharge cs.folds + p.rows.size * (2 * 2 ^ cs.folds.size + 2) +
    2 * s.1.weight.size + 7

def countedQueryBatch (n i : Nat) (cs : LevelChallenges) (p : LevelProof)
    (qs : Array Nat) (s : VerifierState E × E) : VerifierState E × Nat :=
  (queryBatch n i cs p qs s, queryCharge n cs p qs s)

@[simp] theorem countedQueryBatch_value (n i : Nat) (cs : LevelChallenges) (p : LevelProof)
    (qs : Array Nat) (s : VerifierState E × E) :
    (countedQueryBatch n i cs p qs s).1 = queryBatch n i cs p qs s := rfl

/-- Same checked ordering as verifyLevel, including early failures before query batching. Authentication, shape checks and query derivation have zero field arithmetic; their input/loop resources are accounted separately. -/
def countedVerifyLevel (c : Config) (ch : Challenges) (proof : Opening)
    (i : Nat) (s : CheckedState) : Except String CheckedState × Nat :=
  let cs := ch.levels[i]!
  let p := proof.levels[i]!
  if p.afterFold.size != cs.folds.size || p.oods.size != cs.oodPoints.size then
    (.error "round/OOD length", 0)
  else
    let folded := countedFoldBlock (if i == 0 then 2 ^ (c.logN - c.folds[0]!) else 1) cs p s
    let boundary : Except String Unit := do
      if i + 1 < c.folds.size then
        let next ← p.nextOracle.elim (throw "missing commitment") pure
        if !oracleValid next (2 ^ (folded.1.n - c.folds[i + 1]! + c.rates[i + 1]!))
            (2 ^ c.folds[i + 1]!) then throw "commitment shape"
      else
        if p.nextOracle.isSome || proof.residual.size != 2 ^ folded.1.n then throw "final length"
    match boundary with
    | .error error => (.error error, folded.2)
    | .ok _ =>
      match deriveQueries (folded.1.n + c.rates[i]!) c.queries[i]! cs.querySqueezes with
      | none => (.error "query challenges", folded.2)
      | some qs =>
        if p.rows.size != qs.size then (.error "query length", folded.2)
        else
          match runChecked (authenticateRow folded.1.oracle qs p) qs.size 0 () with
          | .error error => (.error error, folded.2)
          | .ok _ =>
            let ood := countedOodBatch cs p folded.1.state
            let batched := countedQueryBatch folded.1.n i cs p qs ood.1
            (.ok ⟨folded.1.n, batched.1, p.nextOracle.getD #[]⟩,
              folded.2 + ood.2 + batched.2)

private theorem except_bind_ok {S T : Type u} (s : S) (f : S → Except String T) :
    (Except.ok s >>= f) = f s := rfl
private theorem except_bind_error {S T : Type u} (e : String) (f : S → Except String T) :
    (Except.error e >>= f) = .error e := rfl
private theorem except_pure {S : Type u} (s : S) : (pure s : Except String S) = .ok s := rfl
private theorem except_throw {S : Type u} (e : String) : (throw e : Except String S) = .error e := rfl
attribute [local simp] except_bind_ok except_bind_error except_pure except_throw

theorem countedVerifyLevel_value (c : Config) (ch : Challenges) (proof : Opening)
    (i : Nat) (s : CheckedState) :
    (countedVerifyLevel c ch proof i s).1 = verifyLevel c ch proof i s := by
  cases next : proof.levels[i]!.nextOracle <;>
    simp only [countedVerifyLevel, verifyLevel, countedFoldBlock_value,
      countedOodBatch_value, countedQueryBatch_value, next, Option.elim,
      except_pure, except_throw, except_bind_ok, except_bind_error]
  all_goals first | rfl | (split <;> try simp_all)
  all_goals first | rfl | (split <;> try simp_all)
  all_goals first | rfl | (split <;> try simp_all)
  all_goals first | rfl | (split <;> try simp_all)
  all_goals first | rfl | (split <;> try simp_all)
  all_goals first | rfl | (split <;> try simp_all)
  all_goals first | rfl | (split <;> try simp_all)

/-- Checked replay retains the count even when a level rejects. -/
def countedChecked {S : Type*} (step : Nat → S → Except String S × Nat) :
    Nat → Nat → S → Except String S × Nat
  | 0, _, s => (.ok s, 0)
  | count + 1, start, s =>
    let next := step start s
    match next.1 with
    | .error error => (.error error, next.2)
    | .ok value =>
      let tail := countedChecked step count (start + 1) value
      (tail.1, next.2 + tail.2)

theorem countedChecked_value {S : Type*} (step : Nat → S → Except String S × Nat)
    (count start : Nat) (s : S) :
    (countedChecked step count start s).1 = runChecked (fun i v => (step i v).1) count start s := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih =>
    simp only [countedChecked, runChecked]
    cases h : (step start s).1 <;> simp [ih]

def countedCloseTail (ch : Challenges) (proof : Opening) (s : VerifierState E) :
    VerifierState E × Nat :=
  countedSteps (fun j state => (tailStep ch proof j state, foldCharge state.weight))
    ch.tail.size 0 (s, 0)

@[simp] theorem countedCloseTail_value (ch : Challenges) (proof : Opening) (s : VerifierState E) :
    (countedCloseTail ch proof s).1 = closeTail ch proof s := by
  simp [countedCloseTail, countedSteps_value, closeTail]

def countedVerify (c : Config) (ch : Challenges) (lanes : Nat) (root : Oracle)
    (weight : Array E) (target : E) (proof : Opening) : Except String Unit × Nat :=
  match initializeVerifier c ch lanes root weight target proof with
  | .error error => (.error error, 0)
  | .ok initial =>
    let levels := countedChecked (countedVerifyLevel c ch proof) c.folds.size 0 initial
    match levels.1 with
    | .error error => (.error error, levels.2)
    | .ok final =>
      let tail := countedCloseTail ch proof final.state
      (checkClosing ch proof tail.1,
        levels.2 + tail.2 + tableCharge ch.tail + 2 * min proof.residual.size (2 ^ ch.tail.size) + 1)

theorem countedVerify_value (c : Config) (ch : Challenges) (lanes : Nat) (root : Oracle)
    (weight : Array E) (target : E) (proof : Opening) :
    (countedVerify c ch lanes root weight target proof).1 = verify c ch lanes root weight target proof := by
  unfold countedVerify verify replayLevels
  simp only [countedChecked_value, countedVerifyLevel_value, countedCloseTail_value]
  cases initialized : initializeVerifier c ch lanes root weight target proof with
  | error error => simp
  | ok initial =>
    simp only [except_bind_ok]
    cases runChecked (verifyLevel c ch proof) c.folds.size 0 initial <;> simp

/-- batchClaims preserves its dense width even for malformed claim arrays. -/
def countedBatchClaims (width : Nat) (claims : Array Claim) (lambda : E) : Claim × Nat :=
  (batchClaims width claims lambda, claims.size * (2 * width + 3))

@[simp] theorem countedBatchClaims_value (width : Nat) (claims : Array Claim) (lambda : E) :
    (countedBatchClaims width claims lambda).1 = batchClaims width claims lambda := rfl

def countedAcceptedReplies (input : Public) (tape : Tape input.config) (answers : List Reply) : Bool × Nat :=
  let c := input.config
  let ch := challenges c tape
  if !(input.claims.all fun claim => shapeValid c input.lanes claim.weight) then (false, 0)
  else
    let statement := countedBatchClaims (2 ^ c.logN) input.claims tape.1
    match opening c ch answers.toArray with
    | .error _ => (false, statement.2)
    | .ok proof =>
      let checked := countedVerify c ch input.lanes (liftRoot input.root) statement.1.weight statement.1.value proof
      (checked.1.isOk, statement.2 + checked.2)

theorem countedAcceptedReplies_value (input : Public) (tape : Tape input.config) (answers : List Reply) :
    (countedAcceptedReplies input tape answers).1 = acceptedReplies input tape answers := by
  unfold countedAcceptedReplies acceptedReplies
  simp only [countedBatchClaims_value, countedVerify_value]
  split <;> simp_all
  cases opening input.config (challenges input.config tape) answers.toArray <;> rfl

end Whir.ExtractorArithmeticCost
