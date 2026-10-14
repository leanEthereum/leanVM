import Whir.SpongefishCurrentOpeningAcceptance
import Whir.WHIRNativeRestoration
import Whir.WHIRPhysicalSoundness
import Whir.CausalPositions
import Whir.CausalBoundary
import Whir.CountedCandidateCheckOriginalCorrectness

/-! Current #607 native opening acceptance as an abstract causal experiment. Pure algebra: no primitive oracle, Merkle table or partition appears in the main statement. The native opening carries empty placeholders for the next commitment oracles; `restoredReplies` replaces each present placeholder by a supplied ghost oracle `next (i+1)`, leaving every physical field unchanged. Row authentication is an explicit hypothesis in the native Merkle opening form that binding against frozen first-mention captures discharges: level 0 opened rows are rows of the base oracle `root`, and level `i > 0` opened rows are rows of `next i`, at the native query indices of the tape. -/
namespace Whir.SpongefishCurrentOpeningExperiment
open Concrete Protocol CausalGame CausalProbability
open SpongefishCurrentOpeningAcceptance
set_option autoImplicit false

variable {p : ParameterBounds.Profile}
local notation "cfg" => ParameterBounds.config p

/-! ## Restored replies -/

/-- Level of the visible fold coordinate at reply position `n`, zero elsewhere. -/
def replyLevel (c : Config) (n : Nat) : Nat :=
  match (visibleCoordinates c)[n]? with
  | some (.fold i _) => i.val
  | _ => 0

/-- A present next-oracle placeholder at reply position `n` becomes the ghost oracle of the following level; every other field is kept. -/
def restoreReply (c : Config) (next : Nat → Oracle) (n : Nat) : Reply → Reply
  | .fold m o residual => .fold m (o.map fun _ => next (replyLevel c n + 1)) residual
  | r => r

def restore (c : Config) (next : Nat → Oracle) (replies : Array Reply) : Array Reply :=
  replies.mapIdx fun n r => restoreReply c next n r

/-- Native replies with the ghost next oracles restored. -/
def restoredReplies (col : Collected p) (next : Nat → Oracle) : Array Reply :=
  restore cfg next col.replies

/-- Base oracle at level zero, supplied next oracle at every later level. -/
def levelOracle (root : BaseOracle) (next : Nat → Oracle) (i : Nat) : Oracle :=
  if i = 0 then liftRoot root else next i

theorem erase_restoreReply (c : Config) (next : Nat → Oracle) (n : Nat) (r : Reply) :
    WHIRPhysicalErasure.eraseReply (restoreReply c next n r) = WHIRPhysicalErasure.eraseReply r := by
  cases r <;> simp [restoreReply, WHIRPhysicalErasure.eraseReply, Option.map_map, Function.comp_def]

theorem rootField_restoreReply (c : Config) (next : Nat → Oracle) (n : Nat) (r : Reply) :
    rootField (restoreReply c next n r) = (rootField r).map fun _ => next (replyLevel c n + 1) := by
  cases r <;> rfl

theorem restore_size (c : Config) (next : Nat → Oracle) (replies : Array Reply) :
    (restore c next replies).size = replies.size := by
  simp [restore]

theorem restore_getElem? (c : Config) (next : Nat → Oracle) (replies : Array Reply) (n : Nat) :
    (restore c next replies)[n]? = replies[n]?.map (restoreReply c next n) := by
  simp [restore, Array.getElem?_mapIdx]

theorem restore_getElem! (c : Config) (next : Nat → Oracle) (replies : Array Reply) (n : Nat) :
    (restore c next replies)[n]! = restoreReply c next n replies[n]! := by
  by_cases h : n < replies.size
  · rw [_root_.getElem!_pos (restore c next replies) n (by rwa [restore_size]),
      _root_.getElem!_pos replies n h]
    simp [restore]
  · rw [_root_.getElem!_neg (restore c next replies) n (by rwa [restore_size]),
      _root_.getElem!_neg replies n h]
    rfl

theorem restore_erase (c : Config) (next : Nat → Oracle) (replies : Array Reply) :
    (restore c next replies).map WHIRPhysicalErasure.eraseReply =
      replies.map WHIRPhysicalErasure.eraseReply := by
  apply Array.ext
  · simp [restore_size]
  · intro n h₁ h₂
    simp [restore, erase_restoreReply]

/-- Prefix law: entry `n` of the restored replies is a function of the native entry `n` and the ghost oracles only. -/
theorem restoredReplies_getElem? (col : Collected p) (next : Nat → Oracle) (n : Nat) :
    (restoredReplies col next)[n]? = col.replies[n]?.map (restoreReply cfg next n) :=
  restore_getElem? cfg next col.replies n

theorem restoredReplies_prefix (col col' : Collected p) (next : Nat → Oracle) (n : Nat)
    (same : col.replies[n]? = col'.replies[n]?) :
    (restoredReplies col next)[n]? = (restoredReplies col' next)[n]? := by
  rw [restoredReplies_getElem?, restoredReplies_getElem?, same]

/-- Restoration agrees with the native replies except for the next-oracle field. -/
theorem restoredReplies_agree (col : Collected p) (next : Nat → Oracle) :
    (restoredReplies col next).size = col.replies.size ∧
    (restoredReplies col next).map WHIRPhysicalErasure.eraseReply =
      col.replies.map WHIRPhysicalErasure.eraseReply ∧
    ∀ n, rootField (restoredReplies col next)[n]! =
      (rootField col.replies[n]!).map fun _ => next (replyLevel cfg n + 1) := by
  refine ⟨restore_size _ _ _,restore_erase _ _ _,fun n => ?_⟩
  rw [restoredReplies,restore_getElem!,rootField_restoreReply]

/-! ## Parsing the restored replies -/

@[simp] theorem initialField_restoreReply (c : Config) (next : Nat → Oracle) (n : Nat) (r : Reply) :
    initialField (restoreReply c next n r) = initialField r := by cases r <;> rfl
@[simp] theorem foldField_restoreReply (c : Config) (next : Nat → Oracle) (n : Nat) (r : Reply) :
    foldField (restoreReply c next n r) = foldField r := by cases r <;> rfl
@[simp] theorem residualField_restoreReply (c : Config) (next : Nat → Oracle) (n : Nat) (r : Reply) :
    residualField (restoreReply c next n r) = residualField r := by cases r <;> rfl
@[simp] theorem oodField_restoreReply (c : Config) (next : Nat → Oracle) (n : Nat) (r : Reply) :
    oodField (restoreReply c next n r) = oodField r := by cases r <;> rfl
@[simp] theorem rowsField_restoreReply (c : Config) (next : Nat → Oracle) (n : Nat) (r : Reply) :
    rowsField (restoreReply c next n r) = rowsField r := by cases r <;> rfl
@[simp] theorem introField_restoreReply (c : Config) (next : Nat → Oracle) (n : Nat) (r : Reply) :
    introField (restoreReply c next n r) = introField r := by cases r <;> rfl
@[simp] theorem tailField_restoreReply (c : Config) (next : Nat → Oracle) (n : Nat) (r : Reply) :
    tailField (restoreReply c next n r) = tailField r := by cases r <;> rfl

theorem fold_visible {c : Config} (i : Fin c.folds.size) (j : Fin c.folds[i.val]!) :
    Coordinate.fold i j ∈ visibleCoordinates c := by
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨i.val,List.mem_range.mpr i.isLt,?_⟩
  unfold levelCoordinates
  rw [dite_eq_left i.isLt]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨j,rfl⟩))

theorem replyLevel_fold {c : Config} (i : Fin c.folds.size) (j : Fin c.folds[i.val]!) :
    replyLevel c (position (Coordinate.fold i j)) = i.val := by
  have mem := fold_visible i j
  have found : (visibleCoordinates c)[position (Coordinate.fold i j)]? = some (Coordinate.fold i j) := by
    unfold position
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem mem), List.getElem_idxOf]
  simp [replyLevel, found]

theorem challenges_folds_size (c : Config) (t : Tape c) (i : Nat) (hi : i < c.folds.size) :
    (challenges c t).levels[i]!.folds.size = c.folds[i]! := by
  simp [challenges, _root_.getElem!_pos, hi]

theorem decodedLevel_restore (c : Config) (t : Tape c) (next : Nat → Oracle)
    (replies : Array Reply) (i : Nat) (hi : i < c.folds.size) :
    decodedLevel c (challenges c t) (restore c next replies) i =
      { decodedLevel c (challenges c t) replies i with
        nextOracle := (decodedLevel c (challenges c t) replies i).nextOracle.map
          fun _ => next (i+1) } := by
  unfold decodedLevel
  simp only [restore_getElem!, foldField_restoreReply, oodField_restoreReply,
    rowsField_restoreReply, introField_restoreReply]
  congr 1
  split_ifs with h
  · rw [rootField_restoreReply]
    congr 2
    have size := challenges_folds_size c t i hi
    have positive : 0 < c.folds[i]! := size ▸ h.2
    have bound : c.folds[i]! - 1 < c.folds[(⟨i,hi⟩ : Fin c.folds.size).val]! := by
      change c.folds[i]! - 1 < c.folds[i]!
      omega
    have pos := CausalPositions.position_fold (c := c) ⟨i,hi⟩ ⟨c.folds[i]! - 1,bound⟩ t
    have level := replyLevel_fold (c := c) ⟨i,hi⟩ ⟨c.folds[i]! - 1,bound⟩
    rw [pos] at level
    have level' : replyLevel c (levelStart (challenges c t) i + (c.folds[i]! - 1)) = i := level
    rw [size, show levelStart (challenges c t) i + c.folds[i]! - 1 =
      levelStart (challenges c t) i + (c.folds[i]! - 1) by omega, level']
  · rfl

theorem decodedOpening_restore (c : Config) (t : Tape c) (next : Nat → Oracle)
    (replies : Array Reply) :
    decodedOpening c (challenges c t) (restore c next replies) =
      WHIRNativeErasure.restoreOracles (decodedOpening c (challenges c t) replies) next := by
  unfold decodedOpening WHIRNativeErasure.restoreOracles
  simp only [restore_getElem!, initialField_restoreReply, residualField_restoreReply,
    tailField_restoreReply]
  congr 1
  apply Array.ext
  · simp
  · intro i h₁ h₂
    simp only [Fin.getElem_fin, Array.getElem_ofFn]
    rw [decodedLevel_restore c t next replies i (by simpa using h₁)]

theorem opening_restore (c : Config) (t : Tape c) (next : Nat → Oracle)
    (replies : Array Reply) (proof : Opening)
    (parsed : opening c (challenges c t) replies = .ok proof) :
    opening c (challenges c t) (restore c next replies) =
      .ok (WHIRNativeErasure.restoreOracles proof next) := by
  have checks : checkReplies (visibleBatches c E.zero (challenges c t)) (restore c next replies).toList =
      checkReplies (visibleBatches c E.zero (challenges c t)) replies.toList := by
    rw [← WHIRPhysicalErasure.checkReplies_erase _ (restore c next replies).toList,
      ← WHIRPhysicalErasure.checkReplies_erase _ replies.toList, ← Array.toList_map,
      ← Array.toList_map, restore_erase]
  unfold opening at parsed ⊢
  rw [checks]
  cases hc : checkReplies (visibleBatches c E.zero (challenges c t)) replies.toList with
  | error e => simp [hc] at parsed
  | ok u =>
    simp only [hc] at parsed ⊢
    have same : decodedOpening c (challenges c t) replies = proof := by
      simpa using parsed
    rw [decodedOpening_restore, same]
    rfl

theorem opening_decoded (c : Config) (ch : Challenges) (replies : Array Reply) (proof : Opening)
    (parsed : opening c ch replies = .ok proof) : proof = decodedOpening c ch replies := by
  unfold opening at parsed
  cases hc : checkReplies (visibleBatches c E.zero ch) replies.toList with
  | error e => simp [hc] at parsed
  | ok u =>
    simp only [hc] at parsed
    exact (by simpa using parsed : decodedOpening c ch replies = proof).symm

theorem restoreOracles_level (proof : Opening) (lookup : Nat → Oracle) (i : Nat)
    (hi : i < proof.levels.size) :
    (WHIRNativeErasure.restoreOracles proof lookup).levels[i]! =
      { proof.levels[i]! with nextOracle := proof.levels[i]!.nextOracle.map fun _ => lookup (i+1) } := by
  unfold WHIRNativeErasure.restoreOracles
  rw [_root_.getElem!_pos _ i (by simpa using hi), _root_.getElem!_pos proof.levels i hi]
  simp

theorem decodedOpening_level (c : Config) (ch : Challenges) (replies : Array Reply) (i : Nat)
    (hi : i < c.folds.size) :
    (decodedOpening c ch replies).levels[i]! = decodedLevel c ch replies i := by
  unfold decodedOpening
  rw [_root_.getElem!_pos _ i (by simpa using hi)]
  simp

/-! ## Commitments, root shapes and authenticated rows -/

/-- An accepted native opening carries a commitment at every non-final level. -/
theorem nativeVerify_present (c : Config) (ch : Challenges) (lanes : Nat) (initialClaim : E)
    (callerAt : Array E → E) (proof : Opening)
    (success : WHIRNativeArithmetic.nativeVerify c ch lanes initialClaim callerAt proof = .ok ()) :
    ∀ k, k + 1 < c.folds.size → (proof.levels[k]!.nextOracle).isSome = true := by
  obtain ⟨_,_,_,s,run,_⟩ :=
    WHIRNativeArithmetic.nativeVerify_success c ch lanes initialClaim callerAt proof success
  have inv := OperationalRefinement.runChecked_invariant (WHIRNativeArithmetic.verifyLevel c ch proof)
    (fun i _ => ∀ k, k < i → k + 1 < c.folds.size → (proof.levels[k]!.nextOracle).isSome = true)
    c.folds.size 0 _ s (by intro k hk; omega) (by
      intro i t u _ _ before step k hk more
      by_cases same : k = i
      · subst same
        have boundary := (WHIRNativeArithmetic.verifyLevel_success c ch proof k t u step).2.2.1
        simpa only [more,↓reduceIte] using boundary
      · exact before k (by omega) more) run
  intro k more
  exact inv k (by omega) more

/-- Supplied next oracles have the rectangular shape of their code level. -/
def NextShapes (c : Config) (next : Nat → Oracle) : Prop :=
  ∀ j, 0 < j → j < c.folds.size →
    oracleValid (next j) (ParameterBounds.length c j) (2^c.folds[j]!) = true

/-- Verifier-side row agreement in the arithmetic `AuthenticatedRows` form, read at the reply position of each query coordinate. -/
def DerivedRows (c : Config) (t : Tape c) (replies : Array Reply)
    (root : BaseOracle) (next : Nat → Oracle) : Prop :=
  ∀ i : Fin c.folds.size, ∀ qs,
    deriveQueries (remaining c i.val + c.rates[i.val]!) c.queries[i.val]!
      (challenges c t).levels[i.val]!.querySqueezes = some qs →
    ∀ j, j < qs.size →
      (rowsField replies[position (Coordinate.query i)]!)[j]! = (levelOracle root next i.val)[qs[j]!]!

/-- Row authentication in the native Merkle opening form: at every level the rows of the native query reply are the rows of `levelOracle root next i` (the base oracle at level 0, the supplied next oracle at later levels) at the native query indices of the tape's query sample. -/
def RowsAuthenticated (t : Tape cfg) (replies : Array Reply)
    (root : BaseOracle) (next : Nat → Oracle) : Prop :=
  ∀ i : Fin (cfg).folds.size,
    rowsField replies[position (Coordinate.query i)]! =
      WHIRPhysicalVerifier.atQueries (levelOracle root next i.val)
        (WHIRPhysicalVerifier.queryIndices p i (get (Coordinate.query i) t))

theorem queryIndices_derived (i : Fin (cfg).folds.size) (x : Sample (Coordinate.query i)) :
    deriveQueries (remaining cfg i.val + (cfg).rates[i.val]!) (cfg).queries[i.val]! (Array.ofFn x.1) =
      some (WHIRPhysicalVerifier.queryIndices p i x).toArray := by
  have depth := TapeValidity.config_query_depth cfg (ParameterBounds.production_config_valid p).1
    i.val i.isLt
  unfold WHIRPhysicalVerifier.queryIndices
  rw [Array.toArray_toList]
  exact QueryBatchSoundness.queries_actual _ _ x.1 (by omega) depth.2

theorem rowsAuthenticated_derived (t : Tape cfg) (replies : Array Reply)
    (root : BaseOracle) (next : Nat → Oracle) (rows : RowsAuthenticated t replies root next) :
    DerivedRows cfg t replies root next := by
  intro i qs derived j hj
  have squeezes : (challenges cfg t).levels[i.val]!.querySqueezes =
      Array.ofFn (get (Coordinate.query i) t).1 := by
    simp [challenges, _root_.getElem!_pos, i.isLt]
    rfl
  rw [squeezes, queryIndices_derived] at derived
  have same := Option.some.inj derived
  subst same
  have inside : j < (WHIRPhysicalVerifier.queryIndices p i (get (Coordinate.query i) t)).length := by
    simpa using hj
  rw [rows i]
  simp [WHIRPhysicalVerifier.atQueries, _root_.getElem!_pos, inside]

theorem restored_rootShapes (next : Nat → Oracle) (proof : Opening)
    (sizes : proof.levels.size = (cfg).folds.size) (shapes : NextShapes cfg next) :
    WHIRNativeArithmetic.RootShapes cfg (WHIRNativeErasure.restoreOracles proof next) := by
  intro i bound hasNext nxt found
  rw [restoreOracles_level proof next i (sizes ▸ bound)] at found
  obtain ⟨_,_,equal⟩ := Option.map_eq_some_iff.mp found
  subst nxt
  have shape := shapes (i+1) (by omega) hasNext
  have dimensions := ((CausalBoundary.production_boundary_facts p ⟨i,bound⟩).2.2 hasNext).1
  change remaining cfg (i+1) + (cfg).folds[i+1]! = remaining cfg i at dimensions
  have rest : remaining cfg (i+1) = remaining cfg i - (cfg).folds[i+1]! := by omega
  simpa only [ParameterBounds.length,rest] using shape

theorem challenges_ood_size (c : Config) (t : Tape c) (i : Nat) (hi : i < c.folds.size) :
    (challenges c t).levels[i]!.oodPoints.size = oodCount c i := by
  simp [challenges, _root_.getElem!_pos, hi]

theorem restored_authenticated (c : Config) (t : Tape c) (replies : Array Reply)
    (proof : Opening) (root : BaseOracle) (next : Nat → Oracle)
    (parsed : opening c (challenges c t) replies = .ok proof)
    (present : ∀ k, k + 1 < c.folds.size → (proof.levels[k]!.nextOracle).isSome = true)
    (rows : DerivedRows c t replies root next) :
    WHIRNativeArithmetic.AuthenticatedRows c (challenges c t)
      (WHIRNativeErasure.restoreOracles proof next) (liftRoot root) := by
  have decoded := opening_decoded c _ replies proof parsed
  have sizes : proof.levels.size = c.folds.size := by rw [decoded]; simp [decodedOpening]
  intro i hi qs derived j hj
  have opened := rows ⟨i,hi⟩ qs derived j hj
  rw [restoreOracles_level proof next i (sizes ▸ hi)]
  dsimp only
  have rowsEq : proof.levels[i]!.rows = rowsField replies[position (Coordinate.query (⟨i,hi⟩ : Fin c.folds.size))]! := by
    rw [decoded, decodedOpening_level c _ replies i hi, CausalPositions.position_query ⟨i,hi⟩ t]
    simp only [decodedLevel, challenges_folds_size c t i hi, challenges_ood_size c t i hi]
  rw [rowsEq, opened]
  unfold WHIRNativeArithmetic.oracleBefore levelOracle
  by_cases zero : i = 0
  · simp [zero]
  · simp only [zero, ↓reduceIte]
    rw [restoreOracles_level proof next (i-1) (by omega)]
    have some := present (i-1) (by omega)
    obtain ⟨o,ho⟩ := Option.isSome_iff_exists.mp some
    simp only [ho, Option.map_some, Option.getD_some, show i - 1 + 1 = i by omega]

/-! ## Original claims shapes from the prepared guards -/

theorem guards_occupied {c : Config} {lanes m : Nat} {family : Fin m → RingPCSGame.FamilyClaim}
    {points : Array RingPCSGame.PointClaim} {anchorPoint : Array E}
    (guards : OriginalClaimsChecker.Guards c lanes family points anchorPoint) :
    lanes * 2^(c.logN - c.folds[0]!) ≤ 2^c.logN := by
  calc lanes * 2^(c.logN - c.folds[0]!) ≤ 2^c.folds[0]! * 2^(c.logN - c.folds[0]!) :=
        Nat.mul_le_mul_right _ guards.2.2.2.1
    _ = 2^c.logN := by rw [← Nat.pow_add, Nat.add_sub_of_le guards.1]

theorem guards_nativeShapes {c : Config} {lanes m : Nat} {family : Fin m → RingPCSGame.FamilyClaim}
    {points : Array RingPCSGame.PointClaim} {anchorPoint : Array E}
    (guards : OriginalClaimsChecker.Guards c lanes family points anchorPoint) :
    SuccinctRingWeight.FamilyShape c.logN family ∧
    (∀ i : Fin points.size, SuccinctPointWeight.Shape c.logN points[i]) ∧
    (∀ point ∈ points.toList, ∀ v, lanes * 2^(c.logN - c.folds[0]!) ≤ v →
      RingPCSGame.pointWeight point v = 0) := by
  have occupied := guards_occupied guards
  obtain ⟨_,_,_,_,_,families,pointGuards⟩ := guards
  refine ⟨fun j => ⟨(families j).1,(families j).2.1,(families j).2.2.trans occupied⟩,?_,?_⟩
  · intro i
    have g := pointGuards i
    generalize points[i] = claim at g ⊢
    cases claim with
    | point offset point value =>
      exact ⟨g.2.1,g.2.2.trans occupied⟩
    | strided offset slot stride point value =>
      exact ⟨g.2.2.1,g.2.2.2.trans occupied,g.2.1⟩
  · intro claim member v lower
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem member
    have g := pointGuards ⟨i,by simpa using hi⟩
    simp only [Array.getElem_toList] at g ⊢
    generalize points[i] = claim at g ⊢
    cases claim with
    | point offset point value =>
      have far := g.2.2
      simp only [RingPCSGame.pointWeight, RingPCSGame.regionWeight]
      rw [ite_eq_right (by omega)]
    | strided offset slot stride point value =>
      have far := g.2.2.2
      simp only [RingPCSGame.pointWeight]
      rw [ite_eq_right (by omega)]

theorem guards_claims_shapes {lanes m : Nat} {family : Fin m → RingPCSGame.FamilyClaim}
    {points : Array RingPCSGame.PointClaim} {anchorPoint : Array E}
    (guards : OriginalClaimsChecker.Guards cfg lanes family points anchorPoint)
    (seed : RingPCSGame.Prefix) (lambda : E) (point : Array E) (value : E) :
    ((((RingPCSGame.transformedClaims (2^(cfg).logN) family points seed).push
      ⟨CommitmentAnchor.weight cfg lanes point,value⟩).all
        (fun claim => Protocol.shapeValid cfg lanes claim.weight)) = true) ∧
      Protocol.shapeValid cfg lanes (CausalGame.batchClaims (2^(cfg).logN)
        ((RingPCSGame.transformedClaims (2^(cfg).logN) family points seed).push
          ⟨CommitmentAnchor.weight cfg lanes point,value⟩) lambda).weight = true := by
  let claims := (RingPCSGame.transformedClaims (2^(cfg).logN) family points seed).push
    ⟨CommitmentAnchor.weight cfg lanes point,value⟩
  change (claims.all fun claim => Protocol.shapeValid cfg lanes claim.weight) = true ∧
    Protocol.shapeValid cfg lanes (CausalGame.batchClaims (2^(cfg).logN) claims lambda).weight = true
  have families := guards.2.2.2.2.2.1
  have positive := guards.2.2.1
  have laneBound := guards.2.2.2.1
  obtain ⟨_,_,pointSupport⟩ := guards_nativeShapes guards
  have supported : ∀ claim ∈ claims.toList, claim.weight.size = 2^(cfg).logN ∧
      ∀ i, lanes*2^((cfg).logN-(cfg).folds[0]!) ≤ i → i < 2^(cfg).logN → claim.weight[i]! = 0 := by
    intro claim member
    simp only [claims,Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with member | last
    · refine ⟨WHIRCallerSupport.transformed_claim_size _ _ _ _ claim member,?_⟩
      intro i lower upper
      exact WHIRCallerSupport.transformed_claim_support _ _ _ _ seed
        (fun j => (families j).2.2) pointSupport claim member i lower upper
    · subst claim
      refine ⟨by simp [CommitmentAnchor.weight],?_⟩
      intro i lower upper
      simp [CommitmentAnchor.weight,ArrayLayout.getElem!_tab _ _ _ upper,Nat.not_lt_of_le lower]
      rfl
  constructor
  · apply Array.all_eq_true'.mpr
    intro claim member
    have supported := supported claim (by simpa [claims] using member)
    exact WHIRCallerSupport.shapeValid_of_support cfg lanes claim.weight
      (ParameterBounds.production_config_valid p).1 positive laneBound supported.1
      (fun i lower upper => supported.2 i lower (by simpa [supported.1] using upper))
  · apply WHIRCallerSupport.shapeValid_of_support cfg lanes _
      (ParameterBounds.production_config_valid p).1 positive laneBound
      (InitialBatching.batchClaims_size _ _ _)
    intro i lower upper
    apply InitialBatching.batchClaims_zero_tail (2^(cfg).logN) (lanes*2^((cfg).logN-(cfg).folds[0]!))
      claims lambda _ i lower (by simpa only [InitialBatching.batchClaims_size] using upper)
    intro j i lower upper
    exact (supported claims[j] (by simp)).2 i lower upper

/-! ## Anchored native equations refine the dense verifier -/

theorem callerAt_dense (c : Config) (record : AnchoredHeaderCodec.Record) {m : Nat}
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (seed : RingPCSGame.Prefix) (lambda : E)
    (hN : record.shape.logN = c.logN) (hB : record.shape.logBatch = c.folds[0]!)
    (occupied : 0 < record.shape.lanes ∧ record.shape.lanes ≤ 2^record.shape.logBatch)
    (dimensions : record.shape.logBatch < record.shape.logN)
    (pointSize : record.point.length = record.shape.logN)
    (familyShape : SuccinctRingWeight.FamilyShape c.logN family)
    (pointShapes : ∀ i : Fin points.size, SuccinctPointWeight.Shape c.logN points[i])
    (x : Array E) (hx : x.size = c.logN) :
    AnchoredPhysicalAnchor.callerAt record family points seed lambda x =
      Concrete.mle (batchClaims (2^c.logN)
        (AnchorPrefixRefinement.anchoredClaims c record family points seed) lambda).weight x := by
  rw [AnchorPrefixRefinement.anchoredClaims, AnchorPrefixRefinement.batchClaims_push]
  rw [AccumulatedTerminalAlgebra.mle_weightGlue _ _ _ _
    (by simp [hx]) (by simp [CommitmentAnchor.weight])]
  rw [AnchoredPhysicalAnchor.callerAt, AnchorPrefixRefinement.anchorAt_dense c record.shape
    record.point.toArray x hN hB occupied dimensions (by simpa using pointSize) (hx.trans hN.symm)]
  have old := SuccinctRingGroups.sourceStackWeightAt_eq_batch_mle family points seed lambda x
    (by simpa [hx] using familyShape) (by simpa [hx] using pointShapes)
  rw [old]
  simp only [RingPCSGame.transformedClaims, Array.size_append, Array.size_map]
  simp [hx, Nat.add_comm]

theorem anchored_refines (c : Config) (record : AnchoredHeaderCodec.Record) {m : Nat}
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (seed : RingPCSGame.Prefix) (lambda : E) (ch : Challenges) (proof : Opening) (root : Oracle)
    (hN : record.shape.logN = c.logN) (hB : record.shape.logBatch = c.folds[0]!)
    (occupied : 0 < record.shape.lanes ∧ record.shape.lanes ≤ 2^record.shape.logBatch)
    (dimensions : record.shape.logBatch < record.shape.logN)
    (pointSize : record.point.length = record.shape.logN)
    (familyShape : SuccinctRingWeight.FamilyShape c.logN family)
    (pointShapes : ∀ i : Fin points.size, SuccinctPointWeight.Shape c.logN points[i])
    (weightShape : shapeValid c record.shape.lanes
      (batchClaims (2^c.logN) (AnchorPrefixRefinement.anchoredClaims c record family points seed)
        lambda).weight = true)
    (rootShape : oracleValid root (2^(c.logN-c.folds[0]!+c.rates[0]!)) record.shape.lanes = true)
    (roots : WHIRNativeArithmetic.RootShapes c proof)
    (authenticated : WHIRNativeArithmetic.AuthenticatedRows c ch proof root)
    (success : AnchoredPhysicalAnchor.sourceVerify record family points seed lambda c ch proof = .ok ()) :
    Protocol.verify c ch record.shape.lanes root
      (batchClaims (2^c.logN) (AnchorPrefixRefinement.anchoredClaims c record family points seed) lambda).weight
      (batchClaims (2^c.logN) (AnchorPrefixRefinement.anchoredClaims c record family points seed) lambda).value
      proof = .ok () := by
  have refined := WHIRNativeArithmetic.nativeVerify_refines c ch record.shape.lanes
    (AnchoredPhysicalAnchor.initialClaim record family points seed lambda)
    (AnchoredPhysicalAnchor.callerAt record family points seed lambda) proof _ root weightShape rootShape
    roots authenticated
    (callerAt_dense c record family points seed lambda hN hB occupied dimensions pointSize
      familyShape pointShapes) success
  rwa [AnchorPrefixRefinement.initialClaim_dense c] at refined

/-! ## The accepted batching scalar is the tape's initial sample -/

/-- Once a seed is recorded, the tape's initial coordinate is its batching scalar. -/
def SeedTape (col : Collected p) : Prop := ∀ s, col.seed = some s → col.tape.1 = s.2

theorem powStep_keeps (C : DuplexModeGame.PrimitiveOracle) (grinding : Fin (cfg).folds.size → Fin 64)
    (cur next : SpongefishPCSRoundFrames.Cursor) (col col' : Collected p) (q : Coord p)
    (ok : powStep C grinding cur col q = some (next,col')) :
    col'.seed = col.seed ∧ col'.tape = col.tape := by
  cases q with
  | query i =>
    simp only [powStep] at ok
    split at ok
    · cases ok; exact ⟨rfl,rfl⟩
    · split at ok
      · cases ok
      · split at ok
        · cases ok
        · cases ok; exact ⟨rfl,rfl⟩
  | initial => cases ok; exact ⟨rfl,rfl⟩
  | fold i j => cases ok; exact ⟨rfl,rfl⟩
  | ood i j => cases ok; exact ⟨rfl,rfl⟩
  | tail j => cases ok; exact ⟨rfl,rfl⟩

theorem recordSample_seedTape (col : Collected p) (q : Coord p) (x : PCSBCSRounds.Raw q)
    (kept : SeedTape col) : SeedTape (recordSample col q x) := by
  intro s found
  cases q with
  | initial =>
    have same : x = s := Option.some.inj found
    subst same
    change get Coordinate.initial
      (set Coordinate.initial col.tape (StackWHIRReplay.projectSample Coordinate.initial x)) = x.2
    rw [get_set]
    rfl
  | fold i j =>
    change get Coordinate.initial (set (Coordinate.fold i j) col.tape _) = s.2
    rw [get_set_ne _ _ _ _ (by intro h; cases h)]
    exact kept s found
  | ood i j =>
    change get Coordinate.initial (set (Coordinate.ood i j) col.tape _) = s.2
    rw [get_set_ne _ _ _ _ (by intro h; cases h)]
    exact kept s found
  | query i =>
    change get Coordinate.initial (set (Coordinate.query i) col.tape _) = s.2
    rw [get_set_ne _ _ _ _ (by intro h; cases h)]
    exact kept s found
  | tail j =>
    change get Coordinate.initial (set (Coordinate.tail j) col.tape _) = s.2
    rw [get_set_ne _ _ _ _ (by intro h; cases h)]
    exact kept s found

theorem replyStep_keeps (C : DuplexModeGame.PrimitiveOracle)
    (decode : List Nat → Nat → List FiatShamirGame.Byte → Option MerkleTransport.PrunedMerklePaths)
    (lanes : Nat) (cur next : SpongefishPCSRoundFrames.Cursor) (col col' : Collected p) (q : Coord p)
    (ok : replyStep C decode lanes cur col q = some (next,col')) :
    col'.seed = col.seed ∧ col'.tape = col.tape := by
  cases q with
  | initial =>
    simp only [replyStep] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok; exact ⟨rfl,rfl⟩
  | fold i j =>
    simp only [replyStep] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    split at ok
    · split at ok
      · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
        cases ok; exact ⟨rfl,rfl⟩
      · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
        cases ok; exact ⟨rfl,rfl⟩
    · cases ok; exact ⟨rfl,rfl⟩
  | ood i j =>
    simp only [replyStep] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok; exact ⟨rfl,rfl⟩
  | query i =>
    simp only [replyStep] at ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
    cases ok; exact ⟨rfl,rfl⟩
  | tail j =>
    change (if isVisibleTail j then (do
      let (next,m) ← readMessage C cur
      pure (next,{col with replies := col.replies.push (.tail m)})) else some (cur,col)) =
      some (next,col') at ok
    split at ok
    · obtain ⟨_,_,ok⟩ := Option.bind_eq_some_iff.mp ok
      cases ok; exact ⟨rfl,rfl⟩
    · cases ok; exact ⟨rfl,rfl⟩

theorem run_seedTape (C : DuplexModeGame.PrimitiveOracle)
    (decode : List Nat → Nat → List FiatShamirGame.Byte → Option MerkleTransport.PrunedMerklePaths)
    (grinding : Fin (cfg).folds.size → Fin 64) (lanes : Nat) :
    ∀ (qs : List (Coord p)) (state final : SpongefishPCSRoundFrames.Cursor × Collected p),
      SeedTape state.2 → SpongefishCurrentOpeningAcceptance.run C decode grinding lanes qs state =
        some final → SeedTape final.2
  | [], state, final, kept, ok => by
    simp only [SpongefishCurrentOpeningAcceptance.run,Option.some.injEq] at ok
    subst ok
    exact kept
  | q :: qs, state, final, kept, ok => by
    simp only [SpongefishCurrentOpeningAcceptance.run] at ok
    obtain ⟨mid,first,rest⟩ := Option.bind_eq_some_iff.mp ok
    apply run_seedTape C decode grinding lanes qs mid final _ rest
    unfold SpongefishCurrentOpeningAcceptance.step at first
    obtain ⟨⟨powed,col⟩,powOk,first⟩ := Option.bind_eq_some_iff.mp first
    obtain ⟨⟨drawn,x⟩,_,first⟩ := Option.bind_eq_some_iff.mp first
    obtain ⟨powSeed,powTape⟩ := powStep_keeps C grinding _ _ _ _ q powOk
    obtain ⟨replySeed,replyTape⟩ := replyStep_keeps C decode lanes _ mid.1 _ mid.2 q first
    have recorded := recordSample_seedTape col q x (by
      intro s found
      rw [powTape]
      exact kept s (powSeed ▸ found))
    intro s found
    rw [replyTape]
    exact recorded s (replySeed ▸ found)

/-- The accepted batching scalar of the native seed is the initial tape sample. -/
theorem accepted_lambda {C : DuplexModeGame.PrimitiveOracle}
    {decode : List Nat → Nat → List FiatShamirGame.Byte → Option MerkleTransport.PrunedMerklePaths}
    {grinding : Fin (cfg).folds.size → Fin 64} {r : SpongefishSessionAdapter.Record}
    {input : PCSBCSCallerBinding.CallerInput p} {cur : SpongefishPCSRoundFrames.Cursor}
    (a : Accepted C decode grinding r input cur) : a.collected.tape.1 = a.seed.2 :=
  run_seedTape C decode grinding r.shape.lanes (WHIRHistory.schedule cfg) _ _
    (fun _ found => by cases found) a.ran a.seed a.seeded

/-! ## Caller binding facts guaranteed by the current original reconstruction -/

theorem prepare_binding (r : SpongefishSessionAdapter.Record)
    (claims : SpongefishCurrentSourceCallerOriginal.Payload) (input : PCSBCSCallerBinding.CallerInput p)
    (prepared : SpongefishCurrentSourceCallerOriginal.prepare p r claims = some input) :
    input.lanes = r.shape.lanes ∧ input.anchorPoint = r.point.toArray ∧ input.anchorValue = r.value := by
  unfold SpongefishCurrentSourceCallerOriginal.prepare at prepared
  split at prepared
  · split at prepared
    · obtain ⟨_,_,built⟩ := Option.bind_eq_some_iff.mp prepared
      cases built
      exact ⟨rfl,rfl,rfl⟩
    · cases prepared
  · cases prepared

theorem finish_binding (layout : WHIRCallerClaims.CallerLayout) (q : FiatShamirGame.Coordinate)
    (r : SpongefishSessionAdapter.Record)
    (result : Except (SpongefishCurrentMixedModeCompiler.Data ×
      SpongefishCurrentPrimitiveEventCompiler.ReplayError) SpongefishCurrentMixedModeCompiler.Data)
    (input : PCSBCSCallerBinding.CallerInput p)
    (finished : SpongefishCurrentSourceCallerOriginal.finish p layout q r result = some input) :
    r.shape = AnchoredSourceCaller.shape layout ∧ input.lanes = r.shape.lanes ∧
      input.anchorPoint = r.point.toArray ∧ input.anchorValue = r.value := by
  cases result with
  | error e => cases finished
  | ok data =>
    change (if (SpongefishPCSRoundFrames.close data.pending).core.history ≠ q.history ∨
        data.narg ≠ [] then none else do
      let events ← SpongefishCurrentSourceCallerOriginal.callerEvents data.events
      let claims ← SpongefishCurrentSourceCallerOriginal.parseEvents layout r events
      SpongefishCurrentSourceCallerOriginal.prepare p r claims) = some input at finished
    split at finished
    · cases finished
    obtain ⟨_,_,finished⟩ := Option.bind_eq_some_iff.mp finished
    obtain ⟨claims,parsed,finished⟩ := Option.bind_eq_some_iff.mp finished
    refine ⟨?_,prepare_binding r claims input finished⟩
    unfold SpongefishCurrentSourceCallerOriginal.parseEvents at parsed
    split at parsed
    · cases parsed
    · next same => exact not_not.mp same

/-- A physically reconstructed original fixes lanes, anchor point and value from the received record, and the record carries the caller layout's shape, whose batch dimension is the configured first fold. -/
theorem physicalCandidate_binding (C : DuplexModeGame.PrimitiveOracle) (iv : FiatShamirGame.Digest32)
    (layout : WHIRCallerClaims.CallerLayout) (q : FiatShamirGame.Coordinate)
    (r : SpongefishSessionAdapter.Record) (instanceBytes : List FiatShamirGame.Byte)
    (input : PCSBCSCallerBinding.CallerInput p)
    (found : SpongefishCurrentSourceCallerOriginal.physicalCandidate C iv p layout q r instanceBytes =
      some input) :
    r.shape = AnchoredSourceCaller.shape layout ∧ r.shape.logBatch = (cfg).folds[0]! ∧
      input.lanes = r.shape.lanes ∧ input.anchorPoint = r.point.toArray ∧ input.anchorValue = r.value := by
  unfold SpongefishCurrentSourceCallerOriginal.physicalCandidate at found
  obtain ⟨result,_,finished⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨shape,binding⟩ := finish_binding layout q r result input finished
  refine ⟨shape,?_,binding⟩
  rw [shape,(WHIRCallerSupport.config_initial_geometry p).2]
  rfl

/-! ## Native acceptance is abstract experiment acceptance -/

/-- An accepted native opening (seed, parsed replies, anchored native equations) for an original bound to the received record is an accepted causal experiment on the original claims, for the base oracle `root` and the indexed strategy of the replies with restored ghost next oracles, provided the opened rows are authenticated against `root` and `next` and these oracles have their public shapes. -/
theorem experiment_accepts (r : SpongefishSessionAdapter.Record)
    (input : PCSBCSCallerBinding.CallerInput p) (col : Collected p)
    (seed : RingPCSGame.Prefix × E) (proof : Opening)
    (lambda : col.tape.1 = seed.2)
    (parsed : CausalGame.opening cfg (challenges cfg col.tape) col.replies = .ok proof)
    (equations : anchoredVerify r input.family input.points seed.1 seed.2 cfg
      (challenges cfg col.tape) proof = .ok ())
    (lanes : input.lanes = r.shape.lanes) (anchorPoint : input.anchorPoint = r.point.toArray)
    (anchorValue : input.anchorValue = r.value)
    (dimension : r.shape.logN = (cfg).logN) (batch : r.shape.logBatch = (cfg).folds[0]!)
    (root : BaseOracle) (next : Nat → Oracle)
    (rootShape : oracleValid (liftRoot root) (2^((cfg).logN-(cfg).folds[0]!+(cfg).rates[0]!))
      r.shape.lanes = true)
    (nextShapes : NextShapes cfg next)
    (rows : RowsAuthenticated col.tape col.replies root next) :
    experiment (OriginalClaimsChecker.input input.prepared root seed.1)
      (CausalStrategy.indexedStrategy (restoredReplies col next)) col.tape = true := by
  let record : AnchoredHeaderCodec.Record :=
    ⟨r.shape,r.root,⟨DuplexRefinement.zeroDigest,fun _ => none,0,false,0,0⟩,r.point,r.value⟩
  have native : AnchoredPhysicalAnchor.sourceVerify record input.family input.points seed.1 seed.2 cfg
      (challenges cfg col.tape) proof = .ok () := equations
  have present := nativeVerify_present cfg _ _ _ _ proof native
  have restored := opening_restore cfg col.tape next col.replies proof parsed
  have sizes : proof.levels.size = (cfg).folds.size := by
    rw [opening_decoded _ _ _ proof parsed]
    simp [decodedOpening]
  have nativeRestored : AnchoredPhysicalAnchor.sourceVerify record input.family input.points seed.1
      seed.2 cfg (challenges cfg col.tape) (WHIRNativeErasure.restoreOracles proof next) = .ok () := by
    unfold AnchoredPhysicalAnchor.sourceVerify
    rw [WHIRNativeErasure.nativeVerify_restored]
    exact native
  have guards := input.prepared.guards
  obtain ⟨familyShape,pointShapes,_⟩ := guards_nativeShapes guards
  obtain ⟨allShapes,batchShape⟩ := guards_claims_shapes guards seed.1 seed.2 r.point.toArray r.value
  rw [lanes] at allShapes batchShape
  have claimsEq : (OriginalClaimsChecker.input input.prepared root seed.1).claims =
      AnchorPrefixRefinement.anchoredClaims cfg record input.family input.points seed.1 := by
    rw [OriginalClaimsChecker.input_claims, AnchorPrefixRefinement.anchoredClaims, lanes, anchorPoint,
      anchorValue]
  have occupied : 0 < r.shape.lanes ∧ r.shape.lanes ≤ 2^r.shape.logBatch := by
    rw [← lanes,batch]
    exact ⟨guards.2.2.1,guards.2.2.2.1⟩
  have dimensions : r.shape.logBatch < r.shape.logN := by
    rw [batch,dimension,(WHIRCallerSupport.config_initial_geometry p).1,
      (WHIRCallerSupport.config_initial_geometry p).2]
    omega
  have pointSize : r.point.length = r.shape.logN := by
    have size := guards.2.2.2.2.1
    rw [anchorPoint] at size
    simpa [dimension] using size
  apply WHIRPhysicalSoundness.experiment_indexed_accepts (OriginalClaimsChecker.input input.prepared root seed.1)
    col.tape (restoredReplies col next) (WHIRNativeErasure.restoreOracles proof next) restored
  · change ((OriginalClaimsChecker.input input.prepared root seed.1).claims.all
      fun claim => shapeValid cfg input.lanes claim.weight) = true
    rw [claimsEq,lanes]
    exact allShapes
  · change Protocol.verify cfg (challenges cfg col.tape) input.lanes (liftRoot root)
      (batchClaims (2^(cfg).logN) (OriginalClaimsChecker.input input.prepared root seed.1).claims
        col.tape.1).weight
      (batchClaims (2^(cfg).logN) (OriginalClaimsChecker.input input.prepared root seed.1).claims
        col.tape.1).value (WHIRNativeErasure.restoreOracles proof next) = .ok ()
    rw [claimsEq,lambda,lanes]
    exact anchored_refines cfg record input.family input.points seed.1 seed.2 (challenges cfg col.tape)
      _ (liftRoot root) dimension batch occupied dimensions pointSize familyShape pointShapes
      batchShape rootShape (restored_rootShapes next proof sizes nextShapes)
      (restored_authenticated cfg col.tape col.replies proof root next parsed present
        (rowsAuthenticated_derived col.tape col.replies root next rows))
      nativeRestored

/-- The same conclusion read off an `Accepted` native opening: the seed, the parsed replies, the anchored equations and the batching scalar all come from the accepted run. -/
theorem accepted_experiment {C : DuplexModeGame.PrimitiveOracle}
    {decode : List Nat → Nat → List FiatShamirGame.Byte → Option MerkleTransport.PrunedMerklePaths}
    {grinding : Fin (cfg).folds.size → Fin 64} {r : SpongefishSessionAdapter.Record}
    {input : PCSBCSCallerBinding.CallerInput p} {cur : SpongefishPCSRoundFrames.Cursor}
    (a : Accepted C decode grinding r input cur)
    (lanes : input.lanes = r.shape.lanes) (anchorPoint : input.anchorPoint = r.point.toArray)
    (anchorValue : input.anchorValue = r.value)
    (dimension : r.shape.logN = (cfg).logN) (batch : r.shape.logBatch = (cfg).folds[0]!)
    (root : BaseOracle) (next : Nat → Oracle)
    (rootShape : oracleValid (liftRoot root) (2^((cfg).logN-(cfg).folds[0]!+(cfg).rates[0]!))
      r.shape.lanes = true)
    (nextShapes : NextShapes cfg next)
    (rows : RowsAuthenticated a.collected.tape a.collected.replies root next) :
    experiment (OriginalClaimsChecker.input input.prepared root a.seed.1)
      (CausalStrategy.indexedStrategy (restoredReplies a.collected next)) a.collected.tape = true :=
  experiment_accepts r input a.collected a.seed a.proof (accepted_lambda a) a.parsed a.equations
    lanes anchorPoint anchorValue dimension batch root next rootShape nextShapes rows

/-- With the original reconstructed by `physicalCandidate` on the received record, only the record dimension, the oracle shapes and row authentication remain. -/
theorem candidate_experiment {C : DuplexModeGame.PrimitiveOracle}
    {decode : List Nat → Nat → List FiatShamirGame.Byte → Option MerkleTransport.PrunedMerklePaths}
    {grinding : Fin (cfg).folds.size → Fin 64} {r : SpongefishSessionAdapter.Record}
    {input : PCSBCSCallerBinding.CallerInput p} {cur : SpongefishPCSRoundFrames.Cursor}
    (a : Accepted C decode grinding r input cur) (iv : FiatShamirGame.Digest32)
    (layout : WHIRCallerClaims.CallerLayout) (q : FiatShamirGame.Coordinate)
    (instanceBytes : List FiatShamirGame.Byte)
    (found : SpongefishCurrentSourceCallerOriginal.physicalCandidate C iv p layout q r instanceBytes =
      some input)
    (dimension : r.shape.logN = (cfg).logN)
    (root : BaseOracle) (next : Nat → Oracle)
    (rootShape : oracleValid (liftRoot root) (2^((cfg).logN-(cfg).folds[0]!+(cfg).rates[0]!))
      r.shape.lanes = true)
    (nextShapes : NextShapes cfg next)
    (rows : RowsAuthenticated a.collected.tape a.collected.replies root next) :
    experiment (OriginalClaimsChecker.input input.prepared root a.seed.1)
      (CausalStrategy.indexedStrategy (restoredReplies a.collected next)) a.collected.tape = true := by
  obtain ⟨_,batch,lanes,anchorPoint,anchorValue⟩ :=
    physicalCandidate_binding C iv layout q r instanceBytes input found
  exact accepted_experiment a lanes anchorPoint anchorValue dimension batch root next rootShape
    nextShapes rows

#print axioms restoredReplies_prefix
#print axioms restoredReplies_agree
#print axioms opening_restore
#print axioms restored_authenticated
#print axioms restored_rootShapes
#print axioms accepted_lambda
#print axioms physicalCandidate_binding
#print axioms experiment_accepts
#print axioms accepted_experiment
#print axioms candidate_experiment

end Whir.SpongefishCurrentOpeningExperiment
