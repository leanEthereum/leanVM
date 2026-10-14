import Whir.SupportedCandidateProtocol

/-! Dense source encoding commutes with the actual chronological Root0
coefficient folds. This supplies the scalar equality used by row cancellation. -/
namespace Whir.SupportedCandidateProtocol
open Concrete Protocol CandidateFolding SupportedCandidateExtraction
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
attribute [local irreducible] ParameterBounds.config

noncomputable def column {k N : Nat} (enc : (Fin k → E) →ₗ[E] (Fin N → E))
    (lanes : Nat) (a : Array E) (q : Fin N) : Array E :=
  Array.ofFn fun lane : Fin lanes => enc (unpack true lanes k a lane) q

theorem column_fold {k N lanes : Nat} (enc : (Fin k → E) →ₗ[E] (Fin N → E))
    (a : Array E) (shape : a.size = (lanes*2)*k) (q : Fin N) (r : E) :
    column enc lanes (foldValues a k r) q = foldLow (column enc (lanes*2) a q) r := by
  let table := unpack true (lanes*2) k a
  have packed : pack true table = a := pack_unpack true a shape
  change column enc lanes (foldValues a (foldBlock true k) r) q = _
  rw [← packed, ← pack_fold true table r]
  simp only [column, unpack_pack]
  rw [← foldOracle_column (fun lane q => enc (table lane) q) r q]
  apply congrArg Array.ofFn
  funext lane
  have linear := congrFun (encode_foldTable enc table r lane) q
  exact linear

private def foldList (k : Nat) (points : List E) (a : Array E) : Array E :=
  points.foldl (fun a r => foldValues a k r) a

private theorem foldList_size (k : Nat) (points : List E) (a : Array E)
    (shape : a.size = 2 ^ points.length * k) : (foldList k points a).size = k := by
  induction points generalizing a with
  | nil => simpa only [foldList, List.foldl_nil, List.length_nil, pow_zero, one_mul] using shape
  | cons r points ih =>
    apply ih
    change (foldValues a k r).size = 2 ^ points.length * k
    rw [ReplayRefinement.foldValues_eq_lane, ArrayLayout.size_foldLane, shape]
    simp only [List.length_cons, pow_succ]
    rw [Nat.mul_right_comm, Nat.mul_div_left _ (by decide : 0 < 2)]

private theorem column_foldList {k N : Nat} (enc : (Fin k → E) →ₗ[E] (Fin N → E))
    (points : List E) (a : Array E) (shape : a.size = 2 ^ points.length * k) (q : Fin N) :
    column enc 1 (foldList k points a) q =
      #[Concrete.mle (column enc (2 ^ points.length) a q) points.toArray] := by
  induction points generalizing a with
  | nil =>
    change column enc 1 a q = #[Concrete.mle (column enc 1 a q) #[]]
    rw [TerminalRefinement.mle_empty _ (by simp [column])]
    apply Array.ext
    · simp [column]
    · intro j hj hj'
      have zero : j = 0 := by simpa [column] using hj
      subst j
      simp [column]
  | cons r points ih =>
    have nextShape : (foldValues a k r).size = 2 ^ points.length * k := by
      rw [ReplayRefinement.foldValues_eq_lane, ArrayLayout.size_foldLane, shape]
      simp only [List.length_cons, pow_succ]
      rw [Nat.mul_right_comm, Nat.mul_div_left _ (by decide : 0 < 2)]
    change column enc 1 (foldList k points (foldValues a k r)) q = _
    rw [ih _ nextShape]
    have nextColumn := column_fold (lanes := 2 ^ points.length) enc a
      (by simpa [List.length_cons, pow_succ] using shape) q r
    have mle := @TerminalRefinement.mle_cons E FieldModel.instCommRingE inferInstance
      (column enc (2 ^ (points.length+1)) a q)
      points.toArray r (by simp [column])
    rw [nextColumn, List.length_cons, pow_succ, List.toArray_cons]
    rw [pow_succ] at mle
    rw [← List.toArray_cons r points] at mle
    exact congrArg (fun x : E => #[x]) mle.symm

/-- Real executable dense encoding at one coordinate after all lane folds. -/
theorem encoded_foldList (n rate : Nat) (points : Array E) (a : Array E)
    (shape : a.size = 2 ^ points.size * 2 ^ n)
    (q : Fin (2 ^ (n+rate))) :
    (encode n rate (points.foldl (fun a r => foldValues a (2 ^ n) r) a))[q.val]! =
      Concrete.mle (column (concreteEncoder n rate) (2 ^ points.size) a q) points := by
  have cols := column_foldList (concreteEncoder n rate) points.toList a (by simpa using shape) q
  have size := foldList_size (2 ^ n) points.toList a (by simpa using shape)
  have entry := congrArg (fun row : Array E => row[0]!) cols
  have unpacked : unpack true 1 (2 ^ n) (foldList (2 ^ n) points.toList a) 0 =
      fun j => (foldList (2 ^ n) points.toList a)[j.val]! := by
    funext j
    simp [unpack, topIndex]
  have linear := ConcreteCandidates.concreteEncoder_ofFn n rate
    (unpack true 1 (2 ^ n) (foldList (2 ^ n) points.toList a) 0) q
  have coeffs : Array.ofFn (fun j : Fin (2 ^ n) => (foldList (2 ^ n) points.toList a)[j.val]!) =
      foldList (2 ^ n) points.toList a := by
    apply Array.ext
    · simpa using size.symm
    · intro j hj hj'
      simp [getElem!_pos, hj']
  rw [unpacked] at linear
  simp [column] at entry
  rw [unpacked, linear, coeffs] at entry
  simpa only [foldList, Array.foldl_toList, Array.toArray_toList, Array.length_toList, column] using entry

open CausalGame CausalExecution CausalProbability ExecutionShapes ParameterBounds InitialKnowledgeSchedule

theorem foldFrom_initial (input : Public) (t : Tape input.config)
    (hasLevel : 0 < input.config.folds.size) (a : Array E) :
    foldFrom input t 0 0 input.config.folds[0]! a =
      (challenges input.config t).levels[0]!.folds.foldl
        (fun a r => foldValues a (width input.config) r) a := by
  have count := CausalStateCausality.challenge_folds_size input.config t ⟨0, hasLevel⟩
  have mapped : (List.range input.config.folds[0]!).map
      (fun j => (challenges input.config t).levels[0]!.folds[j]!) =
      (challenges input.config t).levels[0]!.folds.toList := by
    apply List.ext_getElem
    · simp [count]
    · intro j hj hj'
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      rw [getElem!_pos _ _ (by simpa [count] using hj')]
  unfold foldFrom
  simp only [Nat.zero_add, block, beq_self_eq_true, ↓reduceIte]
  rw [← List.foldl_map, mapped, Array.foldl_toList]

theorem witness_folded_encode (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (t : Tape (config p)) (w : Witness (config p) lanes)
    (q : Fin (blockLength (config p))) :
    (encode ((config p).logN-(config p).folds[0]!) (config p).rates[0]!
      (foldFrom (Input p lanes root claims) t 0 0 (config p).folds[0]!
        (paddedWitness (config p) lanes w)))[q.val]! =
      Concrete.mle (witnessRow (Input p lanes root claims) w q)
        (challenges (config p) t).levels[0]!.folds := by
  rw [foldFrom_initial _ _ (production_config_valid p).2.1]
  have shape : (paddedWitness (config p) lanes w).size =
      2 ^ (challenges (config p) t).levels[0]!.folds.size *
        2 ^ ((config p).logN-(config p).folds[0]!) := by
    rw [CausalStateCausality.challenge_folds_size (config p) t (initialLevel p)]
    simp only [paddedWitness, ArrayLayout.size_tab, ← Nat.pow_add,
      Nat.add_sub_of_le (InitialCandidates.production_initial_facts p).2.1]
  rw [encoded_foldList _ _ _ _ shape]
  congr 1
  rw [CausalStateCausality.challenge_folds_size (config p) t (initialLevel p)]
  unfold column witnessRow
  apply congrArg Array.ofFn
  funext lane
  exact ConcreteCandidates.concreteEncoder_ofFn _ _ _ q

theorem committed_folded_word (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (t : Tape (config p))
    (valid : oracleValid (liftRoot root) (length (config p) 0) lanes = true)
    (laneBound : lanes ≤ 2 ^ (config p).folds[0]!)
    (q : Fin (blockLength (config p))) :
    Concrete.mle (committedRow (Input p lanes root claims) q)
      (challenges (config p) t).levels[0]!.folds =
      QueryBatchSoundness.oldWord ((config p).logN-(config p).folds[0]!) (config p).rates[0]!
        (liftRoot root) true (challenges (config p) t).levels[0]!.folds q := by
  have dims := (InitialCandidates.production_initial_facts p).1
  have qs : q.val < length (config p) 0 := by simpa only [length, dims] using q.isLt
  have live := OracleReplay.oracleValid_row _ _ _ valid q.val qs
  have rs : q.val < root.size := by
    have shape := valid
    simp only [oracleValid, Bool.and_eq_true, beq_iff_eq, liftRoot, Array.size_map] at shape
    exact qs.trans_eq shape.1.symm
  have rootShape : root[q.val]!.size = lanes := by
    simpa [liftRoot, getElem!_pos, rs] using live
  have row : committedRow (Input p lanes root claims) q =
      OracleReplay.ascendingRow true (config p).folds[0]! (liftRoot root)[q.val]! := by
    apply Array.ext
    · simp [committedRow]
    · intro j hj hj'
      have lane : j < laneCount (config p) := by simpa [committedRow] using hj
      have entry := OracleReplay.initial_fullRow (config p) lanes root
        (challenges (config p) t).levels[0]!.folds q rs rootShape ⟨j, lane⟩
      simpa [committedRow, OracleReplay.oracleAt, getElem!_pos, lane] using entry.symm
  rw [row]
  unfold Concrete.mle QueryBatchSoundness.oldWord
  apply OracleReplay.ascendingRow_dot true (config p).folds[0]! _
  · exact live.le.trans laneBound
  · simp [CausalStateCausality.challenge_folds_size (config p) t (initialLevel p)]

#print axioms witness_folded_encode
#print axioms committed_folded_word

end Whir.SupportedCandidateProtocol
