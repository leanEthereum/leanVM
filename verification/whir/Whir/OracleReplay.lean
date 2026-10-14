import Whir.InitialCandidates
import Whir.OperationalRefinement
import Whir.TerminalRefinement

/-! Commitment-only oracle replay. Leaves are arbitrary: only their accepted
physical lengths are used. Initial leaves reverse their live prefix and pad
absent lanes with literal zeros; extension leaves retain their ordinary order. -/
namespace Whir.OracleReplay
open Concrete Protocol ArrayLayout CandidateFolding

/-- Ascending, full-width row; pruning never reverses the absent zero tail. -/
def ascendingRow (base : Bool) (k : Nat) (raw : Array E) : Array E :=
  tab (2^k) fun lane =>
    if lane < raw.size then (if base then raw.reverse else raw)[lane]! else 0

@[simp] theorem ascendingRow_size (base : Bool) (k : Nat) (raw : Array E) :
    (ascendingRow base k raw).size = 2^k := by simp [ascendingRow]

/-- Actual challenge prefix, in chronological order, on an arbitrary row. -/
def rowAt (folds : Array E) (a : Array E) (j : Nat) : Array E :=
  (List.range j).foldl (fun a i => foldLow a folds[i]!) a

@[simp] theorem rowAt_zero (folds a : Array E) : rowAt folds a 0 = a := rfl

@[simp] theorem rowAt_succ (folds a : Array E) (j : Nat) :
    rowAt folds a (j+1) = foldLow (rowAt folds a j) folds[j]! := by
  simp [rowAt, List.range_succ, List.foldl_append]

theorem rowAt_size (folds a : Array E) (k j : Nat)
    (shape : a.size = 2^k) (hj : j ≤ k) :
    (rowAt folds a j).size = 2^(k-j) := by
  induction j with
  | zero => simpa using shape
  | succ j ih =>
    rw [rowAt_succ, size_foldLow, ih (by omega)]
    rw [show k-j = (k-(j+1))+1 by omega, pow_succ,
      Nat.mul_div_left _ (by decide : 0 < 2)]

/-- The matrix at round j; its Fin index states the exact remaining lane count. -/
def oracleAt (base : Bool) (k : Nat) (root : Oracle) (folds : Array E)
    (j : Nat) {N : Nat} : Fin (2^(k-j)) → Fin N → E :=
  fun lane q => (rowAt folds (ascendingRow base k root[q.val]!) j)[lane.val]!

/-- Reindex the old matrix to adjacent pairs, without changing physical indices. -/
def pairedOracle (base : Bool) (k : Nat) (root : Oracle) (folds : Array E)
    (j : Nat) (hj : j < k) {N : Nat} : Fin (2^(k-(j+1))*2) → Fin N → E :=
  fun lane => oracleAt base k root folds j
    ⟨lane.val, by
      have h : 2^(k-j) = 2^(k-(j+1))*2 := by
        rw [show k-j = (k-(j+1))+1 by omega, pow_succ]
      omega⟩

/-- Exact actual-array recurrence, not an honest-codeword assumption. -/
theorem oracleAt_succ (base : Bool) (k : Nat) (root : Oracle) (folds : Array E)
    (j : Nat) (hj : j < k) {N : Nat} :
    oracleAt base k root folds (j+1) (N := N) =
      foldOracle (pairedOracle base k root folds j hj) folds[j]! := by
  funext lane q
  have hs := rowAt_size folds (ascendingRow base k root[q.val]!) k j
    (ascendingRow_size _ _ _) (by omega)
  have hp : 2^(k-j) = 2^(k-(j+1))*2 := by
    rw [show k-j = (k-(j+1))+1 by omega, pow_succ]
  have hl : lane.val < (rowAt folds (ascendingRow base k root[q.val]!) j).size / 2 := by
    rw [hs, hp, Nat.mul_div_left _ (by decide : 0 < 2)]
    exact lane.isLt
  simp [oracleAt, rowAt_succ, foldLow, tab, getElem!_pos, hl,
    foldOracle, pairedOracle, evenLane, oddLane, foldPair]
  linear_combination folds[j]! *
    CharTwo.add_self_eq_zero (rowAt folds (ascendingRow base k root[q.val]!) j)[2*lane.val]!

theorem rowAt_terminal (folds a : Array E) (shape : a.size = 2^folds.size) :
    rowAt folds a folds.size = #[dot a (eqTable folds)] := by
  have mapped : (List.range folds.size).map (fun i => folds[i]!) = folds.toList := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      simp only [getElem!_pos folds i (by simpa using hi')]
  rw [rowAt, ← List.foldl_map, mapped, Array.foldl_toList]
  exact TerminalRefinement.foldLow_terminal a folds shape

/-- Padding has no effect on the verifier's truncated dot product. -/
theorem ascendingRow_dot (base : Bool) (k : Nat) (raw b : Array E)
    (live : raw.size ≤ 2^k) (width : 2^k ≤ b.size) :
    dot (ascendingRow base k raw) b = dot (if base then raw.reverse else raw) b := by
  let f := fun lane => if lane < raw.size then
    (if base then raw.reverse else raw)[lane]! else (0 : E)
  have h := QueryRefinement.dot_tab_zero_tail (2^k) raw.size f b live width
    (by intro i hi _; simp [f, Nat.not_lt.mpr hi])
  have he : tab raw.size f = (if base then raw.reverse else raw) := by
    apply Array.ext
    · cases base <;> simp
    · intro i hi hi'
      have hi0 : i < raw.size := by simpa using hi
      cases base <;> simp [tab, f, hi0, getElem!_pos]
  exact h.trans (congrArg (fun a => dot a b) he)

/-- Literal expression shared with enforced and queryError. -/
def postfoldWord (base : Bool) (root : Oracle) (folds : Array E) (q : Nat) : E :=
  dot (if base then root[q]!.reverse else root[q]!) (eqTable folds)

/-- Every one-lane oracle entry is exactly the actual enforced scalar. -/
theorem oracleAt_terminal (base : Bool) (root : Oracle) (folds : Array E)
    {N : Nat} (q : Fin N) (live : root[q.val]!.size ≤ 2^folds.size)
    (lane : Fin (2^(folds.size-folds.size))) :
    oracleAt base folds.size root folds folds.size lane q =
      postfoldWord base root folds q.val := by
  have hl : lane.val = 0 := by simpa using lane.isLt
  simp only [oracleAt, rowAt_terminal folds _ (ascendingRow_size _ _ _), hl]
  simpa [postfoldWord] using ascendingRow_dot base folds.size root[q.val]! (eqTable folds) live
    (by simp [TerminalRefinement.size_eqTable])

/-- Ordinary next-root leaves are already full ascending rows. -/
theorem ascendingRow_extension (k : Nat) (raw : Array E) (shape : raw.size = 2^k) :
    ascendingRow false k raw = raw := by
  apply Array.ext
  · simp [shape]
  · intro i hi hi'
    simp [ascendingRow, tab, hi', getElem!_pos]

/-- Every candidate has the physical size used by the actual fold ladder. -/
theorem candidate_size (base : Bool) (k n rate j threshold : Nat)
    (root : Oracle) (folds : Array E) (a : Array E)
    (ha : a ∈ arrayCandidates base (concreteEncoder n rate)
      (oracleAt base k root folds j) threshold) :
    a.size = 2^(n+(k-j)) := by
  rw [arrayCandidates_size _ _ _ _ _ ha, ← Nat.pow_add, Nat.add_comm]

/-- Exact paired shape for VerifierState.fold, in either physical layout. -/
theorem candidate_round_shape (base : Bool) (k n rate j threshold : Nat)
    (root : Oracle) (folds : Array E) (hj : j < k) (a : Array E)
    (ha : a ∈ arrayCandidates base (concreteEncoder n rate)
      (pairedOracle base k root folds j hj) threshold) :
    a.size = ((if base then 2^(k-(j+1)) else 2^(k-(j+1))*2^n)*2) *
      CandidateFolding.foldBlock base (2^n) :=
  arrayCandidates_round_shape _ _ _ _ _ ha

/-- The accepted Boolean shape guard supplies each individual leaf's size. -/
theorem oracleValid_row (root : Oracle) (rows width : Nat)
    (valid : oracleValid root rows width = true) (q : Nat) (hq : q < rows) :
    root[q]!.size = width := by
  simp only [oracleValid, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at valid
  have hq' : q < root.size := by omega
  simpa [getElem!_pos root q hq'] using valid.2 q hq'

/-- Entrywise bridge from the commitment-only K list, including pruned lanes. -/
theorem initial_fullRow (c : Config) (lanes : Nat) (root : CausalGame.BaseOracle)
    (folds : Array E) (q : Fin (2^(c.logN-c.folds[0]!+c.rates[0]!)))
    (hq : q.val < root.size) (shape : root[q.val]!.size = lanes)
    (lane : Fin (2^c.folds[0]!)) :
    oracleAt true c.folds[0]! (CausalGame.liftRoot root) folds 0 lane q =
      E.ofK (InitialCandidates.fullRow c lanes root lane q) := by
  have lift : (CausalGame.liftRoot root)[q.val]! = root[q.val]!.map E.ofK := by
    simp [CausalGame.liftRoot, getElem!_pos, hq]
  rw [InitialCandidates.fullRow_reverse c lanes root q shape lane]
  simp only [oracleAt, rowAt_zero, ascendingRow, lift]
  have hl : lane.val < 2^c.folds[0]! := lane.isLt
  by_cases live : lane.val < lanes
  · simp [tab, getElem!_pos, hl, shape, live, ← Array.map_reverse]
  · simp [tab, getElem!_pos, hl, shape, live]

/-- An accepted ordinary next commitment enters the next ladder in row order. -/
theorem extension_root (k rows : Nat) (root : Oracle) (folds : Array E)
    (valid : oracleValid root rows (2^k) = true)
    (q : Fin rows) (lane : Fin (2^k)) :
    oracleAt false k root folds 0 lane q = (root[q.val]!)[lane.val]! := by
  simp only [oracleAt, rowAt_zero]
  rw [ascendingRow_extension k _ (oracleValid_row root rows (2^k) valid q.val q.isLt)]

/-- Authentication suffices for enforced, even when the query vector repeats
indices and the prover chose its rows after seeing the whole vector. -/
theorem enforced_authenticated (base : Bool) (root : Oracle) (folds weights : Array E)
    (qs : Array Nat) (rows : Array (Array E))
    (length : rows.size = qs.size)
    (auth : ∀ j, j < qs.size → rows[j]! = root[qs[j]!]!) :
    enforced rows folds weights base =
      (tab qs.size fun j => weights[j]! * postfoldWord base root folds qs[j]!).foldl
        (· + ·) 0 := by
  dsimp only [enforced, postfoldWord]
  apply congrArg (fun a : Array E => a.foldl (· + ·) 0)
  apply Array.ext
  · simp [length]
  · intro j hj hj'
    have h : j < qs.size := by simpa using hj'
    simp only [tab, Array.getElem_map, List.getElem_toArray, List.getElem_range]
    rw [auth j h]

/-- The matrix dimensions coincide with the verifier's actual remaining n. -/
theorem foldBlock_dimensions (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (s : CheckedState) (n k : Nat) (start : s.n = n+k)
    (folds : cs.folds.size = k) :
    (Protocol.foldBlock block cs p s).n = n := by
  have h := OperationalRefinement.foldBlock_invariant block cs p
    (fun j t => t.n = n+k-j) s (by simpa using start)
    (by intro j t hj ht; simp only [foldStep, ht]; omega)
  simpa [folds] using h

/-- Reindexing the lane type changes neither physical arrays nor membership. -/
theorem arrayCandidates_cast {lanes lanes' width N : Nat} (h : lanes' = lanes)
    (base : Bool) (enc : (Fin width → E) →ₗ[E] (Fin N → E))
    (oracle : Fin lanes → Fin N → E) (threshold : Nat) :
    arrayCandidates base enc (fun lane : Fin lanes' => oracle (Fin.cast h lane)) threshold =
      arrayCandidates base enc oracle threshold := by
  subst lanes'
  rfl

/-- The old list in the adjacent-pair recurrence is the same commitment-fixed
list as at the preceding prefix, not a separately selected candidate set. -/
theorem paired_candidates (base : Bool) (k n rate j threshold : Nat)
    (root : Oracle) (folds : Array E) (hj : j < k) :
    arrayCandidates base (concreteEncoder n rate)
      (pairedOracle base k root folds j hj) threshold =
    arrayCandidates base (concreteEncoder n rate)
      (oracleAt base k root folds j) threshold := by
  have h : 2^(k-(j+1))*2 = 2^(k-j) := by
    rw [show k-j = (k-(j+1))+1 by omega, pow_succ]
  exact arrayCandidates_cast h base (concreteEncoder n rate)
    (oracleAt base k root folds j) threshold

/-- Actual verifier prefix dimensions, independently of every message, claim
and oracle value. This matches candidate_size at the same prefix. -/
theorem foldBlock_prefix_shape (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (s : CheckedState) (n k j : Nat) (hj : j ≤ k)
    (start : s.n = n+k) (weight : s.state.weight.size = 2^(n+k)) :
    let t := runSteps (foldStep block cs p) j 0 s
    t.n = n+(k-j) ∧ t.state.weight.size = 2^(n+(k-j)) := by
  have h := OperationalRefinement.runSteps_invariant (foldStep block cs p)
    (fun i t => t.n = n+(k-i) ∧ t.state.weight.size = 2^(n+(k-i)))
    j 0 s (by simpa using And.intro start weight) ?_
  · simpa using h
  · intro i t _ hi ht
    have hi' : i < k := by omega
    have hexp : n+(k-i) = (n+(k-(i+1)))+1 := by omega
    constructor
    · simp only [foldStep, ht.1]; omega
    · simp only [foldStep, VerifierState.fold, ReplayRefinement.foldValues_eq_lane,
        size_foldLane, ht.2, hexp, pow_succ, Nat.mul_div_left _ (by decide : 0 < 2)]

end Whir.OracleReplay
