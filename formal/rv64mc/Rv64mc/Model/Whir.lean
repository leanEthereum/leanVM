module

public import Rv64mc.Model.RingSwitch
public import Rv64mc.Model.KeccakGkr

/-!
# `whir.rs` as the Rust computes it

Mirrors of `crates/verifier/src/whir.rs`: `whir_queries` and `derive_config`, `ext_row`,
`sample_queries`, `subspace_roots` and `Subspace`, `novel_basis`, `novel_eval`, `FoldRound` and
`fold_row`, `induced_weight`, `GluedWeight` and `GluedClaim`, and `verify_whir`; and, from
`lib.rs`, `read_ood`, `StackWeight` and `verify_stacked_opening`, which feed it. Conventions as in
`Model.KeccakGkr`: an `E` is the statement's, `E::sum` is `sumRust`, `E * K` is `mulKE`, `K`'s
`square` and `inv` are `Model.Field`'s; a `u64` is a `BitVec 64`, a shift by a `usize` masked to
six bits; a pure step that may panic or return `Err` is an `Option`, which the mirror's `TM`
fails on. The mirror may return anything where the Rust panics, and fails only where it fails.

Each pure mirror is proved equal to its counterpart whenever it returns (`_some` lemmas: where
the Rust would panic the mirror fails; `subspaceRootsRust_some`, `SubspaceRust.at_eq` and
`inducedWeightRust_some` also assume fewer than `64` variables, as the shift `K(1 << i)` wraps past
`63`), and returns on the shapes the verifier gives it (`_eq` lemmas: `SubspaceRust.new_eq`,
`foldRowRust_eq`, `novelBasisRust_eq`, `novelEvalRust_eq`, `inducedWeightRust_eq`,
`finalChecksRust_eq`, `batchedRust_eq`). `derive_config` is `Whir.ladder` on the whole parameter
window (`deriveConfigRust_eq`, by evaluation). `Comp` lemmas state the converse of a simulation:
the mirror returns wherever the statement runs (`Comp.foldRound`, `Comp.readOod`,
`Comp.sampleQueries`).

`verify_whir` reads commitments as it goes, and `merkle` opens the root a level holds; the
statement indexes the roots it read. Its simulation (`SimRoots.verifyWhir`) is therefore stated
over the transcripts whose ghost roots are the stack's root only (what `verify_execution` has
read when it opens the stack), with `SimRoots`, `SimR` restricted to the transcripts whose ghost
roots satisfy a predicate. Every other step reads no commitment (`NoCommit`), so keeps the
roots.
-/

namespace Rv64mc.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `K`'s methods -/

/-- `K::square` of a word. -/
def kSquareK (a : K) : K := BF64.ofBitVec (kSquare a.toBitVec)

theorem kSquareK_eq (a : K) : kSquareK a = a * a := by
  rw [kSquareK, kSquare_eq]; rfl

/-- `K::inv` of a word. -/
def kInvK (a : K) : K := BF64.ofBitVec (kInv a.toBitVec)

theorem kInvK_eq (a : K) : kInvK a = a⁻¹ := by
  rw [kInvK, kInv_eq]; rfl

/-- `K(1 << i)`, the shift masked. -/
def kShl (i : ℕ) : K := BF64.ofBitVec (1#64 <<< (i % 64))

theorem one_shl_eq {i : ℕ} (h : i < 64) : 1#64 <<< (i % 64) = BitVec.ofNat 64 (2 ^ i) := by
  apply BitVec.eq_of_toNat_eq
  rw [Nat.mod_eq_of_lt h, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  simp

theorem kShl_eq {i : ℕ} (h : i < 64) : kShl i = K.ofBits (2 ^ i) := by
  rw [kShl, one_shl_eq h]; rfl

/-! ## `whir_queries` and `derive_config` -/

/-- `WHIR_QUERIES`. -/
def whirQueriesTable : List (List (List ℕ)) := [
  [[230,60,42], [225,58,38], [222,57,35], [220,56,34], [219,55,33,27], [218,55,32,25],
   [218,55,32,24], [218,55,32,23], [218,55,32,23,20], [218,55,32,23,19], [218,55,32,23,18],
   [218,55,32,23,18], [218,55,32,23,18,16], [218,55,32,23,18,15], [218,55,32,23,18,15]],
  [[112,47,35], [111,46,32], [110,45,31], [110,45,29], [109,44,29,24], [109,44,28,23],
   [109,44,28,22], [109,44,28,21], [109,44,28,21,18], [109,44,28,21,17], [109,44,28,21,17],
   [109,44,28,21,17], [109,44,28,21,17,15], [109,44,28,21,17,15], [109,44,28,21,17,15]],
  [[74,39,30], [74,38,28], [73,37,27], [73,37,26], [73,37,25,22], [73,37,25,20], [73,37,25,20],
   [73,37,25,19], [73,37,25,19,17], [73,37,25,19,16], [73,37,25,19,16], [73,37,25,19,16],
   [73,37,25,19,16,15], [73,37,25,19,16,14], [73,37,25,19,16,15]],
  [[56,33,27], [55,32,25], [55,32,24], [55,32,23], [55,32,23,20], [55,32,23,19], [55,32,23,18],
   [55,32,23,18], [55,32,23,18,16], [55,32,23,18,15], [55,32,23,18,15], [55,32,23,18,15],
   [55,32,23,18,15,14], [55,32,23,18,16,14], [55,32,23,18,16,14]]]

theorem whirQueriesTable_eq : whirQueriesTable = Whir.queryTable := rfl

/-- `usize::checked_sub`. -/
def checkedSub (a b : ℕ) : Option ℕ := if b ≤ a then some (a - b) else none

/-- `whir_queries(log_n, log_inv_rate)`: the row of the rate, then the entry of the size. -/
def whirQueriesRust (logN logInvRate : ℕ) : Option (List ℕ) := do
  let row ← whirQueriesTable[← checkedSub logInvRate 1]?
  row[← checkedSub logN 16]?

/-- `WhirConfig`. -/
structure WhirConfigRust where
  /-- `log_inv_rates`. -/
  logInvRates : List ℕ
  /-- `folds`. -/
  folds : List ℕ
  /-- `queries`. -/
  queries : List ℕ
  deriving DecidableEq

/-- `derive_config`'s loop, `while remaining > RESIDUAL_MAX_LOG`: the rate, from the last rate and
fold and the pending reduction, then the fold. `fuel` bounds it: every iteration folds four. -/
def configLoop : (fuel remaining : ℕ) → List ℕ → List ℕ → List ℕ × List ℕ
  | 0, _, folds, rates => (folds, rates)
  | fuel + 1, remaining, folds, rates =>
    if 5 < remaining then
      let reduction := if folds.length = 1 then 3 else 1
      let rates := rates ++ [rates.getLastD 0 + folds.getLastD 0 - reduction]
      let fold := min 4 remaining
      configLoop fuel (remaining - fold) (folds ++ [fold]) rates
    else (folds, rates)

/-- `derive_config(log_n, log_inv_rate)`: the tabulated counts (`WhirShape`), the ladder from
`folds = [6]`, `log_inv_rates = [log_inv_rate]`, `remaining = log_n - 6`, then one count per
level (`QueryCountLadder`). -/
def deriveConfigRust (logN logInvRate : ℕ) : Option WhirConfigRust := do
  let queries ← whirQueriesRust logN logInvRate
  let (folds, rates) := configLoop (logN - 6) (logN - 6) [6] [logInvRate]
  if queries.length = folds.length then some ⟨rates, folds, queries⟩ else none

/-- The Rust's configuration of a ladder. -/
def configOf (ls : List Whir.Level) : WhirConfigRust :=
  ⟨ls.map (·.logInvRate), ls.map (·.fold), ls.map (·.queries)⟩

theorem whirQueriesRust_none {logN logInvRate : ℕ} (h : ¬ Whir.Admissible logN logInvRate) :
    whirQueriesRust logN logInvRate = none := by
  unfold Whir.Admissible Whir.minLogStack Whir.maxLogStack at h
  unfold whirQueriesRust checkedSub
  by_cases h1 : 1 ≤ logInvRate
  · by_cases h2 : logInvRate ≤ 4
    · by_cases h3 : 16 ≤ logN
      · have h4 : 30 < logN := by omega
        obtain ⟨r, rfl⟩ : ∃ r, logInvRate = r + 1 := ⟨logInvRate - 1, by omega⟩
        simp only [ite_eq_left h1, ite_eq_left h3, Option.bind_eq_bind, Option.bind_some,
          Nat.add_sub_cancel]
        have hr : r ≤ 3 := by omega
        interval_cases r <;> simp [whirQueriesTable] <;> omega
      · simp [h1, h3, Option.bind_eq_bind]
    · simp only [h1, ite_true, Option.bind_eq_bind, Option.bind_some]
      rw [List.getElem?_eq_none (by simp [whirQueriesTable]; omega)]
      rfl
  · simp [h1, Option.bind_eq_bind]

private def deriveConfigOk (logN logInvRate : ℕ) : Bool :=
  deriveConfigRust logN logInvRate == (Whir.ladder logN logInvRate).map configOf

private theorem deriveConfigOk_window : ∀ logN < 31, ∀ r < 5, deriveConfigOk logN r = true := by
  decide +kernel

/-- **`derive_config` is `Whir.ladder`**, as the Rust's three vectors. -/
theorem deriveConfigRust_eq (logN logInvRate : ℕ) :
    deriveConfigRust logN logInvRate = (Whir.ladder logN logInvRate).map configOf := by
  by_cases h : Whir.Admissible logN logInvRate
  · have h' := h
    unfold Whir.Admissible Whir.maxLogStack at h'
    have := deriveConfigOk_window logN (by omega) logInvRate (by omega)
    simpa [deriveConfigOk] using this
  · rw [deriveConfigRust, whirQueriesRust_none h, Whir.ladder, ite_eq_right h]
    rfl

/-- What every ladder satisfies: the size in the window, level 0 folding six, every level a rate in
`1 .. 33` and one to six folds, and no more folds than variables. -/
def LadderFacts (logN : ℕ) (ls : List Whir.Level) : Prop :=
  logN ≤ 30 ∧ ls ≠ [] ∧ (ls.head?.map (·.fold)) = some 6 ∧
    (∀ l ∈ ls, 1 ≤ l.logInvRate ∧ l.logInvRate < 34 ∧ 1 ≤ l.fold ∧ l.fold ≤ 6) ∧
    (ls.map (·.fold)).sum ≤ logN

private def ladderFactsB (logN r : ℕ) : Bool :=
  match Whir.ladder logN r with
  | none => true
  | some ls => decide (logN ≤ 30 ∧ ls ≠ [] ∧ (ls.head?.map (·.fold)) = some 6) &&
      (ls.all fun l ↦ decide (1 ≤ l.logInvRate ∧ l.logInvRate < 34 ∧ 1 ≤ l.fold ∧ l.fold ≤ 6)) &&
      decide ((ls.map (·.fold)).sum ≤ logN)

private theorem ladderFactsB_window : ∀ logN < 31, ∀ r < 5, ladderFactsB logN r = true := by
  decide +kernel

theorem ladder_facts {logN r : ℕ} {ls : List Whir.Level} (h : Whir.ladder logN r = some ls) :
    LadderFacts logN ls := by
  have hA : Whir.Admissible logN r := by
    by_contra hA
    rw [Whir.ladder, ite_eq_right hA] at h
    cases h
  have hA' := hA
  unfold Whir.Admissible Whir.maxLogStack at hA'
  have hb := ladderFactsB_window logN (by omega) r (by omega)
  rw [ladderFactsB, h] at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hb
  exact ⟨hb.1.1.1, hb.1.1.2.1, hb.1.1.2.2, hb.1.2, hb.2⟩

/-! ## `ext_row`, `sample_queries` -/

/-- `ext_row(words)`: the full chunks of two words (`as_chunks`), each `E::new(c0, c1)`. -/
def extRowRust : List (BitVec 64) → List E
  | c0 :: c1 :: rest => ofLimbsW (c0, c1) :: extRowRust rest
  | _ => []

theorem extRowRust_eq : ∀ row : List K, extRowRust (row.map BF64.toBitVec) = extRow row
  | c0 :: c1 :: rest => by
    rw [List.map_cons, List.map_cons, extRowRust, extRowRust_eq rest, extRow]; rfl
  | [] => rfl
  | [_] => rfl

/-- `sample_queries`' inner loop, `while shift + depth <= 128 && result.len() < count`: push
`(word >> shift) as u64 & (block_length - 1)`. `fuel` bounds it: every iteration pushes. -/
def queryChunks (word : BitVec 128) (blockLength : BitVec 64) (depth count : ℕ) :
    ℕ → ℕ → List (BitVec 64) → List (BitVec 64)
  | 0, _, result => result
  | fuel + 1, shift, result =>
    if shift + depth ≤ 128 ∧ result.length < count then
      queryChunks word blockLength depth count fuel (shift + depth)
        (result ++ [(word >>> (shift % 128)).setWidth 64 &&& (blockLength - 1#64)])
    else result

/-- The 128-bit integer of a sample's limbs: `c0 as u128 | (c1 as u128) << 64`. -/
def sampleWord (e : E) : BitVec 128 := (limbs e).1.setWidth 128 ||| (limbs e).2.setWidth 128 <<< 64

/-- `sample_queries`' outer loop, `while result.len() < count`. `fuel` bounds it. -/
def sampleQueriesLoop (blockLength : BitVec 64) (depth count : ℕ) :
    ℕ → List (BitVec 64) → TM (List (BitVec 64))
  | 0, result => Pure.pure result
  | fuel + 1, result =>
    if result.length < count then do
      let sample ← TM.sample
      sampleQueriesLoop blockLength depth count fuel
        (queryChunks (sampleWord sample) blockLength depth count count 0 result)
    else Pure.pure result

/-- `sample_queries(transcript, block_length, count)`: `log2_strict(block_length)?`, then the
loop from an empty result. -/
def sampleQueriesRust (blockLength : BitVec 64) (count : ℕ) : TM (List (BitVec 64)) := do
  let depth ← TM.ofOption (log2StrictRust blockLength)
  sampleQueriesLoop blockLength depth count count []

/-! ## `subspace_roots`, `Subspace`, `novel_basis`, `novel_eval` -/

/-- `subspace_roots`' loop: per iteration the layer square-and-shifted by the last root, then
`layer.remove(0)` pushed (a panic on an empty layer). -/
def subspaceRootsLoop : ℕ → List K → List K → Option (List K)
  | 0, roots, _ => some roots
  | n + 1, roots, layer =>
    let root := roots.getLastD 0
    match layer.map fun value ↦ kSquareK value + root * value with
    | [] => none
    | first :: rest => subspaceRootsLoop n (roots ++ [first]) rest

/-- `subspace_roots(log_n)`: from `[K(1)]` and the layer `(1..=log_n).map(|i| K(1 << i))`. -/
def subspaceRootsRust (logN : ℕ) : Option (List K) :=
  subspaceRootsLoop logN [1] ((List.range' 1 logN).map kShl)

/-- `Subspace { roots, inverses }`. -/
structure SubspaceRust where
  /-- `roots`. -/
  roots : List K
  /-- `inverses`. -/
  inverses : List K

/-- `Subspace::new(mu)`. -/
def SubspaceRust.new (mu : ℕ) : Option SubspaceRust := do
  let roots ← subspaceRootsRust mu
  pure ⟨roots, roots.map kInvK⟩

/-- `Subspace::at`'s loop over `roots.iter().zip(&inverses)`: push `basis * inverse`, then
`basis = basis.square() + root * basis`. -/
def subspaceAtLoop : List K → List K → K → List K
  | root :: roots, inverse :: inverses, basis =>
    basis * inverse :: subspaceAtLoop roots inverses (kSquareK basis + root * basis)
  | _, _, _ => []

/-- `Subspace::at(x)`. -/
def SubspaceRust.at (s : SubspaceRust) (x : K) : List K := subspaceAtLoop s.roots s.inverses x

/-- `novel_basis`'s loop: `if basis.len() >= count { break }`, else extend by the products. -/
def novelBasisLoop (count : ℕ) : List K → List K → List K
  | [], basis => basis
  | value :: what, basis =>
    if count ≤ basis.length then basis
    else novelBasisLoop count what (basis ++ basis.map (· * value))

/-- `novel_basis(what, count)`: the loop from `[K(1)]`, `assert!(basis.len() >= count)`, then
`truncate(count)`. -/
def novelBasisRust (what : List K) (count : ℕ) : Option (List K) :=
  let basis := novelBasisLoop count what [1]
  if count ≤ basis.length then some (basis.take count) else none

/-- `novel_eval(coefficients, what)`: `E::sum` of `p * b` over the coefficients and the basis. -/
def novelEvalRust (coefficients : List E) (what : List K) : Option E := do
  let basis ← novelBasisRust what coefficients.length
  pure (sumRust ((coefficients.zip basis).map fun pb ↦ mulKE pb.1 pb.2))

/-! ## `fold_row`, `induced_weight` -/

/-- One iteration of `fold_row`'s inner loop: `values[i] = values[2i + 1] + affine * values[2i]`. -/
def foldRowStep (affine : E) (values : List E) (i : ℕ) : List E :=
  values.set i (values.getD (2 * i + 1) 0 + affine * values.getD (2 * i) 0)

/-- One round of `fold_row`: `affine = alpha + beta * x`, the inner loop over `0..half`, then
`truncate(half)`. -/
def foldRowRound (x : K) (values : List E) (round : FoldRound) : List E :=
  let affine := round.alpha + mulKE round.beta x
  let half := values.length / 2
  ((List.range half).foldl (foldRowStep affine) values).take half

/-- `fold_row(values, x, rounds)`: the rounds, then `assert_eq!(values.len(), 1)` and
`values[0]`. -/
def foldRowRust (values : List E) (x : K) (rounds : List FoldRound) : Option E :=
  match rounds.foldl (foldRowRound x) values with
  | [value] => some value
  | _ => none

/-- `induced_weight(message_log, queries, query_weights, point)`: `require(point.len() ==
message_log)`, `Subspace::new`, then per `(weight, query)` the product over `point.zip(&what)` of
`ONE + challenge * (K(1) + value)` from `weight`, summed from `ZERO`. -/
def inducedWeightRust (messageLog : ℕ) (queries : List (BitVec 64)) (queryWeights point : List E) :
    Option E := do
  if point.length = messageLog then
    let subspace ← SubspaceRust.new messageLog
    pure ((queryWeights.zip queries).foldl (fun total wq ↦
      let what := subspace.at (BF64.ofBitVec wq.2)
      total + (point.zip what).foldl (fun product cv ↦
        product * (1 + mulKE cv.1 (1 + cv.2))) wq.1) 0)
  else none

/-! ## Their equalities with the statement -/

section Helpers

private theorem subspaceRootsLoop_some : ∀ (n : ℕ) (roots layer : List K) (out : List K),
    subspaceRootsLoop n roots layer = some out →
    out = roots ++ subspaceRootsAux n (roots.getLastD 0) layer
  | 0, roots, layer, out, h => by
    simp only [subspaceRootsLoop, Option.some.injEq] at h
    simp [h, subspaceRootsAux]
  | n + 1, roots, layer, out, h => by
    simp only [subspaceRootsLoop, kSquareK_eq] at h
    rw [subspaceRootsAux]
    split at h
    · cases h
    · rename_i first rest hfr
      rw [hfr, subspaceRootsLoop_some n _ _ out h, List.getLastD_concat, List.append_assoc]
      rfl

private theorem range'_map_kShl {n : ℕ} (hn : n < 64) :
    (List.range' 1 n).map kShl = (List.range n).map fun i ↦ K.ofBits (2 ^ (i + 1)) := by
  rw [List.range'_eq_map_range, List.map_map]
  refine List.map_congr_left fun i hi ↦ ?_
  have := List.mem_range.1 hi
  simp only [Function.comp_apply]
  rw [kShl_eq (by omega), Nat.add_comm]

end Helpers

/-- **`subspace_roots` is `subspaceRoots`** whenever it returns, for `log_n < 64`. -/
theorem subspaceRootsRust_some {logN : ℕ} (hn : logN < 64) {roots : List K}
    (h : subspaceRootsRust logN = some roots) : roots = subspaceRoots logN := by
  rw [subspaceRootsRust, range'_map_kShl hn] at h
  rw [subspaceRootsLoop_some _ _ _ _ h, subspaceRoots]
  rfl

private theorem subspaceAtLoop_eq : ∀ (roots : List K) (x : K),
    subspaceAtLoop roots (roots.map kInvK) x = subspaceAtAux (roots.map fun r ↦ (r, r⁻¹)) x
  | [], _ => rfl
  | r :: rs, x => by
    rw [List.map_cons, List.map_cons, subspaceAtLoop, subspaceAtAux, subspaceAtLoop_eq rs,
      kSquareK_eq, kInvK_eq]

/-- **`Subspace::new(mu).at(x)` is `subspaceAt`** whenever `Subspace::new` returns. -/
theorem SubspaceRust.at_eq {mu : ℕ} (hmu : mu < 64) {s : SubspaceRust}
    (h : SubspaceRust.new mu = some s) (x : K) : s.at x = subspaceAt mu x := by
  unfold SubspaceRust.new at h
  cases hr : subspaceRootsRust mu with
  | none => rw [hr] at h; cases h
  | some roots =>
    rw [hr] at h
    cases h
    rw [SubspaceRust.at, subspaceAtLoop_eq, subspaceAt, subspaceRootsRust_some hmu hr]

private theorem novelBasisLoop_stuck (count : ℕ) : ∀ (what basis : List K),
    count ≤ basis.length →
    what.foldl (fun basis value ↦
      if count ≤ basis.length then basis else basis ++ basis.map (· * value)) basis = basis
  | [], _, _ => rfl
  | v :: vs, b, h => by rw [List.foldl_cons, ite_eq_left h, novelBasisLoop_stuck count vs b h]

private theorem novelBasisLoop_eq (count : ℕ) : ∀ (what basis : List K),
    novelBasisLoop count what basis = what.foldl (fun basis value ↦
      if count ≤ basis.length then basis else basis ++ basis.map (· * value)) basis
  | [], _ => rfl
  | v :: vs, b => by
    rw [novelBasisLoop, List.foldl_cons]
    split_ifs with h
    · rw [novelBasisLoop_stuck count vs b h]
    · exact novelBasisLoop_eq count vs _

/-- **`novel_basis` is `novelBasis`** whenever its assertion holds. -/
theorem novelBasisRust_some {what : List K} {count : ℕ} {basis : List K}
    (h : novelBasisRust what count = some basis) : basis = novelBasis what count := by
  simp only [novelBasisRust] at h
  split_ifs at h
  cases h
  rw [novelBasis, novelBasisLoop_eq]

/-- **`novel_eval` is `novelEval`** whenever it returns. -/
theorem novelEvalRust_some {coefficients : List E} {what : List K} {v : E}
    (h : novelEvalRust coefficients what = some v) : v = novelEval coefficients what := by
  simp only [novelEvalRust, Option.bind_eq_bind, Option.pure_def] at h
  cases hb : novelBasisRust what coefficients.length with
  | none => rw [hb] at h; cases h
  | some basis =>
    rw [hb] at h
    simp only [Option.bind_some, Option.some.injEq] at h
    rw [← h, novelEval, ← novelBasisRust_some hb, sumRust_eq, ← List.map_uncurry_zip_eq_zipWith]
    simp only [mulKE_eq]
    rfl

private theorem foldRowStep_loop (affine : E) (A : List E) : ∀ n, 2 * n ≤ A.length →
    ((List.range n).foldl (foldRowStep affine) A).length = A.length ∧
      ∀ j, ((List.range n).foldl (foldRowStep affine) A)[j]? =
        if j < n then some (A.getD (2 * j + 1) 0 + affine * A.getD (2 * j) 0) else A[j]?
  | 0, _ => ⟨rfl, fun j ↦ by simp⟩
  | n + 1, h => by
    obtain ⟨hl, hg⟩ := foldRowStep_loop affine A n (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, foldRowStep]
    refine ⟨by rw [List.length_set, hl], fun j ↦ ?_⟩
    have e1 : ((List.range n).foldl (foldRowStep affine) A).getD (2 * n + 1) 0 =
        A.getD (2 * n + 1) 0 := by
      rw [List.getD_eq_getElem?_getD, hg, ite_eq_right (by omega), ← List.getD_eq_getElem?_getD]
    have e2 : ((List.range n).foldl (foldRowStep affine) A).getD (2 * n) 0 = A.getD (2 * n) 0 := by
      rw [List.getD_eq_getElem?_getD, hg, ite_eq_right (by omega), ← List.getD_eq_getElem?_getD]
    rw [e1, e2, List.getElem?_set]
    by_cases hj : n = j
    · subst hj
      rw [ite_eq_left rfl, hl, ite_eq_left (by omega), ite_eq_left (by omega)]
    · rw [ite_eq_right hj, hg]
      by_cases hjn : j < n
      · rw [ite_eq_left hjn, ite_eq_left (by omega)]
      · rw [ite_eq_right hjn, ite_eq_right (by omega)]

private theorem foldLanes_eq (x : K) (round : FoldRound) : ∀ (A : List E),
    foldLanes x round A = (List.range (A.length / 2)).map fun i ↦
      A.getD (2 * i + 1) 0 + (round.alpha + round.beta * ofK x) * A.getD (2 * i) 0
  | [] => rfl
  | [_] => by simp [foldLanes]
  | f :: g :: rest => by
    rw [foldLanes, foldLanes_eq x round rest]
    simp only [List.length_cons, show (rest.length + 1 + 1) / 2 = rest.length / 2 + 1 by omega,
      List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1

private theorem foldRowRound_eq (x : K) (values : List E) (round : FoldRound) :
    foldRowRound x values round = foldLanes x round values := by
  obtain ⟨hl, hg⟩ := foldRowStep_loop (round.alpha + mulKE round.beta x) values
    (values.length / 2) (by omega)
  rw [foldRowRound, foldLanes_eq]
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take, List.getElem?_map]
  by_cases hj : j < values.length / 2
  · rw [ite_eq_left hj, hg, ite_eq_left hj, List.getElem?_range hj, mulKE_eq]; rfl
  · rw [ite_eq_right hj, List.getElem?_eq_none (by simp; omega)]; rfl

/-- **`fold_row` is `foldRow`** whenever its assertion holds. -/
theorem foldRowRust_some {values : List E} {x : K} {rounds : List FoldRound} {v : E}
    (h : foldRowRust values x rounds = some v) : v = foldRow values x rounds := by
  have e : rounds.foldl (foldRowRound x) values =
      rounds.foldl (fun values round ↦ foldLanes x round values) values :=
    List.foldl_ext _ _ _ fun a b _ ↦ foldRowRound_eq x a b
  unfold foldRowRust at h
  rw [foldRow, ← e]
  split at h
  · rename_i value hv
    cases h
    rw [hv]
    rfl
  · cases h

/-- **`induced_weight` is `inducedWeight`** whenever it returns, for `message_log < 64`. -/
theorem inducedWeightRust_some {messageLog : ℕ} (hml : messageLog < 64) {queries : List (BitVec 64)}
    {queryWeights point : List E} {v : E}
    (h : inducedWeightRust messageLog queries queryWeights point = some v) :
    v = inducedWeight messageLog (queries.map BitVec.toNat) queryWeights point := by
  unfold inducedWeightRust at h
  split_ifs at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  cases hs : SubspaceRust.new messageLog with
  | none => rw [hs] at h; cases h
  | some s =>
    rw [hs] at h
    simp only [Option.bind_some, Option.some.injEq] at h
    rw [← h, inducedWeight, List.zip_map_right, List.foldl_map]
    refine List.foldl_ext _ _ _ fun total wq _ ↦ ?_
    have hq : K.ofBits wq.2.toNat = BF64.ofBitVec wq.2 := by simp [K.ofBits]
    simp only [Prod.map, id, hq, SubspaceRust.at_eq hml hs, mulKE_eq]

/-! ## Where the pure mirrors return -/

section Success

private theorem eq_some_of {α : Type} {o : Option α} {a : α} (hs : o.isSome)
    (h : ∀ v, o = some v → v = a) : o = some a := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
  rw [hv, h v hv]

private theorem subspaceRootsLoop_isSome : ∀ (n : ℕ) (roots layer : List K), n ≤ layer.length →
    (subspaceRootsLoop n roots layer).isSome
  | 0, _, _, _ => rfl
  | n + 1, roots, layer, h => by
    simp only [subspaceRootsLoop]
    split
    · rename_i hm
      rw [List.map_eq_nil_iff] at hm
      subst hm
      simp at h
    · rename_i first rest hm
      have := congrArg List.length hm
      simp only [List.length_map, List.length_cons] at this
      exact subspaceRootsLoop_isSome n _ _ (by omega)

/-- **`Subspace::new(mu)` returns** the statement's roots and their inverses, for `mu < 64`. -/
theorem SubspaceRust.new_eq {mu : ℕ} (hmu : mu < 64) :
    SubspaceRust.new mu = some ⟨subspaceRoots mu, (subspaceRoots mu).map kInvK⟩ := by
  have hs : (subspaceRootsRust mu).isSome :=
    subspaceRootsLoop_isSome mu _ _ (by simp)
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hs
  unfold SubspaceRust.new
  rw [hr, ← subspaceRootsRust_some hmu hr]
  rfl

private theorem subspaceRootsAux_length : ∀ (n : ℕ) (last : K) (layer : List K),
    n ≤ layer.length → (subspaceRootsAux n last layer).length = n
  | 0, _, _, _ => rfl
  | n + 1, last, layer, h => by
    rw [subspaceRootsAux]
    split
    · rename_i hm
      rw [List.map_eq_nil_iff] at hm
      subst hm
      simp at h
    · rename_i first rest hm
      have := congrArg List.length hm
      simp only [List.length_map, List.length_cons] at this
      rw [List.length_cons, subspaceRootsAux_length n _ _ (by omega)]

private theorem subspaceAtAux_length : ∀ (pairs : List (K × K)) (x : K),
    (subspaceAtAux pairs x).length = pairs.length
  | [], _ => rfl
  | _ :: ps, x => by rw [subspaceAtAux, List.length_cons, subspaceAtAux_length ps, List.length_cons]

theorem subspaceAt_length (mu : ℕ) (x : K) : (subspaceAt mu x).length = mu + 1 := by
  rw [subspaceAt, subspaceAtAux_length, List.length_map, subspaceRoots, List.length_cons,
    subspaceRootsAux_length _ _ _ (by simp)]

private theorem foldLanes_length (x : K) (round : FoldRound) (A : List E) :
    (foldLanes x round A).length = A.length / 2 := by
  rw [foldLanes_eq]; simp

/-- **`fold_row` returns** on `2^r` lanes and `r` rounds. -/
theorem foldRowRust_eq {values : List E} {x : K} {rounds : List FoldRound}
    (h : values.length = 2 ^ rounds.length) :
    foldRowRust values x rounds = some (foldRow values x rounds) := by
  have hl : ∀ (rs : List FoldRound) (vs : List E), vs.length = 2 ^ rs.length →
      (rs.foldl (foldRowRound x) vs).length = 1 := by
    intro rs
    induction rs with
    | nil => intro vs h; simpa using h
    | cons r rs ih =>
      intro vs h
      rw [List.foldl_cons]
      refine ih _ ?_
      rw [foldRowRound_eq, foldLanes_length, h, List.length_cons, pow_succ, Nat.mul_div_cancel _
        (by norm_num)]
  obtain ⟨v, hv⟩ := List.length_eq_one_iff.1 (hl rounds values h)
  refine eq_some_of ?_ fun w hw ↦ foldRowRust_some hw
  simp [foldRowRust, hv]

private theorem novelBasisLoop_length (count : ℕ) : ∀ (what basis : List K), 1 ≤ basis.length →
    min count (basis.length * 2 ^ what.length) ≤ (novelBasisLoop count what basis).length
  | [], b, _ => by simp [novelBasisLoop]
  | v :: vs, b, hb => by
    rw [novelBasisLoop]
    split_ifs with h
    · exact le_trans (min_le_left _ _) h
    · have := novelBasisLoop_length count vs (b ++ b.map (· * v)) (by simp; omega)
      simp only [List.length_append, List.length_map, List.length_cons] at this ⊢
      convert this using 2
      ring

/-- **`novel_basis` returns** on at most `2^|what|` elements. -/
theorem novelBasisRust_eq {what : List K} {count : ℕ} (h : count ≤ 2 ^ what.length) :
    novelBasisRust what count = some (novelBasis what count) := by
  have hl := novelBasisLoop_length count what [1] (by simp)
  simp only [List.length_singleton, one_mul, min_eq_left h] at hl
  refine eq_some_of ?_ fun w hw ↦ novelBasisRust_some hw
  simp [novelBasisRust, hl]

/-- **`novel_eval` returns** on at most `2^|what|` coefficients. -/
theorem novelEvalRust_eq {coefficients : List E} {what : List K}
    (h : coefficients.length ≤ 2 ^ what.length) :
    novelEvalRust coefficients what = some (novelEval coefficients what) := by
  refine eq_some_of ?_ fun w hw ↦ novelEvalRust_some hw
  simp [novelEvalRust, novelBasisRust_eq h]

/-- **`induced_weight` returns** on a point of `message_log < 64` coordinates. -/
theorem inducedWeightRust_eq {messageLog : ℕ} (hml : messageLog < 64) {queries : List (BitVec 64)}
    {queryWeights point : List E} (h : point.length = messageLog) :
    inducedWeightRust messageLog queries queryWeights point =
      some (inducedWeight messageLog (queries.map BitVec.toNat) queryWeights point) := by
  refine eq_some_of ?_ fun w hw ↦ inducedWeightRust_some hml hw
  simp [inducedWeightRust, h, SubspaceRust.new_eq hml]

end Success

/-! ## `GluedWeight`, `GluedClaim`, the level's pure loops -/

/-- `GluedWeight`. -/
inductive GluedWeightRust where
  /-- `Ood(point)`. -/
  | ood (point : List E)
  /-- `Queries { message_log, queries, query_weights }`. -/
  | queries (messageLog : ℕ) (queries : List (BitVec 64)) (queryWeights : List E)

/-- `GluedWeight::evaluate(x)`. -/
def GluedWeightRust.evaluate : GluedWeightRust → List E → Option E
  | .ood point, x => eqEvalRust point x
  | .queries ml qs qw, x => inducedWeightRust ml qs qw x

/-- `GluedClaim`. -/
structure GluedClaimRust where
  /-- `scalar`. -/
  scalar : E
  /-- `fold_start`. -/
  foldStart : ℕ
  /-- `weight`. -/
  weight : GluedWeightRust

/-- `lanes_of`: level 0's leaf words reversed, each `E::from`; a deeper level's by `ext_row`. -/
def lanesOfRust (level : ℕ) (row : List (BitVec 64)) : List E :=
  if level = 0 then row.reverse.map fun word ↦ ofK (BF64.ofBitVec word) else extRowRust row

/-- The final level's checks (`if transcript.checked()`): per `(query, row)`, `require(fold_row(..)
== novel_eval(&folded, &subspace.at(x)))`. -/
def finalChecksRust (subspace : SubspaceRust) (lanesOf : List (BitVec 64) → List E)
    (rounds : List FoldRound) (folded : List E) (queries : List (BitVec 64))
    (words : List (List (BitVec 64))) : Option Unit :=
  (queries.zip words).forM fun qr ↦ do
    let x := BF64.ofBitVec qr.1
    let value ← foldRowRust (lanesOf qr.2) x rounds
    let expected ← novelEvalRust folded (subspace.at x)
    if value = expected then pure () else none

/-- One query of a non-final level: `correction = novel_eval(&high, &what) * what[mu]`, then
`batched += query_weight * (fold_row(..) + correction)`. -/
def batchedStep (subspace : SubspaceRust) (mu : ℕ) (lanesOf : List (BitVec 64) → List E)
    (rounds : List FoldRound) (high : List E) (batched : E)
    (qrw : (BitVec 64 × List (BitVec 64)) × E) : Option E := do
  let x := BF64.ofBitVec qrw.1.1
  let what := subspace.at x
  let correction ← (novelEvalRust high what).map (mulKE · (what.getD mu 0))
  let folded ← foldRowRust (lanesOf qrw.1.2) x rounds
  pure (batched + qrw.2 * (folded + correction))

/-- A non-final level's batched queries, from `ZERO`. -/
def batchedRust (subspace : SubspaceRust) (mu : ℕ) (lanesOf : List (BitVec 64) → List E)
    (rounds : List FoldRound) (high : List E) (queries : List (BitVec 64))
    (words : List (List (BitVec 64))) (queryWeights : List E) : Option E :=
  ((queries.zip words).zip queryWeights).foldlM (batchedStep subspace mu lanesOf rounds high) 0

/-- The terminal weight: `evaluate_basis` at the point rotated by the lane folds, then `weight +=
scalar * weight.evaluate(&point[fold_start..])?` per glued claim. -/
def terminalWeightRust (basis : List E → Option E) (laneFolds : ℕ) (glued : List GluedClaimRust)
    (point : List E) : Option E := do
  let weight ← basis (point.drop laneFolds ++ point.take laneFolds)
  glued.foldlM (fun weight g ↦ do
    let value ← g.weight.evaluate (point.drop g.foldStart)
    pure (weight + g.scalar * value)) weight

/-! ## The level loop -/

/-- One fold round: `next_scalars(4)?` (`u0, w, c0, c1`), `grind_check(FOLD_GRINDING_BITS)?`,
`alpha`, `beta`, and the claim folded. -/
def foldRoundRust (claim : E) : TM (E × FoldRound) := do
  let table ← TM.nextScalars 4
  let u0 := table.getD 0 0
  let w := table.getD 1 0
  let c0 := table.getD 2 0
  let c1 := table.getD 3 0
  TM.grindCheck 7
  let alpha ← TM.sample
  let beta ← TM.sample
  Pure.pure (u0 + beta * c0 + alpha * (u0 + claim + alpha * w + beta * (c0 + c1)), ⟨alpha, beta⟩)

/-- `for _ in 0..fold_count`: the rounds, each `alpha` pushed to `alphas` and the round to
`rounds`. -/
def foldRoundsRust : ℕ → E → List E → TM (E × List E × List FoldRound)
  | 0, claim, alphas => Pure.pure (claim, alphas, [])
  | n + 1, claim, alphas => do
    let (claim, round) ← foldRoundRust claim
    let (claim, alphas, rounds) ← foldRoundsRust n claim (alphas ++ [round.alpha])
    Pure.pure (claim, alphas, round :: rounds)

/-- `read_ood(transcript, vars, bits)` (`lib.rs`): a grind, `vars` samples, the value. -/
def readOodRust (vars bits : ℕ) : TM (List E × E) := do
  TM.grindCheck bits
  let z ← TM.samples vars
  let value ← TM.nextScalar
  Pure.pure (z, value)

/-- `verify_whir`'s locals across levels: `claim`, `alphas`, `glued`, `current_root`. -/
structure WhirLocals where
  /-- `claim`. -/
  claim : E
  /-- `alphas`. -/
  alphas : List E
  /-- `glued`. -/
  glued : List GluedClaimRust
  /-- `current_root`, as its bytes. -/
  currentRoot : List (BitVec 8)

/-- The level loop of `verify_whir`, from level `level` on, over the `(fold, rate)` pairs left;
`Err(WhirNoTerminalLevel)` past the last. The height and width given to `TM.commit` are the ghost
shape the root is opened at, a level later. -/
def whirLevelsRust (logN : ℕ) (config : WhirConfigRust) (basis : List E → Option E) :
    ℕ → List (ℕ × ℕ) → WhirLocals → TM Unit
  | _, [], _ => TM.fail
  | level, (foldCount, levelRate) :: rest, s => do
    let (claim, alphas, rounds) ← foldRoundsRust foldCount s.claim s.alphas
    let mu := logN - alphas.length
    let subspace ← TM.ofOption (SubspaceRust.new mu)
    let blockLength := 1#64 <<< ((mu + levelRate) % 64)
    let lanes := 2 ^ (foldCount % 64)
    let leafWords := if level = 0 then lanes else 2 * lanes
    if level = config.folds.length - 1 then do
      let folded ← TM.nextScalars (2 ^ (mu % 64) + foldCount)
      TM.grindCheck 17
      let queries ← sampleQueriesRust blockLength (config.queries.getD level 0)
      let words ← TM.merkle s.currentRoot blockLength queries leafWords
      TM.whenChecked (TM.ofOption
        (finalChecksRust subspace (lanesOfRust level) rounds folded queries words))
      let (tail, claim) ← TM.sumcheck claim 3 (List.replicate mu none)
      let checked ← TM.checked
      if !checked then Pure.pure () else do
        let point := alphas ++ tail
        let weight ← TM.ofOption (terminalWeightRust basis (config.folds.getD 0 0) s.glued point)
        let residual ← TM.ofOption (multilinearEvalRust (folded.take (2 ^ (mu % 64))) tail)
        TM.require (weight * residual = claim)
    else do
      let nextFold := config.folds.getD (level + 1) 0
      let nextRate := config.logInvRates.getD (level + 1) 0
      let nextRoot ← TM.commit (mu - nextFold + nextRate) (2 * 2 ^ nextFold)
      let high ← TM.nextScalars foldCount
      let (oodPoint, oodValue) ← readOodRust mu 15
      TM.grindCheck 17
      let queries ← sampleQueriesRust blockLength (config.queries.getD level 0)
      let lambda ← TM.sample
      let queryWeights := (powersM (limbs lambda) queries.length).map ofLimbsW
      let words ← TM.merkle s.currentRoot blockLength queries leafWords
      let batched ← TM.ofOption
        (batchedRust subspace mu (lanesOfRust level) rounds high queries words queryWeights)
      let claim := claim + lambda * oodValue
      let glued := s.glued ++ [⟨lambda, alphas.length, .ood oodPoint⟩]
      let lambda2 := lambda * lambda
      let claim := claim + lambda2 * batched
      let glued := glued ++ [⟨lambda2, alphas.length, .queries mu queries queryWeights⟩]
      whirLevelsRust logN config basis (level + 1) rest ⟨claim, alphas, glued, nextRoot⟩

/-- `verify_whir(transcript, log_n, log_inv_rate, target, root, evaluate_basis)`, `basis` the
closure (a panic or an `Err` of it `none`). -/
def verifyWhirRust (logN logInvRate : ℕ) (target : E) (root : List (BitVec 8))
    (basis : List E → Option E) : TM Unit := do
  let config ← TM.ofOption (deriveConfigRust logN logInvRate)
  whirLevelsRust logN config basis 0 (config.folds.zip config.logInvRates) ⟨target, [], [], root⟩

/-! ## Roots -/

section RootsLemmas

variable {α β γ δ : Type}

theorem RootsKept.merkle (root : List (BitVec 8)) (blockLength : BitVec 64)
    (queries : List (BitVec 64)) (leafWords : ℕ) :
    RootsKept (TM.merkle root blockLength queries leafWords) := by
  intro t a t' _ h
  simp only [TM.merkle, StateT.run] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split_ifs at h
      cases h; rfl

/-- **`merkle` opens the root a level holds**, the `i`-th the statement read. -/
theorem SimRoots.merkle_bind {pre : Roots → Prop} {i : ℕ} {d : Digest} {height width : ℕ}
    (hpre : ∀ roots, pre roots → roots[i]? = some (d, height, width)) (hh : height < 64)
    {qs : List (BitVec 64)} {ps : List ℕ} (hq : qs.map BitVec.toNat = ps)
    {k : List (List (BitVec 64)) → TM γ} {Q : List (List K) → VerifierProgram δ}
    {r : γ → δ → Prop}
    (hk : ∀ rows : List (List K), SimRoots pre (k (rows.map (·.map BF64.toBitVec))) (Q rows) r) :
    SimRoots pre (TM.merkle (digestBits d) (BitVec.ofNat 64 (2 ^ height)) qs width >>= k)
      (VerifierProgram.queryOpenings i ps >>= Q) r := by
  intro t c t' hi hp h
  rw [StateT.run_bind] at h
  cases hmt : (TM.merkle (digestBits d) (BitVec.ofNat 64 (2 ^ height)) qs width).run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨rows, t₁⟩ := p
    rw [hmt] at h
    obtain ⟨hi₁, rows', hrun, hrows⟩ := merkle_run hi (hpre _ hp) hh hq hmt
    rw [runK_bind, hrun]
    subst hrows
    exact hk rows' t₁ c t' hi₁
      (by rw [RootsKept.merkle _ _ _ _ t _ t₁ hi hmt]; exact hp) h

theorem commit_roots {height width : ℕ} {t t' : TState} {root : List (BitVec 8)} (hi : t.Inv)
    (h : (TM.commit height width).run t = some (root, t')) :
    ∃ d, root = digestBits d ∧ t'.roots = t.roots ++ [(d, height, width)] := by
  simp only [TM.commit, StateT.run_bind] at h
  cases h2 : (TM.nextScalars 2).run t with
  | none => rw [h2] at h; cases h
  | some p =>
    obtain ⟨halves, t₁⟩ := p
    rw [h2] at h
    have hr := RootsKept.ofSimR (Sim.nextScalars 2) (NoCommit.readScalars 2) t halves t₁ hi h2
    simp only [Option.bind_eq_bind, Option.bind_some, TM.ghostRoot, StateT.run] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨KeccakHash.digestFromHalves (halves.getD 0 0, halves.getD 1 0), ?_, ?_⟩
    · rw [digestFromHalvesRust_eq]; rfl
    · simp [hr]

/-- **A root's read**: the continuation runs from the roots with the new root appended. -/
theorem SimRoots.commit_bind {pre : Roots → Prop} {height width : ℕ}
    {k : List (BitVec 8) → TM γ} {Q : VerifierProgram δ} {r : γ → δ → Prop}
    (hk : ∀ d, SimRoots (fun roots ↦ ∃ old, pre old ∧ roots = old ++ [(d, height, width)])
      (k (digestBits d)) Q r) :
    SimRoots pre (TM.commit height width >>= k)
      (VerifierProgram.readCommitment height width >>= fun _ ↦ Q) r := by
  intro t c t' hi hp h
  rw [StateT.run_bind] at h
  cases hmt : (TM.commit height width).run t with
  | none => rw [hmt] at h; cases h
  | some p =>
    obtain ⟨root, t₁⟩ := p
    rw [hmt] at h
    obtain ⟨hi₁, b, hb, -⟩ := SimR.commit height width t root t₁ hi hmt
    obtain ⟨d, rfl, hroots⟩ := commit_roots hi hmt
    rw [runK_bind, hb]
    exact hk d t₁ c t' hi₁ ⟨t.roots, hp, hroots⟩ h

end RootsLemmas

/-! ## `sample_queries` runs `sampleQueries` -/

section SampleQueries

private theorem sampleWord_toNat (e : E) : (sampleWord e).toNat = eToNat e := by
  have h0 := (limbs e).1.isLt
  have h1 := (limbs e).2.isLt
  rw [sampleWord, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by
      have : (limbs e).2.toNat * 2 ^ 64 < 2 ^ 64 * 2 ^ 64 := by
        exact Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      omega), Nat.or_comm, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_add_eq_or_of_lt h0, Nat.shiftLeft_eq]
  simp only [eToNat, kToNat, limbs]
  ring

private theorem chunk_toNat (w : BitVec 128) {d s : ℕ} (hd : d < 64) (hs : s < 128) :
    ((w >>> (s % 128)).setWidth 64 &&& (BitVec.ofNat 64 (2 ^ d) - 1#64)).toNat =
      (w.toNat >>> s) % 2 ^ d := by
  have hp : 2 ^ d < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hd
  have hm : (BitVec.ofNat 64 (2 ^ d) - 1#64).toNat = 2 ^ d - 1 := by
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
      simp only [Nat.one_mod_two_pow (show 0 < 64 by norm_num)]
      exact Nat.one_le_two_pow), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
    rfl
  rw [Nat.mod_eq_of_lt hs, BitVec.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

private theorem queryChunks_eq (w : BitVec 128) {d : ℕ} (hd0 : 0 < d) (hd : d < 64)
    (count : ℕ) : ∀ (fuel c : ℕ) (result : List (BitVec 64)), c ≤ 128 / d →
    min (128 / d - c) (count - result.length) ≤ fuel →
    (queryChunks w (BitVec.ofNat 64 (2 ^ d)) d count fuel (c * d) result).map BitVec.toNat =
      result.map BitVec.toNat ++ (List.range' c (min (128 / d - c) (count - result.length))).map
        fun i ↦ (w.toNat >>> (i * d)) % 2 ^ d
  | 0, c, result, _, hm => by
    rw [show min (128 / d - c) (count - result.length) = 0 by omega]
    simp [queryChunks]
  | fuel + 1, c, result, hc, hm => by
    rw [queryChunks]
    by_cases hcond : c * d + d ≤ 128 ∧ result.length < count
    · rw [ite_eq_left hcond]
      have hc1 : c + 1 ≤ 128 / d :=
        (Nat.le_div_iff_mul_le hd0).2 (by rw [Nat.succ_mul]; exact hcond.1)
      have hmin : min (128 / d - c) (count - result.length) =
          min (128 / d - (c + 1)) (count - (result.length + 1)) + 1 := by omega
      rw [show c * d + d = (c + 1) * d by ring,
        queryChunks_eq w hd0 hd count fuel (c + 1) _ hc1 (by simp; omega), hmin,
        List.range'_succ]
      simp only [List.length_append, List.length_singleton, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc, List.cons_append, List.nil_append]
      rw [chunk_toNat w hd (by have := hcond.1; nlinarith)]
    · rw [ite_eq_right hcond]
      have hz : min (128 / d - c) (count - result.length) = 0 := by
        by_cases h1 : c * d + d ≤ 128
        · omega
        · have : ¬ c + 1 ≤ 128 / d := fun h ↦ h1 (by
            have := (Nat.le_div_iff_mul_le hd0).1 h; rw [Nat.succ_mul] at this; exact this)
          omega
      rw [hz]
      simp

private theorem sampleQueriesLoop_sim {d : ℕ} (hd0 : 0 < d) (hd : d < 64) (count : ℕ) :
    ∀ (fuel : ℕ) (result : List (BitVec 64)), result.length ≤ count →
    SimR (sampleQueriesLoop (BitVec.ofNat 64 (2 ^ d)) d count fuel result)
      (sampleQueriesAux d fuel (count - result.length))
      fun qs ps ↦ qs.map BitVec.toNat = result.map BitVec.toNat ++ ps
  | 0, result, _ => by
    simp only [sampleQueriesLoop, sampleQueriesAux]
    exact SimR.pure (by simp)
  | fuel + 1, result, hlen => by
    simp only [sampleQueriesLoop, sampleQueriesAux]
    by_cases hlt : result.length < count
    · rw [ite_eq_left hlt, ite_eq_right (by omega)]
      refine SimR.bindEq Sim.sample fun e ↦ ?_
      have hq := queryChunks_eq (sampleWord e) hd0 hd count count 0 result (Nat.zero_le _)
        (by omega)
      simp only [Nat.zero_mul, Nat.sub_zero] at hq
      have hlen' : (queryChunks (sampleWord e) (BitVec.ofNat 64 (2 ^ d)) d count count 0
          result).length = result.length + min (128 / d) (count - result.length) := by
        have := congrArg List.length hq
        simpa using this
      rw [← bind_pure (sampleQueriesLoop _ _ _ _ _)]
      have ih := sampleQueriesLoop_sim hd0 hd count fuel
        (queryChunks (sampleWord e) (BitVec.ofNat 64 (2 ^ d)) d count count 0 result)
        (by rw [hlen']; omega)
      rw [hlen', show count - (result.length + min (128 / d) (count - result.length)) =
        count - result.length - min (128 / d) (count - result.length) by omega] at ih
      refine SimR.bind ih fun qs ps h ↦ SimR.pure ?_
      rw [h, hq, List.append_assoc, sampleWord_toNat, List.range'_eq_map_range, List.map_map]
      simp only [Nat.zero_add]
      rfl
    · rw [ite_eq_right hlt, ite_eq_left (by omega)]
      exact SimR.pure (by simp)

private theorem sampleQueriesLoop_comp {d : ℕ} (hd0 : 0 < d) (hd : d < 64) (count : ℕ) :
    ∀ (fuel : ℕ) (result : List (BitVec 64)), result.length ≤ count →
    Comp (sampleQueriesLoop (BitVec.ofNat 64 (2 ^ d)) d count fuel result)
      (sampleQueriesAux d fuel (count - result.length))
  | 0, result, _ => by
    simp only [sampleQueriesLoop, sampleQueriesAux]
    exact Comp.pure _ _
  | fuel + 1, result, hlen => by
    simp only [sampleQueriesLoop, sampleQueriesAux]
    by_cases hlt : result.length < count
    · rw [ite_eq_left hlt, ite_eq_right (by omega)]
      refine Comp.bindEq Comp.sample Sim.sample fun e ↦ ?_
      have hq := queryChunks_eq (sampleWord e) hd0 hd count count 0 result (Nat.zero_le _)
        (by omega)
      simp only [Nat.zero_mul, Nat.sub_zero] at hq
      have hlen' : (queryChunks (sampleWord e) (BitVec.ofNat 64 (2 ^ d)) d count count 0
          result).length = result.length + min (128 / d) (count - result.length) := by
        have := congrArg List.length hq
        simpa using this
      have hr : count - (result.length + min (128 / d) (count - result.length)) =
          count - result.length - min (128 / d) (count - result.length) := by omega
      have ih := sampleQueriesLoop_comp hd0 hd count fuel
        (queryChunks (sampleWord e) (BitVec.ofNat 64 (2 ^ d)) d count count 0 result)
        (by rw [hlen']; omega)
      have hs := sampleQueriesLoop_sim hd0 hd count fuel
        (queryChunks (sampleWord e) (BitVec.ofNat 64 (2 ^ d)) d count count 0 result)
        (by rw [hlen']; omega)
      rw [hlen', hr] at ih hs
      rw [← bind_pure (sampleQueriesLoop _ _ _ _ _)]
      exact Comp.bind ih hs fun _ _ _ ↦ Comp.pure _ _
    · rw [ite_eq_right hlt, ite_eq_left (by omega)]
      exact Comp.pure _ _

/-- **`sample_queries` returns wherever `sampleQueries` runs**, at a depth in `1 .. 63`. -/
theorem Comp.sampleQueries {d : ℕ} (hd0 : 0 < d) (hd : d < 64) (count : ℕ) :
    Comp (sampleQueriesRust (1#64 <<< (d % 64)) count) (sampleQueries d count) := by
  rw [one_shl_eq hd, sampleQueriesRust, log2StrictRust_two_pow hd]
  simp only [TM.ofOption, pure_bind]
  have := sampleQueriesLoop_comp hd0 hd count count [] (Nat.zero_le _)
  simpa [LeanVM.Protocol.Verifier.sampleQueries] using this

/-- **`sample_queries` runs `sampleQueries`**, at a depth in `1 .. 63`. -/
theorem SimR.sampleQueries {d : ℕ} (hd0 : 0 < d) (hd : d < 64) (count : ℕ) :
    SimR (sampleQueriesRust (1#64 <<< (d % 64)) count) (sampleQueries d count)
      fun qs ps ↦ qs.map BitVec.toNat = ps := by
  rw [one_shl_eq hd, sampleQueriesRust, log2StrictRust_two_pow hd]
  simp only [TM.ofOption, pure_bind]
  have := sampleQueriesLoop_sim hd0 hd count count [] (Nat.zero_le _)
  simpa [LeanVM.Protocol.Verifier.sampleQueries] using this

theorem NoCommit.sampleQueries (d count : ℕ) : NoCommit (sampleQueries d count) := by
  suffices ∀ fuel rem, NoCommit (sampleQueriesAux d fuel rem) from this _ _
  intro fuel
  induction fuel with
  | zero => intro rem; exact NoCommit.ret _
  | succ n ih =>
    intro rem
    rw [sampleQueriesAux]
    split
    · exact NoCommit.ret _
    · exact NoCommit.bind NoCommit.sampleChallenge fun _ ↦ NoCommit.bind (ih _) fun _ ↦
        NoCommit.ret _

end SampleQueries

/-! ## The fold rounds and the out-of-domain read -/

private theorem readScalars_four {γ : Type} (f : List E → VerifierProgram γ) :
    VerifierProgram.readScalars 4 >>= f =
      VerifierProgram.readScalar >>= fun a ↦ VerifierProgram.readScalar >>= fun b ↦
        VerifierProgram.readScalar >>= fun c ↦ VerifierProgram.readScalar >>= fun d ↦
          f [a, b, c, d] := by
  simp only [VerifierProgram.readScalars, VerifierProgram.bind_assoc']
  rfl

/-- **A fold round runs `foldRound`**: the same claim and round; the statement's `alphas` grows by
the round's `alpha`. -/
private theorem foldRound_eq (s : WhirState) :
    LeanVM.Protocol.Verifier.foldRound s = VerifierProgram.readScalars 4 >>= fun table ↦
      (do
        VerifierProgram.grindProofOfWork Whir.foldGrindingBits
        let alpha ← VerifierProgram.sampleChallenge
        let beta ← VerifierProgram.sampleChallenge
        return ({ s with
          claim := table.getD 0 0 + alpha * (table.getD 0 0 + s.claim) +
            alpha * alpha * table.getD 1 0 + beta * table.getD 2 0 +
            alpha * beta * (table.getD 2 0 + table.getD 3 0),
          alphas := s.alphas ++ [alpha] }, ⟨alpha, beta⟩)) := by
  rw [readScalars_four]; rfl

theorem SimR.foldRound (s : WhirState) :
    SimR (foldRoundRust s.claim) (LeanVM.Protocol.Verifier.foldRound s) fun a b ↦
      a.1 = b.1.claim ∧ a.2 = b.2 ∧ b.1.alphas = s.alphas ++ [a.2.alpha] ∧ b.1.glued = s.glued := by
  rw [foldRound_eq]
  unfold foldRoundRust
  refine SimR.bindEq (Sim.nextScalars 4) fun table ↦ SimR.bindEq (Sim.grindCheck _) fun _ ↦
    SimR.bindEq Sim.sample fun alpha ↦ SimR.bindEq Sim.sample fun beta ↦
      SimR.pure ⟨by ring, rfl, rfl, rfl⟩

/-- **A fold round returns wherever `foldRound` runs.** -/
theorem Comp.foldRound (s : WhirState) :
    Comp (foldRoundRust s.claim) (LeanVM.Protocol.Verifier.foldRound s) := by
  rw [foldRound_eq]
  unfold foldRoundRust
  exact Comp.bindEq (Comp.nextScalars 4) (Sim.nextScalars 4) fun _ ↦
    Comp.bindEq (Comp.grindCheck _) (Sim.grindCheck _) fun _ ↦
      Comp.bindEq Comp.sample Sim.sample fun _ ↦ Comp.bindEq Comp.sample Sim.sample fun _ ↦
        Comp.pure _ _

/-- **`read_ood` returns** wherever its grind, samples and read run. -/
theorem Comp.readOod (vars bits : ℕ) :
    Comp (readOodRust vars bits) (do
      VerifierProgram.grindProofOfWork bits
      let z ← VerifierProgram.sampleChallenges vars
      let value ← VerifierProgram.readScalar
      return (z, value)) :=
  Comp.bindEq (Comp.grindCheck _) (Sim.grindCheck _) fun _ ↦
    Comp.bindEq (Comp.samples _) (Sim.samples _) fun _ ↦
      Comp.bindEq Comp.nextScalar Sim.nextScalar fun _ ↦ Comp.pure _ _

/-- **The fold rounds run `foldRounds`.** -/
theorem SimR.foldRounds : ∀ (n : ℕ) (s : WhirState),
    SimR (foldRoundsRust n s.claim s.alphas) (LeanVM.Protocol.Verifier.foldRounds n s)
      fun a b ↦ a.1 = b.1.claim ∧ a.2.1 = b.1.alphas ∧ a.2.2 = b.2 ∧ b.1.glued = s.glued ∧
        b.1.alphas.length = s.alphas.length + n
  | 0, s => SimR.pure ⟨rfl, rfl, rfl, rfl, rfl⟩
  | n + 1, s => by
    rw [foldRoundsRust, LeanVM.Protocol.Verifier.foldRounds]
    refine SimR.bind (SimR.foldRound s) fun a b hab ↦ ?_
    obtain ⟨c, rd⟩ := a
    obtain ⟨s₁, rd'⟩ := b
    obtain ⟨h1, h2, h3, h4⟩ := hab
    dsimp only at h1 h2 h3 h4 ⊢
    subst h2
    rw [h1, ← h3]
    refine SimR.bind (SimR.foldRounds n s₁) fun a b hab ↦ ?_
    obtain ⟨c', al, rs⟩ := a
    obtain ⟨s₂, rs'⟩ := b
    obtain ⟨g1, g2, g3, g4, g5⟩ := hab
    dsimp only at g1 g2 g3 g4 g5 ⊢
    refine SimR.pure ⟨g1, g2, by rw [g3], g4.trans h4, ?_⟩
    rw [g5, h3, List.length_append, List.length_singleton]
    omega

theorem NoCommit.foldRounds : ∀ (n : ℕ) (s : WhirState),
    NoCommit (LeanVM.Protocol.Verifier.foldRounds n s)
  | 0, _ => NoCommit.ret _
  | n + 1, s => by
    rw [LeanVM.Protocol.Verifier.foldRounds, LeanVM.Protocol.Verifier.foldRound]
    no_commit
    exact NoCommit.foldRounds n _

/-! ## The level's pure steps against the statement -/

theorem lanesOfRust_eq (level : ℕ) (row : List K) :
    lanesOfRust level (row.map BF64.toBitVec) =
      if level = 0 then row.reverse.map ofK else extRow row := by
  unfold lanesOfRust
  split_ifs
  · rw [← List.map_reverse, List.map_map]; rfl
  · exact extRowRust_eq row

theorem ofBits_toNat (q : BitVec 64) : K.ofBits q.toNat = BF64.ofBitVec q := by
  simp [K.ofBits]

private theorem forM_some {α : Type} {f : α → Option Unit} :
    ∀ (l : List α), l.forM f = some () → ∀ x ∈ l, f x = some ()
  | [], _, x, hx => by cases hx
  | a :: l, h, x, hx => by
    simp only [List.forM] at h
    cases ha : f a with
    | none => rw [ha] at h; cases h
    | some u =>
      rw [ha] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact forM_some l h x hx

/-- **The final level's checks hold** wherever they pass. -/
theorem finalChecksRust_mem {sub : SubspaceRust} {mu : ℕ} (hmu : mu < 64)
    (hsub : SubspaceRust.new mu = some sub) {lanesOf : List (BitVec 64) → List E}
    {rounds : List FoldRound} {folded : List E} {qs : List (BitVec 64)}
    {ws : List (List (BitVec 64))} (h : finalChecksRust sub lanesOf rounds folded qs ws = some ()) :
    ∀ x ∈ qs.zip ws, foldRow (lanesOf x.2) (BF64.ofBitVec x.1) rounds =
      novelEval folded (subspaceAt mu (BF64.ofBitVec x.1)) := by
  intro x hx
  have hf := forM_some _ h x hx
  simp only [Option.bind_eq_bind] at hf
  cases hv : foldRowRust (lanesOf x.2) (BF64.ofBitVec x.1) rounds with
  | none => rw [hv] at hf; cases hf
  | some value =>
    rw [hv] at hf
    simp only [Option.bind_some] at hf
    cases he : novelEvalRust folded (sub.at (BF64.ofBitVec x.1)) with
    | none => rw [he] at hf; cases hf
    | some expected =>
      rw [he] at hf
      simp only [Option.bind_some] at hf
      split_ifs at hf with hve
      rw [← foldRowRust_some hv, hve, novelEvalRust_some he, SubspaceRust.at_eq hmu hsub]

private theorem foldlM_sum {α : Type} {step : E → α → Option E} {T : α → E}
    (hs : ∀ b a b', step b a = some b' → b' = b + T a) :
    ∀ (l : List α) (acc v : E), l.foldlM step acc = some v → v = (l.map T).foldl (· + ·) acc
  | [], acc, v, h => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    simp [h]
  | a :: l, acc, v, h => by
    rw [List.foldlM_cons] at h
    cases ha : step acc a with
    | none => rw [ha] at h; cases h
    | some b =>
      rw [ha] at h
      rw [List.map_cons, List.foldl_cons, ← hs acc a b ha]
      exact foldlM_sum hs l b v h

/-- **A non-final level's batched queries** wherever they return. -/
theorem batchedRust_some {sub : SubspaceRust} {mu : ℕ} (hmu : mu < 64)
    (hsub : SubspaceRust.new mu = some sub) {lanesOf : List (BitVec 64) → List E}
    {rounds : List FoldRound} {high : List E} {qs : List (BitVec 64)}
    {ws : List (List (BitVec 64))} {qw : List E} {v : E}
    (h : batchedRust sub mu lanesOf rounds high qs ws qw = some v) :
    v = sumE (((qs.zip ws).zip qw).map fun x ↦
      let what := subspaceAt mu (BF64.ofBitVec x.1.1)
      x.2 * (foldRow (lanesOf x.1.2) (BF64.ofBitVec x.1.1) rounds +
        novelEval high what * ofK (what.getD mu 0))) := by
  refine foldlM_sum (fun b x b' hb ↦ ?_) _ 0 v h
  simp only [batchedStep, Option.bind_eq_bind] at hb
  cases hc : novelEvalRust high (sub.at (BF64.ofBitVec x.1.1)) with
  | none => rw [hc] at hb; cases hb
  | some c =>
    rw [hc] at hb
    simp only [Option.map_some, Option.bind_some] at hb
    cases hf : foldRowRust (lanesOf x.1.2) (BF64.ofBitVec x.1.1) rounds with
    | none => rw [hf] at hb; cases hb
    | some f =>
      rw [hf] at hb
      simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at hb
      rw [← hb, foldRowRust_some hf, novelEvalRust_some hc, mulKE_eq, SubspaceRust.at_eq hmu hsub]

private theorem forM_of_all {α : Type} {f : α → Option Unit} :
    ∀ (l : List α), (∀ x ∈ l, f x = some ()) → l.forM f = some ()
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.forM, h a (by simp)]
    exact forM_of_all l fun x hx ↦ h x (by simp [hx])

/-- **The final level's checks pass** where the statement's do, on rows of `2^r` lanes and at
most `2^(mu+1)` coefficients. -/
theorem finalChecksRust_eq {sub : SubspaceRust} {mu : ℕ} (hmu : mu < 64)
    (hsub : SubspaceRust.new mu = some sub) {lanesOf : List (BitVec 64) → List E}
    {rounds : List FoldRound} {folded : List E} {qs : List (BitVec 64)}
    {ws : List (List (BitVec 64))} (hf : folded.length ≤ 2 ^ (mu + 1))
    (h : ∀ x ∈ qs.zip ws, (lanesOf x.2).length = 2 ^ rounds.length ∧
      foldRow (lanesOf x.2) (BF64.ofBitVec x.1) rounds =
        novelEval folded (subspaceAt mu (BF64.ofBitVec x.1))) :
    finalChecksRust sub lanesOf rounds folded qs ws = some () := by
  refine forM_of_all _ fun x hx ↦ ?_
  obtain ⟨hl, he⟩ := h x hx
  simp [foldRowRust_eq hl, SubspaceRust.at_eq hmu hsub,
    novelEvalRust_eq (what := subspaceAt mu (BF64.ofBitVec x.1))
      (by rw [subspaceAt_length]; exact hf), he]

private theorem foldlM_isSome {α : Type} {step : E → α → Option E} :
    ∀ (l : List α) (acc : E), (∀ b, ∀ a ∈ l, (step b a).isSome) → (l.foldlM step acc).isSome
  | [], _, _ => rfl
  | a :: l, acc, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h acc a (by simp))
    rw [List.foldlM_cons, hb]
    exact foldlM_isSome l b fun b' a' ha' ↦ h b' a' (by simp [ha'])

/-- **A non-final level's batched queries return** on rows of `2^r` lanes and a high part of at
most `2^(mu+1)` coefficients. -/
theorem batchedRust_eq {sub : SubspaceRust} {mu : ℕ} (hmu : mu < 64)
    (hsub : SubspaceRust.new mu = some sub) {lanesOf : List (BitVec 64) → List E}
    {rounds : List FoldRound} {high : List E} {qs : List (BitVec 64)}
    {ws : List (List (BitVec 64))} {qw : List E} (hh : high.length ≤ 2 ^ (mu + 1))
    (h : ∀ x ∈ qs.zip ws, (lanesOf x.2).length = 2 ^ rounds.length) :
    batchedRust sub mu lanesOf rounds high qs ws qw = some (sumE (((qs.zip ws).zip qw).map fun x ↦
      let what := subspaceAt mu (BF64.ofBitVec x.1.1)
      x.2 * (foldRow (lanesOf x.1.2) (BF64.ofBitVec x.1.1) rounds +
        novelEval high what * ofK (what.getD mu 0)))) := by
  have hs : (batchedRust sub mu lanesOf rounds high qs ws qw).isSome := by
    refine foldlM_isSome _ _ fun b x hx ↦ ?_
    have hl := h x.1 (List.of_mem_zip hx).1
    simp [batchedStep, foldRowRust_eq hl, SubspaceRust.at_eq hmu hsub,
      novelEvalRust_eq (what := subspaceAt mu (BF64.ofBitVec x.1.1))
        (by rw [subspaceAt_length]; exact hh)]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
  rw [hv, batchedRust_some hmu hsub hv]

/-- A glued claim and the statement's: the same scalar and start, and a weight that agrees with
the statement's wherever it returns. -/
def GluedRel (g : GluedClaimRust) (g' : GluedClaim) : Prop :=
  g.scalar = g'.scalar ∧ g.foldStart = g'.foldStart ∧
    ∀ x v, g.weight.evaluate x = some v → v = g'.weightAt x

/-- **The terminal weight is the statement's** wherever it returns. -/
theorem terminalWeightRust_some {basis : List E → Option E} {evaluateBasis : List E → E}
    (laneFolds : ℕ) (point : List E)
    (hb : ∀ v, basis (point.drop laneFolds ++ point.take laneFolds) = some v →
      v = evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
    {gs : List GluedClaimRust} {gs' : List GluedClaim} (hg : List.Forall₂ GluedRel gs gs')
    {v : E} (h : terminalWeightRust basis laneFolds gs point = some v) :
    v = gs'.foldl (fun weight glued ↦ weight + glued.scalar * glued.weightAt
      (point.drop glued.foldStart))
      (evaluateBasis (point.drop laneFolds ++ point.take laneFolds)) := by
  unfold terminalWeightRust at h
  simp only [Option.bind_eq_bind] at h
  cases hw : basis (point.drop laneFolds ++ point.take laneFolds) with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    simp only [Option.bind_some] at h
    rw [← hb _ hw]
    clear hw
    induction hg generalizing w with
    | nil => simpa using h.symm
    | @cons g g' gs gs' hr _ ih =>
      rw [List.foldlM_cons] at h
      simp only [Option.bind_eq_bind] at h
      cases he : g.weight.evaluate (point.drop g.foldStart) with
      | none => rw [he] at h; simp at h
      | some e =>
        rw [he] at h
        simp only [Option.bind_some, Option.pure_def] at h
        rw [List.foldl_cons, ← hr.1, ← hr.2.1, ← hr.2.2 _ _ he]
        exact ih _ h

/-! ## `verify_whir` runs `verifyWhir` -/

/-- The roots a level opens from: `index + 1` read, the last one the level's, of its shape. -/
def LevelRoots (index : ℕ) (d : Digest) (shape : ℕ × ℕ) (roots : Roots) : Prop :=
  roots.length = index + 1 ∧ roots[index]? = some (d, shape.1, shape.2)

/-- The shape level `index` opens its commitment at, `alphas` fold rounds before it. -/
def levelOpenShape (logN alphas index : ℕ) (level : Whir.Level) : ℕ × ℕ :=
  (logN - alphas - level.fold + level.logInvRate,
    if index = 0 then 2 ^ level.fold else 2 * 2 ^ level.fold)

theorem SimRoots.whirLevels (logN : ℕ) (ls : List Whir.Level) (hf : LadderFacts logN ls)
    {basis : List E → Option E} {evaluateBasis : List E → E}
    (hb : ∀ x v, x.length = logN → basis x = some v → v = evaluateBasis x) :
    ∀ (rest : List Whir.Level) (index : ℕ) (s : WhirLocals) (s' : WhirState) (d : Digest),
      ls.drop index = rest → s.claim = s'.claim → s.alphas = s'.alphas →
      List.Forall₂ GluedRel s.glued s'.glued → s.currentRoot = digestBits d →
      s.alphas.length + (rest.map (·.fold)).sum ≤ logN →
      SimRoots (fun roots ↦ ∀ level ∈ rest.head?,
          LevelRoots index d (levelOpenShape logN s.alphas.length index level) roots)
        (whirLevelsRust logN (configOf ls) basis index (rest.map fun l ↦ (l.fold, l.logInvRate)) s)
        (whirLevels logN 6 evaluateBasis index rest s') fun _ _ ↦ True
  | [], index, s, s', d, _, _, _, _, _, _ => by
    simp only [List.map_nil, whirLevelsRust, LeanVM.Protocol.Verifier.whirLevels]
    exact SimRoots.fail
  | level :: rest, index, s, s', d, hdrop, hc, ha, hg, hr, hsum => by
    have hmem : level ∈ ls := List.mem_of_mem_drop (by rw [hdrop]; exact List.mem_cons_self ..)
    obtain ⟨hq1, hq2, hq3, hq4⟩ := hf.2.2.2.1 level hmem
    simp only [List.map_cons, List.sum_cons] at hsum
    have hal := congrArg List.length ha
    simp only [List.map_cons, whirLevelsRust, LeanVM.Protocol.Verifier.whirLevels]
    rw [hc, ha]
    refine SimRoots.bindR (SimR.foldRounds level.fold s') (NoCommit.foldRounds _ _)
      fun a b hab ↦ ?_
    obtain ⟨claim, alphas, rounds⟩ := a
    obtain ⟨s₂, rounds'⟩ := b
    obtain ⟨h1, h2, h3, h4, h5⟩ := hab
    dsimp only at h1 h2 h3 h4 h5 ⊢
    subst h2 h3
    have hlen := congrArg List.length hdrop
    rw [List.length_drop, List.length_cons] at hlen
    have hls : ls[index]? = some level := by
      have h0 : (ls.drop index)[0]? = some level := by rw [hdrop]; rfl
      rwa [List.getElem?_drop, Nat.add_zero] at h0
    have hmu : logN - s₂.alphas.length < 64 := by have := hf.1; omega
    have hdepth : logN - s₂.alphas.length + level.logInvRate < 64 := by have := hf.1; omega
    have hfold : level.fold < 64 := by omega
    have hqueries : (configOf ls).queries.getD index 0 = level.queries := by
      simp [configOf, List.getD_eq_getElem?_getD, hls]
    have hfl : (configOf ls).folds.length = ls.length := by simp [configOf]
    have hg₂ : List.Forall₂ GluedRel s.glued s₂.glued := h4 ▸ hg
    rw [hqueries, hfl, Nat.mod_eq_of_lt hmu, Nat.mod_eq_of_lt hfold]
    refine SimRoots.ofOption_bind fun sub hsub ↦ ?_
    cases rest with
    | nil =>
      simp only [List.length_nil] at hlen
      rw [ite_eq_left (by omega)]
      have hlaneFolds : (configOf ls).folds.getD 0 0 = 6 := by
        have h6 := hf.2.2.1
        cases ls with
        | nil => cases h6
        | cons l ls => simpa [configOf] using h6
      subst h1
      dsimp only
      refine SimRoots.bindE (Sim.nextScalars _) (NoCommit.readScalars _) fun folded ↦ ?_
      refine SimRoots.bindE (Sim.grindCheck _) (NoCommit.grindProofOfWork _) fun _ ↦ ?_
      refine SimRoots.bindR (SimR.sampleQueries (by omega) hdepth level.queries)
        (NoCommit.sampleQueries _ _) fun qs ps hq ↦ ?_
      rw [hr, one_shl_eq hdepth]
      refine SimRoots.merkle_bind (i := index)
        (height := logN - s₂.alphas.length + level.logInvRate) (fun roots hroots ↦ ?_) hdepth hq
        fun rows ↦ ?_
      · obtain ⟨-, h⟩ := hroots level rfl
        rw [h, levelOpenShape, show logN - s'.alphas.length - level.fold =
          logN - s₂.alphas.length by omega]
      refine SimRoots.whenChecked_bind (SimRoots.ofOption_bind fun u hu ↦ ?_)
      refine SimRoots.require_right ?_ ?_
      · rw [List.all_eq_true]
        intro x hx
        rw [← hq, List.zip_map_left, List.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have := finalChecksRust_mem hmu hsub hu (y.1, y.2.map BF64.toBitVec)
          (by rw [List.zip_map_right]; exact List.mem_map_of_mem (f := Prod.map id _) hy)
        rw [lanesOfRust_eq] at this
        simpa [ofBits_toNat] using this
      have hsc := SimR.sumcheck_bind s₂.claim (count := 3) (by norm_num) (by norm_num)
        (List.replicate (logN - s₂.alphas.length) none) (k := fun x ↦ Pure.pure x)
        (K := VerifierProgram.ret) (r := fun a b ↦ a = b ∧ a.1.length = logN - s₂.alphas.length)
        fun p v hp ↦ SimR.pure ⟨rfl, by simpa using hp⟩
      rw [bind_pure, VerifierProgram.bind_ret'] at hsc
      refine SimRoots.bindR hsc (NoCommit.sumcheck _ _ _) fun x y hxy ↦ ?_
      obtain ⟨rfl, htail⟩ := hxy
      obtain ⟨tail, c⟩ := x
      dsimp only at htail
      refine SimRoots.checked_bind ?_
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine SimRoots.ofOption_bind fun w hw ↦ SimRoots.ofOption_bind fun res hres ↦ ?_
      refine SimRoots.of (SimR.mono (Sim.require_iff ?_) fun _ _ _ ↦ trivial)
      rw [hlaneFolds] at hw
      rw [terminalWeightRust_some _ _ (fun v hv ↦ hb _ v (by
        simp only [List.length_append, List.length_drop, List.length_take, htail]
        simp only [List.map_nil, List.sum_nil] at hsum
        omega) hv) hg₂ hw,
        multilinearEvalRust_some hres]
    | cons next rest =>
      simp only [List.length_cons] at hlen
      rw [ite_eq_right (by omega)]
      have hnext : ls[index + 1]? = some next := by
        have h0 : (ls.drop index)[1]? = some next := by rw [hdrop]; rfl
        rwa [List.getElem?_drop] at h0
      have hnf : (configOf ls).folds.getD (index + 1) 0 = next.fold := by
        simp [configOf, List.getD_eq_getElem?_getD, hnext]
      have hnr : (configOf ls).logInvRates.getD (index + 1) 0 = next.logInvRate := by
        simp [configOf, List.getD_eq_getElem?_getD, hnext]
      rw [hnf, hnr]
      subst h1
      simp only [levelShape]
      refine SimRoots.commit_bind fun d' ↦ ?_
      refine SimRoots.bindE (Sim.nextScalars _) (NoCommit.readScalars _) fun high ↦ ?_
      simp only [readOodRust, bind_assoc, pure_bind]
      refine SimRoots.bindE (Sim.grindCheck _) (NoCommit.grindProofOfWork _) fun _ ↦ ?_
      refine SimRoots.bindE (Sim.samples _) (NoCommit.sampleChallenges _) fun oodPoint ↦ ?_
      refine SimRoots.bindE Sim.nextScalar NoCommit.readScalar fun oodValue ↦ ?_
      refine SimRoots.bindE (Sim.grindCheck _) (NoCommit.grindProofOfWork _) fun _ ↦ ?_
      refine SimRoots.bindR (SimR.sampleQueries (by omega) hdepth level.queries)
        (NoCommit.sampleQueries _ _) fun qs ps hq ↦ ?_
      refine SimRoots.bindE Sim.sample NoCommit.sampleChallenge fun lam ↦ ?_
      rw [hr, one_shl_eq hdepth]
      refine SimRoots.merkle_bind (i := index)
        (height := logN - s₂.alphas.length + level.logInvRate) (fun roots hroots ↦ ?_) hdepth hq
        fun rows ↦ ?_
      · obtain ⟨old, hold, rfl⟩ := hroots
        obtain ⟨hl, h⟩ := hold level rfl
        rw [List.getElem?_append_left (by omega), h, levelOpenShape,
          show logN - s'.alphas.length - level.fold = logN - s₂.alphas.length by omega]
      refine SimRoots.ofOption_bind fun batched hbat ↦ ?_
      have hqw : (powersM (limbs lam) qs.length).map ofLimbsW = powers lam ps.length := by
        rw [powersM_eq, List.map_map, ← hq, List.length_map]
        simp [Function.comp_def, ofLimbsW_limbs]
      have hbat' := batchedRust_some hmu hsub hbat
      have hdrop' : ls.drop (index + 1) = next :: rest := by
        rw [← List.drop_drop, hdrop]; rfl
      refine SimRoots.weaken ?_ (SimRoots.whirLevels logN ls hf hb (next :: rest) (index + 1) _ _ d'
        hdrop' ?_ rfl ?_ rfl (by dsimp only; omega))
      · intro roots ⟨old, hold, hroots⟩ l hl
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hl
        subst hl hroots
        obtain ⟨hlen', -⟩ := hold level rfl
        refine ⟨by simp [hlen'], ?_⟩
        rw [List.getElem?_append_right (by omega), show index + 1 - old.length = 0 by omega]
        simp [levelOpenShape]
      · simp only [glueLevel]
        rw [hbat', hqw]
        congr 3
        rw [← List.map_uncurry_zip_eq_zipWith, ← hq]
        simp only [List.zip_map_left, List.zip_map_right, List.map_map]
        refine List.map_congr_left fun x _ ↦ ?_
        obtain ⟨⟨q, row⟩, w⟩ := x
        simp [lanesOfRust_eq, ofBits_toNat]
      · simp only [glueLevel, List.append_assoc, List.singleton_append]
        refine List.rel_append hg₂ (List.Forall₂.cons ⟨rfl, rfl, fun x v h ↦ eqEvalRust_some h⟩
          (List.Forall₂.cons ⟨rfl, rfl, fun x v h ↦ ?_⟩ List.Forall₂.nil))
        rw [inducedWeightRust_some hmu h, hq, hqw]

/-- The roots `verify_execution` has read when it opens the stack: the stack's alone, of the shape
level `0` opens it at (`commitStack`). -/
def StackRoots (logN logInvRate : ℕ) (d : Digest) (roots : Roots) : Prop :=
  ∀ ls, Whir.ladder logN logInvRate = some ls → ∀ l ∈ ls.head?,
    roots = [(d, (levelShape logN l (2 ^ l.fold)).1, (levelShape logN l (2 ^ l.fold)).2)]

/-- **`verify_whir` runs `verifyWhir`**, the stack's root `d` the only one read, with a basis
that agrees with the statement's wherever it returns. -/
theorem SimRoots.verifyWhir (logN logInvRate : ℕ) (target : E) (d : Digest)
    {basis : List E → Option E} {evaluateBasis : List E → E}
    (hb : ∀ x v, x.length = logN → basis x = some v → v = evaluateBasis x) :
    SimRoots (StackRoots logN logInvRate d)
      (verifyWhirRust logN logInvRate target (digestBits d) basis)
      (verifyWhir logN logInvRate target evaluateBasis) fun _ _ ↦ True := by
  unfold verifyWhirRust LeanVM.Protocol.Verifier.verifyWhir
  rw [deriveConfigRust_eq]
  cases hl : Whir.ladder logN logInvRate with
  | none => exact SimRoots.ofOption_bind fun a h ↦ by cases h
  | some ls =>
    have hf := ladder_facts hl
    refine SimRoots.ofOption_bind fun c hc ↦ ?_
    cases hc
    have hz : (configOf ls).folds.zip (configOf ls).logInvRates =
        ls.map fun l ↦ (l.fold, l.logInvRate) := by
      simp only [configOf, List.zip_map']
    have h6 : (ls.head?.map (·.fold)).getD 0 = 6 := by rw [hf.2.2.1]; rfl
    show SimRoots _ _ (LeanVM.Protocol.Verifier.whirLevels logN ((ls.head?.map (·.fold)).getD 0)
      evaluateBasis 0 ls
      ⟨target, [], []⟩) _
    rw [hz, h6]
    refine SimRoots.weaken ?_
      (SimRoots.whirLevels logN ls hf hb ls 0 _ _ d rfl rfl rfl List.Forall₂.nil rfl
        (by simpa using hf.2.2.2.2))
    intro roots hroots l hlm
    rw [hroots ls hl l hlm]
    refine ⟨rfl, ?_⟩
    simp [levelShape, levelOpenShape]

/-! ## The stacked opening (`lib.rs`) -/

/-- `StackWeight`. -/
inductive StackWeightRust where
  /-- `Eq(point)`. -/
  | eq (point : List E)
  /-- `Ring(weight)`. -/
  | ring (weight : RingWeightRust)
  /-- `PlacedRing(placement, weight)`. -/
  | placedRing (placement : PlacementRust) (weight : RingWeightRust)

/-- `StackWeight::evaluate(x)`: `placement.eq_above(x) * weight.evaluate(&x[..variables])` for a
placed ring weight. -/
def StackWeightRust.evaluate : StackWeightRust → List E → Option E
  | .eq point, x => eqEvalRust point x
  | .ring weight, x => weight.evaluate x
  | .placedRing placement weight, x => do
    let above ← placement.eqAbove x
    let value ← weight.evaluate (x.take placement.variableCount)
    pure (above * value)

/-- `verify_stacked_opening(transcript, root, stack_log, log_inv_rate, claims)`: the values,
`require(claims.len() <= MAX_STACKED_CLAIMS)`, the powers of one challenge, the basis closure
(`dot` of the scales and the weights) and the target. -/
def verifyStackedOpeningRust (root : List (BitVec 8)) (stackLog logInvRate : ℕ)
    (claims : List (StackWeightRust × E)) : TM Unit := do
  let values := claims.map (·.2)
  TM.require (claims.length ≤ 512)
  let scales := (powersM (limbs (← TM.sample)) claims.length).map ofLimbsW
  let basis := fun point ↦ do
    let weights ← claims.mapM fun c ↦ c.1.evaluate point
    dotRust scales weights
  let target ← TM.ofOption (dotRust scales values)
  verifyWhirRust stackLog logInvRate target root basis

/-- A stacked claim and the statement's: the same value, and a weight that agrees with the
statement's wherever it returns on a point of the stack's `stackLog ≤ 64` variables. -/
def StackClaimRel (stackLog : ℕ) (c : StackWeightRust × E) (c' : StackClaim) : Prop :=
  c.2 = c'.2 ∧ ∀ x v, x.length = stackLog → c.1.evaluate x = some v → v = c'.1 x

/-- `Eq(point)` is an equality claim. -/
theorem stackClaimRel_eq (stackLog : ℕ) (point : List E) (value : E) :
    StackClaimRel stackLog (.eq point, value) (fun x ↦ eqEval point x, value) :=
  ⟨rfl, fun _ _ _ h ↦ eqEvalRust_some h⟩

/-- **`PlacedRing` is the statement's ring-switching claim** (`ringSwitchClaim`), the weight the
ring switch's. `walk` builds it from `layout.committed(QKECCAK)?`, the placement the statement's
`layout.placement qkeccak` transcribes, and opens the stack at `stack_log ≤ MAX_STACKED_LOG = 30`
(`CommittedSize`), so `stackLog ≤ 64`. -/
theorem stackClaimRel_placedRing {stackLog : ℕ} (hs : stackLog ≤ 64) (layout : Layout)
    (placement : PlacementRust) (hp : placement.toSpec = layout.placement qkeccak)
    (w : RingWeightRust) (f : List E → E)
    (hw : ∀ x v, w.evaluate x = some v → v = f x) (target : E) :
    StackClaimRel stackLog (.placedRing placement w, target) (ringSwitchClaim layout target f) := by
  refine ⟨rfl, fun x v hx h ↦ ?_⟩
  simp only [StackWeightRust.evaluate, Option.bind_eq_bind] at h
  rw [placement.eqAbove_eq x (by omega)] at h
  simp only [Option.bind_some] at h
  cases he : w.evaluate (x.take placement.variableCount) with
  | none => rw [he] at h; cases h
  | some e =>
    rw [he] at h
    simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h
    rw [← h, hw _ _ he, ringSwitchClaim, ← hp]
    rfl

private theorem mapM_eval {stackLog : ℕ} {x : List E} (hx : x.length = stackLog) :
    ∀ {claims : List (StackWeightRust × E)} {claims' : List StackClaim},
    List.Forall₂ (StackClaimRel stackLog) claims claims' → ∀ ws,
      claims.mapM (fun c ↦ c.1.evaluate x) = some ws → ws = claims'.map fun c ↦ c.1 x
  | [], [], .nil, ws, h => by simpa using h.symm
  | c :: cs, c' :: cs', .cons hc hcs, ws, h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.pure_def] at h
    cases he : c.1.evaluate x with
    | none => rw [he] at h; cases h
    | some e =>
      rw [he] at h
      simp only [Option.bind_some] at h
      cases hr : cs.mapM (fun c ↦ c.1.evaluate x) with
      | none => rw [hr] at h; cases h
      | some rs =>
        rw [hr] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        rw [← h, List.map_cons, hc.2 x e hx he, mapM_eval hx hcs rs hr]

/-- **`verify_stacked_opening` runs `verifyStackedOpening`**, on claims that are the
statement's, the stack's root the only one read. -/
theorem SimRoots.verifyStackedOpening (stackLog logInvRate : ℕ) (d : Digest)
    {claims : List (StackWeightRust × E)} {claims' : List StackClaim}
    (hc : List.Forall₂ (StackClaimRel stackLog) claims claims') :
    SimRoots (StackRoots stackLog logInvRate d)
      (verifyStackedOpeningRust (digestBits d) stackLog logInvRate claims)
      (verifyStackedOpening stackLog logInvRate claims') fun _ _ ↦ True := by
  have hlen := hc.length_eq
  unfold verifyStackedOpeningRust LeanVM.Protocol.Verifier.verifyStackedOpening
  rw [hlen]
  refine SimRoots.bindE (Sim.require _) (NoCommit.require _) fun _ ↦ ?_
  refine SimRoots.bindE Sim.sample NoCommit.sampleChallenge fun lam ↦ ?_
  have hp : (powersM (limbs lam) claims'.length).map ofLimbsW = powers lam claims'.length := by
    rw [powersM_eq, List.map_map]
    simp [Function.comp_def, ofLimbsW_limbs]
  rw [hp]
  have hv : claims.map (·.2) = claims'.map (·.2) := by
    clear hlen hp
    induction hc with
    | nil => rfl
    | cons h _ ih => rw [List.map_cons, List.map_cons, h.1, ih]
  refine SimRoots.ofOption_bind fun t ht ↦ ?_
  rw [dotRust_some ht, hv]
  refine SimRoots.verifyWhir stackLog logInvRate _ d fun x v hx h ↦ ?_
  simp only [Option.bind_eq_bind] at h
  cases hw : claims.mapM (fun c ↦ c.1.evaluate x) with
  | none => rw [hw] at h; cases h
  | some ws =>
    rw [hw] at h
    simp only [Option.bind_some] at h
    rw [dotRust_some h, mapM_eval hx hc ws hw]

end

end Rv64mc.Model
