module

public import NativeVm.Model.Whir
public import NativeVm.Code.Phase7.FoldRow

/-!
# The stacked opening as the code runs it

`whirLevels` level by level: the non-final levels as one step each (`levelM`, the glued state it
returns), the final level (`finalM`), and the ladder as a fold of the non-final levels then the final
one (`whirLevels_fold`), the shape the code's level loop refines (`Refines.foldlM`).
-/

@[expose] public section

namespace NativeVm.Code.P7

open NativeVm.Model LeanVM.Parameters

/-- The batched value of a non-final level's queries. -/
def batchedW (index mu : Nat) (rounds : Array FoldRoundW) (high : Array EW) (queries : Array UInt64)
    (words : Array (Array UInt64)) (queryWeights : Array EW) : EW :=
  let table := subspaceTable mu
  sumE (Array.zipWith (fun (query, row) queryWeight ↦
    let what := subspaceAtTable table query
    queryWeight * (foldRow (lanesW index row) query rounds +
      EW.scale (what.getD mu 0) (novelEval high what))) (queries.zip words) queryWeights)

/-- **A non-final level** `index` (`level`, then `next`): its fold rounds, the next commitment,
the out-of-domain sample, the queries; the glued state. -/
def levelM (logN index : Nat) (level next : Whir.Level) (s : WhirStateW) : VM WhirStateW := do
  let (s, rounds) ← foldRounds level.fold s
  let mu := logN - s.alphas.size
  let depth := mu + level.logInvRate
  let (height, width) := levelShape mu next (2 * 2 ^ next.fold)
  readCommitment height width
  let high ← readScalars level.fold
  grind Whir.oodGrindingBits
  let oodPoint ← sampleChallenges mu
  let oodValue ← readScalar
  grind Whir.queryGrindingBits
  let queries ← sampleQueries depth level.queries
  let lam ← sampleChallenge
  let queryWeights := powers lam queries.size
  let words ← queryOpenings index queries
  pure (glueLevel s lam mu oodPoint oodValue queries queryWeights
    (batchedW index mu rounds high queries words queryWeights))

/-- The final check of the queries. -/
def finalOkW (index mu : Nat) (rounds : Array FoldRoundW) (folded : Array EW)
    (queries : Array UInt64) (words : Array (Array UInt64)) : Bool :=
  let table := subspaceTable mu
  (queries.zip words).all fun (query, row) ↦
    foldRow (lanesW index row) query rounds == novelEval folded (subspaceAtTable table query)

/-- The final weight at the sumcheck's point. -/
def finalWeightW (laneFolds : Nat) (basis : BasisW) (s : WhirStateW) (tail : Array EW) : EW :=
  let point := s.alphas ++ tail
  s.glued.foldl
    (fun weight glued ↦
      weight + glued.scalar * glued.weight.eval (point.extract glued.foldStart point.size))
    (basis.eval (point.extract laneFolds point.size ++ point.extract 0 laneFolds))

/-- **The final level** `index`: its fold rounds, the folded polynomial, the queries, the final
sumcheck and the weight's check. -/
def finalM (logN laneFolds : Nat) (basis : BasisW) (index : Nat) (level : Whir.Level)
    (s : WhirStateW) : VM Unit := do
  let (s, rounds) ← foldRounds level.fold s
  let mu := logN - s.alphas.size
  let depth := mu + level.logInvRate
  let folded ← readScalars (2 ^ mu + level.fold)
  grind Whir.queryGrindingBits
  let queries ← sampleQueries depth level.queries
  let words ← queryOpenings index queries
  require (finalOkW index mu rounds folded queries words)
  let (tail, claim) ← sumcheckPlain s.claim 3 mu
  require (finalWeightW laneFolds basis s tail * multilinearEval (folded.extract 0 (2 ^ mu)) tail
    == claim)

theorem whirLevels_cons_cons (logN laneFolds : Nat) (basis : BasisW) (index : Nat)
    (level next : Whir.Level) (rest : List Whir.Level) (s : WhirStateW) :
    whirLevels logN laneFolds basis index (level :: next :: rest) s =
      levelM logN index level next s >>= whirLevels logN laneFolds basis (index + 1) (next :: rest) := by
  simp only [whirLevels, levelM, bind_assoc, pure_bind]
  rfl

theorem whirLevels_single (logN laneFolds : Nat) (basis : BasisW) (index : Nat)
    (level : Whir.Level) (s : WhirStateW) :
    whirLevels logN laneFolds basis index [level] s = finalM logN laneFolds basis index level s := by
  simp only [whirLevels, finalM]
  rfl

/-- The non-final levels' step, by index into the ladder. -/
def levelAt (logN : Nat) (L : List Whir.Level) (s : WhirStateW) (k : Nat) : VM WhirStateW :=
  levelM logN k (L.getD k ⟨0, 0, 0⟩) (L.getD (k + 1) ⟨0, 0, 0⟩) s

theorem getD_lt {α : Type} {L : List α} {k : Nat} (h : k < L.length) (d : α) :
    L.getD k d = L[k] := by
  simp [List.getD, h]

theorem drop_getD {α : Type} {L : List α} {k : Nat} (h : k < L.length) (d : α) :
    L.drop k = L.getD k d :: L.drop (k + 1) := by
  rw [getD_lt h, List.drop_eq_getElem_cons h]

theorem whirLevels_from (logN laneFolds : Nat) (basis : BasisW) (L : List Whir.Level) :
    ∀ n k, k + 1 + n = L.length → ∀ s,
      whirLevels logN laneFolds basis k (L.drop k) s =
        (List.range' k n).foldlM (levelAt logN L) s >>= fun s ↦
          finalM logN laneFolds basis (k + n) (L.getD (k + n) ⟨0, 0, 0⟩) s
  | 0, k, hk, s => by
    have hd : L.drop k = [L.getD k ⟨0, 0, 0⟩] := by
      rw [drop_getD (by omega) ⟨0, 0, 0⟩, List.drop_eq_nil_of_le (by omega)]
    rw [hd, whirLevels_single, List.range'_zero, List.foldlM_nil, pure_bind, Nat.add_zero]
  | n + 1, k, hk, s => by
    rw [drop_getD (by omega) ⟨0, 0, 0⟩, drop_getD (k := k + 1) (by omega) ⟨0, 0, 0⟩,
      whirLevels_cons_cons, List.range'_succ, List.foldlM_cons, bind_assoc]
    congr 1
    funext s'
    have := whirLevels_from logN laneFolds basis L n (k + 1) (by omega) s'
    rw [drop_getD (k := k + 1) (by omega) ⟨0, 0, 0⟩,
      show k + 1 + n = k + (n + 1) by omega] at this
    exact this

/-- **The ladder as the code runs it**: the non-final levels by a fold, then the final one. -/
theorem whirLevels_fold (logN laneFolds : Nat) (basis : BasisW) (L : List Whir.Level)
    (hL : 1 ≤ L.length) (s : WhirStateW) :
    whirLevels logN laneFolds basis 0 L s =
      (List.range (L.length - 1)).foldlM (levelAt logN L) s >>= fun s ↦
        finalM logN laneFolds basis (L.length - 1) (L.getD (L.length - 1) ⟨0, 0, 0⟩) s := by
  have := whirLevels_from logN laneFolds basis L (L.length - 1) 0 (by omega) s
  rw [List.drop_zero, Nat.zero_add] at this
  rw [this, List.range_eq_range']

theorem require_true {c : Bool} (h : c = true) : Model.require c = pure () := by
  rw [h]; rfl

theorem liftOpt_some {α : Type} {a : α} : Model.liftOpt (some a) = pure a := rfl

/-- **The stacked opening as the code runs it**: the batching challenge, the non-final levels by a
fold, the final level. -/
theorem verifyStackedOpening_eq {logN rate : Nat} {cl : Array StackClaimW} {L : List Whir.Level}
    (hL : Whir.ladder logN rate = some L) (hcl : cl.size ≤ LeanVM.Protocol.Verifier.maxStackedClaims) (hlen : 1 ≤ L.length)
    (hhead : (L.head?.map (·.fold)).getD 0 = Whir.initialFold) :
    verifyStackedOpening logN rate cl = (Model.sampleChallenge >>= fun lam ↦
      (List.range (L.length - 1)).foldlM (levelAt logN L)
          ⟨dot (powers lam cl.size) (cl.map (·.value)), #[], #[]⟩ >>= fun s ↦
        finalM logN Whir.initialFold ⟨powers lam cl.size, cl⟩ (L.length - 1)
          (L.getD (L.length - 1) ⟨0, 0, 0⟩) s) := by
  unfold verifyStackedOpening verifyWhir
  rw [require_true (decide_eq_true hcl), pure_bind]
  congr 1
  funext lam
  rw [hL, liftOpt_some, pure_bind, hhead, whirLevels_fold _ _ _ _ hlen]

end NativeVm.Code.P7
