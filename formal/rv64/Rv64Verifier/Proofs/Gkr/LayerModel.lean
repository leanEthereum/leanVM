import Rv64Verifier.Proofs.Gkr.Contracts

/-!
# `keccak::verify_layer`: the mirror in the code's order

`verifyLayerRust` cut where the code calls into the transcript (`stage2` .. `stage7`, `packRest`
for the pack rounds still to run), so that a proof of the code carries the mirror's remaining
run; and the loops the code runs inline, as one step each: sums over a growing range, the powers,
the lane weights' indices.
-/

namespace Rv64Verifier.Gkr.Layer
open LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Model Rv64Verifier.Model.Gkr
  Rv64Verifier.Transcript

/-! ## The stages -/

def stage7 (mu point eqZ eqLane t : List E) : TM KeccakClaim := do
  let beta ← TM.sample
  pure ⟨t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0), mu, point,
    linearTransposeRust (nextWeightsRust eqZ eqLane beta)⟩

abbrev check2 (weights : List E) (kappa scale value : E) (localPt t : List E) : Prop :=
  scale * atLocalRust weights (eqKernelRust (localPt.take 6)) (eqKernelRust (localPt.drop 6)) *
    (kappa * t.getD 0 0 + (kappa + t.getD 1 0) * t.getD 2 0) = value

def stage5 (claim : KeccakClaim) (mu : List E) (kappa scale : E) (point localPt : List E)
    (value : E) : TM KeccakClaim := do
  let t ← TM.nextScalars 3
  TM.require (check2 claim.weights kappa scale value localPt t)
  stage7 mu point (eqKernelRust (localPt.take 6)) (eqKernelRust (localPt.drop 6)) t

def stage4 (claim : KeccakClaim) (mu : List E) (kappa : E) (r : E × E × List E) :
    TM KeccakClaim := do
  let (localPt, value) ← TM.sumcheck r.1 4 (List.replicate keccakLocalBits none)
  stage5 claim mu kappa r.2.1 r.2.2 localPt value

/-- The pack rounds from the `k`-th on, from `acc`, then the rest. -/
def packRest (claim : KeccakClaim) (mu : List E) (kappa : E) (k : Nat) (acc : E × E × List E) :
    TM KeccakClaim :=
  (claim.point.drop k).foldlM packRound acc >>= stage4 claim mu kappa

def stage2 (claim : KeccakClaim) (product : List E) : TM KeccakClaim := do
  let s ← TM.sample
  packRest claim (instanceWeightsRust s) (sumE (instanceWeightsRust s)) 0
    (polyEvalRust product s, 1, [])

abbrev check1 (shape : KeccakShape) (step : Nat) (claim : KeccakClaim) (product : List E) : Prop :=
  projectedRust claim.mu product + iotaRust shape step claim * sumE claim.mu = claim.value

/-! ## Runs -/

variable {α β : Type}

theorem run_bind_some {m : TM α} {f : α → TM β} {T T' : TState} {a : α}
    (h : m.run T = some (a, T')) : (m >>= f).run T = (f a).run T' := by
  simp only [StateT.run_bind, h, Option.bind_eq_bind, Option.bind_some]

theorem run_bind_none {m : TM α} {f : α → TM β} {T : TState} (h : m.run T = none) :
    (m >>= f).run T = none := by
  simp only [StateT.run_bind, h, Option.bind_eq_bind, Option.bind_none]

theorem run_require {c : Prop} [Decidable c] {k : TM α} {T : TState} :
    (TM.require c >>= fun _ ↦ k).run T = if c then k.run T else none := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]
    exact run_bind_some (a := ()) (by simp only [TM.require, StateT.run, hc, ↓reduceIte])
  · simp only [hc, ↓reduceIte]
    exact run_bind_none (by simp only [TM.require, StateT.run, hc, ↓reduceIte])

theorem verifyLayerRust_eq (shape : KeccakShape) (step : Nat) (claim : KeccakClaim) :
    verifyLayerRust shape step claim = (TM.nextScalars productBits >>= fun product ↦
      TM.require (check1 shape step claim product) >>= fun _ ↦ stage2 claim product) := by
  unfold verifyLayerRust stage2 packRest stage4 stage5 stage7 check1 check2
  simp only [List.drop_zero]

theorem stage4_eq (claim : KeccakClaim) (mu : List E) (kappa : E) (r : E × E × List E) :
    stage4 claim mu kappa r = (TM.sumcheck r.1 4 (List.replicate keccakLocalBits none) >>=
      fun lv ↦ stage5 claim mu kappa r.2.1 r.2.2 lv.1 lv.2) := rfl

theorem packRest_succ (claim : KeccakClaim) (mu : List E) (kappa : E) {k : Nat}
    (hk : k < claim.point.length) (acc : E × E × List E) :
    packRest claim mu kappa k acc = (packRound acc (claim.point.getD k 0) >>=
      packRest claim mu kappa (k + 1)) := by
  unfold packRest
  rw [List.drop_eq_getElem_cons hk, List.foldlM_cons, bind_assoc, List.getD_eq_getElem _ _ hk]

theorem packRest_end (claim : KeccakClaim) (mu : List E) (kappa : E) (acc : E × E × List E) :
    packRest claim mu kappa claim.point.length acc = stage4 claim mu kappa acc := by
  unfold packRest
  rw [List.drop_length, List.foldlM_nil, pure_bind]

/-! ## Sums over a growing range -/

theorem sumE_append (l : List E) (x : E) : sumE (l ++ [x]) = sumE l + x := by
  rw [sumE_eq_sum, sumE_eq_sum, List.sum_append, List.sum_singleton]

theorem sumE_map_succ (f : Nat → E) (n : Nat) :
    sumE ((List.range (n + 1)).map f) = sumE ((List.range n).map f) + f n := by
  rw [List.range_succ, List.map_append, List.map_singleton, sumE_append]

theorem sumE_filter_succ (p : Nat → Bool) (f : Nat → E) (n : Nat) :
    sumE (((List.range (n + 1)).filter p).map f) =
      sumE (((List.range n).filter p).map f) + if p n then f n else 0 := by
  rw [List.range_succ, List.filter_append]
  cases h : p n
  · simp only [List.filter_cons, h, List.filter_nil, List.append_nil, Bool.false_eq_true,
      ↓reduceIte, add_zero]
  · simp only [List.filter_cons, h, List.filter_nil, ↓reduceIte, List.map_append, List.map_cons,
      List.map_nil, sumE_append]

theorem sumE_nil : sumE ([] : List E) = 0 := rfl

end Rv64Verifier.Gkr.Layer
