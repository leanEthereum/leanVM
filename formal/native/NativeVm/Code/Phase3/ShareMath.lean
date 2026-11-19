module

public import NativeVm.Model.Bus
public import NativeVm.Equiv.Field

/-!
# The bytecode share: the model's facts

The plain-mode rounds of `bytecodeShare` grind no bits (`share_grindingBits`), so a round is two
reads, a challenge and the round polynomial's value (`share_round_run`); and the check's dot
product with the equality kernel at the four-coordinate slot is the weights' multilinear
extension there (`share_dot_eqKernel`), which `emle` computes.
-/

@[expose] public section

namespace NativeVm.Code.P3

open NativeVm.Model NativeVm.Equiv LeanVM.Parameters LeanVM.Protocol
open LeanVM.Protocol.Verifier (busBits)

/-- The plain rounds' grind, `grindingBits (3 - 1)`, has no bits.  -/
theorem share_grindingBits : grindingBits (3 - 1) = 0 := by decide

/-- A plain round of `sumcheckPlain _ 3`, as the code runs it. -/
def shareRoundM (acc : Array EW × EW) : VM (Array EW × EW) := do
  let c ← readScalar
  let tt ← readScalar
  let x ← sampleChallenge
  pure (acc.1.push x, polyEval #[c, acc.2 + sumE #[tt], tt] x)

theorem readScalars_one_run (t : TState) :
    (readScalars 1).run t = (readScalar.run t).map fun p ↦ (#[p.1], p.2) := by
  unfold readScalars
  simp only [List.range_one, List.foldlM_cons, List.foldlM_nil, StateT.run_bind, StateT.run_pure]
  cases readScalar.run t <;> rfl

theorem grind0_run (t : TState) : (grind 0).run t = some ((), t) := (rfl)

/-- **A plain round** is `shareRoundM`. -/
theorem share_round_run (acc : Array EW × EW) (t : TState) :
    (do
      let message ← sumcheckRoundPoly 3 acc.2 none
      let challenge ← sampleChallenge
      pure (acc.1.push challenge, polyEval message challenge) : VM (Array EW × EW)).run t =
      (shareRoundM acc).run t := by
  unfold sumcheckRoundPoly shareRoundM
  rw [share_grindingBits]
  simp only [StateT.run_bind, StateT.run_pure, show 3 - 2 = 1 from rfl, readScalars_one_run]
  cases readScalar.run t with
  | none => rfl
  | some p =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    rcases readScalar.run p.2 with _ | q
    · rfl
    · simp only [Option.map_some, Option.bind_some, grind0_run, Option.pure_def]
      rfl

theorem foldlM_replicate_congr {β : Type} {f g : β → Option EW → VM β}
    (h : ∀ acc, f acc none = g acc none) : ∀ (n : Nat) (init : β),
    (List.replicate n none).foldlM f init = (List.replicate n none).foldlM g init
  | 0, _ => rfl
  | n + 1, init => by
    simp only [List.replicate_succ, List.foldlM_cons, h, foldlM_replicate_congr h n]

/-- The sumcheck of `bytecodeShare` is a fold of `shareRoundM` over four rounds. -/
theorem share_sumcheck_run (share : EW) (t : TState) :
    (sumcheckPlain share 3 busBits).run t =
      ((List.replicate 4 (none : Option EW)).foldlM (fun acc _ ↦ shareRoundM acc)
        (#[], share)).run t := by
  unfold sumcheckPlain sumcheck
  rw [← Array.foldlM_toList, Array.toList_replicate, show busBits = 4 by decide,
    foldlM_replicate_congr (g := fun acc _ ↦ shareRoundM acc) (fun acc ↦ ?_)]
  funext t
  exact share_round_run acc t

/-- **The check's dot product** is the weights' multilinear extension at the slot. -/
theorem share_dot_eqKernel {p w : Array EW} (hp : p.size = 4) (hw : w.size = 16) :
    (dot (eqKernel p) w).toE = (multilinearEval w p).toE := by
  rw [toE_dot, toList_map_eqKernel, toE_multilinearEval]
  obtain ⟨p0, p1, p2, p3, hp'⟩ : ∃ a b c d, p.toList.map EW.toE = [a, b, c, d] := by
    rcases p with ⟨l⟩
    simp only [List.size_toArray] at hp
    match l, hp with
    | [a, b, c, d], _ => exact ⟨_, _, _, _, rfl⟩
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, hw'⟩ :
      ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15, w.toList.map EW.toE =
        [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := by
    rcases w with ⟨l⟩
    simp only [List.size_toArray] at hw
    match l, hw with
    | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15], _ =>
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  rw [hp', hw']
  simp only [Verifier.eqKernel, Verifier.dot, Verifier.multilinearEval, Verifier.foldPairs,
    List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.zipWith_cons_cons, List.zipWith_nil_left, List.headD_cons]
  ring

/-- The round polynomial's value at the challenge, as the code computes it. -/
theorem sh_poly (c cl tt x : EW) :
    (polyEval #[c, cl + sumE #[tt], tt] x).toE =
      ((tt.toE * x.toE + cl.toE) + tt.toE) * x.toE + c.toE := by
  rw [toE_polyEval]
  show Verifier.polyEval [c.toE, (cl + sumE #[tt]).toE, tt.toE] x.toE = _
  rw [EW.toE_add, toE_sumE]
  show ((0 * x.toE + tt.toE) * x.toE + (cl.toE + (0 + tt.toE))) * x.toE + c.toE = _
  ring

end NativeVm.Code.P3
