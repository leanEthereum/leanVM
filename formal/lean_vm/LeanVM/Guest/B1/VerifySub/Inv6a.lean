/-
  LeanVM.Guest.B1.VerifySub.Inv6a

  The announced sizes read under any hash, and an accepting deferred run.
-/

module

public import LeanVM.Guest.B1.VerifySub.Inv5
public import LeanVM.Protocol.Verifier

/-!
# The announced sizes and the accepting run

* `RO`: a program that only reads; its result and the stream it leaves do not depend on the hash,
  the chain state, the openings or the roots (`ro_run`), so `announced` is `readSizes`' result
  (`announced_of_runs`);
* `verifyDeferred_inv`: an accepting deferred verifier runs its program from the seed's state to
  an empty stream and no openings.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A program that only reads. -/
inductive RO {α : Type} : Prog α → Prop where
  | ret (a : α) : RO (.ret a)
  | fail : RO .fail
  | read (k : E → Prog α) (h : ∀ x, RO (k x)) : RO (.read k)

theorem RO.bind {α β : Type} {p : Prog α} {f : α → Prog β} (hp : RO p) (hf : ∀ a, RO (f a)) :
    RO (p >>= f) := by
  show RO (p.bind f)
  induction hp with
  | ret a => exact hf a
  | fail => exact .fail
  | read k _ ih => exact .read _ ih

theorem ro_readN : ∀ n, RO (Prog.readN n)
  | 0 => .ret _
  | n + 1 => (RO.read _ fun x => .ret x).bind fun _ => (ro_readN n).bind fun _ => .ret _

theorem ro_require (c : Prop) [Decidable c] : RO (Prog.require c) := by
  unfold Prog.require; split
  · exact .ret _
  · exact .fail

theorem ro_liftOption {α : Type} : ∀ o : Option α, RO (Verifier.liftOption o)
  | none => .fail
  | some a => .ret a

theorem ro_readSizes (bytecode : List K) : RO (readSizes bytecode) := by
  unfold readSizes
  exact (ro_readN _).bind fun _ => (ro_require _).bind fun _ => (ro_require _).bind fun _ =>
    (ro_liftOption _).bind fun _ => (ro_require _).bind fun _ => .ret _

/-- **A reading program's result does not depend on the hash** nor on the chain state, the
openings and the roots. -/
theorem ro_run {α : Type} {p : Prog α} (hp : RO p) (H H' : Bytes → Id Digest) :
    ∀ (cv cv' : Digest) (xs : List E) (os os' : List Opening) (roots roots' : List (Digest × ℕ × ℕ)),
      (Compile.run H p ⟨cv, xs, os, roots⟩).map (fun r => r.1) =
        (Compile.run H' p ⟨cv', xs, os', roots'⟩).map (fun r => r.1) := by
  induction hp with
  | ret a => intros; rfl
  | fail => intros; rfl
  | read k _ ih =>
    intro cv cv' xs os os' roots roots'
    match xs with
    | [] => rfl
    | x :: xs => exact ih x _ _ xs os os' roots roots'

/-- **`announced` is `readSizes`' result.** -/
theorem announced_of_runs {bytecode : List K} {cv : Digest} {xs : List E} {os : List Opening}
    {roots : List (Digest × ℕ × ℕ)} {lr : Layout × ℕ} {s' : St}
    (h : Runs (readSizes bytecode) ⟨cv, xs, os, roots⟩ lr s') : announced bytecode xs = some lr := by
  unfold announced
  have := ro_run (ro_readSizes bytecode) (fun _ ↦ pure default) blake2sBytes default cv xs [] os [] roots
  unfold Runs runId at h
  simp only [Id.run]
  rw [this, h]
  rfl

/-- **An accepting deferred verifier** runs its program to an empty stream and no openings. -/
theorem verifyDeferred_inv {bytecode : List K} {seed pi : Digest} {c : FixedClaims} {π : Proof}
    (h : verifyDeferred bytecode seed pi c π = true) :
    ∃ s', Runs (deferredProgram c bytecode pi)
      ⟨blake2sBytes (digestBytes seed ++ digestBytes pi), π.stream, π.openings, []⟩ true s' ∧
      s'.stream = [] ∧ s'.openings = [] := by
  unfold verifyDeferred verifyDeferredWith runProof at h
  simp only [Id.run, bind] at h
  split at h
  · rename_i s' hr
    simp only [pure, Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨s', hr, h.1, h.2⟩
  · cases h

end
end LeanVM.Guest.B1.VerifySub
