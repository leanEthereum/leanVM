/-
  LeanVM.Guest.Batch.Node

  `NodeRelation` gives the node's deferred claim the split program's shape: the zero point's, or
  the batching sumcheck's challenges.
-/

module

public import Statement.LeanVmGuest
public import LeanVM.Protocol.Compile.Prog
public import LeanVM.Guest.BatchConsts

/-!
# The deferred claim's shape

`DeferredClaimBatched` (`Statement/LeanVmGuest.lean`) has a node without children defer the split
program at the zero point, and a node with children run the batching program
(`nodeBatchingProgram`) with the check that its outcome is the statement's deferred claim. An
accepting run returns `true` only past that check, at the sumcheck's `deferredVariableCount`
challenges (`retsIn_nodeBatching`), so the deferred claim has the split program's shape
(`NodeRelation.hasBytecodeShape`), which `statementDigestBinds` asks of a decoded statement.

`RetsIn Q p`: every value `p` returns satisfies `Q`. It composes through `bind` (`RetsIn.bind`),
and a run that returns a value returns one of them (`RetsIn.of_run`), whatever the sponge and the
proof.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The values a program returns -/

/-- **Every value `p` returns satisfies `Q`.** -/
def RetsIn {α : Type} (Q : α → Prop) : VerifierProgram α → Prop
  | .ret a => Q a
  | .fail => True
  | .read k => ∀ x, RetsIn Q (k x)
  | .sample k => ∀ x, RetsIn Q (k x)
  | .readPacked _ k => ∀ xs, RetsIn Q (k xs)
  | .samplePacked _ k => ∀ xs, RetsIn Q (k xs)
  | .grind _ k => RetsIn Q k
  | .commit _ _ k => RetsIn Q k
  | .query _ _ k => ∀ rows, RetsIn Q (k rows)

/-- Sequencing: the continuation on every value the first part returns. -/
theorem RetsIn.bind {α β : Type} {Q : α → Prop} {R : β → Prop} {p : VerifierProgram α}
    {f : α → VerifierProgram β} (hp : RetsIn Q p) (hf : ∀ a, Q a → RetsIn R (f a)) :
    RetsIn R (p.bind f) := by
  induction p with
  | ret a => exact hf a hp
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | readPacked n k ih => exact fun xs ↦ ih xs (hp xs)
  | samplePacked n k ih => exact fun xs ↦ ih xs (hp xs)
  | grind b k ih => exact ih hp
  | commit h w k ih => exact ih hp
  | query i ps k ih => exact fun rows ↦ ih rows (hp rows)

/-- Every program returns values that satisfy `True`. -/
theorem retsIn_true {α : Type} (p : VerifierProgram α) : RetsIn (fun _ ↦ True) p := by
  induction p with
  | ret a => trivial
  | fail => trivial
  | read k ih => exact ih
  | sample k ih => exact ih
  | readPacked n k ih => exact ih
  | samplePacked n k ih => exact ih
  | grind b k ih => exact ih
  | commit h w k ih => exact ih
  | query i ps k ih => exact ih

theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

/-- **A run returns what the program returns**: over a permutation `π`, deployed or not. -/
theorem RetsIn.of_run {α : Type} {Q : α → Prop} (π : KeccakState → KeccakState) :
    ∀ {p : VerifierProgram α} {s : VerifierProgramState} {a : α} {s' : VerifierProgramState},
      RetsIn Q p → Compile.run (m := Id) π p s = some (a, s') → Q a := by
  intro p
  induction p with
  | ret a =>
    intro s a' s' hp hr
    have h : some (a, s) = some (a', s') := hr
    cases h
    exact hp
  | fail => intro s a s' _ hr; simp [Compile.run, pure] at hr
  | read k ih =>
    intro s a s' hp hr
    simp only [Compile.run] at hr
    split at hr
    · exact ih _ (hp _) hr
    · simp [pure] at hr
  | sample k ih =>
    intro s a s' hp hr
    simp only [Compile.run] at hr
    exact ih _ (hp _) hr
  | readPacked n k ih =>
    intro s a s' hp hr
    simp only [Compile.run] at hr
    split at hr
    · exact ih _ (hp _) hr
    · simp [pure] at hr
  | samplePacked n k ih =>
    intro s a s' hp hr
    simp only [Compile.run] at hr
    exact ih _ (hp _) hr
  | grind b k ih =>
    intro s a s' hp hr
    simp only [Compile.run] at hr
    split at hr
    · rw [id_bind] at hr
      split at hr
      · exact ih hp hr
      · simp [pure] at hr
    · simp [pure] at hr
  | commit h w k ih =>
    intro s a s' hp hr
    simp only [Compile.run] at hr
    split at hr
    · exact ih hp hr
    · simp [pure] at hr
  | query i ps k ih =>
    intro s a s' hp hr
    simp only [Compile.run] at hr
    split at hr
    · rw [id_bind] at hr
      split at hr
      · exact ih _ (hp _) hr
      · simp [pure] at hr
    · simp [pure] at hr

/-! ## The batching's returns -/

theorem retsIn_ret {α : Type} {Q : α → Prop} {a : α} (h : Q a) : RetsIn Q (VerifierProgram.ret a) :=
  h

theorem retsIn_require (q : Prop) (inst : Decidable q) :
    RetsIn (fun _ ↦ q) (@VerifierProgram.require q inst) := by
  unfold VerifierProgram.require
  split
  · assumption
  · trivial

/-- The rounds return their challenges, one per round. -/
theorem retsIn_roundsProg : ∀ (k : ℕ) (claim : E),
    RetsIn (fun r ↦ r.1.length = k) (sumcheckRoundsProgram claim k)
  | 0, _ => rfl
  | k + 1, _ => by
    rw [sumcheckRoundsProgram_succ]
    exact fun _ _ _ ↦ (retsIn_roundsProg k _).bind fun r hr ↦ retsIn_ret (by
      show (_ :: r.1).length = k + 1
      rw [List.length_cons, hr])

/-- **The batching returns `true` only past its check**, at the sumcheck's challenges. -/
theorem retsIn_batchingAfterChildren (check : DeferredBytecodeClaim → Prop) (bytecode : List K)
    (cs : List ChildClaims) :
    RetsIn (fun b ↦ b = true → ∃ d : DeferredBytecodeClaim, check d ∧
        d.bytecodePoint.length = deferredVariableCount bytecode)
      (batchingAfterChildren check bytecode cs) := by
  unfold batchingAfterChildren
  refine (retsIn_true _).bind fun _ _ ↦ (retsIn_true _).bind fun _ _ ↦ (retsIn_true _).bind
    fun _ _ ↦ (retsIn_roundsProg _ _).bind fun r hr ↦ (retsIn_true _).bind fun fv _ ↦
      (retsIn_require _ _).bind fun _ hq ↦ retsIn_ret fun _ ↦ ⟨⟨r.1, fv⟩, hq.2, hr⟩

theorem retsIn_nodeBatching (check : DeferredBytecodeClaim → Prop) (bytecode : List K)
    (cs : List ChildClaims) :
    RetsIn (fun b ↦ b = true → ∃ d : DeferredBytecodeClaim, check d ∧
        d.bytecodePoint.length = deferredVariableCount bytecode)
      (nodeBatchingProgram check bytecode cs) := by
  unfold nodeBatchingProgram
  exact (retsIn_true _).bind fun _ _ ↦ (retsIn_require _ _).bind fun _ _ ↦
    retsIn_batchingAfterChildren check bytecode cs

/-! ## The deferred claim's shape -/

/-- The batching transcript run over `π`, in `Id`: the program from the label's seed. -/
theorem runBatching_id (π : KeccakState → KeccakState) (program : VerifierProgram Bool)
    (proof : Proof) :
    runBatching (m := Id) π program proof =
      match Compile.run (m := Id) π program
          ⟨⟨π (seedInput (keccak256With (m := Id) π batchingLabel) (Vector.replicate 4 0)), [], none⟩,
            proof.stream, proof.openings, []⟩ with
      | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
      | _ => false := rfl

/-- **The batched deferred claim has the split program's shape**: the zero point's, or the
batching sumcheck's challenges. -/
theorem _root_.LeanVM.Node.DeferredClaimBatched.hasBytecodeShape {bytecode : List K}
    {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hb : DeferredClaimBatched bytecode seed s w) : s.deferredClaim.HasBytecodeShape bytecode := by
  unfold DeferredClaimBatched at hb
  split at hb
  · unfold DeferredBytecodeClaim.HasZeroPoint at hb
    rw [DeferredBytecodeClaim.HasBytecodeShape, hb, List.length_replicate]
  · dsimp only at hb
    rw [runBatching_id] at hb
    split at hb
    · rename_i r st hr
      obtain ⟨d, rfl, hd⟩ := RetsIn.of_run keccakF1600 (retsIn_nodeBatching _ _ _) hr rfl
      exact hd
    · simp at hb

/-- **A node's deferred claim has the split program's shape**, under `NodeRelation`. -/
theorem _root_.LeanVM.Node.NodeRelation.hasBytecodeShape {bytecode : List K} {seed : Digest}
    {s : NodeStatement} {w : NodeWitness} (h : NodeRelation bytecode seed s w) :
    s.deferredClaim.HasBytecodeShape bytecode :=
  DeferredClaimBatched.hasBytecodeShape h.2.2.2

end
end LeanVM.Guest.Batch
