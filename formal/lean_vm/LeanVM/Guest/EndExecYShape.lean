/-
  LeanVM.Guest.EndExecYShape

  The honest pushes read the bytecode only through its length: `PushShape`.
-/

module

public import LeanVM.Guest.EndExecY
public import LeanVM.Protocol.Verifier.Phases
public import LeanVM.Protocol.Extraction.Fast.AfterRoot

/-!
# The honest pushes and the bytecode's length

`guestAdvice` builds its streams from `bytecodeShape`, `2^23` zero words, and `Ref.Ok.pops` is
about `End.bytecode`. The pushes read the bytecode only in a child's hints, through the deferring
verifier: its announced layout keeps the words (`buildLayout_len`) but nothing reads them, the
bytecode check comparing the proof's point and value with the claim's (`claimedBytecodeValue`).
So a bytecode of the same length gives the same layout but its words (`announced_len`), the same
deferring program (`deferring_len`), and the same pushes (`honestPushes_len`, `pushShape`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile LeanVM.Guest

public section

variable {b b' : List K}

theorem buildLayout_len (h : b.length = b'.length) (lm : ℕ) (tr : List ℕ) :
    buildLayout b lm tr = (buildLayout b' lm tr).map fun L ↦ { L with bytecode := b } := by
  unfold buildLayout
  rw [h]
  split
  · rfl
  · split_ifs <;> rfl

theorem sizesOf_len (h : b.length = b'.length) (a : List E) :
    sizesOf b a = (sizesOf b' a).map fun x ↦ ({ x.1 with bytecode := b }, x.2) := by
  unfold sizesOf
  simp only [buildLayout_len h]
  split_ifs
  · generalize buildLayout b' _ _ = o
    cases o with
    | none => rfl
    | some L => simp only [Option.map_some, Option.bind_some]; split_ifs <;> rfl
  · rfl
  · rfl

theorem readAnnouncedSizes_len (h : b.length = b'.length) :
    readAnnouncedSizes b = readAnnouncedSizes b' >>= fun x ↦ pure ({ x.1 with bytecode := b }, x.2) := by
  rw [readAnnouncedSizes_eq, readAnnouncedSizes_eq]
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc]
  congr 1
  funext a
  rw [sizesOf_len h a]
  cases sizesOf b' a <;> rfl

/-- **The announced layout of a bytecode of the same length**, but its words. -/
theorem announced_len (h : b.length = b'.length) (st : List E) :
    announcedLayoutAndRate b st = (announcedLayoutAndRate b' st).map fun x ↦ ({ x.1 with bytecode := b }, x.2) := by
  unfold announcedLayoutAndRate
  rw [readAnnouncedSizes_len h, Extraction.Fast.runPure_bind]
  cases runPure (readAnnouncedSizes b') _ <;> rfl

/-- **The deferring verifier on a bytecode of the same length** is the same program. -/
theorem deferring_len (h : b.length = b'.length) (claim : BytecodeClaim) (pi : Digest) :
    deferringVerifierProgram claim b pi = deferringVerifierProgram claim b' pi := by
  unfold deferringVerifierProgram verifyExecution
  rw [readAnnouncedSizes_len h]
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
    VerifierProgram.ret_bind]
  congr 1

theorem childHints_len (h : b.length = b'.length) (seed : Digest) (c : Node.Child) :
    Hints.childHints b seed c = Hints.childHints b' seed c := by
  have hq : Hints.childQueries b seed c = Hints.childQueries b' seed c := by
    unfold Hints.childQueries
    rw [deferring_len h]
  unfold Hints.childHints
  rw [announced_len h, hq]
  cases announcedLayoutAndRate b' c.proof.stream with
  | none => rfl
  | some x => obtain ⟨L, r⟩ := x; rfl

/-- **The honest pushes on a bytecode of the same length.** -/
theorem honestPushes_len (h : b.length = b'.length) (seed : Digest) (s : Node.NodeStatement)
    (w : Node.NodeWitness) : Hints.honestPushes b seed s w = Hints.honestPushes b' seed s w := by
  unfold Hints.honestPushes
  simp only [childHints_len h]

/-- **The honest pushes read the bytecode only through its length.** -/
theorem pushShape : PushShape := fun seed s w ↦
  honestPushes_len (by rw [End.bytecode_length, bytecodeShape, List.length_replicate]) seed s w

end

end LeanVM.Guest.EndExec
