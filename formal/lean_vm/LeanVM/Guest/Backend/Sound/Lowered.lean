/-
  LeanVM.Guest.Backend.Sound.Lowered

  Emission and assembly together: a halting run of the assembled program that enters a function
  has the meaning of the function's placed body.
-/

module

public import LeanVM.Guest.Backend.Sound.Run
public import LeanVM.Guest.Backend.Sound.Asm

/-!
# The assembled program runs the placed bodies

`lowered_sound` composes the two passes after placement. For labelled functions with distinct
names, assembled with any jump table slots, and a function `f` of them whose code is the emitted
code of a placed body (`opsOf f.code = blockOps body 0`, which `emitFn_ops` gives): a run of the
statement's program `LeanVM.Guest.assemble a.toFunctions logSize` that reaches `f`'s entry at a
frame `fp` and halts after `k ≤ n` steps satisfies `PStmt.SemList body`, given every function's
contract for runs shorter than `n`. Nothing is assumed of the placed body: this half of the
back end is correct for every placed program, whatever placement produced it.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

@[expose] public section

/-- The program of an assembled back end output, as the statement reads a program's functions. -/
def Assembled.program (a : Assembled) (logSize : ℕ) (hl : logSize ≤ maxLogBytecode) :
    LeanIsaProgram :=
  Guest.assemble a.toFunctions logSize hl

/-- A function of the laid out program on a memory, with the contracts of its callees. -/
def siteOf {κ : ℕ} (L : MemoryImage κ) (fns : List Lowered) (slots : Array KVal)
    (pre : List Lowered) (f : Lowered) (Pre Post : String → K → Prop) : Site κ :=
  ⟨L, layoutOf fns slots, totalSize pre, f.frameSize, Pre, Post⟩

/-- The assembled program holds each function's code at its entry. -/
theorem loaded_of_assemble {κ : ℕ} (L : MemoryImage κ) {fns : List Lowered} {slots : Array KVal}
    {pre post : List Lowered} {f : Lowered}
    (hnd : ((withTables fns slots).1.map (·.name)).Nodup)
    (hsplit : (withTables fns slots).1 = pre ++ f :: post) {logSize : ℕ}
    (hl : logSize ≤ maxLogBytecode) (hsize : (assemble fns slots).size = 2 ^ logSize)
    (Pre Post : String → K → Prop) :
    Loaded ((assemble fns slots).program logSize hl) (siteOf L fns slots pre f Pre Post)
      (opsOf f.code) := by
  obtain ⟨hfetch, hfit⟩ := assemble_fetch hnd hsplit hl hsize
  refine ⟨fun i hi => ?_, by rw [opsOf_length]; exact hfit⟩
  have hi' : i < f.code.size := by simpa [opsOf_length] using hi
  have := hfetch i hi'
  simpa [opsOf, Site.R, siteOf, Assembled.program] using this

/-- **Emission and assembly are sound**: a halting run of the assembled program from a
function's entry has the meaning of the function's placed body. -/
theorem lowered_sound {κ : ℕ} (L : MemoryImage κ) {fns : List Lowered} {slots : Array KVal}
    {pre post : List Lowered} {f : Lowered} {body : List PStmt}
    (hnd : ((withTables fns slots).1.map (·.name)).Nodup)
    (hsplit : (withTables fns slots).1 = pre ++ f :: post)
    (hcode : opsOf f.code = blockOps body 0) {logSize : ℕ} (hl : logSize ≤ maxLogBytecode)
    (hsize : (assemble fns slots).size = 2 ^ logSize) (Pre Post : String → K → Prop) {n : ℕ}
    (hC : ∀ g, FunSpecLtReached ((assemble fns slots).program logSize hl) L n
      ((siteOf L fns slots pre f Pre Post).ent g) (Pre g) (Post g))
    {fp : K} {k : ℕ} (hk : k ≤ n)
    (hs : SafeReached ((assemble fns slots).program logSize hl) L k
      ⟨addressOfIndex (totalSize pre), fp⟩)
    {next : Prop} {kj : E → E → Prop} {kret : Prop} {khalt : E → E → Prop}
    (hnext : NextOK ((assemble fns slots).program logSize hl) (siteOf L fns slots pre f Pre Post)
      fp k (blockSize body) next)
    (hjump : JumpOK ((assemble fns slots).program logSize hl) (siteOf L fns slots pre f Pre Post)
      k kj)
    (hret : RetOK ((assemble fns slots).program logSize hl) (siteOf L fns slots pre f Pre Post)
      fp k kret)
    (hhalt : JumpOK ((assemble fns slots).program logSize hl) (siteOf L fns slots pre f Pre Post)
      k khalt) :
    PStmt.SemList (siteOf L fns slots pre f Pre Post) fp body 0 next kj kret khalt := by
  have hL := loaded_of_assemble L hnd hsplit hl hsize Pre Post
  refine PStmt.semList_of_run hL hC body 0 k next kj kret khalt ?_ hk ?_ ?_ hjump hret hhalt
  · rw [← hcode]
    exact codeAt_self _
  · simpa [SafeAt, siteOf] using hs
  · simpa using hnext

end
end LeanVM.Guest.Backend
