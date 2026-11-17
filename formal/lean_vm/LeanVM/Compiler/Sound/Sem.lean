/-
  LeanVM.Compiler.Sound.Sem

  The meaning of the placed IR: what a halting run through a placed statement's instructions
  checks of the memory, by structural recursion on the statement.
-/

module

public import LeanVM.Compiler.Sound.Ops
public import LeanVM.Compiler.Assemble
public import LeanVM.Guest.Logic

/-!
# The meaning of a placed statement

`PStmt.Sem Γ fp s pos next kj kret khalt` is what a halting run entering instruction `pos` of a
function at frame `fp` checks of the one memory `Γ.L`, in continuation form as the core IR's
`Stmt.Holds` is: `next` after the statement's last instruction, `kret` after a return, `kj d f`
after a taken jump whose target cells hold the words `d` and `f`, `khalt d f` after `main`'s
closing jump.

It is read off the instructions alone, so it claims nothing the instructions do not check. Where
a jump goes depends on what its cells hold, which emission does not know: every continuation of a
taken jump is under the hypotheses that name its target (the target cell holds the pc meant, the
frame cell holds this frame's pointer, a callee's frame holds the return registers, the callee's
precondition holds). Placement discharges them from the facts of the instructions before
(`Sound.Place`), and `PStmt.sem_of_run` proves the meaning of a run with no invariant at all.

* a straight-line instruction is `Guest.Holds` of its resolved form;
* `ite`: the branch taken by the condition word, the `else` block entered at its own pc;
* `chain`: a jump into any arm of any stage (`StagesJump`), an arm's exit a jump into a later
  stage or to the join;
* `call`, `loopNext`, `dispatch`: the callee's postcondition at the frame the jump names, then
  the returned words read back, or this frame's return for a tail call.
-/

namespace LeanVM.Compiler

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

@[expose] public section

/-- A function's code in a laid out program, on one memory: the layout, the function's entry and
frame size, and the contracts of the functions it calls, by name. -/
structure Site (κ : ℕ) where
  L : MemoryImage κ
  l : Layout
  pc0 : ℕ
  frame : ℕ
  Pre : String → K → Prop
  Post : String → K → Prop

variable {κ : ℕ} (Γ : Site κ) (fp : K)

/-- An instruction of the function, resolved. -/
def Site.R (o : LOp) : OffsetInstruction := resolveOp Γ.l Γ.pc0 Γ.frame o

/-- A function's entry. -/
def Site.ent (f : String) : ℕ := Γ.l.entry.getD f 0

/-- The word of the pc of instruction `q` of the function. -/
def Site.tgt (q : ℕ) : E := ofK (addressOfIndex (Γ.pc0 + q))

/-- The instructions `ops`, none a jump, the first at instruction `pos`, hold. -/
def SegHolds (ops : List LOp) (pos : ℕ) : Prop :=
  ∀ i (h : i < ops.length), Holds Γ.L (Γ.pc0 + pos + i) fp (Γ.R ops[i])

/-- A `JUMP`: its three cells hold words of `K`; `fall` if the condition is zero, else `taken`
of the target words. -/
def JumpAt (oc od of : ℕ) (fall : Prop) (taken : E → E → Prop) : Prop :=
  ∃ c d f, Γ.L.read (fp * addressOfIndex oc) = some c ∧
    Γ.L.read (fp * addressOfIndex od) = some d ∧ Γ.L.read (fp * addressOfIndex of) = some f ∧
    IsInK c ∧ IsInK d ∧ IsInK f ∧ (c = 0 → fall) ∧ (c ≠ 0 → taken d f)

/-- One instruction at `pos`. -/
def OpSem (o : LOp) (pos : ℕ) (next : Prop) (kj : E → E → Prop) : Prop :=
  match o with
  | .jump oc od of => JumpAt Γ fp oc od of next kj
  | o => Holds Γ.L (Γ.pc0 + pos) fp (Γ.R o) ∧ next

/-- What a taken call's jump to `(d, f)` gives: under the callee's entry in `d`, its
precondition at the frame `f` names and the return registers `ret` there, its postcondition and
`k`. -/
def CallSem (callee : String) (ret : Option (Registers K)) (k : Prop) (d f : E) : Prop :=
  d = ofK (addressOfIndex (Γ.ent callee)) → Γ.Pre callee (f.limb 0) →
    retRegs Γ.L (f.limb 0) = ret → Γ.Post callee (f.limb 0) ∧ k

mutual
/-- The meaning of a placed statement whose first instruction is `pos`. -/
def PStmt.Sem : PStmt → ℕ → Prop → (E → E → Prop) → Prop → (E → E → Prop) → Prop
  | .op _ o, pos, next, kj, _, _ => OpSem Γ fp o pos next kj
  | .ite _ c bdest sfp zero hasElse edest one nonzero, pos, next, kj, kret, khalt =>
      Holds Γ.L (Γ.pc0 + pos) fp (Γ.R (.set bdest (.local (elseAt pos zero hasElse)))) ∧
      JumpAt Γ fp c bdest sfp
        (PStmt.SemList zero (pos + 2)
          (if hasElse then
            Holds Γ.L (Γ.pc0 + (pos + 2 + blockSize zero)) fp
              (Γ.R (.set edest (.local (elseAt pos zero hasElse + blockSize nonzero)))) ∧
            JumpAt Γ fp one edest sfp
              (PStmt.SemList nonzero (elseAt pos zero hasElse) next kj kret khalt)
              (fun d f => d = Γ.tgt (elseAt pos zero hasElse + blockSize nonzero) → f = ofK fp →
                next)
           else next) kj kret khalt)
        (fun d f => d = Γ.tgt (elseAt pos zero hasElse) → f = ofK fp →
          if hasElse then PStmt.SemList nonzero (elseAt pos zero hasElse) next kj kret khalt
          else next)
  | .chain _ join x entry one sfp firsts stages, pos, next, _, kret, khalt =>
      Holds Γ.L (Γ.pc0 + pos) fp (Γ.R (.set join (.local (pos + 3 + stagesSize stages)))) ∧
      Holds Γ.L (Γ.pc0 + pos + 1) fp (Γ.R (.slot x (firsts.headD 0) entry)) ∧
      JumpAt Γ fp one entry sfp True (PStmt.StagesJump stages (pos + 3) next kret khalt)
  | .call _ c, pos, next, _, kret, _ =>
      SegHolds Γ fp (callPre c) pos ∧
      JumpAt Γ fp c.oc c.entry c.nfp
        (SegHolds Γ fp (callRets c.nfp c.args.length c.rets) (pos + (callPre c).length + 1) ∧ next)
        (if c.tail then CallSem Γ c.callee (retRegs Γ.L fp) kret
         else CallSem Γ c.callee
          (some ⟨addressOfIndex (Γ.pc0 + (pos + (callPre c).length + 1)), fp⟩)
          (SegHolds Γ fp (callRets c.nfp c.args.length c.rets) (pos + (callPre c).length + 1) ∧
            next))
  | .loopNext _ callee nfp entry oc one args, pos, next, _, kret, _ =>
      SegHolds Γ fp (loopPre callee nfp entry one args) pos ∧
      JumpAt Γ fp oc entry nfp next (CallSem Γ callee (retRegs Γ.L fp) kret)
  | .dispatch _ callees nfp joinCell x entry one first args rets, pos, next, _, _, _ =>
      SegHolds Γ fp (dispatchPre pos nfp joinCell x entry first args) pos ∧
      JumpAt Γ fp one entry nfp True
        (fun d f => ∀ callee ∈ callees, CallSem Γ callee
          (some ⟨addressOfIndex (Γ.pc0 + (pos + args.length + 5)), fp⟩)
          (SegHolds Γ fp (callRets nfp args.length rets) (pos + args.length + 5) ∧ next) d f)
  | .ret _ one, _, _, _, kret, _ =>
      ∃ c, Γ.L.read (fp * addressOfIndex one) = some c ∧ (c ≠ 0 → kret)
  | .halt _ one dest, pos, _, _, _, khalt =>
      Holds Γ.L (Γ.pc0 + pos) fp (Γ.R (.set dest .endSentinel)) ∧
      JumpAt Γ fp one dest one True khalt

/-- The meaning of a block whose first instruction is `pos`. -/
def PStmt.SemList : List PStmt → ℕ → Prop → (E → E → Prop) → Prop → (E → E → Prop) → Prop
  | [], _, next, _, _, _ => next
  | s :: ss, pos, next, kj, kret, khalt =>
      PStmt.Sem s pos (PStmt.SemList ss (pos + stmtSize s) next kj kret khalt) kj kret khalt

/-- A jump to `(d, f)` into the stages of a chain from instruction `pos`: an arm of a stage, an
arm of a later one, or the join past them, at this frame. -/
def PStmt.StagesJump : List (List (List PStmt)) → ℕ → Prop → Prop → (E → E → Prop) → E → E → Prop
  | [], pos, next, _, _, d, f => d = Γ.tgt pos → f = ofK fp → next
  | s :: ss, pos, next, kret, khalt, d, f =>
      PStmt.ArmsJump s pos (PStmt.StagesJump ss (pos + armsSize s) next kret khalt) kret khalt d
          f ∧
        PStmt.StagesJump ss (pos + armsSize s) next kret khalt d f

/-- A jump to `(d, f)` into the arms of a stage from instruction `pos`: the arm entered runs,
and leaves by a jump `kj` or by falling off its end, which is a jump to the next instruction. -/
def PStmt.ArmsJump : List (List PStmt) → ℕ → (E → E → Prop) → Prop → (E → E → Prop) → E → E →
    Prop
  | [], _, _, _, _, _, _ => True
  | a :: as, pos, kj, kret, khalt, d, f =>
      (d = Γ.tgt pos → f = ofK fp →
        PStmt.SemList a pos (kj (Γ.tgt (pos + blockSize a)) (ofK fp)) kj kret khalt) ∧
      PStmt.ArmsJump as (pos + blockSize a) kj kret khalt d f
end

end
end LeanVM.Compiler
