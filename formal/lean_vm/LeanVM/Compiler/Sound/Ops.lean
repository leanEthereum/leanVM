/-
  LeanVM.Compiler.Sound.Ops

  Emission as a function to lists: the instructions of a placed statement at a position, and
  the proof that `emitBlock` appends exactly them.
-/

module

public import LeanVM.Compiler.Emit

/-!
# The instructions of a placed statement

`emitBlock` threads the code so far as an array. `blockOps b pos` is the same code as a list, a
function of the block and of the position of its first instruction alone, and `emitBlock_ops`
says emission appends it. Everything proved about a run of emitted code is proved about
`stmtOps`, so no proof reads an array.

* `emitBlock_ops`, `emitFn_ops`: emission appends `blockOps`;
* `blockOps_length`, `emitBlockSize`: its length is `blockSize` (`EmitBlockSize`).
-/

namespace LeanVM.Compiler

open LeanVM.Guest LeanVM.Semantics

@[expose] public section

/-- The first instruction of the block an `ite` jumps to at a nonzero condition: the `else`
block, or the join when there is none. -/
def elseAt (pos : Nat) (zero : List PStmt) (hasElse : Bool) : Nat :=
  pos + 2 + blockSize zero + (if hasElse then 2 else 0)

/-- A call's instructions before its jump. -/
def callPre (c : CallSite) : List LOp :=
  [LOp.set c.entry (.entry c.callee)] ++
    ((c.args.zipIdx.map fun (a, k) => LOp.deref c.nfp (argBase + k) a .cell) ++
      (if c.loop.isSome then [LOp.deref c.nfp (argBase + c.args.length) c.nfp .cell] else []) ++
      (if c.tail then [LOp.deref c.nfp 1 1 .cell, LOp.deref c.nfp 0 0 .cell]
       else [LOp.deref c.nfp 1 0 .fp, LOp.deref c.nfp 0 0 .pc]))

/-- A call's instructions after its jump: the returned words read back. -/
def callRets (nfp : Cell) (nargs : Nat) (rets : List Cell) : List LOp :=
  rets.zipIdx.map fun (r, i) => LOp.deref nfp (argBase + nargs + i) r .cell

/-- A loop helper's closing call before its jump. -/
def loopPre (callee : String) (nfp entry one : Cell) (args : List Cell) : List LOp :=
  [LOp.set entry (.entry callee)] ++
    (args.zipIdx.map fun (a, k) => LOp.mulNextFrame a one (argBase + k)) ++
    [LOp.mulNextFrame nfp one (argBase + args.length), LOp.mulNextFrame 1 one 1,
      LOp.mulNextFrame 0 one 0]

/-- A fused `match` of calls before its jump, the first instruction at `pos`. -/
def dispatchPre (pos : Nat) (nfp joinCell x entry : Cell) (first : Nat) (args : List Cell) :
    List LOp :=
  (args.zipIdx.map fun (a, k) => LOp.deref nfp (argBase + k) a .cell) ++ [LOp.deref nfp 1 0 .fp] ++
    [LOp.set joinCell (.local (pos + args.length + 5)), LOp.deref nfp 0 joinCell .cell,
      LOp.slot x first entry]

mutual
/-- The instructions of a placed statement whose first is instruction `pos` of its function. -/
def stmtOps : PStmt → Nat → List LOp
  | .op _ o, _ => [o]
  | .ite _ c bdest sfp zero hasElse edest one nonzero, pos =>
      [LOp.set bdest (.local (elseAt pos zero hasElse)), LOp.jump c bdest sfp] ++
        blockOps zero (pos + 2) ++
        (if hasElse then
          [LOp.set edest (.local (elseAt pos zero hasElse + blockSize nonzero)),
            LOp.jump one edest sfp] ++ blockOps nonzero (elseAt pos zero hasElse)
        else [])
  | .chain _ join x entry one sfp firsts stages, pos =>
      [LOp.set join (.local (pos + 3 + stagesSize stages)), LOp.slot x (firsts.headD 0) entry,
        LOp.jump one entry sfp] ++ stagesOps stages (pos + 3)
  | .call _ c, _ =>
      callPre c ++ [LOp.jump c.oc c.entry c.nfp] ++ callRets c.nfp c.args.length c.rets
  | .loopNext _ callee nfp entry oc one args, _ =>
      loopPre callee nfp entry one args ++ [LOp.jump oc entry nfp]
  | .dispatch _ _ nfp joinCell x entry one first args rets, pos =>
      dispatchPre pos nfp joinCell x entry first args ++ [LOp.jump one entry nfp] ++
        callRets nfp args.length rets
  | .ret _ one, _ => [LOp.jump one 0 1]
  | .halt _ one dest, _ => [LOp.set dest .endSentinel, LOp.jump one dest one]

def blockOps : List PStmt → Nat → List LOp
  | [], _ => []
  | s :: ss, pos => stmtOps s pos ++ blockOps ss (pos + stmtSize s)

def armsOps : List (List PStmt) → Nat → List LOp
  | [], _ => []
  | a :: as, pos => blockOps a pos ++ armsOps as (pos + blockSize a)

def stagesOps : List (List (List PStmt)) → Nat → List LOp
  | [], _ => []
  | s :: ss, pos => armsOps s pos ++ stagesOps ss (pos + armsSize s)
end

/-! ## Lengths -/

theorem callPre_length (c : CallSite) :
    (callPre c).length = 1 + c.args.length + (if c.loop.isSome then 1 else 0) + 2 := by
  unfold callPre
  split <;> split <;> simp <;> omega

theorem callRets_length (nfp : Cell) (nargs : Nat) (rets : List Cell) :
    (callRets nfp nargs rets).length = rets.length := by
  simp [callRets]

theorem loopPre_length (callee : String) (nfp entry one : Cell) (args : List Cell) :
    (loopPre callee nfp entry one args).length = 1 + args.length + 3 := by
  simp [loopPre]
  omega

theorem dispatchPre_length (pos : Nat) (nfp joinCell x entry : Cell) (first : Nat)
    (args : List Cell) :
    (dispatchPre pos nfp joinCell x entry first args).length = args.length + 4 := by
  simp [dispatchPre]

mutual
theorem stmtOps_length : ∀ (s : PStmt) (pos : Nat), (stmtOps s pos).length = stmtSize s
  | .op _ _, _ => rfl
  | .ite _ _ _ _ zero hasElse _ _ nonzero, pos => by
      simp only [stmtOps, stmtSize, List.length_append, List.length_cons, List.length_nil,
        blockOps_length zero]
      cases hasElse <;> simp [blockOps_length nonzero]
      omega
  | .chain _ _ _ _ _ _ _ stages, pos => by
      simp only [stmtOps, stmtSize, List.length_append, List.length_cons, List.length_nil,
        stagesOps_length stages]
  | .call _ c, _ => by
      simp only [stmtOps, stmtSize, List.length_append, callPre_length, callRets_length,
        List.length_cons, List.length_nil]
  | .loopNext _ _ _ _ _ _ _, _ => by
      simp only [stmtOps, stmtSize, List.length_append, loopPre_length, List.length_cons,
        List.length_nil]
  | .dispatch _ _ _ _ _ _ _ _ _ _, _ => by
      simp only [stmtOps, stmtSize, List.length_append, dispatchPre_length, callRets_length,
        List.length_cons, List.length_nil]
  | .ret _ _, _ => rfl
  | .halt _ _ _, _ => rfl

theorem blockOps_length : ∀ (b : List PStmt) (pos : Nat), (blockOps b pos).length = blockSize b
  | [], _ => rfl
  | s :: ss, pos => by
      simp only [blockOps, blockSize, List.length_append, stmtOps_length s, blockOps_length ss]

theorem armsOps_length : ∀ (as : List (List PStmt)) (pos : Nat),
    (armsOps as pos).length = armsSize as
  | [], _ => rfl
  | a :: as, pos => by
      simp only [armsOps, armsSize, List.length_append, blockOps_length a, armsOps_length as]

theorem stagesOps_length : ∀ (ss : List (List (List PStmt))) (pos : Nat),
    (stagesOps ss pos).length = stagesSize ss
  | [], _ => rfl
  | s :: ss, pos => by
      simp only [stagesOps, stagesSize, List.length_append, armsOps_length s, stagesOps_length ss]
end

/-! ## Emission appends them -/

/-- The instructions of labelled code, without their hints. -/
def opsOf (code : Array LInstr) : List LOp := code.toList.map (·.op)

theorem opsOf_length (code : Array LInstr) : (opsOf code).length = code.size := by
  simp [opsOf]

/-- The instructions of labelled code being emitted, without their hints. -/
def opsR (code : Rev LInstr) : List LOp := code.toList.map (·.op)

theorem opsR_push (code : Rev LInstr) (i : LInstr) : opsR (code.push i) = opsR code ++ [i.op] := by
  simp [opsR]

theorem opsR_appendList (code : Rev LInstr) (is : List LInstr) :
    opsR (code.appendList is) = opsR code ++ is.map (·.op) := by
  simp [opsR]

theorem opsR_length (code : Rev LInstr) : (opsR code).length = code.size := by
  simp [opsR, Rev.size_eq_length]

theorem emitCall_ops (hints : List LHint) (c : CallSite) :
    (emitCall hints c).map (·.op) =
      callPre c ++ [LOp.jump c.oc c.entry c.nfp] ++ callRets c.nfp c.args.length c.rets := by
  simp only [emitCall, callPre, callRets]
  split <;> rename_i h <;> rw [h] <;> simp [bare, Function.comp_def]

theorem emitLoopNext_ops (hints : List LHint) (callee : String) (nfp entry oc one : Cell)
    (args : List Cell) :
    (emitLoopNext hints callee nfp entry oc one args).map (·.op) =
      loopPre callee nfp entry one args ++ [LOp.jump oc entry nfp] := by
  simp [emitLoopNext, loopPre, bare, Function.comp_def]

theorem emitDispatch_ops (pos : Nat) (hints : List LHint) (callees : List String)
    (nfp joinCell x entry one : Cell) (first : Nat) (args rets : List Cell) :
    (emitDispatch pos hints callees nfp joinCell x entry one first args rets).map (·.op) =
      dispatchPre pos nfp joinCell x entry first args ++ [LOp.jump one entry nfp] ++
        callRets nfp args.length rets := by
  simp only [emitDispatch, dispatchPre, callRets]
  split <;> rename_i h <;> rw [h] <;> simp [bare, Function.comp_def]

mutual
theorem emitStmt_ops (f : String) : ∀ (s : PStmt) (acc : Rev LInstr × Rev Fill),
    opsR (emitStmt f s acc).1 = opsR acc.1 ++ stmtOps s acc.1.size
  | .op _ _, (code, fills) => by simp [emitStmt, stmtOps, opsR_push]
  | .ite hints c bdest sfp zero hasElse edest one nonzero, (code, fills) => by
      have hz := emitBlock_ops f zero
        (((code.push ⟨.set bdest (.local (elseAt code.size zero hasElse)), hints⟩).push
          (bare (.jump c bdest sfp))), fills)
      cases hasElse with
      | false =>
          simp only [emitStmt, stmtOps, elseAt, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
            Nat.add_zero] at hz ⊢
          rw [hz]
          simp [opsR_push, bare]
      | true =>
          have hn := emitBlock_ops f nonzero
          simp only [emitStmt, stmtOps, elseAt, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
            at hz ⊢
          rw [hn, opsR_push, opsR_push, hz]
          have hlen := congrArg List.length hz
          simp only [opsR_length, List.length_append, blockOps_length, Rev.size_push, bare]
            at hlen
          simp [opsR_push, bare, Rev.size_push]
          rw [hlen]
  | .chain _ join x entry one sfp firsts stages, (code, fills) => by
      simp only [emitStmt, stmtOps]
      rw [emitStages_ops]
      simp [opsR_push, bare, Rev.size_push]
  | .call _ c, (code, fills) => by simp [emitStmt, stmtOps, opsR_appendList, emitCall_ops]
  | .loopNext _ _ _ _ _ _ _, (code, fills) => by
      simp [emitStmt, stmtOps, opsR_appendList, emitLoopNext_ops]
  | .dispatch _ _ _ _ _ _ _ _ _ _, (code, fills) => by
      simp [emitStmt, stmtOps, opsR_appendList, emitDispatch_ops]
  | .ret _ _, (code, fills) => by simp [emitStmt, stmtOps, opsR_push]
  | .halt _ _ _, (code, fills) => by simp [emitStmt, stmtOps, opsR_push, bare]

theorem emitBlock_ops (f : String) : ∀ (b : List PStmt) (acc : Rev LInstr × Rev Fill),
    opsR (emitBlock f b acc).1 = opsR acc.1 ++ blockOps b acc.1.size
  | [], _ => by simp [emitBlock, blockOps]
  | s :: ss, acc => by
      have hs := emitStmt_ops f s acc
      have hlen := congrArg List.length hs
      simp only [opsR_length, List.length_append, stmtOps_length] at hlen
      rw [emitBlock, emitBlock_ops f ss, hs, hlen, blockOps, List.append_assoc]

theorem emitArms_ops (f : String) (first : Nat) : ∀ (as : List (List PStmt)) (j : Nat)
    (acc : Rev LInstr × Rev Fill),
    opsR (emitArms f first as j acc).1 = opsR acc.1 ++ armsOps as acc.1.size
  | [], _, _ => by simp [emitArms, armsOps]
  | a :: as, j, (code, fills) => by
      have ha := emitBlock_ops f a (code, fills.push (first + j, .at f code.size))
      have hlen := congrArg List.length ha
      simp only [opsR_length, List.length_append, blockOps_length] at hlen
      rw [emitArms, emitArms_ops f first as, ha, hlen, armsOps, List.append_assoc]

theorem emitStages_ops (f : String) : ∀ (firsts : List Nat) (ss : List (List (List PStmt)))
    (acc : Rev LInstr × Rev Fill),
    opsR (emitStages f firsts ss acc).1 = opsR acc.1 ++ stagesOps ss acc.1.size
  | _, [], _ => by simp [emitStages, stagesOps]
  | firsts, s :: ss, acc => by
      have hs := emitArms_ops f (firsts.headD 0) s 0 acc
      have hlen := congrArg List.length hs
      simp only [opsR_length, List.length_append, armsOps_length] at hlen
      rw [emitStages, emitStages_ops f firsts.tail ss, hs, hlen, stagesOps, List.append_assoc]
end

/-- **Emission appends a block's instructions.** -/
theorem emitFn_ops (p : PFn) : opsOf (emitFn p).1.code = blockOps p.body 0 := by
  have h := emitBlock_ops p.name p.body ({}, {})
  simpa [emitFn, opsOf, opsR] using h

/-- Emission adds exactly a block's size to the code (`EmitBlockSize`). -/
theorem emitBlockSize : EmitBlockSize := by
  intro f b acc
  have h := congrArg List.length (emitBlock_ops f b acc)
  simpa only [opsR_length, List.length_append, blockOps_length] using h

theorem emitFn_size (p : PFn) : (emitFn p).1.code.size = blockSize p.body := by
  have h := congrArg List.length (emitFn_ops p)
  simpa only [opsOf_length, blockOps_length] using h

end
end LeanVM.Compiler
