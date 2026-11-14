/-
  LeanVM.Guest.Backend.Sound.Fills

  The jump table slots a placed statement fills, as a function of its position, and the proof
  that emission records exactly them.
-/

module

public import LeanVM.Guest.Backend.Sound.Ops

/-!
# The jump table slots of a placed statement

`blockFills f b pos` lists the slots the block `b` of the function `f` fills when its first
instruction is `pos`: arm `j` of a stage whose table is at `first` fills slot `first + j` with
`KVal.at f q`, `q` the arm's first instruction. `emitFn_fills` says `emitFn` returns them.
-/

namespace LeanVM.Guest.Backend

@[expose] public section

mutual
/-- The slots a placed statement fills. -/
def stmtFills (f : String) : PStmt → Nat → List Fill
  | .ite _ _ _ _ zero hasElse _ _ nonzero, pos =>
      blockFills f zero (pos + 2) ++
        (if hasElse then blockFills f nonzero (elseAt pos zero hasElse) else [])
  | .chain _ _ _ _ _ _ firsts stages, pos => stagesFills f firsts stages (pos + 3)
  | _, _ => []

def blockFills (f : String) : List PStmt → Nat → List Fill
  | [], _ => []
  | s :: ss, pos => stmtFills f s pos ++ blockFills f ss (pos + stmtSize s)

def armsFills (f : String) (first : Nat) : List (List PStmt) → Nat → Nat → List Fill
  | [], _, _ => []
  | a :: as, j, pos =>
      (first + j, KVal.at f pos) :: (blockFills f a pos ++
        armsFills f first as (j + 1) (pos + blockSize a))

def stagesFills (f : String) : List Nat → List (List (List PStmt)) → Nat → List Fill
  | _, [], _ => []
  | firsts, s :: ss, pos =>
      armsFills f (firsts.headD 0) s 0 pos ++ stagesFills f firsts.tail ss (pos + armsSize s)
end

theorem blockFills_append (f : String) (a b : List PStmt) (pos : Nat) :
    blockFills f (a ++ b) pos = blockFills f a pos ++ blockFills f b (pos + blockSize a) := by
  induction a generalizing pos with
  | nil => simp [blockFills, blockSize]
  | cons s ss ih => simp [blockFills, blockSize, ih, Nat.add_assoc]

theorem blockSize_append (a b : List PStmt) : blockSize (a ++ b) = blockSize a + blockSize b := by
  induction a with
  | nil => simp [blockSize]
  | cons s ss ih => simp [blockSize, ih, Nat.add_assoc]

theorem size_emitStmt (f : String) (s : PStmt) (acc : Array LInstr × Array Fill) :
    (emitStmt f s acc).1.size = acc.1.size + stmtSize s := by
  have h := congrArg List.length (emitStmt_ops f s acc)
  simpa only [opsOf_length, List.length_append, stmtOps_length] using h

theorem size_emitBlock (f : String) (b : List PStmt) (acc : Array LInstr × Array Fill) :
    (emitBlock f b acc).1.size = acc.1.size + blockSize b := emitBlockSize f b acc

theorem size_emitArms (f : String) (first : Nat) (as : List (List PStmt)) (j : Nat)
    (acc : Array LInstr × Array Fill) :
    (emitArms f first as j acc).1.size = acc.1.size + armsSize as := by
  have h := congrArg List.length (emitArms_ops f first as j acc)
  simpa only [opsOf_length, List.length_append, armsOps_length] using h

mutual
theorem emitStmt_fills (f : String) : ∀ (s : PStmt) (acc : Array LInstr × Array Fill),
    (emitStmt f s acc).2.toList = acc.2.toList ++ stmtFills f s acc.1.size
  | .op _ _, (code, fills) => by simp [emitStmt, stmtFills]
  | .ite hints c bdest sfp zero hasElse edest one nonzero, (code, fills) => by
      have hz := emitBlock_fills f zero
        (((code.push ⟨.set bdest (.local (elseAt code.size zero hasElse)), hints⟩).push
          (bare (.jump c bdest sfp))), fills)
      have hsz := size_emitBlock f zero
        (((code.push ⟨.set bdest (.local (elseAt code.size zero hasElse)), hints⟩).push
          (bare (.jump c bdest sfp))), fills)
      cases hasElse with
      | false =>
          simp only [emitStmt, stmtFills, elseAt, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
            Nat.add_zero, Array.size_push] at hz ⊢
          rw [hz]
          simp
      | true =>
          have hn := emitBlock_fills f nonzero
          simp only [emitStmt, stmtFills, elseAt, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
            Array.size_push] at hz hsz ⊢
          rw [hn, hz]
          simp only [Array.size_push, hsz, List.append_assoc]
  | .chain _ join x entry one sfp firsts stages, (code, fills) => by
      simp only [emitStmt, stmtFills]
      rw [emitStages_fills]
      simp [Array.size_push]
  | .call _ c, (code, fills) => by simp [emitStmt, stmtFills]
  | .loopNext _ _ _ _ _ _ _, (code, fills) => by simp [emitStmt, stmtFills]
  | .dispatch _ _ _ _ _ _ _ _ _ _, (code, fills) => by simp [emitStmt, stmtFills]
  | .ret _ _, (code, fills) => by simp [emitStmt, stmtFills]
  | .halt _ _ _, (code, fills) => by simp [emitStmt, stmtFills]

theorem emitBlock_fills (f : String) : ∀ (b : List PStmt) (acc : Array LInstr × Array Fill),
    (emitBlock f b acc).2.toList = acc.2.toList ++ blockFills f b acc.1.size
  | [], _ => by simp [emitBlock, blockFills]
  | s :: ss, acc => by
      rw [emitBlock, emitBlock_fills f ss, emitStmt_fills f s, size_emitStmt, blockFills,
        List.append_assoc]

theorem emitArms_fills (f : String) (first : Nat) : ∀ (as : List (List PStmt)) (j : Nat)
    (acc : Array LInstr × Array Fill),
    (emitArms f first as j acc).2.toList = acc.2.toList ++ armsFills f first as j acc.1.size
  | [], _, _ => by simp [emitArms, armsFills]
  | a :: as, j, (code, fills) => by
      rw [emitArms, emitArms_fills f first as, emitBlock_fills f a, size_emitBlock, armsFills]
      simp

theorem emitStages_fills (f : String) : ∀ (firsts : List Nat) (ss : List (List (List PStmt)))
    (acc : Array LInstr × Array Fill),
    (emitStages f firsts ss acc).2.toList = acc.2.toList ++ stagesFills f firsts ss acc.1.size
  | _, [], _ => by simp [emitStages, stagesFills]
  | firsts, s :: ss, acc => by
      rw [emitStages, emitStages_fills f firsts.tail ss, emitArms_fills f (firsts.headD 0) s,
        size_emitArms, stagesFills, List.append_assoc]
end

/-- **Emission records a body's jump table slots.** -/
theorem emitFn_fills (p : PFn) : (emitFn p).2.toList = blockFills p.name p.body 0 := by
  have h := emitBlock_fills p.name p.body (#[], #[])
  simpa [emitFn] using h

end
end LeanVM.Guest.Backend
