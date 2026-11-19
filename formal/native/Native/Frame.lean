module

public import Native.WP

/-!
# What every run keeps

A run never adds or removes a word of memory (`Exec.mem_isSome`), and never changes a register no
instruction of the statement writes (`Exec.reg_frame`). The failure exit relies on both: it reads
the saved registers through `rdi`.
-/

@[expose] public section

namespace Native

/-- `s'` agrees with `s` on every register but those of `rs`. -/
def RegsFrame (rs : List Reg64) (s s' : QState) : Prop := ∀ r, r ∉ rs → s'.reg r = s.reg r

/-- The state an outcome ends in. -/
def Outcome.st : Outcome → QState
  | .ok s => s
  | .err s => s

/-- The register an instruction writes, if any. -/
def QInstr.dst : QInstr → Option Reg64
  | .mov d _ | .movi d _ | .load d _ | .lea d _ | .add d _ | .addi d _ | .sub d _ | .subi d _
  | .xor d _ | .xori d _ | .and d _ | .andi d _ | .or d _ | .not d | .neg d | .shli d _
  | .shri d _ | .sari d _ | .roli d _ | .shlcl d => some d
  | .store _ _ | .storei _ _ => none

/-- Whether a statement may write the register `r`. -/
def Stmt.writes (r : Reg64) : Stmt → Bool
  | .skip | .fail => false
  | .ins i => decide (i.dst = some r)
  | .seq a b => a.writes r || b.writes r
  | .ite _ t e => t.writes r || e.writes r
  | .loop _ b => b.writes r

theorem QInstr.step_mem_isSome {i : QInstr} {s s' : QState} (h : i.step s = some s') (a : UInt64) :
    (s'.mem a).isSome = (s.mem a).isSome := by
  cases i <;> simp only [QInstr.step, Option.map_eq_some_iff, Option.some.injEq] at h <;>
    first
    | (subst h; rfl)
    | (obtain ⟨v, hv, rfl⟩ := h; rfl)
    | (obtain ⟨v, hv, rfl⟩ := h
       simp only [QState.setMem_mem]
       split <;> simp_all)

theorem QInstr.step_reg {i : QInstr} {s s' : QState} (h : i.step s = some s') {r : Reg64}
    (hr : decide (i.dst = some r) = false) : s'.reg r = s.reg r := by
  cases i <;> simp [QInstr.dst] at hr <;>
    simp only [QInstr.step, Option.map_eq_some_iff, Option.some.injEq] at h <;>
    first
    | (subst h; simp [QState.setReg, Ne.symm hr])
    | (obtain ⟨v, hv, rfl⟩ := h; simp [QState.setReg, Ne.symm hr])
    | (obtain ⟨v, hv, rfl⟩ := h; rfl)

/-- A run keeps which words exist. -/
theorem Exec.mem_isSome {c : Stmt} {s : QState} {o : Outcome} (h : Exec c s o) (a : UInt64) :
    (o.st.mem a).isSome = (s.mem a).isSome := by
  induction h with
  | skip => rfl
  | ins hs => exact QInstr.step_mem_isSome hs a
  | seqOk _ _ ih1 ih2 => exact ih2.trans ih1
  | seqErr _ ih => exact ih
  | iteTrue _ _ ih => exact ih
  | iteFalse _ _ ih => exact ih
  | loopTrue _ _ _ ih1 ih2 => exact ih2.trans ih1
  | loopErr _ _ ih => exact ih
  | loopFalse => rfl
  | fail => rfl

/-- A run keeps every register the statement does not write. -/
theorem Exec.reg_frame {c : Stmt} {s : QState} {o : Outcome} (h : Exec c s o) {r : Reg64}
    (hr : c.writes r = false) : o.st.reg r = s.reg r := by
  induction h with
  | skip => rfl
  | ins hs => exact QInstr.step_reg hs hr
  | seqOk _ _ ih1 ih2 =>
    simp only [Stmt.writes, Bool.or_eq_false_iff] at hr
    exact (ih2 hr.2).trans (ih1 hr.1)
  | seqErr _ ih =>
    simp only [Stmt.writes, Bool.or_eq_false_iff] at hr
    exact ih hr.1
  | iteTrue _ _ ih =>
    simp only [Stmt.writes, Bool.or_eq_false_iff] at hr
    exact ih hr.1
  | iteFalse _ _ ih =>
    simp only [Stmt.writes, Bool.or_eq_false_iff] at hr
    exact ih hr.2
  | loopTrue _ _ _ ih1 ih2 => exact (ih2 hr).trans (ih1 hr)
  | loopErr _ _ ih => exact ih hr
  | loopFalse => rfl
  | fail => rfl

end Native
