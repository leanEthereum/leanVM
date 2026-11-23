module

public import NativeRustcVmArm.Tables.TableSumcheck.Defs

/-!
# `table_sumcheck`: one swap of the reverse

`b5` from the state `m`, the elements at X9 (region 0) and X10 (region 1), sixteen bytes each and
apart: they exchanged (`swap_x9`, `swap_x10`), every other byte kept (`swap_other`), X9 sixteen
bytes on, X10 sixteen back, X8 one less.
-/

namespace NativeRustcVmArm.Tables.TableSumcheck

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableSumcheck
open NativeRustcVm (ewOf wordOf)

public section

variable [Labels] {m m' : MachineData} {p q : BitVec 64}

/-- The swap's environment. -/
abbrev envS (m : MachineData) (p q : BitVec 64) : Env := Env.ofMachine m [(p, 16), (q, 16)]

omit [Labels] in
theorem loadSym_b5_0 (o : Nat) (ho : o = 0 ∨ o = 8) :
    loadSym (Bus.after b5 revS).mem 0 o 8 = .load 1 o 8 := by
  rw [ok_b5.2.1]; rcases ho with rfl | rfl <;> decide

omit [Labels] in
theorem loadSym_b5_1 (o : Nat) (ho : o = 0 ∨ o = 8) :
    loadSym (Bus.after b5 revS).mem 1 o 8 = .load 0 o 8 := by
  rw [ok_b5.2.1]; rcases ho with rfl | rfl <;> decide

omit [Labels] in
/-- The swap's environment, well formed. -/
theorem wf_swap (hp : NativeRustcVm.Mapped m.dmem p 16 ∧ NoWrap p 16)
    (hq : NativeRustcVm.Mapped m.dmem q 16 ∧ NoWrap q 16) (hpq : Apart p 16 q 16) :
    (envS m p q).WF :=
  Env.wf_of ⟨hp, hq, trivial⟩ (List.Pairwise.cons (by simpa using hpq) (List.pairwise_singleton _ _))

/-- The swap's start. -/
theorem match_swap (h9 : (m.regs.getXReg .X9).toBitVec = p)
    (h10 : (m.regs.getXReg .X10).toBitVec = q) : Match (envS m p q) revS m :=
  match_ofMachine (sregions := [(16, false), (16, false)]) (regions := [(p, 16), (q, 16)])
    ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
    ⟨by simp [Sym.eval, h9], by simp [Sym.eval, h10], trivial⟩ trivial trivial trivial

omit [Labels] in
/-- Where the swap wrote: the two elements. -/
theorem written_swap {a : BitVec 64} (hwf : (envS m p q).WF)
    (h : Written (envS m p q) (Bus.after b5 revS) a) : InRange p 16 a ∨ InRange q 16 a := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := h
  rw [ok_b5.2.1] at hw
  have hn0 := hwf.noWrap 0 p 16 rfl
  have hn1 := hwf.noWrap 1 q 16 rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  all_goals simp only [envS, Env.ofMachine_regions] at hb
  all_goals simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  all_goals obtain ⟨rfl, rfl⟩ := hb
  · right; rw [Sym.inRange_iff hn1]; simp only at h1 h2; omega
  · right; rw [Sym.inRange_iff hn1]; simp only at h1 h2; omega
  · left; rw [Sym.inRange_iff hn0]; simp only at h1 h2; omega
  · left; rw [Sym.inRange_iff hn0]; simp only at h1 h2; omega

/-- A byte outside both elements: kept. -/
theorem swap_other (hm : Match (envS m p q) (Bus.after b5 revS) m') (hwf : (envS m p q).WF)
    {a : BitVec 64} (ha : ¬InRange p 16 a) (hb : ¬InRange q 16 a) :
    m'.dmem.get? a = m.dmem.get? a :=
  hm.get?_mem0 hwf fun h ↦ (written_swap hwf h).elim ha hb

theorem wordOf_swap (hm : Match (envS m p q) (Bus.after b5 revS) m') (hwf : (envS m p q).WF)
    {r : Nat} {b b' : BitVec 64} (hb : (envS m p q).regions[r]? = some (b, 16))
    (hb' : (envS m p q).base (1 - r) = b') {o : Nat} (ho : o = 0 ∨ o = 8)
    (hl : loadSym (Bus.after b5 revS).mem r o 8 = .load (1 - r) o 8) :
    wordOf m'.dmem (b + BitVec.ofNat 64 o) = wordOf m.dmem (b' + BitVec.ofNat 64 o) := by
  apply UInt64.toBitVec_inj.mp
  rw [match_wordOf hm hwf hb (by omega), hl]
  show (envS m p q).load (1 - r) o 8 = _
  rw [load8, hb']
  rfl

/-- **The element at X9** after the swap: X10's before. -/
theorem swap_x9 (hm : Match (envS m p q) (Bus.after b5 revS) m') (hwf : (envS m p q).WF) :
    ewOf m'.dmem p = ewOf m.dmem q := by
  have h0 := wordOf_swap (r := 0) (b := p) (b' := q) hm hwf rfl rfl (o := 0) (.inl rfl)
    (loadSym_b5_0 0 (.inl rfl))
  have h8 := wordOf_swap (r := 0) (b := p) (b' := q) hm hwf rfl rfl (o := 8) (.inr rfl)
    (loadSym_b5_0 8 (.inr rfl))
  rw [NativeRustcVm.addr_add_zero, NativeRustcVm.addr_add_zero] at h0
  unfold ewOf
  rw [h0]
  exact congrArg _ h8

/-- **The element at X10** after the swap: X9's before. -/
theorem swap_x10 (hm : Match (envS m p q) (Bus.after b5 revS) m') (hwf : (envS m p q).WF) :
    ewOf m'.dmem q = ewOf m.dmem p := by
  have h0 := wordOf_swap (r := 1) (b := q) (b' := p) hm hwf rfl rfl (o := 0) (.inl rfl)
    (loadSym_b5_1 0 (.inl rfl))
  have h8 := wordOf_swap (r := 1) (b := q) (b' := p) hm hwf rfl rfl (o := 8) (.inr rfl)
    (loadSym_b5_1 8 (.inr rfl))
  rw [NativeRustcVm.addr_add_zero, NativeRustcVm.addr_add_zero] at h0
  unfold ewOf
  rw [h0]
  exact congrArg _ h8

end

end NativeRustcVmArm.Tables.TableSumcheck
