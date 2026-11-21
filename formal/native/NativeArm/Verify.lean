module

public import NativeArm.Compile
public import Native.Context

/-!
# A verifier's return on AArch64

At the body's `RET`, a run that kept the callee-saved QM registers (`Native.Context.calleeSaved`)
and never wrote `rsp` leaves every register AAPCS64 asks a procedure to preserve, X19 to X30 and
SP, as it found them (`Compile.Exits.saved`).
-/

open Native

namespace NativeArm

@[expose] public section

/-- The registers AAPCS64 asks a procedure to preserve besides SP: X19 to X29, and X30, the
return address. -/
def _root_.XReg.saved : XReg → Bool
  | .X19 | .X20 | .X21 | .X22 | .X23 | .X24 | .X25 | .X26 | .X27 | .X28 | .X29 | .X30 => true
  | _ => false

end

public section

/-- At the body's `RET`, every register AAPCS64 asks a procedure to preserve is as in `m`. -/
theorem Compile.Exits.saved {body : Stmt} {s s₁ : QState} {m m' : MachineData}
    (hR : StateRel s m) (hx : Compile.Exits body.writes s₁ m m')
    (hcs : ∀ r ∈ Context.calleeSaved, s₁.reg r = s.reg r) (hsp : body.writes .rsp = false) :
    (∀ x : XReg, x.saved = true → m'.regs.getXReg x = m.regs.getXReg x) ∧
      m'.regs.SP = m.regs.SP := by
  have img : ∀ r ∈ Context.calleeSaved, m'.regs.getXReg r.toX = m.regs.getXReg r.toX :=
    fun r hr => by
      have hrd : r ≠ .rdi := by
        simp only [Context.calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h <;> subst h <;> decide
      rw [hx.2.1 r hrd, hcs r hr, hR.get]
  have other : ∀ x : XReg, x ≠ .X0 → x.scratch = false → (∀ r : Reg64, r.toX = x → r = .rsp) →
      m'.regs.getXReg x = m.regs.getXReg x := fun x h0 hs hr =>
    hx.2.2.2.1 x h0 hs fun r hw he => by
      obtain rfl := hr r he
      exact absurd hw (by simp [hsp])
  refine ⟨fun x hxs => ?_, hx.2.2.2.2⟩
  cases x <;> simp only [XReg.saved, Bool.false_eq_true] at hxs
  · exact img .rbx (by decide)
  · exact img .rbp (by decide)
  · exact img .r12 (by decide)
  · exact img .r13 (by decide)
  · exact img .r14 (by decide)
  · exact img .r15 (by decide)
  all_goals exact other _ (by decide) rfl fun r he => by cases r <;> first | rfl | cases he

end

end NativeArm
