module

public import NativeRustcVmArm.Ring.Frame
public import NativeRustcVmArm.Spec.Ring

/-!
# An `Option<EW>` written by a block

The weights' last blocks store the tag (`0` or `1`) at an `Option<EW>`'s byte `0` and, for
`Some`, X0 and X1 at bytes `8` and `16`: region 1 of the block's environment, checked by
`decide` on its literal result (`outNone`, `outSome`).
-/

namespace NativeRustcVmArm.Ring

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript

@[expose] public section

/-- The tag `0` at region 1's byte `0`. -/
def outNone (S : SState) : Bool :=
  (List.range 8).all fun i ↦ findWrite 1 (0 + i) S.mem == some (.lit 0, i)

/-- The tag `1` at region 1's byte `0`, X0 and X1 at `8` and `16`. -/
def outSome (S : SState) : Bool :=
  (List.range 8).all fun i ↦ findWrite 1 (0 + i) S.mem == some (.lit 1, i) &&
    findWrite 1 (8 + i) S.mem == some (.reg .X0, i) &&
    findWrite 1 (16 + i) S.mem == some (.reg .X1, i)

/-- The block's writes are in region 1's first `24` bytes. -/
def outOnly (S : SState) : Bool := S.mem.all fun w ↦ w.r == 1 && decide (w.off + w.n ≤ 24)

end

public section

variable [Labels] {m st : MachineData} {S : SState} {rs : List (BitVec 64 × Nat)} {o : BitVec 64}

theorem outNone_at (hm : Match (Env.ofMachine m rs) S st) (h1 : rs[1]? = some (o, 24))
    (hc : outNone S = true) : OptEWAt st.dmem o none := by
  simp only [outNone, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  have w := hm.bytesAt_write (r := 1) (o := 0) (n := 8) (b := o) (sz := 24) h1 (by omega)
    (v := .lit 0) fun i hi ↦ hc i hi
  rw [wordBytes_reg, NativeRustcVm.addr_add_zero] at w
  exact w

theorem outSome_at (hm : Match (Env.ofMachine m rs) S st) (h1 : rs[1]? = some (o, 24))
    (hc : outSome S = true) :
    OptEWAt st.dmem o (some ⟨m.regs.getXReg .X0, m.regs.getXReg .X1⟩) := by
  simp only [outSome, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hc
  have w0 := hm.bytesAt_write (r := 1) (o := 0) (n := 8) (b := o) (sz := 24) h1 (by omega)
    (v := .lit 1) fun i hi ↦ (hc i hi).1.1
  have w1 := hm.bytesAt_write (r := 1) (o := 8) (n := 8) (b := o) (sz := 24) h1 (by omega)
    (v := .reg .X0) fun i hi ↦ (hc i hi).1.2
  have w2 := hm.bytesAt_write (r := 1) (o := 16) (n := 8) (b := o) (sz := 24) h1 (by omega)
    (v := .reg .X1) fun i hi ↦ (hc i hi).2
  rw [wordBytes_reg, NativeRustcVm.addr_add_zero] at w0
  rw [wordBytes_reg] at w1 w2
  refine ⟨w0, ?_⟩
  rw [NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add]
  exact ⟨w1, w2⟩

/-- Memory after the block: as before but in the `Option<EW>`. -/
theorem outOnly_same (hm : Match (Env.ofMachine m rs) S st) (hwf : (Env.ofMachine m rs).WF)
    (h1 : rs[1]? = some (o, 24)) (hc : outOnly S = true) :
    SameOutside m.dmem st.dmem (InRange o 24) := by
  refine NativeRustcVm.SameOutside.mono (hm.sameOutside hwf) fun q ⟨w, hw, b, sz, hb, h1', h2⟩ ↦ ?_
  simp only [outOnly, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨hr, hn⟩ := hc w hw
  rw [hr] at hb
  change rs[1]? = some (b, sz) at hb
  rw [h1] at hb
  cases hb
  have := hwf.noWrap 1 o 24 h1
  rw [Sym.inRange_iff this]
  omega

end

end NativeRustcVmArm.Ring
