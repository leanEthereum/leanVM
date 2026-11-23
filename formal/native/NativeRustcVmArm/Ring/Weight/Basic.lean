module

public import NativeRustcVmArm.Ring.Frame
public import NativeRustcVmArm.Ring.Weight.Exec
public import NativeRustcVmArm.Ring.Weight.Model
public import NativeRustcVmArm.Spec.Ring
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `ring_weight`: its frame, its arguments, the steps every block takes

From the entry state `m0` (`out` X0, `r` X1, X2, `r'` X3, X4, the coefficients X5): the frame
(`WFr`: 688 bytes, X19 to X30 saved from byte `592`, `out` at byte `8`, the 36 powers from byte
`16`, `slotA`); the arguments' elements, the entry's in every state of the frame (`elem`); the
windows a block's environment has (`win_wf2`, `win_apart`); a block without writes
(`Fr.ofBlock`), one writing a window of the powers (`frWin`, `slot_set`, `slot_keep`), one
calling `EW::mul` (`mulStep`, `slot_call`).
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingWeight

@[expose] public section

/-- The saved registers' slots, `out`'s address at byte `8`. -/
def slots : List (Nat × XReg) :=
  [(8, .X0), (592, .X29), (600, .X30), (608, .X28), (616, .X27), (624, .X26), (632, .X25),
    (640, .X24), (648, .X23), (656, .X22), (664, .X21), (672, .X20), (680, .X19)]

/-- The frame (the output written by the epilogue only). -/
abbrev WFr (m0 m : MachineData) : Prop :=
  Fr m0 688 ringWeightStack slots [] (fun _ ↦ False) m

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := base m0 688

/-- `|r|`. -/
abbrev nR (m0 : MachineData) : Nat := m0.regs.X2.toNat
/-- `|r'|`. -/
abbrev nQ (m0 : MachineData) : Nat := m0.regs.X4.toNat
/-- `r`. -/
abbrev rL (m0 : MachineData) : Array EW := slice m0 m0.regs.X1 m0.regs.X2
/-- `r'`. -/
abbrev qL (m0 : MachineData) : Array EW := slice m0 m0.regs.X3 m0.regs.X4
/-- The coefficients. -/
abbrev cL (m0 : MachineData) : Array EW := arr m0 m0.regs.X5 coeffCount

/-- The address of power `j`. -/
abbrev slotA (m0 : MachineData) (j : Nat) : BitVec 64 := fb m0 + BitVec.ofNat 64 (16 + 16 * j)

/-- The powers hold `f`: power `j < |r|` is `f j`. -/
def PowAt (m0 : MachineData) (d : DataMem) (f : Nat → EW) : Prop :=
  ∀ j < nR m0, NativeRustcVm.EWAt d (slotA m0 j) (f j)

end

public section

variable {m0 : MachineData}

theorem stack_eq : ringWeightStack = 1280 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 688 := by decide

theorem keep_nil : ∀ r ∈ ([] : List XReg), calleeSaved r = true := by simp

theorem getD_slice (m : MachineData) (a n : UInt64) {i : Nat} (hi : i < n.toNat) :
    (slice m a n).getD i 0 = NativeRustcVm.ewOf m.dmem (a.toBitVec + BitVec.ofNat 64 (16 * i)) := by
  simp [slice, Array.getD, hi]

theorem getD_arr (m : MachineData) (a : UInt64) {n i : Nat} (hi : i < n) :
    (arr m a n).getD i 0 = NativeRustcVm.ewOf m.dmem (a.toBitVec + BitVec.ofNat 64 (16 * i)) := by
  simp [arr, Array.getD, hi]

theorem size_rL : (rL m0).size = nR m0 := by simp [slice]
theorem size_qL : (qL m0).size = nQ m0 := by simp [slice]
theorem size_cL : (cL m0).size = 64 := by simp [arr, coeffCount]

/-- A window of an argument: mapped in every state of the frame, not wrapping. -/
theorem arg_win {m : MachineData} (hfr : WFr m0 m) {a : BitVec 64} {n o len : Nat}
    (hr : Mapped m0.dmem a n ∧ NoWrap a n) (hle : o + len ≤ n) (hlen : 0 < len) :
    Mapped m.dmem (a + BitVec.ofNat 64 o) len ∧ NoWrap (a + BitVec.ofNat 64 o) len := by
  obtain ⟨hm, hw⟩ := hr
  unfold NoWrap at *
  refine ⟨fun j hj ↦ ?_, ?_⟩
  · rw [NativeRustcVm.addr_add_add]; exact hfr.kept _ (hm _ (by omega))
  · rw [NativeRustcVm.toNat_add_ofNat (by omega)]; omega

section
variable (h : RingWeightPre m0)
include h

theorem hN : ringWeightStack ≤ m0.regs.SP.toNat := h.1.2.1

theorem fbN : (fb m0).toNat = m0.regs.SP.toNat - 688 :=
  base_toNat (by have := hN h; rw [stack_eq] at this; omega)

theorem fbw : NoWrap (fb m0) 688 := base_noWrap (by have := hN h; rw [stack_eq] at this; omega)

theorem sN : (stackBelow m0 ringWeightStack).toNat = m0.regs.SP.toNat - 1280 := base_toNat (hN h)

theorem n36 : nR m0 ≤ 36 := h.2.1

/-- Bytes apart from the stack are the entry's in every state of the frame. -/
theorem same_of {m : MachineData} (hfr : WFr m0 m) {a : BitVec 64} {n : Nat}
    (ha : Apart a n (stackBelow m0 ringWeightStack) ringWeightStack) (hw : NoWrap a n)
    {j : Nat} (hj : j < n) :
    m.dmem.get? (a + BitVec.ofNat 64 j) = m0.dmem.get? (a + BitVec.ofNat 64 j) :=
  hfr.same _ fun hq ↦ hq.elim (fun hq ↦ NativeRustcVm.Apart.not_inRange_add ha hw
    (base_noWrap (hN h)) hj hq) id

/-- **An argument's element**, the entry's in every state of the frame. -/
theorem elem {m : MachineData} (hfr : WFr m0 m) {a : UInt64} {n i : Nat}
    (ha : Apart a.toBitVec (16 * n) (stackBelow m0 ringWeightStack) ringWeightStack)
    (hw : NoWrap a.toBitVec (16 * n)) (hi : i < n) :
    NativeRustcVm.ewOf m.dmem (a.toBitVec + BitVec.ofNat 64 (16 * i)) =
      NativeRustcVm.ewOf m0.dmem (a.toBitVec + BitVec.ofNat 64 (16 * i)) :=
  NativeRustcVm.ewOf_congr fun j hj ↦ by
    rw [NativeRustcVm.addr_add_add]
    exact same_of h hfr ha hw (by omega)

theorem elem_r {m : MachineData} (hfr : WFr m0 m) {i : Nat} (hi : i < nR m0) :
    NativeRustcVm.ewOf m.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * i)) = (rL m0).getD i 0 := by
  rw [getD_slice _ _ _ hi]
  exact elem h hfr h.2.2.1.2 h.2.2.1.1.2 hi

theorem elem_q {m : MachineData} (hfr : WFr m0 m) {i : Nat} (hi : i < nQ m0) :
    NativeRustcVm.ewOf m.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * i)) = (qL m0).getD i 0 := by
  rw [getD_slice _ _ _ hi]
  exact elem h hfr h.2.2.2.1.2 h.2.2.2.1.1.2 hi

theorem elem_c {m : MachineData} (hfr : WFr m0 m) {i : Nat} (hi : i < 64) :
    NativeRustcVm.ewOf m.dmem (m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * i)) = (cL m0).getD i 0 := by
  rw [show (cL m0).getD i 0 = _ from getD_arr m0 m0.regs.X5 (n := coeffCount) hi]
  exact elem h hfr h.2.2.2.2.1.2 h.2.2.2.2.1.1.2 hi

theorem frame_toNat {o : Nat} (ho : o ≤ 688) :
    (fb m0 + BitVec.ofNat 64 o).toNat = m0.regs.SP.toNat - 688 + o := by
  have := fbN h
  have := hN h
  have := m0.regs.SP.toNat_lt
  rw [stack_eq] at *
  rw [NativeRustcVm.toNat_add_ofNat (by omega), fbN h]

/-- A window of the frame: mapped in every state of the frame, not wrapping. -/
theorem frame_win {m : MachineData} (hfr : WFr m0 m) {o len : Nat} (hle : o + len ≤ 688)
    (hlen : 0 < len) :
    Mapped m.dmem (fb m0 + BitVec.ofNat 64 o) len ∧ NoWrap (fb m0 + BitVec.ofNat 64 o) len :=
  arg_win hfr (n := 688) ⟨frame_mapped h.1 (by decide), fbw h⟩ hle hlen

/-- A window of an argument (apart from the stack) is apart from one of the frame. -/
theorem win_apart {a : BitVec 64} {n o len o' len' : Nat}
    (ha : Apart a n (stackBelow m0 ringWeightStack) ringWeightStack) (hw : NoWrap a n)
    (hle : o + len ≤ n) (hlen : 0 < len) (hle' : o' + len' ≤ 688) :
    Apart (a + BitVec.ofNat 64 o) len (fb m0 + BitVec.ofNat 64 o') len' := by
  have h1 := sN h
  have h2 := frame_toNat h (o := o') (by omega)
  have h3 := hN h
  have := m0.regs.SP.toNat_lt
  rw [stack_eq] at h1 h3 ha
  unfold Apart NoWrap at *
  rw [h2, NativeRustcVm.toNat_add_ofNat (by omega)]
  rw [h1] at ha
  omega

end

theorem win_wf2 {m : MachineData} {a b : BitVec 64} {n n' : Nat}
    (ha : Mapped m.dmem a n ∧ NoWrap a n) (hb : Mapped m.dmem b n' ∧ NoWrap b n')
    (hab : Apart a n b n') : (Env.ofMachine m [(a, n), (b, n')]).WF :=
  Env.wf_of ⟨ha, hb, trivial⟩ (List.pairwise_pair.mpr hab)

theorem win_wf1 {m : MachineData} {a : BitVec 64} {n : Nat} (ha : Mapped m.dmem a n ∧ NoWrap a n) :
    (Env.ofMachine m [(a, n)]).WF :=
  Env.wf_of ⟨ha, trivial⟩ (List.pairwise_singleton _ _)

section
variable [Labels]

theorem reg_of {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r : XReg}
    {v : Sym} (h : S.reg r = some v) {w : UInt64} (hv : v.eval env = w.toBitVec) :
    m.regs.getXReg r = w :=
  UInt64.toBitVec_inj.mp ((hm.regs r v h).trans hv)

theorem reg_bv {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r : XReg}
    {v : Sym} (h : S.reg r = some v) {w : BitVec 64} (hv : v.eval env = w) :
    (m.regs.getXReg r).toBitVec = w :=
  (hm.regs r v h).trans hv

/-- A word of a region, as the environment loads it. -/
theorem load_ofMachine {m : MachineData} {rs : List (BitVec 64 × Nat)} {r : Nat} {a : BitVec 64}
    {n : Nat} (hr : rs[r]? = some (a, n)) (off : Nat) :
    (Sym.load r off 8).eval (Env.ofMachine m rs) =
      (NativeRustcVm.wordOf m.dmem (a + BitVec.ofNat 64 off)).toBitVec := by
  simp only [Sym.eval]
  rw [load_eq_wordOf, Env.base_ofMachine m rs _ hr]
  rfl

/-- An element of a region, as the environment loads it: limb `0`. -/
theorem load_c0 {m : MachineData} {rs : List (BitVec 64 × Nat)} {r : Nat} {a : BitVec 64}
    {n : Nat} (hr : rs[r]? = some (a, n)) (off : Nat) :
    (Sym.load r off 8).eval (Env.ofMachine m rs) =
      (NativeRustcVm.ewOf m.dmem (a + BitVec.ofNat 64 off)).c0.toBitVec :=
  load_ofMachine hr off

/-- An element of a region, as the environment loads it: limb `1`. -/
theorem load_c1 {m : MachineData} {rs : List (BitVec 64 × Nat)} {r : Nat} {a : BitVec 64}
    {n : Nat} (hr : rs[r]? = some (a, n)) (off : Nat) :
    (Sym.load r (off + 8) 8).eval (Env.ofMachine m rs) =
      (NativeRustcVm.ewOf m.dmem (a + BitVec.ofNat 64 off)).c1.toBitVec := by
  rw [load_ofMachine hr]
  show _ = (NativeRustcVm.wordOf m.dmem (a + BitVec.ofNat 64 off + BitVec.ofNat 64 8)).toBitVec
  rw [NativeRustcVm.addr_add_add]

end

end

end NativeRustcVmArm.Ring.Weight
