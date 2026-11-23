module

public import NativeRustcVmArm.Ring.Track
public import NativeRustcVmArm.Ring.Switch.Exec
public import NativeRustcVmArm.Spec.Ring
public import NativeRustcVmArm.Bus.GkrModel
public import NativeRustcVm.Ring.Math
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.Transcript.Update

/-!
# `ring_switch`: its frame and the entry's facts

From the entry state `m0` (the `TState` at X0, `s` at X1, the `RingW` at X2): the frame (`SFr`:
432 bytes, X19 to X22, X29, X30 saved from byte `384`), its outputs (the `RingW`, the `TState`),
the entry's facts (`RingSwitchPre`, unpacked), the frame's environment (`envM`).
-/

namespace NativeRustcVmArm.Ring.Switch

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVm.Transcript

@[expose] public section

/-- The saved registers' slots. -/
def slots : List (Nat × XReg) :=
  [(384, .X29), (392, .X30), (400, .X22), (408, .X21), (416, .X20), (424, .X19)]

/-- The callee-saved registers the prologue does not save. -/
def keep : List XReg := [.X23, .X24, .X25, .X26, .X27, .X28]

/-- The `TState`'s, `s`'s and the `RingW`'s addresses. -/
def tA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
def sA (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
def oA (m0 : MachineData) : BitVec 64 := m0.regs.X2.toBitVec

/-- The outputs: the `RingW`, the `TState`. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (oA m0) ringWBytes q ∨ InRange (tA m0) tstateBytes q

/-- The frame. -/
abbrev SFr (m0 m : MachineData) : Prop := Fr m0 432 ringSwitchStack slots keep (outs m0) m

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := base m0 432

/-- The environment of the code between the calls: the frame. -/
abbrev envM (m0 m : MachineData) : Env := Env.ofMachine m [(fb m0, 432)]

/-- The block writes only the frame below the slots. -/
def wrLow (S : SState) : Bool := S.mem.all fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 384)

end

public section

variable {m0 : MachineData} {a : DecArea} {s : TState}

theorem stack_eq : ringSwitchStack = 3440 := rfl

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 432 := by decide

theorem slots_ge : ∀ p ∈ slots, 384 ≤ p.1 := by decide

theorem keep_cs : ∀ r ∈ keep, calleeSaved r = true := by decide

section
variable [Labels] (h : RingSwitchPre a s m0)
include h

theorem hN : ringSwitchStack ≤ m0.regs.SP.toNat := h.1.2.1

theorem fbN : (fb m0).toNat = m0.regs.SP.toNat - 432 :=
  base_toNat (by have := hN h; rw [stack_eq] at this; omega)

theorem fbw : NoWrap (fb m0) 432 := base_noWrap (by have := hN h; rw [stack_eq] at this; omega)

theorem t_frame : Apart (tA m0) tstateBytes (fb m0) 432 :=
  apart_frame (hN h) (by decide) h.2.2.2.1.1

theorem o_frame : Apart (oA m0) ringWBytes (fb m0) 432 :=
  apart_frame (hN h) (by decide) h.2.2.2.2.1.2.2.2.2.1

theorem s_frame : Apart (sA m0) 1024 (fb m0) 432 :=
  apart_frame (hN h) (by decide) h.2.2.2.2.2.1.2

theorem w_frame : Apart a.words (8 * a.len) (fb m0) 432 :=
  apart_frame (hN h) (by decide) h.2.2.2.1.2.1

theorem o_noWrap : NoWrap (oA m0) ringWBytes := h.2.2.2.2.1.2.1

theorem t_noWrap : NoWrap (tA m0) tstateBytes := h.2.2.1.footprint.1.2

/-- The outputs are apart from the frame. -/
theorem outs_frame : ∀ q, outs m0 q → ¬InRange (fb m0) 432 q := by
  rintro q (hq | hq)
  · exact NativeRustcVm.Apart.not_inRange (o_frame h) (o_noWrap h) (fbw h) hq
  · exact NativeRustcVm.Apart.not_inRange (t_frame h) (t_noWrap h) (fbw h) hq

end

theorem envM_wf [Labels] (h : RingSwitchPre a s m0) {m : MachineData} (hfr : SFr m0 m) :
    (envM m0 m).WF :=
  Env.wf_of ⟨⟨fun i hi ↦ hfr.kept _ (frame_mapped h.1 (by decide) i hi), fbw h⟩, trivial⟩
    (List.pairwise_singleton _ _)

theorem matchM [Labels] (h : RingSwitchPre a s m0) {m : MachineData} (hfr : SFr m0 m) :
    Match (envM m0 m) midS m :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1 (by decide) (by decide), trivial⟩
    (by rw [hfr.sp]; simp [Sym.eval]) trivial trivial trivial trivial

theorem reg_of [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r : XReg}
    {v : Sym} (h : S.reg r = some v) {w : UInt64} (hv : v.eval env = w.toBitVec) :
    m.regs.getXReg r = w :=
  UInt64.toBitVec_inj.mp ((hm.regs r v h).trans hv)

/-! ## Reading elements -/

theorem ewsOf_take (d : Mem 64) (b : BitVec 64) {n k : Nat} (h : k ≤ n) :
    (NativeRustcVm.ewsOf d b n).take k = NativeRustcVm.ewsOf d b k := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp

theorem ewsOf_drop (d : Mem 64) (b : BitVec 64) (n k : Nat) :
    (NativeRustcVm.ewsOf d b (k + n)).drop k =
      NativeRustcVm.ewsOf d (b + BitVec.ofNat 64 (16 * k)) n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_drop, NativeRustcVm.getElem_ewsOf]
  rw [NativeRustcVm.addr_add_add, Nat.mul_add]

/-- Elements read from words equal pairwise. -/
theorem ewsOf_of_words {d d' : Mem 64} {b b' : BitVec 64} {n : Nat}
    (h : ∀ j < 2 * n, NativeRustcVm.wordOf d' (b' + BitVec.ofNat 64 (8 * j)) =
      NativeRustcVm.wordOf d (b + BitVec.ofNat 64 (8 * j))) :
    NativeRustcVm.ewsOf d' b' n = NativeRustcVm.ewsOf d b n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [NativeRustcVm.getElem_ewsOf]
  simp only [NativeRustcVm.length_ewsOf] at h1
  unfold NativeRustcVm.ewOf
  have e0 := h (2 * i) (by omega)
  have e1 := h (2 * i + 1) (by omega)
  rw [show 8 * (2 * i) = 16 * i by omega] at e0
  rw [show 8 * (2 * i + 1) = 16 * i + 8 by omega, ← NativeRustcVm.addr_add_add,
    ← NativeRustcVm.addr_add_add] at e1
  rw [e0]
  exact congrArg _ e1

end

end NativeRustcVmArm.Ring.Switch
