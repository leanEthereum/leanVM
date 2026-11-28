module

public import NativeRustcVmArm.KeccakGkr.KeccakPhase.Exec
public import NativeRustcVmArm.KeccakGkr.Common
public import NativeRustcVmArm.Ring.Frame
public import NativeRustcVm.Tables.Same
public import NativeRustcVm.Transcript.Update

/-!
# `keccak_phase`: its frame and the entry's facts

From the entry state `m0` (the `TState` at X0, `logSteps` X1, the tables' evaluations at X2, the
scratch at X3, the column claims at X4, the `KeccakOutW` at X5): the 480-byte frame (`slots`, the
callee-saved registers X26 to X28 kept), the outputs (`wsOf`), the output lanes the code builds at
the frame's base (`lanes`), the regions as numbers (`Nums`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakPhase

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript
open NativeRustcVm.KeccakGkr (scratchBytes outBytes)
open NativeRustcVm (Region InAny)
open LeanVM.Protocol.Verifier (keccakOut)

@[expose] public section

/-- The saved registers' slots. -/
def slots : List (Nat × XReg) :=
  [(400, .X29), (416, .X30), (424, .X25), (432, .X24), (440, .X23), (448, .X22), (456, .X21),
    (464, .X20), (472, .X19)]

/-- The callee-saved registers the prologue does not save. -/
def keep : List XReg := [.X26, .X27, .X28]

/-- The regions written. -/
def wsOf (m0 : MachineData) : List Region :=
  [⟨m0.regs.X0.toBitVec, tstateBytes⟩, ⟨m0.regs.X3.toBitVec, scratchBytes⟩,
    ⟨m0.regs.X4.toBitVec, NativeRustcVm.Layout.claimsBytes⟩, ⟨m0.regs.X5.toBitVec, outBytes⟩]

/-- The outputs. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop := InAny (wsOf m0) q

/-- The output lanes `keccak_phase` passes: `values`' from `keccakOut` on, zeros past its end. -/
def lanes (values : Array EW) : Array EW :=
  (Array.range 25).map fun lane ↦ values.getD (keccakOut + lane) 0

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := base m0 480

/-- **The regions as numbers**: none wraps; the stack, the outputs and the regions read apart. -/
structure Nums [Labels] (a : DecArea) (m0 : MachineData) : Prop where
  hN : 7488 ≤ m0.regs.SP.toNat
  al : m0.regs.SP.toNat % 16 = 0
  tW : m0.regs.X0.toNat + 760 ≤ 2 ^ 64
  tS : m0.regs.X0.toNat + 760 ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ m0.regs.X0.toNat
  sW : m0.regs.X3.toNat + 205824 ≤ 2 ^ 64
  sS : m0.regs.X3.toNat + 205824 ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ m0.regs.X3.toNat
  cW : m0.regs.X4.toNat + 97288 ≤ 2 ^ 64
  cS : m0.regs.X4.toNat + 97288 ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ m0.regs.X4.toNat
  oW : m0.regs.X5.toNat + 1608 ≤ 2 ^ 64
  oS : m0.regs.X5.toNat + 1608 ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ m0.regs.X5.toNat
  eW : m0.regs.X2.toNat + 11808 ≤ 2 ^ 64
  eS : m0.regs.X2.toNat + 11808 ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ m0.regs.X2.toNat
  wW : a.words.toNat + 8 * a.len ≤ 2 ^ 64
  wS : a.words.toNat + 8 * a.len ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ a.words.toNat
  rcW : rcAddr.toNat + 192 ≤ 2 ^ 64
  rcS : rcAddr.toNat + 192 ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ rcAddr.toNat
  pjW : projectAddr.toNat + 128 ≤ 2 ^ 64
  pjS : projectAddr.toNat + 128 ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ projectAddr.toNat
  rhW : rhoAddr.toNat + 100 ≤ 2 ^ 64
  rhS : rhoAddr.toNat + 100 ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ rhoAddr.toNat
  txs : m0.regs.X0.toNat + 760 ≤ m0.regs.X3.toNat ∨ m0.regs.X3.toNat + 205824 ≤ m0.regs.X0.toNat
  txc : m0.regs.X0.toNat + 760 ≤ m0.regs.X4.toNat ∨ m0.regs.X4.toNat + 97288 ≤ m0.regs.X0.toNat
  txo : m0.regs.X0.toNat + 760 ≤ m0.regs.X5.toNat ∨ m0.regs.X5.toNat + 1608 ≤ m0.regs.X0.toNat
  sxc : m0.regs.X3.toNat + 205824 ≤ m0.regs.X4.toNat ∨ m0.regs.X4.toNat + 97288 ≤ m0.regs.X3.toNat
  sxo : m0.regs.X3.toNat + 205824 ≤ m0.regs.X5.toNat ∨ m0.regs.X5.toNat + 1608 ≤ m0.regs.X3.toNat
  cxo : m0.regs.X4.toNat + 97288 ≤ m0.regs.X5.toNat ∨ m0.regs.X5.toNat + 1608 ≤ m0.regs.X4.toNat
  t_e : m0.regs.X0.toNat + 760 ≤ m0.regs.X2.toNat ∨ m0.regs.X2.toNat + 11808 ≤ m0.regs.X0.toNat
  s_e : m0.regs.X3.toNat + 205824 ≤ m0.regs.X2.toNat ∨ m0.regs.X2.toNat + 11808 ≤ m0.regs.X3.toNat
  c_e : m0.regs.X4.toNat + 97288 ≤ m0.regs.X2.toNat ∨ m0.regs.X2.toNat + 11808 ≤ m0.regs.X4.toNat
  o_e : m0.regs.X5.toNat + 1608 ≤ m0.regs.X2.toNat ∨ m0.regs.X2.toNat + 11808 ≤ m0.regs.X5.toNat
  t_w : m0.regs.X0.toNat + 760 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ m0.regs.X0.toNat
  s_w : m0.regs.X3.toNat + 205824 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ m0.regs.X3.toNat
  c_w : m0.regs.X4.toNat + 97288 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ m0.regs.X4.toNat
  o_w : m0.regs.X5.toNat + 1608 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ m0.regs.X5.toNat
  t_rc : m0.regs.X0.toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ m0.regs.X0.toNat
  s_rc : m0.regs.X3.toNat + 205824 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ m0.regs.X3.toNat
  c_rc : m0.regs.X4.toNat + 97288 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ m0.regs.X4.toNat
  o_rc : m0.regs.X5.toNat + 1608 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ m0.regs.X5.toNat
  t_pj : m0.regs.X0.toNat + 760 ≤ projectAddr.toNat ∨ projectAddr.toNat + 128 ≤ m0.regs.X0.toNat
  s_pj : m0.regs.X3.toNat + 205824 ≤ projectAddr.toNat ∨
    projectAddr.toNat + 128 ≤ m0.regs.X3.toNat
  c_pj : m0.regs.X4.toNat + 97288 ≤ projectAddr.toNat ∨ projectAddr.toNat + 128 ≤ m0.regs.X4.toNat
  o_pj : m0.regs.X5.toNat + 1608 ≤ projectAddr.toNat ∨ projectAddr.toNat + 128 ≤ m0.regs.X5.toNat
  t_rh : m0.regs.X0.toNat + 760 ≤ rhoAddr.toNat ∨ rhoAddr.toNat + 100 ≤ m0.regs.X0.toNat
  s_rh : m0.regs.X3.toNat + 205824 ≤ rhoAddr.toNat ∨ rhoAddr.toNat + 100 ≤ m0.regs.X3.toNat
  c_rh : m0.regs.X4.toNat + 97288 ≤ rhoAddr.toNat ∨ rhoAddr.toNat + 100 ≤ m0.regs.X4.toNat
  o_rh : m0.regs.X5.toNat + 1608 ≤ rhoAddr.toNat ∨ rhoAddr.toNat + 100 ≤ m0.regs.X5.toNat

end

public section

theorem stack_eq : keccakPhaseStack = 7488 := by decide

theorem vk_stack_eq : verifyKeccakStack = 7008 := by decide

/-- The read regions of `keccak_phase`'s precondition. -/
abbrev rsOf [Labels] (a : DecArea) (m0 : MachineData) : List Region :=
  [a.region, ⟨m0.regs.X2.toBitVec, NativeRustcVm.Tables.tableEvalsBytes⟩, rcRegion, projectRegion,
    rhoRegion]

section
variable [Labels] {a : DecArea} {m0 : MachineData}

theorem nums_of (hS : StackOk m0 keccakPhaseStack)
    (hA : Areas m0 keccakPhaseStack (wsOf m0) (rsOf a m0)) : Nums a m0 := by
  have hN : 7488 ≤ m0.regs.SP.toNat := by have := hS.2.1; rw [stack_eq] at this; exact this
  have hsb : (stackBelow m0 keccakPhaseStack).toNat = m0.regs.SP.toNat - 7488 := by
    rw [stack_eq]; exact NativeRustcVm.toNat_sub_ofNat hN
  have ws : ∀ w ∈ wsOf m0, w.addr.toNat + w.size ≤ 2 ^ 64 ∧
      (w.addr.toNat + w.size ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ w.addr.toNat) := by
    intro w hw
    have h1 := Areas.apart_stack hA hw
    refine ⟨(Areas.ok hA (Or.inl hw)).2, ?_⟩
    unfold Apart at h1; rw [hsb, stack_eq] at h1; omega
  have rs : ∀ r ∈ rsOf a m0, r.addr.toNat + r.size ≤ 2 ^ 64 ∧
      (r.addr.toNat + r.size ≤ m0.regs.SP.toNat - 7488 ∨ m0.regs.SP.toNat ≤ r.addr.toNat) := by
    intro r hr
    have h1 := Areas.stack_rs hA hr
    refine ⟨(Areas.ok hA (Or.inr hr)).2, ?_⟩
    unfold Apart at h1; rw [hsb, stack_eq] at h1; omega
  have wr : ∀ w ∈ wsOf m0, ∀ r ∈ rsOf a m0, Apart w.addr w.size r.addr r.size :=
    fun w hw r hr ↦ Areas.apart_rs hA hw hr
  have ww := fun i j hi hj hij ↦ Areas.apart_ws hA (i := i) (j := j) hi hj hij
  simp only [wsOf, rsOf, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at ws rs wr
  obtain ⟨⟨tW, tS⟩, ⟨sW, sS⟩, ⟨cW, cS⟩, ⟨oW, oS⟩⟩ := ws
  obtain ⟨⟨wW, wS⟩, ⟨eW, eS⟩, ⟨rcW, rcS⟩, ⟨pjW, pjS⟩, ⟨rhW, rhS⟩⟩ := rs
  obtain ⟨⟨t_w, t_e, t_rc, t_pj, t_rh⟩, ⟨s_w, s_e, s_rc, s_pj, s_rh⟩,
    ⟨c_w, c_e, c_rc, c_pj, c_rh⟩, ⟨o_w, o_e, o_rc, o_pj, o_rh⟩⟩ := wr
  exact {
    hN := hN, al := hS.1, tW := tW, tS := tS, sW := sW, sS := sS, cW := cW, cS := cS,
    oW := oW, oS := oS, eW := eW, eS := eS, wW := wW, wS := wS, rcW := rcW, rcS := rcS,
    pjW := pjW, pjS := pjS, rhW := rhW, rhS := rhS,
    txs := ww 0 1 (by simp [wsOf]) (by simp [wsOf]) (by decide)
    txc := ww 0 2 (by simp [wsOf]) (by simp [wsOf]) (by decide)
    txo := ww 0 3 (by simp [wsOf]) (by simp [wsOf]) (by decide)
    sxc := ww 1 2 (by simp [wsOf]) (by simp [wsOf]) (by decide)
    sxo := ww 1 3 (by simp [wsOf]) (by simp [wsOf]) (by decide)
    cxo := ww 2 3 (by simp [wsOf]) (by simp [wsOf]) (by decide)
    t_e := t_e, s_e := s_e, c_e := c_e, o_e := o_e, t_w := t_w, s_w := s_w, c_w := c_w,
    o_w := o_w, t_rc := t_rc, s_rc := s_rc, c_rc := c_rc, o_rc := o_rc, t_pj := t_pj,
    s_pj := s_pj, c_pj := c_pj, o_pj := o_pj, t_rh := t_rh, s_rh := s_rh, c_rh := c_rh,
    o_rh := o_rh }

end

end

end NativeRustcVmArm.KeccakGkr.KeccakPhase
