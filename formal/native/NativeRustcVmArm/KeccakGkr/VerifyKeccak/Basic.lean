module

public import NativeRustcVmArm.Ring.Frame
public import NativeRustcVmArm.KeccakGkr.Common
public import NativeRustcVmArm.Spec.Field
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Exec
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Model

/-!
# `verify_keccak`: its frame and the entry's facts

From the entry state `m0` (the `TState` at X0, `logSteps` X1, `inst` at X2 (X3 elements), the
output lanes at X4, the scratch at X5, the column claims at X6, the `KeccakOutW` at X7): the frame
(`VFr`: 3360 bytes, X19 to X30 saved from byte `3264`), the outputs (`outs`), the entry's facts
(`P0`) and its regions as numbers (`Nums`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript
open NativeRustcVm.KeccakGkr (scratchBytes outBytes)
open NativeRustcVm (Region)

@[expose] public section

/-- The saved registers' slots. -/
def slots : List (Nat × XReg) :=
  [(3264, .X29), (3272, .X30), (3280, .X28), (3288, .X27), (3296, .X26), (3304, .X25),
    (3312, .X24), (3320, .X23), (3328, .X22), (3336, .X21), (3344, .X20), (3352, .X19)]

/-- The arguments' addresses. -/
def tA (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
def ipA (m0 : MachineData) : BitVec 64 := m0.regs.X2.toBitVec
def opA (m0 : MachineData) : BitVec 64 := m0.regs.X4.toBitVec
def scA (m0 : MachineData) : BitVec 64 := m0.regs.X5.toBitVec
def clA (m0 : MachineData) : BitVec 64 := m0.regs.X6.toBitVec
def oA (m0 : MachineData) : BitVec 64 := m0.regs.X7.toBitVec

/-- The regions written. -/
def wsOf (m0 : MachineData) : List Region :=
  [⟨tA m0, tstateBytes⟩, ⟨scA m0, scratchBytes⟩, ⟨clA m0, NativeRustcVm.Layout.claimsBytes⟩,
    ⟨oA m0, outBytes⟩]

/-- The regions read. -/
def rsOf [Labels] (a : DecArea) (inst : Array EW) (m0 : MachineData) : List Region :=
  [a.region, ewsRegion (ipA m0) inst.size, ewsRegion (opA m0) 25, rcRegion, projectRegion,
    rhoRegion]

/-- The outputs. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (tA m0) tstateBytes q ∨ InRange (scA m0) scratchBytes q ∨
    InRange (clA m0) NativeRustcVm.Layout.claimsBytes q ∨ InRange (oA m0) outBytes q

/-- **The frame.** -/
abbrev VFr (m0 m : MachineData) : Prop := Fr m0 3360 verifyKeccakStack slots [] (outs m0) m

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := base m0 3360

/-- A frame offset's address. -/
abbrev loc (m0 : MachineData) (o : Nat) : BitVec 64 := fb m0 + BitVec.ofNat 64 o

/-- The environment of the code between the calls: the frame. -/
abbrev envM (m0 m : MachineData) : Env := Env.ofMachine m [(fb m0, 3360)]

/-- What the function must reach. -/
def Goal [Labels] (a : DecArea) (s : TState) (cs : Array NativeVm.Model.ColumnClaimW)
    (inst output : Array EW) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ VerifyKeccakPost a s cs inst output m0 st.data

/-- **The entry's facts.** -/
structure P0 [Labels] (a : DecArea) (s : TState) (cs : Array NativeVm.Model.ColumnClaimW)
    (inst output : Array EW) (m0 : MachineData) : Prop where
  stk : StackOk m0 verifyKeccakStack
  rc : RcAt m0 verifyKeccakStack
  proj : ProjectAt m0
  rho : RhoAt m0
  ts : TStateAt m0.dmem (tA m0) a s
  cls : NativeRustcVm.Layout.ClaimsWAt m0.dmem (clA m0) cs
  ncs : cs.size < NativeRustcVm.Layout.claimCap
  n3 : inst.size = m0.regs.X3.toNat
  n1 : inst.size = m0.regs.X1.toNat
  n30 : inst.size ≤ 30
  insts : NativeRustcVm.EWsAt m0.dmem (ipA m0) inst.toList
  o25 : output.size = 25
  outv : NativeRustcVm.EWsAt m0.dmem (opA m0) output.toList
  areas : Areas m0 verifyKeccakStack (wsOf m0) (rsOf a inst m0)

/-- **The regions as numbers**: none wraps; the stack, the outputs and the regions read apart. -/
structure Nums [Labels] (a : DecArea) (inst : Array EW) (m0 : MachineData) : Prop where
  stk : StackOk m0 verifyKeccakStack
  hN : 7008 ≤ m0.regs.SP.toNat
  al : m0.regs.SP.toNat % 16 = 0
  spW : m0.regs.SP.toNat < 2 ^ 64
  tW : (tA m0).toNat + 760 ≤ 2 ^ 64
  tS : (tA m0).toNat + 760 ≤ m0.regs.SP.toNat - 7008 ∨ m0.regs.SP.toNat ≤ (tA m0).toNat
  sW : (scA m0).toNat + 205824 ≤ 2 ^ 64
  sS : (scA m0).toNat + 205824 ≤ m0.regs.SP.toNat - 7008 ∨ m0.regs.SP.toNat ≤ (scA m0).toNat
  cW : (clA m0).toNat + 97288 ≤ 2 ^ 64
  cS : (clA m0).toNat + 97288 ≤ m0.regs.SP.toNat - 7008 ∨ m0.regs.SP.toNat ≤ (clA m0).toNat
  oW : (oA m0).toNat + 1608 ≤ 2 ^ 64
  oS : (oA m0).toNat + 1608 ≤ m0.regs.SP.toNat - 7008 ∨ m0.regs.SP.toNat ≤ (oA m0).toNat
  wW : a.words.toNat + 8 * a.len ≤ 2 ^ 64
  wS : a.words.toNat + 8 * a.len ≤ m0.regs.SP.toNat - 7008 ∨ m0.regs.SP.toNat ≤ a.words.toNat
  iW : (ipA m0).toNat + 16 * inst.size ≤ 2 ^ 64
  iS : (ipA m0).toNat + 16 * inst.size ≤ m0.regs.SP.toNat - 7008 ∨ m0.regs.SP.toNat ≤ (ipA m0).toNat
  pW : (opA m0).toNat + 400 ≤ 2 ^ 64
  pS : (opA m0).toNat + 400 ≤ m0.regs.SP.toNat - 7008 ∨ m0.regs.SP.toNat ≤ (opA m0).toNat
  rcW : rcAddr.toNat + 192 ≤ 2 ^ 64
  rcS : rcAddr.toNat + 192 ≤ m0.regs.SP.toNat - 7008 ∨ m0.regs.SP.toNat ≤ rcAddr.toNat
  pjW : projectAddr.toNat + 128 ≤ 2 ^ 64
  pjS : projectAddr.toNat + 128 ≤ m0.regs.SP.toNat - 7008 ∨ m0.regs.SP.toNat ≤ projectAddr.toNat
  rhW : rhoAddr.toNat + 100 ≤ 2 ^ 64
  rhS : rhoAddr.toNat + 100 ≤ m0.regs.SP.toNat - 7008 ∨ m0.regs.SP.toNat ≤ rhoAddr.toNat
  txs : (tA m0).toNat + 760 ≤ (scA m0).toNat ∨ (scA m0).toNat + 205824 ≤ (tA m0).toNat
  txc : (tA m0).toNat + 760 ≤ (clA m0).toNat ∨ (clA m0).toNat + 97288 ≤ (tA m0).toNat
  txo : (tA m0).toNat + 760 ≤ (oA m0).toNat ∨ (oA m0).toNat + 1608 ≤ (tA m0).toNat
  sxc : (scA m0).toNat + 205824 ≤ (clA m0).toNat ∨ (clA m0).toNat + 97288 ≤ (scA m0).toNat
  sxo : (scA m0).toNat + 205824 ≤ (oA m0).toNat ∨ (oA m0).toNat + 1608 ≤ (scA m0).toNat
  cxo : (clA m0).toNat + 97288 ≤ (oA m0).toNat ∨ (oA m0).toNat + 1608 ≤ (clA m0).toNat
  t_w : (tA m0).toNat + 760 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (tA m0).toNat
  t_i : (tA m0).toNat + 760 ≤ (ipA m0).toNat ∨ (ipA m0).toNat + 16 * inst.size ≤ (tA m0).toNat
  t_p : (tA m0).toNat + 760 ≤ (opA m0).toNat ∨ (opA m0).toNat + 400 ≤ (tA m0).toNat
  t_rc : (tA m0).toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (tA m0).toNat
  t_pj : (tA m0).toNat + 760 ≤ projectAddr.toNat ∨ projectAddr.toNat + 128 ≤ (tA m0).toNat
  t_rh : (tA m0).toNat + 760 ≤ rhoAddr.toNat ∨ rhoAddr.toNat + 100 ≤ (tA m0).toNat
  s_w : (scA m0).toNat + 205824 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (scA m0).toNat
  s_i : (scA m0).toNat + 205824 ≤ (ipA m0).toNat ∨ (ipA m0).toNat + 16 * inst.size ≤ (scA m0).toNat
  s_p : (scA m0).toNat + 205824 ≤ (opA m0).toNat ∨ (opA m0).toNat + 400 ≤ (scA m0).toNat
  s_rc : (scA m0).toNat + 205824 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (scA m0).toNat
  s_pj : (scA m0).toNat + 205824 ≤ projectAddr.toNat ∨ projectAddr.toNat + 128 ≤ (scA m0).toNat
  s_rh : (scA m0).toNat + 205824 ≤ rhoAddr.toNat ∨ rhoAddr.toNat + 100 ≤ (scA m0).toNat
  c_w : (clA m0).toNat + 97288 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (clA m0).toNat
  c_i : (clA m0).toNat + 97288 ≤ (ipA m0).toNat ∨ (ipA m0).toNat + 16 * inst.size ≤ (clA m0).toNat
  c_p : (clA m0).toNat + 97288 ≤ (opA m0).toNat ∨ (opA m0).toNat + 400 ≤ (clA m0).toNat
  c_rc : (clA m0).toNat + 97288 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (clA m0).toNat
  c_pj : (clA m0).toNat + 97288 ≤ projectAddr.toNat ∨ projectAddr.toNat + 128 ≤ (clA m0).toNat
  c_rh : (clA m0).toNat + 97288 ≤ rhoAddr.toNat ∨ rhoAddr.toNat + 100 ≤ (clA m0).toNat
  o_w : (oA m0).toNat + 1608 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (oA m0).toNat
  o_i : (oA m0).toNat + 1608 ≤ (ipA m0).toNat ∨ (ipA m0).toNat + 16 * inst.size ≤ (oA m0).toNat
  o_p : (oA m0).toNat + 1608 ≤ (opA m0).toNat ∨ (opA m0).toNat + 400 ≤ (oA m0).toNat
  o_rc : (oA m0).toNat + 1608 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (oA m0).toNat
  o_pj : (oA m0).toNat + 1608 ≤ projectAddr.toNat ∨ projectAddr.toNat + 128 ≤ (oA m0).toNat
  o_rh : (oA m0).toNat + 1608 ≤ rhoAddr.toNat ∨ rhoAddr.toNat + 100 ≤ (oA m0).toNat

end

public section

theorem stack_eq : verifyKeccakStack = 7008 := by decide

theorem P0.of [Labels] {a : DecArea} {s : TState} {cs : Array NativeVm.Model.ColumnClaimW}
    {inst output : Array EW} {m0 : MachineData} (h : VerifyKeccakPre a s cs inst output m0) :
    P0 a s cs inst output m0 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem P0.nums [Labels] {a : DecArea} {s : TState} {cs : Array NativeVm.Model.ColumnClaimW}
    {inst output : Array EW} {m0 : MachineData}
        (h : P0 a s cs inst output m0) : Nums a inst m0 := by
  have hA := h.areas
  have hS := h.stk
  have hN : 7008 ≤ m0.regs.SP.toNat := by have := hS.2.1; rw [stack_eq] at this; exact this
  have hsb : (stackBelow m0 verifyKeccakStack).toNat = m0.regs.SP.toNat - 7008 := by
    rw [stack_eq]; exact NativeRustcVm.toNat_sub_ofNat hN
  exact {
  stk := hS
  hN := hN
  al := hS.1
  spW := m0.regs.SP.toNat_lt
  tW := (Areas.ok hA (r := ⟨tA m0, tstateBytes⟩) (Or.inl (by simp [wsOf]))).2
  tS := by
    have h1 : Apart (tA m0) 760 (stackBelow m0 verifyKeccakStack) 7008 :=
      Areas.apart_stack hA (w := ⟨tA m0, tstateBytes⟩) (by simp [wsOf])
    unfold Apart at h1; rw [hsb] at h1; omega
  sW := (Areas.ok hA (r := ⟨scA m0, scratchBytes⟩) (Or.inl (by simp [wsOf]))).2
  sS := by
    have h1 : Apart (scA m0) 205824 (stackBelow m0 verifyKeccakStack) 7008 :=
      Areas.apart_stack hA (w := ⟨scA m0, scratchBytes⟩) (by simp [wsOf])
    unfold Apart at h1; rw [hsb] at h1; omega
  cW := (Areas.ok hA (r := ⟨clA m0, NativeRustcVm.Layout.claimsBytes⟩) (Or.inl (by simp [wsOf]))).2
  cS := by
    have h1 : Apart (clA m0) 97288 (stackBelow m0 verifyKeccakStack) 7008 :=
      Areas.apart_stack hA (w := ⟨clA m0, NativeRustcVm.Layout.claimsBytes⟩) (by simp [wsOf])
    unfold Apart at h1; rw [hsb] at h1; omega
  oW := (Areas.ok hA (r := ⟨oA m0, outBytes⟩) (Or.inl (by simp [wsOf]))).2
  oS := by
    have h1 : Apart (oA m0) 1608 (stackBelow m0 verifyKeccakStack) 7008 :=
      Areas.apart_stack hA (w := ⟨oA m0, outBytes⟩) (by simp [wsOf])
    unfold Apart at h1; rw [hsb] at h1; omega
  wW := (Areas.ok hA (r := a.region) (Or.inr (by simp [rsOf]))).2
  wS := by
    have h1 : Apart (stackBelow m0 verifyKeccakStack) 7008 a.words (8 * a.len) :=
      Areas.stack_rs hA (r := a.region) (by simp [rsOf])
    unfold Apart at h1; rw [hsb] at h1; omega
  iW := (Areas.ok hA (r := ewsRegion (ipA m0) inst.size) (Or.inr (by simp [rsOf]))).2
  iS := by
    have h1 : Apart (stackBelow m0 verifyKeccakStack) 7008 (ipA m0) (16 * inst.size) :=
      Areas.stack_rs hA (r := ewsRegion (ipA m0) inst.size) (by simp [rsOf])
    unfold Apart at h1; rw [hsb] at h1; omega
  pW := (Areas.ok hA (r := ewsRegion (opA m0) 25) (Or.inr (by simp [rsOf]))).2
  pS := by
    have h1 : Apart (stackBelow m0 verifyKeccakStack) 7008 (opA m0) (400) :=
      Areas.stack_rs hA (r := ewsRegion (opA m0) 25) (by simp [rsOf])
    unfold Apart at h1; rw [hsb] at h1; omega
  rcW := (Areas.ok hA (r := rcRegion) (Or.inr (by simp [rsOf]))).2
  rcS := by
    have h1 : Apart (stackBelow m0 verifyKeccakStack) 7008 rcAddr (192) :=
      Areas.stack_rs hA (r := rcRegion) (by simp [rsOf])
    unfold Apart at h1; rw [hsb] at h1; omega
  pjW := (Areas.ok hA (r := projectRegion) (Or.inr (by simp [rsOf]))).2
  pjS := by
    have h1 : Apart (stackBelow m0 verifyKeccakStack) 7008 projectAddr (128) :=
      Areas.stack_rs hA (r := projectRegion) (by simp [rsOf])
    unfold Apart at h1; rw [hsb] at h1; omega
  rhW := (Areas.ok hA (r := rhoRegion) (Or.inr (by simp [rsOf]))).2
  rhS := by
    have h1 : Apart (stackBelow m0 verifyKeccakStack) 7008 rhoAddr (100) :=
      Areas.stack_rs hA (r := rhoRegion) (by simp [rsOf])
    unfold Apart at h1; rw [hsb] at h1; omega
  txs := Areas.apart_ws hA (i := 0) (j := 1) (by simp [wsOf]) (by simp [wsOf]) (by decide)
  txc := Areas.apart_ws hA (i := 0) (j := 2) (by simp [wsOf]) (by simp [wsOf]) (by decide)
  txo := Areas.apart_ws hA (i := 0) (j := 3) (by simp [wsOf]) (by simp [wsOf]) (by decide)
  sxc := Areas.apart_ws hA (i := 1) (j := 2) (by simp [wsOf]) (by simp [wsOf]) (by decide)
  sxo := Areas.apart_ws hA (i := 1) (j := 3) (by simp [wsOf]) (by simp [wsOf]) (by decide)
  cxo := Areas.apart_ws hA (i := 2) (j := 3) (by simp [wsOf]) (by simp [wsOf]) (by decide)
  t_w := Areas.apart_rs hA (w := ⟨tA m0, tstateBytes⟩) (r := a.region) (by simp [wsOf])
      (by simp [rsOf])
  t_i := Areas.apart_rs hA (w := ⟨tA m0, tstateBytes⟩) (r := ewsRegion (ipA m0) inst.size)
      (by simp [wsOf]) (by simp [rsOf])
  t_p := Areas.apart_rs hA (w := ⟨tA m0, tstateBytes⟩) (r := ewsRegion (opA m0) 25)
      (by simp [wsOf]) (by simp [rsOf])
  t_rc := Areas.apart_rs hA (w := ⟨tA m0, tstateBytes⟩) (r := rcRegion) (by simp [wsOf])
      (by simp [rsOf])
  t_pj := Areas.apart_rs hA (w := ⟨tA m0, tstateBytes⟩) (r := projectRegion) (by simp [wsOf])
      (by simp [rsOf])
  t_rh := Areas.apart_rs hA (w := ⟨tA m0, tstateBytes⟩) (r := rhoRegion) (by simp [wsOf])
      (by simp [rsOf])
  s_w := Areas.apart_rs hA (w := ⟨scA m0, scratchBytes⟩) (r := a.region) (by simp [wsOf])
      (by simp [rsOf])
  s_i := Areas.apart_rs hA (w := ⟨scA m0, scratchBytes⟩) (r := ewsRegion (ipA m0) inst.size)
      (by simp [wsOf]) (by simp [rsOf])
  s_p := Areas.apart_rs hA (w := ⟨scA m0, scratchBytes⟩) (r := ewsRegion (opA m0) 25)
      (by simp [wsOf]) (by simp [rsOf])
  s_rc := Areas.apart_rs hA (w := ⟨scA m0, scratchBytes⟩) (r := rcRegion) (by simp [wsOf])
      (by simp [rsOf])
  s_pj := Areas.apart_rs hA (w := ⟨scA m0, scratchBytes⟩) (r := projectRegion) (by simp [wsOf])
      (by simp [rsOf])
  s_rh := Areas.apart_rs hA (w := ⟨scA m0, scratchBytes⟩) (r := rhoRegion) (by simp [wsOf])
      (by simp [rsOf])
  c_w := Areas.apart_rs hA (w := ⟨clA m0, NativeRustcVm.Layout.claimsBytes⟩) (r := a.region)
      (by simp [wsOf]) (by simp [rsOf])
  c_i := Areas.apart_rs hA (w := ⟨clA m0, NativeRustcVm.Layout.claimsBytes⟩) (r := ewsRegion
      (ipA m0) inst.size) (by simp [wsOf]) (by simp [rsOf])
  c_p := Areas.apart_rs hA (w := ⟨clA m0, NativeRustcVm.Layout.claimsBytes⟩) (r := ewsRegion
      (opA m0) 25) (by simp [wsOf]) (by simp [rsOf])
  c_rc := Areas.apart_rs hA (w := ⟨clA m0, NativeRustcVm.Layout.claimsBytes⟩) (r := rcRegion)
      (by simp [wsOf]) (by simp [rsOf])
  c_pj := Areas.apart_rs hA (w := ⟨clA m0, NativeRustcVm.Layout.claimsBytes⟩) (r := projectRegion)
      (by simp [wsOf]) (by simp [rsOf])
  c_rh := Areas.apart_rs hA (w := ⟨clA m0, NativeRustcVm.Layout.claimsBytes⟩) (r := rhoRegion)
      (by simp [wsOf]) (by simp [rsOf])
  o_w := Areas.apart_rs hA (w := ⟨oA m0, outBytes⟩) (r := a.region) (by simp [wsOf])
      (by simp [rsOf])
  o_i := Areas.apart_rs hA (w := ⟨oA m0, outBytes⟩) (r := ewsRegion (ipA m0) inst.size)
      (by simp [wsOf]) (by simp [rsOf])
  o_p := Areas.apart_rs hA (w := ⟨oA m0, outBytes⟩) (r := ewsRegion (opA m0) 25) (by simp [wsOf])
      (by simp [rsOf])
  o_rc := Areas.apart_rs hA (w := ⟨oA m0, outBytes⟩) (r := rcRegion) (by simp [wsOf])
      (by simp [rsOf])
  o_pj := Areas.apart_rs hA (w := ⟨oA m0, outBytes⟩) (r := projectRegion) (by simp [wsOf])
      (by simp [rsOf])
  o_rh := Areas.apart_rs hA (w := ⟨oA m0, outBytes⟩) (r := rhoRegion) (by simp [wsOf])
      (by simp [rsOf])
  }

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
