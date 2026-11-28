module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Proj

/-!
# `verify_layer` on x86-64: the masked sum's loop

At `NativeRustcVmX64.Vm.VerifyLayer.label_10` (`b16`, `MIn j i`) the masked sum at bit `j` has its first `2 i` terms
in RDI, RSI; RCX is `2 i`, R8 the pair of instance weights `2 i`, `2 i + 1` plus 24, RDX the mask
`1 << j`. `b16`, `b17` take term `2 i` into R10, R9 (`MA`), `b18`, `b19` term `2 i + 1` into RBP,
R11 (`MB`), `b15` adds both: back at `NativeRustcVmX64.Vm.VerifyLayer.label_10` with `i + 1`, or out at
`NativeRustcVmX64.Vm.VerifyLayer.label_14` (`b21`) with the pairs done (`MX`): `inner`.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The masked sum's registers. -/
def mRegs : List Reg64 := [.rcx, .r8, .rdx, .rdi, .rsi]

/-- **The masked sum's loop head**, `2 i` terms summed. -/
structure MIn [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (j i : Nat) (d : MachineData) : Prop where
  core : PCore m0 a c p s1 j d
  rcx : reg d .rcx = BitVec.ofNat 64 (2 * i)
  r8 : reg d .r8 = cA m0 + BitVec.ofNat 64 (48 + 32 * i)
  rdx : reg d .rdx = bitJ j
  acc : ewArg (reg d .rdi) (reg d .rsi) = xs (muSel c.mu j) (2 * i)
  lt : 2 * i + 2 ≤ c.mu.size

/-- After `b16`, `b17`: term `2 i` in R10, R9. -/
structure MA [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (j i : Nat) (d : MachineData) : Prop where
  base : MIn m0 a c p s1 j i d
  t0 : ewArg (reg d .r10) (reg d .r9) = muSel c.mu j (2 * i)

/-- After `b18`, `b19`: term `2 i + 1` in RBP, R11. -/
structure MB [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (j i : Nat) (d : MachineData) : Prop where
  base : MA m0 a c p s1 j i d
  t1 : ewArg (reg d .rbp) (reg d .r11) = muSel c.mu j (2 * i + 1)

/-- **The pairs done**, at `NativeRustcVmX64.Vm.VerifyLayer.label_14`. -/
structure MX [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (j : Nat) (d : MachineData) : Prop where
  core : PCore m0 a c p s1 j d
  rcx : reg d .rcx = BitVec.ofNat 64 (c.mu.size / 2 * 2)
  rdx : reg d .rdx = bitJ j
  acc : ewArg (reg d .rdi) (reg d .rsi) = xs (muSel c.mu j) (c.mu.size / 2 * 2)

end

public section

theorem mul8 {n : Nat} (h : n < 2 ^ 32) :
    (BinOp.apply .mul .W64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 8)).toNat = 8 * n := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem eq64 (x y : BitVec 64) : CmpOp.apply .eq .W64 x y = (x == y) := by
  simp [CmpOp.apply]

theorem and64 (x y : BitVec 64) : BinOp.apply .and .W64 x y = x &&& y := by
  simp [BinOp.apply]

theorem keepR_regs [Labels] {env : Env} {S : SState} {d d' : MachineData} (hm : Match env S d')
    {rs : List Reg64} (h : keepR S rs = true) (henv : ∀ r, env.regs r = reg d r) :
    ∀ r ∈ rs, reg d' r = reg d r := fun r hr ↦
  (hm.regs r (.reg r) (by simpa using List.all_eq_true.mp h r hr)).trans (henv r)

theorem muSel_def (mu : Array EW) (j i : Nat) :
    muSel mu j i = sel (testBitW (rmfeProjectW.getD i 0) j) (mu.getD i 0) := rfl

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}
  {p : Array EW} {s1 : TState} {j i : Nat}

theorem MIn.keep {d d' : MachineData} (h : MIn m0 a c p s1 j i d) (hc : PCore m0 a c p s1 j d')
    (hr : ∀ r ∈ mRegs, reg d' r = reg d r) : MIn m0 a c p s1 j i d' :=
  ⟨hc, by rw [hr .rcx (by simp [mRegs])]; exact h.rcx, by rw [hr .r8 (by simp [mRegs])]; exact h.r8,
    by rw [hr .rdx (by simp [mRegs])]; exact h.rdx,
    by rw [hr .rdi (by simp [mRegs]), hr .rsi (by simp [mRegs])]; exact h.acc, h.lt⟩

/-- `b16`, `b17`: term `2 i`. -/
theorem stepA (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : MIn m0 a c p s1 j i d) {R : MachineState → Prop}
    (cont : ∀ d', MA m0 a c p s1 j i d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b18Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b16Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hc := h.core
  have hlen : c.mu.size ≤ 16 := by
    have := (hc.body.claim hpre fun _ h ↦ h).2.1.1
    simpa [NativeRustcVm.KeccakGkr.muCap] using this
  have hwf : (envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0).WF :=
    wfR hpre hc.body (r := projectRegion) (by simp)
  have hm : Match (envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0) (projS 15) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hc.body.rsp, trivial⟩ trivial
      ⟨by show (reg d .rcx).toNat < 15
          rw [h.rcx, BitVec.toNat_ofNat]; have := h.lt; omega, trivial⟩
      ⟨by show reg d .r15 = projectAddr + BitVec.ofInt 64 0
          rw [hc.r15]; simp, trivial⟩
  have e3 : ∀ r, (envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0).regs r = reg d r := fun _ ↦ rfl
  have hw : BinOp.apply .and .W64 ((envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0).load 1
      (0 + (BinOp.apply .mul .W64 (reg d .rcx) (BitVec.ofNat 64 8)).toNat) 8) (reg d .rdx) =
      BinOp.apply .and .W64 (rmfeProjectW.getD (2 * i) 0).toBitVec (bitJ j) := by
    rw [h.rcx, mul8 (by have := h.lt; omega), Nat.zero_add,
      projLoad hpre hWo hc.body (by have := h.lt; omega), h.rdx]
  refine hc.pure hpre hwf (blk hp b16_in_code (by simp [b16])) e16 nofun hm (by decide +kernel) rfl
    (by decide +kernel) fun st hm1 hpc1 hd1 hc1 ↦ ?_
  have hk1 : ∀ r ∈ mRegs, reg st.data r = reg d r := keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  have hin1 := h.keep hc1 hk1
  simp only [PcOk] at hpc1
  have hbit := projBit (2 * i) (by have := h.lt; omega) j hc.lt
  have hcond : (SBool.cmp .eq .W64 (.bin .and .W64 (.loadx 1 0 (.bin .mul .W64 (.reg .rcx) (.lit 8)) 8)
      (.reg .rdx)) (.lit 0)).eval (envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0) =
      !testBitW (rmfeProjectW.getD (2 * i) 0) j := by
    simp only [SBool.eval, Sym.eval, e3]
    rw [hw]; exact hbit
  rw [hcond] at hpc1
  cases hb : testBitW (rmfeProjectW.getD (2 * i) 0) j with
  | false =>
    simp only [hb, Bool.not_false, ↓reduceIte] at hpc1
    rw [lbl hp b18_in_code rfl] at hpc1
    obtain ⟨d1, pc1⟩ := st
    simp only at hpc1 hm1 hin1
    subst hpc1
    refine cont d1 ⟨hin1, ?_⟩
    have h9 : reg d1 .r9 = BinOp.apply .and .W64 (rmfeProjectW.getD (2 * i) 0).toBitVec (bitJ j) := by
      rw [show reg d1 .r9 = _ from hm1.regs .r9 _ rfl]
      simp only [Sym.eval, e3]; exact hw
    have h10 : reg d1 .r10 = BinOp.apply .and .W64 (rmfeProjectW.getD (2 * i) 0).toBitVec (bitJ j) := by
      rw [show reg d1 .r10 = _ from hm1.regs .r10 _ rfl]
      simp only [Sym.eval, e3]; exact hw
    have hz := eq0 (hbit.trans (by rw [hb]; rfl))
    rw [h9, h10, hz, muSel_def, hb]
    rfl
  | true =>
    simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨d1, pc1⟩ := st
    simp only at hpc1 hm1 hin1 hc1
    subst hpc1
    -- `b17`
    have hc1' := hin1.core
    have hwf2 := wfSub hpre hc1'.body (x := cA m0 + BitVec.ofNat 64 (24 + 32 * i)) (n := 32)
      (by rw [g.ca (by have := h.lt; omega)]; omega)
      (by rw [g.ca (by have := h.lt; omega)]; have := h.lt; omega) (vars := fun _ ↦ 0) (ret := 0)
    have hm2 : Match (envB m0 d1 [(cA m0 + BitVec.ofNat 64 (24 + 32 * i), 32)] (fun _ ↦ 0) 0)
        (pairS .r8) d1 :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hc1'.body.rsp, trivial⟩ trivial trivial
        ⟨by show reg d1 .r8 = cA m0 + BitVec.ofNat 64 (24 + 32 * i) + BitVec.ofInt 64 24
            rw [hin1.r8]; simp only [BitVec.ofInt_ofNat]; bv_omega, trivial⟩
    refine hc1'.pure hpre hwf2 (blk hp b17_in_code (by simp [b17])) e17 nofun hm2
      (by decide +kernel) rfl (by decide +kernel) fun st hm3 hpc3 hd3 hc3 ↦ ?_
    simp only [PcOk] at hpc3
    obtain ⟨d3, pc3⟩ := st
    simp only at hpc3 hm3 hc3
    subst hpc3
    have hk3 : ∀ r ∈ mRegs, reg d3 r = reg d1 r := keepR_regs hm3 (by decide +kernel) fun _ ↦ rfl
    refine cont d3 ⟨hin1.keep hc3 hk3, ?_⟩
    rw [show reg d3 .r10 = _ from hm3.regs .r10 _ rfl, show reg d3 .r9 = _ from hm3.regs .r9 _ rfl]
    simp only [Sym.eval]
    rw [muSel_def, hb, sel_true]
    exact muLoad hpre (fun _ h ↦ h) hc1'.body (by have := h.lt; omega) (oo := 0)
      (by rw [BitVec.add_zero]; bv_omega)

theorem MA.keep {d d' : MachineData} (h : MA m0 a c p s1 j i d) (hc : PCore m0 a c p s1 j d')
    (hr : ∀ r ∈ mRegs ++ [.r10, .r9], reg d' r = reg d r) : MA m0 a c p s1 j i d' :=
  ⟨h.base.keep hc fun r hr' ↦ hr r (List.mem_append_left _ hr'), by
    rw [hr .r10 (by simp [mRegs]), hr .r9 (by simp [mRegs])]; exact h.t0⟩

/-- `b18`, `b19`: term `2 i + 1`. -/
theorem stepB (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : MA m0 a c p s1 j i d) {R : MachineState → Prop}
    (cont : ∀ d', MB m0 a c p s1 j i d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b15Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b18Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hin := h.base
  have hc := hin.core
  have hlen : c.mu.size ≤ 16 := by
    have := (hc.body.claim hpre fun _ h ↦ h).2.1.1
    simpa [NativeRustcVm.KeccakGkr.muCap] using this
  have hwf : (envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0).WF :=
    wfR hpre hc.body (r := projectRegion) (by simp)
  have hm : Match (envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0) (projS 15) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hc.body.rsp, trivial⟩ trivial
      ⟨by show (reg d .rcx).toNat < 15
          rw [hin.rcx, BitVec.toNat_ofNat]; have := hin.lt; omega, trivial⟩
      ⟨by show reg d .r15 = projectAddr + BitVec.ofInt 64 0
          rw [hc.r15]; simp, trivial⟩
  have e3 : ∀ r, (envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0).regs r = reg d r := fun _ ↦ rfl
  have hw : BinOp.apply .and .W64 ((envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0).load 1
      (8 + (BinOp.apply .mul .W64 (reg d .rcx) (BitVec.ofNat 64 8)).toNat) 8) (reg d .rdx) =
      BinOp.apply .and .W64 (rmfeProjectW.getD (2 * i + 1) 0).toBitVec (bitJ j) := by
    rw [hin.rcx, mul8 (by have := hin.lt; omega), show 8 + 8 * (2 * i) = 8 * (2 * i + 1) by omega,
      projLoad hpre hWo hc.body (by have := hin.lt; omega), hin.rdx]
  refine hc.pure hpre hwf (blk hp b18_in_code (by simp [b18])) e18 nofun hm (by decide +kernel) rfl
    (by decide +kernel) fun st hm1 hpc1 hd1 hc1 ↦ ?_
  have hk1 : ∀ r ∈ mRegs ++ [.r10, .r9], reg st.data r = reg d r :=
    keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  have hma1 := h.keep hc1 hk1
  simp only [PcOk] at hpc1
  have hbit := projBit (2 * i + 1) (by have := hin.lt; omega) j hc.lt
  have hcond : (SBool.cmp .eq .W64 (.bin .and .W64 (.loadx 1 8 (.bin .mul .W64 (.reg .rcx) (.lit 8)) 8)
      (.reg .rdx)) (.lit 0)).eval (envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0) =
      !testBitW (rmfeProjectW.getD (2 * i + 1) 0) j := by
    simp only [SBool.eval, Sym.eval, e3]
    rw [hw]; exact hbit
  rw [hcond] at hpc1
  cases hb : testBitW (rmfeProjectW.getD (2 * i + 1) 0) j with
  | false =>
    simp only [hb, Bool.not_false, ↓reduceIte] at hpc1
    rw [lbl hp b15_in_code rfl] at hpc1
    obtain ⟨d1, pc1⟩ := st
    simp only at hpc1 hm1 hma1
    subst hpc1
    refine cont d1 ⟨hma1, ?_⟩
    have h11 : reg d1 .r11 = BinOp.apply .and .W64 (rmfeProjectW.getD (2 * i + 1) 0).toBitVec (bitJ j) := by
      rw [show reg d1 .r11 = _ from hm1.regs .r11 _ rfl]
      simp only [Sym.eval, e3]; exact hw
    have hbp : reg d1 .rbp = BinOp.apply .and .W64 (rmfeProjectW.getD (2 * i + 1) 0).toBitVec (bitJ j) := by
      rw [show reg d1 .rbp = _ from hm1.regs .rbp _ rfl]
      simp only [Sym.eval, e3]; exact hw
    have hz := eq0 (hbit.trans (by rw [hb]; rfl))
    rw [h11, hbp, hz, muSel_def, hb]
    rfl
  | true =>
    simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨d1, pc1⟩ := st
    simp only at hpc1 hm1 hma1 hc1
    subst hpc1
    have hc1' := hma1.base.core
    have hwf2 := wfSub hpre hc1'.body (x := cA m0 + BitVec.ofNat 64 (24 + 32 * i)) (n := 32)
      (by rw [g.ca (by have := hin.lt; omega)]; omega)
      (by rw [g.ca (by have := hin.lt; omega)]; have := hin.lt; omega) (vars := fun _ ↦ 0) (ret := 0)
    have hm2 : Match (envB m0 d1 [(cA m0 + BitVec.ofNat 64 (24 + 32 * i), 32)] (fun _ ↦ 0) 0)
        (pairS .r8) d1 :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hc1'.body.rsp, trivial⟩ trivial trivial
        ⟨by show reg d1 .r8 = cA m0 + BitVec.ofNat 64 (24 + 32 * i) + BitVec.ofInt 64 24
            rw [hma1.base.r8]; simp only [BitVec.ofInt_ofNat]; bv_omega, trivial⟩
    refine hc1'.pure hpre hwf2 (blk hp b19_in_code (by simp [b19])) e19 nofun hm2
      (by decide +kernel) rfl (by decide +kernel) fun st hm3 hpc3 hd3 hc3 ↦ ?_
    simp only [PcOk] at hpc3
    rw [lbl hp b15_in_code rfl] at hpc3
    obtain ⟨d3, pc3⟩ := st
    simp only at hpc3 hm3 hc3
    subst hpc3
    have hk3 : ∀ r ∈ mRegs ++ [.r10, .r9], reg d3 r = reg d1 r :=
      keepR_regs hm3 (by decide +kernel) fun _ ↦ rfl
    refine cont d3 ⟨hma1.keep hc3 hk3, ?_⟩
    rw [show reg d3 .rbp = _ from hm3.regs .rbp _ rfl, show reg d3 .r11 = _ from hm3.regs .r11 _ rfl]
    simp only [Sym.eval]
    rw [muSel_def, hb, sel_true]
    exact muLoad hpre (fun _ h ↦ h) hc1'.body (by have := hin.lt; omega) (oo := 16) (by bv_omega)

/-- `b15`: both terms added; the next pair or out. -/
theorem step15 (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : MB m0 a c p s1 j i d) {R : MachineState → Prop}
    (hnext : ∀ d', MIn m0 a c p s1 j (i + 1) d' →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b16Offset)⟩)
    (hout : ∀ d', MX m0 a c p s1 j d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b21Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b15Offset)⟩ := by
  have hin := h.base.base
  have hc := hin.core
  have hwf := wf0 (pre_stack hpre) hc.body (vars := fun _ ↦ 0) (ret := 0)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) 0) (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hc.body.rsp, trivial⟩ trivial trivial trivial
  have e3 : ∀ r, (envB m0 d [] (fun _ ↦ 0) 0).regs r = reg d r := fun _ ↦ rfl
  refine hc.pure hpre hwf (blk hp b15_in_code (by simp [b15])) e15 nofun hm (by decide +kernel) rfl
    (by decide +kernel) fun st hm1 hpc1 hd1 hc1 ↦ ?_
  have hrdx : reg st.data .rdx = bitJ j := by
    rw [show reg st.data .rdx = _ from hm1.regs .rdx _ rfl]; exact hin.rdx
  have hrcx : reg st.data .rcx = BitVec.ofNat 64 (2 * (i + 1)) := by
    rw [show reg st.data .rcx = _ from hm1.regs .rcx _ rfl]
    simp only [Sym.eval, e3, add64]
    rw [hin.rcx]; bv_omega
  have hr8 : reg st.data .r8 = cA m0 + BitVec.ofNat 64 (48 + 32 * (i + 1)) := by
    rw [show reg st.data .r8 = _ from hm1.regs .r8 _ rfl]
    simp only [Sym.eval, e3, add64]
    rw [hin.r8]; bv_omega
  have hacc : ewArg (reg st.data .rdi) (reg st.data .rsi) = xs (muSel c.mu j) (2 * (i + 1)) := by
    rw [show reg st.data .rdi = _ from hm1.regs .rdi _ rfl,
      show reg st.data .rsi = _ from hm1.regs .rsi _ rfl]
    simp only [Sym.eval, e3, NativeRustcVmX64.Arrays.xor_eval]
    rw [NativeRustcVmX64.Arrays.ewArg_xor, NativeRustcVmX64.Arrays.ewArg_xor, hin.acc, h.base.t0,
      h.t1, show 2 * (i + 1) = 2 * i + 1 + 1 by omega, xs_succ, xs_succ]
  simp only [PcOk] at hpc1
  have hcond : (SBool.cmp .eq .W64 (.reg .rbx) (.bin .add .W64 (.lit 2) (.reg .rcx))).eval
      (envB m0 d [] (fun _ ↦ 0) 0) = decide (2 * i + 2 = c.mu.size / 2 * 2) := by
    simp only [SBool.eval, Sym.eval, e3, add64, eq64]
    rw [hc.rbx, hin.rcx]
    have := hin.lt
    have hl : c.mu.size ≤ 16 := by
      have := (hc.body.claim hpre fun _ h ↦ h).2.1.1
      simpa [NativeRustcVm.KeccakGkr.muCap] using this
    rw [show BitVec.ofNat 64 2 + BitVec.ofNat 64 (2 * i) = BitVec.ofNat 64 (2 * i + 2) by bv_omega]
    by_cases he : 2 * i + 2 = c.mu.size / 2 * 2
    · rw [he]; simp [show c.mu.size % 32 = c.mu.size by omega]
    · simp only [he, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro he'
      have := congrArg BitVec.toNat he'
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at this
      omega
  rw [hcond] at hpc1
  by_cases he : 2 * i + 2 = c.mu.size / 2 * 2
  · simp only [he, decide_true, ↓reduceIte] at hpc1
    rw [lbl hp b21_in_code rfl] at hpc1
    obtain ⟨d1, pc1⟩ := st
    simp only at hpc1 hc1 hrdx hrcx hacc
    subst hpc1
    exact hout d1 ⟨hc1, by rw [hrcx, ← he, Nat.mul_add, Nat.mul_one], hrdx,
      by rw [hacc, ← he, Nat.mul_add, Nat.mul_one]⟩
  · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨d1, pc1⟩ := st
    simp only at hpc1 hc1 hrdx hrcx hacc hr8
    subst hpc1
    exact hnext d1 ⟨hc1, hrcx, hr8, hrdx, hacc, by have := hin.lt; omega⟩

/-- **The pairs' loop**, from `NativeRustcVmX64.Vm.VerifyLayer.label_10` to `NativeRustcVmX64.Vm.VerifyLayer.label_14`. -/
theorem inner (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : MIn m0 a c p s1 j 0 d) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b21Offset) ∧ MX m0 a c p s1 j st.data)
      ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b16Offset)⟩ := by
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b16Offset) ∧ ∃ i, c.mu.size - 2 * i = n ∧
    MIn m0 a c p s1 j i st.data) (fun n st ⟨hpc, i, hn, hi⟩ ↦ ?_) ⟨rfl, 0, rfl, h⟩
  obtain ⟨d', pc⟩ := st
  simp only at hpc hi
  subst hpc
  exact stepA hp hpre hi fun d1 ha ↦ stepB hp hpre ha fun d2 hb ↦
    step15 hp hpre hb (fun d3 hn' ↦ .done _ (.inr ⟨_, by have := hn'.lt; have := hi.lt; omega,
      rfl, i + 1, rfl, hn'⟩)) fun d3 hx ↦ .done _ (.inl ⟨rfl, hx⟩)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
