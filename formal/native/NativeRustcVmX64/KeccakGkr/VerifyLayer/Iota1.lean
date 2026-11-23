module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.IotaDefs

/-!
# `verify_layer` on x86-64: ι's first segment

`b26` loads the round constant `KECCAK_RC[11 - step]` and the first segment's weight; the loop
`NativeRustcVmX64.Vm.VerifyLayer.label_21` (`b30`, the raw `bt` of bit `2 i`; `b28` or `b31` the term; `b29` the
next bit and the sum) sums the bit weights it selects (`IA i`): `iota1`, to `NativeRustcVmX64.Vm.VerifyLayer.label_23`
with `bitsOf` in RDX, RAX (`IX`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The step. -/
abbrev stepN (m0 : MachineData) : Nat := (reg m0 .rdx).toNat

/-- **The first segment's loop head**, `2 i` bits summed. -/
structure IA [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (i : Nat) (d : MachineData) : Prop where
  k0 : K0 m0 a c p s1 (spillsI m0 c) d
  rcx : reg d .rcx = BitVec.ofNat 64 (2 * i)
  r10 : reg d .r10 = sA m0 + BitVec.ofNat 64 (25624 + 32 * i)
  r9 : reg d .r9 = (rcW (11 - stepN m0)).toBitVec
  acc : ewArg (reg d .rdx) (reg d .rax) = xs (bitSel c.weights (rcW (11 - stepN m0))) (2 * i)
  seg : ewArg (reg d .rdi) (reg d .rsi) = (segK m0 c).getD 0 0
  r15 : reg d .r15 = sA m0
  r8 : reg d .r8 = rcAddr
  lt : i < 32

/-- After the term `2 i`, in RBX, R11. -/
structure IB [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (i : Nat) (d : MachineData) : Prop where
  base : IA m0 a c p s1 i d
  t : ewArg (reg d .rbx) (reg d .r11) = bitSel c.weights (rcW (11 - stepN m0)) (2 * i)

/-- **The first segment done**, at `NativeRustcVmX64.Vm.VerifyLayer.label_23`. -/
structure IX [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (d : MachineData) : Prop where
  k0 : K0 m0 a c p s1 (spillsI m0 c) d
  acc : ewArg (reg d .rdx) (reg d .rax) = bitsOf c.weights (rcW (11 - stepN m0))
  seg : ewArg (reg d .rdi) (reg d .rsi) = (segK m0 c).getD 0 0
  r15 : reg d .r15 = sA m0
  r8 : reg d .r8 = rcAddr

/-- The registers the loop keeps. -/
def iaRegs : List Reg64 := [.rcx, .r10, .r9, .rdx, .rax, .rdi, .rsi, .r15, .r8, .r12, .r13]

end

public section

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}
  {p : Array EW} {s1 : TState} {i : Nat}

theorem IA.keep {d d' : MachineData} (h : IA m0 a c p s1 i d)
    (hk : K0 m0 a c p s1 (spillsI m0 c) d') (hr : ∀ r ∈ iaRegs, reg d' r = reg d r) :
    IA m0 a c p s1 i d' :=
  ⟨hk, by rw [hr .rcx (by simp [iaRegs])]; exact h.rcx, by rw [hr .r10 (by simp [iaRegs])]; exact h.r10,
    by rw [hr .r9 (by simp [iaRegs])]; exact h.r9,
    by rw [hr .rdx (by simp [iaRegs]), hr .rax (by simp [iaRegs])]; exact h.acc,
    by rw [hr .rdi (by simp [iaRegs]), hr .rsi (by simp [iaRegs])]; exact h.seg,
    by rw [hr .r15 (by simp [iaRegs])]; exact h.r15, by rw [hr .r8 (by simp [iaRegs])]; exact h.r8,
    h.lt⟩

/-- `b30`, then `b28` or `b31`: the term `2 i`. -/
theorem iaStep (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : IA m0 a c p s1 i d) {R : MachineState → Prop}
    (cont : ∀ d', IB m0 a c p s1 i d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b29Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b30Offset)⟩ := by
  have g := geo_of hpre
  have hk := h.k0
  have hst := pre_step hpre
  have hwf := wf0 (pre_stack hpre) hk.body (vars := fun _ ↦ 0) (ret := 0)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) 0) (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hk.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g hk.body hwf (blk hp b30_in_code (by simp [b30])) e30 nofun hm
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hk1 := hk.blk hpre (spillsI_in c) hwf hm1 hb1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl)
  have hia1 := h.keep hk1 (keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl)
  simp only [PcOk] at hpc1
  have e : ∀ r, (envB m0 d [] (fun _ ↦ 0) 0).regs r = reg d r := fun _ ↦ rfl
  rw [show (SBool.cmp .bit .W64 (.reg .r9) (.reg .rcx)).eval
      (envB m0 d [] (fun _ ↦ 0) 0) = testBitW (rcW (11 - stepN m0)) (2 * i) by
    simp only [SBool.eval, Sym.eval, e, h.r9, h.rcx]
    exact rcBit _ (by omega) _ (by have := h.lt; omega)] at hpc1
  obtain ⟨d1, pc1⟩ := st
  simp only at hpc1 hb1 hk1 hia1
  cases hb : testBitW (rcW (11 - stepN m0)) (2 * i) with
  | true =>
    simp only [hb, ↓reduceIte] at hpc1
    rw [lbl hp b28_in_code rfl] at hpc1
    subst hpc1
    have hwf2 := wfScr hpre hk1.body (x := sA m0 + BitVec.ofNat 64 (25600 + 32 * i)) (n := 32)
      (by rw [g.sa (by have := h.lt; omega)]; omega)
      (by rw [g.sa (by have := h.lt; omega)]; have := h.lt; omega) (vars := fun _ ↦ 0) (ret := 0)
    have hm2 : Match (envB m0 d1 [(sA m0 + BitVec.ofNat 64 (25600 + 32 * i), 32)] (fun _ ↦ 0) 0)
        (pairS .r10) d1 :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hk1.body.rsp, trivial⟩ trivial trivial
        ⟨by show reg d1 .r10 = sA m0 + BitVec.ofNat 64 (25600 + 32 * i) + BitVec.ofInt 64 24
            rw [hia1.r10]; simp only [BitVec.ofInt_ofNat]; bv_omega, trivial⟩
    refine Body.blk (o' := 24) g hk1.body hwf2 (blk hp b28_in_code (by simp [b28])) e28 nofun hm2
      (by decide +kernel) (hex0 (by decide +kernel)) fun st hm3 hpc3 hb3 _ ↦ ?_
    simp only [PcOk] at hpc3
    obtain ⟨d3, pc3⟩ := st
    simp only at hpc3 hb3
    subst hpc3
    have hk3 := hk1.blk hpre (spillsI_in c) hwf2 hm3 hb3 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (keepR_regs hm3 (by decide +kernel) fun _ ↦ rfl)
    refine cont d3 ⟨hia1.keep hk3 (keepR_regs hm3 (by decide +kernel) fun _ ↦ rfl), ?_⟩
    rw [show reg d3 .rbx = _ from hm3.regs .rbx _ rfl, show reg d3 .r11 = _ from hm3.regs .r11 _ rfl]
    simp only [Sym.eval]
    rw [wLoad hpre (fun _ h ↦ h) hk1.body (i := 2 * i) (oo := 0) (by have := h.lt; omega)
      (by rw [BitVec.add_zero]; unfold lA; bv_omega)]
    unfold bitSel
    rw [hb]
    rfl
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at hpc1
    subst hpc1
    have hwf2 := wf0 (pre_stack hpre) hk1.body (vars := fun _ ↦ 0) (ret := 0)
    have hm2 : Match (envB m0 d1 [] (fun _ ↦ 0) 0) (fr 24) d1 :=
      match_ofMachine ⟨rfl, trivial⟩ ⟨hk1.body.rsp, trivial⟩ trivial trivial trivial
    refine Body.blk (o' := 24) g hk1.body hwf2 (blk hp b31_in_code (by simp [b31])) e31 nofun hm2
      (by decide +kernel) (hex0 (by decide +kernel)) fun st hm3 hpc3 hb3 _ ↦ ?_
    simp only [PcOk] at hpc3
    rw [lbl hp b29_in_code rfl] at hpc3
    obtain ⟨d3, pc3⟩ := st
    simp only at hpc3 hb3
    subst hpc3
    have hk3 := hk1.blk hpre (spillsI_in c) hwf2 hm3 hb3 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (keepR_regs hm3 (by decide +kernel) fun _ ↦ rfl)
    refine cont d3 ⟨hia1.keep hk3 (keepR_regs hm3 (by decide +kernel) fun _ ↦ rfl), ?_⟩
    rw [show reg d3 .rbx = _ from hm3.regs .rbx _ rfl, show reg d3 .r11 = _ from hm3.regs .r11 _ rfl]
    unfold bitSel
    rw [hb]
    rfl

omit [Host] in
theorem bits_xs (w : Array EW) (k : UInt64) : xs (bitSel w k) (2 * 32) = bitsOf w k :=
  (bits_eq w k).symm

/-- `b29`: the term `2 i + 1`, the sum; the next head or out. -/
theorem iaStep2 (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : IB m0 a c p s1 i d) {R : MachineState → Prop}
    (hnext : ∀ d', IA m0 a c p s1 (i + 1) d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b30Offset)⟩)
    (hout : ∀ d', IX m0 a c p s1 d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b32Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b29Offset)⟩ := by
  have g := geo_of hpre
  have hia := h.base
  have hk := hia.k0
  have hlt := hia.lt
  have hwf := wfScr hpre hk.body (x := sA m0 + BitVec.ofNat 64 (25600 + 32 * i)) (n := 32)
    (by rw [g.sa (by omega)]; omega) (by rw [g.sa (by omega)]; omega) (vars := fun _ ↦ 0) (ret := 0)
  have hm : Match (envB m0 d [(sA m0 + BitVec.ofNat 64 (25600 + 32 * i), 32)] (fun _ ↦ 0) 0)
      (pairS .r10) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hk.body.rsp, trivial⟩ trivial trivial
      ⟨by show reg d .r10 = sA m0 + BitVec.ofNat 64 (25600 + 32 * i) + BitVec.ofInt 64 24
          rw [hia.r10]; simp only [BitVec.ofInt_ofNat]; bv_omega, trivial⟩
  refine Body.blk (o' := 24) g hk.body hwf (blk hp b29_in_code (by simp [b29])) e29 nofun hm
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hk1 := hk.blk hpre (spillsI_in c) hwf hm1 hb1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl)
  have hkr : ∀ r ∈ [Reg64.r9, .rdi, .rsi, .r15, .r8], reg st.data r = reg d r :=
    keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  have e : ∀ r, (envB m0 d [(sA m0 + BitVec.ofNat 64 (25600 + 32 * i), 32)] (fun _ ↦ 0) 0).regs r =
      reg d r := fun _ ↦ rfl
  have hmask : BinOp.apply .sar .W64 (BinOp.apply .shl .W64 (BinOp.apply .shr .W64 (reg d .r9)
      (reg d .rcx)) (BitVec.ofNat 64 62)) (BitVec.ofNat 64 63) =
      maskOf (testBitW (rcW (11 - stepN m0)) (2 * i + 1)) := by
    rw [hia.r9, hia.rcx]; exact rcMask _ (by have := pre_step hpre; omega) _ (by omega)
  have hw1 := wLoad (c := c) hpre (fun _ h ↦ h) hk.body
    (x := sA m0 + BitVec.ofNat 64 (25600 + 32 * i)) (n := 32) (vars := fun _ ↦ 0) (ret := 0)
    (i := 2 * i + 1) (oo := 16) (by omega) (by unfold lA; bv_omega)
  have hacc : ewArg (reg st.data .rdx) (reg st.data .rax) =
      xs (bitSel c.weights (rcW (11 - stepN m0))) (2 * (i + 1)) := by
    rw [show reg st.data .rdx = _ from hm1.regs .rdx _ rfl,
      show reg st.data .rax = _ from hm1.regs .rax _ rfl]
    simp only [Sym.eval, e]
    rw [hmask, and_mask, mask_and, NativeRustcVmX64.Arrays.xor_eval,
      NativeRustcVmX64.Arrays.xor_eval, NativeRustcVmX64.Arrays.xor_eval,
      NativeRustcVmX64.Arrays.xor_eval, NativeRustcVmX64.Arrays.ewArg_xor,
      NativeRustcVmX64.Arrays.ewArg_xor]
    rw [sel_ewArg', hw1, h.t, hia.acc]
    exact xs_two (bitSel c.weights (rcW (11 - stepN m0))) i _ rfl
  have hrcx : reg st.data .rcx = BitVec.ofNat 64 (2 * (i + 1)) := by
    rw [show reg st.data .rcx = _ from hm1.regs .rcx _ rfl]
    simp only [Sym.eval, e, add64, hia.rcx]
    bv_omega
  have hr10 : reg st.data .r10 = sA m0 + BitVec.ofNat 64 (25624 + 32 * (i + 1)) := by
    rw [show reg st.data .r10 = _ from hm1.regs .r10 _ rfl]
    simp only [Sym.eval, e, add64, hia.r10]
    bv_omega
  simp only [PcOk] at hpc1
  rw [show (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 2) (.reg .rcx)) (.lit 64)).eval
      (envB m0 d [(sA m0 + BitVec.ofNat 64 (25600 + 32 * i), 32)] (fun _ ↦ 0) 0) =
      decide (i + 1 = 32) by
    simp only [SBool.eval, Sym.eval, e, add64, hia.rcx, NativeRustcVmX64.KeccakGkr.VerifyLayer.eq64]
    by_cases he : i + 1 = 32
    · simp only [he, decide_true, beq_iff_eq]; bv_omega
    · simp only [he, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro he'; have := congrArg BitVec.toNat he'
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this; omega] at hpc1
  obtain ⟨d1, pc1⟩ := st
  simp only at hpc1 hb1 hk1 hkr hacc hrcx hr10
  by_cases he : i + 1 = 32
  · simp only [he, decide_true, ↓reduceIte] at hpc1
    rw [lbl hp b32_in_code rfl] at hpc1
    subst hpc1
    refine hout d1 ⟨hk1, ?_, ?_, ?_, ?_⟩
    · rw [hacc, he, bits_xs]
    · rw [hkr .rdi (by simp), hkr .rsi (by simp)]; exact hia.seg
    · rw [hkr .r15 (by simp)]; exact hia.r15
    · rw [hkr .r8 (by simp)]; exact hia.r8
  · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    subst hpc1
    exact hnext d1 ⟨hk1, hrcx, hr10, by rw [hkr .r9 (by simp)]; exact hia.r9, hacc,
      by rw [hkr .rdi (by simp), hkr .rsi (by simp)]; exact hia.seg,
      by rw [hkr .r15 (by simp)]; exact hia.r15, by rw [hkr .r8 (by simp)]; exact hia.r8,
      by omega⟩

/-- **The first segment's loop.** -/
theorem iotaLoop1 (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : IA m0 a c p s1 0 d) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b32Offset) ∧ IX m0 a c p s1 st.data)
      ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b30Offset)⟩ := by
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b30Offset) ∧ ∃ i, 32 - i = n ∧
    IA m0 a c p s1 i st.data) (fun n st ⟨hpc, i, hn, hi⟩ ↦ ?_) ⟨rfl, 0, rfl, h⟩
  obtain ⟨d', pc⟩ := st
  simp only at hpc hi
  subst hpc
  exact iaStep hp hpre hi fun d1 hb ↦ iaStep2 hp hpre hb
    (fun d2 hn' ↦ .done _ (.inr ⟨_, by have := hi.lt; have := hn'.lt; omega, rfl, i + 1, rfl, hn'⟩))
    fun d2 hx ↦ .done _ (.inl ⟨rfl, hx⟩)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
