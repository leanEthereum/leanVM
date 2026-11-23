module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.B26

/-!
# `verify_layer` on x86-64: ι's second segment

`b32` (from `IX`, the first segment's bits in RDX, RAX) spills the second segment's weight to the
frame's `24` and `72`, loads `KECCAK_RC[23 - step]` into R8 and enters `NativeRustcVmX64.Vm.VerifyLayer.label_26` with no
bit summed (`JA 0`): `b32Run`. The loop (`b36`, the raw `bt` of bit `2 i`; `b34` or `b37`
the term; `b35` the next bit and the sum) sums the bit weights it selects in R15, RBX: `iotaLoop2`,
to `NativeRustcVmX64.Vm.VerifyLayer.label_28` (`JX`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The spills of ι's second loop: `spillsI` and the second segment's weight at `24`, `72`. -/
def spillsJ (m0 : MachineData) (c : KeccakClaimW) : List (Nat × UInt64) :=
  spillsI m0 c ++ [(24, ((segK m0 c).getD 1 0).c0), (72, ((segK m0 c).getD 1 0).c1)]

/-- **The second segment's loop head**, `2 i` bits summed. -/
structure JA [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (i : Nat) (d : MachineData) : Prop where
  k0 : K0 m0 a c p s1 (spillsJ m0 c) d
  rcx : reg d .rcx = BitVec.ofNat 64 (2 * i)
  r9 : reg d .r9 = sA m0 + BitVec.ofNat 64 (25624 + 32 * i)
  r8 : reg d .r8 = (rcW (23 - stepN m0)).toBitVec
  acc : ewArg (reg d .r15) (reg d .rbx) = xs (bitSel c.weights (rcW (23 - stepN m0))) (2 * i)
  b1 : ewArg (reg d .rdx) (reg d .rax) = bitsOf c.weights (rcW (11 - stepN m0))
  seg : ewArg (reg d .rdi) (reg d .rsi) = (segK m0 c).getD 0 0
  lt : i < 32

/-- After the term `2 i`, in R11, R10. -/
structure JB [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (i : Nat) (d : MachineData) : Prop where
  base : JA m0 a c p s1 i d
  t : ewArg (reg d .r11) (reg d .r10) = bitSel c.weights (rcW (23 - stepN m0)) (2 * i)

/-- **The second segment done**, at `NativeRustcVmX64.Vm.VerifyLayer.label_28`. -/
structure JX [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (d : MachineData) : Prop where
  k0 : K0 m0 a c p s1 (spillsJ m0 c) d
  b2 : ewArg (reg d .r15) (reg d .rbx) = bitsOf c.weights (rcW (23 - stepN m0))
  b1 : ewArg (reg d .rdx) (reg d .rax) = bitsOf c.weights (rcW (11 - stepN m0))
  seg : ewArg (reg d .rdi) (reg d .rsi) = (segK m0 c).getD 0 0

/-- The registers the loop keeps. -/
def jaRegs : List Reg64 := [.rcx, .r9, .r8, .r15, .rbx, .rdx, .rax, .rdi, .rsi, .r12, .r13]

end

public section

theorem spillsJ_in (c : KeccakClaimW) {m0 : MachineData} :
    ∀ q ∈ spillsJ m0 c, 24 ≤ q.1 ∧ q.1 + 8 ≤ 232 := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact spillsI_in c q hq
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}
  {p : Array EW} {s1 : TState} {i : Nat}

/-- **Into ι's second loop**: `b32`. -/
theorem b32Run (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : IX m0 a c p s1 d) {R : MachineState → Prop}
    (cont : ∀ d', JA m0 a c p s1 0 d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b36Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b32Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hst : stepN m0 < 12 := pre_step hpre
  have hk := h.k0
  have hwf : (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0).WF :=
    wfR hpre hk.body (r := rcRegion) (by simp)
  have h56 : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) 56) (.ofBitVec (reg m0 .rdx)) :=
    hk.sp (56, _) (by simp [spillsI, spills3])
  have hi : i23.eval (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0) =
      BitVec.ofNat 64 (8 * (23 - stepN m0)) := idxLoad hst h56 (by decide) (by decide)
  have hm : Match (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0)
      (fr 24 [192] [] [(i23, 185)] [(.reg .r8, 1, 0)]) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hk.body.rsp, trivial⟩ trivial
      ⟨by show (i23.eval (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0)).toNat < 185
          rw [hi, BitVec.toNat_ofNat]; omega, trivial⟩
      ⟨by show reg d .r8 = rcAddr + BitVec.ofInt 64 0
          rw [h.r8]; simp, trivial⟩
  refine Body.blk (o' := 24) g hk.body hwf (blk hp b32_in_code (by simp [b32])) e32 nofun hm
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  simp only [PcOk] at hpc1
  rw [lbl hp b36_in_code rfl] at hpc1
  obtain ⟨d1, pc1⟩ := st
  simp only at hpc1 hm1 hb1
  subst hpc1
  have e : ∀ r, (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0).regs r = reg d r := fun _ ↦ rfl
  have hfrA := frSame_blk (o := 80) (n := 1936) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hfrB := frSame_blk (o := 32) (n := 40) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hkr : ∀ r ∈ [Reg64.rax, .rdx, .rdi, .rsi, .r12, .r13], reg d1 r = reg d r :=
    keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  have hs1 : 1 < (segK m0 c).size := by have := hk.ssize; omega
  have hw24 := fwW (o := 24) hm1 rfl rfl (by decide) (by decide +kernel)
    (w := ((segK m0 c).getD 1 0).c0) (by
      rw [← frLoad (o := 232) (j := 1) (ex := [(rcAddr, 192)]) (vars := fun _ ↦ 0) (ret := 0)
        hk.seg hs1]
      rfl)
  have hw72 := fwW (o := 72) hm1 rfl rfl (by decide) (by decide +kernel)
    (w := ((segK m0 c).getD 1 0).c1) (by
      rw [← frLoad (o := 232) (j := 1) (ex := [(rcAddr, 192)]) (vars := fun _ ↦ 0) (ret := 0)
        hk.seg hs1]
      rfl)
  have hspI : FWs m0 d1.dmem (spillsI m0 c) := by
    intro q hq
    have hq' := hk.sp q hq
    simp only [spillsI, spills3, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact (hfrB.sub (o' := 32) (n' := 8) (by decide) (by decide)).word hq' (by decide)
    · exact (hfrB.sub (o' := 40) (n' := 8) (by decide) (by decide)).word hq' (by decide)
    · exact (hfrB.sub (o' := 48) (n' := 8) (by decide) (by decide)).word hq' (by decide)
    · exact (hfrB.sub (o' := 56) (n' := 8) (by decide) (by decide)).word hq' (by decide)
    · exact (hfrB.sub (o' := 64) (n' := 8) (by decide) (by decide)).word hq' (by decide)
    · exact (hfrA.sub (o' := 80) (n' := 8) (by decide) (by decide)).word hq' (by decide)
    · exact (hfrA.sub (o' := 96) (n' := 8) (by decide) (by decide)).word hq' (by decide)
    · exact (hfrA.sub (o' := 224) (n' := 8) (by decide) (by decide)).word hq' (by decide)
    · exact (hfrA.sub (o' := 120) (n' := 8) (by decide) (by decide)).word hq' (by decide)
    · exact (hfrA.sub (o' := 128) (n' := 8) (by decide) (by decide)).word hq' (by decide)
  refine cont d1 ⟨⟨hb1, ts_blk0 hpre hwf hm1 (by decide +kernel) (by decide +kernel) hk.ts, ?_, ?_,
    ?_, ?_, hk.psize, hk.ssize⟩, ?_, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · exact (hfrA.sub (o' := 472) (n' := 752) (by decide) (by decide)).ews hk.prod
      (by rw [Array.length_toList, hk.psize])
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hspI q hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hw24
      · exact hw72
  · exact (hfrA.sub (o' := 232) (n' := 64) (by decide) (by decide)).ews hk.seg
      (by rw [Array.length_toList]; have := segK_le4 (pre_seg hpre); omega)
  · rw [hkr .r12 (by simp), hkr .r13 (by simp)]; exact hk.acc
  · rw [show reg d1 .rcx = _ from hm1.regs .rcx _ rfl]; rfl
  · rw [show reg d1 .r9 = _ from hm1.regs .r9 _ rfl]
    simp only [Sym.eval, e, h.r15, add64]
  · rw [show reg d1 .r8 = _ from hm1.regs .r8 _ rfl]
    change (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0).load 1 (0 + (i23.eval (envB m0 d [(rcAddr, 192)] (fun _ ↦ 0) 0)).toNat) 8 = _
    rw [hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.zero_add]
    exact rcLoad hpre hWo hk.body (by omega)
  · rw [show reg d1 .r15 = _ from hm1.regs .r15 _ rfl, show reg d1 .rbx = _ from hm1.regs .rbx _ rfl]
    rfl
  · rw [hkr .rdx (by simp), hkr .rax (by simp)]; exact h.acc
  · rw [hkr .rdi (by simp), hkr .rsi (by simp)]; exact h.seg

theorem JA.keep {d d' : MachineData} (h : JA m0 a c p s1 i d)
    (hk : K0 m0 a c p s1 (spillsJ m0 c) d') (hr : ∀ r ∈ jaRegs, reg d' r = reg d r) :
    JA m0 a c p s1 i d' :=
  ⟨hk, by rw [hr .rcx (by simp [jaRegs])]; exact h.rcx, by rw [hr .r9 (by simp [jaRegs])]; exact h.r9,
    by rw [hr .r8 (by simp [jaRegs])]; exact h.r8,
    by rw [hr .r15 (by simp [jaRegs]), hr .rbx (by simp [jaRegs])]; exact h.acc,
    by rw [hr .rdx (by simp [jaRegs]), hr .rax (by simp [jaRegs])]; exact h.b1,
    by rw [hr .rdi (by simp [jaRegs]), hr .rsi (by simp [jaRegs])]; exact h.seg, h.lt⟩

/-- `b36`, then `b34` or `b37`: the term `2 i`. -/
theorem jaStep (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : JA m0 a c p s1 i d) {R : MachineState → Prop}
    (cont : ∀ d', JB m0 a c p s1 i d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b35Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b36Offset)⟩ := by
  have g := geo_of hpre
  have hk := h.k0
  have hwf := wf0 (pre_stack hpre) hk.body (vars := fun _ ↦ 0) (ret := 0)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) 0) (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hk.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g hk.body hwf (blk hp b36_in_code (by simp [b36])) e36 nofun hm
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hk1 := hk.blk hpre (spillsJ_in c) hwf hm1 hb1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl)
  have hja1 := h.keep hk1 (keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl)
  simp only [PcOk] at hpc1
  have e : ∀ r, (envB m0 d [] (fun _ ↦ 0) 0).regs r = reg d r := fun _ ↦ rfl
  rw [show (SBool.cmp .bit .W64 (.reg .r8) (.reg .rcx)).eval
      (envB m0 d [] (fun _ ↦ 0) 0) = testBitW (rcW (23 - stepN m0)) (2 * i) by
    simp only [SBool.eval, Sym.eval, e, h.r8, h.rcx]
    exact rcBit _ (by omega) _ (by have := h.lt; omega)] at hpc1
  obtain ⟨d1, pc1⟩ := st
  simp only at hpc1 hb1 hk1 hja1
  cases hb : testBitW (rcW (23 - stepN m0)) (2 * i) with
  | true =>
    simp only [hb, ↓reduceIte] at hpc1
    rw [lbl hp b34_in_code rfl] at hpc1
    subst hpc1
    have hwf2 := wfScr hpre hk1.body (x := sA m0 + BitVec.ofNat 64 (25600 + 32 * i)) (n := 32)
      (by rw [g.sa (by have := h.lt; omega)]; omega)
      (by rw [g.sa (by have := h.lt; omega)]; have := h.lt; omega) (vars := fun _ ↦ 0) (ret := 0)
    have hm2 : Match (envB m0 d1 [(sA m0 + BitVec.ofNat 64 (25600 + 32 * i), 32)] (fun _ ↦ 0) 0)
        (pairS .r9) d1 :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hk1.body.rsp, trivial⟩ trivial trivial
        ⟨by show reg d1 .r9 = sA m0 + BitVec.ofNat 64 (25600 + 32 * i) + BitVec.ofInt 64 24
            rw [hja1.r9]; simp only [BitVec.ofInt_ofNat]; bv_omega, trivial⟩
    refine Body.blk (o' := 24) g hk1.body hwf2 (blk hp b34_in_code (by simp [b34])) e34 nofun hm2
      (by decide +kernel) (hex0 (by decide +kernel)) fun st hm3 hpc3 hb3 _ ↦ ?_
    simp only [PcOk] at hpc3
    obtain ⟨d3, pc3⟩ := st
    simp only at hpc3 hb3
    subst hpc3
    have hk3 := hk1.blk hpre (spillsJ_in c) hwf2 hm3 hb3 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (keepR_regs hm3 (by decide +kernel) fun _ ↦ rfl)
    refine cont d3 ⟨hja1.keep hk3 (keepR_regs hm3 (by decide +kernel) fun _ ↦ rfl), ?_⟩
    rw [show reg d3 .r11 = _ from hm3.regs .r11 _ rfl, show reg d3 .r10 = _ from hm3.regs .r10 _ rfl]
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
    refine Body.blk (o' := 24) g hk1.body hwf2 (blk hp b37_in_code (by simp [b37])) e37 nofun hm2
      (by decide +kernel) (hex0 (by decide +kernel)) fun st hm3 hpc3 hb3 _ ↦ ?_
    simp only [PcOk] at hpc3
    rw [lbl hp b35_in_code rfl] at hpc3
    obtain ⟨d3, pc3⟩ := st
    simp only at hpc3 hb3
    subst hpc3
    have hk3 := hk1.blk hpre (spillsJ_in c) hwf2 hm3 hb3 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (keepR_regs hm3 (by decide +kernel) fun _ ↦ rfl)
    refine cont d3 ⟨hja1.keep hk3 (keepR_regs hm3 (by decide +kernel) fun _ ↦ rfl), ?_⟩
    rw [show reg d3 .r11 = _ from hm3.regs .r11 _ rfl, show reg d3 .r10 = _ from hm3.regs .r10 _ rfl]
    unfold bitSel
    rw [hb]
    rfl

/-- `b35`: the term `2 i + 1`, the sum; the next head or out. -/
theorem jaStep2 (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : JB m0 a c p s1 i d) {R : MachineState → Prop}
    (hnext : ∀ d', JA m0 a c p s1 (i + 1) d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b36Offset)⟩)
    (hout : ∀ d', JX m0 a c p s1 d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b38Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b35Offset)⟩ := by
  have g := geo_of hpre
  have hja := h.base
  have hk := hja.k0
  have hlt := hja.lt
  have hwf := wfScr hpre hk.body (x := sA m0 + BitVec.ofNat 64 (25600 + 32 * i)) (n := 32)
    (by rw [g.sa (by omega)]; omega) (by rw [g.sa (by omega)]; omega) (vars := fun _ ↦ 0) (ret := 0)
  have hm : Match (envB m0 d [(sA m0 + BitVec.ofNat 64 (25600 + 32 * i), 32)] (fun _ ↦ 0) 0)
      (pairS .r9) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hk.body.rsp, trivial⟩ trivial trivial
      ⟨by show reg d .r9 = sA m0 + BitVec.ofNat 64 (25600 + 32 * i) + BitVec.ofInt 64 24
          rw [hja.r9]; simp only [BitVec.ofInt_ofNat]; bv_omega, trivial⟩
  refine Body.blk (o' := 24) g hk.body hwf (blk hp b35_in_code (by simp [b35])) e35 nofun hm
    (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hk1 := hk.blk hpre (spillsJ_in c) hwf hm1 hb1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl)
  have hkr : ∀ r ∈ [Reg64.r8, .rdx, .rax, .rdi, .rsi], reg st.data r = reg d r :=
    keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  have e : ∀ r, (envB m0 d [(sA m0 + BitVec.ofNat 64 (25600 + 32 * i), 32)] (fun _ ↦ 0) 0).regs r =
      reg d r := fun _ ↦ rfl
  have hmask : BinOp.apply .sar .W64 (BinOp.apply .shl .W64 (BinOp.apply .shr .W64 (reg d .r8)
      (reg d .rcx)) (BitVec.ofNat 64 62)) (BitVec.ofNat 64 63) =
      maskOf (testBitW (rcW (23 - stepN m0)) (2 * i + 1)) := by
    rw [hja.r8, hja.rcx]; exact rcMask _ (by have := pre_step hpre; omega) _ (by omega)
  have hw1 := wLoad (c := c) hpre (fun _ h ↦ h) hk.body
    (x := sA m0 + BitVec.ofNat 64 (25600 + 32 * i)) (n := 32) (vars := fun _ ↦ 0) (ret := 0)
    (i := 2 * i + 1) (oo := 16) (by omega) (by unfold lA; bv_omega)
  have hacc : ewArg (reg st.data .r15) (reg st.data .rbx) =
      xs (bitSel c.weights (rcW (23 - stepN m0))) (2 * (i + 1)) := by
    rw [show reg st.data .r15 = _ from hm1.regs .r15 _ rfl,
      show reg st.data .rbx = _ from hm1.regs .rbx _ rfl]
    simp only [Sym.eval, e]
    rw [hmask, and_mask, mask_and, NativeRustcVmX64.Arrays.xor_eval,
      NativeRustcVmX64.Arrays.xor_eval, NativeRustcVmX64.Arrays.xor_eval,
      NativeRustcVmX64.Arrays.xor_eval, NativeRustcVmX64.Arrays.ewArg_xor,
      NativeRustcVmX64.Arrays.ewArg_xor]
    rw [sel_ewArg', hw1, h.t, hja.acc]
    exact xs_two (bitSel c.weights (rcW (23 - stepN m0))) i _ rfl
  have hrcx : reg st.data .rcx = BitVec.ofNat 64 (2 * (i + 1)) := by
    rw [show reg st.data .rcx = _ from hm1.regs .rcx _ rfl]
    simp only [Sym.eval, e, add64, hja.rcx]
    bv_omega
  have hr9 : reg st.data .r9 = sA m0 + BitVec.ofNat 64 (25624 + 32 * (i + 1)) := by
    rw [show reg st.data .r9 = _ from hm1.regs .r9 _ rfl]
    simp only [Sym.eval, e, add64, hja.r9]
    bv_omega
  simp only [PcOk] at hpc1
  rw [show (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 2) (.reg .rcx)) (.lit 64)).eval
      (envB m0 d [(sA m0 + BitVec.ofNat 64 (25600 + 32 * i), 32)] (fun _ ↦ 0) 0) =
      decide (i + 1 = 32) by
    simp only [SBool.eval, Sym.eval, e, add64, hja.rcx, NativeRustcVmX64.KeccakGkr.VerifyLayer.eq64]
    by_cases he : i + 1 = 32
    · simp only [he, decide_true, beq_iff_eq]; bv_omega
    · simp only [he, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro he'; have := congrArg BitVec.toNat he'
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this; omega] at hpc1
  obtain ⟨d1, pc1⟩ := st
  simp only at hpc1 hb1 hk1 hkr hacc hrcx hr9
  by_cases he : i + 1 = 32
  · simp only [he, decide_true, ↓reduceIte] at hpc1
    rw [lbl hp b38_in_code rfl] at hpc1
    subst hpc1
    refine hout d1 ⟨hk1, ?_, ?_, ?_⟩
    · rw [hacc, he, bits_xs]
    · rw [hkr .rdx (by simp), hkr .rax (by simp)]; exact hja.b1
    · rw [hkr .rdi (by simp), hkr .rsi (by simp)]; exact hja.seg
  · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    subst hpc1
    exact hnext d1 ⟨hk1, hrcx, hr9, by rw [hkr .r8 (by simp)]; exact hja.r8, hacc,
      by rw [hkr .rdx (by simp), hkr .rax (by simp)]; exact hja.b1,
      by rw [hkr .rdi (by simp), hkr .rsi (by simp)]; exact hja.seg, by omega⟩

/-- **The second segment's loop.** -/
theorem iotaLoop2 (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : JA m0 a c p s1 0 d) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b38Offset) ∧ JX m0 a c p s1 st.data)
      ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b36Offset)⟩ := by
  refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b36Offset) ∧ ∃ i, 32 - i = n ∧
    JA m0 a c p s1 i st.data) (fun n st ⟨hpc, i, hn, hi⟩ ↦ ?_) ⟨rfl, 0, rfl, h⟩
  obtain ⟨d', pc⟩ := st
  simp only at hpc hi
  subst hpc
  exact jaStep hp hpre hi fun d1 hb ↦ jaStep2 hp hpre hb
    (fun d2 hn' ↦ .done _ (.inr ⟨_, by have := hi.lt; have := hn'.lt; omega, rfl, i + 1, rfl, hn'⟩))
    fun d2 hx ↦ .done _ (.inl ⟨rfl, hx⟩)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
