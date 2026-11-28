module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.ProjInner

/-!
# `verify_layer` on x86-64: the masked sum at one bit

From `NativeRustcVmX64.Vm.VerifyLayer.label_4` (`PHead j`): no instance weight (`b7`, `b11`), one (`b8`, `b9`), more
(`b8`, `b13`, the pairs' loop, `b21`); an odd count's last weight (`MT`, `b22`, `b23`, `b4`): at
`NativeRustcVmX64.Vm.VerifyLayer.label_3` with the masked sum at bit `j` in RDI, RSI (`MQ`): `masked`.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- **At `NativeRustcVmX64.Vm.VerifyLayer.label_3`**: the masked sum at bit `j` in RDI, RSI. -/
structure MQ [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (j : Nat) (d : MachineData) : Prop where
  core : PCore m0 a c p s1 j d
  acc : ewArg (reg d .rdi) (reg d .rsi) = maskedOf c.mu j

/-- **An odd count's last weight** to add, at `NativeRustcVmX64.Vm.VerifyLayer.label_15`. -/
structure MT [Labels] (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (p : Array EW)
    (s1 : TState) (j : Nat) (d : MachineData) : Prop where
  core : PCore m0 a c p s1 j d
  rcx : reg d .rcx = BitVec.ofNat 64 (c.mu.size / 2 * 2)
  rdx : reg d .rdx = bitJ j
  acc : ewArg (reg d .rdi) (reg d .rsi) = xs (muSel c.mu j) (c.mu.size / 2 * 2)
  odd : c.mu.size % 2 = 1

end

public section

theorem low1 : ∀ n < 17, BitVec.ofInt 64 (Int.ofBytes ((NativeRustcVm.wordBytes (UInt64.ofNat n)).take 1)) =
    BitVec.ofNat 64 n := by decide +kernel

/-- A small word's low byte, loaded. -/
theorem load1_small [Labels] {env : Env} {r o n : Nat} (hn : n < 17)
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 o) (UInt64.ofNat n)) :
    env.load r o 1 = BitVec.ofNat 64 n := by
  have h1 : NativeRustcVm.BytesAt env.mem0 (env.base r + BitVec.ofNat 64 o)
      ((NativeRustcVm.wordBytes (UInt64.ofNat n)).take 1) := fun i hi ↦ by
    have hi' : i < 1 := by simp at hi; omega
    have := h i (by simp [NativeRustcVm.wordBytes, LeanVM.Protocol.KeccakHash.wordBytes]; omega)
    rw [List.getElem_take]
    exact this
  rw [Env.load_of_bytesAt (n := 1) (by simp [NativeRustcVm.wordBytes,
    LeanVM.Protocol.KeccakHash.wordBytes]) h1]
  exact low1 n hn

/-- A small frame word's low byte, loaded. -/
theorem fload1 [Labels] {m0 d : MachineData} {ex : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {o n : Nat} (hn : n < 17)
    (h : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) o) n.toUInt64) :
    (envB m0 d ex vars ret).load 0 o 1 = BitVec.ofNat 64 n :=
  load1_small hn h

theorem test1 : ∀ n < 17, CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (BitVec.ofNat 64 n)
    (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) = decide (n % 2 = 0) := by decide +kernel

theorem masked_xs {mu : Array EW} {j : Nat} (h : mu.size ≤ 16) :
    xs (muSel mu j) mu.size = maskedOf mu j := (masked_eq mu j h).symm

theorem xor_zero (x : BitVec 64) : BinOp.apply .xor .W64 x (BitVec.ofNat 64 0) = x := by
  simp [BinOp.apply]

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}
  {p : Array EW} {s1 : TState} {j : Nat}

theorem muSize (hpre : VerifyLayerPre a s c m0) {d : MachineData} (hc : PCore m0 a c p s1 j d) :
    c.mu.size ≤ 16 := by
  have := (hc.body.claim hpre fun _ h ↦ h).2.1.1
  simpa [NativeRustcVm.KeccakGkr.muCap] using this

/-- `b4`: R8, RDX added into RDI, RSI. -/
theorem step4 (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (hc : PCore m0 a c p s1 j d) {R : MachineState → Prop}
    (cont : ∀ d', PCore m0 a c p s1 j d' →
      ewArg (reg d' .rdi) (reg d' .rsi) =
        ewArg (reg d .rdi) (reg d .rsi) + ewArg (reg d .r8) (reg d .rdx) →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b5Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b4Offset)⟩ := by
  have hwf4 := wf0 (pre_stack hpre) hc.body (vars := fun _ ↦ 0) (ret := 0)
  have hm4 : Match (envB m0 d [] (fun _ ↦ 0) 0) (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hc.body.rsp, trivial⟩ trivial trivial trivial
  refine hc.pure hpre hwf4 (blk hp b4_in_code (by simp [b4])) e4 nofun hm4 (by decide +kernel)
    rfl (by decide +kernel) fun st hm5 hpc5 _ hc5 ↦ ?_
  simp only [PcOk] at hpc5
  obtain ⟨d5, pc5⟩ := st
  simp only at hpc5 hm5 hc5
  subst hpc5
  refine cont d5 hc5 ?_
  rw [show reg d5 .rdi = _ from hm5.regs .rdi _ rfl, show reg d5 .rsi = _ from hm5.regs .rsi _ rfl]
  simp only [Sym.eval]
  exact NativeRustcVmX64.Arrays.ewArg_xor _ _ _ _

/-- The alias of `b23`'s instance weight. -/
theorem a23_eval {d : MachineData} (hc : PCore m0 a c p s1 j d) {i : Nat}
    (hrcx : reg d .rcx = BitVec.ofNat 64 i) (ex : List (BitVec 64 × Nat)) :
    a23.eval (envB m0 d ex (fun _ ↦ 0) 0) =
      cA m0 + BitVec.ofNat 64 (24 + 16 * i) + BitVec.ofInt 64 0 := by
  have hl : (envB m0 d ex (fun _ ↦ 0) 0).load 0 48 8 = cA m0 + 24#64 :=
    fload8 (sp48 hc.sp)
  have hr : (envB m0 d ex (fun _ ↦ 0) 0).regs .rcx = BitVec.ofNat 64 i := hrcx
  simp only [a23, Sym.eval, hl, hr, add64]
  simp only [BinOp.apply, low_W64, ext_W64, shiftCount, shiftMask, BitVec.ofInt_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp [low, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- `b23`: the instance weight `i` into R8, RDX. -/
theorem step23 (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (hc : PCore m0 a c p s1 j d) {i : Nat} (hi : i < c.mu.size)
    (hrcx : reg d .rcx = BitVec.ofNat 64 i) {R : MachineState → Prop}
    (cont : ∀ d', PCore m0 a c p s1 j d' → ewArg (reg d' .r8) (reg d' .rdx) = c.mu.getD i 0 →
      reg d' .rdi = reg d .rdi → reg d' .rsi = reg d .rsi →
      Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b4Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b23Offset)⟩ := by
  have g := geo_of hpre
  have hlen := muSize hpre hc
  have hwf2 := wfSub hpre hc.body (x := cA m0 + BitVec.ofNat 64 (24 + 16 * i))
    (n := 16) (by rw [g.ca (by omega)]; omega) (by rw [g.ca (by omega)]; omega)
    (vars := fun _ ↦ 0) (ret := 0)
  have hm2 : Match (envB m0 d [(cA m0 + BitVec.ofNat 64 (24 + 16 * i), 16)]
      (fun _ ↦ 0) 0) (fr 24 [16] [] [] [(a23, 1, 0)]) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hc.body.rsp, trivial⟩ trivial trivial
      ⟨a23_eval hc hrcx _, trivial⟩
  refine hc.pure hpre hwf2 (blk hp b23_in_code (by simp [b23])) e23 nofun hm2
    (by decide +kernel) rfl (by decide +kernel) fun st hm3 hpc3 _ hc3 ↦ ?_
  simp only [PcOk] at hpc3
  rw [lbl hp b4_in_code rfl] at hpc3
  obtain ⟨d3, pc3⟩ := st
  simp only at hpc3 hm3 hc3
  subst hpc3
  have hk3 : ∀ r ∈ [Reg64.rdi, .rsi], reg d3 r = reg d r :=
    keepR_regs hm3 (by decide +kernel) fun _ ↦ rfl
  refine cont d3 hc3 ?_ (hk3 .rdi (by simp)) (hk3 .rsi (by simp))
  rw [show reg d3 .r8 = _ from hm3.regs .r8 _ rfl, show reg d3 .rdx = _ from hm3.regs .rdx _ rfl]
  exact muLoad hpre (fun _ h ↦ h) hc.body hi (oo := 0) (by rw [BitVec.add_zero]; bv_omega)

omit [Host] in
theorem last_sum {mu : Array EW} {j : Nat} (hlen : mu.size ≤ 16) (hodd : mu.size % 2 = 1) :
    xs (muSel mu j) (mu.size / 2 * 2) + muSel mu j (mu.size - 1) = maskedOf mu j := by
  rw [← masked_xs hlen, show mu.size / 2 * 2 = mu.size - 1 by omega]
  conv => rhs; rw [show mu.size = mu.size - 1 + 1 by omega]
  rw [xs_succ]

/-- `b22`, `b23`, `b4`: an odd count's last weight. -/
theorem lastW (hp : Placed code k) (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : MT m0 a c p s1 j d) {R : MachineState → Prop}
    (cont : ∀ d', MQ m0 a c p s1 j d' → Eventually (step1 Host.exe) R ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b5Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b22Offset)⟩ := by
  have hWo := wFront_outs hpre
  have hc := h.core
  have hlen := muSize hpre hc
  have hodd := h.odd
  have hi : c.mu.size / 2 * 2 = c.mu.size - 1 := by omega
  have hwf : (envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0).WF :=
    wfR hpre hc.body (r := projectRegion) (by simp)
  have hm : Match (envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0) (projS 16) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hc.body.rsp, trivial⟩ trivial
      ⟨by show (reg d .rcx).toNat < 16
          rw [h.rcx, BitVec.toNat_ofNat]; omega, trivial⟩
      ⟨by show reg d .r15 = projectAddr + BitVec.ofInt 64 0
          rw [hc.r15]; simp, trivial⟩
  have e3 : ∀ r, (envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0).regs r = reg d r := fun _ ↦ rfl
  have hw : BinOp.apply .and .W64 (reg d .rdx) ((envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0).load 1
      (0 + (BinOp.apply .mul .W64 (reg d .rcx) (BitVec.ofNat 64 8)).toNat) 8) =
      BinOp.apply .and .W64 (bitJ j) (rmfeProjectW.getD (c.mu.size - 1) 0).toBitVec := by
    rw [h.rcx, mul8 (by omega), Nat.zero_add, hi, projLoad hpre hWo hc.body (by omega), h.rdx]
  refine hc.pure hpre hwf (blk hp b22_in_code (by simp [b22])) e22 nofun hm (by decide +kernel) rfl
    (by decide +kernel) fun st hm1 hpc1 _ hc1 ↦ ?_
  have hk1 : ∀ r ∈ [Reg64.rcx, .rdi, .rsi], reg st.data r = reg d r :=
    keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  simp only [PcOk] at hpc1
  have hbit := projBit' (c.mu.size - 1) (by omega) j hc.lt
  have hcond : (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rdx)
      (.loadx 1 0 (.bin .mul .W64 (.reg .rcx) (.lit 8)) 8)) (.lit 0)).eval
      (envB m0 d [(projectAddr, 128)] (fun _ ↦ 0) 0) =
      !testBitW (rmfeProjectW.getD (c.mu.size - 1) 0) j := by
    simp only [SBool.eval, Sym.eval, e3]
    rw [hw]; exact hbit
  rw [hcond] at hpc1
  have hacc := h.acc
  cases hb : testBitW (rmfeProjectW.getD (c.mu.size - 1) 0) j with
  | false =>
    simp only [hb, Bool.not_false, ↓reduceIte] at hpc1
    rw [lbl hp b4_in_code rfl] at hpc1
    obtain ⟨d1, pc1⟩ := st
    simp only at hpc1 hm1 hc1 hk1
    subst hpc1
    have hz := eq0 (hbit.trans (by rw [hb]; rfl))
    have h8 : reg d1 .r8 = 0#64 := by
      rw [show reg d1 .r8 = _ from hm1.regs .r8 _ rfl]
      simp only [Sym.eval, e3]; rw [hw, hz]
    have hdx : reg d1 .rdx = 0#64 := by
      rw [show reg d1 .rdx = _ from hm1.regs .rdx _ rfl]
      simp only [Sym.eval, e3]; rw [hw, hz]
    refine step4 hp hpre hc1 fun d5 hc5 hs5 ↦ cont d5 ⟨hc5, ?_⟩
    rw [hs5, h8, hdx, ewArg_zero, hk1 .rdi (by simp), hk1 .rsi (by simp), hacc,
      ← last_sum hlen hodd, muSel_def, hb]
    rfl
  | true =>
    simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨d1, pc1⟩ := st
    simp only at hpc1 hm1 hc1 hk1
    subst hpc1
    refine step23 hp hpre hc1 (i := c.mu.size - 1) (by omega)
      (by rw [hk1 .rcx (by simp), h.rcx, hi]) fun d3 hc3 hld hdi hsi ↦
        step4 hp hpre hc3 fun d5 hc5 hs5 ↦ cont d5 ⟨hc5, ?_⟩
    rw [hs5, hld, hdi, hsi, hk1 .rdi (by simp), hk1 .rsi (by simp), hacc,
      ← last_sum hlen hodd, muSel_def, hb]
    rfl

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
