module

public import NativeRustcVmArm.Code.Vm.IvWord.Names
public import NativeRustcVmArm.Keccak.WordsIv.Call
public import NativeRustcVmArm.Keccak.WordsIv.Blocks
public import NativeRustcVmArm.Keccak.WordsHash.Lane

/-!
# `keccak256_words::<fiat_shamir_iv's closure>`: one lane of a block

A block's lanes, the block's first word `B` in register `r` (X25 for a whole block, X24 for the
last). `LaneAt m0 k r A B j sL sZ`: before lane `j`, the lanes `A` with the closure's words `B`
to `B + j - 1` XORed into the first `j`, at lane `j`'s call block `sL` if word `B + j` is below
the count, else at its zero block `sZ`. `laneZ_step`: lane `j` past the count, XORed with zero
(one block); `laneL_step`: lane `j` below it, `iv_word`'s call (`call_iv`) and the XOR of its
result (two blocks). `X0At`: lane 16's word in X0 after the 16 lanes; `lane16L_step` (its call),
`lane16Z_step` (zero).
-/

namespace NativeRustcVmArm.WordsIv

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep load_of_wordAt)
open NativeRustcVmArm.WordsHash (frame nb Lanes pre pre_succ lanes_step frame_mapped
  frame_noWrap frame_aligned eor64 add64 ult_ofNat)

@[expose] public section

/-- Word `B + j` (`B` in `r`) is below the count X23. -/
def cmpI (r : XReg) (j : Nat) : SBool :=
  .cmp .ult .W64 (.bin .add .W64 (.reg r) (.lit j)) (.reg .X23)

/-- **Before lane `j`** of the block whose first word `B` is in `r`; for the last block, before
lane 16, X2 is `B + 16`. -/
def LaneAt [Host] (m0 : MachineData) (k : Nat) (r : XReg) (A : KeccakState) (B j sL sZ : Nat)
    (st : MachineState) : Prop :=
  Ctx m0 st.data ∧ Lanes m0 st.data (pre A (wv m0) B j) ∧
    (st.data.regs.getXReg r).toBitVec = BitVec.ofNat 64 B ∧
    (j = 16 → r = .X24 → (st.data.regs.getXReg .X2).toBitVec = BitVec.ofNat 64 (B + 16)) ∧
    st.pc = if B + j < m0.regs.X1.toNat then Host.addrOf (k + sL) else Host.addrOf (k + sZ)

/-- **After the 16 lanes**, lane 16's word in X0, at `s`. -/
def X0At [Host] (m0 : MachineData) (k : Nat) (r : XReg) (A : KeccakState) (B s : Nat)
    (st : MachineState) : Prop :=
  Ctx m0 st.data ∧ Lanes m0 st.data (pre A (wv m0) B 16) ∧
    (st.data.regs.getXReg r).toBitVec = BitVec.ofNat 64 B ∧
    (st.data.regs.getXReg .X0).toBitVec = (wv m0 (B + 16)).toBitVec ∧
    st.pc = Host.addrOf (k + s)

end

public section

theorem count_lt {m0 : MachineData} (g : Geo m0) : m0.regs.X1.toNat < 2 ^ 32 + 2 := by
  have := g.cnt
  have := g.small
  omega

theorem nb_le {m0 : MachineData} (g : Geo m0) : 17 * nb m0 ≤ m0.regs.X4.toNat + 1 := by
  have := g.len
  unfold nb
  omega

theorem x1_bv (m0 : MachineData) : m0.regs.X1.toBitVec = BitVec.ofNat 64 m0.regs.X1.toNat := by
  simp

/-- The comparison of word `B + j` with the count. -/
theorem cmpI_eval [Labels] {m0 m : MachineData} (g : Geo m0) (hc : Ctx m0 m) {r : XReg} {B : Nat}
    (hB : (m.regs.getXReg r).toBitVec = BitVec.ofNat 64 B) (hBle : B ≤ 17 * nb m0) {j : Nat}
    (hj : j ≤ 17) {rs : List (BitVec 64 × Nat)} :
    (cmpI r j).eval (Env.ofMachine m rs) = decide (B + j < m0.regs.X1.toNat) := by
  have := nb_le g
  have := g.small
  have h1 := m0.regs.X1.toNat_lt
  simp only [cmpI, SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, add64, Env.ofMachine_regs]
  rw [hB, hc.x23, x1_bv, ult_ofNat (by omega) h1]

/-- The branch after lane `j`. -/
theorem lane_pc {m0 m : MachineData} [Host] (g : Geo m0) (hc : Ctx m0 m) {r : XReg} {B : Nat}
    (hB : (m.regs.getXReg r).toBitVec = BitVec.ofNat 64 B) (hBle : B ≤ 17 * nb m0)
    {rs : List (BitVec 64 × Nat)} {j : Nat} (hj : j ≤ 17) {st : MachineState} {s n : Nat}
    {pos : Bool} {lbl : Label} {sL sZ k : Nat}
    (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : s + n = if pos then sZ else sL)
    (hpc : PcOk (Env.ofMachine m rs) (.cond (if pos then cmpI r j else .not (cmpI r j)) lbl)
      (Host.addrOf (k + s + n)) st) :
    st.pc = if B + j < m0.regs.X1.toNat then Host.addrOf (k + sL) else
      Host.addrOf (k + sZ) := by
  have hev := cmpI_eval (rs := rs) g hc hB hBle hj
  simp only [PcOk] at hpc
  rw [hpc, Nat.add_assoc, hnext]
  cases pos <;> simp only [Bool.false_eq_true, ↓reduceIte, SBool.eval, hev] at hlab ⊢ <;>
    rw [hlab] <;> by_cases h : B + j < m0.regs.X1.toNat <;> simp [h]

variable [Host]

/-- The frame's environment and a state matching it. -/
theorem frame_env {m0 m : MachineData} (g : Geo m0) (hc : Ctx m0 m) :
    (Env.ofMachine m [(frame m0, 288)]).WF ∧ Match (Env.ofMachine m [(frame m0, 288)]) startMain m :=
  ⟨Env.wf_of ⟨⟨frame_mapped g.stk hc.kept, frame_noWrap g.stk⟩, trivial⟩
      (List.pairwise_singleton _ _),
    match_ofMachine ⟨rfl, fun _ => frame_aligned g.stk, trivial⟩
      (by rw [hc.sp]; simp [Sym.eval]) trivial trivial trivial trivial⟩

/-- **A lane past the count**: lane `j` XORed with zero. -/
theorem laneZ_step {k : Nat} {m0 m : MachineData} (g : Geo m0) {r : XReg} {A : KeccakState}
    {B j : Nat} (hj : j < 16) (hBle : B ≤ 17 * nb m0) (hz : m0.regs.X1.toNat ≤ B + j)
    (hc : Ctx m0 m) (hl : Lanes m0 m (pre A (wv m0) B j))
    (hB : (m.regs.getXReg r).toBitVec = BitVec.ofNat 64 B)
    {blk : List Directive} {s : Nat} {S : SState} {x : Exit}
    (hk : blk.IsInfixAt Host.prog (k + s)) (hx : exec blk startMain = some (S, x))
    (hmem : S.mem = [⟨0, 8 + 8 * j, 8, .load 0 (8 + 8 * j) 8⟩]) (hsp : S.sp = .ptr 0 0)
    (hregs : AllOf (fun r => S.reg r = some (.reg r)) ctxRegs) (hr : S.reg r = some (.reg r))
    (hx2 : j + 1 = 16 → r = .X24 → S.reg .X2 = some (.bin .add .W64 (.reg r) (.lit 16)))
    {pos : Bool} {lbl : Label}
    (hexit : x = .cond (if pos then cmpI r (j + 1) else .not (cmpI r (j + 1))) lbl)
    {sL sZ : Nat} (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : s + blk.length = if pos then sZ else sL) :
    Eventually (step1 Host.exe) (LaneAt m0 k r A B (j + 1) sL sZ) ⟨m, Host.addrOf (k + s)⟩ := by
  obtain ⟨hwf, hm⟩ := frame_env g hc
  refine exec_then hk hx hwf hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ctx_step g.stk hc hm' hwf rfl hsp hregs fun w hw => ?_
    rw [hmem, List.mem_singleton] at hw
    subst hw
    exact ⟨rfl, by simp; omega⟩
  · have := lanes_step hm' rfl (by omega) hmem hl (x := Keccak.lane A j ^^^ wv m0 (B + j))
      (by
        rw [wv_of_ge hz, UInt64.xor_zero]
        show (Env.ofMachine m [(frame m0, 288)]).load 0 (8 + 8 * j) 8 = _
        rw [load_of_wordAt (r := 0) (hl j (by omega))]
        simp [pre])
    rwa [pre_succ _ _ _ _ rfl] at this
  · exact (hm'.regs r _ hr).trans hB
  · intro h16 h24
    rw [hm'.regs .X2 _ (hx2 h16 h24)]
    show BinOp.apply .add .W64 (m.regs.getXReg r).toBitVec (BitVec.ofNat 64 16) = _
    rw [add64, hB, BitVec.ofNat_add_ofNat]
  · rw [hexit] at hpc
    exact lane_pc g hc hB hBle (by omega) hlab hnext hpc

/-- **A lane below the count**: `iv_word`'s call, and lane `j` XORed with its result. -/
theorem laneL_step (hiv : Spec (label NativeRustcVmArm.Vm.IvWord.entryLabel) NativeRustcVmArm.IvWordPre
      NativeRustcVmArm.IvWordPost) {k : Nat} {m0 m : MachineData} (g : Geo m0) {r : XReg}
    {A : KeccakState} {B j : Nat} (hj : j < 16) (hBle : B ≤ 17 * nb m0)
    (hin : B + j < m0.regs.X1.toNat) (hc : Ctx m0 m) (hl : Lanes m0 m (pre A (wv m0) B j))
    (hB : (m.regs.getXReg r).toBitVec = BitVec.ofNat 64 B) (hrs : calleeSaved r = true)
    {blkC : List Directive} {sC : Nat} {SC : SState}
    (hkC : blkC.IsInfixAt Host.prog (k + sC))
    (hxC : exec blkC startMain = some (SC, .call NativeRustcVmArm.Vm.IvWord.entryLabel))
    (hC0 : SC.reg .X0 = some (.reg .X22)) (hC1 : SC.reg .X1 = some (.reg .X21))
    (hC2 : SC.reg .X2 = some (if j = 0 then .reg r else .bin .add .W64 (.reg r) (.lit j)))
    (hCmem : SC.mem = []) (hCsp : SC.sp = .ptr 0 0)
    (hCregs : AllOf (fun r => SC.reg r = some (.reg r)) ctxRegs) (hCr : SC.reg r = some (.reg r))
    {blkX : List Directive} {sX : Nat} {S : SState} {x : Exit}
    (hkX : blkX.IsInfixAt Host.prog (k + sX)) (hsX : sC + blkC.length = sX)
    (hx : exec blkX startMain = some (S, x))
    (hmem : S.mem = [⟨0, 8 + 8 * j, 8, .bin .eor .W64 (.load 0 (8 + 8 * j) 8) (.reg .X0)⟩])
    (hsp : S.sp = .ptr 0 0)
    (hregs : AllOf (fun r => S.reg r = some (.reg r)) ctxRegs) (hr : S.reg r = some (.reg r))
    (hx2 : j + 1 = 16 → r = .X24 → S.reg .X2 = some (.bin .add .W64 (.reg r) (.lit 16)))
    {pos : Bool} {lbl : Label}
    (hexit : x = .cond (if pos then cmpI r (j + 1) else .not (cmpI r (j + 1))) lbl)
    {sL sZ : Nat} (hlab : Labels.label lbl = Host.addrOf (k + if pos then sL else sZ))
    (hnext : sX + blkX.length = if pos then sZ else sL) :
    Eventually (step1 Host.exe) (LaneAt m0 k r A B (j + 1) sL sZ) ⟨m, Host.addrOf (k + sC)⟩ := by
  obtain ⟨hwf, hm⟩ := frame_env g hc
  refine exec_then hkC hxC hwf hm fun st1 hm1 hpc1 => ?_
  have hc1 : Ctx m0 st1.data := ctx_step g.stk hc hm1 hwf rfl hCsp hCregs fun w hw => by
    rw [hCmem] at hw; cases hw
  have hl1 : Lanes m0 st1.data (pre A (wv m0) B j) := fun i hi =>
    wordAt_keep (r := 0) (sz := 288) hm1 rfl (by omega) (by rw [hCmem]; rfl) (hl i hi)
  have hB1 : (st1.data.regs.getXReg r).toBitVec = BitVec.ofNat 64 B := (hm1.regs r _ hCr).trans hB
  refine call_iv hiv g hc1 ((hm1.regs .X0 _ hC0).trans hc.x22) ((hm1.regs .X1 _ hC1).trans hc.x21)
    (i := B + j) ?_ hin hpc1 fun st2 hpc2 hd2 hs2 hx0 => ?_
  · rw [hm1.regs .X2 _ hC2]
    split
    · next h0 => subst h0; exact hB
    · show BinOp.apply .add .W64 (m.regs.getXReg r).toBitVec (BitVec.ofNat 64 j) = _
      rw [add64, hB, BitVec.ofNat_add_ofNat]
  have hc2 := ctx_call hc1 hd2 hs2
  have hl2 : Lanes m0 st2.data (pre A (wv m0) B j) := by rw [Lanes, hd2]; exact hl1
  have hB2 : (st2.data.regs.getXReg r).toBitVec = BitVec.ofNat 64 B := by
    rw [hs2.1 r hrs]; exact hB1
  obtain ⟨m2, pc2⟩ := st2
  simp only at hpc2 hc2 hl2 hB2 hx0
  rw [Nat.add_assoc, hsX] at hpc2
  subst hpc2
  obtain ⟨hwf2, hm2⟩ := frame_env g hc2
  refine exec_then hkX hx hwf2 hm2 fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ctx_step g.stk hc2 hm' hwf2 rfl hsp hregs fun w hw => ?_
    rw [hmem, List.mem_singleton] at hw
    subst hw
    exact ⟨rfl, by simp; omega⟩
  · have := lanes_step hm' rfl (by omega) hmem hl2 (x := Keccak.lane A j ^^^ wv m0 (B + j))
      (by
        show BinOp.apply .eor .W64 ((Env.ofMachine m2 [(frame m0, 288)]).load 0 (8 + 8 * j) 8)
          (m2.regs.getXReg .X0).toBitVec = _
        rw [eor64, load_of_wordAt (r := 0) (hl2 j (by omega)), hx0]
        simp [pre])
    rwa [pre_succ _ _ _ _ rfl] at this
  · exact (hm'.regs r _ hr).trans hB2
  · intro h16 h24
    rw [hm'.regs .X2 _ (hx2 h16 h24)]
    show BinOp.apply .add .W64 (m2.regs.getXReg r).toBitVec (BitVec.ofNat 64 16) = _
    rw [add64, hB2, BitVec.ofNat_add_ofNat]
  · rw [hexit] at hpc
    exact lane_pc g hc2 hB2 hBle (by omega) hlab hnext hpc

/-- **Lane 16's word below the count**: `iv_word`'s call, to `s`. -/
theorem lane16L_step (hiv : Spec (label NativeRustcVmArm.Vm.IvWord.entryLabel) NativeRustcVmArm.IvWordPre
      NativeRustcVmArm.IvWordPost) {k : Nat} {m0 m : MachineData} (g : Geo m0) {r : XReg}
    {A : KeccakState} {B : Nat} (hin : B + 16 < m0.regs.X1.toNat) (hc : Ctx m0 m)
    (hl : Lanes m0 m (pre A (wv m0) B 16))
    (hB : (m.regs.getXReg r).toBitVec = BitVec.ofNat 64 B) (hrs : calleeSaved r = true)
    {blkC : List Directive} {sC : Nat} {SC : SState}
    (hkC : blkC.IsInfixAt Host.prog (k + sC))
    (hxC : exec blkC startMain = some (SC, .call NativeRustcVmArm.Vm.IvWord.entryLabel))
    (hC0 : SC.reg .X0 = some (.reg .X22)) (hC1 : SC.reg .X1 = some (.reg .X21)) {v2 : Sym}
    (hC2 : SC.reg .X2 = some v2)
    (hv2 : v2.eval (Env.ofMachine m [(frame m0, 288)]) = BitVec.ofNat 64 (B + 16))
    (hCmem : SC.mem = []) (hCsp : SC.sp = .ptr 0 0)
    (hCregs : AllOf (fun r => SC.reg r = some (.reg r)) ctxRegs) (hCr : SC.reg r = some (.reg r))
    {s : Nat} (hs : sC + blkC.length = s) :
    Eventually (step1 Host.exe) (X0At m0 k r A B s) ⟨m, Host.addrOf (k + sC)⟩ := by
  obtain ⟨hwf, hm⟩ := frame_env g hc
  refine exec_then hkC hxC hwf hm fun st1 hm1 hpc1 => ?_
  have hc1 : Ctx m0 st1.data := ctx_step g.stk hc hm1 hwf rfl hCsp hCregs fun w hw => by
    rw [hCmem] at hw; cases hw
  have hl1 : Lanes m0 st1.data (pre A (wv m0) B 16) := fun i hi =>
    wordAt_keep (r := 0) (sz := 288) hm1 rfl (by omega) (by rw [hCmem]; rfl) (hl i hi)
  have hB1 : (st1.data.regs.getXReg r).toBitVec = BitVec.ofNat 64 B := (hm1.regs r _ hCr).trans hB
  refine call_iv hiv g hc1 ((hm1.regs .X0 _ hC0).trans hc.x22) ((hm1.regs .X1 _ hC1).trans hc.x21)
    (i := B + 16) ((hm1.regs .X2 _ hC2).trans hv2) hin hpc1 fun st2 hpc2 hd2 hs2 hx0 =>
      .done _ ⟨ctx_call hc1 hd2 hs2, by rw [Lanes, hd2]; exact hl1,
        by rw [hs2.1 r hrs]; exact hB1, hx0, by rw [hpc2, Nat.add_assoc, hs]⟩

/-- **Lane 16's word past the count**: zero, to `s`. -/
theorem lane16Z_step {k : Nat} {m0 m : MachineData} (g : Geo m0) {r : XReg} {A : KeccakState}
    {B : Nat} (hz : m0.regs.X1.toNat ≤ B + 16) (hc : Ctx m0 m)
    (hl : Lanes m0 m (pre A (wv m0) B 16))
    (hB : (m.regs.getXReg r).toBitVec = BitVec.ofNat 64 B)
    {blk : List Directive} {s0 : Nat} {S : SState} {lbl : Label}
    (hk : blk.IsInfixAt Host.prog (k + s0)) (hx : exec blk startMain = some (S, .jump lbl))
    (h0 : S.reg .X0 = some (.lit 0)) (hmem : S.mem = []) (hsp : S.sp = .ptr 0 0)
    (hregs : AllOf (fun r => S.reg r = some (.reg r)) ctxRegs) (hr : S.reg r = some (.reg r))
    {s : Nat} (hlab : Labels.label lbl = Host.addrOf (k + s)) :
    Eventually (step1 Host.exe) (X0At m0 k r A B s) ⟨m, Host.addrOf (k + s0)⟩ := by
  obtain ⟨hwf, hm⟩ := frame_env g hc
  refine exec_then hk hx hwf hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ctx_step g.stk hc hm' hwf rfl hsp hregs fun w hw => by rw [hmem] at hw; cases hw
  · exact fun i hi =>
      wordAt_keep (r := 0) (sz := 288) hm' rfl (by omega) (by rw [hmem]; rfl) (hl i hi)
  · exact (hm'.regs r _ hr).trans hB
  · rw [hm'.regs .X0 _ h0, wv_of_ge hz]
    rfl
  · simp only [PcOk] at hpc
    rw [hpc, hlab]

end

end NativeRustcVmArm.WordsIv
