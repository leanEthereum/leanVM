module

public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Keccak.WordsIv.Tail
public import NativeRustcVmArm.Keccak.WordsIv.BlocksFull

/-!
# `keccak256_words::<fiat_shamir_iv's closure>`: the whole blocks

`FullHead m0 k b`: at the head of whole block `b < nb` (X25 its first word `17 b`), the lanes
the state after `b` blocks. Every word of a whole block is below the count (`full_lt`), so each
lane's branch goes on to the next lane's call: the head (`full_head`), the lanes (`full{j}`,
`laneL_step`), lane 16's word (`full16`), its XOR and the call of `keccak_f` (`call_kf`) and the
next block's branch (`full_end`) take the machine to the head of block `b + 1` or, after the last,
to the last block's head (`TailStart`). `full_loop`: by induction on the blocks left.
-/

namespace NativeRustcVmArm.WordsIv

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (wordAt_keep load_of_wordAt)
open NativeRustcVmArm.WordsHash (frame nb Lanes pre pre_zero pre_succ pre_17 lanes_step
  lanes_congr add64 eor64)
open NativeRustcVm.Keccak (wordBlocks)
open Vm.Keccak256WordsOfFiatShamirIv

@[expose] public section

/-- **At the head of whole block `b`.** -/
def FullHead [Host] (m0 : MachineData) (k b : Nat) (st : MachineState) : Prop :=
  Ctx m0 st.data ∧ Lanes m0 st.data (Keccak.lane (wordBlocks (wv m0) b)) ∧
    (st.data.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 (17 * b) ∧ b < nb m0 ∧
    st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b25Offset)

/-- Before lane `j` of whole block `b`. -/
abbrev FullLane [Host] (m0 : MachineData) (k b j sL sZ : Nat) : MachineState → Prop :=
  LaneAt m0 k .X25 (wordBlocks (wv m0) b) (17 * b) j sL sZ

end

public section

variable [Host]

/-- **The head of whole block `b`**: to lane 0. -/
theorem full_head {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0) {b : Nat}
    {st : MachineState} (h : FullHead m0 k b st) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 0 164 280 st' ∧ b < nb m0) st := by
  obtain ⟨hc, hl, hB, hb, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hB hpc
  subst hpc
  have hin := full_lt g hb (j := 0) (by decide)
  obtain ⟨hwf, hm⟩ := frame_env g hc
  refine exec_then (ic hp b25_in_code (List.cons_ne_nil _ _)) fullHead hwf hm
    fun st hm' hpc => .done _ ⟨⟨?_, ?_, ?_, fun _ h => absurd h (by decide), ?_⟩, hb⟩
  · exact ctx_step g.stk hc hm' hwf rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
      (fun w hw => by cases hw)
  · rw [pre_zero]
    exact fun i hi => wordAt_keep (r := 0) (sz := 288) hm' rfl (by omega) rfl (hl i hi)
  · exact (hm'.regs .X25 _ rfl).trans hB
  · have := count_lt g
    simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, Env.ofMachine_regs] at hpc
    rw [hpc]
    show (if (!((m.regs.getXReg .X25).toBitVec).ult (m.regs.getXReg .X23).toBitVec) = true then _
      else _) = _
    rw [hB, hc.x23, x1_bv, ult_nat (by omega) (by omega)]
    simp only [show 17 * b < m0.regs.X1.toNat by omega, hin, decide_true, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    rfl

set_option hygiene false in
/-- Lane `j < 16` of whole block `b`: its call `c` and XOR `x` (`bc`, `bx`), the branch to the
next lane's call (`pos`) or zero block (`¬ pos`) at `bl`. -/
local macro "full_lane " j:num c:ident x:ident bc:ident bx:ident ps:ident bl:ident : tactic =>
  `(tactic| (
  obtain ⟨⟨hc, hl, hB, -, hpc⟩, hb⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hB hpc
  have hin := full_lt g hb (j := $j) (by decide)
  simp only [hin, ↓reduceIte] at hpc
  subst hpc
  refine Eventually.mono (laneL_step hiv g (B := 17 * b) (j := $j) (by decide) (by omega) hin hc hl
    hB rfl (ic hp $bc (List.cons_ne_nil _ _)) $c rfl rfl rfl rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl
    (ic hp $bx (List.cons_ne_nil _ _)) rfl $x rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl
    (fun _ h => absurd h (by decide)) (pos := $ps) rfl (label_at hp $bl rfl) rfl)
    fun _ h => ⟨h, hb⟩))

theorem full0 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 0 164 280 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 1 287 174 st' ∧ b < nb m0) st := by
  full_lane 0 fullC0 fullX0 b26_in_code b27_in_code true b45_in_code

theorem full1 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 1 287 174 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 2 298 181 st' ∧ b < nb m0) st := by
  full_lane 1 fullC1 fullX1 b45_in_code b46_in_code false b29_in_code

theorem full2 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 2 298 181 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 3 309 188 st' ∧ b < nb m0) st := by
  full_lane 2 fullC2 fullX2 b47_in_code b48_in_code false b30_in_code

theorem full3 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 3 309 188 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 4 320 195 st' ∧ b < nb m0) st := by
  full_lane 3 fullC3 fullX3 b49_in_code b50_in_code false b31_in_code

theorem full4 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 4 320 195 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 5 331 202 st' ∧ b < nb m0) st := by
  full_lane 4 fullC4 fullX4 b51_in_code b52_in_code false b32_in_code

theorem full5 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 5 331 202 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 6 342 209 st' ∧ b < nb m0) st := by
  full_lane 5 fullC5 fullX5 b53_in_code b54_in_code false b33_in_code

theorem full6 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 6 342 209 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 7 353 216 st' ∧ b < nb m0) st := by
  full_lane 6 fullC6 fullX6 b55_in_code b56_in_code false b34_in_code

theorem full7 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 7 353 216 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 8 364 223 st' ∧ b < nb m0) st := by
  full_lane 7 fullC7 fullX7 b57_in_code b58_in_code false b35_in_code

theorem full8 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 8 364 223 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 9 375 230 st' ∧ b < nb m0) st := by
  full_lane 8 fullC8 fullX8 b59_in_code b60_in_code false b36_in_code

theorem full9 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 9 375 230 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 10 386 237 st' ∧ b < nb m0) st := by
  full_lane 9 fullC9 fullX9 b61_in_code b62_in_code false b37_in_code

theorem full10 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 10 386 237 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 11 397 244 st' ∧ b < nb m0) st := by
  full_lane 10 fullC10 fullX10 b63_in_code b64_in_code false b38_in_code

theorem full11 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 11 397 244 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 12 408 251 st' ∧ b < nb m0) st := by
  full_lane 11 fullC11 fullX11 b65_in_code b66_in_code false b39_in_code

theorem full12 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 12 408 251 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 13 419 258 st' ∧ b < nb m0) st := by
  full_lane 12 fullC12 fullX12 b67_in_code b68_in_code false b40_in_code

theorem full13 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 13 419 258 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 14 430 265 st' ∧ b < nb m0) st := by
  full_lane 13 fullC13 fullX13 b69_in_code b70_in_code false b41_in_code

theorem full14 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 14 430 265 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 15 441 272 st' ∧ b < nb m0) st := by
  full_lane 14 fullC14 fullX14 b71_in_code b72_in_code false b42_in_code

theorem full15 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 15 441 272 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullLane m0 k b 16 147 452 st' ∧ b < nb m0) st := by
  full_lane 15 fullC15 fullX15 b73_in_code b74_in_code true b22_in_code

/-- **Lane 16's word** of whole block `b`. -/
theorem full16 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {b : Nat} {st : MachineState} (h : FullLane m0 k b 16 147 452 st ∧ b < nb m0) :
    Eventually (step1 Host.exe)
      (fun st' => X0At m0 k .X25 (wordBlocks (wv m0) b) (17 * b) 152 st' ∧ b < nb m0) st := by
  obtain ⟨⟨hc, hl, hB, -, hpc⟩, hb⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hB hpc
  have hin := full_lt g hb (j := 16) (by decide)
  simp only [hin, ↓reduceIte] at hpc
  subst hpc
  refine Eventually.mono (lane16L_step hiv g (B := 17 * b) hin hc hl hB rfl
    (ic hp b22_in_code (List.cons_ne_nil _ _)) fullC16 rfl rfl rfl ?_ rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl) fun _ h => ⟨h, hb⟩
  show BinOp.apply .add .W64 (d.regs.getXReg .X25).toBitVec (BitVec.ofNat 64 16) = _
  rw [add64, hB, BitVec.ofNat_add_ofNat]

omit [Host] in
/-- The next block's branch: taken after the last whole block. -/
theorem next_cmp {m0 : MachineData} (g : Geo m0) {b : Nat} (hb : b < nb m0) :
    (BitVec.ofNat 64 (17 * nb m0) == BitVec.ofNat 64 (17 * b) + BitVec.ofNat 64 17) =
      decide (b + 1 = nb m0) := by
  have := nb_le g
  have := g.small
  rw [BitVec.ofNat_add_ofNat]
  by_cases h : b + 1 = nb m0
  · rw [show 17 * nb m0 = 17 * b + 17 by omega, beq_self_eq_true]
    exact (decide_eq_true h).symm
  · simp only [h, decide_false]
    rw [beq_eq_false_iff_ne]
    intro he
    have := congrArg BitVec.toNat he
    have h1 : 17 * nb m0 < 2 ^ 64 := by omega
    have h2 : 17 * b + 17 < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
    exact h (by omega)

/-- **The end of whole block `b`**: lane 16's XOR, `keccak_f`, and the next block's branch. -/
theorem full_end (hkf : Spec (label NativeRustcVmArm.Vm.KeccakF.entryLabel) NativeRustcVmArm.KeccakFPre
      NativeRustcVmArm.KeccakFPost) {k : Nat} (hp : Placed code k) {m0 : MachineData}
    (g : Geo m0) (hrc : NativeRustcVmArm.RcAt m0 NativeRustcVmArm.keccak256WordsStack)
    {b : Nat} {st : MachineState}
    (h : X0At m0 k .X25 (wordBlocks (wv m0) b) (17 * b) 152 st ∧ b < nb m0) :
    Eventually (step1 Host.exe) (fun st' => FullHead m0 k (b + 1) st' ∨ TailStart m0 k st') st := by
  obtain ⟨⟨hc, hl, hB, hx0, hpc⟩, hb⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hB hx0 hpc
  subst hpc
  obtain ⟨hwf, hm⟩ := frame_env g hc
  refine exec_then (ic hp b23_in_code (List.cons_ne_nil _ _)) fullEnd hwf hm
    fun st2 hm2 hpc2 => ?_
  have hc2 : Ctx m0 st2.data := ctx_step g.stk hc hm2 hwf rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact ⟨rfl, by decide⟩
  have hl2 : Lanes m0 st2.data (Keccak.lane (Native.Keccak.Proof.xorRate (wordBlocks (wv m0) b)
      fun k => wv m0 (17 * b + k))) := by
    have := lanes_step (j := 16) hm2 rfl (by omega) rfl hl
      (x := Keccak.lane (wordBlocks (wv m0) b) 16 ^^^ wv m0 (17 * b + 16)) (by
        show BinOp.apply .eor .W64 ((Env.ofMachine m [(frame m0, 288)]).load 0 (8 + 8 * 16) 8)
          (m.regs.getXReg .X0).toBitVec = _
        rw [eor64, load_of_wordAt (r := 0) (hl 16 (by omega)), hx0]
        simp [pre])
    rw [pre_succ _ _ _ _ rfl] at this
    exact lanes_congr this fun i hi => pre_17 _ _ _ hi
  have hx0' : st2.data.regs.X0.toBitVec = frame m0 + BitVec.ofNat 64 8 :=
    (hm2.regs .X0 _ rfl).trans (by simp [Sym.eval])
  have hB2 : (st2.data.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 (17 * b) :=
    (hm2.regs .X25 _ rfl).trans hB
  refine call_kf hkf g.stk hrc hc2 hl2 hx0' hpc2 fun st3 hpc3 hc3 hl3 hsv3 => ?_
  have hB3 : (st3.data.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 (17 * b) := by
    rw [hsv3 .X25 rfl]; exact hB2
  obtain ⟨m3, pc3⟩ := st3
  simp only at hpc3 hc3 hl3 hB3
  rw [NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b23_length, NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b23Length] at hpc3
  subst hpc3
  obtain ⟨hwf3, hm3⟩ := frame_env g hc3
  refine exec_then (ic hp b24_in_code (List.cons_ne_nil _ _)) fullNext hwf3 hm3
    fun st4 hm4 hpc4 => .done _ ?_
  have hc4 : Ctx m0 st4.data := ctx_step g.stk hc3 hm4 hwf3 rfl rfl
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ (fun w hw => by cases hw)
  have hl4 : Lanes m0 st4.data (Keccak.lane (wordBlocks (wv m0) (b + 1))) :=
    fun i hi => wordAt_keep (r := 0) (sz := 288) hm4 rfl (by omega) rfl (hl3 i hi)
  have hcmp := next_cmp g hb
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64] at hpc4
  have hpc4' : st4.pc = if b + 1 = nb m0 then Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b2Offset) else Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b25Offset) := by
    rw [hpc4]
    show (if ((m3.regs.getXReg .X24).toBitVec == BinOp.apply .add .W64
      (m3.regs.getXReg .X25).toBitVec 17#64) = true then _ else _) = _
    rw [add64, hc3.x24, hB3, show (17#64 : BitVec 64) = BitVec.ofNat 64 17 from rfl, hcmp]
    by_cases h : b + 1 = nb m0
    · simp only [h, decide_true, ↓reduceIte]
      exact label_at hp b2_in_code rfl
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      rfl
  have hB4 : (st4.data.regs.getXReg .X25).toBitVec = BitVec.ofNat 64 (17 * (b + 1)) := by
    rw [hm4.regs .X25 _ rfl]
    show BinOp.apply .add .W64 (m3.regs.getXReg .X25).toBitVec (BitVec.ofNat 64 17) = _
    rw [add64, hB3, BitVec.ofNat_add_ofNat, show 17 * b + 17 = 17 * (b + 1) by omega]
  by_cases h : b + 1 = nb m0
  · right
    refine ⟨hc4, ?_, ?_⟩
    · rw [stI, ← h]; exact hl4
    · rw [hpc4']
      simp [h]
  · left
    refine ⟨hc4, hl4, hB4, by omega, ?_⟩
    rw [hpc4']
    simp [h]

/-- **A whole block.** -/
theorem full_block (hkf : Spec (label NativeRustcVmArm.Vm.KeccakF.entryLabel) NativeRustcVmArm.KeccakFPre
      NativeRustcVmArm.KeccakFPost) {k : Nat} (hp : Placed code k) (hiv : IvSpec)
    {m0 : MachineData} (g : Geo m0)
    (hrc : NativeRustcVmArm.RcAt m0 NativeRustcVmArm.keccak256WordsStack) {b : Nat}
    {st : MachineState} (h : FullHead m0 k b st) :
    Eventually (step1 Host.exe) (fun st' => FullHead m0 k (b + 1) st' ∨ TailStart m0 k st') st := by
  refine Eventually.bind (full_head hp g h) fun st0 h0 => ?_
  refine Eventually.bind (full0 hp hiv g h0) fun st1 h1 => ?_
  refine Eventually.bind (full1 hp hiv g h1) fun st2 h2 => ?_
  refine Eventually.bind (full2 hp hiv g h2) fun st3 h3 => ?_
  refine Eventually.bind (full3 hp hiv g h3) fun st4 h4 => ?_
  refine Eventually.bind (full4 hp hiv g h4) fun st5 h5 => ?_
  refine Eventually.bind (full5 hp hiv g h5) fun st6 h6 => ?_
  refine Eventually.bind (full6 hp hiv g h6) fun st7 h7 => ?_
  refine Eventually.bind (full7 hp hiv g h7) fun st8 h8 => ?_
  refine Eventually.bind (full8 hp hiv g h8) fun st9 h9 => ?_
  refine Eventually.bind (full9 hp hiv g h9) fun st10 h10 => ?_
  refine Eventually.bind (full10 hp hiv g h10) fun st11 h11 => ?_
  refine Eventually.bind (full11 hp hiv g h11) fun st12 h12 => ?_
  refine Eventually.bind (full12 hp hiv g h12) fun st13 h13 => ?_
  refine Eventually.bind (full13 hp hiv g h13) fun st14 h14 => ?_
  refine Eventually.bind (full14 hp hiv g h14) fun st15 h15 => ?_
  refine Eventually.bind (full15 hp hiv g h15) fun st16 h16 => ?_
  refine Eventually.bind (full16 hp hiv g h16) fun st17 h17 => ?_
  exact full_end hkf hp g hrc h17

/-- **The whole blocks' loop.** -/
theorem full_loop (hkf : Spec (label NativeRustcVmArm.Vm.KeccakF.entryLabel) NativeRustcVmArm.KeccakFPre
      NativeRustcVmArm.KeccakFPost) {k : Nat} (hp : Placed code k) (hiv : IvSpec)
    {m0 : MachineData} (g : Geo m0)
    (hrc : NativeRustcVmArm.RcAt m0 NativeRustcVmArm.keccak256WordsStack) {b : Nat}
    {st : MachineState} (h : FullHead m0 k b st) :
    Eventually (step1 Host.exe) (TailStart m0 k) st :=
  Sym.loop (tr := step1 Host.exe) (Q := TailStart m0 k)
    (fun n st => ∃ b, n = nb m0 - b ∧ FullHead m0 k b st)
    (fun _ st ⟨b, hn, h⟩ => Eventually.mono (full_block hkf hp hiv g hrc h) fun _ h2 => by
        rcases h2 with h2 | h2
        · exact .inr ⟨nb m0 - (b + 1), by have := h.2.2.2.1; omega, b + 1, rfl, h2⟩
        · exact .inl h2)
    ⟨b, rfl, h⟩

end

end NativeRustcVmArm.WordsIv
