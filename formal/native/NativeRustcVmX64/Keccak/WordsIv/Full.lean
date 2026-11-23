module

public import NativeRustcVmX64.Keccak.WordsIv.Entry
public import NativeRustcVmX64.Code.Vm.IvWord.Names
public import NativeRustcVmX64.Code.Vm.KeccakF.Names

/-!
# `keccak256_words::<fiat_shamir_iv's closure>` (x86-64): the whole blocks

In whole block `b < nb` (its first index `17 b` in RBP) every index is below the count, so each
lane goes through its call block and its XOR block (`laneF_step`, `fullStep j`). `full_lanes`:
from the block's first lane to lane 16's word in RAX (`ValAt … 16`, after `b23`). `fullEnd`: lane
16's XOR and the call of `keccak_f` (`fullKf`, `b24`, `call_kf`), then the next block's branch
(`fullNext`, `b25`), to the next block's head or, after the last, the last block's head.
`full_loop`: by induction on the blocks left.
-/

namespace NativeRustcVmX64.WordsIv

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt load_of_wordAt)
open NativeRustcVm.Keccak (wordBlocks)
open NativeRustcVmX64.WordsHash (frame Ctx Lanes pre RegsAt ctx_step lanes_keep lanes_stepB
  lanes_congr regsAt_keep regsAt_saved call_kf pre_succ pre_17 xor64 add64)
open Vm.Keccak256WordsOfFiatShamirIv

public section

/-- The next block's branch: taken after the last whole block. -/
theorem next_cmp {nb b : Nat} (hb : b < nb) (hnb : 17 * nb < 2 ^ 64) :
    (BitVec.ofNat 64 (17 * nb) == BitVec.ofNat 64 17 + BitVec.ofNat 64 (17 * b)) =
      decide (b + 1 = nb) := by
  have h2 : 17 + 17 * b < 2 ^ 64 := by omega
  rw [BitVec.ofNat_add_ofNat, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt hnb, Nat.mod_eq_of_lt h2] at this
    clear he
    omega
  · intro h
    congr 1
    omega

variable [Host]

/-- **Lane `j` of a whole block**, from the lane's registers `R` (`RL` for lane 0, `RD … j`
after), RDX's source `r`. -/
theorem fullStep (hiv : Spec (label NativeRustcVmX64.Vm.IvWord.entryLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} {m0 : MachineData} (g : Geo m0) {b j : Nat}
    (hb : b < nb m0) (hj : j < 16) {R : List (Reg64 × BitVec 64)}
    (hsub : ∀ m, RegsAt m R → RegsAt m (RL m0 .rbp (17 * b) (Rf m0)))
    {r : Reg64} (hrR : ∀ m, RegsAt m R → m.regs.get64 r = BitVec.ofNat 64 (17 * b + j))
    {sL sZ sV sL' sZ' : Nat}
    {blkC : List Directive} {SC : SState} (hkC : blkC.IsInfixAt Host.prog (k + sL))
    (hxC : exec blkC startMain = some (SC, .call NativeRustcVmX64.Vm.IvWord.entryLabel))
    (hmemC : SC.mem = [⟨0, 0, 8, .retAddr⟩]) (hrspC : SC.reg .rsp = some (.ptr 0 0))
    (hrdiC : SC.reg .rdi = some (.reg .r12)) (hrsiC : SC.reg .rsi = some (.reg .r15))
    (hrdxC : SC.reg .rdx = some (.reg r))
    (hkeepC : WordsHash.keepsRegs SC [.r13, .r12, .r15, .rbp, .rbx, .r14] = true)
    (hsV : sL + blkC.length = sV)
    {blkX : List Directive} {SX : SState} {xX : Exit} (hkX : blkX.IsInfixAt Host.prog (k + sV))
    (hxX : exec blkX startMain = some (SX, xX))
    (hmemX : SX.mem =
      [⟨0, 40 + 8 * j, 8, .bin .xor .W64 (.load 0 (40 + 8 * j) 8) (.reg .rax)⟩])
    (hrspX : SX.reg .rsp = some (.ptr 0 8))
    (hrdxX : SX.reg .rdx = some (.bin .add .W64 (.reg .rbp) (.lit (j + 1))))
    (hkeepX : WordsHash.keepsRegs SX [.r13, .r12, .r15, .rbp, .rbx, .r14] = true)
    {posX : Bool} {lblX : Label}
    (hexitX : xX = .cond (if posX then cmpI .rbp (j + 1) else .not (cmpI .rbp (j + 1))) lblX)
    (hlabX : Labels.label lblX = Host.addrOf (k + if posX then sL' else sZ'))
    (hnextX : sV + blkX.length = if posX then sZ' else sL')
    {st : MachineState} (h : LaneAt m0 k R (wordBlocks (wv m0) b) (17 * b) j sL sZ st) :
    Eventually (step1 Host.exe)
      (LaneAt m0 k (RD m0 .rbp (17 * b) (Rf m0) (j + 1)) (wordBlocks (wv m0) b) (17 * b) (j + 1)
        sL' sZ') st :=
  laneF_step hiv g (by omega) (full_lt g hb (by omega))
    (by have := full_lt g hb (j := j + 1) (by omega); have := cnt_small g; omega) hsub hrR
    (names := [.r13, .r12, .r15, .rbp, .rbx, .r14]) rfl (by decide) hkC hxC hmemC hrspC hrdiC hrsiC hrdxC hkeepC hsV hkX hxX hmemX hrspX hrdxX
    hkeepX hexitX hlabX hnextX h

theorem ic {k : Nat} (hp : Placed code k) {b : List Directive} {j : Nat}
    (hb : b.IsInfixAt code j) (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

/-- **A whole block's 16 lanes**, then lane 16's word in RAX. -/
theorem full_lanes (hiv : Spec (label NativeRustcVmX64.Vm.IvWord.entryLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {b : Nat} (hb : b < nb m0) {st : MachineState}
    (h : LaneAt m0 k (RL m0 .rbp (17 * b) (Rf m0)) (wordBlocks (wv m0) b) (17 * b) 0 NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b27Offset NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b46Offset st) :
    Eventually (step1 Host.exe)
      (ValAt m0 k (RL m0 .rbp (17 * b) (Rf m0)) (wordBlocks (wv m0) b) (17 * b) 16 NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b24Offset) st := by
  have s1 : ∀ i m, RegsAt m (RD m0 .rbp (17 * b) (Rf m0) i) →
      RegsAt m (RL m0 .rbp (17 * b) (Rf m0)) := fun _ _ h => h.2
  refine Eventually.bind (fullStep hiv g hb (j := 0) (by decide) (fun _ h => h)
    (fun _ h => h.2.2.2.1) (ic hp b27_in_code (List.cons_ne_nil _ _)) fullC0 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b28_in_code (List.cons_ne_nil _ _)) fullX0 rfl rfl rfl
    (by decide +kernel) (posX := true) rfl (label_at hp b47_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 1) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b47_in_code (List.cons_ne_nil _ _)) fullC1 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b48_in_code (List.cons_ne_nil _ _)) fullX1 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b30_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 2) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b49_in_code (List.cons_ne_nil _ _)) fullC2 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b50_in_code (List.cons_ne_nil _ _)) fullX2 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b31_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 3) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b51_in_code (List.cons_ne_nil _ _)) fullC3 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b52_in_code (List.cons_ne_nil _ _)) fullX3 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b32_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 4) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b53_in_code (List.cons_ne_nil _ _)) fullC4 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b54_in_code (List.cons_ne_nil _ _)) fullX4 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b33_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 5) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b55_in_code (List.cons_ne_nil _ _)) fullC5 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b56_in_code (List.cons_ne_nil _ _)) fullX5 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b34_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 6) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b57_in_code (List.cons_ne_nil _ _)) fullC6 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b58_in_code (List.cons_ne_nil _ _)) fullX6 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b35_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 7) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b59_in_code (List.cons_ne_nil _ _)) fullC7 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b60_in_code (List.cons_ne_nil _ _)) fullX7 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b36_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 8) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b61_in_code (List.cons_ne_nil _ _)) fullC8 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b62_in_code (List.cons_ne_nil _ _)) fullX8 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b37_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 9) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b63_in_code (List.cons_ne_nil _ _)) fullC9 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b64_in_code (List.cons_ne_nil _ _)) fullX9 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b38_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 10) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b65_in_code (List.cons_ne_nil _ _)) fullC10 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b66_in_code (List.cons_ne_nil _ _)) fullX10 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b39_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 11) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b67_in_code (List.cons_ne_nil _ _)) fullC11 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b68_in_code (List.cons_ne_nil _ _)) fullX11 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b40_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 12) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b69_in_code (List.cons_ne_nil _ _)) fullC12 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b70_in_code (List.cons_ne_nil _ _)) fullX12 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b41_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 13) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b71_in_code (List.cons_ne_nil _ _)) fullC13 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b72_in_code (List.cons_ne_nil _ _)) fullX13 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b42_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 14) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b73_in_code (List.cons_ne_nil _ _)) fullC14 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b74_in_code (List.cons_ne_nil _ _)) fullX14 rfl rfl rfl
    (by decide +kernel) (posX := false) rfl (label_at hp b43_in_code rfl) rfl h) fun st h => ?_
  refine Eventually.bind (fullStep hiv g hb (j := 15) (by decide) (s1 _) (fun _ h => h.1)
    (ic hp b75_in_code (List.cons_ne_nil _ _)) fullC15 rfl rfl rfl rfl rfl
    (by decide +kernel) rfl (ic hp b76_in_code (List.cons_ne_nil _ _)) fullX15 rfl rfl rfl
    (by decide +kernel) (posX := true) rfl (label_at hp b23_in_code rfl) rfl h) fun st h => ?_
  -- lane 16's word: `iv_word` (`b23`)
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  have hin : 17 * b + 16 < cnt m0 := full_lt g hb (by decide)
  simp only [hin, ↓reduceIte] at hpc
  subst hpc
  have hRL := hc.regs.2
  exact call_step hiv g hc hl (ic hp b23_in_code (List.cons_ne_nil _ _)) fullC16 rfl rfl rfl rfl
    rfl hRL.2.1 hRL.2.2.1 hc.regs.1 hin hRL (names := [.r13, .r12, .r15, .rbp, .rbx, .r14]) rfl
    (by decide +kernel) (by decide) rfl

/-- **The end of whole block `b`.** -/
theorem fullEnd (hkf : Spec (label NativeRustcVmX64.Vm.KeccakF.entryLabel) NativeRustcVmX64.KeccakFPre
      NativeRustcVmX64.KeccakFPost) {k : Nat} (hp : Placed code k) {m0 : MachineData}
    (g : Geo m0) {b : Nat} (hb : b < nb m0) {st : MachineState}
    (h : ValAt m0 k (RL m0 .rbp (17 * b) (Rf m0)) (wordBlocks (wv m0) b) (17 * b) 16 NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b24Offset st) :
    Eventually (step1 Host.exe)
      (fun st' => FullHead m0 k (b + 1) st' ∨ TailStart m0 k st') st := by
  obtain ⟨hc, hl, hrax, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hrax hpc
  subst hpc
  have hnb := nb_small g
  -- lane 16's XOR, and the call
  let env := Env.ofMachine m [(frame m0, 296)] (fun _ => 0) (Host.addrOf (k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b25Offset)).toBitVec
  have hwf : env.WF := WordsHash.frame_wf g.stk hc.kept
  have hm : Match env startMain m :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨WordsHash.rsp_eval hc.rsp rfl, trivial⟩ trivial trivial trivial
  refine exec_then (ic hp b24_in_code (List.cons_ne_nil _ _)) fullKf hwf (fun _ _ => rfl) hm
    fun st1 hm1 hpc1 => ?_
  have hR1 : RegsAt st1.data (RL m0 .rbp (17 * b) (Rf m0)) :=
    regsAt_keep hm1 hc.regs (names := [.r13, .r12, .r15, .rbp, .rbx, .r14]) rfl (by decide +kernel)
  have hc1 : Ctx m0 (slotsI m0) _ 0 st1.data :=
    ctx_step g.stk (slotsI_low m0) hc hm1 hwf rfl rfl rfl hR1
  have hl1 : Lanes m0 st1.data.dmem (Keccak.lane (Native.Keccak.Proof.xorRate
      (wordBlocks (wv m0) b) fun k => wv m0 (17 * b + k))) := by
    have := lanes_stepB hm1 rfl (j := 16) rfl rfl hl
      (x := Keccak.lane (wordBlocks (wv m0) b) 16 ^^^ wv m0 (17 * b + 16)) (by
        show BinOp.apply .xor .W64 (env.load 0 168 8) (m.regs.get64 .rax) = _
        rw [xor64, hrax, load_of_wordAt (r := 0) (off := 168) (hl 16 (by omega))]
        simp [pre])
    rw [pre_succ] at this
    exact lanes_congr this fun i hi => pre_17 _ _ _ hi
  have hrdi : st1.data.regs.get64 .rdi = frame m0 + BitVec.ofNat 64 40 :=
    (hm1.regs .rdi _ rfl).trans hc.regs.2.2.2.2.1
  refine call_kf hkf g.stk g.rc g.got (slotsI_low m0) hc1 hl1 hrdi hpc1 fun st2 hpc2 hc2 hl2 hsv2 => ?_
  have hR2 := regsAt_saved hR1 hsv2 (names := [.r13, .r12, .r15, .rbp, .rbx, .r14]) rfl
    (by decide +kernel)
  -- the next block's branch
  obtain ⟨m2, pc2⟩ := st2
  simp only at hpc2 hc2 hl2 hR2
  rw [show k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b24Offset + b24.length = k + NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b25Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.b24_next]] at hpc2
  subst hpc2
  obtain ⟨hwf3, hm3⟩ := main_env g.stk hc2 (vars := fun _ => 0) (ret := 0)
  refine exec_then (ic hp b25_in_code (List.cons_ne_nil _ _)) fullNext hwf3
    (fun _ h => by cases h) hm3 fun st4 hm4 hpc4 => .done _ ?_
  have hl4 : Lanes m0 st4.data.dmem (Keccak.lane (wordBlocks (wv m0) (b + 1))) :=
    lanes_keep hm4 rfl (fun w hw => by cases hw) hl2
  have hrbp : st4.data.regs.get64 .rbp = BitVec.ofNat 64 (17 * (b + 1)) := by
    rw [hm4.regs .rbp _ rfl]
    simp only [Sym.eval, add64, Env.ofMachine_regs, hR2.2.2.2.1, BitVec.ofNat_add_ofNat]
    congr 1
    omega
  have hcmp := next_cmp hb (by omega)
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, low_W64, add64, Env.ofMachine_regs,
    hR2.2.2.2.1, hR2.2.2.2.2.2.1, hcmp] at hpc4
  by_cases hend : b + 1 = nb m0
  · right
    simp only [hend, decide_true, ↓reduceIte] at hpc4
    refine ⟨ctx_step g.stk (slotsI_low m0) hc2 hm4 hwf3 rfl rfl rfl
      ⟨(hm4.regs .r13 _ rfl).trans hR2.1, (hm4.regs .r12 _ rfl).trans hR2.2.1,
        (hm4.regs .r15 _ rfl).trans hR2.2.2.1, trivial⟩, ?_, ?_⟩
    · rw [← hend]; exact hl4
    · rw [hpc4]
      exact label_at hp b2_in_code rfl
  · left
    simp only [hend, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc4
    refine ⟨ctx_step g.stk (slotsI_low m0) hc2 hm4 hwf3 rfl rfl rfl
      ⟨(hm4.regs .r13 _ rfl).trans hR2.1, (hm4.regs .r12 _ rfl).trans hR2.2.1,
        (hm4.regs .r15 _ rfl).trans hR2.2.2.1, hrbp,
        (hm4.regs .rbx _ rfl).trans hR2.2.2.2.2.1, (hm4.regs .r14 _ rfl).trans hR2.2.2.2.2.2.1,
        trivial⟩, hl4, by omega, hpc4⟩

/-- **The whole blocks' loop.** -/
theorem full_loop (hkf : Spec (label NativeRustcVmX64.Vm.KeccakF.entryLabel) NativeRustcVmX64.KeccakFPre
      NativeRustcVmX64.KeccakFPost)
    (hiv : Spec (label NativeRustcVmX64.Vm.IvWord.entryLabel) NativeRustcVmX64.IvWordPre
      NativeRustcVmX64.IvWordPost) {k : Nat} (hp : Placed code k) {m0 : MachineData}
    (g : Geo m0) {b : Nat} {st : MachineState} (h : FullHead m0 k b st) :
    Eventually (step1 Host.exe) (TailStart m0 k) st :=
  Sym.loop (tr := step1 Host.exe) (Q := TailStart m0 k)
    (fun n st => ∃ b, n = nb m0 - b ∧ FullHead m0 k b st)
    (fun _ st ⟨b, hn, h⟩ => Eventually.bind (fullHead_step hp g h) fun _ h1 =>
      Eventually.bind (full_lanes hiv hp g h.2.2.1 h1) fun _ h2 =>
      Eventually.mono (fullEnd hkf hp g h.2.2.1 h2) fun _ h3 => by
        rcases h3 with h3 | h3
        · exact .inr ⟨nb m0 - (b + 1), by have := h.2.2.1; omega, b + 1, rfl, h3⟩
        · exact .inl h3)
    ⟨b, rfl, h⟩

end

end NativeRustcVmX64.WordsIv
