module

public import NativeRustcVmX64.Whir.NextLevel.Frame
public import NativeRustcVmX64.Got

/-!
# `next_level`: blocks' bytes, the exits (x86-64)

Bytes of the frame a block does not write (`Ctx.bytes_blk`) or a call does not change
(`Ctx.bytes_call`); the environments of the body's blocks (`Ctx.wf0`, `Ctx.wf1`); the exit at
`NativeRustcVmX64.Vm.NextLevel.label_14` (`exit_spec`: AL R15's low byte, the registers restored, `ret`), at
`NativeRustcVmX64.Vm.NextLevel.label_13` (`fail_spec`: AL `0`), and the postcondition on a rejection (`post_none`).
-/

namespace NativeRustcVmX64.Whir.Levels.NL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.NextLevel

public section

/-- **Bytes of the frame a call does not change.** -/
theorem bytes_call {m0 d d' : MachineData} {o lo n : Nat}
    (hk : ∀ j, o + 8 ≤ j → j < 8192 → (j < lo ∨ lo + n ≤ j) →
      d'.dmem.get? (loc m0 j) = d.dmem.get? (loc m0 j))
    {j : Nat} {bs : List UInt8} (hj : o + 8 ≤ j) (hjn : j + bs.length ≤ 8192)
    (hmiss : j + bs.length ≤ lo ∨ lo + n ≤ j) (h : NativeRustcVm.BytesAt d.dmem (loc m0 j) bs) :
    NativeRustcVm.BytesAt d'.dmem (loc m0 j) bs := by
  intro i hi
  have := h i hi
  rw [off_add] at this ⊢
  rw [hk (j + i) (by omega) (by omega) (by omega)]
  exact this


theorem al_trunc (x : BitVec 64) : (UnOp.apply .trunc .W32 x).toNat % 256 = x.toNat % 256 := by
  simp only [UnOp.apply, ext, low, BitVec.toNat_setWidth]
  show x.toNat % 2 ^ 32 % 2 ^ 64 % 256 = _
  omega

theorem cAl_eval [Labels] (env : Env) :
    cAl.eval env = decide ((env.regs .rax).toNat % 256 = 0) := by
  simp only [cAl, SBool.eval, Sym.eval]
  exact testAl_eq _

theorem okWord_toNat (b : Bool) : (okWord b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

private theorem got_frame_gap {sp slot : Nat} (hn : 11312 ≤ sp)
    (hs : slot + 8 ≤ sp - 11312 ∨ sp - 11312 + (11312 + 8) ≤ slot)
    (ha : slot + 8 ≤ sp + 8 ∨ sp + 16 ≤ slot) :
    slot + 8 ≤ sp - 8176 ∨ sp + 16 ≤ slot := by
  rcases hs with hs | hs
  · exact Or.inl (hs.trans (Nat.sub_le_sub_left (by decide : 8176 ≤ 11312) sp))
  · rw [← Nat.add_assoc, Nat.sub_add_cancel hn] at hs
    rcases ha with ha | ha
    · exact False.elim ((Nat.not_le_of_gt
        (Nat.lt_add_of_pos_right (by decide : 0 < 8))) (ha.trans hs))
    · exact Or.inr ha

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s level w rounds m0)
include c

/-- The environment of a body block: the frame's region, then `rest`. -/
theorem wf0 {d : MachineData} (hk : Kept m0.dmem d.dmem) {ret : BitVec 64} :
    (argEnv m0 d 8176 8 [] (fun _ ↦ 0) ret).WF :=
  argEnv_wf (c.region_ok hk) (by simp) (List.pairwise_singleton _ _)

/-- The environment of a body block with one more region `x` (`n` bytes), apart. -/
theorem wf1 {d : MachineData} (hk : Kept m0.dmem d.dmem) {x : BitVec 64} {n : Nat}
    (hx : NativeRustcVm.Mapped d.dmem x n) (hnw : x.toNat + n ≤ 2 ^ 64)
    (hap : x.toNat + n ≤ (rspOf m0).toNat - 8176 ∨ (rspOf m0).toNat + 16 ≤ x.toNat)
    {ret : BitVec 64} : (argEnv m0 d 8176 8 [(x, n)] (fun _ ↦ 0) ret).WF := by
  have hf := c.fa_toNat
  have := c.geo.hN
  refine argEnv_wf (c.region_ok hk) (fun y hy ↦ ?_) (List.pairwise_pair.mpr ?_)
  · rw [List.mem_singleton] at hy; subst hy; exact ⟨hx, hnw⟩
  · show (fa m0).toNat + (8176 + 8 + 8) ≤ x.toNat ∨ x.toNat + n ≤ (fa m0).toNat
    rw [hf]; omega

/-- Only the state and transcript, besides the stack, may change loader-slot neighbours. -/
theorem got_bytes {d : MachineData} {o : Nat} (hf : Fr m0 o d) :
    ∀ l ∈ ["memcpy", "memset"], ∀ i < 8,
      d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  have hg := c.got.areas (areas' := [(tA m0, tstateBytes), (pA m0, whirBytes)])
    (by intro ar har; simp only [List.mem_cons, List.not_mem_nil, or_false] at har; rcases har with rfl | rfl <;> simp)
  apply NativeRustcVmX64.GotAt.unchanged_vm hg c.stack
  · intro ar har
    simp only [List.mem_cons, List.not_mem_nil, or_false] at har
    rcases har with rfl | rfl
    · exact c.ts.footprint.1.2
    · exact c.pout.1.2.1
  · intro q hq
    apply hf.same q
    rintro (hs | hp | ht)
    · exact hq (.inl hs)
    · exact hq (.inr ⟨(pA m0, whirBytes), by simp, hp⟩)
    · exact hq (.inr ⟨(tA m0, tstateBytes), by simp, ht⟩)

/-- The `memcpy` slot is a separate read-only region, including from the argument word. -/
theorem got_wf {d : MachineData} {o : Nat} (hf : Fr m0 o d) {ret : BitVec 64} :
    (argEnv m0 d 8176 8 [(gotAddr "memcpy", 8)] (fun _ => 0) ret).WF := by
  have hg := c.got.1 "memcpy" (by simp)
  have hs : Apart (gotAddr "memcpy") 8 (stackBelow m0 nextLevelStack)
      (nextLevelStack + 8) := hg.2.2.1
  have ha : Apart (gotAddr "memcpy") 8 (rspOf m0 + 8#64) 8 :=
    hg.2.2.2 (rspOf m0 + 8#64, 8) (by simp)
  have g := c.geo
  have hsb := stackBelow_toNat c.stack.1
  have harg : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 :=
    toNat_add_ofNat _ _ (by have := g.hA; omega)
  apply c.wf1 hf.frame.kept
    (fun i hi => hf.frame.kept _ (c.got.mapped (by simp) i hi)) hg.2.1
  unfold Apart at hs ha
  rw [hsb, stack_eq] at hs
  rw [harg] at ha
  exact got_frame_gap g.hN hs ha

/-- Seed the copy's register target from the actual loader bytes. -/
theorem m_copy {d : MachineData} (hf : Fr m0 72 d) {ret : BitVec 64} :
    Match (argEnv m0 d 8176 8 [(gotAddr "memcpy", 8)] (fun _ => 0) ret) copyS d := by
  have hm : Match (argEnv m0 d 8176 8 [(gotAddr "memcpy", 8)] (fun _ => 0) ret)
      (init [8192, 8] [(.rsp, .ptr 0 72)] [] [] [(.gotSlot "memcpy", 1, 0)]) d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨Frame.rsp_evalA hf.frame, trivial⟩ trivial trivial
      ⟨(BitVec.add_zero _).symm, trivial⟩
  apply hm.withKnownBytes
  intro i hi
  simpa [Env.base, Sym.eval] using
    (c.got_bytes hf "memcpy" (by simp) i hi).trans (c.got.byte (by simp) hi)

/-- Every callee sees only a contained portion of the caller's stack and protected areas. -/
theorem got_call {d : MachineData} {o N : Nat} (hf : Fr m0 o d) (ho : o ≤ 8176)
    (hle : 8176 - o + N ≤ nextLevelStack) {areas : List (BitVec 64 × Nat)}
    {symbols : List Label} (hlabels : symbols.Sublist ["memcpy", "memset"])
    (hcover : ∀ ar ∈ areas, ∃ b ∈ (stackBelow m0 nextLevelStack, nextLevelStack + 8) ::
      ([(tA m0, tstateBytes), (a.words, 8 * a.len), (pA m0, whirBytes),
        (lA m0, levelBytes), (rspOf m0 + 8#64, 8)] ++ rodataAreas),
      b.1.toNat ≤ ar.1.toNat ∧ ar.1.toNat + ar.2 ≤ b.1.toNat + b.2) :
    GotAt d N areas symbols := by
  have g := c.geo
  have hsp : (rspOf d).toNat = (rspOf m0).toNat - 8176 + o := by
    rw [hf.frame.sp]
    exact c.loc_toNat (by omega)
  have hd : (stackBelow d N).toNat = (rspOf m0).toNat - 8176 + o - N := by
    rw [stackBelow_toNat (by rw [hsp]; rw [stack_eq] at hle; have := g.hN; omega), hsp]
  apply NativeRustcVmX64.GotAt.callee (c.got.symbols hlabels)
    (fun l hl i hi => c.got_bytes hf l (hlabels.subset hl) i hi) _ _ hcover <;>
    rw [hd, c.stk_toNat] <;> have := g.hN <;> simp only [stack_eq] at * <;> omega

/-- A local input/output buffer is protected by the caller's existing stack separation. -/
theorem got_loc {areas : List (BitVec 64 × Nat)} {j n : Nat} (hj : j < 8192)
    (hn : j + n ≤ 8184) :
    ∃ b ∈ (stackBelow m0 nextLevelStack, nextLevelStack + 8) :: areas,
      b.1.toNat ≤ (loc m0 j).toNat ∧ (loc m0 j).toNat + n ≤ b.1.toNat + b.2 := by
  refine ⟨(stackBelow m0 nextLevelStack, nextLevelStack + 8), by simp, ?_, ?_⟩
  · change (stackBelow m0 nextLevelStack).toNat ≤ (loc m0 j).toNat
    rw [c.stk_toNat, c.loc_toNat hj]
    have := c.geo.hN
    omega
  · change (loc m0 j).toNat + n ≤ (stackBelow m0 nextLevelStack).toNat + (nextLevelStack + 8)
    rw [c.stk_toNat, c.loc_toNat hj, stack_eq]
    have := c.geo.hN
    omega

omit c in
/-- The round constants are already among the caller's read-only inputs. -/
theorem got_rc (_c : Ctx a s level w rounds m0) :
    ∃ b ∈ (stackBelow m0 nextLevelStack, nextLevelStack + 8) ::
      ([(tA m0, tstateBytes), (a.words, 8 * a.len), (pA m0, whirBytes),
        (lA m0, levelBytes), (rspOf m0 + 8#64, 8)] ++ rodataAreas),
      b.1.toNat ≤ rcAddr.toNat ∧ rcAddr.toNat + 192 ≤ b.1.toNat + b.2 := by
  have hrc : (rcAddr, 192) ∈ rodataAreas := by
    change (rodataAddr .keccakRC, NativeRustcVm.Data.Item.bytes .keccakRC |>.length) ∈ rodataAreas
    exact List.mem_map.mpr ⟨.keccakRC, by decide, rfl⟩
  exact ⟨(rcAddr, 192), by simp [hrc], le_rfl, le_rfl⟩

omit c in
/-- **Bytes of the frame a block does not write.** -/
theorem bytes_blk {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {S : SState}
    {ret : BitVec 64} (hwf : (argEnv m0 d 8176 8 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (argEnv m0 d 8176 8 rest (fun _ ↦ 0) ret) S d')
    (hin : writesIn S = true) {rs : List (Nat × Nat)} (hW : Wr rs S) {j : Nat} {bs : List UInt8}
    (hj : j + bs.length ≤ 8192) (hmiss : ∀ p ∈ rs, p.2 ≤ j ∨ j + bs.length ≤ p.1)
    (h : NativeRustcVm.BytesAt d.dmem (loc m0 j) bs) :
    NativeRustcVm.BytesAt d'.dmem (loc m0 j) bs := by
  intro i hi
  have := h i hi
  rw [off_add] at this ⊢
  rw [hm.get?_mem0 hwf (not_written0A hwf hm hin (by omega) fun w hw _ ↦ ?_)]
  · exact this
  · obtain ⟨-, p, hp, h1, h2⟩ := hW w hw
    rcases hmiss p hp with h' | h'
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

end Ctx

end

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The exit** at `NativeRustcVmX64.Vm.NextLevel.label_14`: AL R15's low byte, the registers restored, `ret`. -/
theorem exit_spec (hp : Placed code k) (c : Ctx a s level w rounds m0) {st : MachineState}
    (hf : Fr m0 72 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b27Offset)) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
        boolRet st'.data = (reg st.data .r15).toNat % 256 ∧ st'.data.dmem = st.data.dmem ∧
        Saved m0 st'.data) st := by
  have hwf := c.wf0 hf.frame.kept (ret := 0)
  have hm : Match (argEnv m0 st.data 8176 8 []) retS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hf.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b27_in_code (by simp [b27]) hp) exit_b27 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hepi, hmem, hrax⟩ := ok_b27
  obtain ⟨hsv, hrsp⟩ := Frame.epilogueA hf.frame hwf hm' hepi
  simp only [PcOk, Sym.eval] at hpc'
  refine .done _ ⟨hpc'.trans (Frame.load_retA hf.frame c.stack (by rw [stack_eq]; omega)), hrsp,
    ?_, hm'.dmem_eq hwf hmem, hsv⟩
  rw [boolRet, show reg st'.data .rax = _ from hm'.regs .rax _ hrax]
  exact al_trunc _

/-- **A failure** at `NativeRustcVmX64.Vm.NextLevel.label_13`: R15 cleared, then the exit; AL `0`. -/
theorem fail_spec (hp : Placed code k) (c : Ctx a s level w rounds m0) {st : MachineState}
    (hf : Fr m0 72 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b26Offset)) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
        boolRet st'.data = 0 ∧ st'.data.dmem = st.data.dmem ∧ Saved m0 st'.data) st := by
  have hwf := c.wf0 hf.frame.kept (ret := 0)
  have hm : Match (argEnv m0 st.data 8176 8 []) retS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hf.frame, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b26_in_code (by simp [b26]) hp) exit_b26 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hmem, hr15⟩ := ok_b26
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem
  have hf1 : Fr m0 72 st1.data :=
    ⟨Frame.of_blockA hf.frame hwf hm1 hmid slots_le, by rw [Sm, hd]; exact hf.same⟩
  have h0 : reg st1.data .r15 = 0 := hm1.regs .r15 _ hr15
  simp only [PcOk] at hpc1
  exact Eventually.mono (exit_spec hp c hf1 hpc1) fun st' ⟨h1, h2, h3, h4, h5⟩ ↦
    ⟨h1, h2, by rw [h3, h0]; rfl, h4.trans hd, h5⟩

omit [Host] in
/-- The frame's changes are the contract's. -/
theorem changes_of {d : MachineData} (hs : Sm m0 d) :
    ChangesIn m0 d nextLevelStack [⟨pA m0, whirBytes⟩, ⟨tA m0, tstateBytes⟩] :=
  NativeRustcVm.SameOutside.mono hs fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact Or.inr hq
    · exact Or.inl ⟨_, List.mem_cons_self, hq⟩
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩

/-- **A rejection**, from a state of the frame at `NativeRustcVmX64.Vm.NextLevel.label_13`. -/
theorem none13 (hp : Placed code k) (c : Ctx a s level w rounds m0) {st : MachineState}
    (hf : Fr m0 72 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b26Offset))
    (hnone : runN level w rounds m0 s = none) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st := by
  simp only [runN] at hnone
  refine Eventually.mono (fail_spec hp c hf hpc) fun st' ⟨h1, h2, h3, h4, h5⟩ ↦
    ⟨h1, h2, ?_, ?_, ?_, ?_, h5⟩
  · show boolRet st'.data = _
    rw [h3, hnone]; rfl
  · intro x s' h; rw [hnone] at h; cases h
  · intro x s' h; rw [hnone] at h; cases h
  · unfold ChangesIn; rw [h4]; exact changes_of hf.same

/-- **A rejection**, from a state of the frame at `NativeRustcVmX64.Vm.NextLevel.label_14` with R15 `0`. -/
theorem none14 (hp : Placed code k) (c : Ctx a s level w rounds m0) {st : MachineState}
    (hf : Fr m0 72 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.NextLevel.b27Offset)) (h15 : reg st.data .r15 = 0)
    (hnone : runN level w rounds m0 s = none) :
    Eventually (step1 Host.exe) (Goal a s level w rounds m0) st := by
  simp only [runN] at hnone
  refine Eventually.mono (exit_spec hp c hf hpc) fun st' ⟨h1, h2, h3, h4, h5⟩ ↦
    ⟨h1, h2, ?_, ?_, ?_, ?_, h5⟩
  · show boolRet st'.data = _
    rw [h3, h15, hnone]; rfl
  · intro x s' h; rw [hnone] at h; cases h
  · intro x s' h; rw [hnone] at h; cases h
  · unfold ChangesIn; rw [h4]; exact changes_of hf.same

end

end NativeRustcVmX64.Whir.Levels.NL
