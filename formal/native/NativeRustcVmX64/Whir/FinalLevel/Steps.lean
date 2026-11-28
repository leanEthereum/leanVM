module

public import NativeRustcVmX64.Whir.FinalLevel.Frame
public import NativeRustcVmX64.Code.Vm.FinalLevel.Names
public import NativeRustcVmX64.Got

/-!
# `final_level`: tests, exits, the first zeroing loop (x86-64)

`test_spec`: a two-instruction block `testb %al, %al; je l` from a state of the body leaves
registers and memory as they were and goes to `l` when AL is `0`; `cond_spec` any block without
writes or register changes ending in a branch. The exit at `NativeRustcVmX64.Vm.FinalLevel.label_6` (`exit_spec`: AL the
low byte of RAX, the registers restored, `ret`), at `NativeRustcVmX64.Vm.FinalLevel.label_5` (`fail_spec`: AL `0`), the
postcondition from them (`post37`, `none36`). `zero_loop`: `b1` zeroes the folded scalars' buffer
(`1600` to `2624`), the registers but RAX kept.
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.FinalLevel

public section

theorem retS_some (r : Reg64) : (retS.reg r).isSome = true := by cases r <;> decide

/-- A block whose registers are its start's leaves the machine's registers. -/
theorem regs_same [Labels] {env : Env} {S : SState} {d d' : MachineData} (hm0 : Match env retS d)
    (hm : Match env S d') (hS : S.regs = retS.regs) : ∀ r, reg d' r = reg d r := fun r ↦ by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (retS_some r)
  exact Match.reg_eq hm0 hm hv (by unfold SState.reg at hv ⊢; rw [hS]; exact hv)

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

/-- A block's label is its address. -/
theorem label_of_infix [Host] {F bl : List Directive} {k j : Nat} {l : Label} (hp : Placed F k)
    (hb : bl.IsInfixAt F j) (h0 : bl[0]? = some (.label l)) :
    Labels.label l = Host.addrOf (k + j) := by
  apply hp.label
  cases bl with
  | nil => simp at h0
  | cons x xs =>
    have h := (List.IsInfixAt.cons hb).1
    rw [h]
    exact h0

/-- The machine state of the body (RSP at `40`) is `retS`'s. -/
theorem match_retS [Labels] {m0 d : MachineData} (hf : Fr m0 40 d) {ret : BitVec 64} :
    Match (argEnv m0 d 2672 8 [] (fun _ ↦ 0) ret) retS d :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨Frame.rsp_evalA hf.frame, trivial⟩ trivial trivial trivial

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s level ba b w rounds m0)
include c

/-- Stack and query/transcript writes preserve the loader's slots. -/
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
    · exact hq (.inr ⟨(pA m0, whirBytes), by simp,
        NativeRustcVm.InRange.of_sub hp c.pout.1.2.1
          (show 61352 + queryBufBytes ≤ whirBytes by decide)⟩)
    · exact hq (.inr ⟨(tA m0, tstateBytes), by simp, ht⟩)

/-- Transport the loader slots to a callee's contained stack and protected areas. -/
theorem got_call {d : MachineData} {o N : Nat} (hf : Fr m0 o d) (ho : o ≤ 2672)
    (hle : 2672 - o + N ≤ finalLevelStack) {areas : List (BitVec 64 × Nat)}
    {symbols : List Label} (hlabels : symbols.Sublist ["memcpy", "memset"])
    (hcover : ∀ ar ∈ areas, ∃ b ∈ (stackBelow m0 finalLevelStack, finalLevelStack + 8) ::
      ([(tA m0, tstateBytes), (a.words, 8 * a.len), (pA m0, whirBytes),
        (lA m0, levelBytes), (rspOf m0 + 8#64, 8)] ++ rodataAreas),
      b.1.toNat ≤ ar.1.toNat ∧ ar.1.toNat + ar.2 ≤ b.1.toNat + b.2) :
    GotAt d N areas symbols := by
  have g := c.geo
  have hsp : (rspOf d).toNat = (rspOf m0).toNat - 2672 + o := by
    rw [hf.frame.sp]
    exact c.loc_toNat (by omega)
  have hd : (stackBelow d N).toNat = (rspOf m0).toNat - 2672 + o - N := by
    rw [stackBelow_toNat (by rw [hsp]; rw [stack_eq] at hle; have := g.hN; omega), hsp]
  apply NativeRustcVmX64.GotAt.callee (c.got.symbols hlabels)
    (fun l hl i hi => c.got_bytes hf l (hlabels.subset hl) i hi) _ _ hcover <;>
    rw [hd, c.stk_toNat] <;> have := g.hN <;> rw [stack_eq] at * <;> omega

/-- Local buffers are protected by the caller's stack separation. -/
theorem got_loc {areas : List (BitVec 64 × Nat)} {j n : Nat} (hj : j < 2688)
    (hn : j + n ≤ 2680) :
    ∃ b ∈ (stackBelow m0 finalLevelStack, finalLevelStack + 8) :: areas,
      b.1.toNat ≤ (loc m0 j).toNat ∧ (loc m0 j).toNat + n ≤ b.1.toNat + b.2 := by
  have hN := c.geo.hN
  refine ⟨(stackBelow m0 finalLevelStack, finalLevelStack + 8), by simp, ?_, ?_⟩
  · change (stackBelow m0 finalLevelStack).toNat ≤ (loc m0 j).toNat
    rw [c.stk_toNat, c.loc_toNat hj]
    omega
  · change (loc m0 j).toNat + n ≤
      (stackBelow m0 finalLevelStack).toNat + (finalLevelStack + 8)
    rw [c.stk_toNat, c.loc_toNat hj, stack_eq]
    omega

omit c in
/-- Round constants are among the caller's read-only inputs. -/
theorem got_rc (_c : Ctx a s level ba b w rounds m0) :
    ∃ b ∈ (stackBelow m0 finalLevelStack, finalLevelStack + 8) ::
      ([(tA m0, tstateBytes), (a.words, 8 * a.len), (pA m0, whirBytes),
        (lA m0, levelBytes), (rspOf m0 + 8#64, 8)] ++ rodataAreas),
      b.1.toNat ≤ rcAddr.toNat ∧ rcAddr.toNat + 192 ≤ b.1.toNat + b.2 := by
  have hrc : (rcAddr, 192) ∈ rodataAreas := by
    change (rodataAddr .keccakRC, NativeRustcVm.Data.Item.bytes .keccakRC |>.length) ∈ rodataAreas
    exact List.mem_map.mpr ⟨.keccakRC, by decide, rfl⟩
  exact ⟨(rcAddr, 192), by simp [hrc], le_rfl, le_rfl⟩

end Ctx

/-- The frame's changes are the contract's. -/
theorem changes_of (c : Ctx a s level ba b w rounds m0) {d : MachineData} (hs : Sm m0 d) :
    ChangesIn m0 d finalLevelStack [⟨pA m0, whirBytes⟩, ⟨tA m0, tstateBytes⟩] :=
  NativeRustcVm.SameOutside.mono hs fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact Or.inr hq
    · exact Or.inl ⟨_, List.mem_cons_self,
        NativeRustcVm.InRange.of_sub hq c.pout.1.2.1
          (show 61352 + queryBufBytes ≤ whirBytes by decide)⟩
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hq⟩

end

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **A `bool` tested**: AL `0` goes to `l`, else to the next block; nothing else changes. -/
theorem test_spec (hp : Placed code k) (c : Ctx a s level ba b w rounds m0) {bl : List Directive}
    {j : Nat} (hb : bl.IsInfixAt code j) (hlen : bl.length = 2) {l : Label}
    (hx : exec bl retS = some (after bl retS, .cond cAl l))
    (hok : (after bl retS).mem = [] ∧ (after bl retS).regs = retS.regs) {st : MachineState}
    (hf : Fr m0 40 st.data) (hpc : st.pc = Host.addrOf (k + j)) {x : Bool}
    (hal : (reg st.data .rax).toNat % 256 = (okWord x).toNat) :
    Eventually (step1 Host.exe) (fun st' ↦ (∀ r, reg st'.data r = reg st.data r) ∧
      st'.data.dmem = st.data.dmem ∧
      st'.pc = if x then Host.addrOf (k + j + 2) else Labels.label l) st := by
  have hwf := c.wf0 hf.frame.kept (ret := 0)
  have hm := match_retS hf (ret := 0)
  refine exec_at (infix_of hb (by intro h; rw [h] at hlen; cases hlen) hp) hx hwf nofun hpc hm
    fun st' hm' hpc' ↦ .done _ ⟨regs_same hm hm' hok.2, hm'.dmem_eq hwf hok.1, ?_⟩
  simp only [PcOk, cAl_eval] at hpc'
  have h' : ((argEnv m0 st.data 2672 8 []).regs .rax).toNat % 256 = (okWord x).toNat := hal
  rw [hpc', hlen, h']
  cases x <;> rfl

/-- **A block without writes or register changes** ending in a conditional branch. -/
theorem cond_spec (hp : Placed code k) (c : Ctx a s level ba b w rounds m0) {bl : List Directive}
    {j : Nat} (hb : bl.IsInfixAt code j) (hne : bl ≠ []) {l : Label} {cnd : SBool}
    (hx : exec bl retS = some (after bl retS, .cond cnd l))
    (hok : (after bl retS).mem = [] ∧ (after bl retS).regs = retS.regs) {st : MachineState}
    (hf : Fr m0 40 st.data) (hpc : st.pc = Host.addrOf (k + j)) :
    Eventually (step1 Host.exe) (fun st' ↦ (∀ r, reg st'.data r = reg st.data r) ∧
      st'.data.dmem = st.data.dmem ∧
      st'.pc = if cnd.eval (argEnv m0 st.data 2672 8 [] (fun _ ↦ 0) 0) then Labels.label l
        else Host.addrOf (k + j + bl.length)) st := by
  have hwf := c.wf0 hf.frame.kept (ret := 0)
  have hm := match_retS hf (ret := 0)
  exact exec_at (infix_of hb hne hp) hx hwf nofun hpc hm
    fun st' hm' hpc' ↦ .done _ ⟨regs_same hm hm' hok.2, hm'.dmem_eq hwf hok.1, hpc'⟩

/-- **The exit** at `NativeRustcVmX64.Vm.FinalLevel.label_6`: AL RAX's low byte, the registers restored, `ret`. -/
theorem exit_spec (hp : Placed code k) (c : Ctx a s level ba b w rounds m0) {st : MachineState}
    (hf : Fr m0 40 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b37Offset)) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
        boolRet st'.data = (reg st.data .rax).toNat % 256 ∧ st'.data.dmem = st.data.dmem ∧
        Saved m0 st'.data) st := by
  have hwf := c.wf0 hf.frame.kept (ret := 0)
  have hm := match_retS hf (ret := 0)
  refine exec_at (infix_of b37_in_code (by simp [b37]) hp) exit_b37 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hepi, hmem, hrax⟩ := ok_b37
  obtain ⟨hsv, hrsp⟩ := Frame.epilogueA hf.frame hwf hm' hepi
  simp only [PcOk, Sym.eval] at hpc'
  refine .done _ ⟨hpc'.trans (Frame.load_retA hf.frame c.stack (by rw [stack_eq]; omega)), hrsp,
    ?_, hm'.dmem_eq hwf hmem, hsv⟩
  rw [boolRet, show reg st'.data .rax = _ from hm'.regs .rax _ hrax]
  rfl

/-- **A failure** at `NativeRustcVmX64.Vm.FinalLevel.label_5`: RAX cleared, then the exit; AL `0`. -/
theorem fail_spec (hp : Placed code k) (c : Ctx a s level ba b w rounds m0) {st : MachineState}
    (hf : Fr m0 40 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b36Offset)) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
        boolRet st'.data = 0 ∧ st'.data.dmem = st.data.dmem ∧ Saved m0 st'.data) st := by
  have hwf := c.wf0 hf.frame.kept (ret := 0)
  have hm := match_retS hf (ret := 0)
  refine exec_at (infix_of b36_in_code (by simp [b36]) hp) exit_b36 hwf nofun hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hmem, hrax, -⟩ := ok_b36
  have hd : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem
  have hf1 : Fr m0 40 st1.data :=
    ⟨Frame.of_blockA hf.frame hwf hm1 hmid slots_le, by rw [Sm, hd]; exact hf.same⟩
  have h0 : reg st1.data .rax = 0 := hm1.regs .rax _ hrax
  simp only [PcOk] at hpc1
  exact Eventually.mono (exit_spec hp c hf1 hpc1) fun st' ⟨h1, h2, h3, h4, h5⟩ ↦
    ⟨h1, h2, (by rw [h3, h0]; rfl), h4.trans hd, h5⟩

/-- **The postcondition** from the exit at `NativeRustcVmX64.Vm.FinalLevel.label_6`, AL the verdict. -/
theorem post37 (hp : Placed code k) (c : Ctx a s level ba b w rounds m0) {st : MachineState}
    (hf : Fr m0 40 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b37Offset))
    (hal : (reg st.data .rax).toNat % 256 =
      (okWord (runF level b w rounds m0 s).isSome).toNat)
    (hnext : NextAt st.data.dmem (tA m0) a (runF level b w rounds m0 s)) :
    Eventually (step1 Host.exe) (Goal a s level b w rounds m0) st :=
  Eventually.mono (exit_spec hp c hf hpc) fun st' ⟨h1, h2, h3, h4, h5⟩ ↦
    ⟨h1, h2, (by show boolRet st'.data = _; rw [h3, hal]), (by rw [h4]; exact hnext),
      (by unfold ChangesIn; rw [h4]; exact changes_of c hf.same), h5⟩

/-- **A rejection** with RAX's low byte `0` at `NativeRustcVmX64.Vm.FinalLevel.label_6`. -/
theorem none37 (hp : Placed code k) (c : Ctx a s level ba b w rounds m0) {st : MachineState}
    (hf : Fr m0 40 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b37Offset))
    (h0 : (reg st.data .rax).toNat % 256 = 0) (hnone : runF level b w rounds m0 s = none) :
    Eventually (step1 Host.exe) (Goal a s level b w rounds m0) st :=
  post37 hp c hf hpc (by rw [h0, hnone]; rfl) (by rw [hnone]; intro _ _ h; cases h)

/-- **A rejection** at `NativeRustcVmX64.Vm.FinalLevel.label_5`. -/
theorem none36 (hp : Placed code k) (c : Ctx a s level ba b w rounds m0) {st : MachineState}
    (hf : Fr m0 40 st.data) (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b36Offset))
    (hnone : runF level b w rounds m0 s = none) :
    Eventually (step1 Host.exe) (Goal a s level b w rounds m0) st :=
  Eventually.mono (fail_spec hp c hf hpc) fun st' ⟨h1, h2, h3, h4, h5⟩ ↦ by
    simp only [runF] at hnone
    exact ⟨h1, h2, (by show boolRet st'.data = _; rw [h3, hnone]; rfl),
      (by rw [hnone]; intro _ _ h; cases h),
      (by unfold ChangesIn; rw [h4]; exact changes_of c hf.same), h5⟩

/-- `NativeRustcVmX64.Vm.FinalLevel.label_5`'s address. -/
theorem l5 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.FinalLevel.label_5 = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b36Offset) :=
  label_of_infix hp b36_in_code rfl

/-- `NativeRustcVmX64.Vm.FinalLevel.label_6`'s address. -/
theorem l6 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.FinalLevel.label_6 = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b37Offset) :=
  label_of_infix hp b37_in_code rfl

/-! ## The first zeroing loop -/

omit [Host] in
theorem cZero_eval [Labels] (env : Env) {i : Nat} (hi : i < 16)
    (hx : env.regs .rax = BitVec.ofNat 64 (56 + 64 * i)) :
    cZero.eval env = decide (i + 1 < 16) := by
  simp only [cZero, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, hx]
  have e : (BitVec.ofNat 64 64 + BitVec.ofNat 64 (56 + 64 * i)) = BitVec.ofNat 64 (120 + 64 * i) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e]
  by_cases h : i + 1 < 16
  · have : (BitVec.ofNat 64 (120 + 64 * i) == BitVec.ofNat 64 1080) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at this
      omega
    rw [this, decide_eq_true h]
    rfl
  · have : i = 15 := by omega
    subst this
    rw [decide_eq_false h]
    decide

/-- **One step of the first zeroing loop**: `b1` from iteration `i`. -/
theorem zero_step (hp : Placed code k) (c : Ctx a s level ba b w rounds m0) {d0 : MachineData}
    {i : Nat} (hi : i < 16) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b1Offset))
    (hf : Fr m0 40 st.data) (hrax : reg st.data .rax = BitVec.ofNat 64 (56 + 64 * i))
    (hr : ∀ r, r ≠ .rax → reg st.data r = reg d0 r)
    (hd : NativeRustcVm.SameOutside m0.dmem st.data.dmem (NativeRustcVm.InRange (fa m0) 2672)) :
    Eventually (step1 Host.exe) (fun st' ↦ Fr m0 40 st'.data ∧
      (∀ r, r ≠ .rax → reg st'.data r = reg d0 r) ∧
      NativeRustcVm.SameOutside m0.dmem st'.data.dmem (NativeRustcVm.InRange (fa m0) 2672) ∧
      ((i + 1 < 16 ∧ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b1Offset) ∧
          reg st'.data .rax = BitVec.ofNat 64 (56 + 64 * (i + 1))) ∨
        (i + 1 = 16 ∧ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b2Offset)))) st := by
  have g := c.geo
  set x := loc m0 (96 + 64 * i) with hxdef
  have hxn : x.toNat = (rspOf m0).toNat - 2672 + (96 + 64 * i) := c.loc_toNat (by omega)
  have hreg := c.region_ok hf.frame.kept
  let env := Env.ofMachine st.data [(x, 1568)]
  have hwf : env.WF := Env.wf_of
    ⟨⟨fun j hj ↦ by
        have := hreg.1 (96 + 64 * i + j) (by omega)
        rwa [show fa m0 + BitVec.ofNat 64 (96 + 64 * i + j) = x + BitVec.ofNat 64 j by
          rw [hxdef, loc, off_add]] at this,
      by show x.toNat + 1568 ≤ 2 ^ 64; rw [hxn]; have := g.hA; omega⟩, trivial⟩
    (List.pairwise_singleton _ _)
  have hm : Match env zeroS st.data := by
    refine match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨?_, trivial⟩
    show BinOp.apply .add .W64 (rspOf st.data) (reg st.data .rax) = x + BitVec.ofInt 64 0
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [hf.frame.sp, hrax, ofInt_zero64, BitVec.add_zero, hxdef]
    show off (stackBelow m0 2672) 40 + BitVec.ofNat 64 (56 + 64 * i) =
      off (stackBelow m0 2672) (96 + 64 * i)
    rw [off_add]
    congr 1
    omega
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf nofun hpc hm
    fun st' hm' hpc' ↦ ?_
  obtain ⟨hw, hrax', hkr⟩ := ok_b1
  have hso : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (NativeRustcVm.InRange x 1568) :=
    sameOutside_region hwf hm' (r := 0) rfl hw
  have hkeep : ∀ r, r ≠ .rax → reg st'.data r = reg st.data r := fun r hr' ↦
    hm'.regs r _ (hkr r (List.mem_filter.mpr ⟨mem_allRegs r, by
      cases r <;> first | exact absurd rfl hr' | rfl⟩))
  have hxj : ∀ j, j < 2688 → (j < 96 + 64 * i ∨ 96 + 64 * i + 1568 ≤ j) →
      ¬ NativeRustcVm.InRange x 1568 (loc m0 j) := by
    intro j hj hjr hq
    rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [hxn]; have := g.hA; omega), hxn,
      c.loc_toNat hj] at hq
    omega
  have hfr : Frame m0 2672 slots 40 st'.data := by
    refine ⟨?_, fun p hp' ↦ ?_, fun j hj ↦ ?_, kept_trans hf.frame.kept (hm'.kept hwf),
      fun r hr hs ↦ ?_⟩
    · show reg st'.data .rsp = _
      rw [hkeep .rsp (by decide)]; exact hf.frame.sp
    · refine bytesAt_congr (hf.frame.slot p hp') fun i' hi' ↦ ?_
      have hi8 : i' < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi'
      rw [off_add]
      have := slots_ge p hp'; have := slots_le p hp'
      exact hso _ (hxj (p.1 + i') (by omega) (Or.inr (by omega)))
    · rw [hso _ (hxj (2672 + j) (by omega) (Or.inr (by omega)))]
      exact hf.frame.ret j hj
    · rw [hkeep r (by rintro rfl; cases hr)]
      exact hf.frame.regs r hr hs
  have hf' : Fr m0 40 st'.data := ⟨hfr, NativeRustcVm.SameOutside.mono (hf.same.trans hso)
    fun q hq ↦ by
      rcases hq with hq | hq
      · exact hq
      · left
        obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists hq
        rw [hxdef, loc, off_add]
        exact c.loc_stk (by omega)⟩
  have hr' : ∀ r, r ≠ .rax → reg st'.data r = reg d0 r := fun r h ↦ (hkeep r h).trans (hr r h)
  have hd' : NativeRustcVm.SameOutside m0.dmem st'.data.dmem
      (NativeRustcVm.InRange (fa m0) 2672) :=
    NativeRustcVm.SameOutside.mono (hd.trans hso) fun q hq ↦ by
      rcases hq with hq | hq
      · exact hq
      · exact NativeRustcVm.InRange.of_sub (o := 96 + 64 * i) hq
          ((c.region_ok hf.frame.kept).2.mono (by omega)) (by omega)
  simp only [PcOk, cZero_eval env hi hrax] at hpc'
  by_cases hl : i + 1 < 16
  · rw [decide_eq_true hl] at hpc'
    simp only [ite_true] at hpc'
    refine .done _ ⟨hf', hr', hd', Or.inl ⟨hl, hpc'.trans (label_of_infix hp b1_in_code rfl), ?_⟩⟩
    rw [show reg st'.data .rax = _ from hm'.regs .rax _ hrax']
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [show env.regs .rax = _ from hrax]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show Width.W64.bits = 64 from rfl]
    omega
  · rw [decide_eq_false hl] at hpc'
    simp only [Bool.false_eq_true, ite_false] at hpc'
    exact .done _ ⟨hf', hr', hd', Or.inr ⟨by omega, hpc'.trans rfl⟩⟩

/-- **The first zeroing loop**: from `b1` with RAX `56` to `b2`, the frame and the registers but
RAX kept, the memory changed only in the frame. -/
theorem zero_loop (hp : Placed code k) (c : Ctx a s level ba b w rounds m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b1Offset)) (hf : Fr m0 40 st.data)
    (hrax : reg st.data .rax = BitVec.ofNat 64 56)
    (hd : NativeRustcVm.SameOutside m0.dmem st.data.dmem (NativeRustcVm.InRange (fa m0) 2672)) :
    Eventually (step1 Host.exe) (fun st' ↦ Fr m0 40 st'.data ∧
      (∀ r, r ≠ .rax → reg st'.data r = reg st.data r) ∧
      NativeRustcVm.SameOutside m0.dmem st'.data.dmem (NativeRustcVm.InRange (fa m0) 2672) ∧
      st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b2Offset)) st :=
  loop (Q := fun st' ↦ Fr m0 40 st'.data ∧ (∀ r, r ≠ .rax → reg st'.data r = reg st.data r) ∧
      NativeRustcVm.SameOutside m0.dmem st'.data.dmem (NativeRustcVm.InRange (fa m0) 2672) ∧
      st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b2Offset))
    (fun n st' ↦ ∃ i, n = 16 - i ∧ i < 16 ∧ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b1Offset) ∧ Fr m0 40 st'.data ∧
      reg st'.data .rax = BitVec.ofNat 64 (56 + 64 * i) ∧
      (∀ r, r ≠ .rax → reg st'.data r = reg st.data r) ∧
      NativeRustcVm.SameOutside m0.dmem st'.data.dmem (NativeRustcVm.InRange (fa m0) 2672))
    (fun _ st' ⟨i, hn, hi, hpc', hf', hrax', hr', hd'⟩ ↦
      (zero_step hp c hi hpc' hf' hrax' hr' hd').mono fun st'' ⟨hf'', hr'', hd'', h⟩ ↦ by
        rcases h with ⟨hlt, hpc'', hrax''⟩ | ⟨-, hpc''⟩
        · exact Or.inr ⟨16 - (i + 1), by omega, i + 1, rfl, hlt, hpc'', hf'', hrax'', hr'', hd''⟩
        · exact Or.inl ⟨hf'', hr'', hd'', hpc''⟩)
    ⟨0, rfl, by decide, hpc, hf, hrax, fun _ _ ↦ rfl, hd⟩

end

end NativeRustcVmX64.Whir.Levels.FL
