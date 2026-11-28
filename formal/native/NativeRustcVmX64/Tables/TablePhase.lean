module

public import NativeRustcVmX64.Tables.TablePhase.Mid
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.Powers.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TablePhase.Names
public import NativeRustcVmX64.Code.Vm.TableSumcheck.Names

/-!
# `table_phase` on x86-64

**`tablePhase_spec`**: rustc's `table_phase`, placed anywhere in the program, meets
`TablePhasePre`/`TablePhasePost` given its callees' contracts. `b0` saves the registers in the
160-byte frame and calls `bit_length(3)` (`2`); `b1` grinds `grindingBits 4 = 0` bits; `b2` leaves
with AL zero on a failed grind (`exit8`); `b3` squeezes `ξ`; from `b4` on, `mid4`.
-/

namespace NativeRustcVmX64.Tables.TablePhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Vm.TablePhase
open NativeRustcVmX64.Bus.Gkr (Fr off_fb written_fb testAl_okAl)
open NativeRustcVmX64.Tables.ColumnClaims (RegsAre)

public section

variable [Host] {k : Nat}

omit [Host] in
/-- `bit_length(3) - 3`, saturated, as ESI: `0`. -/
theorem grind_bits [Labels] {env : Env} (hx : env.regs .rax = BitVec.ofNat 64 2) :
    (Sym.un .trunc .W32 (.ite (.cmp .ult .W32 (.reg .rax) (.lit 3)) (.lit 0)
      (.bin .sub .W32 (.reg .rax) (.lit 3)))).eval env = BitVec.ofNat 64 0 := by
  simp only [Sym.eval, SBool.eval, hx]
  decide

/-- **`table_phase` meets its contract.** -/
theorem tablePhase_spec (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgrind : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpow : Spec (Labels.label NativeRustcVmX64.Vm.Powers.entryLabel) PowersPre PowersPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    (hsum : ∀ a s heights bus, Spec (Labels.label NativeRustcVmX64.Vm.TableSumcheck.entryLabel)
      (TableSumcheckPre a s heights bus) (TableSumcheckPost a s heights bus))
    {a : DecArea} {s : TState} {L : LayoutW} {bus : BusResultW} :
    Spec (Labels.label NativeRustcVmX64.Vm.TablePhase.entryLabel) (TablePhasePre a s L bus) (TablePhasePost a s L bus) := by
  intro m0 h
  rw [show Labels.label NativeRustcVmX64.Vm.TablePhase.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b0Offset) from hp.label NativeRustcVmX64.Vm.TablePhase.entry_at]
  have p := pre_parts h
  have hS := p.1
  have c144 := ctx h (F := 144) (by decide)
  have hfnw : NativeRustcVm.NoWrap (stackBelow m0 160) (160 + 8) := (ctx h N_ge).noWrap_frame
  -- `b0`: the prologue, `bit_length(3)`
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 160) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b0Offset + b0.length)).toBitVec)
    ⟨frame_mapped hS N_ge, frame_noWrap hS N_ge⟩ (by simp) (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 160 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b0Offset + b0.length)).toBitVec)
      entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨off_frame_F.symm.trans (eval_ptr0 160).symm, trivial⟩ trivial
      trivial trivial
  obtain ⟨hpro, h00, hregs0⟩ := after_eq run_b0 ▸ ok_b0
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf0 (fun _ _ ↦ rfl) hm0
    fun st1 hm1 hpc1 ↦ ?_
  have fr1 : St m0 16 st1.data := Fr.of_prologue hS N_ge hwf0 hm1 hpro slots_le slots_cs h00
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 160) 160) := fun q hq ↦
    hm1.get?_mem0 hwf0 fun hw ↦ hq (written_fb hS N_ge (fun w hw ↦ ⟨h00 w hw,
      belowRet_spec (belowRet_of_pro hpro) w hw (h00 w hw)⟩) hw)
  have g1 : ∀ r v, (r, v) ∈ ([(.rbx, .reg .rcx), (.r14, .reg .rdx), (.r15, .reg .rsi),
      (.r12, .reg .rdi), (.rdi, .lit 3)] : List (Reg64 × Sym)) → reg st1.data r = v.eval
        (frameEnv m0 m0 160 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b0Offset + b0.length)).toBitVec) :=
    fun r v hr ↦ hm1.regs r v (hregs0 _ hr)
  have hts1 : TStateAt st1.data.dmem (reg m0 .rdi) a s :=
    tstate_keep h p.2.2.2.1 (hm1.kept hwf0) hs1 fun q hq ↦ .inl (frame_in h hq)
  have hle_b : 160 - 16 + bitLengthStack ≤ N := by decide
  have hat1 := at_call h fr1 (by omega)
  refine Fr.call hS N_ge (c := 16) (lo := 0) (len := 0) (by omega) hle_b
    (fun p hp ↦ by have := slots_le p hp; have := (show ∀ p ∈ slots, 112 ≤ p.1 by decide) p hp; omega)
    (by omega) (fun q hq ↦ outs_not_frame h hq) (X := fun _ ↦ False) (fun _ hq ↦ hq.elim)
    hbl fr1 hpc1 (c144.stackOk hat1 hle_b)
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ .inl hq', hq.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  have hrax2 : reg m2 .rax = BitVec.ofNat 64 2 := by
    apply BitVec.eq_of_toNat_eq
    rw [hq2.1, show (reg st1.data .rdi).toNat = 3 by rw [g1 .rdi (.lit 3) (by simp)]; rfl,
      bitLength_three]
    rfl
  have hts2 : TStateAt m2.dmem (reg m0 .rdi) a s :=
    tstate_keep h hts1 hq2.2.2.2 hs2 fun q hq ↦ hq.elim
      (fun hq ↦ .inl (c144.inRange_callee hat1 hle_b hq).1) False.elim
  have hr2 : ∀ r, calleeSaved r = true → ∀ v, (r, v) ∈ ([(.rbx, .reg .rcx), (.r14, .reg .rdx),
      (.r15, .reg .rsi), (.r12, .reg .rdi), (.rdi, .lit 3)] : List (Reg64 × Sym)) →
      reg m2 r = v.eval (frameEnv m0 m0 160 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b0Offset + b0.length)).toBitVec) :=
    fun r hc v hr ↦ (hcs2 r hc).trans (g1 r v hr)
  -- `b1`: `grind(0)`
  obtain ⟨hmid1, h01, hregs1⟩ := after_eq run_b1 ▸ ok_b1
  refine blk h fr2 (st := ⟨m2, _⟩) (b1_in_code.trans hp.1 (by simp [b1])) run_b1 hmid1 h01 rfl
    fun st3 fr3 hm3 hs3 hpc3 ↦ ?_
  have hwf3 := wfF h fr2 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b1Offset + b1.length)).toBitVec)
  have g3 : ∀ r v, (r, v) ∈ ([(.rdi, .reg .r12), (.rbp, .lit 0), (.rsi, .un .trunc .W32 (.ite
      (.cmp .ult .W32 (.reg .rax) (.lit 3)) (.lit 0) (.bin .sub .W32 (.reg .rax) (.lit 3)))),
      (.rbx, .reg .rbx), (.r12, .reg .r12), (.r14, .reg .r14), (.r15, .reg .r15)] :
        List (Reg64 × Sym)) → reg st3.data r = v.eval
          (frameEnv m0 m2 160 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b1Offset + b1.length)).toBitVec) :=
    fun r v hr ↦ hm3.regs r v (hregs1 _ hr)
  have e3di : reg st3.data .rdi = reg m0 .rdi :=
    (g3 .rdi (.reg .r12) (by simp)).trans (hr2 .r12 rfl (.reg .rdi) (by simp))
  have e3gb : grindBits st3.data = 0 := by
    unfold grindBits
    rw [g3 .rsi (.un .trunc .W32 (.ite (.cmp .ult .W32 (.reg .rax) (.lit 3)) (.lit 0)
      (.bin .sub .W32 (.reg .rax) (.lit 3)))) (by simp), grind_bits hrax2]
    rfl
  have hts3 : TStateAt st3.data.dmem (reg m0 .rdi) a s :=
    tstate_keep h hts2 (hm3.kept hwf3) hs3 fun q hq ↦ .inl (frame_in h hq)
  have hle_g : 160 - 16 + grindStack ≤ N := by decide
  have hat3 := at_call h fr3 (by omega)
  have hpre3 : GrindPre a s st3.data := by
    unfold GrindPre
    rw [e3di, e3gb]
    refine ⟨c144.stackOk hat3 hle_g, c144.rcAt hat3 hle_g, hts3, c144.tstateOk hat3 hle_g,
      by decide, got_call h fr3 (by omega) hle_g ?_⟩
    intro l hl b hb
    exact ((got h).1 l hl).2.2.2 b (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> simp)
  refine Fr.call hS N_ge (c := 16) (lo := 0) (len := 0) (by omega) hle_g
    (fun p hp ↦ by have := slots_le p hp; have := (show ∀ p ∈ slots, 112 ≤ p.1 by decide) p hp; omega)
    (by omega) (fun q hq ↦ outs_not_frame h hq) (X := fun q ↦ NativeRustcVm.InRange (reg m0 .rdi)
      tstateBytes q) (fun _ hq ↦ .inl (.inl hq))
    (hgrind a s) fr3 hpc3 hpre3
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ by
      rw [e3di] at hq'; exact hq'.elim .inr .inl, hq.2.2.2⟩)
    fun m4 fr4 hq4 hs4 hcs4 ↦ ?_
  obtain ⟨q40, q41, -, hsv4⟩ := hq4
  rw [e3gb, ← grindingBits_four] at q40 q41
  rw [e3di] at q41
  have hrbp4 : reg m4 .rbp = BitVec.ofNat 64 0 :=
    (hcs4 .rbp rfl).trans (g3 .rbp (.lit 0) (by simp))
  have hr4 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg m4 r = reg m2 r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hcs4 .rbx rfl).trans (g3 .rbx (.reg .rbx) (by simp))
    · exact (hcs4 .r12 rfl).trans (g3 .r12 (.reg .r12) (by simp))
    · exact (hcs4 .r14 rfl).trans (g3 .r14 (.reg .r14) (by simp))
    · exact (hcs4 .r15 rfl).trans (g3 .r15 (.reg .r15) (by simp))
  -- `b2`: the grind's result
  obtain ⟨hmid2, hmem2, hregs2⟩ := after_eq run_b2 ▸ ok_b2
  refine blk h fr4 (st := ⟨m4, _⟩) (b2_in_code.trans hp.1 (by simp [b2])) run_b2 hmid2
    (by rw [hmem2]; intro w hw; cases hw) rfl fun st5 fr5 hm5 _ hpc5 ↦ ?_
  have hwf5 := wfF h fr4 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b2Offset + b2.length)).toBitVec)
  have hd5 : st5.data.dmem = m4.dmem := hm5.dmem_eq hwf5 hmem2
  have g5 : ∀ r ∈ [Reg64.rbp, .rbx, .r12, .r14, .r15], reg st5.data r = reg m4 r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hm5.regs _ _ (hregs2 (.rbp, .reg .rbp) (by simp))
    · exact hm5.regs _ _ (hregs2 (.rbx, .reg .rbx) (by simp))
    · exact hm5.regs _ _ (hregs2 (.r12, .reg .r12) (by simp))
    · exact hm5.regs _ _ (hregs2 (.r14, .reg .r14) (by simp))
    · exact hm5.regs _ _ (hregs2 (.r15, .reg .r15) (by simp))
  have hc5 : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
      (frameEnv m0 m4 160 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b2Offset + b2.length)).toBitVec) =
      !((grind (grindingBits 4)).run s).isSome := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    exact testAl_okAl q40
  simp only [PcOk] at hpc5
  obtain ⟨hT5, hF5⟩ := NativeRustcVmX64.Arrays.pc_cond hpc5
  cases hr : (grind (grindingBits 4)).run s with
  | none =>
    -- a failed grind: the exit with AL zero
    have hrun : (tablePhase L bus).run s = none := by rw [tablePhase_run, hr]; rfl
    have hpc5' := hT5 (hc5.trans (by rw [hr]; rfl))
    refine exit8 hp h (hpc5'.trans (hp.label NativeRustcVmX64.Vm.TablePhase.label_2_at)) fr5 ?_ (fun x s' h' ↦ by
      rw [hrun] at h'; cases h') (fun x s' h' ↦ by rw [hrun] at h'; cases h')
    rw [g5 .rbp (by simp), hrbp4, hrun]
    rfl
  | some q =>
    obtain ⟨⟨⟩, s1⟩ := q
    have hpc5 := hF5 (fun hc ↦ by have := hc5.symm.trans hc; rw [hr] at this; cases this)
    have hts4 := q41 () s1 hr
    -- `b3`: `squeeze`
    obtain ⟨hmid6, h06, hregs6⟩ := after_eq run_b3 ▸ ok_b3
    refine blk h fr5 (b3_in_code.trans hp.1 (by simp [b3])) run_b3 hmid6 h06
      (by rw [hpc5]; rfl) fun st6 fr6 hm6 hs6 hpc6 ↦ ?_
    have hwf6 := wfF h fr5 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b3Offset + b3.length)).toBitVec)
    have g6 : ∀ r v, (r, v) ∈ ([(.rdi, .reg .r12), (.rbp, .reg .rbp), (.rbx, .reg .rbx),
        (.r12, .reg .r12), (.r14, .reg .r14), (.r15, .reg .r15)] : List (Reg64 × Sym)) →
        reg st6.data r = v.eval (frameEnv m0 st5.data 160 [] (fun _ ↦ 0)
          (Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b3Offset + b3.length)).toBitVec) := fun r v hr ↦ hm6.regs r v (hregs6 _ hr)
    have hreg6 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg st6.data r = reg m2 r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ((g6 .rbx (.reg .rbx) (by simp)).trans (g5 .rbx (by simp))).trans (hr4 .rbx (by simp))
      · exact ((g6 .r12 (.reg .r12) (by simp)).trans (g5 .r12 (by simp))).trans (hr4 .r12 (by simp))
      · exact ((g6 .r14 (.reg .r14) (by simp)).trans (g5 .r14 (by simp))).trans (hr4 .r14 (by simp))
      · exact ((g6 .r15 (.reg .r15) (by simp)).trans (g5 .r15 (by simp))).trans (hr4 .r15 (by simp))
    have e6di : reg st6.data .rdi = reg m0 .rdi :=
      ((g6 .rdi (.reg .r12) (by simp)).trans (g5 .r12 (by simp))).trans
        ((hr4 .r12 (by simp)).trans (hr2 .r12 rfl (.reg .rdi) (by simp)))
    have hts6 : TStateAt st6.data.dmem (reg m0 .rdi) a s1 :=
      tstate_keep h (d := st5.data.dmem) (by rw [hd5]; exact hts4) (hm6.kept hwf6) hs6
        fun q hq ↦ .inl (frame_in h hq)
    have hle_q : 160 - 16 + squeezeStack ≤ N := by decide
    have hat6 := at_call h fr6 (by omega)
    have htok6 := c144.tstateOk hat6 hle_q
    have hfp := hts6.footprint
    have hTn : NativeRustcVm.NoWrap (reg m0 .rdi) tstateBytes := hfp.1.2
    have hpre6 : SqueezePre s1.sponge st6.data := by
      unfold SqueezePre
      rw [e6di]
      refine ⟨c144.stackOk hat6 hle_q, c144.rcAt hat6 hle_q,
        ⟨fun j hj ↦ hfp.1.1 j (by simp only [spongeBytes] at hj; show j < 760; omega),
          hTn.mono (by decide), by
          have h1 : NativeRustcVm.Apart (reg m0 .rdi) 760 (stackBelow st6.data squeezeStack)
            (squeezeStack + 8) := htok6.1
          unfold NativeRustcVm.Apart at h1
          show (reg m0 .rdi).toNat + 328 ≤ _ ∨ _ ≤ (reg m0 .rdi).toNat
          omega, by
          have h1 : NativeRustcVm.Apart (reg m0 .rdi) 760 rcAddr 192 := htok6.2.2
          unfold NativeRustcVm.Apart at h1
          show (reg m0 .rdi).toNat + 328 ≤ _ ∨ _ ≤ (reg m0 .rdi).toNat
          omega⟩,
        hts6.sponge, got_call h fr6 (by omega) hle_q ?_⟩
      intro l hl b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact Apart.sub (((got h).1 l hl).2.2.2 (reg m0 .rdi, tstateBytes) (by simp))
          (Nat.le_refl _) (by simp only [spongeBytes, tstateBytes]; omega)
      · exact ((got h).1 l hl).2.2.2 (rcAddr, 192) (by simp)
    refine Fr.call hS N_ge (c := 16) (lo := 0) (len := 0) (by omega) hle_q
      (fun p hp ↦ by have := slots_le p hp; have := (show ∀ p ∈ slots, 112 ≤ p.1 by decide) p hp; omega)
      (by omega) (fun q hq ↦ outs_not_frame h hq)
      (X := NativeRustcVm.InRange (reg m0 .rdi) spongeBytes)
      (fun _ hq ↦ .inl (.inl (inRange_mono hq (by decide)))) (hsq s1.sponge) fr6 hpc6 hpre6
      (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q hq' ↦ by
        rw [e6di] at hq'; exact hq'.elim .inr .inl, hq.2.2.2.2⟩)
      fun m7 fr7 hq7 hs7 hcs7 ↦ ?_
    obtain ⟨c0, c1, hsp7, -, hsv7⟩ := hq7
    rw [e6di] at hsp7
    have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st6.data squeezeStack) squeezeStack q →
        ¬NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∧
          ¬NativeRustcVm.InRange a.words (8 * a.len) q := fun q hq ↦
      (ctx h N_ge).stack_not_t (c144.inRange_callee hat6 hle_q hq).1
    have hts7 : TStateAt m7.dmem (reg m0 .rdi) a { s1 with sponge := s1.sponge.squeeze.2 } := by
      refine hts6.with_sponge hsv7.2 hcal (fun q hq ↦ hs7 q ?_) hsp7
      rintro (h' | h')
      · exact hq (.inr h')
      · obtain ⟨j, hj, hw, hq'⟩ := touch_of_inRange (o := 0) (n := 328) hTn (by decide)
          (by rwa [off_zero])
        exact hq (.inl ⟨j, hj, hw.2, hq'⟩)
    refine mid4 hp hpow hdot hsum h hr (st := ⟨m7, _⟩)
      (by show Host.addrOf (k + NativeRustcVmX64.Vm.TablePhase.b3Offset + b3.length) = _; rfl) fr7 ?_ ?_ ?_ ?_ ?_ hts7
    · exact (hcs7 .r12 rfl).trans ((hreg6 .r12 (by simp)).trans (hr2 .r12 rfl (.reg .rdi) (by simp)))
    · exact (hcs7 .r15 rfl).trans ((hreg6 .r15 (by simp)).trans (hr2 .r15 rfl (.reg .rsi) (by simp)))
    · exact (hcs7 .r14 rfl).trans ((hreg6 .r14 (by simp)).trans (hr2 .r14 rfl (.reg .rdx) (by simp)))
    · exact (hcs7 .rbx rfl).trans ((hreg6 .rbx (by simp)).trans (hr2 .rbx rfl (.reg .rcx) (by simp)))
    · show ewArg (reg m7 .rax) (reg m7 .rdx) = _
      rw [c0, c1]
      rfl

end

end NativeRustcVmX64.Tables.TablePhase
