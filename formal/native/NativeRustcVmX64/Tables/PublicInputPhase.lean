module

public import NativeRustcVmX64.Tables.PublicInputPhase.Limbs
public import NativeRustcVmX64.Code.Vm.LayoutWPlacement.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmX64.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmX64.Code.Vm.PushClaim.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names

/-!
# `public_input_phase` on x86-64

**`publicInputPhase_spec`**: rustc's `public_input_phase`, placed anywhere in the program, meets
`PublicInputPhasePre`/`PublicInputPhasePost` given its callees' contracts. `b0` saves the
registers and squeezes the challenge; `b1` zeroes the claims' point and calls
`LayoutW::placement(memory0)`; `b2` takes the point's length `max vc 1` (never above `31`); the
first limb (`limb0`: `b3`, `multilinear_eval_by`, `b4`, `push_claim`, `b5`) leaves with AL zero
when its claim does not fit, else the second (`limb1`).
-/

namespace NativeRustcVmX64.Tables.PublicInputPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmX64.Vm.PublicInputPhase
open NativeRustcVmX64.Bus.Gkr (Fr testAl_okAl written_fb)
open NativeRustcVmX64.Tables.ColumnClaims (RegsAre)
open NativeRustcVm.Layout (LayoutWAt layoutBytes Same ClaimsWAt claimsBytes claimCap pointCap)
open LeanVM.Protocol.Verifier (memory0 memory1)
open NativeRustcVmX64.Arrays (eval_reg)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {L : LayoutW} {pub : Vector UInt64 4}
  {cs : Array ColumnClaimW} {m0 : MachineData}

omit [Host] in
/-- `b2`'s branch is not taken: the column count is at most `31`. -/
theorem cond31 {v : Nat} (hv : v ≤ 31) :
    (!CmpOp.apply .ult .W64 (BitVec.ofNat 64 v) 31#64 &&
      !CmpOp.apply .eq .W64 (BitVec.ofNat 64 v) 31#64) = false := by
  simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat, Bool.and_eq_false_iff,
    Bool.not_eq_false', decide_eq_true_eq, beq_iff_eq, Width.bits]
  rcases Nat.lt_or_eq_of_le hv with h | rfl
  · left; rw [Nat.mod_eq_of_lt (by omega)]; omega
  · right; rfl

omit [Host] in
/-- `b2`'s point length: `max v 1`. -/
theorem len_max {v : Nat} {x : BitVec 64} (hx : x = BitVec.ofNat 64 v) (hv : v ≤ 31)
    {inst : Decidable (CmpOp.apply .ult .W64 x (BitVec.ofNat 64 1) = true)} :
    BinOp.apply .add .W64 x (@ite _ (CmpOp.apply .ult .W64 x (BitVec.ofNat 64 1) = true) inst
      (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)) = BitVec.ofNat 64 (max v 1) := by
  subst hx
  apply BitVec.eq_of_toNat_eq
  simp only [CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.ult, BitVec.toNat_ofNat,
    Width.bits]
  split <;> rename_i hh <;> simp only [decide_eq_true_eq] at hh <;>
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

/-- **The first limb**: `b3`, its value, `b4`, its claim, `b5`, then `limb1` or the exit. -/
theorem limb0 (hp : Placed code k) (h : PublicInputPhasePre a s L pub cs m0)
    (hmle : Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    (hpush : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b3Offset)) (hL : LimbAt a s L cs 2 m0 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
      PublicInputPhasePost a s L pub cs m0 st'.data) st := by
  have p := pre_parts h
  obtain ⟨hm3, h03, hw3, hr3, hwr3⟩ := after_eq run_b3 ▸ ok_b3
  refine mleStep h hL.fr hL.r14 hL.r15 hL.r12 (i := 0) (by omega) (b3_in_code.trans hp.1
    (by simp [b3])) run_b3 hm3 h03 (by simpa using hr3)
    (fun q hq ↦ hwr3 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)) hmle hpc
    fun st1 st2 hm1 hpc2 fr2 hval hcs2 hkeep2 hs2 hk2 ↦ ?_
  have hwf1 := wfPub h hL.fr (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b3Offset + b3.length)).toBitVec)
  -- the point after `b3`: the challenge in words `0`, `1`
  have hpt1 : PtW m0 st1.data.dmem (chOf s) 0 := by
    intro i h1 h2
    rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi
    · have := wordW (m0 := m0) hm1 (o := 64) (by omega) (hwr3 (64, .reg .r15) (by simp))
      rw [eval_reg, Env.ofMachine_regs, show st.data.regs.get64 .r15 = reg st.data .r15 from rfl,
        hL.r15, UInt64.ofBitVec_toBitVec] at this
      exact this
    · have := wordW (m0 := m0) hm1 (o := 72) (by omega) (hwr3 (72, .reg .r12) (by simp))
      rw [eval_reg, Env.ofMachine_regs, show st.data.regs.get64 .r12 = reg st.data .r12 from rfl,
        hL.r12, UInt64.ofBitVec_toBitVec] at this
      exact this
    · exact wordHi hwf1 hm1 (writesIn_of_mid hm3) hw3 (by omega) (by omega) (hL.pt i hi h2)
  have hpt2 : PtW m0 st2.data.dmem (chOf s) 0 := fun i h1 h2 j hj ↦ by
    have hj' : j < 8 := by simpa [NativeRustcVm.length_wordBytes] using hj
    rw [off_add, hkeep2 _ (by omega) (by omega), ← off_add]
    exact hpt1 i h1 h2 j hj
  have hcl2 := claims_keep h hs2 (fun _ hq ↦ hq) hL.claims
  obtain ⟨hm4, h04, hw4, hr4⟩ := after_eq run_b4 ▸ ok_b4
  refine pushStep h fr2 hcl2 hpt2 ((hcs2 .rbx rfl).trans hL.rbx) ((hcs2 .r13 rfl).trans hL.r13)
    p.2.2.2.2.2.2.2.2.1 (col := 0) (v := .lit 0) (b4_in_code.trans hp.1 (by simp [b4]))
    run_b4 hm4 h04 hw4 hr4 (by decide) hpush (by rw [hpc2]; rfl)
    fun st3 st4 hm3' hpc4 fr4 hres4 hcs4 hpt4 hs4 hk4 ↦ ?_
  have hwf3 := wfF h fr2 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b4Offset + b4.length)).toBitVec)
  have hts4 : TStateAt st4.data.dmem (reg m0 .rdi) a { s with sponge := s.sponge.squeeze.2 } :=
    tstate_keep h hL.ts (fun p hp ↦ hk4 p (hk2 p hp)) (hs2.trans hs4) fun q hq ↦ by
      rcases hq with hq | hq
      · exact .inl hq
      · exact hq
  have g3 : ∀ r w, (r, w) ∈ ([(.rcx, .reg .r13), (.rdx, .ptr 0 64), (.rsi, .lit 0),
      (.rdi, .reg .rbx), (.rbp, .lit 0), (.r8, .reg .rax), (.r9, .reg .rdx), (.rbx, .reg .rbx),
      (.r12, .reg .r12), (.r13, .reg .r13), (.r14, .reg .r14), (.r15, .reg .r15)] :
        List (Reg64 × Sym)) → reg st3.data r = w.eval
        (frameEnv m0 st2.data 608 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b4Offset + b4.length)).toBitVec) :=
    fun r w hr ↦ hm3'.regs r w (hr4 _ hr)
  -- `b5`: the first claim's result
  obtain ⟨hm5, hmem5, hr5⟩ := after_eq run_b5 ▸ ok_b5
  refine blk h fr4 (b5_in_code.trans hp.1 (by simp [b5])) run_b5 hm5
    (by rw [hmem5]; intro w hw; cases hw) (by rw [hpc4]; rfl) fun st5 fr5 hm5' _ hpc5 ↦ ?_
  have hwf5 := wfF h fr4 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b5Offset + b5.length)).toBitVec)
  have hd5 : st5.data.dmem = st4.data.dmem := hm5'.dmem_eq hwf5 hmem5
  have g5 : ∀ r ∈ [Reg64.rbp, .rbx, .r12, .r13, .r14, .r15], reg st5.data r = reg st4.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hm5'.regs _ _ (hr5 (.rbp, .reg .rbp) (by simp))
    · exact hm5'.regs _ _ (hr5 (.rbx, .reg .rbx) (by simp))
    · exact hm5'.regs _ _ (hr5 (.r12, .reg .r12) (by simp))
    · exact hm5'.regs _ _ (hr5 (.r13, .reg .r13) (by simp))
    · exact hm5'.regs _ _ (hr5 (.r14, .reg .r14) (by simp))
    · exact hm5'.regs _ _ (hr5 (.r15, .reg .r15) (by simp))
  have hreg : ∀ r, calleeSaved r = true → r ≠ .rbp → reg st5.data r = reg st.data r := by
    intro r hc hne
    rcases calleeSaved_cases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g5 .rbx (by simp), hcs4 .rbx rfl, g3 .rbx (.reg .rbx) (by simp)]; exact hcs2 .rbx rfl
    · exact absurd rfl hne
    · rw [g5 .r12 (by simp), hcs4 .r12 rfl, g3 .r12 (.reg .r12) (by simp)]; exact hcs2 .r12 rfl
    · rw [g5 .r13 (by simp), hcs4 .r13 rfl, g3 .r13 (.reg .r13) (by simp)]; exact hcs2 .r13 rfl
    · rw [g5 .r14 (by simp), hcs4 .r14 rfl, g3 .r14 (.reg .r14) (by simp)]; exact hcs2 .r14 rfl
    · rw [g5 .r15 (by simp), hcs4 .r15 rfl, g3 .r15 (.reg .r15) (by simp)]; exact hcs2 .r15 rfl
  have hrbp5 : reg st5.data .rbp = BitVec.ofNat 64 0 := by
    rw [g5 .rbp (by simp), hcs4 .rbp rfl, g3 .rbp (.lit 0) (by simp)]; rfl
  simp only [PcOk] at hpc5
  have hc5 : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
      (frameEnv m0 st4.data 608 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b5Offset + b5.length)).toBitVec) =
      decide (boolRet st4.data = 0) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    exact NativeRustcVmX64.Sumcheck.testAl_eq _
  obtain ⟨hT5, hF5⟩ := NativeRustcVmX64.Arrays.pc_cond hpc5
  by_cases hfit : cs.size < claimCap
  · simp only [hfit, ↓reduceIte] at hres4
    have hpc5' := hF5 (by rw [hc5, hres4.1]; decide)
    refine limb1 hp h hmle hpush (st := st5) (by rw [hpc5']; rfl) ⟨fr5, ?_, ?_, ?_, ?_, ?_, ?_,
      by rw [hd5]; exact hpt4, by rw [hd5]; exact hts4⟩
    · rw [hreg .rbx rfl (by decide)]; exact hL.rbx
    · rw [hreg .r14 rfl (by decide)]; exact hL.r14
    · rw [hreg .r15 rfl (by decide)]; exact hL.r15
    · rw [hreg .r12 rfl (by decide)]; exact hL.r12
    · rw [hreg .r13 rfl (by decide)]; exact hL.r13
    · rw [hd5]
      have := hres4.2
      rw [hval] at this
      exact this
  · simp only [hfit, ↓reduceIte] at hres4
    have hpc5' := hT5 (by rw [hc5, hres4]; decide)
    have hnf : ¬cs.size + 2 ≤ claimCap := by omega
    refine exit9 hp h (hpc5'.trans (hp.label NativeRustcVmX64.Vm.PublicInputPhase.label_3_at)) fr5 ?_ (fun _ _ _ hf ↦ absurd hf hnf) ?_
    · rw [hrbp5, decide_eq_false hnf, Bool.and_false]; rfl
    · intro x s' hr
      rw [run_eq] at hr
      cases hr
      rw [hd5]; exact hts4

/-- **`public_input_phase` meets its contract.** -/
theorem publicInputPhase_spec (hp : Placed code k)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hplace : ∀ L, Spec (Labels.label NativeRustcVmX64.Vm.LayoutWPlacement.entryLabel) (LayoutWPlacementPre L)
      (LayoutWPlacementPost L))
    (hmle : Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    (hpush : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs)) :
    Spec (Labels.label NativeRustcVmX64.Vm.PublicInputPhase.entryLabel) (PublicInputPhasePre a s L pub cs)
      (PublicInputPhasePost a s L pub cs) := by
  intro m0 h
  rw [show Labels.label NativeRustcVmX64.Vm.PublicInputPhase.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b0Offset) from hp.label NativeRustcVmX64.Vm.PublicInputPhase.entry_at]
  have p := pre_parts h
  have hS := p.1
  have c := ctx h N_ge
  -- `b0`: the prologue, `squeeze`
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 608) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b0Offset + b0.length)).toBitVec)
    ⟨frame_mapped hS N_ge, frame_noWrap hS N_ge⟩ (by simp) (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 608 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b0Offset + b0.length)).toBitVec)
      (stO 608) m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨off_frame_F.symm.trans (eval_ptr0 608).symm, trivial⟩ trivial
      trivial trivial
  obtain ⟨hpro, h00, hregs0⟩ := after_eq run_b0 ▸ ok_b0
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf0 (fun _ _ ↦ rfl) hm0
    fun st1 hm1 hpc1 ↦ ?_
  have fr1 : St m0 0 st1.data := Fr.of_prologue hS N_ge hwf0 hm1 hpro slots_le slots_cs h00
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (fb m0) 608) := fun q hq ↦
    hm1.get?_mem0 hwf0 fun hw ↦ hq (written_fb hS N_ge (fun w hw ↦ ⟨h00 w hw,
      belowRet_spec (belowRet_of_pro hpro) w hw (h00 w hw)⟩) hw)
  have g1 : ∀ r w, (r, w) ∈ ([(.rbx, .reg .rcx), (.r14, .reg .rdx), (.r13, .reg .rsi),
      (.rdi, .reg .rdi)] : List (Reg64 × Sym)) → reg st1.data r = w.eval
        (frameEnv m0 m0 608 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b0Offset + b0.length)).toBitVec) :=
    fun r w hr ↦ hm1.regs r w (hregs0 _ hr)
  have e1di : reg st1.data .rdi = reg m0 .rdi := g1 .rdi (.reg .rdi) (by simp)
  have hk1 := hm1.kept hwf0
  have hts1 : TStateAt st1.data.dmem (reg m0 .rdi) a s :=
    tstate_keep h p.2.2.1 hk1 hs1 fun q hq ↦ .inl (frame_in h hq)
  have hle_q : 608 + squeezeStack ≤ N := by decide
  have hat1 := at_call h fr1
  have htok1 := c.tstateOk hat1 hle_q
  have hfp := hts1.footprint
  have hTn : NativeRustcVm.NoWrap (reg m0 .rdi) tstateBytes := hfp.1.2
  have hpre1 : SqueezePre s.sponge st1.data := by
    unfold SqueezePre
    rw [e1di]
    refine ⟨c.stackOk hat1 hle_q, c.rcAt hat1 hle_q,
      ⟨fun j hj ↦ hfp.1.1 j (by simp only [spongeBytes] at hj; show j < 760; omega),
        hTn.mono (by decide), by
          have h1 : NativeRustcVm.Apart (reg m0 .rdi) 760 (stackBelow st1.data squeezeStack)
            (squeezeStack + 8) := htok1.1
          unfold NativeRustcVm.Apart at h1
          show (reg m0 .rdi).toNat + 328 ≤ _ ∨ _ ≤ (reg m0 .rdi).toNat
          omega, by
          have h1 : NativeRustcVm.Apart (reg m0 .rdi) 760 rcAddr 192 := htok1.2.2
          unfold NativeRustcVm.Apart at h1
          show (reg m0 .rdi).toNat + 328 ≤ _ ∨ _ ≤ (reg m0 .rdi).toNat
          omega⟩, hts1.sponge, got_call h fr1 hle_q ?_⟩
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact Apart.sub (((got h).1 l hl).2.2.2 (reg m0 .rdi, tstateBytes) (by simp))
        (Nat.le_refl _) (by simp only [spongeBytes, tstateBytes]; omega)
    · exact ((got h).1 l hl).2.2.2 (rcAddr, 192) (by simp)
  refine Fr.call hS N_ge (c := 0) (lo := 0) (len := 0) (by omega) (by simpa using hle_q)
    (fun p hp ↦ by have := slots_le p hp; have := slots_hi p hp; omega) (by omega)
    (fun q hq ↦ outs_not_frame h hq) (X := NativeRustcVm.InRange (reg m0 .rdi) spongeBytes)
    (fun _ hq ↦ .inl (.inl (inRange_mono hq (by decide)))) (hsq s.sponge) fr1 hpc1 hpre1
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q hq' ↦ by
      rw [e1di] at hq'; exact hq'.elim .inr .inl, hq.2.2.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  obtain ⟨c0, c1, hsp2, -, hsv2⟩ := hq2
  rw [e1di] at hsp2
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st1.data squeezeStack) squeezeStack q →
      ¬NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∧
        ¬NativeRustcVm.InRange a.words (8 * a.len) q := fun q hq ↦
    c.stack_not_t (callee_in h hat1 hle_q hq)
  have hts2 : TStateAt m2.dmem (reg m0 .rdi) a { s with sponge := s.sponge.squeeze.2 } := by
    refine hts1.with_sponge hsv2.2 hcal (fun q hq ↦ hs2 q ?_) hsp2
    rintro (h' | h')
    · exact hq (.inr h')
    · obtain ⟨j, hj, hw, hq'⟩ := touch_of_inRange (o := 0) (n := 328) hTn (by decide)
        (by rwa [off_zero])
      exact hq (.inl ⟨j, hj, hw.2, hq'⟩)
  have ho := p.2.2.2.2.1
  have hcS : ∀ j < claimsBytes, ¬NativeRustcVm.InRange (stackBelow m0 N) N
      (reg m0 .rcx + BitVec.ofNat 64 j) ∧ ¬NativeRustcVm.InRange (reg m0 .rdi) tstateBytes
      (reg m0 .rcx + BitVec.ofNat 64 j) := fun j hj ↦
    ⟨fun h' ↦ NativeRustcVm.Apart.not_inRange_add ho.2.2.2.2.1 ho.2.1 c.noWrap_stack hj
      (inRange_mono h' (by omega)),
     NativeRustcVm.Apart.not_inRange_add ho.2.2.1 ho.2.1 hTn hj⟩
  have hcl2 : ClaimsWAt m2.dmem (reg m0 .rcx) cs :=
    NativeRustcVm.Tables.ClaimsWAt.of_same p.2.2.2.2.2.1 fun j hj ↦ by
      rw [hs2 _ fun h' ↦ ?_, hs1 _ fun h' ↦ (hcS j hj).1 (frame_in h h')]
      rcases h' with h' | h'
      · exact (hcS j hj).1 (callee_in h hat1 hle_q h')
      · exact (hcS j hj).2 (inRange_mono h' (by decide))
  have hr2 : ∀ r, calleeSaved r = true → ∀ w, (r, w) ∈ ([(.rbx, .reg .rcx), (.r14, .reg .rdx),
      (.r13, .reg .rsi), (.rdi, .reg .rdi)] : List (Reg64 × Sym)) → reg m2 r = w.eval
        (frameEnv m0 m0 608 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b0Offset + b0.length)).toBitVec) :=
    fun r hc w hr ↦ (hcs2 r hc).trans (g1 r w hr)
  -- `b1`: the point zeroed, `LayoutW::placement(memory0)`
  obtain ⟨hm1b, h01b, hw1b, hr1b, hz1b⟩ := after_eq run_b1 ▸ ok_b1
  refine blk h fr2 (st := ⟨m2, _⟩) (b1_in_code.trans hp.1 (by simp [b1])) run_b1 hm1b h01b rfl
    fun st3 fr3 hm3 hs3 hpc3 ↦ ?_
  have hwf3 := wfF h fr2 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b1Offset + b1.length)).toBitVec)
  have g3 : ∀ r w, (r, w) ∈ ([(.rsi, .lit 0), (.rdi, .reg .r13), (.rbp, .lit 0), (.r12, .reg .rdx),
      (.r15, .reg .rax), (.rbx, .reg .rbx), (.r14, .reg .r14)] : List (Reg64 × Sym)) →
      reg st3.data r = w.eval (frameEnv m0 m2 608 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b1Offset + b1.length)).toBitVec) := fun r w hr ↦ hm3.regs r w (hr1b _ hr)
  have e3di : reg st3.data .rdi = reg m0 .rsi :=
    (g3 .rdi (.reg .r13) (by simp)).trans (hr2 .r13 rfl (.reg .rsi) (by simp))
  have e3si : reg st3.data .rsi = BitVec.ofNat 64 0 := g3 .rsi (.lit 0) (by simp)
  have hpt3 : PtW m0 st3.data.dmem (chOf s) 2 := fun i h1 h2 ↦ by
    have := wordW (m0 := m0) hm3 (o := 64 + 8 * i) (by omega) (hz1b i (by omega))
    rw [show ptw (chOf s) i = 0 by unfold ptw; split <;> first | omega | rfl]
    exact this
  have hL3 : LayoutWAt st3.data.dmem (reg m0 .rsi) L :=
    NativeRustcVm.Tables.LayoutWAt.of_same p.2.2.2.2.2.2.2.1 (same_in h fr3 p.2.2.2.2.2.2.1)
  have hle_l : 608 + layoutWPlacementStack ≤ N := by decide
  have hat3 := at_call h fr3
  have hpre3 : LayoutWPlacementPre L st3.data := by
    unfold LayoutWPlacementPre
    rw [e3di, e3si]
    exact ⟨c.stackOk hat3 hle_l, by decide, hL3,
      (readIn_call h fr3 hle_l p.2.2.2.2.2.2.1).1⟩
  refine Fr.call hS N_ge (c := 0) (lo := 0) (len := 0) (by omega) (by simpa using hle_l)
    (fun p hp ↦ by have := slots_le p hp; have := slots_hi p hp; omega) (by omega)
    (fun q hq ↦ outs_not_frame h hq) (X := fun _ ↦ False) (fun _ hq ↦ hq.elim) (hplace L) fr3 hpc3
    hpre3 (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun _ hq' ↦ hq'.elim, hq.2.2.2⟩)
    fun m4 fr4 hq4 hs4 hcs4 ↦ ?_
  obtain ⟨hvc, -, hs4', hsv4⟩ := hq4
  rw [e3si] at hvc
  have hd4 : m4.dmem = st3.data.dmem := Std.ExtHashMap.ext_getElem? fun q ↦ by
    rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
    exact hs4' q id
  have hvc' : reg m4 .rax = BitVec.ofNat 64 (vcOf L) := by
    rw [hvc]; rfl
  -- `b2`: the point's length
  obtain ⟨hm5, hmem5, hr5⟩ := after_eq run_b2 ▸ ok_b2
  refine blk h fr4 (st := ⟨m4, _⟩) (b2_in_code.trans hp.1 (by simp [b2])) run_b2 hm5
    (by rw [hmem5]; intro w hw; cases hw) rfl fun st5 fr5 hm5' _ hpc5 ↦ ?_
  have hwf5 := wfF h fr4 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b2Offset + b2.length)).toBitVec)
  have hd5 : st5.data.dmem = m4.dmem := hm5'.dmem_eq hwf5 hmem5
  have hvc31 := p.2.2.2.2.2.2.2.2.1
  simp only [PcOk] at hpc5
  obtain ⟨-, hF5⟩ := NativeRustcVmX64.Arrays.pc_cond hpc5
  have hpc5' := hF5 (by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [show m4.regs.get64 .rax = reg m4 .rax from rfl, hvc', cond31 hvc31]
    decide)
  have g5 : ∀ r w, (r, w) ∈ ([(.r13, .bin .add .W64 (.reg .rax)
      (.ite (.cmp .ult .W64 (.reg .rax) (.lit 1)) (.lit 1) (.lit 0))), (.rbp, .reg .rbp),
      (.rbx, .reg .rbx), (.r12, .reg .r12), (.r14, .reg .r14), (.r15, .reg .r15)] :
        List (Reg64 × Sym)) → reg st5.data r = w.eval (frameEnv m0 m4 608 [] (fun _ ↦ 0)
          (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b2Offset + b2.length)).toBitVec) := fun r w hr ↦ hm5'.regs r w (hr5 _ hr)
  have hk5 : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg st5.data r = reg st3.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (g5 .rbx (.reg .rbx) (by simp)).trans (hcs4 .rbx rfl)
    · exact (g5 .r12 (.reg .r12) (by simp)).trans (hcs4 .r12 rfl)
    · exact (g5 .r14 (.reg .r14) (by simp)).trans (hcs4 .r14 rfl)
    · exact (g5 .r15 (.reg .r15) (by simp)).trans (hcs4 .r15 rfl)
  refine limb0 hp h hmle hpush (st := st5) (by rw [hpc5']; rfl) ⟨fr5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk5 .rbx (by simp), g3 .rbx (.reg .rbx) (by simp)]
    exact hr2 .rbx rfl (.reg .rcx) (by simp)
  · rw [hk5 .r14 (by simp), g3 .r14 (.reg .r14) (by simp)]
    exact hr2 .r14 rfl (.reg .rdx) (by simp)
  · rw [hk5 .r15 (by simp), g3 .r15 (.reg .rax) (by simp)]; exact c0
  · rw [hk5 .r12 (by simp), g3 .r12 (.reg .rdx) (by simp)]; exact c1
  · rw [g5 .r13 (.bin .add .W64 (.reg .rax)
      (.ite (.cmp .ult .W64 (.reg .rax) (.lit 1)) (.lit 1) (.lit 0))) (by simp)]
    simp only [Sym.eval, SBool.eval, Env.ofMachine_regs]
    exact len_max hvc' hvc31
  · rw [hd5, hd4]
    exact claims_keep h hs3 (fun q hq ↦ frame_in h hq) hcl2
  · rw [hd5, hd4]; exact hpt3
  · rw [hd5, hd4]
    exact tstate_keep h hts2 (hm3.kept hwf3) hs3 fun q hq ↦ .inl (frame_in h hq)

end

end NativeRustcVmX64.Tables.PublicInputPhase
