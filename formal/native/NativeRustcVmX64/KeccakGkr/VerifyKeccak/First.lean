module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.FrontB
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Ar
public import NativeRustcVmX64.Code.Vm.FirstClaim.Names

/-!
# `verify_keccak`: the first claim (x86-64)

`b7` and `first_claim` (the `Option<KeccakClaimW>` at frame offset `992`, the claim from `1000`,
its bit weights at the scratch's start; the committed value and the weights' address the stack
arguments), `b8` (its tag: always `Some`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea TStateAt)
open NativeRustcVm.KeccakGkr (off ClaimAt WeightsAt)
open NativeRustcVm (Region)

@[expose] public section

/-- The values after the committed value's read. -/
def V1 (cm : EW) : Vs := { c0 := cm.c0.toBitVec, c1 := cm.c1.toBitVec }

end

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

/-- **`first_claim`'s footprint.** -/
theorem areas_fc (c : Ctx a inst m0) (h : LayZ m0 3344 3368 verifyKeccakStack (rsOf m0))
    {mc : MachineData} (ca : CallAt m0 wrA 16 mc) :
    Areas mc firstClaimStack [⟨off (fb m0) 992, 776⟩, ⟨off (ob m0 2) 0, 25600⟩]
      [⟨reg m0 .rdx, 16 * inst.size⟩, ⟨off (fb m0) 152, 16⟩, ⟨off (fb m0) 328, 80⟩,
        ⟨reg m0 .r8, 400⟩, ⟨off (fb m0) 24, 24⟩] := by
  have hN : 3344 - 16 + firstClaimStack ≤ verifyKeccakStack := by rw [vk_eq]; decide
  have hS := stk_callee c ca hN
  have hiM := NativeRustcVm.Transcript.Mapped.keeps c.iM ca.kept
  have hpM := NativeRustcVm.Transcript.Mapped.keeps c.pM ca.kept
  refine areas_of ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)
    · exact mapF h ca (by nd)
    · exact mapR h ca (by nd) (by nd) (by nd)
    · exact hiM
    · exact mapF h ca (by nd)
    · exact mapF h ca (by nd)
    · exact hpM
    · exact mapF h ca (by nd)
  · intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)
    · exact nwF c (by nd)
    · exact nwR c (by nd) (by nd) (by nd)
    · exact c.iW
    · exact nwF c (by nd)
    · exact nwF c (by nd)
    · exact c.pW
    · exact nwF c (by nd)
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true, false_implies, implies_true]
    exact (sepRF c (by nd) (by nd) (by nd) (by nd) (stk_frame c (by nd))).symm
  · intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact (sepSF c ca hN (by nd) (by nd) (by nd)).symm
    · exact sepRF c (by nd) (by nd) (by nd) (by nd) hS
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact sep_stk hS c.iS
    · exact sepSF c ca hN (by nd) (by nd) (by nd)
    · exact sepSF c ca hN (by nd) (by nd) (by nd)
    · exact sep_stk hS c.pS
    · exact sepSF c ca hN (by nd) (by nd) (by nd)
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact sepFX c (by nd) c.iS
    · exact sepFF c (by nd) (by nd) (by nd) (by nd) (by nd)
    · exact sepFF c (by nd) (by nd) (by nd) (by nd) (by nd)
    · exact sepFX c (by nd) c.pS
    · exact sepFF c (by nd) (by nd) (by nd) (by nd) (by nd)
    · exact sepRX c (by nd) (by nd) (by nd) (by nd) c.si
    · exact sepRF c (by nd) (by nd) (by nd) (by nd) (stk_frame c (by nd))
    · exact sepRF c (by nd) (by nd) (by nd) (by nd) (stk_frame c (by nd))
    · exact sepRX c (by nd) (by nd) (by nd) (by nd) c.spp
    · exact sepRF c (by nd) (by nd) (by nd) (by nd) (stk_frame c (by nd))

omit [Host] in
/-- An element's words loaded from the frame. -/
theorem ld_ew {d : MachineData} {rs : List (BitVec 64 × Nat)} {vals : Nat → BitVec 64}
    {ret : BitVec 64} {o : Nat} {x : EW} (h : NativeRustcVm.EWAt d.dmem (off (fb m0) o) x) :
    (envZ m0 d 3344 3368 rs vals ret).load 0 o 8 = x.c0.toBitVec ∧
      (envZ m0 d 3344 3368 rs vals ret).load 0 (o + 8) 8 = x.c1.toBitVec := by
  rw [NativeRustcVm.ewAt_iff] at h
  refine ⟨ld_frame h.1, ld_frame ?_⟩
  have e : off (fb m0) (o + 8) = off (fb m0) o + 8#64 := (NativeRustcVm.addr_add_add _ _ _).symm
  rw [e]
  exact h.2

/-- **The first claim**: at `b9` (`t9`), the claim at frame offset `1000`, its bit weights at the
scratch's start. -/
theorem firstStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hfc : ∀ inst segment lanePoint output, Spec (Labels.label NativeRustcVmX64.Vm.FirstClaim.entryLabel)
      (FirstClaimPre inst segment lanePoint output) (FirstClaimPost inst segment lanePoint output))
    {st : MachineState} {s4 : TState} {seg lp : Array EW} {cm : EW}
    (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b7Offset wrA t2 (vv m0 {}) st) (hts : TStateAt st.data.dmem (reg m0 .rdi) a s4)
    (hseg1 : seg.size = 1) (hseg : NativeRustcVm.EWsAt st.data.dmem (off (fb m0) 152) seg.toList)
    (hlp5 : lp.size = 5) (hlp : NativeRustcVm.EWsAt st.data.dmem (off (fb m0) 328) lp.toList)
    (hcm : NativeRustcVm.EWAt st.data.dmem (off (fb m0) 1000) cm) {R : MachineState → Prop}
    (cont : ∀ st', At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b9Offset wrA t9 (vv m0 (V1 cm)) st' →
      TStateAt st'.data.dmem (reg m0 .rdi) a s4 →
      ClaimAt st'.data.dmem (off (fb m0) 1000) (keccakFirstClaim inst seg lp output cm) →
      WeightsAt st'.data.dmem (off (reg m0 .r9) 0) (keccakFirstClaim inst seg lp output cm) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  obtain ⟨-, -, -, -, -, -, -, -, hisz, -, hi30, hinst, hosz, hout, -⟩ := hpre
  have hl0 : ∀ ret, (envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 {}) ret).load 0 1000 8 =
      cm.c0.toBitVec := fun ret ↦ (ld_ew hcm).1
  have hl1 : ∀ ret, (envZ m0 st.data 3344 3368 (rsOf m0) (vv m0 {}) ret).load 0 1008 8 =
      cm.c1.toBitVec := fun ret ↦ (ld_ew hcm).2
  refine stepC (T' := t8) (vals' := vv m0 (V1 cm)) hp c h hat b7_in_code (by simp [b7]) run_b7
    hat.2.mt (by decide) (oc := 16) (by decide) rfl
    (hfc inst seg lp output) (Sk := firstClaimStack) (by rw [vk_eq]; decide)
    (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_) (Lc := [(992, 776)]) (Oc := [(2, 0, 25600)])
    (fun mc m' hmc hq ↦ ?_) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl
    ?_ (fun i hi ↦ nomatch tregE (rfl : t8.reg .rax = some (.reg .rax)) hi)
    (fun i hi ↦ nomatch tregE (rfl : t8.reg .rdx = some (.reg .rdx)) hi) rfl rfl rfl
    (fun _ _ _ _ _ h ↦ by cases h) rfl fun st8 hpc8 hB8 ⟨mc, hmc, hrsp, hq, hch⟩ hc8 hk8 ↦ ?_
  · -- `first_claim`'s precondition.
    have ca : CallAt m0 wrA 16 mc := ⟨hrsp, by decide, hk, hso⟩
    have rdi : reg mc .rdi = off (fb m0) 992 := (hmc.regs .rdi _ rfl).trans (ev_frame 992)
    have rsi : reg mc .rsi = reg m0 .rdx := hmc.regs .rsi _ rfl
    have rdx : reg mc .rdx = reg m0 .rcx := hmc.regs .rdx _ rfl
    have rcx : reg mc .rcx = off (fb m0) 152 := (hmc.regs .rcx _ rfl).trans (ev_frame 152)
    have r8 : reg mc .r8 = off (fb m0) 328 := (hmc.regs .r8 _ rfl).trans (ev_frame 328)
    have r9 : reg mc .r9 = reg m0 .r8 := hmc.regs .r9 _ rfl
    have hw2 : firstWeights mc = off (ob m0 2) 0 :=
      (stackArg_of hmc rfl rfl (by decide) (i := 2) (by decide) (v := .var 11) (by decide)).trans
        (off0 _).symm
    have hch' : Chg m0 st.data.dmem mc.dmem _ [] := hch
    unfold FirstClaimPre
    dsimp only
    rw [rdi, rsi, rdx, rcx, r8, r9, hw2]
    refine ⟨hsk, argsOk c h ca (by decide), hisz, hi30, ca.instAt c hinst, by rw [hseg1]; rfl,
      Chg.ewsF c hch' (by decide) (by decide) (by rw [Array.length_toList, hseg1]; decide)
        (by rw [Array.length_toList, hseg1]; decide) hseg,
      by rw [hlp5]; rfl,
      Chg.ewsF c hch' (by decide) (by decide) (by rw [Array.length_toList, hlp5]; decide)
        (by rw [Array.length_toList, hlp5]; decide) hlp,
      hosz, ca.lanes c hosz hout, ?_, ?_⟩
    · have := areas_fc (inst := inst) c h ca
      simpa [ewsRegion, argsRegion, hseg1, hlp5, NativeRustcVm.KeccakGkr.claimBytes,
        NativeRustcVm.KeccakGkr.weightsBytes, args_eq ca] using this
    · rw [args_eq ca]
      apply ca.got c (by rw [vk_eq]; decide)
      simp only [NativeRustcVm.Transcript.DecArea.region, NativeRustcVm.KeccakGkr.claimBytes, NativeRustcVm.KeccakGkr.weightsBytes]
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp, ?_, ?_⟩
        all_goals
          dsimp only [Prod.fst, Prod.snd]
          rw [c.K, h.addr (by decide)]
          have := c.sp
          rw [vk_eq] at *
          omega
      · refine ⟨(reg m0 .r9, 205824), by simp, ?_, ?_⟩
        · change (reg m0 .r9).toNat ≤ (off (reg m0 .r9) 0).toNat
          rw [off0]
        · change (off (reg m0 .r9) 0).toNat + 25600 ≤ (reg m0 .r9).toNat + 205824
          rw [off0]
          omega
      · exact ⟨(reg m0 .rdx, 16 * inst.size), by simp, le_rfl, le_rfl⟩
      · refine ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp, ?_, ?_⟩
        all_goals
          dsimp only [Prod.fst, Prod.snd]
          rw [c.K, h.addr (by decide)]
          have := c.sp
          rw [vk_eq] at *
          omega
      · refine ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp, ?_, ?_⟩
        all_goals
          dsimp only [Prod.fst, Prod.snd]
          rw [c.K, h.addr (by decide)]
          have := c.sp
          rw [vk_eq] at *
          omega
      · exact ⟨(reg m0 .r8, 400), by simp, le_rfl, le_rfl⟩
      · refine ⟨(stackBelow m0 verifyKeccakStack, verifyKeccakStack + 8), by simp, ?_, ?_⟩
        all_goals
          dsimp only [Prod.fst, Prod.snd]
          rw [c.K, h.addr (by decide)]
          have := c.sp
          rw [vk_eq] at *
          omega
  · -- Its changes.
    have rdi : reg mc .rdi = off (fb m0) 992 := (hmc.regs .rdi _ rfl).trans (ev_frame 992)
    obtain ⟨-, -, -, hso, hsv⟩ := hq
    refine chgQ hso (fun q ⟨r, hr, hq⟩ ↦ ?_) hsv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl hq
    · exact .inr (inR_frame rdi List.mem_cons_self hq)
    · have hw2 : firstWeights mc = off (ob m0 2) 0 :=
        (stackArg_of hmc rfl rfl (by decide) (i := 2) (by decide) (v := .var 11) (by decide)).trans
          (off0 _).symm
      exact .inr (inR_reg hw2 List.mem_cons_self hq)
  · intro ret
    simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval, hl0, hl1]
    and_intros <;> first | rfl | exact fun _ h ↦ nomatch h
  -- `b8`: the tag.
  have rdi : reg mc .rdi = off (fb m0) 992 := (hmc.regs .rdi _ rfl).trans (ev_frame 992)
  have hw2 : firstWeights mc = off (ob m0 2) 0 :=
    (stackArg_of hmc rfl rfl (by decide) (i := 2) (by decide) (v := .var 11) (by decide)).trans
      (off0 _).symm
  have hcm' : firstCommitted mc = cm := by
    unfold firstCommitted ewArg
    rw [stackArg_of hmc rfl rfl (by decide) (i := 0) (by decide) (v := .load 0 1000 8) (by decide),
      stackArg_of hmc rfl rfl (by decide) (i := 1) (by decide) (v := .load 0 1008 8) (by decide)]
    simp only [Sym.eval]
    rw [hl0, hl1]
  obtain ⟨htag, hcl, hwt, -, -⟩ := hq
  rw [rdi] at htag hcl
  rw [hw2] at hwt
  rw [hcm'] at hcl hwt
  rw [NativeRustcVm.Transcript.off_off] at hcl
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b7_next] at hpc8
  refine stepJ (T' := t9) (vals' := vv m0 (V1 cm)) (o := NativeRustcVmX64.Vm.VerifyKeccak.b8Offset) hp c h ⟨hpc8, hB8⟩ b8_in_code
    (by simp [b8]) run_b8 nofun (hB8.mt 0) (by decide) rfl rfl (by vtacJ) (by decide) rfl rfl rfl
    (fun _ _ _ _ _ h ↦ by cases h) rfl fun st9 hpc9 hB9 _ hc9 hk9 ↦ ?_
  simp only [PcOk] at hpc9
  rw [tag8 (env := envZ m0 st8.data 3344 3368 (rsOf m0) (vv m0 (V1 cm)) 0) (Or.inr rfl) htag]
    at hpc9
  simp only [show ((1 : UInt64) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte] at hpc9
  have hc := hc8.trans hc9
  exact cont st9 ⟨hpc9.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b8_next]), hB9⟩
    (Chg.ts c hc (by decide) (by decide) (by decide)
      (NativeRustcVmX64.Transcript.kept_trans hk8 hk9) hts)
    (Chg.claimF c hc9 (by decide) (by decide) (by decide) (by decide) hcl)
    (Chg.wtsR c hc9 (by decide) (by decide) (by decide) (by decide) hwt)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
