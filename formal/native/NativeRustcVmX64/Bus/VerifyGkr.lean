module

public import NativeRustcVmX64.Bus.VerifyGkr.Exec
public import NativeRustcVmX64.Bus.GkrCommon
public import NativeRustcVmX64.Bus.GkrModel
public import NativeRustcVmX64.Code.Vm.GkrLayers.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.VerifyGkrGrandProducts.Names
public import NativeRustcX64.Got

/-!
# `verify_gkr_grand_products` on x86-64

`b0` pushes RBP to RBX (the 80-byte frame: the slots from `32`, `read_scalar`'s `Option<EW>` at
`8`), keeps the output in RBX, the `TState` in R12, the `GkrStateW` in R14, `depth` in R15 and
reads the shared root (`b1` its tag); `b2` keeps it in R13, RBP and reads the count (`b3` its tag);
`b4` writes the values `[shared, shared, count]` and an empty point, keeps the count in R13, RBP and
calls `gkr_layers(t, depth, s)` (`b5` its result); `b6` writes the count at the output, `b8` the tag
`1`; a failure leaves through `b7` (`fail_spec`), `b8` the tag `0`. `verifyGkr_spec`.
-/

namespace NativeRustcVmX64.Bus.VerifyGkr

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyGkrGrandProducts
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus

@[expose] public section

/-- The outputs: the `Option<EW>` (RDI), the `TState` (RSI), the `GkrStateW` (RCX). -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (reg m0 .rdi) 24 q ∨ NativeRustcVm.InRange (reg m0 .rsi) tstateBytes q ∨
    NativeRustcVm.InRange (reg m0 .rcx) gkrStateBytes q

end

public section

theorem N_ge : 80 ≤ verifyGkrStack := Nat.le_add_right _ _
theorem le_rs : 80 + readScalarStack ≤ verifyGkrStack :=
  Nat.add_le_add_left (Nat.le_max_left _ _) _
theorem le_gl : 80 + gkrLayersStack ≤ verifyGkrStack :=
  Nat.add_le_add_left (Nat.le_max_right _ _) _
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 80 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_call : ∀ p ∈ slots, 0 ≤ p.1 ∧ 8 + 24 ≤ p.1 ∧ p.1 + 8 ≤ 80 := by decide

section
variable [Labels] {a : DecArea} {s0 : TState} {m0 : MachineData}

theorem pre_out (h : VerifyGkrPre a s0 m0) :
    OutOk m0 (reg m0 .rsi) a (reg m0 .rdi) 24 verifyGkrStack := h.2.2.2.2.2.1
theorem pre_gk (h : VerifyGkrPre a s0 m0) :
    OutOk m0 (reg m0 .rsi) a (reg m0 .rcx) gkrStateBytes verifyGkrStack := h.2.2.2.2.2.2.1

theorem pre_got (h : VerifyGkrPre a s0 m0) :
    GotAt m0 verifyGkrStack [(reg m0 .rsi, tstateBytes), (a.words, 8 * a.len),
      (reg m0 .rdi, 24), (reg m0 .rcx, gkrStateBytes), (rcAddr, 192)] ["memcpy"] :=
  h.2.2.2.2.2.2.2.2

theorem got_pass (h : VerifyGkrPre a s0 m0) {d : MachineData}
    (fr : Fr m0 80 verifyGkrStack slots (outs m0) 0 d) {n : Nat}
    (hn : 80 + n ≤ verifyGkrStack) {areas : List (BitVec 64 × Nat)}
    (ha : ∀ l ∈ ["memcpy"], ∀ b ∈ areas, Apart (gotAddr l) 8 b.1 b.2) :
    GotAt d n areas ["memcpy"] := by
  refine got_callee (pre_got h) ?_ (by rw [fr.frame.sp, off_zero]) h.1.1 hn ha
  refine got_keep (pre_got h) h.1
    (writes := [(reg m0 .rdi, 24), (reg m0 .rsi, tstateBytes), (reg m0 .rcx, gkrStateBytes)])
    (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> simp)
    (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact (pre_out h).2.1
      · exact h.2.2.1.footprint.1.2
      · exact (pre_gk h).2.1)
    (NativeRustcVm.SameOutside.mono fr.same ?_)
  intro q hq
  rcases hq with hq | hq | hq | hq
  · exact .inr hq
  · exact .inl ⟨(reg m0 .rdi, 24), by simp, hq⟩
  · exact .inl ⟨(reg m0 .rsi, tstateBytes), by simp, hq⟩
  · exact .inl ⟨(reg m0 .rcx, gkrStateBytes), by simp, hq⟩

/-- The entry's context. -/
theorem ctx (h : VerifyGkrPre a s0 m0) : Ctx m0 (reg m0 .rsi) a verifyGkrStack 80 :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1.footprint, N_ge⟩

theorem outs_not_rc (h : VerifyGkrPre a s0 m0) :
    ∀ q, outs m0 q → ¬ NativeRustcVm.InRange rcAddr 192 q := by
  intro q hq
  have c := ctx h
  rcases hq with hq | hq | hq
  · exact c.out_not_rc (pre_out h) hq
  · exact c.not_rc_tstate hq
  · exact c.out_not_rc (pre_gk h) hq

theorem outs_not_frame (h : VerifyGkrPre a s0 m0) :
    ∀ q, outs m0 q → ¬ NativeRustcVm.InRange (stackBelow m0 80) (80 + 8) q := by
  intro q hq
  have c := ctx h
  rcases hq with hq | hq | hq
  · exact not_inRange_of_apart (apart_frame (pre_out h).2.2.2.2.1 c.spN N_ge) (pre_out h).2.1
      c.noWrap_frame hq
  · exact not_inRange_of_apart (apart_frame c.tok.1 c.spN N_ge) c.fp.1.2 c.noWrap_frame hq
  · exact not_inRange_of_apart (apart_frame (pre_gk h).2.2.2.2.1 c.spN N_ge) (pre_gk h).2.1
      c.noWrap_frame hq

/-- The `TState` kept where the memory changed in the stack, the output or the `GkrStateW`. -/
theorem ts_keep (h : VerifyGkrPre a s0 m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hk : Kept d d') (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 verifyGkrStack) verifyGkrStack q ∨
      NativeRustcVm.InRange (reg m0 .rdi) 24 q ∨ NativeRustcVm.InRange (reg m0 .rcx) gkrStateBytes q)
    {s : TState} (ht : TStateAt d (reg m0 .rsi) a s) : TStateAt d' (reg m0 .rsi) a s := by
  have c := ctx h
  refine ht.frame hk (fun q hq ↦ ?_) hs
  rcases hR q hq with hq | hq | hq
  · exact c.stack_not_t hq
  · exact c.out_not_t (pre_out h) hq
  · exact c.out_not_t (pre_gk h) hq

/-- The frame's environment with the output as region 1 is well formed. -/
theorem wf_o (h : VerifyGkrPre a s0 m0) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (ret : BitVec 64) :
    (frameEnv m0 d 80 [(reg m0 .rdi, 24)] (fun _ ↦ 0) ret).WF := by
  have c := ctx h
  refine frame_wf ⟨c.mapped_frame hk, c.noWrap_frame⟩ (fun x hx ↦ ?_)
    (List.pairwise_pair.mpr (Apart.symm' (apart_frame (pre_out h).2.2.2.2.1 c.spN N_ge)))
  rw [List.mem_singleton] at hx
  subst hx
  exact ⟨Mapped.keeps (pre_out h).1 hk, (pre_out h).2.1⟩

/-- The frame's environment with the `GkrStateW` as region 1 is well formed. -/
theorem wf_p (h : VerifyGkrPre a s0 m0) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (ret : BitVec 64) :
    (frameEnv m0 d 80 [(reg m0 .rcx, 1064)] (fun _ ↦ 0) ret).WF := by
  have c := ctx h
  refine frame_wf ⟨c.mapped_frame hk, c.noWrap_frame⟩ (fun x hx ↦ ?_)
    (List.pairwise_pair.mpr (Apart.symm' (apart_frame (pre_gk h).2.2.2.2.1 c.spN N_ge)))
  rw [List.mem_singleton] at hx
  subst hx
  exact ⟨Mapped.keeps (pre_gk h).1 hk, (pre_gk h).2.1⟩

theorem wf_0 (h : VerifyGkrPre a s0 m0) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (ret : BitVec 64) : (frameEnv m0 d 80 [] (fun _ ↦ 0) ret).WF := by
  have c := ctx h
  exact frame_wf ⟨c.mapped_frame hk, c.noWrap_frame⟩ (by simp) (List.pairwise_singleton _ _)

/-- The registers `b0` sets and every later block and call keeps. -/
structure Regs (m0 d : MachineData) : Prop where
  rbx : reg d .rbx = reg m0 .rdi
  r12 : reg d .r12 = reg m0 .rsi
  r14 : reg d .r14 = reg m0 .rcx
  r15 : reg d .r15 = reg m0 .rdx

omit [Labels] in
theorem Regs.call {d d' : MachineData} (hr : Regs m0 d)
    (h : ∀ r, calleeSaved r = true → d'.regs.get64 r = d.regs.get64 r) : Regs m0 d' :=
  ⟨(h .rbx rfl).trans hr.rbx, (h .r12 rfl).trans hr.r12, (h .r14 rfl).trans hr.r14,
    (h .r15 rfl).trans hr.r15⟩

theorem Regs.block {d d' : MachineData} {env : Env} {S : SState} (hr : Regs m0 d)
    (henv : ∀ r, env.regs r = d.regs.get64 r) (hm : Match env S d')
    (hk : Keeps S [.rbx, .r12, .r14, .r15] = true) : Regs m0 d' := by
  simp only [Keeps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hk
  obtain ⟨h1, h2, h3, h4⟩ := hk
  exact ⟨((hm.regs _ _ h1).trans (henv _)).trans hr.rbx, ((hm.regs _ _ h2).trans (henv _)).trans hr.r12,
    ((hm.regs _ _ h3).trans (henv _)).trans hr.r14, ((hm.regs _ _ h4).trans (henv _)).trans hr.r15⟩

end

section
variable [Host] {a : DecArea} {s0 : TState} {m0 : MachineData} {k : Nat}

/-- What `verify_gkr_grand_products` reaches. -/
abbrev Goal (a : DecArea) (s0 : TState) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ VerifyGkrPost a s0 m0 st.data

/-- **A failure** (`NativeRustcVmX64.Vm.VerifyGkrGrandProducts.label_5`, `b7`, `b8`): the tag `0` at the output. -/
theorem fail_spec (hp : Placed code k) (h : VerifyGkrPre a s0 m0) {d : MachineData}
    (fr : Fr m0 80 verifyGkrStack slots (outs m0) 8 d) (hr : Regs m0 d)
    (hrun : (verifyGkrGrandProducts (reg m0 .rdx).toNat).run s0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b7Offset)⟩ := by
  have hwf := wf_o h fr.frame.kept 0
  have hm : Match (frameEnv m0 d 80 [(reg m0 .rdi, 24)] (fun _ ↦ 0) 0) oS d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨fr.frame.rsp_eval, known_ptr rfl hr.rbx, trivial⟩
      trivial trivial trivial
  refine exec_then (infix_of b7_in_code (by simp [b7]) hp) exit_b7 hwf nofun hm
    fun st hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  obtain ⟨hend, hw0⟩ := ok_b8f
  simp only [EndOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hend
  obtain ⟨⟨hepi, -⟩, hws⟩ := hend
  refine fr.exit h.1 N_ge (infix_of b8_in_code (by simp [b8]) hp) exit_b8f hwf
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b7_next)) hm1 hepi (fun q hw ↦ ?_)
    fun st' hm' hpc' hrsp' hsame _ hsv ↦ .done _ ⟨hpc', hrsp', ?_, ?_, ?_, hsv⟩
  · obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hw
    obtain ⟨hr1, hle⟩ := hws w hw
    rw [hr1] at hb
    cases hb
    refine .inl ?_
    rw [inRange_toNat (pre_out h).2.1]
    omega
  · rw [hrun]
    have := wordAt_write hm' (r := 1) (o := 0) rfl (by decide) hw0
    rwa [off_zero] at this
  · intro _ _ _ _ he
    rw [hrun] at he
    cases he
  · exact NativeRustcVm.SameOutside.mono hsame fun q hq ↦ by
      rcases hq with hq | hq | hq | hq
      · exact .inr (.inr (.inr hq))
      · exact .inl hq
      · exact .inr (.inl hq)
      · exact .inr (.inr (.inl hq))

/-- A state of the body (`headS`) in the frame's environment. -/
theorem match_head {d : MachineData} {o : Nat} (fr : Fr m0 80 verifyGkrStack slots (outs m0) o d)
    (hk : o = 8) (ret : BitVec 64) :
    Match (frameEnv m0 d 80 [] (fun _ ↦ 0) ret) headS d := by
  subst hk
  exact match_ofMachine ⟨rfl, trivial⟩ ⟨fr.frame.rsp_eval, trivial⟩ trivial trivial trivial

/-- **After `gkr_layers`** (`b5`, then `b6`, `b8`): the count at the output, the tag `1`. -/
theorem tail_spec (hp : Placed code k) (h : VerifyGkrPre a s0 m0) {d : MachineData}
    (fr : Fr m0 80 verifyGkrStack slots (outs m0) 8 d) (hr : Regs m0 d) {y : EW}
    (h13 : reg d .r13 = y.c0.toBitVec) (hbp : reg d .rbp = y.c1.toBitVec)
    {rL : Option (GkrStateW × TState)} (hal : OkAl d rL.isSome)
    (hok : ∀ g' s', rL = some (g', s') → TStateAt d.dmem (reg m0 .rsi) a s' ∧
      GkrStateWAt d.dmem (reg m0 .rcx) g')
    (hrun : (verifyGkrGrandProducts (reg m0 .rdx).toNat).run s0 =
      rL.bind fun z ↦ some ((y, z.1.point, z.1.values), z.2)) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b5Offset)⟩ := by
  have hwf := wf_0 h fr.frame.kept 0
  refine exec_then (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf nofun
    (match_head fr rfl 0) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hmem5, hk5⟩ := ok_b5
  have fr5 := (fr.block0 h.1 N_ge hwf hm5 hmid5 slots_le (by simp [hmem5])).1
  have hd5 : st5.data.dmem = d.dmem := hm5.dmem_eq hwf hmem5
  simp only [Keeps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hk5
  have hr5 : Regs m0 st5.data :=
    ⟨(hm5.regs _ _ hk5.1).trans hr.rbx, (hm5.regs _ _ hk5.2.2.1).trans hr.r12,
      (hm5.regs _ _ hk5.2.2.2.2.1).trans hr.r14, (hm5.regs _ _ hk5.2.2.2.2.2).trans hr.r15⟩
  have e13 : reg st5.data .r13 = y.c0.toBitVec := (hm5.regs _ _ hk5.2.2.2.1).trans h13
  have ebp : reg st5.data .rbp = y.c1.toBitVec := (hm5.regs _ _ hk5.2.1).trans hbp
  simp only [PcOk] at hpc5
  have hc : SBool.eval (frameEnv m0 d 80 [] (fun _ ↦ 0) 0)
      (.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)) = !rL.isSome :=
    testAl_okAl hal
  rw [hc] at hpc5
  cases hrl : rL with
  | none =>
    simp only [hrl, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc5
    exact at_pc (hpc5.trans (hp.label NativeRustcVmX64.Vm.VerifyGkrGrandProducts.label_5_at))
      (fail_spec hp h fr5 hr5 (by rw [hrun, hrl]; rfl))
  | some z =>
    simp only [hrl, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc5
    obtain ⟨hts, hgs⟩ := hok z.1 z.2 (by rw [hrl])
    have hwf6 := wf_o h fr5.frame.kept 0
    have hm6 : Match (frameEnv m0 st5.data 80 [(reg m0 .rdi, 24)] (fun _ ↦ 0) 0) oS st5.data :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨fr5.frame.rsp_eval, known_ptr rfl hr5.rbx, trivial⟩
        trivial trivial trivial
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf6 nofun
      (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b5_next)) hm6 fun st6 hm6' hpc6 ↦ ?_
    simp only [PcOk] at hpc6
    obtain ⟨hend, hw0, hw8, hw16⟩ := ok_b8s
    simp only [EndOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hend
    obtain ⟨⟨hepi, -⟩, hws⟩ := hend
    have hwo : ∀ q, Written (frameEnv m0 st5.data 80 [(reg m0 .rdi, 24)] (fun _ ↦ 0) 0)
        (after b8 (after b6 oS)) q → NativeRustcVm.InRange (reg m0 .rdi) 24 q := by
      intro q hw
      obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hw
      obtain ⟨hr1, hle⟩ := hws w hw
      rw [hr1] at hb
      cases hb
      rw [inRange_toNat (pre_out h).2.1]
      omega
    refine fr5.exit h.1 N_ge (infix_of b8_in_code (by simp [b8]) hp) exit_b8s hwf6
      (hpc6.trans (hp.label NativeRustcVmX64.Vm.VerifyGkrGrandProducts.label_6_at)) hm6' hepi (fun q hw ↦ .inl (hwo q hw))
      fun st' hm' hpc' hrsp' hsame hso hsv ↦ .done _ ⟨hpc', hrsp', ?_, ?_, ?_, hsv⟩
    · rw [hrun, hrl]
      refine ⟨?_, ?_⟩
      · have := wordAt_write hm' (r := 1) (o := 0) rfl (by decide) hw0
        rwa [off_zero] at this
      · refine ewAt_iff.mpr ⟨?_, ?_⟩
        · have := wordAt_write hm' (r := 1) (o := 8) rfl (by decide) hw8
          rwa [show (Sym.reg .r13).eval (frameEnv m0 st5.data 80 [(reg m0 .rdi, 24)]
            (fun _ ↦ 0) 0) = y.c0.toBitVec from e13, UInt64.ofBitVec_toBitVec] at this
        · have := wordAt_write hm' (r := 1) (o := 16) rfl (by decide) hw16
          rw [show (Sym.reg .rbp).eval (frameEnv m0 st5.data 80 [(reg m0 .rdi, 24)]
            (fun _ ↦ 0) 0) = y.c1.toBitVec from ebp, UInt64.ofBitVec_toBitVec] at this
          rw [off_off]
          exact this
    · intro c pt vs s' he
      rw [hrun, hrl] at he
      simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := he
      have hso' : NativeRustcVm.SameOutside st5.data.dmem st'.data.dmem
          (NativeRustcVm.InRange (reg m0 .rdi) 24) :=
        fun q hq ↦ hm'.get?_mem0 hwf6 fun hw ↦ hq (hwo q hw)
      rw [← hd5] at hts hgs
      exact ⟨ts_keep h (hm'.kept hwf6) hso' (fun q hq ↦ .inr (.inl hq)) hts,
        gkrStateWAt_keep hgs hso' fun q hq ↦
          not_inRange_of_apart h.2.2.2.2.2.2.2.1 (pre_out h).2.1 (pre_gk h).2.1 hq⟩
    · exact NativeRustcVm.SameOutside.mono hsame fun q hq ↦ by
        rcases hq with hq | hq | hq | hq
        · exact .inr (.inr (.inr hq))
        · exact .inl hq
        · exact .inr (.inl hq)
        · exact .inr (.inr (.inl hq))

/-- `read_scalar(frame + 8, t)`'s precondition, at a call from the frame. -/
theorem rs_pre (h : VerifyGkrPre a s0 m0) {d : MachineData} (hat : At m0 80 d)
    (fr : Fr m0 80 verifyGkrStack slots (outs m0) 0 d)
    (hsi : reg d .rsi = reg m0 .rsi) (hdi : reg d .rdi = off (stackBelow m0 80) 8) {s : TState}
    (hts : TStateAt d.dmem (reg m0 .rsi) a s) : ReadScalarPre a s d := by
  have c := ctx h
  unfold ReadScalarPre
  rw [hsi, hdi]
  refine ⟨c.stackOk hat le_rs, c.rcAt hat le_rs, hts, c.tstateOk hat le_rs,
    c.outOk_frame hat le_rs (o := 8) (n := 24) (by omega) (by omega), got_pass h fr le_rs ?_⟩
  intro l hl b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
  · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)
  · exact got_apart_frame (pre_got h) h.1 hl N_ge (by omega)
  · exact ((pre_got h).1 l hl).2.2.2 _ (by simp)

/-- **`read_scalar(frame + 8, t)`** from the frame at a call. -/
theorem rs_call (h : VerifyGkrPre a s0 m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (fr : Fr m0 80 verifyGkrStack slots (outs m0) 0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel ∧ retOf st.data = next)
    (hsi : reg st.data .rsi = reg m0 .rsi) (hdi : reg st.data .rdi = off (stackBelow m0 80) 8)
    {s : TState} (hts : TStateAt st.data.dmem (reg m0 .rsi) a s)
    (cont : ∀ m2 : MachineData, Fr m0 80 verifyGkrStack slots (outs m0) 8 m2 →
      OptEWAt m2.dmem (off (stackBelow m0 80) 8) ((readScalar.run s).map (·.1)) →
      NextAt m2.dmem (reg m0 .rsi) a (readScalar.run s) →
      (∀ r, calleeSaved r = true → m2.regs.get64 r = st.data.regs.get64 r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have c := ctx h
  have hat : At m0 80 st.data := fr.at_ c (by omega) (outs_not_rc h)
  refine fr.call (c := 0) (Nc := readScalarStack) (lo := 8) (len := 24)
    (X := fun q ↦ NativeRustcVm.InRange (off (stackBelow m0 80) 8) 24 q ∨
      NativeRustcVm.InRange (reg m0 .rsi) tstateBytes q)
    h.1 N_ge (by omega) le_rs slots_call (by omega) (outs_not_frame h)
    (fun q hq ↦ hq.elim .inr fun hq ↦ .inl (.inr (.inl hq))) (hrs s) hpc
    (rs_pre h hat fr hsi hdi hts) (fun m' hq ↦ ⟨?_, hq.2.2.2⟩) fun m2 fr2 hq _ hcs ↦ ?_
  · have := hq.2.2.1
    rw [hsi, hdi] at this
    exact NativeRustcVm.SameOutside.mono this fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr (.inl hq)
      · exact .inr (.inr hq)
      · exact .inl hq
  · obtain ⟨hout, hnext, -, -⟩ := hq
    rw [hdi] at hout
    rw [hsi] at hnext
    exact cont m2 fr2 hout hnext hcs

omit [Host] in
/-- Three elements by their words. -/
theorem ews3 {d : Mem 64} {p : BitVec 64} {x y z : EW}
    (h0 : NativeRustcVm.WordAt d (off p 0) x.c0) (h1 : NativeRustcVm.WordAt d (off p 8) x.c1)
    (h2 : NativeRustcVm.WordAt d (off p 16) y.c0) (h3 : NativeRustcVm.WordAt d (off p 24) y.c1)
    (h4 : NativeRustcVm.WordAt d (off p 32) z.c0) (h5 : NativeRustcVm.WordAt d (off p 40) z.c1) :
    NativeRustcVm.EWsAt d p [x, y, z] := by
  rw [off_zero] at h0
  refine ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨h0, h1⟩, ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨?_, ?_⟩,
    ewsAt_cons.mpr ⟨ewAt_iff.mpr ⟨?_, ?_⟩, ewsAt_nil _ _⟩⟩⟩
  · exact h2
  · rw [off_off]; exact h3
  · rw [off_off]; exact h4
  · rw [off_off, off_off]; exact h5

/-- **`verify_gkr_grand_products`'s contract.** -/
theorem verifyGkr_spec (hp : Placed code k)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hgl : ∀ s g, Spec (Labels.label NativeRustcVmX64.Vm.GkrLayers.entryLabel) (GkrLayersPre a s g)
      (GkrLayersPost a s g)) :
    Spec (Labels.label NativeRustcVmX64.Vm.VerifyGkrGrandProducts.entryLabel) (VerifyGkrPre a s0) (VerifyGkrPost a s0) := by
  intro m0 h
  have c := ctx h
  have hS := h.1
  have hts0 := h.2.2.1
  set fb := stackBelow m0 80 with hfb
  set t := reg m0 .rsi with ht
  unfold NativeRustcVmX64.Vm.VerifyGkrGrandProducts.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.VerifyGkrGrandProducts.entry_at]
  -- `b0`: the prologue, `read_scalar(frame + 8, t)`.
  have hwf0 := wf_0 h (d := m0) (fun _ h ↦ h) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b0Offset + b0.length)).toBitVec
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 (fun _ _ ↦ rfl)
    (match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hw1, hdi1, hsi1, hbx1, h121, h141, h151⟩ := ok_b0
  have hw1' : ∀ w ∈ (after b0 entryS).mem, w.r = 0 := fun w hw ↦ (hw1 w hw).1
  have fr1 : Fr m0 80 verifyGkrStack slots (outs m0) 0 st1.data :=
    Fr.of_prologue hS N_ge hwf0 hm1 hpro slots_le slots_cs hw1'
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange fb 80) :=
    fun q hq ↦ hm1.get?_mem0 hwf0 fun hw ↦ hq (written_fb hS N_ge (fun w hw ↦ ⟨hw1' w hw,
      belowRet_spec (belowRet_of_pro hpro) w hw (hw1' w hw)⟩) hw)
  have hreg1 : Regs m0 st1.data :=
    ⟨hm1.regs _ _ hbx1, hm1.regs _ _ h121, hm1.regs _ _ h141, hm1.regs _ _ h151⟩
  have hts1 : TStateAt st1.data.dmem t a s0 :=
    hts0.frame (hm1.kept hwf0) (fun q hq ↦ c.stack_not_t (c.inRange_frame hq)) hs1
  refine rs_call h hrs fr1 hpc1 (hm1.regs _ _ hsi1) ((hm1.regs _ _ hdi1).trans (eval_ptr0 8))
    hts1 fun m2 fr2 hout2 hnext2 hcs2 ↦ ?_
  have hreg2 := hreg1.call hcs2
  -- `b1`: the shared root's tag.
  have hwf2 := wf_0 h fr2.frame.kept 0
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf2 nofun
    (by show Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b0Offset + b0.length) = _; rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b0_next)
    (match_head fr2 rfl 0) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hk3⟩ := ok_b1
  have fr3 := (fr2.block0 hS N_ge hwf2 hm3 hmid3 slots_le (by simp [hmem3])).1
  have hd3 : st3.data.dmem = m2.dmem := hm3.dmem_eq hwf2 hmem3
  have hreg3 : Regs m0 st3.data := hreg2.block (fun _ ↦ rfl) hm3 hk3
  simp only [PcOk] at hpc3
  sym_simp_at hpc3
  have hrun := verifyGkr_run (reg m0 .rdx).toNat s0
  cases hr1 : readScalar.run s0 with
  | none =>
    rw [hr1] at hout2
    have hl : (frameEnv m0 m2 80 [] (fun _ ↦ 0) 0).load 0 8 4 = BitVec.ofNat 64 0 :=
      load4_of_tag (Or.inl rfl) hout2
    simp only [hl] at hpc3
    simp (config := { decide := true }) only [↓reduceIte] at hpc3
    exact at_pc (hpc3.trans (hp.label NativeRustcVmX64.Vm.VerifyGkrGrandProducts.label_5_at))
      (fail_spec hp h fr3 hreg3 (by rw [hrun, hr1]; rfl))
  | some p1 =>
  obtain ⟨sh, s1⟩ := p1
  rw [hr1] at hout2 hnext2
  obtain ⟨ht1, hel1⟩ := (hout2 : OptEWAt m2.dmem (off fb 8) (some sh))
  rw [ewAt_iff, off_off, off_off] at hel1
  have hts2 : TStateAt m2.dmem t a s1 := hnext2 sh s1 rfl
  have hl : (frameEnv m0 m2 80 [] (fun _ ↦ 0) 0).load 0 8 4 = BitVec.ofNat 64 1 :=
    load4_of_tag (Or.inr rfl) ht1
  simp only [hl] at hpc3
  simp (config := { decide := true }) only [↓reduceIte] at hpc3
  -- `b2`: the shared root kept in R13, RBP; `read_scalar(frame + 8, t)`.
  have hwf3 := wf_0 h fr3.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b2Offset + b2.length)).toBitVec
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf3 (fun _ _ ↦ rfl)
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b1_next)) (match_head fr3 rfl _)
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hw4, hdi4, hsi4, h134, hbp4, hk4⟩ := ok_b2
  have hw4' : ∀ w ∈ (after b2 headS).mem, w.r = 0 := fun w hw ↦ (hw4 w hw).1
  obtain ⟨fr4, hs4⟩ := fr3.block0 hS N_ge hwf3 hm4 hmid4 slots_le hw4'
  have hreg4 : Regs m0 st4.data := hreg3.block (fun _ ↦ rfl) hm4 (by
    simp only [Keeps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hk4 ⊢
    exact hk4)
  have e134 : reg st4.data .r13 = sh.c0.toBitVec :=
    (hm4.regs _ _ h134).trans (load_ofMachine (o := 16) rfl (hd3 ▸ hel1.1))
  have ebp4 : reg st4.data .rbp = sh.c1.toBitVec :=
    (hm4.regs _ _ hbp4).trans (load_ofMachine (o := 24) rfl (hd3 ▸ hel1.2))
  have hts4 : TStateAt st4.data.dmem t a s1 :=
    (hd3 ▸ hts2).frame (hm4.kept hwf3) (fun q hq ↦ c.stack_not_t (c.inRange_frame hq)) hs4
  refine rs_call h hrs fr4 hpc4 ((hm4.regs _ _ hsi4).trans hreg3.r12)
    ((hm4.regs _ _ hdi4).trans (eval_ptr0 8)) hts4 fun m5 fr5 hout5 hnext5 hcs5 ↦ ?_
  have hreg5 := hreg4.call hcs5
  have e135 : reg m5 .r13 = sh.c0.toBitVec := (hcs5 .r13 rfl).trans e134
  have ebp5 : reg m5 .rbp = sh.c1.toBitVec := (hcs5 .rbp rfl).trans ebp4
  -- `b3`: the count's tag.
  have hwf5 := wf_0 h fr5.frame.kept 0
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf5 nofun
    (by show Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b2Offset + b2.length) = _; rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b2_next)
    (match_head fr5 rfl 0) fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hmid6, hmem6, hk6⟩ := ok_b3
  have fr6 := (fr5.block0 hS N_ge hwf5 hm6 hmid6 slots_le (by simp [hmem6])).1
  have hd6 : st6.data.dmem = m5.dmem := hm6.dmem_eq hwf5 hmem6
  simp only [Keeps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hk6
  have hreg6 : Regs m0 st6.data :=
    ⟨(hm6.regs _ _ hk6.1).trans hreg5.rbx, (hm6.regs _ _ hk6.2.2.1).trans hreg5.r12,
      (hm6.regs _ _ hk6.2.2.2.2.1).trans hreg5.r14, (hm6.regs _ _ hk6.2.2.2.2.2).trans hreg5.r15⟩
  have e136 : reg st6.data .r13 = sh.c0.toBitVec := (hm6.regs _ _ hk6.2.2.2.1).trans e135
  have ebp6 : reg st6.data .rbp = sh.c1.toBitVec := (hm6.regs _ _ hk6.2.1).trans ebp5
  simp only [PcOk] at hpc6
  sym_simp_at hpc6
  cases hr2 : readScalar.run s1 with
  | none =>
    rw [hr2] at hout5
    have hl : (frameEnv m0 m5 80 [] (fun _ ↦ 0) 0).load 0 8 1 = BitVec.ofNat 64 0 :=
      load1_of_tag (Or.inl rfl) hout5
    simp only [hl] at hpc6
    simp (config := { decide := true }) only [↓reduceIte] at hpc6
    exact at_pc (hpc6.trans (hp.label NativeRustcVmX64.Vm.VerifyGkrGrandProducts.label_5_at))
      (fail_spec hp h fr6 hreg6 (by rw [hrun, hr1]; simp only [Option.bind_some, hr2]; rfl))
  | some p2 =>
  obtain ⟨cnt, s2⟩ := p2
  rw [hr2] at hout5 hnext5
  obtain ⟨ht2, hel2⟩ := (hout5 : OptEWAt m5.dmem (off fb 8) (some cnt))
  rw [ewAt_iff, off_off, off_off] at hel2
  have hts5 : TStateAt m5.dmem t a s2 := hnext5 cnt s2 rfl
  have hl : (frameEnv m0 m5 80 [] (fun _ ↦ 0) 0).load 0 8 1 = BitVec.ofNat 64 1 :=
    load1_of_tag (Or.inr rfl) ht2
  simp only [hl] at hpc6
  simp (config := { decide := true }) only [↓reduceIte] at hpc6
  -- `b4`: the `GkrStateW`'s values and empty point; `gkr_layers(t, depth, s)`.
  have hwf6 := wf_p h fr6.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b4Offset + b4.length)).toBitVec
  have hm6' : Match (frameEnv m0 st6.data 80 [(reg m0 .rcx, 1064)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b4Offset + b4.length)).toBitVec) sS st6.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨fr6.frame.rsp_eval, known_ptr rfl hreg6.r14, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf6 (fun _ _ ↦ rfl)
    (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b3_next)) hm6' fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hws7, hv0, hv8, hv16, hv24, hv32, hv40, hv48, hdi7, hsi7, hdx7, h137, hbp7,
    h147, hk7⟩ := ok_b4
  have hgsb : gkrStateBytes = 1064 := rfl
  have hW7 : ∀ q, Written (frameEnv m0 st6.data 80 [(reg m0 .rcx, 1064)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b4Offset + b4.length)).toBitVec) (after b4 sS) q →
      NativeRustcVm.InRange fb 80 q ∨ NativeRustcVm.InRange (reg m0 .rcx) gkrStateBytes q :=
    fun q hw ↦ written_fb1 hS N_ge (fun w hw ↦ (hws7 w hw).imp (fun h ↦ ⟨h.1, by omega⟩)
      (fun h ↦ ⟨h.1, by omega⟩)) (by have := (pre_gk h).2.1; rw [hgsb] at this; exact this) hw
  obtain ⟨fr7, hs7⟩ := fr6.block hS N_ge hwf6 hm7 hmid7 slots_le fun q hw ↦
    (hW7 q hw).imp id fun hq ↦ .inr (.inr hq)
  simp only [Keeps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hk7
  have e147 : reg st7.data .r14 = reg m0 .rcx := (hm7.regs _ _ h147).trans (eval_ptr rfl)
  have hreg7 : Regs m0 st7.data :=
    ⟨(hm7.regs _ _ hk7.1).trans hreg6.rbx, (hm7.regs _ _ hk7.2.1).trans hreg6.r12, e147,
      (hm7.regs _ _ hk7.2.2).trans hreg6.r15⟩
  -- the state `gkr_layers` starts from
  have hs7' : NativeRustcVm.SameOutside st6.data.dmem st7.data.dmem (fun q ↦
      NativeRustcVm.InRange fb 80 q ∨ NativeRustcVm.InRange (reg m0 .rcx) gkrStateBytes q) :=
    fun q hq ↦ hm7.get?_mem0 hwf6 fun hw ↦ hq (hW7 q hw)
  have hts7 : TStateAt st7.data.dmem t a s2 :=
    (hd6 ▸ hts5).frame (hm7.kept hwf6) (fun q (hq : NativeRustcVm.InRange fb 80 q ∨
      NativeRustcVm.InRange (reg m0 .rcx) gkrStateBytes q) ↦ hq.elim
      (fun hq ↦ c.stack_not_t (c.inRange_frame hq)) (fun hq ↦ c.out_not_t (pre_gk h) hq)) hs7'
  have hld16 : (Sym.load 0 16 8).eval (frameEnv m0 st6.data 80 [(reg m0 .rcx, 1064)]
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b4Offset + b4.length)).toBitVec) = cnt.c0.toBitVec :=
    load_ofMachine (o := 16) rfl (hd6 ▸ hel2.1)
  have hld24 : (Sym.load 0 24 8).eval (frameEnv m0 st6.data 80 [(reg m0 .rcx, 1064)]
      (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b4Offset + b4.length)).toBitVec) = cnt.c1.toBitVec :=
    load_ofMachine (o := 24) rfl (hd6 ▸ hel2.2)
  have w0 := wordAt_write hm7 (r := 1) (o := 0) rfl (by decide) hv0
  have w8 := wordAt_write hm7 (r := 1) (o := 8) rfl (by decide) hv8
  have w16 := wordAt_write hm7 (r := 1) (o := 16) rfl (by decide) hv16
  have w24 := wordAt_write hm7 (r := 1) (o := 24) rfl (by decide) hv24
  have w32 := wordAt_write hm7 (r := 1) (o := 32) rfl (by decide) hv32
  have w40 := wordAt_write hm7 (r := 1) (o := 40) rfl (by decide) hv40
  have w48 := wordAt_write hm7 (r := 1) (o := 48) rfl (by decide) hv48
  rw [show (Sym.reg .r13).eval (frameEnv m0 st6.data 80 [(reg m0 .rcx, 1064)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b4Offset + b4.length)).toBitVec) = sh.c0.toBitVec from e136,
    UInt64.ofBitVec_toBitVec] at w0 w16
  rw [show (Sym.reg .rbp).eval (frameEnv m0 st6.data 80 [(reg m0 .rcx, 1064)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b4Offset + b4.length)).toBitVec) = sh.c1.toBitVec from ebp6,
    UInt64.ofBitVec_toBitVec] at w8 w24
  rw [hld16, UInt64.ofBitVec_toBitVec] at w32
  rw [hld24, UInt64.ofBitVec_toBitVec] at w40
  have hgs7 : GkrStateWAt st7.data.dmem (reg m0 .rcx) ⟨#[sh, sh, cnt], #[]⟩ :=
    ⟨rfl, ews3 w0 w8 w16 w24 w32 w40, ⟨Nat.zero_le _, w48, ewsAt_nil _ _⟩⟩
  have hat7 : At m0 80 st7.data := fr7.at_ c (by omega) (outs_not_rc h)
  have edi7 : reg st7.data .rdi = t := (hm7.regs _ _ hdi7).trans hreg6.r12
  have esi7 : reg st7.data .rsi = reg m0 .rdx := (hm7.regs _ _ hsi7).trans hreg6.r15
  have edx7 : reg st7.data .rdx = reg m0 .rcx := (hm7.regs _ _ hdx7).trans (eval_ptr rfl)
  have hpre7 : GkrLayersPre a s2 ⟨#[sh, sh, cnt], #[]⟩ st7.data := by
    unfold GkrLayersPre GkrOk
    rw [edi7, esi7, edx7]
    refine ⟨c.stackOk hat7 le_gl, c.rcAt hat7 le_gl, hts7, c.tstateOk hat7 le_gl,
      by simpa using h.2.2.2.2.1, c.outOk hat7 le_gl (pre_gk h), hgs7, got_pass h fr7 le_gl ?_⟩
    intro l hl b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · rw [ht]
      exact ((pre_got h).1 l hl).2.2.2 (reg m0 .rsi, tstateBytes) (by simp)
    · exact ((pre_got h).1 l hl).2.2.2 (a.words, 8 * a.len) (by simp)
    · exact ((pre_got h).1 l hl).2.2.2 (reg m0 .rcx, gkrStateBytes) (by simp)
    · exact ((pre_got h).1 l hl).2.2.2 (rcAddr, 192) (by simp)
  simp only [PcOk] at hpc7
  refine fr7.call (c := 0) (Nc := gkrLayersStack) (lo := 8) (len := 0)
    (X := fun q ↦ NativeRustcVm.InRange t tstateBytes q ∨
      NativeRustcVm.InRange (reg m0 .rcx) gkrStateBytes q)
    hS N_ge (by omega) le_gl (by decide) (by omega) (outs_not_frame h)
    (fun q hq ↦ .inl (.inr hq)) (hgl s2 _) hpc7 hpre7
    (fun m' hq ↦ ⟨?_, hq.2.2.2⟩) fun m8 fr8 hq8 _ hcs8 ↦ ?_
  · have := hq.2.2.1
    rw [edi7, edx7] at this
    exact NativeRustcVm.SameOutside.mono this fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inr (.inl hq)
      · exact .inr (.inr hq)
      · exact .inl hq
  obtain ⟨hal, hok, -, -⟩ := hq8
  rw [esi7] at hal hok
  rw [edi7, edx7] at hok
  refine at_pc (by show Host.addrOf (k + NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b4Offset + b4.length) = _; rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyGkrGrandProducts.b4_next)
    (tail_spec hp h fr8 (hreg7.call hcs8) (y := cnt)
      ((hcs8 .r13 rfl).trans ((hm7.regs _ _ h137).trans hld16))
      ((hcs8 .rbp rfl).trans ((hm7.regs _ _ hbp7).trans hld24)) hal hok ?_)
  rw [hrun, hr1]
  simp only [Option.bind_some, hr2]


end

end

end NativeRustcVmX64.Bus.VerifyGkr
