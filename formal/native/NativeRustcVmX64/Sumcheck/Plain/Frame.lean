module

public import NativeRustcVmX64.Sumcheck.Plain.Exec
public import NativeRustcVmX64.Sumcheck.Loop

/-!
# `sumcheck` with `sumcheck_plain`'s closure: the frame, the entry, the exits (x86-64)

The 176-byte frame (`FrP`, `SF`): the output's address at `16`, the message at `24`, `eq` at
`104`, the pushed registers from `128`. The loop's head `.L2` after `i < n` rounds (`Inv`: R12 the
`TState`, R13 `eq`, R14 slot `i`, R15 the count, RBX the slots' end, RBP the message, RAX, RCX the
claim, `Rounds`); `.L5` after the last (`Done`). `entry_spec`: `b0`, `b1` to the head, or to `.L5`
without slots; `exit_done` (`b7`, `b9`): the claim at the output; `exit_fail` (`b8`, `b9`):
`None`.
-/

namespace NativeRustcVmX64.Sumcheck.Plain

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

@[expose] public section

/-- The frame: 176 bytes below the entry's RSP. -/
abbrev fP (m0 : MachineData) : BitVec 64 := stackBelow m0 176

/-- The `TState`, the output, the slots, their count, the count at the entry. -/
abbrev tP (m0 : MachineData) : BitVec 64 := reg m0 .rsi
abbrev outP (m0 : MachineData) : BitVec 64 := reg m0 .rdi
abbrev slP (m0 : MachineData) : BitVec 64 := reg m0 .r9
abbrev nP (m0 : MachineData) : Nat := (stackArg m0 0).toNat
abbrev cntP (m0 : MachineData) : Nat := (reg m0 .r8).toNat

/-- The claim in RAX, RCX. -/
abbrev claimR (m : MachineData) : EW := ⟨.ofBitVec (reg m .rax), .ofBitVec (reg m .rcx)⟩

/-- The loop's frame. -/
abbrev FrP [Labels] (m0 : MachineData) (o : Nat) (m : MachineData) : Prop :=
  SF m0 (tP m0) (slP m0) (nP m0) sumcheckPlainStack 176 slots o m

/-- The model's run after `i` rounds. -/
abbrev RoundsP (a : DecArea) (s : TState) (m0 : MachineData) (d : Mem 64) (i : Nat) (c : EW) :
    Prop :=
  Rounds d (tP m0) a (slP m0) (claimArg m0) (cntP m0) (fun _ ↦ none) s i c

/-- **The loop's invariant** at `.L2`, `i < n` rounds done. -/
structure Inv [Labels] (a : DecArea) (s : TState) (m0 : MachineData) (i : Nat) (m : MachineData) :
    Prop where
  fr : FrP m0 8 m
  lt : i < nP m0
  out : NativeRustcVm.WordAt m.dmem (off (fP m0) 16) (UInt64.ofBitVec (outP m0))
  r12 : reg m .r12 = tP m0
  r13 : reg m .r13 = off (fP m0) 104
  r14 : reg m .r14 = off (slP m0) (16 * i)
  r15 : reg m .r15 = reg m0 .r8
  rbx : reg m .rbx = off (slP m0) (16 * nP m0)
  rbp : reg m .rbp = off (fP m0) 24
  run : RoundsP a s m0 m.dmem i (claimR m)

/-- At `.L5`: every round done. -/
structure Done [Labels] (a : DecArea) (s : TState) (m0 : MachineData) (m : MachineData) : Prop where
  fr : FrP m0 8 m
  out : NativeRustcVm.WordAt m.dmem (off (fP m0) 16) (UInt64.ofBitVec (outP m0))
  run : RoundsP a s m0 m.dmem (nP m0) (claimR m)

/-- The exits' environment: the frame, the output. -/
abbrev envO (m0 m : MachineData) : Env := frameEnv m0 m 176 [(outP m0, 24)] (fun _ ↦ 0) 0

/-- The body's environment: the frame. -/
abbrev envB (m0 m : MachineData) (ret : BitVec 64) : Env := frameEnv m0 m 176 [] (fun _ ↦ 0) ret

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 176 := by decide

theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

theorem Keeps.reg {S : SState} {rs : List Reg64} (h : Keeps S rs = true) {r : Reg64} (hr : r ∈ rs) :
    S.reg r = some (.reg r) := by
  simp only [Keeps, List.all_eq_true, beq_iff_eq] at h
  exact h r hr

/-- `x <<< 4` is `16 x`. -/
theorem shl4 (x : BitVec 64) :
    BinOp.apply .shl .W64 x (BitVec.ofNat 64 4) = BitVec.ofNat 64 (16 * x.toNat) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [show shiftCount .W64 (BitVec.ofNat 64 4) = 4 by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mul_comm]

section
variable [Labels] {a : DecArea} {s : TState} {m0 : MachineData}

theorem geo (h : SumcheckPlainPre a s m0) :
    Geo a s m0 (tP m0) (outP m0) (slP m0) (cntP m0) (nP m0) sumcheckPlainStack 176 slots 128 :=
  ⟨h.2, by unfold sumcheckPlainStack; omega, by decide, by decide⟩

theorem wf_envO (h : SumcheckPlainPre a s m0) {o : Nat} {m : MachineData} (hf : FrP m0 o m) :
    (envO m0 m).WF := by
  have g := geo h
  refine frame_wf ⟨g.ctx.mapped_frame hf.frame.kept, g.ctx.noWrap_frame⟩ (fun x hx ↦ ?_)
    (List.pairwise_pair.mpr (Apart.symm' (apart_frame g.outOk.2.2.2.2.1 g.ctx.spN g.ctx.le)))
  rw [List.mem_singleton] at hx
  subst hx
  exact ⟨Mapped.keeps g.outOk.1 hf.frame.kept, g.outOk.2.1⟩

theorem wf_envB (h : SumcheckPlainPre a s m0) {o : Nat} {m : MachineData} (hf : FrP m0 o m)
    (ret : BitVec 64) : (envB m0 m ret).WF :=
  frame_wf ⟨(geo h).ctx.mapped_frame hf.frame.kept, (geo h).ctx.noWrap_frame⟩ (by simp)
    (List.pairwise_singleton _ _)

theorem match_bodyS {m : MachineData} (hf : FrP m0 8 m) (ret : BitVec 64) :
    Match (envB m0 m ret) bodyS m :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hf.frame.rsp_eval, trivial⟩ trivial trivial trivial

theorem match_outS {m : MachineData} (hf : FrP m0 8 m)
    (hout : NativeRustcVm.WordAt m.dmem (off (fP m0) 16) (UInt64.ofBitVec (outP m0))) :
    Match (envO m0 m) outS m := by
  have hal : (Sym.load 0 16 8).eval (envO m0 m) = (envO m0 m).base 1 + BitVec.ofInt 64 0 := by
    rw [ofInt_zero64, BitVec.add_zero]
    exact load_ofMachine (o := 16) rfl hout
  exact match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.frame.rsp_eval, trivial⟩ trivial trivial
    ⟨hal, trivial⟩

end

variable [Host] {a : DecArea} {s : TState} {m0 : MachineData} {k : Nat}

/-- **The exits' common end**: after `b9`, the registers restored, the postcondition. -/
theorem exit_post (hpre : SumcheckPlainPre a s m0) {m : MachineData} (hf : FrP m0 8 m)
    {S' : SState} {st : MachineState} (hm' : Match (envO m0 m) S' st.data)
    (hepi : EpiOk 176 slots S' = true) (hW : ∀ w ∈ S'.mem, w.r = 1 ∧ w.off + w.n ≤ 24)
    (hpc : PcOk (envO m0 m) (.ret (.load 0 176 8)) 0 st)
    {r : Option ((Array EW × EW) × TState)}
    (hr : r = (sumcheckPlain (claimArg m0) (reg m0 .r8).toNat (stackArg m0 0).toNat).run s)
    (hxs : ∀ xs c s', r = some ((xs, c), s') →
      xs.toList.length ≤ nP m0 ∧ NativeRustcVm.EWsAt m.dmem (slP m0) xs.toList)
    (hts : NextAt m.dmem (tP m0) a r)
    (ho : OptEWAt st.data.dmem (outP m0) (r.map (·.1.2))) :
    st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ SumcheckPlainPost a s m0 st.data := by
  have g := geo hpre
  have hwf := wf_envO hpre hf
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf.frame hwf hm' hepi
  simp only [PcOk, Sym.eval] at hpc
  have hs : NativeRustcVm.SameOutside m.dmem st.data.dmem (NativeRustcVm.InRange (outP m0) 24) :=
    sameOutside_region hwf hm' (r := 1) rfl fun w hw ↦ ⟨(hW w hw).1, Nat.zero_le _, (hW w hw).2⟩
  have hosl : ∀ q, NativeRustcVm.InRange (outP m0) 24 q →
      ¬ NativeRustcVm.InRange (slP m0) (16 * nP m0) q := fun q hq ↦
    not_inRange_of_apart g.ok.2.2.2.2.2.2.2.2.1 g.outOk.2.1 g.slOk.2.1 hq
  refine ⟨hpc.trans (hf.frame.load_ret g.ok.1 (by unfold sumcheckPlainStack; omega)), hrsp, ?_⟩
  unfold SumcheckPlainPost
  dsimp only
  rw [← hr]
  refine ⟨⟨ho, fun xs c s' h ↦ g.sl_keep hs hosl (hxs xs c s' h).1 (hxs xs c s' h).2,
    fun x s' h ↦ (hts x s' h).frame (hm'.kept hwf) (fun q hq ↦ g.ctx.out_not_t g.outOk hq) hs⟩,
    NativeRustcVm.SameOutside.mono (hf.same.trans hs) fun q hq ↦ ?_, hsv⟩
  rcases hq with (hq | hq | hq) | hq
  · exact Or.inr (Or.inr (Or.inr hq))
  · exact Or.inr (Or.inr (Or.inl hq))
  · exact Or.inr (Or.inl hq)
  · exact Or.inl hq

/-- **`b7`, `b9`**: every round done, the claim into the output, the exit. -/
theorem exit_done (hp : Placed code k) (hpre : SumcheckPlainPre a s m0) {m : MachineData}
    (hd : Done a s m0 m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
        SumcheckPlainPost a s m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b7Offset)⟩ := by
  obtain ⟨xs, sn, hrun, hsz, hxs, hts⟩ := hd.run
  have hr : (sumcheckPlain (claimArg m0) (reg m0 .r8).toNat (stackArg m0 0).toNat).run s =
      some ((xs, claimR m), sn) := by
    rw [← sumcheckFn_none]; exact hrun
  have hwf := wf_envO hpre hd.fr
  refine exec_then (infix_of b7_in_code (by simp [b7]) hp) exit_b7 hwf nofun
    (match_outS hd.fr hd.out) fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  rw [hp.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.label_6_at] at hpc1
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) exit_b9a hwf nofun hpc1 hm1
    fun st2 hm2 hpc2 ↦ Eventually.done _ ?_
  obtain ⟨hepi, hW, hW0, hW8, hW16⟩ := ok_b9a
  refine exit_post hpre hd.fr hm2 hepi hW hpc2 hr.symm
    (fun xs' c s' h ↦ by cases h; exact ⟨by simp [hsz], hxs⟩)
    (fun x s' h ↦ by cases h; exact hts) ?_
  have w0 := wordAt_written hm2 (r := 1) (o := 0) rfl (by omega) hW0 (w := 1) rfl
  have w8 := wordAt_written hm2 (r := 1) (o := 8) rfl (by omega) hW8 (w := (claimR m).c0) rfl
  have w16 := wordAt_written hm2 (r := 1) (o := 16) rfl (by omega) hW16 (w := (claimR m).c1) rfl
  rw [off_zero] at w0
  refine ⟨w0, ewAt_iff.mpr ⟨w8, ?_⟩⟩
  rw [off_off]
  exact w16

/-- **`b8`, `b9`**: a rejected round, `None` into the output, the exit. -/
theorem exit_fail (hp : Placed code k) (hpre : SumcheckPlainPre a s m0) {m : MachineData}
    (hf : FrP m0 8 m)
    (hout : NativeRustcVm.WordAt m.dmem (off (fP m0) 16) (UInt64.ofBitVec (outP m0)))
    (hnone : (sumcheckFn (claimArg m0) (cntP m0) (fun _ ↦ none) (nP m0)).run s = none) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
        SumcheckPlainPost a s m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b8Offset)⟩ := by
  have hwf := wf_envO hpre hf
  refine exec_then (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf nofun
    (match_outS hf hout) fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) exit_b9b hwf nofun
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b8_next)) hm1 fun st2 hm2 hpc2 ↦ Eventually.done _ ?_
  obtain ⟨hepi, hW, hW0⟩ := ok_b9b
  refine exit_post hpre hf hm2 hepi hW hpc2 (r := none)
    (by rw [← sumcheckFn_none]; exact hnone.symm) (fun _ _ _ h ↦ (nomatch h))
    (fun _ _ h ↦ (nomatch h)) ?_
  have w0 := wordAt_written hm2 (r := 1) (o := 0) rfl (by omega) hW0 (w := 0) rfl
  rw [off_zero] at w0
  exact w0

/-- **The entry**: `b0` pushes the registers and zeroes the message; without slots at `.L5`,
else `b1` and the loop's head with no round done. -/
theorem entry_spec (hp : Placed code k) (hpre : SumcheckPlainPre a s m0) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b7Offset) ∧ Done a s m0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b2Offset) ∧ Inv a s m0 0 st.data))
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b0Offset)⟩ := by
  have g := geo hpre
  have hargs := hpre.1
  have hst := g.ok.1
  have hle : 176 ≤ sumcheckPlainStack := by unfold sumcheckPlainStack; omega
  let env := frameEnv m0 m0 176 [(rspOf m0 + 8#64, 8)] (fun _ ↦ 0) 0
  have hrd := args_readable hargs (by omega)
  have hwf : env.WF := by
    refine frame_wf ⟨frame_mapped hst hle, frame_noWrap hst hle⟩ (fun x hx ↦ ?_)
      (List.pairwise_pair.mpr (args_apart hst hargs (by omega) hle))
    rw [List.mem_singleton] at hx
    subst hx
    exact hrd
  have hal : (Sym.ptr 0 184).eval env = env.base 1 + BitVec.ofInt 64 0 := by
    rw [ofInt_zero64, BitVec.add_zero]
    exact (eval_ptr0 (m0 := m0) (d := m0) (F := 176) (rest := [(rspOf m0 + 8#64, 8)])
      (vars := fun _ ↦ 0) (ret := 0) 184).trans (frame_add (m0 := m0) 176 8)
  have hm : Match env entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial ⟨hal, trivial⟩
  have hload : env.load 1 0 8 = stackArg m0 0 :=
    load_ofMachine (r := 1) (o := 0) rfl (stackArg_wordAt hargs (i := 0) (by omega))
  have hts0 := g.ok.2.2.1
  -- The frame and the `TState` after the prologue's writes.
  have hpro : ∀ {S : SState} {d : MachineData}, Match env S d → ProOk 176 8 slots S = true →
      (∀ w ∈ S.mem, w.r = 0) → WordW 0 16 (.reg .rdi) S →
      FrP m0 8 d ∧ NativeRustcVm.WordAt d.dmem (off (fP m0) 16) (UInt64.ofBitVec (outP m0)) ∧
        TStateAt d.dmem (tP m0) a s := by
    intro S d hmS hP hall hW16
    have hs : NativeRustcVm.SameOutside m0.dmem d.dmem (NativeRustcVm.InRange (fP m0) 176) :=
      sameOutside_low hwf hmS (r := 0) rfl (hi := 176) (by omega) fun w hw ↦
        ⟨hall w hw, belowRet_spec (belowRet_of_pro hP) w hw (hall w hw)⟩
    refine ⟨⟨Frame.of_prologue Frame.entry hwf hmS hP slots_le slots_cs,
      NativeRustcVm.SameOutside.mono hs fun q hq ↦ Or.inl (g.ctx.inRange_frame hq)⟩,
      wordAt_written hmS (r := 0) (o := 16) rfl (by omega) hW16 rfl, ?_⟩
    exact g.t_keep hs (hmS.kept hwf) (fun q hq ↦ Or.inl (g.ctx.inRange_frame hq)) hts0
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf nofun hm
    fun st0 hm0 hpc0 ↦ ?_
  obtain ⟨hP0, hall0, hW0, hrax0, hrcx0⟩ := ok_b0
  obtain ⟨hfr0, hout0, hts0'⟩ := hpro hm0 hP0 hall0 hW0
  have hc0 : c0.eval env = decide (nP m0 = 0) := by
    simp only [c0, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
      BitVec.and_self, hload]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
    rfl
  simp only [PcOk, hc0] at hpc0
  have hclaim0 : claimR st0.data = claimArg m0 := by
    show (⟨_, _⟩ : EW) = ⟨_, _⟩
    rw [show reg st0.data .rax = reg m0 .rdx from hm0.regs .rax _ hrax0,
      show reg st0.data .rcx = reg m0 .rcx from hm0.regs .rcx _ hrcx0]
  by_cases h0 : nP m0 = 0
  · simp only [h0, decide_true, ite_true] at hpc0
    refine .done _ (Or.inl ⟨hpc0.trans (hp.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.label_5_at), hfr0, hout0, ?_⟩)
    rw [hclaim0, h0]
    exact rounds_zero hts0'
  · simp only [h0, decide_false, Bool.false_eq_true, ite_false] at hpc0
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf nofun
      (hpc0.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b0_next)) hm0 fun st1 hm1 hpc1 ↦ ?_
    obtain ⟨hP1, hall1, hW1, hrax1, hrcx1, hrbx1, hrbp1, hr12, hr13, hr14, hr15⟩ := ok_b1
    obtain ⟨hfr1, hout1, hts1⟩ := hpro hm1 hP1 hall1 hW1
    simp only [PcOk] at hpc1
    have hclaim1 : claimR st1.data = claimArg m0 := by
      show (⟨_, _⟩ : EW) = ⟨_, _⟩
      rw [show reg st1.data .rax = reg m0 .rdx from hm1.regs .rax _ hrax1,
        show reg st1.data .rcx = reg m0 .rcx from hm1.regs .rcx _ hrcx1]
    refine .done _ (Or.inr ⟨hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b1_next), hfr1,
      Nat.pos_of_ne_zero h0, hout1, hm1.regs .r12 _ hr12,
      (hm1.regs .r13 _ hr13).trans (eval_ptr0 104), ?_, hm1.regs .r15 _ hr15, ?_,
      (hm1.regs .rbp _ hrbp1).trans (eval_ptr0 24), ?_⟩)
    · rw [show reg st1.data .r14 = _ from hm1.regs .r14 _ hr14, Nat.mul_zero, off_zero]
      rfl
    · rw [show reg st1.data .rbx = _ from hm1.regs .rbx _ hrbx1]
      simp only [Sym.eval, hload, shl4]
      simp only [BinOp.apply, low_W64, ext_W64]
      rfl
    · rw [hclaim1]
      exact rounds_zero hts1

end

end NativeRustcVmX64.Sumcheck.Plain
