module

public import NativeRustcVmX64.Sumcheck.Plain.Head
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names

/-!
# `sumcheck` with `sumcheck_plain`'s closure: a round's challenge and claim (x86-64)

From `b4` (`Mid`): `squeeze` the challenge, `b5` stores it in slot `i` and calls `poly_eval` for
the next claim, `b6` goes back to the loop's head, or on to `.L5` after the last round
(`tail_spec`).
-/

namespace NativeRustcVmX64.Sumcheck.Plain

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

public section

theorem add16_off (sl : BitVec 64) (i : Nat) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 16) (off sl (16 * i)) = off sl (16 * (i + 1)) := by
  simp only [BinOp.apply, low_W64, ext_W64, off]
  rw [BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

variable [Host] {a : DecArea} {s : TState} {m0 : MachineData} {k : Nat}

/-- **A round's challenge and claim**: from `b4`, the next round's head or `.L5`. -/
theorem tail_spec (hp : Placed code k)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpe : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hpre : SumcheckPlainPre a s m0) {i : Nat} {xs msg : Array EW} {s1 : TState}
    {m : MachineData} (hi : Mid a s m0 i xs msg s1 m) :
    Eventually (step1 Host.exe)
      (fun st ↦ Goal a s m0 k st ∨ (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b2Offset) ∧ Inv a s m0 (i + 1) st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b4Offset)⟩ := by
  have g := geo hpre
  have hlt := hi.lt
  have hc5 := g.cnt5
  have hmlen : 24 + (msg.toList.flatMap NativeRustcVm.ewBytes).length ≤ 176 := by
    rw [NativeRustcVm.length_ewsBytes]; simp [hi.msz]; omega
  have hl2 : Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.label_2 = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b2Offset) :=
    hp.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.label_2_at
  -- `b4`: `squeeze`.
  have hwf4 := wf_envB hpre hi.fr (Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b4Offset + b4.length)).toBitVec
  refine exec_then (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf4 (fun _ _ ↦ rfl)
    (match_bodyS hi.fr _) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hw5, hrdi5, hk5⟩ := ok_b4
  have hin5 := writesIn_of_mid hmid5
  have hs5 : NativeRustcVm.SameOutside m.dmem st5.data.dmem (NativeRustcVm.InRange (fP m0) 176) :=
    sameOutside_low hwf4 hm5 (r := 0) rfl (hi := 176) (by omega) fun w hw ↦
      ⟨(hw5 w hw).1, by have := (hw5 w hw).2; omega⟩
  have hf5 : FrP m0 0 st5.data :=
    g.block hi.fr hwf4 hm5 hmid5 hs5 fun q hq ↦ Or.inl (g.ctx.inRange_frame hq)
  have hmiss5 : ∀ o, 8 ≤ o → ∀ w ∈ (after b4 bodyS).mem, w.r = 0 →
      w.off + w.n ≤ o ∨ o + 8 ≤ w.off := fun o h1 w hw _ ↦ Or.inl (by have := (hw5 w hw).2; omega)
  have ts5 : TStateAt st5.data.dmem (tP m0) a s1 :=
    g.t_keep hs5 (hm5.kept hwf4) (fun q hq ↦ Or.inl (g.ctx.inRange_frame hq)) hi.ts
  have xs5 : NativeRustcVm.EWsAt st5.data.dmem (slP m0) xs.toList :=
    g.sl_keep hs5 (fun q hq ↦ g.not_sl_stack (g.ctx.inRange_frame hq)) (by simp [hi.xsz]; omega)
      hi.xs
  have msg5 := keep_frame hwf4 hm5 hin5 (o := 24) (by omega)
    (fun w hw _ ↦ Or.inl (by have := (hw5 w hw).2; omega)) hi.msg
  have out5 := keepW hwf4 hm5 hin5 (o := 16) (by omega) (hmiss5 16 (by omega)) hi.out
  have hrdi : reg st5.data .rdi = tP m0 := (hm5.regs .rdi _ hrdi5).trans hi.r12
  have hreg5 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st5.data r = reg m r :=
    fun r hr ↦ hm5.regs r _ (Keeps.reg hk5 hr)
  refine call_then hpc5 (hsq s1.sponge) (g.squeezePre hf5 ts5 hrdi)
    fun st6 hpc6 hrsp6 hpost6 ↦ ?_
  have hsv6 := hpost6.2.2.2.2
  obtain ⟨hf6, h60, h61, ts6, hsl6, hloc6⟩ := g.afterSqueeze hf5 ts5 hpost6 hrsp6 hrdi
  have hreg6 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st6.data r = reg m r :=
    fun r hr ↦ (hsv6.1 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans
      (hreg5 r hr)
  have xs6 := hsl6 xs.toList (by simp [hi.xsz]; omega) xs5
  have msg6 := hloc6 24 _ (by omega) hmlen msg5
  have out6 := hloc6 16 (NativeRustcVm.wordBytes (UInt64.ofBitVec (outP m0))) (by omega)
    (by rw [NativeRustcVm.length_wordBytes]; omega) out5
  -- `b5`: the challenge into slot `i`, `poly_eval`.
  obtain ⟨⟨hslm, hslnw⟩, hslA⟩ := g.slot_ok hlt hf6.frame.kept
  let env := frameEnv m0 st6.data 176 [(off (slP m0) (16 * i), 16)] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b5Offset + b5.length)).toBitVec
  have hwf5 : env.WF :=
    frame_wf ⟨g.ctx.mapped_frame hf6.frame.kept, g.ctx.noWrap_frame⟩
      (fun x hx ↦ by rw [List.mem_singleton] at hx; subst hx; exact ⟨hslm, hslnw⟩)
      (List.pairwise_pair.mpr hslA)
  have hr14_6 : reg st6.data .r14 = off (slP m0) (16 * i) := (hreg6 .r14 (by simp)).trans hi.r14
  have hm5' : Match env slotS st6.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf6.frame.rsp_eval, known_ptr rfl hr14_6, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf5 (fun _ _ ↦ rfl)
    (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b4_next)) hm5' fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hw7, hW0, hW8, hrdi7, hrsi7, hrdx7, hrcx7, hr14_7, hk7⟩ := ok_b5
  have hin7 := writesIn_of_mid hmid7
  have hs7 : NativeRustcVm.SameOutside st6.data.dmem st7.data.dmem (fun q ↦
      NativeRustcVm.InRange (fP m0) 176 q ∨ NativeRustcVm.InRange (off (slP m0) (16 * i)) 16 q) :=
    fun q hq ↦ hm7.get?_mem0 hwf5 fun hw ↦ hq (written_frame_hi hslnw le_rfl g.ctx.noWrap_frame
      (fun w hw' ↦ (hw7 w hw').imp (fun h ↦ ⟨h.1, by omega⟩) id) hw)
  have hf7 : FrP m0 0 st7.data :=
    g.block hf6 hwf5 hm7 hmid7 hs7 fun q hq ↦ hq.elim (fun h ↦ Or.inl (g.ctx.inRange_frame h))
      fun h ↦ Or.inr (Or.inr (g.slot_in hlt h))
  have hmiss7 : ∀ o, 8 ≤ o → ∀ w ∈ (after b5 slotS).mem, w.r = 0 →
      w.off + w.n ≤ o ∨ o + 8 ≤ w.off := fun o h1 w hw hr ↦ by
    rcases hw7 w hw with h | h
    · exact Or.inl (by omega)
    · omega
  have ts7 : TStateAt st7.data.dmem (tP m0) a { s1 with sponge := s1.sponge.squeeze.2 } :=
    g.t_keep hs7 (hm7.kept hwf5) (fun q hq ↦ hq.elim (fun h ↦ Or.inl (g.ctx.inRange_frame h))
      fun h ↦ Or.inr (g.slot_in hlt h)) ts6
  have msg7 := keep_frame hwf5 hm7 hin7 (o := 24) (by omega)
    (fun w hw hr ↦ Or.inl (by rcases hw7 w hw with h | h <;> omega)) msg6
  have out7 := keepW hwf5 hm7 hin7 (o := 16) (by omega) (hmiss7 16 (by omega)) out6
  have xs7 : NativeRustcVm.EWsAt st7.data.dmem (slP m0) (xs.push s1.sponge.squeeze.1).toList := by
    refine ewsAt_push (g.prefix_keep hlt hs7 (fun q hq ↦ hq.elim
      (fun h ↦ Or.inr fun h' ↦ g.sl_not_local (o := 0) (w := 176) (by omega) h'
        (by rwa [off_zero])) Or.inl) (by simp [hi.xsz]) xs6) ?_
    have w0 := wordAt_written hm7 (r := 1) (o := 0) rfl (by omega) hW0
      (w := s1.sponge.squeeze.1.c0) h60
    have w8 := wordAt_written hm7 (r := 1) (o := 8) rfl (by omega) hW8
      (w := s1.sponge.squeeze.1.c1) h61
    rw [off_zero] at w0
    rw [hi.xsz]
    exact ewAt_iff.mpr ⟨w0, w8⟩
  have hrdi' : reg st7.data .rdi = off (fP m0) 24 :=
    (hm7.regs .rdi _ hrdi7).trans ((hreg6 .rbp (by simp)).trans hi.rbp)
  have hrsi' : (reg st7.data .rsi).toNat = cntP m0 := by
    rw [show reg st7.data .rsi = _ from
      (hm7.regs .rsi _ hrsi7).trans ((hreg6 .r15 (by simp)).trans hi.r15)]
  have hrdx' : reg st7.data .rdx = s1.sponge.squeeze.1.c0.toBitVec := (hm7.regs .rdx _ hrdx7).trans h60
  have hrcx' : reg st7.data .rcx = s1.sponge.squeeze.1.c1.toBitVec := (hm7.regs .rcx _ hrcx7).trans h61
  have hr14' : reg st7.data .r14 = off (slP m0) (16 * i) := (hm7.regs .r14 _ hr14_7).trans
    (by rw [Sym.eval, Env.base_ofMachine _ _ _ _ rfl, ofInt_zero64, BitVec.add_zero])
  have hreg7 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r15], reg st7.data r = reg m r :=
    fun r hr ↦ (hm7.regs r _ (Keeps.reg hk7 hr)).trans
      (hreg6 r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp))
  refine call_then hpc7 hpe (g.polyEvalPre hf7 (Mo := 24) (by omega) (by omega) hrdi' hrsi')
    fun st8 hpc8 hrsp8 hpost8 ↦ ?_
  have hsv8 := hpost8.2.2
  have hev : ewRet st8.data = polyEval msg s1.sponge.squeeze.1 := by
    rw [hpost8.1]
    unfold slice ewArg
    rw [hrdx', hrcx', hrsi', hrdi', show cntP m0 = msg.toList.length by simp [hi.msz],
      NativeRustcVm.ewsOf_of_ewsAt msg7]
  obtain ⟨hf8, hsl8, ht8, hloc8⟩ := g.afterPolyEval hf7 hpost8 hrsp8
  have out8 := hloc8 16 (NativeRustcVm.wordBytes (UInt64.ofBitVec (outP m0))) (by omega)
    (by rw [NativeRustcVm.length_wordBytes]; omega) out7
  -- `b6`: the claim, the next round or the end.
  have hwf8 := wf_envB hpre hf8 0
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf8 nofun
    (hpc8.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b5_next)) (match_bodyS hf8 _) fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨hmid9, hmem9, hrcx9, hr14_9, hk9⟩ := ok_b6
  have hd9 : st9.data.dmem = st8.data.dmem := hm9.dmem_eq hwf8 hmem9
  have hf9 : FrP m0 8 st9.data := g.block hf8 hwf8 hm9 hmid9 (R := fun _ ↦ False)
    (fun q _ ↦ by rw [hd9]) fun _ h ↦ h.elim
  have hreg9 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r15], reg st9.data r = reg m r :=
    fun r hr ↦ (hm9.regs r _ (Keeps.reg hk9 (by simp at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp))).trans
      ((hsv8.1 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (hreg7 r hr))
  have hr14_8 : reg st8.data .r14 = off (slP m0) (16 * i) := (hsv8.1 .r14 rfl).trans hr14'
  have hrbx8 : reg st8.data .rbx = off (slP m0) (16 * nP m0) :=
    (hsv8.1 .rbx rfl).trans ((hreg7 .rbx (by simp)).trans hi.rbx)
  have hclaim : claimR st9.data = polyEval msg s1.sponge.squeeze.1 := by
    rw [← hev]
    show (⟨_, _⟩ : EW) = ⟨_, _⟩
    rw [show reg st9.data .rax = _ from hm9.regs .rax _ (Keeps.reg hk9 (by simp)),
      show reg st9.data .rcx = _ from hm9.regs .rcx _ hrcx9]
    rfl
  have hrun9 : RoundsP a s m0 st9.data.dmem (i + 1) (claimR st9.data) := by
    rw [hclaim]
    refine ⟨xs.push s1.sponge.squeeze.1, _, hi.run, by simp [hi.xsz], ?_, ?_⟩
    · rw [hd9]; exact hsl8 _ (by simp [hi.xsz]; omega) xs7
    · rw [hd9]; exact ht8 _ ts7
  have hc : c6.eval (envB m0 st8.data 0) = !(i + 1 == nP m0) := by
    simp only [c6, SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
    show (!(BinOp.apply .add .W64 (BitVec.ofNat 64 16) (reg st8.data .r14) == reg st8.data .rbx)) = _
    rw [hr14_8, hrbx8, add16_off, g.slot_eq_end hlt]
  simp only [PcOk] at hpc9
  rw [hc] at hpc9
  by_cases hlast : i + 1 = nP m0
  · simp only [hlast, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc9
    refine Eventually.done _ (.inl (.inr ⟨hpc9.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b6_next), hf9,
      by rw [hd9]; exact out8, ?_⟩))
    rw [← hlast]; exact hrun9
  · have hb : (i + 1 == nP m0) = false := by simpa using hlast
    simp only [hb, Bool.not_false, ↓reduceIte] at hpc9
    refine Eventually.done _ (.inr ⟨hpc9.trans hl2, hf9, by omega, by rw [hd9]; exact out8,
      ?_, ?_, ?_, ?_, ?_, ?_, hrun9⟩)
    · rw [hreg9 .r12 (by simp)]; exact hi.r12
    · rw [hreg9 .r13 (by simp)]; exact hi.r13
    · rw [show reg st9.data .r14 = _ from hm9.regs .r14 _ hr14_9]
      change BinOp.apply .add .W64 (BitVec.ofNat 64 16) (reg st8.data .r14) = _
      rw [hr14_8, add16_off]
    · rw [hreg9 .r15 (by simp)]; exact hi.r15
    · rw [hreg9 .rbx (by simp)]; exact hi.rbx
    · rw [hreg9 .rbp (by simp)]; exact hi.rbp

end

end NativeRustcVmX64.Sumcheck.Plain
