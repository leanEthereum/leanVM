module

public import NativeRustcVmX64.Sumcheck.Gkr.Head
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfGkrStep.Names

/-!
# `sumcheck` with `gkr_step`'s closure: a round's challenge and claim (x86-64)

From `b8` (`Mid`): `squeeze` the challenge, `b9` stores it in slot `i` and calls `poly_eval` for
the next claim, `b10` goes back to the loop's head, or on to `.L8` after the last round
(`tail_spec`).
-/

namespace NativeRustcVmX64.Sumcheck.Gkr

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SumcheckOfGkrStep
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

public section

theorem add16_ofNat (i : Nat) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 16) (BitVec.ofNat 64 (16 * i)) =
      BitVec.ofNat 64 (16 * (i + 1)) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [← BitVec.ofNat_add, Nat.mul_succ, Nat.add_comm]

theorem add_ofNat_one (i : Nat) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 i) (BitVec.ofNat 64 1) = BitVec.ofNat 64 (i + 1) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [← BitVec.ofNat_add]

variable [Host] {a : DecArea} {s : TState} {pt : Array EW} {n : Nat} {m0 : MachineData} {k : Nat}

/-- **A round's challenge and claim**: from `b8`, the next round's head or `.L8`. -/
theorem tail_spec (hp : Placed code k)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpe : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hpre : SumcheckGkrPre a s pt n m0) {i : Nat} {xs msg : Array EW} {s1 : TState}
    {m : MachineData} (hi : Mid a s pt n m0 i xs msg s1 m) :
    Eventually (step1 Host.exe)
      (fun st ↦ Goal a s pt n m0 k st ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfGkrStep.b2Offset) ∧ Inv a s pt n m0 (i + 1) st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfGkrStep.b8Offset)⟩ := by
  have g := geo hpre
  have hlt := hi.lt
  have hc5 := g.cnt5
  have hmlen : 64 + (msg.toList.flatMap NativeRustcVm.ewBytes).length ≤ 144 := by
    rw [NativeRustcVm.length_ewsBytes]; simp [hi.msz]; omega
  have hl2 : Labels.label NativeRustcVmX64.Vm.SumcheckOfGkrStep.label_2 = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfGkrStep.b2Offset) :=
    hp.label NativeRustcVmX64.Vm.SumcheckOfGkrStep.label_2_at
  -- `b8`: `squeeze`.
  have hwf4 := wf_envB hpre hi.fr (Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfGkrStep.b8Offset + b8.length)).toBitVec
  refine exec_then (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf4 (fun _ _ ↦ rfl)
    (match_bodyS hi.fr _) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hw5, hrdi5, hrbx5, hrbp5, hr12_5, hr15_5, hk5⟩ := ok_b8
  have hin5 := writesIn_of_mid hmid5
  have hs5 : NativeRustcVm.SameOutside m.dmem st5.data.dmem (NativeRustcVm.InRange (fG m0) 192) :=
    sameOutside_low hwf4 hm5 (r := 0) rfl (hi := 192) (by omega) fun w hw ↦
      ⟨(hw5 w hw).1, by have := (hw5 w hw).2; omega⟩
  have hf5 : FrG m0 n 0 st5.data :=
    g.block hi.fr hwf4 hm5 hmid5 hs5 fun q hq ↦ Or.inl (g.ctx.inRange_frame hq)
  have ts5 : TStateAt st5.data.dmem (tG m0) a s1 :=
    g.t_keep hs5 (hm5.kept hwf4) (fun q hq ↦ Or.inl (g.ctx.inRange_frame hq)) hi.ts
  have xs5 : NativeRustcVm.EWsAt st5.data.dmem (slG m0) xs.toList :=
    g.sl_keep hs5 (fun q hq ↦ g.not_sl_stack (g.ctx.inRange_frame hq)) (by simp [hi.xsz]; omega)
      hi.xs
  have msg5 := keep_frame hwf4 hm5 hin5 (o := 64) (by omega)
    (fun w hw _ ↦ Or.inl (by have := (hw5 w hw).2; omega)) hi.msg
  have w5 := Words.block hwf4 hm5 hin5 (fun w hw _ ↦ Or.inl (by have := (hw5 w hw).2; omega)) hi.w
  have hrdi : reg st5.data .rdi = tG m0 := (hm5.regs .rdi _ hrdi5).trans hi.r12
  have hrbp : reg st5.data .rbp = off (slG m0) (16 * i) := by
    rw [show reg st5.data .rbp = _ from hm5.regs .rbp _ hrbp5]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [load_ofMachine (r := 1) (o := 8) rfl (arg_keep hpre hi.fr (i := 1) (by omega)),
      toBitVec_ofBitVec]
    show slG m0 + reg m .r13 = _
    rw [hi.r13]
  have hrbx : reg st5.data .rbx = off (fG m0) 64 := (hm5.regs .rbx _ hrbx5).trans hi.rbp
  have hr12 : reg st5.data .r12 = reg m0 .r8 := (hm5.regs .r12 _ hr12_5).trans hi.r15
  have hr15 : reg st5.data .r15 = off (slG m0) (16 * n) := (hm5.regs .r15 _ hr15_5).trans hi.rbx
  have hr13 : reg st5.data .r13 = BitVec.ofNat 64 (16 * i) :=
    (hm5.regs .r13 _ (Keeps.reg hk5 (by simp))).trans hi.r13
  have hr14 : reg st5.data .r14 = BitVec.ofNat 64 i :=
    (hm5.regs .r14 _ (Keeps.reg hk5 (by simp))).trans hi.r14
  refine call_then hpc5 (hsq s1.sponge) (g.squeezePre hf5 ts5 hrdi)
    fun st6 hpc6 hrsp6 hpost6 ↦ ?_
  have hsv6 := hpost6.2.2.2.2
  obtain ⟨hf6, h60, h61, ts6, hsl6, hloc6⟩ := g.afterSqueeze hf5 ts5 hpost6 hrsp6 hrdi
  have xs6 := hsl6 xs.toList (by simp [hi.xsz]; omega) xs5
  have msg6 := hloc6 64 _ (by omega) (by omega) msg5
  have w6 := Words.keep (fun o bs ho hob hb ↦ hloc6 o bs (by omega) (by omega) hb) w5
  -- `b9`: the challenge into slot `i`, `poly_eval`.
  obtain ⟨⟨hslm, hslnw⟩, hslA⟩ := g.slot_ok hlt hf6.frame.kept
  have hwf5 : (envX m0 st6.data (off (slG m0) (16 * i)) 16
      (Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfGkrStep.b9Offset + b9.length)).toBitVec).WF :=
    frame_wf ⟨g.ctx.mapped_frame hf6.frame.kept, g.ctx.noWrap_frame⟩
      (fun x hx ↦ by rw [List.mem_singleton] at hx; subst hx; exact ⟨hslm, hslnw⟩)
      (List.pairwise_pair.mpr hslA)
  have hrbp6 : reg st6.data .rbp = off (slG m0) (16 * i) := (hsv6.1 .rbp rfl).trans hrbp
  have hm5' : Match (envX m0 st6.data (off (slG m0) (16 * i)) 16
      (Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfGkrStep.b9Offset + b9.length)).toBitVec) slotS st6.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf6.frame.rsp_eval, known_ptr rfl hrbp6, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) exit_b9 hwf5 (fun _ _ ↦ rfl)
    (hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfGkrStep.b8_next)) hm5' fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hw7, hW0, hW8, hrdi7, hrsi7, hrdx7, hrcx7, hrbx7, hr15_7, hrbp7, hk7⟩ := ok_b9
  have hin7 := writesIn_of_mid hmid7
  have hs7 : NativeRustcVm.SameOutside st6.data.dmem st7.data.dmem (fun q ↦
      NativeRustcVm.InRange (fG m0) 192 q ∨ NativeRustcVm.InRange (off (slG m0) (16 * i)) 16 q) :=
    fun q hq ↦ hm7.get?_mem0 hwf5 fun hw ↦ hq (written_frame_hi hslnw le_rfl g.ctx.noWrap_frame
      (fun w hw' ↦ (hw7 w hw').imp (fun h ↦ ⟨h.1, by omega⟩) id) hw)
  have hf7 : FrG m0 n 0 st7.data :=
    g.block hf6 hwf5 hm7 hmid7 hs7 fun q hq ↦ hq.elim (fun h ↦ Or.inl (g.ctx.inRange_frame h))
      fun h ↦ Or.inr (Or.inr (g.slot_in hlt h))
  have hmiss7 : ∀ w ∈ (after b9 slotS).mem, w.r = 0 → w.off + w.n ≤ 8 := fun w hw hr ↦ by
    rcases hw7 w hw with h | h
    · exact h.2
    · omega
  have ts7 : TStateAt st7.data.dmem (tG m0) a { s1 with sponge := s1.sponge.squeeze.2 } :=
    g.t_keep hs7 (hm7.kept hwf5) (fun q hq ↦ hq.elim (fun h ↦ Or.inl (g.ctx.inRange_frame h))
      fun h ↦ Or.inr (g.slot_in hlt h)) ts6
  have msg7 := keep_frame hwf5 hm7 hin7 (o := 64) (by omega)
    (fun w hw hr ↦ Or.inl (by have := hmiss7 w hw hr; omega)) msg6
  have w7 := Words.block hwf5 hm7 hin7 (fun w hw hr ↦ Or.inl (by have := hmiss7 w hw hr; omega)) w6
  have xs7 : NativeRustcVm.EWsAt st7.data.dmem (slG m0) (xs.push s1.sponge.squeeze.1).toList := by
    have hR7 : ∀ q, (NativeRustcVm.InRange (fG m0) 192 q ∨
        NativeRustcVm.InRange (off (slG m0) (16 * i)) 16 q) →
        NativeRustcVm.InRange (off (slG m0) (16 * i)) 16 q ∨
          ¬ NativeRustcVm.InRange (slG m0) (16 * n) q := by
      intro q hq
      rcases hq with h | h
      · refine Or.inr fun h' ↦ g.sl_not_local (o := 0) (w := 192) (by omega) h' ?_
        rw [off_zero]; exact h
      · exact Or.inl h
    refine ewsAt_push (g.prefix_keep hlt hs7 hR7 (by simp [hi.xsz]) xs6) ?_
    have w0 := wordAt_written hm7 (r := 1) (o := 0) rfl (by omega) hW0
      (w := s1.sponge.squeeze.1.c0) h60
    have w8 := wordAt_written hm7 (r := 1) (o := 8) rfl (by omega) hW8
      (w := s1.sponge.squeeze.1.c1) h61
    rw [off_zero] at w0
    rw [hi.xsz]
    exact ewAt_iff.mpr ⟨w0, w8⟩
  have hrdi' : reg st7.data .rdi = off (fG m0) 64 :=
    (hm7.regs .rdi _ hrdi7).trans ((hsv6.1 .rbx rfl).trans hrbx)
  have hrsi' : (reg st7.data .rsi).toNat = cntG m0 := by
    rw [show reg st7.data .rsi = _ from (hm7.regs .rsi _ hrsi7).trans ((hsv6.1 .r12 rfl).trans hr12)]
  have hrdx' : reg st7.data .rdx = s1.sponge.squeeze.1.c0.toBitVec :=
    (hm7.regs .rdx _ hrdx7).trans h60
  have hrcx' : reg st7.data .rcx = s1.sponge.squeeze.1.c1.toBitVec :=
    (hm7.regs .rcx _ hrcx7).trans h61
  have hrbx7' : reg st7.data .rbx = off (slG m0) (16 * n) :=
    (hm7.regs .rbx _ hrbx7).trans ((hsv6.1 .r15 rfl).trans hr15)
  have hr15_7' : reg st7.data .r15 = reg m0 .r8 :=
    (hm7.regs .r15 _ hr15_7).trans ((hsv6.1 .r12 rfl).trans hr12)
  have hrbp7' : reg st7.data .rbp = off (slG m0) (16 * i) := (hm7.regs .rbp _ hrbp7).trans
    (by rw [Sym.eval, Env.base_ofMachine _ _ _ _ rfl, ofInt_zero64, BitVec.add_zero])
  have hr13_7 : reg st7.data .r13 = BitVec.ofNat 64 (16 * i) :=
    (hm7.regs .r13 _ (Keeps.reg hk7 (by simp))).trans ((hsv6.1 .r13 rfl).trans hr13)
  have hr14_7 : reg st7.data .r14 = BitVec.ofNat 64 i :=
    (hm7.regs .r14 _ (Keeps.reg hk7 (by simp))).trans ((hsv6.1 .r14 rfl).trans hr14)
  refine call_then hpc7 hpe (g.polyEvalPre hf7 (Mo := 64) (by omega) (by omega) hrdi' hrsi')
    fun st8 hpc8 hrsp8 hpost8 ↦ ?_
  have hsv8 := hpost8.2.2
  have hev : ewRet st8.data = polyEval msg s1.sponge.squeeze.1 := by
    rw [hpost8.1]
    unfold slice ewArg
    rw [hrdx', hrcx', hrsi', hrdi', show cntG m0 = msg.toList.length by simp [hi.msz],
      NativeRustcVm.ewsOf_of_ewsAt msg7]
  obtain ⟨hf8, hsl8, ht8, hloc8⟩ := g.afterPolyEval hf7 hpost8 hrsp8
  have w8 := Words.keep (fun o bs ho hob hb ↦ hloc8 o bs (by omega) (by omega) hb) w7
  -- `b10`: the claim, the next round or the end.
  have hwf8 := wf_envB hpre hf8 0
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) exit_b10 hwf8 nofun
    (hpc8.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfGkrStep.b9_next)) (match_bodyS hf8 _) fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨hmid9, hmem9, hrcx9, hrbp9, hr13_9, hr14_9, hk9⟩ := ok_b10
  have hd9 : st9.data.dmem = st8.data.dmem := hm9.dmem_eq hwf8 hmem9
  have hf9 : FrG m0 n 8 st9.data := g.block hf8 hwf8 hm9 hmid9 (R := fun _ ↦ False)
    (fun q _ ↦ by rw [hd9]) fun _ h ↦ h.elim
  have hrbp8 : reg st8.data .rbp = off (slG m0) (16 * i) := (hsv8.1 .rbp rfl).trans hrbp7'
  have hrbx8 : reg st8.data .rbx = off (slG m0) (16 * n) := (hsv8.1 .rbx rfl).trans hrbx7'
  have hclaim : claimR st9.data = polyEval msg s1.sponge.squeeze.1 := by
    rw [← hev]
    show (⟨_, _⟩ : EW) = ⟨_, _⟩
    rw [show reg st9.data .rax = _ from hm9.regs .rax _ (Keeps.reg hk9 (by simp)),
      show reg st9.data .rcx = _ from hm9.regs .rcx _ hrcx9]
    rfl
  have hrun9 : RoundsG a s pt m0 st9.data.dmem (i + 1) (claimR st9.data) := by
    rw [hclaim]
    refine ⟨xs.push s1.sponge.squeeze.1, _, hi.run, by simp [hi.xsz], ?_, ?_⟩
    · rw [hd9]; exact hsl8 _ (by simp [hi.xsz]; omega) xs7
    · rw [hd9]; exact ht8 _ ts7
  have hc : c10.eval (envB m0 st8.data 0) = !(i + 1 == n) := by
    simp only [c10, SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
    show (!(BinOp.apply .add .W64 (BitVec.ofNat 64 16) (reg st8.data .rbp) == reg st8.data .rbx)) = _
    rw [hrbp8, hrbx8, add16_off, g.slot_eq_end hlt]
  simp only [PcOk] at hpc9
  rw [hc] at hpc9
  by_cases hlast : i + 1 = n
  · simp only [hlast, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc9
    refine Eventually.done _ (.inl (.inr ⟨hpc9.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfGkrStep.b10_next), hf9,
      by rw [hd9]; exact w8.out, ?_⟩))
    rw [← hlast]; exact hrun9
  · have hb : (i + 1 == n) = false := by simpa using hlast
    simp only [hb, Bool.not_false, ↓reduceIte] at hpc9
    refine Eventually.done _ (.inr ⟨hpc9.trans hl2, hf9, by omega, by rw [hd9]; exact w8,
      ?_, ?_, ?_, ?_, hrun9⟩)
    · rw [show reg st9.data .r13 = _ from hm9.regs .r13 _ hr13_9]
      change BinOp.apply .add .W64 (BitVec.ofNat 64 16) (reg st8.data .r13) = _
      rw [show reg st8.data .r13 = _ from (hsv8.1 .r13 rfl).trans hr13_7, add16_ofNat]
    · rw [show reg st9.data .r14 = _ from hm9.regs .r14 _ hr14_9]
      change BinOp.apply .add .W64 (reg st8.data .r14) (BitVec.ofNat 64 1) = _
      rw [show reg st8.data .r14 = _ from (hsv8.1 .r14 rfl).trans hr14_7, add_ofNat_one]
    · exact (hm9.regs .r15 _ (Keeps.reg hk9 (by simp))).trans ((hsv8.1 .r15 rfl).trans hr15_7')
    · exact (hm9.regs .rbx _ (Keeps.reg hk9 (by simp))).trans hrbx8

end

end NativeRustcVmX64.Sumcheck.Gkr
