module

public import NativeRustcVmArm.Code.Vm.PolyEval.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.Sumcheck.Plain.Head

/-!
# `sumcheck` with `sumcheck_plain`'s closure: a round's challenge and claim

From `b4` (`Mid`): `squeeze` the challenge, `b5` stores it in slot `i` and calls `poly_eval` for
the next claim, `b6` goes back to the loop's head, or on to `.L4` after the last round
(`tail_spec`).
-/

namespace NativeRustcVmArm.Sumcheck.Plain

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck

public section

variable [Host] {a : DecArea} {s : TState} {m0 : MachineData} {k : Nat}

/-- **A round's challenge and claim**: from `b4`, the next round's head or `.L4`. -/
theorem tail_spec (hp : Placed code k)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpe : Spec (Labels.label NativeRustcVmArm.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hpre : SumcheckPlainPre a s m0) {i : Nat} {xs msg : Array EW} {s1 : TState}
    {m : MachineData} (hi : Mid a s m0 i xs msg s1 m) :
    Eventually (step1 Host.exe)
      (fun st ↦ Goal a s m0 k st ∨ (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b2Offset) ∧ Inv a s m0 (i + 1) st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b4Offset)⟩ := by
  have g := geo hpre
  have hS := hpre.1
  have hlt := hi.lt
  have hc5 := g.ok.2.2.2.2.2.1
  unfold maxCount at hc5
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b4Offset) := b4_in_code.trans hp.1 (by simp [b4])
  have hk5 : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b5Offset) := b5_in_code.trans hp.1 (by simp [b5])
  have hk6 : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b6Offset) := b6_in_code.trans hp.1 (by simp [b6])
  have hl2 : Labels.label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b2Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.b2Offset) NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.label_2_at
  -- `b4`: `squeeze`.
  have hwf4 := Bus.wf_frame (F := 160) hS (by decide) hi.fr.kept
  have hm4 : Match (Env.ofMachine m [(base m0 160, 160)]) frS m :=
    Bus.match_frame hS (by decide) (by decide) hi.fr.sp
  refine exec_then hk4 run_b4 hwf4 hm4 fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hfr5, hd5⟩ := frBlock hi.fr hS (by decide) (by decide) hm5 rfl rfl (by decide)
    (by decide)
  have hts5 : TStateAt st5.data.dmem (tP m0) a s1 := by rw [hd5]; exact hi.ts
  have hx0 : st5.data.regs.X0.toBitVec = tP m0 :=
    (hm5.regs .X0 _ rfl).trans (congrArg UInt64.toBitVec hi.x22)
  have hreg5 : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 →
      st5.data.regs.getXReg r = m.regs.getXReg r := by
    rintro r (rfl | rfl | rfl | rfl | rfl) <;>
      exact UInt64.toBitVec_inj.mp ((hm5.regs _ _ rfl).trans rfl)
  refine call_then hpc5 (hsq s1.sponge) (g.squeezePre hfr5 hts5 hx0) fun st6 hpc6 hpost6 ↦ ?_
  have hsv6 := hpost6.2.2.2.2
  obtain ⟨hfr6, h60, h61, hts6, hsl6, hloc6⟩ :=
    g.afterSqueeze hfr5 hts5 hpost6 hx0 keepP_saved slotsP8
  have hreg6 : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 →
      st6.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    (hsv6.1 r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (hreg5 r hr)
  have hxs6 : NativeRustcVm.EWsAt st6.data.dmem (slP m0) xs.toList :=
    hsl6 xs.toList (by simp [hi.xsz]; omega) (by rw [hd5]; exact hi.xs)
  have hmsg6 : NativeRustcVm.EWsAt st6.data.dmem (base m0 160 + BitVec.ofNat 64 8) msg.toList :=
    hloc6 8 _ (by rw [NativeRustcVm.length_ewsBytes]; simp [hi.msz]; omega)
      (by rw [hd5]; exact hi.msg)
  -- `b5`: the challenge into slot `i`, `poly_eval`.
  have hx20 : (st6.data.regs.getXReg .X20).toBitVec = slP m0 + BitVec.ofNat 64 (16 * i) := by
    rw [hreg6 .X20 (.inr (.inl rfl))]; exact hi.x20
  have hwf5 : (Env.ofMachine st6.data [(base m0 160, 160),
      (slP m0 + BitVec.ofNat 64 (16 * i), 16)]).WF :=
    Bus.wf_frame2 hS (by decide) hfr6.kept (g.slot_ok hlt).1 (g.slot_ok hlt).2
  have hm5' : Match (Env.ofMachine st6.data [(base m0 160, 160),
      (slP m0 + BitVec.ofNat 64 (16 * i), 16)]) slotS st6.data := by
    have := Bus.match_frame2 (r := .X20) (n := 16) hS (by decide) (by decide) hfr6.sp
    rwa [hx20] at this
  refine exec_at hk5 run_b5 hwf5 hpc6 hm5' fun st7 hm7 hpc7 ↦ ?_
  have hm7A : Match (Env.ofMachine st6.data [(base m0 160, 160),
      (slP m0 + BitVec.ofNat 64 (16 * i), 16)]) (after b5 slotS) st7.data := by
    rw [after_eq run_b5]; exact hm7
  have hnws := (g.slot_ok hlt).1.2
  have hWs : ∀ q, Written (Env.ofMachine st6.data [(base m0 160, 160),
      (slP m0 + BitVec.ofNat 64 (16 * i), 16)]) (after b5 slotS) q →
      InRange (slP m0 + BitVec.ofNat 64 (16 * i)) 16 q := fun q hq ↦
    Written.inRange (r := 1) rfl hnws (by rw [after_eq run_b5]; decide +kernel) hq
  have hslot : ∀ q, InRange (slP m0 + BitVec.ofNat 64 (16 * i)) 16 q →
      InRange (slP m0) (16 * nP m0) q := fun q hq ↦ by
    obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists hq
    exact g.slot_in hlt hj
  have hs7 := hm7A.sameOutside hwf5
  have hk7 := hm7A.kept hwf5
  have hfr7 : FrP m0 st7.data := by
    refine Fr.ofBlockW hfr6 hm5' hm7 hwf5 rfl rfl ?_ rfl (by decide) g.hN slotsP8 ?_
    · intro r hr
      simp only [keepP, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      refine .inr ⟨by rcases hw with rfl | rfl <;> decide, fun b sz hb ↦ ?_⟩
      have hr1 : w.r = 1 := by rcases hw with rfl | rfl <;> rfl
      rw [hr1] at hb
      simp only [Env.ofMachine, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨by rcases hw with rfl | rfl <;> decide, fun j hj ↦ .inr (.inl (g.slot_in hlt hj))⟩
  have hts7 : TStateAt st7.data.dmem (tP m0) a { s1 with sponge := s1.sponge.squeeze.2 } :=
    g.t_keep hs7 hk7 (fun q hq ↦ .inr (.inl (hslot q (hWs q hq)))) hts6
  have hmsg7 : NativeRustcVm.EWsAt st7.data.dmem (base m0 160 + BitVec.ofNat 64 8) msg.toList :=
    g.local_keep hfr6 (N' := 0) (by decide) (R := InRange (slP m0) (16 * nP m0))
      (fun q hq ↦ .inr (.inl hq))
      (NativeRustcVm.SameOutside.mono hs7 fun q hq ↦ .inl (hslot q (hWs q hq)))
      (by rw [NativeRustcVm.length_ewsBytes]; simp [hi.msz]; omega) hmsg6
  have hxs7 : NativeRustcVm.EWsAt st7.data.dmem (slP m0)
      (xs.push s1.sponge.squeeze.1).toList := by
    refine ewsAt_push (g.prefix_keep hlt (NativeRustcVm.SameOutside.mono hs7 hWs)
      (by simp [hi.xsz]) hxs6) ?_
    have w0 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm7 (r := 1) (o := 0) rfl
      (by decide) (v := .reg .X0) (by decide +kernel)
    have w8 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm7 (r := 1) (o := 8) rfl
      (by decide) (v := .reg .X1) (by decide +kernel)
    rw [NativeRustcVm.addr_add_zero] at w0
    rw [hi.xsz, NativeRustcVm.ewAt_iff]
    exact ⟨h60 ▸ w0, h61 ▸ w8⟩
  have hx0' : st7.data.regs.X0.toBitVec = base m0 160 + BitVec.ofNat 64 8 := by
    rw [show st7.data.regs.X0 = st7.data.regs.getXReg .X0 from rfl, hm7.regs .X0 _ rfl]
    simp [Sym.eval, Env.base, Env.ofMachine]
  have hx1' : st7.data.regs.X1 = m0.regs.X4 :=
    UInt64.toBitVec_inj.mp ((hm7.regs .X1 _ rfl).trans
      (congrArg UInt64.toBitVec ((hreg6 .X21 (.inr (.inr (.inl rfl)))).trans hi.x21)))
  have hx2' : st7.data.regs.X2 = s1.sponge.squeeze.1.c0 :=
    (UInt64.toBitVec_inj.mp ((hm7.regs .X2 _ rfl).trans rfl)).trans h60
  have hx3' : st7.data.regs.X3 = s1.sponge.squeeze.1.c1 :=
    (UInt64.toBitVec_inj.mp ((hm7.regs .X3 _ rfl).trans rfl)).trans h61
  have hx20' : (st7.data.regs.getXReg .X20).toBitVec =
      slP m0 + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [hm7.regs .X20 _ rfl]
    simp only [Sym.eval, Env.base, Env.ofMachine, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    rw [show (BitVec.ofInt 64 16) = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add_add]
    congr 2
  have hreg7 : ∀ r, r = .X19 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 →
      st7.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr
    refine Eq.trans ?_ (hreg6 r (by rcases hr with rfl | rfl | rfl | rfl <;> simp))
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact UInt64.toBitVec_inj.mp ((hm7.regs _ _ rfl).trans rfl)
  refine call_then hpc7 hpe (g.polyEvalPre hfr7 hx0' (by rw [hx1'])) fun st8 hpc8 hpost8 ↦ ?_
  have hsv8 := hpost8.2.2
  obtain ⟨hfr8, hsl8, ht8⟩ := g.afterPolyEval hfr7 hpost8 keepP_saved slotsP8
  have hev : ewRet st8.data = polyEval msg s1.sponge.squeeze.1 := by
    rw [hpost8.1]
    unfold slice ewArg
    rw [hx2', hx3', show st7.data.regs.X1.toNat = msg.toList.length by
      rw [hx1']; simp [hi.msz], hx0', NativeRustcVm.ewsOf_of_ewsAt hmsg7]
  -- `b6`: the claim, the next round or the end.
  have hwf8 := Bus.wf_frame (F := 160) hS (by decide) hfr8.kept
  have hm8 : Match (Env.ofMachine st8.data [(base m0 160, 160)]) frS st8.data :=
    Bus.match_frame hS (by decide) (by decide) hfr8.sp
  refine exec_at hk6 run_b6 hwf8 hpc8 hm8 fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨hfr9, hd9⟩ := frBlock hfr8 hS (by decide) (by decide) hm9 rfl rfl (by decide)
    (by decide)
  have hreg9 : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 →
      st9.data.regs.getXReg r = st7.data.regs.getXReg r := by
    intro r hr
    refine Eq.trans ?_ (hsv8.1 r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl))
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact UInt64.toBitVec_inj.mp ((hm9.regs _ _ rfl).trans rfl)
  have hx2 : st9.data.regs.X2 = (polyEval msg s1.sponge.squeeze.1).c0 := by
    rw [← hev]; exact UInt64.toBitVec_inj.mp ((hm9.regs .X2 _ rfl).trans rfl)
  have hx3 : st9.data.regs.X3 = (polyEval msg s1.sponge.squeeze.1).c1 := by
    rw [← hev]; exact UInt64.toBitVec_inj.mp ((hm9.regs .X3 _ rfl).trans rfl)
  have hrun9 : RoundsP a s m0 st9.data.dmem (i + 1) ⟨st9.data.regs.X2, st9.data.regs.X3⟩ := by
    rw [hx2, hx3]
    refine ⟨xs.push s1.sponge.squeeze.1, _, hi.run, by simp [hi.xsz], ?_, ?_⟩
    · rw [hd9]; exact hsl8 _ (by simp [hi.xsz]; omega) hxs7
    · rw [hd9]; exact ht8 _ hts7
  have hx19 : st9.data.regs.getXReg .X19 = m0.regs.X0 := by
    rw [hreg9 .X19 (.inl rfl), hreg7 .X19 (.inl rfl)]; exact hi.x19
  have hx23 : (st9.data.regs.getXReg .X23).toBitVec = slP m0 + BitVec.ofNat 64 (16 * nP m0) := by
    rw [hreg9 .X23 (by simp), hreg7 .X23 (by simp)]; exact hi.x23
  have hx20 : (st9.data.regs.getXReg .X20).toBitVec = slP m0 + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [hreg9 .X20 (by simp)]; exact hx20'
  have hc : ((SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X20) (.reg .X23)).not.eval
      (Env.ofMachine st8.data [(base m0 160, 160)])) = !(i + 1 == nP m0) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
    have e20 : (st8.data.regs.getXReg .X20).toBitVec = slP m0 + BitVec.ofNat 64 (16 * (i + 1)) := by
      rw [hsv8.1 .X20 rfl]; exact hx20'
    have e23 : (st8.data.regs.getXReg .X23).toBitVec = slP m0 + BitVec.ofNat 64 (16 * nP m0) := by
      rw [hsv8.1 .X23 rfl, hreg7 .X23 (by simp)]; exact hi.x23
    show (!((st8.data.regs.getXReg .X20).toBitVec == (st8.data.regs.getXReg .X23).toBitVec)) = _
    rw [e20, e23, g.slot_eq_end hlt]
  simp only [PcOk] at hpc9
  rw [hc] at hpc9
  by_cases hlast : i + 1 = nP m0
  · simp only [hlast, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc9
    refine Eventually.done _ (.inl (.inr ⟨hpc9, hfr9, hx19, ?_⟩))
    rw [← hlast]; exact hrun9
  · have hb : (i + 1 == nP m0) = false := by simpa using hlast
    simp only [hb, Bool.not_false, ↓reduceIte] at hpc9
    refine Eventually.done _ (.inr ⟨hpc9.trans hl2, hfr9, by omega, hx19, hx20, ?_, ?_, hx23,
      hrun9⟩)
    · rw [hreg9 .X21 (by simp), hreg7 .X21 (by simp)]; exact hi.x21
    · rw [hreg9 .X22 (by simp), hreg7 .X22 (by simp)]; exact hi.x22

end

end NativeRustcVmArm.Sumcheck.Plain
