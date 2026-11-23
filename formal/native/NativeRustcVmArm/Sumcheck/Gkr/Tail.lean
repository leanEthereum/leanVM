module

public import NativeRustcVmArm.Code.Vm.PolyEval.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfGkrStep.Names
public import NativeRustcVmArm.Sumcheck.Gkr.Head

/-!
# `sumcheck` with `gkr_step`'s closure: a round's challenge and claim

From `b7` (`Mid`): `squeeze` the challenge, `b8` stores it in slot `i` and calls `poly_eval` for
the next claim, `b9` goes back to the loop's head, or on to `.L7` after the last round
(`tail_spec`).
-/

namespace NativeRustcVmArm.Sumcheck.Gkr

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SumcheckOfGkrStep
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck

@[expose] public section

/-- The registers the loop keeps across a round's calls. -/
def loopRegs : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26]

end

public section

variable [Host] {a : DecArea} {s : TState} {pt : Array EW} {n : Nat} {m0 : MachineData} {k : Nat}

/-- **A round's challenge and claim**: from `b4`, the next round's head or `.L4`. -/
theorem tail_spec (hp : Placed code k)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpe : Spec (Labels.label NativeRustcVmArm.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost)
    (hpre : SumcheckGkrPre a s pt n m0) {i : Nat} {xs msg : Array EW} {s1 : TState}
    {m : MachineData} (hi : Mid a s pt n m0 i xs msg s1 m) :
    Eventually (step1 Host.exe)
      (fun st ↦ Goal a s pt n m0 k st ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b2Offset) ∧ Inv a s pt n m0 (i + 1) st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b7Offset)⟩ := by
  have g := geo hpre
  have hS := hpre.1.1
  have hlt := hi.lt
  have hc5 := g.ok.2.2.2.2.2.1
  unfold maxCount at hc5
  have hk4 : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b7Offset) := b7_in_code.trans hp.1 (by simp [b7])
  have hk5 : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b8Offset) := b8_in_code.trans hp.1 (by simp [b8])
  have hk6 : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b9Offset) := b9_in_code.trans hp.1 (by simp [b9])
  have hl2 : Labels.label NativeRustcVmArm.Vm.SumcheckOfGkrStep.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b2Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.SumcheckOfGkrStep.b2Offset) NativeRustcVmArm.Vm.SumcheckOfGkrStep.label_2_at
  -- `b4`: `squeeze`.
  have hwf4 := Bus.wf_frame (F := 192) hS (by decide) hi.fr.kept
  have hm4 : Match (Env.ofMachine m [(base m0 192, 192)]) frS m :=
    Bus.match_frame hS (by decide) (by decide) hi.fr.sp
  refine exec_then hk4 run_b7 hwf4 hm4 fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hfr5, hd5⟩ := frBlock hi.fr hS (by decide) (by decide) hm5 rfl rfl (by decide)
    (by decide)
  have hts5 : TStateAt st5.data.dmem (tG m0) a s1 := by rw [hd5]; exact hi.ts
  have hx0 : st5.data.regs.X0.toBitVec = tG m0 :=
    (hm5.regs .X0 _ rfl).trans (congrArg UInt64.toBitVec hi.x23)
  have hreg5 : ∀ r ∈ loopRegs, st5.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr
    simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact UInt64.toBitVec_inj.mp ((hm5.regs _ _ rfl).trans rfl)
  refine call_then hpc5 (hsq s1.sponge) (g.squeezePre hfr5 hts5 hx0) fun st6 hpc6 hpost6 ↦ ?_
  have hsv6 := hpost6.2.2.2.2
  obtain ⟨hfr6, h60, h61, hts6, hsl6, hloc6⟩ :=
    g.afterSqueeze hfr5 hts5 hpost6 hx0 keepG_saved slotsG8
  have hreg6 : ∀ r ∈ loopRegs, st6.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    (hsv6.1 r (by
      simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans (hreg5 r hr)
  have hxs6 : NativeRustcVm.EWsAt st6.data.dmem (slG m0) xs.toList :=
    hsl6 xs.toList (by simp [hi.xsz]; omega) (by rw [hd5]; exact hi.xs)
  have hmsg6 : NativeRustcVm.EWsAt st6.data.dmem (base m0 192 + BitVec.ofNat 64 8) msg.toList :=
    hloc6 8 _ (by rw [NativeRustcVm.length_ewsBytes]; simp [hi.msz]; omega)
      (by rw [hd5]; exact hi.msg)
  -- `b5`: the challenge into slot `i`, `poly_eval`.
  have hx20 : (st6.data.regs.getXReg .X20).toBitVec = slG m0 + BitVec.ofNat 64 (16 * i) := by
    rw [hreg6 .X20 (by simp [loopRegs])]; exact hi.x20
  have hwf5 : (Env.ofMachine st6.data [(base m0 192, 192),
      (slG m0 + BitVec.ofNat 64 (16 * i), 16)]).WF :=
    Bus.wf_frame2 hS (by decide) hfr6.kept (g.slot_ok hlt).1 (g.slot_ok hlt).2
  have hm5' : Match (Env.ofMachine st6.data [(base m0 192, 192),
      (slG m0 + BitVec.ofNat 64 (16 * i), 16)]) slotS st6.data := by
    have := Bus.match_frame2 (r := .X20) (n := 16) hS (by decide) (by decide) hfr6.sp
    rwa [hx20] at this
  refine exec_at hk5 run_b8 hwf5 hpc6 hm5' fun st7 hm7 hpc7 ↦ ?_
  have hm7A : Match (Env.ofMachine st6.data [(base m0 192, 192),
      (slG m0 + BitVec.ofNat 64 (16 * i), 16)]) (after b8 slotS) st7.data := by
    rw [after_eq run_b8]; exact hm7
  have hnws := (g.slot_ok hlt).1.2
  have hWs : ∀ q, Written (Env.ofMachine st6.data [(base m0 192, 192),
      (slG m0 + BitVec.ofNat 64 (16 * i), 16)]) (after b8 slotS) q →
      InRange (slG m0 + BitVec.ofNat 64 (16 * i)) 16 q := fun q hq ↦
    Written.inRange (r := 1) rfl hnws (by rw [after_eq run_b8]; decide +kernel) hq
  have hslot : ∀ q, InRange (slG m0 + BitVec.ofNat 64 (16 * i)) 16 q →
      InRange (slG m0) (16 * n) q := fun q hq ↦ by
    obtain ⟨j, hj, rfl⟩ := NativeRustcVm.InRange.exists hq
    exact g.slot_in hlt hj
  have hs7 := hm7A.sameOutside hwf5
  have hk7 := hm7A.kept hwf5
  have hfr7 : FrG m0 n st7.data := by
    refine Fr.ofBlockW hfr6 hm5' hm7 hwf5 rfl rfl ?_ rfl (by decide) g.hN slotsG8 ?_
    · intro r hr
      simp only [keepG, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      refine .inr ⟨by rcases hw with rfl | rfl <;> decide, fun b sz hb ↦ ?_⟩
      have hr1 : w.r = 1 := by rcases hw with rfl | rfl <;> rfl
      rw [hr1] at hb
      simp only [Env.ofMachine, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨by rcases hw with rfl | rfl <;> decide, fun j hj ↦ .inl (g.slot_in hlt hj)⟩
  have hts7 : TStateAt st7.data.dmem (tG m0) a { s1 with sponge := s1.sponge.squeeze.2 } :=
    g.t_keep hs7 hk7 (fun q hq ↦ .inr (.inl (hslot q (hWs q hq)))) hts6
  have hmsg7 : NativeRustcVm.EWsAt st7.data.dmem (base m0 192 + BitVec.ofNat 64 8) msg.toList :=
    g.local_keep hfr6 (N' := 0) (by decide) (R := InRange (slG m0) (16 * n))
      (fun q hq ↦ .inl hq)
      (NativeRustcVm.SameOutside.mono hs7 fun q hq ↦ .inl (hslot q (hWs q hq)))
      (by rw [NativeRustcVm.length_ewsBytes]; simp [hi.msz]; omega) hmsg6
  have hxs7 : NativeRustcVm.EWsAt st7.data.dmem (slG m0)
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
  have hx0' : st7.data.regs.X0.toBitVec = base m0 192 + BitVec.ofNat 64 8 := by
    rw [show st7.data.regs.X0 = st7.data.regs.getXReg .X0 from rfl, hm7.regs .X0 _ rfl]
    simp [Sym.eval, Env.base, Env.ofMachine]
  have hx1' : st7.data.regs.X1 = m0.regs.X4 :=
    UInt64.toBitVec_inj.mp ((hm7.regs .X1 _ rfl).trans
      (congrArg UInt64.toBitVec ((hreg6 .X22 (by simp [loopRegs])).trans hi.x22)))
  have hx2' : st7.data.regs.X2 = s1.sponge.squeeze.1.c0 :=
    (UInt64.toBitVec_inj.mp ((hm7.regs .X2 _ rfl).trans rfl)).trans h60
  have hx3' : st7.data.regs.X3 = s1.sponge.squeeze.1.c1 :=
    (UInt64.toBitVec_inj.mp ((hm7.regs .X3 _ rfl).trans rfl)).trans h61
  have hx20' : (st7.data.regs.getXReg .X20).toBitVec =
      slG m0 + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [hm7.regs .X20 _ rfl]
    simp only [Sym.eval, Env.base, Env.ofMachine, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    rw [show (BitVec.ofInt 64 16) = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add_add]
    congr 2
  have hreg7 : ∀ r ∈ loopRegs, r ≠ .X20 → st7.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr h20
    refine Eq.trans ?_ (hreg6 r hr)
    simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd rfl h20
      | exact UInt64.toBitVec_inj.mp ((hm7.regs _ _ rfl).trans rfl)
  refine call_then hpc7 hpe (g.polyEvalPre hfr7 hx0' (by rw [hx1'])) fun st8 hpc8 hpost8 ↦ ?_
  have hsv8 := hpost8.2.2
  obtain ⟨hfr8, hsl8, ht8⟩ := g.afterPolyEval hfr7 hpost8 keepG_saved slotsG8
  have hev : ewRet st8.data = polyEval msg s1.sponge.squeeze.1 := by
    rw [hpost8.1]
    unfold slice ewArg
    rw [hx2', hx3', show st7.data.regs.X1.toNat = msg.toList.length by
      rw [hx1']; simp [hi.msz], hx0', NativeRustcVm.ewsOf_of_ewsAt hmsg7]
  -- `b6`: the claim, the next round or the end.
  have hwf8 := Bus.wf_frame (F := 192) hS (by decide) hfr8.kept
  have hm8 : Match (Env.ofMachine st8.data [(base m0 192, 192)]) frS st8.data :=
    Bus.match_frame hS (by decide) (by decide) hfr8.sp
  refine exec_at hk6 run_b9 hwf8 hpc8 hm8 fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨hfr9, hd9⟩ := frBlock hfr8 hS (by decide) (by decide) hm9 rfl rfl (by decide)
    (by decide)
  have hreg9 : ∀ r, r = .X19 ∨ r = .X20 ∨ r = .X21 ∨ r = .X22 ∨ r = .X23 ∨ r = .X25 →
      st9.data.regs.getXReg r = st7.data.regs.getXReg r := by
    intro r hr
    refine Eq.trans ?_ (hsv8.1 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl))
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact UInt64.toBitVec_inj.mp ((hm9.regs _ _ rfl).trans rfl)
  have hx2 : st9.data.regs.X2 = (polyEval msg s1.sponge.squeeze.1).c0 := by
    rw [← hev]; exact UInt64.toBitVec_inj.mp ((hm9.regs .X2 _ rfl).trans rfl)
  have hx3 : st9.data.regs.X3 = (polyEval msg s1.sponge.squeeze.1).c1 := by
    rw [← hev]; exact UInt64.toBitVec_inj.mp ((hm9.regs .X3 _ rfl).trans rfl)
  have hrun9 : RoundsG a s pt m0 st9.data.dmem (i + 1) ⟨st9.data.regs.X2, st9.data.regs.X3⟩ := by
    rw [hx2, hx3]
    refine ⟨xs.push s1.sponge.squeeze.1, _, hi.run, by simp [hi.xsz], ?_, ?_⟩
    · rw [hd9]; exact hsl8 _ (by simp [hi.xsz]; omega) hxs7
    · rw [hd9]; exact ht8 _ hts7
  have hx19 : st9.data.regs.getXReg .X19 = m0.regs.X0 := by
    rw [hreg9 .X19 (by simp), hreg7 .X19 (by simp [loopRegs]) (by decide)]; exact hi.x19
  have hx25 : (st9.data.regs.getXReg .X25).toBitVec = slG m0 + BitVec.ofNat 64 (16 * n) := by
    rw [hreg9 .X25 (by simp), hreg7 .X25 (by simp [loopRegs]) (by decide)]; exact hi.x25
  have hx20 : (st9.data.regs.getXReg .X20).toBitVec = slG m0 + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [hreg9 .X20 (by simp)]; exact hx20'
  have hc : ((SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X20) (.reg .X25)).not.eval
      (Env.ofMachine st8.data [(base m0 192, 192)])) = !(i + 1 == n) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
    have e20 : (st8.data.regs.getXReg .X20).toBitVec = slG m0 + BitVec.ofNat 64 (16 * (i + 1)) := by
      rw [hsv8.1 .X20 rfl]; exact hx20'
    have e23 : (st8.data.regs.getXReg .X25).toBitVec = slG m0 + BitVec.ofNat 64 (16 * n) := by
      rw [hsv8.1 .X25 rfl, hreg7 .X25 (by simp [loopRegs]) (by decide)]; exact hi.x25
    show (!((st8.data.regs.getXReg .X20).toBitVec == (st8.data.regs.getXReg .X25).toBitVec)) = _
    rw [e20, e23, g.slot_eq_end hlt]
  simp only [PcOk] at hpc9
  rw [hc] at hpc9
  by_cases hlast : i + 1 = n
  · simp only [hlast, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc9
    refine Eventually.done _ (.inl (.inr ⟨hpc9, hfr9, hx19, ?_⟩))
    rw [← hlast]; exact hrun9
  · have hb : (i + 1 == n) = false := by simpa using hlast
    simp only [hb, Bool.not_false, ↓reduceIte] at hpc9
    refine Eventually.done _ (.inr ⟨hpc9.trans hl2, hfr9, by omega, hx19, hx20, ?_, ?_, ?_, ?_,
      hx25, ?_, hrun9⟩)
    · rw [hreg9 .X21 (by simp), hreg7 .X21 (by simp [loopRegs]) (by decide)]; exact hi.x21
    · rw [hreg9 .X22 (by simp), hreg7 .X22 (by simp [loopRegs]) (by decide)]; exact hi.x22
    · rw [hreg9 .X23 (by simp), hreg7 .X23 (by simp [loopRegs]) (by decide)]; exact hi.x23
    · rw [UInt64.toNat, hm9.regs .X24 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
      show ((st8.data.regs.getXReg .X24).toBitVec + 1#64).toNat = i + 1
      rw [hsv8.1 .X24 rfl, hreg7 .X24 (by simp [loopRegs]) (by decide)]
      have h24 : (m.regs.getXReg .X24).toBitVec.toNat = i := hi.x24
      have hn64 : n < 2 ^ 64 := hpre.2.2.2.2.2.2.2.1
      rw [BitVec.toNat_add, h24]
      simp only [BitVec.toNat_ofNat]
      omega
    · rw [hm9.regs .X26 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
      show (st8.data.regs.getXReg .X26).toBitVec + BitVec.ofNat 64 16 = _
      rw [hsv8.1 .X26 rfl, hreg7 .X26 (by simp [loopRegs]) (by decide), hi.x26,
        NativeRustcVm.addr_add_add]
      congr 2

end

end NativeRustcVmArm.Sumcheck.Gkr
