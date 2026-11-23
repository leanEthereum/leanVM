module

public import NativeRustcVmArm.Code.Vm.BasisWEval.Names
public import NativeRustcVmArm.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmArm.Whir.FinalLevel.Point

/-!
# `final_level`: the rotated point and the basis

`rotate`: from `b21`, the rotated point (`Buf<EW, 30>` at the frame's byte `2064`) set to the
point's entries from `laneFolds` (`b21`, `extend`; `b22`) then extended by those before
(`b23`, `extend`; `b24`), `BasisW::eval` of it into the `Option<EW>` at `2552` (`b25`; `b26`), to
`b27`.
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.FinalLevel
open NativeRustcVmArm.Transcript (known_ptr load_ofMachine eval_ptr wordAt_write load_of_wordAt)

public section

section
variable [Labels] (env : Env)

/-- `subs; csel lo`: the saturating difference. -/
theorem ev_satSub (x y : Sym) :
    ((Sym.ite (.cmp .ult .W64 x y) (.lit 0) (.bin .sub .W64 x y)).eval env).toNat =
      (x.eval env).toNat - (y.eval env).toNat := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  split <;> rename_i hc <;> simp only [BitVec.ult, decide_eq_true_eq] at hc
  · simp; omega
  · rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]

/-- `cmp; csel lo`: the minimum. -/
theorem ev_min (x y : Sym) :
    ((Sym.ite (.cmp .ult .W64 x y) x y).eval env).toNat =
      min (x.eval env).toNat (y.eval env).toNat := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
  split <;> rename_i hc <;> simp only [BitVec.ult, decide_eq_true_eq] at hc <;> omega

/-- `add p, s, lsl #4; csel lo`: the point's rest, or `8`. -/
theorem ev_above (n p s : Sym) :
    (Sym.ite (.cmp .ult .W64 n s) (.lit 8) (.bin .add .W64 p (.un (.shift .LSL 4) .W64 s))).eval
      env = if (n.eval env).toNat < (s.eval env).toNat then 8#64
      else p.eval env + BitVec.ofNat 64 (16 * (s.eval env).toNat) := by
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, UnOp.apply, shiftW, low_W64,
    ext_W64, BitVec.ult]
  by_cases hc : (n.eval env).toNat < (s.eval env).toNat
  · simp only [hc, decide_true, ↓reduceIte]
  · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega

end

theorem slice_eq {m : MachineData} {u n : UInt64} {x : BitVec 64} {xs : List EW}
    (hu : u.toBitVec = x) (hn : n.toNat = xs.length) (h : NativeRustcVm.EWsAt m.dmem x xs) :
    slice m u n = xs.toArray := by
  unfold slice
  rw [hu, hn, NativeRustcVm.ewsOf_of_ewsAt h]

theorem slice_zero {m : MachineData} {u n : UInt64} (hn : n.toNat = 0) : slice m u n = #[] := by
  unfold slice
  rw [hn]
  rfl

theorem extract_drop (xs : Array EW) (v : Nat) :
    xs.extract v xs.size = (xs.toList.drop v).toArray :=
  Array.ext' (by simp)

theorem extract_take (xs : Array EW) (v : Nat) : xs.extract 0 v = (xs.toList.take v).toArray :=
  Array.ext' (by simp)

theorem cbz_one [Labels] {env : Env} (h : env.regs .X0 = (1 : UInt64).toBitVec) :
    SBool.eval env (.cmp .eq .W32 (.reg .X0) (.lit 0)) = false :=
  cbz_ok (b := true) h

theorem one_iff {x q : BitVec 64} {n : Nat} :
    NativeRustcVm.InAny [⟨x, n⟩] q ↔ InRange x n q := by
  simp only [NativeRustcVm.inAny_cons_iff, NativeRustcVm.inAny_nil, or_false,
    NativeRustcVm.Region.Holds]
  exact Iff.rfl

variable [Host] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The rotated point and the basis.** -/
theorem rotate (hp : Placed code k) (c : Ctx a s0 level ba b w rounds m0)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hbw : ∀ ba b, Spec (Labels.label NativeRustcVmArm.Vm.BasisWEval.entryLabel) (BasisWEvalPre ba b) (BasisWEvalPost b))
    {st : MachineState} {folded tail : Array EW} {claim : EW} {s5 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b21Offset)) (hc : Core level m0 st.data folded)
    (hx22 : st.data.regs.X22.toBitVec = loc m0 1576)
    (hx23 : st.data.regs.X23 = claim.c0) (hx24 : st.data.regs.X24 = claim.c1)
    (htail : NativeRustcVm.EWsAt st.data.dmem (loc m0 1096) tail.toList)
    (hbuf : NativeRustcVm.BufEWAt st.data.dmem (loc m0 1576) 30 (w.alphas ++ tail).toList)
    (hts : TStateAt st.data.dmem (tA m0) a s5)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b27Offset) →
      Core level m0 st'.data folded → st'.data.regs.X22.toBitVec = loc m0 1584 →
      st'.data.regs.X29.toNat = (w.alphas ++ tail).size →
      st'.data.regs.X23 = claim.c0 → st'.data.regs.X24 = claim.c1 →
      NativeRustcVm.EWsAt st'.data.dmem (loc m0 1096) tail.toList →
      NativeRustcVm.EWsAt st'.data.dmem (loc m0 1584) (w.alphas ++ tail).toList →
      OptEWAt st'.data.dmem (loc m0 2552) (some (weightAt m0.regs.X4.toNat b w tail 0)) →
      TStateAt st'.data.dmem (tA m0) a s5 →
      Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st := by
  have hfo := c.two_mu_le
  have hf := hc.fr
  have hsp := m0.regs.SP.toNat_lt
  have hN := c.hN'
  set pt := w.alphas ++ tail with hpt_def
  set lf := m0.regs.X4.toNat with hlf_def
  have hn30 : pt.size ≤ 30 := by have := hbuf.1; rwa [Array.length_toList] at this
  have hpt : NativeRustcVm.EWsAt st.data.dmem (loc m0 1584) pt.toList := by
    have := hbuf.2.2
    rwa [show loc m0 1576 + 8#64 = loc m0 1584 from by
      show _ + _ + _ = _; rw [BitVec.add_assoc]; rfl] at this
  -- `b21`: the rotated point zeroed, `extend(&rotated, point.get(lf..))`.
  have hwf := c.fwf hf
  refine exec_at (inf hp b21_in_code (by simp [b21])) run_b21 hwf hpc (c.fmatch hf)
    fun st1 hm1 hpc1 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b21Offset + b21.length = k + NativeRustcVmArm.Vm.FinalLevel.b22Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b21_next]] at hpc1
  have hS : ∀ w ∈ (after b21 fS).mem, w.r = 0 ∧ w.off + w.n ≤ 2576 := by
    rw [after_eq run_b21]; decide +kernel
  have hS' : ∀ w ∈ (after b21 fS).mem, w.r = 0 ∧ w.off + w.n ≤ 2672 := fun w hw ↦
    ⟨(hS w hw).1, by have := (hS w hw).2; omega⟩
  have hf1 : FFr m0 st1.data := c.fr_block hf (c.fmatch hf) hm1 hwf rfl
    (by rw [← after_eq run_b21]; exact hS)
  have hlow : NativeRustcVm.Layout.Same st.data.dmem st1.data.dmem (loc m0 0) 2064 :=
    Ctx.same_block hm1 hwf (by decide +kernel) (by decide)
  have hsub1 : ∀ o len, o + len ≤ 2064 →
      NativeRustcVm.Layout.Same st.data.dmem st1.data.dmem (loc m0 o) len := fun o len hol j hj ↦ by
    have := hlow (o + j) (by omega)
    rwa [show loc m0 0 + BitVec.ofNat 64 (o + j) = loc m0 o + BitVec.ofNat 64 j by
      simp only [loc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_zero]] at this
  have hc1 : Core level m0 st1.data folded :=
    hc.saved hf1 (fun r hr ↦ reg_of hm1 (kept_of (by decide) r hr) rfl) (hsub1 40 1024 (by decide))
      hfo
  have hts1 : TStateAt st1.data.dmem (tA m0) a s5 :=
    c.ts_block hm1 hwf (by rw [← after_eq run_b21]; exact hS') hts
  have hpt1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 1584) pt.toList :=
    ewsAt_same hpt (hsub1 1584 480 (by decide)) (by rw [Array.length_toList]; omega)
  have htail1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 1096) tail.toList :=
    ewsAt_same htail (hsub1 1096 480 (by decide)) (by
      have : tail.size ≤ pt.size := by simp [hpt_def]
      rw [Array.length_toList]; omega)
  have hw0 : NativeRustcVm.WordAt st1.data.dmem (loc m0 2064) 0 :=
    wordAt_write hm1 (r := 0) (o := 2064) (b := base m0 2672) (sz := 2672) rfl (by decide)
      (v := .lit 0) (by rw [← after_eq run_b21]; decide +kernel)
  -- The values `b21` computes.
  have l1576 : (fenv m0 st.data []).load 0 1576 8 = pt.size.toUInt64.toBitVec :=
    load_ofMachine (r := 0) (o := 1576) rfl (by rw [← Array.length_toList]; exact hbuf.2.1)
  have hlt : ((Sym.load 0 1576 8).eval (fenv m0 st.data [])).toNat < 31 := by
    show ((fenv m0 st.data []).load 0 1576 8).toNat < 31
    rw [l1576]
    simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  have vN : ((Sym.ite (.cmp .ult .W64 (.load 0 1576 8) (.lit 31)) (.load 0 1576 8)
      (.lit 0)).eval (fenv m0 st.data [])).toNat = pt.size := by
    rw [ite_ult hlt (by decide)]
    show ((fenv m0 st.data []).load 0 1576 8).toNat = _
    rw [l1576]
    simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  have vP : (Sym.ite (.cmp .ult .W64 (.load 0 1576 8) (.lit 31))
      (.bin .add .W64 (.reg .X22) (.lit 8)) (.lit 8)).eval (fenv m0 st.data []) = loc m0 1584 := by
    rw [ite_ult hlt (by decide), ev_add]
    show st.data.regs.X22.toBitVec + _ = _
    rw [hx22]
    show _ + _ + _ = _
    rw [BitVec.add_assoc]
    rfl
  have v28 : ((Sym.reg .X28).eval (fenv m0 st.data [])).toNat = lf := by
    show (st.data.regs.getXReg .X28).toBitVec.toNat = _
    rw [show st.data.regs.getXReg .X28 = m0.regs.X4 from hc.base.x28]
    rfl
  have x0 : st1.data.regs.X0.toBitVec = loc m0 2064 :=
    reg_val hm1 (r := .X0) (v := .ptr 0 2064) rfl
  have x22 : st1.data.regs.X22.toBitVec = loc m0 1584 := (reg_val hm1 (r := .X22) rfl).trans vP
  have x25 : st1.data.regs.X25.toBitVec = loc m0 2064 :=
    reg_val hm1 (r := .X25) (v := .ptr 0 2064) rfl
  have x29 : st1.data.regs.X29.toNat = pt.size := by
    rw [← UInt64.toNat_toBitVec]
    show (st1.data.regs.getXReg .X29).toBitVec.toNat = _
    rw [reg_val hm1 (r := .X29) rfl]; exact vN
  have x1 : st1.data.regs.X1.toBitVec = if pt.size < lf then 8#64
      else loc m0 1584 + BitVec.ofNat 64 (16 * lf) := by
    show (st1.data.regs.getXReg .X1).toBitVec = _
    rw [reg_val hm1 (r := .X1) rfl, ev_above, vN, vP, v28]
  have x2 : st1.data.regs.X2.toNat = pt.size - lf := by
    rw [← UInt64.toNat_toBitVec]
    show (st1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [reg_val hm1 (r := .X2) rfl, ev_satSub, vN, v28]
  -- The rest of the point.
  have hrest : NativeRustcVm.EWsAt st1.data.dmem st1.data.regs.X1.toBitVec
      (pt.toList.drop lf) ∧ (slice st1.data st1.data.regs.X1 st1.data.regs.X2) =
        pt.extract lf pt.size := by
    rw [extract_drop]
    by_cases hlt' : pt.size < lf
    · have hd : pt.toList.drop lf = [] := List.drop_eq_nil_of_le (by simp; omega)
      rw [hd]
      exact ⟨NativeRustcVm.ewsAt_nil _ _, slice_zero (by rw [x2]; omega)⟩
    · rw [x1]; simp only [hlt', ↓reduceIte]
      have h := NativeRustcVm.EWsAt.drop hpt1 lf
      exact ⟨h, slice_eq (by rw [x1]; simp only [hlt', ↓reduceIte]) (by rw [x2]; simp) h⟩
  have hle : 2672 + bufExtendStack ≤ finalLevelStack := by decide
  have hloc := c.locIn hf1 hle (o := 1584) (n := 480) (by decide)
  have hrd : Readable st1.data st1.data.regs.X1.toBitVec (16 * st1.data.regs.X2.toNat) ∧
      Apart (loc m0 2064) (8 + 16 * 30) st1.data.regs.X1.toBitVec
        (16 * st1.data.regs.X2.toNat) := by
    rw [x2]
    by_cases hlt' : pt.size < lf
    · rw [x1, show pt.size - lf = 0 by omega]; simp only [hlt', ↓reduceIte]
      refine ⟨⟨fun i hi ↦ absurd hi (by omega), by unfold NoWrap; simp⟩, ?_⟩
      unfold Apart; rw [c.loc_nat (by decide)]; right; simp
    · rw [x1]; simp only [hlt', ↓reduceIte]
      have := WhirIn.sub hloc (o := 16 * lf) (n := 16 * (pt.size - lf)) (by omega)
      rw [show loc m0 1584 + BitVec.ofNat 64 (16 * lf) = loc m0 1584 + BitVec.ofNat 64 (16 * lf)
        from rfl] at this
      refine ⟨this.1, ?_⟩
      have hl := c.loc_nat (o := 1584) (by decide)
      unfold Apart
      rw [NativeRustcVm.toNat_add_ofNat (a := loc m0 1584) (i := 16 * lf) (by rw [hl]; omega), hl,
        c.loc_nat (by decide)]
      omega
  have hext1 : ∀ m' : MachineData, BufEWExtendPost 30 st1.data m' →
      SameOutside st1.data.dmem m'.dmem fun q ↦
        InRange (stackBelow st1.data bufExtendStack) bufExtendStack q ∨
          InRange (loc m0 2064) 488 q := fun m' hq ↦
    NativeRustcVm.SameOutside.mono hq.2.1 fun q h ↦ by
      rcases h with h | h
      · rw [x0] at h; exact .inr h
      · exact .inl h
  refine c.call hf1 (lo := 2064) (n := 488) hle (by decide) hext hpc1 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono (hext1 m' hq) fun q h ↦ by
      rcases h with h | h
      · exact .inl h
      · exact .inr (.inl h), hq.2.2⟩) fun m2 hf2 hq hcs2 ↦ ?_
  · refine ⟨?_, ?_, hrd.1, ?_⟩
    · rw [x0, NativeRustcVm.wordOf_of_wordAt hw0]; decide
    · rw [x0]; exact (c.locIn hf1 hle (o := 2064) (n := 488) (by decide)).1
    · rw [x0]; exact hrd.2
  -- `b22`: the rest fits.
  have hs2 := hext1 m2 hq
  obtain ⟨hr2, -, hsv2⟩ := hq
  rw [x0, NativeRustcVm.wordOf_of_wordAt hw0, x2,
    ite_eq_left (show (0 : UInt64).toNat + (pt.size - lf) ≤ 30 by
      simp only [UInt64.toNat_zero]; omega)] at hr2
  obtain ⟨h0, hbuf2⟩ := hr2
  rw [bufEWOf_zero hw0, hrest.2, List.nil_append] at hbuf2
  have hstk2 := c.call_stk hf1 hle (by decide) hs2
  have hsub2 : ∀ o len, o + len ≤ 2064 →
      NativeRustcVm.Layout.Same st1.data.dmem m2.dmem (loc m0 o) len := fun o len hol ↦
    c.keep_call hf1 hle (lo := 2064) (n := 488) (NativeRustcVm.SameOutside.mono hs2
      fun q h ↦ by
        rcases h with h | h
        · exact .inl h
        · exact .inr (.inl h)) (by omega) (by decide) (by omega)
  have hc2 : Core level m0 m2 folded := hc1.saved hf2 (core_cs hcs2) (hsub2 40 1024 (by decide)) hfo
  refine c.fblock hp b22_in_code (by simp [b22]) run_b22 rfl rfl rfl hf2
    fun st3 hm3 hpc3 hf3 hd3 hk3 ↦ ?_
  simp only [PcOk] at hpc3
  rw [cbz_one (show (fenv m0 m2 []).regs .X0 = _ from congrArg UInt64.toBitVec h0)] at hpc3
  simp only [Bool.false_eq_true, ↓reduceIte, show k + NativeRustcVmArm.Vm.FinalLevel.b22Offset + b22.length = k + NativeRustcVmArm.Vm.FinalLevel.b23Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b22_next]] at hpc3
  -- `b23`: `extend(&rotated, point.get(..lf).unwrap_or(point))`.
  have hwf3 := c.fwf hf3
  refine exec_at (inf hp b23_in_code (by simp [b23])) run_b23 hwf3 hpc3 (c.fmatch hf3)
    fun st4 hm4 hpc4 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b23Offset + b23.length = k + NativeRustcVmArm.Vm.FinalLevel.b24Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b23_next]] at hpc4
  have hf4 : FFr m0 st4.data :=
    Fr.ofBlock hf3 (c.fmatch hf3) hm4 hwf3 rfl rfl rfl (fun _ h ↦ by cases h)
  have hd4' : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 rfl
  have hd4 : st4.data.dmem = m2.dmem := hd4'.trans hd3
  have kk3 : ∀ r, calleeSaved r = true → st4.data.regs.getXReg r = st1.data.regs.getXReg r :=
    fun r hr ↦ (reg_of hm4 (r := r) (v := .reg r) (by
      cases r <;> first | rfl | exact absurd hr (by decide)) rfl).trans
        ((hk3 r (by cases r <;> rfl)).trans (hcs2 r hr))
  have hc4 : Core level m0 st4.data folded :=
    hc2.saved hf4 (fun r hr ↦ (reg_of hm4 (kept_of (by decide) r hr) rfl).trans
      (hk3 r (by cases r <;> rfl))) (fun j _ ↦ by rw [hd4]) hfo
  have y0 : st4.data.regs.X0.toBitVec = loc m0 2064 :=
    reg_val hm4 (r := .X0) (v := .ptr 0 2064) rfl
  have y1 : st4.data.regs.X1.toBitVec = loc m0 1584 :=
    (reg_val hm4 (r := .X1) (v := .reg .X22) rfl).trans
      ((congrArg UInt64.toBitVec ((hk3 .X22 rfl).trans (hcs2 .X22 rfl))).trans x22)
  have y2 : st4.data.regs.X2.toNat = min pt.size lf := by
    rw [← UInt64.toNat_toBitVec]
    show (st4.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [reg_val hm4 (r := .X2) rfl, ev_min]
    show min (st3.data.regs.getXReg .X29).toBitVec.toNat
      (st3.data.regs.getXReg .X28).toBitVec.toNat = _
    rw [UInt64.toNat_toBitVec, UInt64.toNat_toBitVec, (hk3 .X29 rfl).trans (hcs2 .X29 rfl),
      (hk3 .X28 rfl).trans hc2.base.x28]
    show min st1.data.regs.X29.toNat _ = _
    rw [x29]
  have hbuf4 : NativeRustcVm.BufEWAt st4.data.dmem (loc m0 2064) 30
      (pt.extract lf pt.size).toList := by rw [hd4]; exact hbuf2
  have hpt4 : NativeRustcVm.EWsAt st4.data.dmem (loc m0 1584) pt.toList := by
    rw [hd4]
    exact ewsAt_same hpt1 (hsub2 1584 480 (by decide)) (by rw [Array.length_toList]; omega)
  have htail4 : NativeRustcVm.EWsAt st4.data.dmem (loc m0 1096) tail.toList := by
    rw [hd4]
    have : tail.size ≤ pt.size := by simp [hpt_def]
    exact ewsAt_same htail1 (hsub2 1096 480 (by decide)) (by rw [Array.length_toList]; omega)
  have hcnt : (pt.extract lf pt.size).toList.length = pt.size - lf := by simp
  have hwn : (NativeRustcVm.wordOf st4.data.dmem (loc m0 2064)).toNat = pt.size - lf := by
    rw [NativeRustcVm.wordOf_of_wordAt hbuf4.2.1, hcnt, Nat.toUInt64, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega)]
  have htake := NativeRustcVm.EWsAt.take hpt4 (min pt.size lf)
  have hext2 : ∀ m' : MachineData, BufEWExtendPost 30 st4.data m' →
      SameOutside st4.data.dmem m'.dmem fun q ↦
        InRange (stackBelow st4.data bufExtendStack) bufExtendStack q ∨
          InRange (loc m0 2064) 488 q := fun m' hq ↦
    NativeRustcVm.SameOutside.mono hq.2.1 fun q h ↦ by
      rcases h with h | h
      · rw [y0] at h; exact .inr h
      · exact .inl h
  refine c.call hf4 (lo := 2064) (n := 488) hle (by decide) hext hpc4 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono (hext2 m' hq) fun q h ↦ by
      rcases h with h | h
      · exact .inl h
      · exact .inr (.inl h), hq.2.2⟩) fun m5 hf5 hq5 hcs5 ↦ ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [y0, hwn]; omega
    · rw [y0]; exact (c.locIn hf4 hle (o := 2064) (n := 488) (by decide)).1
    · rw [y1, y2]; exact (c.locIn hf4 hle (o := 1584) (n := 16 * min pt.size lf) (by omega)).1
    · rw [y0, y1, y2]; exact NativeRustcVm.Apart.symm (c.apart_locs (by omega) (by decide))
  -- `b24`: the rest fits.
  have hs5 := hext2 m5 hq5
  obtain ⟨hr5, -, hsv5⟩ := hq5
  rw [y0, hwn, y2, ite_eq_left (show pt.size - lf + min pt.size lf ≤ 30 by omega)] at hr5
  obtain ⟨h5, hbuf5⟩ := hr5
  have emin : (pt.toList.take (min pt.size lf)).toArray = pt.extract 0 lf := by
    rw [extract_take, ← Array.length_toList, ← List.take_take, List.take_of_length_le
      (by simp)]
  rw [bufEWOf_eq hbuf4, slice_eq y1 (by rw [y2]; simp) htake, emin,
    ← Array.toList_append] at hbuf5
  have hstk5 := c.call_stk hf4 hle (by decide) hs5
  have hsub5 : ∀ o len, o + len ≤ 2064 →
      NativeRustcVm.Layout.Same st4.data.dmem m5.dmem (loc m0 o) len := fun o len hol ↦
    c.keep_call hf4 hle (lo := 2064) (n := 488) (NativeRustcVm.SameOutside.mono hs5
      fun q h ↦ by
        rcases h with h | h
        · exact .inl h
        · exact .inr (.inl h)) (by omega) (by decide) (by omega)
  have hc5 : Core level m0 m5 folded := hc4.saved hf5 (core_cs hcs5) (hsub5 40 1024 (by decide)) hfo
  refine c.fblock hp b24_in_code (by simp [b24]) run_b24 rfl rfl rfl hf5
    fun st6 hm6 hpc6 hf6 hd6 hk6 ↦ ?_
  simp only [PcOk] at hpc6
  rw [tbz_one (show (fenv m0 m5 []).regs .X0 = _ from congrArg UInt64.toBitVec h5)] at hpc6
  simp only [Bool.false_eq_true, ↓reduceIte, show k + NativeRustcVmArm.Vm.FinalLevel.b24Offset + b24.length = k + NativeRustcVmArm.Vm.FinalLevel.b25Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b24_next]] at hpc6
  -- `b25`: `BasisW::eval(&out, basis, rotated)`.
  have kk6 : ∀ r, calleeSaved r = true → st6.data.regs.getXReg r = st1.data.regs.getXReg r :=
    fun r hr ↦ (hk6 r (by cases r <;> rfl)).trans ((hcs5 r hr).trans (kk3 r hr))
  have hc6 : Core level m0 st6.data folded :=
    hc5.saved hf6 (fun r hr ↦ hk6 r (kept_of (by decide) r hr)) (fun j _ ↦ by rw [hd6]) hfo
  have hwf6 := c.fwf hf6
  refine exec_at (inf hp b25_in_code (by simp [b25])) run_b25 hwf6 hpc6 (c.fmatch hf6)
    fun st7 hm7 hpc7 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b25Offset + b25.length = k + NativeRustcVmArm.Vm.FinalLevel.b26Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b25_next]] at hpc7
  have hf7 : FFr m0 st7.data :=
    Fr.ofBlock hf6 (c.fmatch hf6) hm7 hwf6 rfl rfl rfl (fun _ h ↦ by cases h)
  have hd7' : st7.data.dmem = st6.data.dmem := hm7.dmem_eq hwf6 rfl
  have hd7 : st7.data.dmem = m5.dmem := hd7'.trans hd6
  have hc7 : Core level m0 st7.data folded :=
    hc6.saved hf7 (fun r hr ↦ reg_of hm7 (kept_of (by decide) r hr) rfl)
      (fun j _ ↦ by rw [hd7']) hfo
  have hrot : NativeRustcVm.BufEWAt st7.data.dmem (loc m0 2064) 30
      (pt.extract lf pt.size ++ pt.extract 0 lf).toList := by rw [hd7]; exact hbuf5
  have hrn : (pt.extract lf pt.size ++ pt.extract 0 lf).toList.length ≤ 30 := hrot.1
  have hw6 : NativeRustcVm.WordAt st6.data.dmem (loc m0 2064)
      (pt.extract lf pt.size ++ pt.extract 0 lf).toList.length.toUInt64 := by
    rw [hd6]; exact hbuf5.2.1
  have l2064 : (fenv m0 st6.data []).load 0 2064 8 =
      (pt.extract lf pt.size ++ pt.extract 0 lf).toList.length.toUInt64.toBitVec :=
    load_ofMachine (r := 0) (o := 2064) rfl hw6
  have hlt2 : ((Sym.load 0 2064 8).eval (fenv m0 st6.data [])).toNat < 31 := by
    show ((fenv m0 st6.data []).load 0 2064 8).toNat < 31
    rw [l2064]
    simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  have z0 : st7.data.regs.X0.toBitVec = loc m0 2552 :=
    reg_val hm7 (r := .X0) (v := .ptr 0 2552) rfl
  have z1 : st7.data.regs.X1 = m0.regs.X5 :=
    (reg_of hm7 (r := .X1) (v := .reg .X21) rfl rfl).trans hc6.base.x21
  have z2 : st7.data.regs.X2.toBitVec = loc m0 2072 := by
    show (st7.data.regs.getXReg .X2).toBitVec = _
    rw [reg_val hm7 (r := .X2) rfl, ite_ult hlt2 (by decide), ev_add]
    rw [show (st6.data.regs.getXReg .X25).toBitVec = loc m0 2064 from
      (congrArg UInt64.toBitVec (kk6 .X25 rfl)).trans x25]
    show _ + _ + _ = _
    rw [BitVec.add_assoc]
    rfl
  have z3 : st7.data.regs.X3.toNat = (pt.extract lf pt.size ++ pt.extract 0 lf).toList.length := by
    rw [← UInt64.toNat_toBitVec]
    show (st7.data.regs.getXReg .X3).toBitVec.toNat = _
    rw [reg_val hm7 (r := .X3) rfl, ite_ult hlt2 (by decide)]
    show ((fenv m0 st6.data []).load 0 2064 8).toNat = _
    rw [l2064]
    simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  have hrot2 : NativeRustcVm.EWsAt st7.data.dmem (loc m0 2072)
      (pt.extract lf pt.size ++ pt.extract 0 lf).toList := by
    have := hrot.2.2
    rwa [show loc m0 2064 + 8#64 = loc m0 2072 from by
      show _ + _ + _ = _; rw [BitVec.add_assoc]; rfl] at this
  have hleB : 2672 + basisWEvalStack ≤ finalLevelStack := by decide
  have hso : ∀ m' : MachineData, BasisWEvalPost b st7.data m' →
      SameOutside st7.data.dmem m'.dmem fun q ↦
        InRange (stackBelow st7.data basisWEvalStack) basisWEvalStack q ∨
          InRange (loc m0 2552) 24 q := fun m' hq ↦
    NativeRustcVm.SameOutside.mono hq.2.1 fun q h ↦ by
      rcases h with h | h
      · rw [z0] at h; exact .inr (one_iff.mp h)
      · exact .inl h
  have hb := c.bp
  refine c.call hf7 (lo := 2552) (n := 24) hleB (by decide) (hbw ba b) hpc7 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono (hso m' hq) fun q h ↦ by
      rcases h with h | h
      · exact .inl h
      · exact .inr (.inl h), hq.2.2⟩) fun m8 hf8 hq8 hcs8 ↦ ?_
  · refine ⟨c.stackOk' hf7 hleB, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show BasisWAt st7.data.dmem st7.data.regs.X1.toBitVec ba b
      rw [z1]; exact c.basis_at hf7
    · show BasisIn st7.data st7.data.regs.X1.toBitVec ba basisWEvalStack
        st7.data.regs.X0.toBitVec 24
      rw [z1, z0]
      exact ⟨c.whirIn' hf7 hleB hb.1, c.apart_loc hb.1 (by decide), fun r hr ↦
        ⟨c.whirIn' hf7 hleB (hb.2.2 r hr).1, c.apart_loc (hb.2.2 r hr).1 (by decide)⟩⟩
    · show st7.data.regs.X3.toNat ≤ 64
      rw [z3]; omega
    · show SliceOk st7.data st7.data.regs.X2 st7.data.regs.X3 basisWEvalStack
      rw [show st7.data.regs.X2 = UInt64.ofBitVec (loc m0 2072) from
        UInt64.toBitVec_inj.mp z2]
      exact c.locSlice hf7 hleB (by rw [z3]; omega)
    · show WhirIn st7.data st7.data.regs.X0.toBitVec 24 basisWEvalStack
      rw [z0]; exact c.locIn hf7 hleB (by decide)
    · show BasisApart st7.data.regs.X1.toBitVec ba
      rw [z1]; exact c.bap
  -- `b26`: `Some`.
  have hs8 := hso m8 hq8
  obtain ⟨hopt, -, hsv8⟩ := hq8
  rw [z0, slice_eq z2 z3 hrot2, Array.toArray_toList, ← weightAt_zero] at hopt
  have hsub8 : ∀ o len, o + len ≤ 2552 →
      NativeRustcVm.Layout.Same st7.data.dmem m8.dmem (loc m0 o) len := fun o len hol ↦
    c.keep_call hf7 hleB (lo := 2552) (n := 24) (NativeRustcVm.SameOutside.mono hs8
      fun q h ↦ by
        rcases h with h | h
        · exact .inl h
        · exact .inr (.inl h)) (by omega) (by decide) (by omega)
  have hc8 : Core level m0 m8 folded := hc7.saved hf8 (core_cs hcs8) (hsub8 40 1024 (by decide)) hfo
  refine c.fblock hp b26_in_code (by simp [b26]) run_b26 rfl rfl rfl hf8
    fun st9 hm9 hpc9 hf9 hd9 hk9 ↦ ?_
  simp only [PcOk] at hpc9
  rw [cbz_load (load_of_wordAt hopt.1)] at hpc9
  simp only [show ((1 : UInt64) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    show k + NativeRustcVmArm.Vm.FinalLevel.b26Offset + b26.length = k + NativeRustcVmArm.Vm.FinalLevel.b27Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b26_next]] at hpc9
  have kk9 : ∀ r, calleeSaved r = true → st9.data.regs.getXReg r = st1.data.regs.getXReg r :=
    fun r hr ↦ (hk9 r (by cases r <;> first | rfl | exact absurd hr (by decide))).trans
      ((hcs8 r hr).trans ((reg_of hm7 (r := r)
      (v := .reg r) (by cases r <;> first | rfl | exact absurd hr (by decide)) rfl).trans
        (kk6 r hr)))
  have kk1 : ∀ r ∈ [XReg.X23, XReg.X24], st1.data.regs.getXReg r = st.data.regs.getXReg r :=
    fun r hr ↦ reg_of hm1 (r := r) (v := .reg r) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> rfl) rfl
  have hts9 : TStateAt st9.data.dmem (tA m0) a s5 := by
    rw [hd9]
    refine c.ts_stk hsv8.2.2 (c.call_stk hf7 hleB (by decide) hs8) ?_
    rw [hd7]
    refine c.ts_stk hsv5.2.2 hstk5 ?_
    rw [hd4]
    exact c.ts_stk hsv2.2.2 hstk2 hts1
  refine cont st9 hpc9
    (hc8.saved hf9 (fun r hr ↦ hk9 r (kept_of (by decide) r hr)) (fun j _ ↦ by rw [hd9]) hfo)
    ((congrArg UInt64.toBitVec (kk9 .X22 rfl)).trans x22)
    (by rw [show st9.data.regs.X29 = _ from kk9 .X29 rfl]; exact x29)
    ((kk9 .X23 rfl).trans ((kk1 .X23 (by simp)).trans hx23))
    ((kk9 .X24 rfl).trans ((kk1 .X24 (by simp)).trans hx24)) ?_ ?_ (by rw [hd9]; exact hopt) hts9
  · have : tail.size ≤ pt.size := by simp [hpt_def]
    have h7 : NativeRustcVm.EWsAt st7.data.dmem (loc m0 1096) tail.toList := by
      rw [hd7]
      exact ewsAt_same htail4 (hsub5 1096 480 (by decide)) (by rw [Array.length_toList]; omega)
    rw [hd9]
    exact ewsAt_same h7 (hsub8 1096 480 (by decide)) (by rw [Array.length_toList]; omega)
  · have h7 : NativeRustcVm.EWsAt st7.data.dmem (loc m0 1584) pt.toList := by
      rw [hd7]
      exact ewsAt_same hpt4 (hsub5 1584 480 (by decide)) (by rw [Array.length_toList]; omega)
    rw [hd9]
    exact ewsAt_same h7 (hsub8 1584 480 (by decide)) (by rw [Array.length_toList]; omega)

end

end NativeRustcVmArm.Whir.FinalLevel
