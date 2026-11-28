module

public import NativeRustcVmArm.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmArm.Whir.FinalLevel.Core

/-!
# `final_level`: the point

`point`: from `b17`, the point (`Buf<EW, 30>` at the frame's byte `1576`) set to the `α`s
(`b17`, `extend`; `b18`) and extended by the tail (`b19`, `extend`; `b20`), to `b21`.
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.FinalLevel
open NativeRustcVmArm.Transcript (known_ptr load_ofMachine eval_ptr wordAt_write load_of_wordAt)

public section

theorem slice_toList {m : MachineData} {u n : UInt64} {x : BitVec 64} {xs : List EW}
    (hu : u.toBitVec = x) (hn : n.toNat = xs.length) (h : NativeRustcVm.EWsAt m.dmem x xs) :
    (slice m u n).toList = xs := by
  unfold slice
  rw [hu, hn, NativeRustcVm.ewsOf_of_ewsAt h]

theorem bufEWOf_eq {d : Mem 64} {p : BitVec 64} {xs : List EW}
    (h : NativeRustcVm.BufEWAt d p 30 xs) : NativeRustcVm.bufEWOf d p = xs := by
  unfold NativeRustcVm.bufEWOf
  have hl : xs.length ≤ 30 := h.1
  rw [NativeRustcVm.wordOf_of_wordAt h.2.1, Nat.toUInt64, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega), NativeRustcVm.ewsOf_of_ewsAt h.2.2]

theorem bufEWOf_zero {d : Mem 64} {p : BitVec 64} (h : NativeRustcVm.WordAt d p 0) :
    NativeRustcVm.bufEWOf d p = [] := by
  unfold NativeRustcVm.bufEWOf
  rw [NativeRustcVm.wordOf_of_wordAt h]
  rfl

theorem tbz_one [Labels] {env : Env} (h : env.regs .X0 = (1 : UInt64).toBitVec) :
    SBool.eval env (.not (.bit .W32 (.reg .X0) 0)) = false :=
  (tbz_ok (b := true) h)

variable [Host] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The point.** -/
theorem point (hp : Placed code k) (c : Ctx a s0 level ba b w rounds m0)
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    {st : MachineState} {folded tail : Array EW} {claim : EW} {s5 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b17Offset)) (hc : Core level m0 st.data folded)
    (htn : tail.size = mu m0)
    (htail : NativeRustcVm.EWsAt st.data.dmem (loc m0 1096) tail.toList)
    (hcl : NativeRustcVm.EWAt st.data.dmem (loc m0 2072) claim)
    (hts : TStateAt st.data.dmem (tA m0) a s5)
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b21Offset) →
      Core level m0 st'.data folded → st'.data.regs.X22.toBitVec = loc m0 1576 →
      st'.data.regs.X23 = claim.c0 → st'.data.regs.X24 = claim.c1 →
      NativeRustcVm.EWsAt st'.data.dmem (loc m0 1096) tail.toList →
      NativeRustcVm.BufEWAt st'.data.dmem (loc m0 1576) 30 (w.alphas ++ tail).toList →
      TStateAt st'.data.dmem (tA m0) a s5 →
      Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st := by
  have hfo := c.two_mu_le
  have hmu6 := mu_le hfo
  have hal := c.alphas
  have hf := hc.fr
  have hsp := m0.regs.SP.toNat_lt
  have hN := c.hN'
  -- `b17`: the point zeroed, `extend(&point, alphas)`.
  have x27 : (st.data.regs.getXReg .X27).toBitVec = pA m0 :=
    congrArg UInt64.toBitVec hc.base.x27
  have hin : WhirIn m0 (pA m0) 24 finalLevelStack := whirIn_pre c.pIn (by decide)
  have hwf := c.wf1 hf hin
  have hm := c.match1 (n := 24) hf x27
  refine exec_at (inf hp b17_in_code (by simp [b17])) run_b17 hwf hpc hm
    fun st1 hm1 hpc1 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b17Offset + b17.length = k + NativeRustcVmArm.Vm.FinalLevel.b18Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b17_next]] at hpc1
  have hS : ∀ w ∈ (after b17 (wS 24)).mem, w.r = 0 ∧ w.off + w.n ≤ 2576 := by
    rw [after_eq run_b17]; decide +kernel
  have hS' : ∀ w ∈ (after b17 (wS 24)).mem, w.r = 0 ∧ w.off + w.n ≤ 2672 := fun w hw ↦
    ⟨(hS w hw).1, by have := (hS w hw).2; omega⟩
  have hf1 : FFr m0 st1.data := c.fr_block hf hm hm1 hwf rfl
    (by rw [← after_eq run_b17]; exact hS)
  have hc1 : Core level m0 st1.data folded :=
    hc.saved hf1 (fun r hr ↦ by
      simp only [coreRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact reg_of hm1 rfl rfl
        | exact UInt64.toBitVec_inj.mp ((reg_val hm1 (r := .X27) (v := .ptr 1 0) rfl).trans
            ((eval_ptr rfl).trans x27.symm)))
      (Ctx.same_block hm1 hwf (by decide +kernel) (by decide)) hfo
  have hts1 : TStateAt st1.data.dmem (tA m0) a s5 :=
    c.ts_block hm1 hwf (by rw [← after_eq run_b17]; exact hS') hts
  have htail1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 1096) tail.toList :=
    ewsAt_same htail (Ctx.same_block hm1 hwf (o := 1096) (len := 480) (by decide +kernel)
      (by decide)) (by rw [Array.length_toList]; omega)
  obtain ⟨hcl0, hcl1'⟩ := ewAt_iff.mp hcl
  rw [loc_off] at hcl1'
  have x23 : st1.data.regs.X23 = claim.c0 := UInt64.toBitVec_inj.mp
    ((reg_val hm1 (r := .X23) (v := .load 0 2072 8) rfl).trans
      (load_ofMachine (r := 0) (o := 2072) rfl hcl0))
  have x24 : st1.data.regs.X24 = claim.c1 := UInt64.toBitVec_inj.mp
    ((reg_val hm1 (r := .X24) (v := .load 0 2080 8) rfl).trans
      (load_ofMachine (r := 0) (o := 2080) rfl hcl1'))
  have x22 : st1.data.regs.X22.toBitVec = loc m0 1576 :=
    reg_val hm1 (r := .X22) (v := .ptr 0 1576) rfl
  have x0 : st1.data.regs.X0.toBitVec = loc m0 1576 :=
    reg_val hm1 (r := .X0) (v := .ptr 0 1576) rfl
  have hw0 : NativeRustcVm.WordAt st1.data.dmem (loc m0 1576) 0 :=
    wordAt_write hm1 (r := 0) (o := 1576) (b := base m0 2672) (sz := 2672) rfl (by decide)
      (v := .lit 0) (by rw [← after_eq run_b17]; decide +kernel)
  -- The `α`s.
  have hsa := (c.state_at hf).alphas
  have hn30 : w.alphas.size ≤ 30 := by have := hsa.1; rwa [Array.length_toList] at this
  have l16 : (fenv m0 st.data [(pA m0, 24)]).load 1 16 8 = w.alphas.size.toUInt64.toBitVec :=
    load_ofMachine (r := 1) (o := 16) rfl
      (by rw [← Array.length_toList]; exact (hsa.2.1 : NativeRustcVm.WordAt _ (off (pA m0) 16) _))
  have hlt : ((Sym.load 1 16 8).eval (fenv m0 st.data [(pA m0, 24)])).toNat < 31 := by
    show ((fenv m0 st.data [(pA m0, 24)]).load 1 16 8).toNat < 31
    rw [l16]
    simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  have e24 : off (off (pA m0) alphasOff) 8 = pA m0 + BitVec.ofNat 64 24 := by
    show pA m0 + BitVec.ofNat 64 16 + BitVec.ofNat 64 8 = _
    rw [BitVec.add_assoc]
    rfl
  have hA : NativeRustcVm.EWsAt st1.data.dmem (pA m0 + BitVec.ofNat 64 24) w.alphas.toList := by
    rw [← e24]; exact (c.state_at hf1).alphas.2.2
  have x1 : st1.data.regs.X1.toBitVec = pA m0 + BitVec.ofNat 64 24 := by
    show (st1.data.regs.getXReg .X1).toBitVec = _
    rw [reg_val hm1 (r := .X1) rfl, ite_ult hlt (by decide)]
    rfl
  have x2 : st1.data.regs.X2.toNat = w.alphas.size := by
    rw [← UInt64.toNat_toBitVec]
    show (st1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [reg_val hm1 (r := .X2) rfl, ite_ult hlt (by decide)]
    show ((fenv m0 st.data [(pA m0, 24)]).load 1 16 8).toNat = _
    rw [l16]
    simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  have hle : 2672 + bufExtendStack ≤ finalLevelStack := by decide
  have hpA : WhirIn m0 (pA m0 + BitVec.ofNat 64 24) (16 * w.alphas.size) finalLevelStack :=
    WhirLevels.whirIn_sub c.pIn (by unfold whirBytes; omega)
  have hext1 : ∀ m' : MachineData, BufEWExtendPost 30 st1.data m' →
      SameOutside st1.data.dmem m'.dmem fun q ↦
        InRange (stackBelow st1.data bufExtendStack) bufExtendStack q ∨
          InRange (loc m0 1576) 488 q := fun m' hq ↦
    NativeRustcVm.SameOutside.mono hq.2.1 fun q h ↦ by
      rcases h with h | h
      · rw [x0] at h; exact .inr h
      · exact .inl h
  refine c.call hf1 (lo := 1576) (n := 488) hle (by decide) hext hpc1 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono (hext1 m' hq) fun q h ↦ by
      rcases h with h | h
      · exact .inl h
      · exact .inr (.inl h), hq.2.2⟩) fun m2 hf2 hq hcs2 ↦ ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [x0, NativeRustcVm.wordOf_of_wordAt hw0]; decide
    · rw [x0]; exact (c.locIn hf1 hle (o := 1576) (n := 488) (by decide)).1
    · rw [x1, x2]; exact (c.whirIn' hf1 hle hpA).1
    · rw [x0, x1, x2]; exact NativeRustcVm.Apart.symm (c.apart_loc hpA (by decide))
  -- `b18`: the `α`s fit.
  have hs2 := hext1 m2 hq
  obtain ⟨hr2, -, hsv2⟩ := hq
  rw [x0, NativeRustcVm.wordOf_of_wordAt hw0, x2] at hr2
  rw [ite_eq_left (show (0 : UInt64).toNat + w.alphas.size ≤ 30 by
    simp only [UInt64.toNat_zero]; omega)] at hr2
  obtain ⟨h0, hbuf2⟩ := hr2
  rw [bufEWOf_zero hw0, slice_toList x1 x2 hA, List.nil_append] at hbuf2
  have hstk2 := c.call_stk hf1 hle (by decide) hs2
  have hk2 : NativeRustcVm.Layout.Same st1.data.dmem m2.dmem (loc m0 0) 1576 :=
    c.keep_call hf1 hle (lo := 1576) (n := 488) (NativeRustcVm.SameOutside.mono hs2
      fun q h ↦ by
        rcases h with h | h
        · exact .inl h
        · exact .inr (.inl h)) (by omega) (by decide) (by decide)
  have hsub : ∀ o len, o + len ≤ 1576 →
      NativeRustcVm.Layout.Same st1.data.dmem m2.dmem (loc m0 o) len := fun o len hol j hj ↦ by
    have := hk2 (o + j) (by omega)
    rwa [show loc m0 0 + BitVec.ofNat 64 (o + j) = loc m0 o + BitVec.ofNat 64 j by
      simp only [loc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_zero]] at this
  have hc2 : Core level m0 m2 folded := hc1.saved hf2 (core_cs hcs2) (hsub 40 1024 (by decide)) hfo
  refine c.fblock hp b18_in_code (by simp [b18]) run_b18 rfl rfl rfl hf2
    fun st3 hm3 hpc3 hf3 hd3 hk3 ↦ ?_
  simp only [PcOk] at hpc3
  rw [tbz_one (show (fenv m0 m2 []).regs .X0 = _ from congrArg UInt64.toBitVec h0)] at hpc3
  simp only [Bool.false_eq_true, ↓reduceIte, show k + NativeRustcVmArm.Vm.FinalLevel.b18Offset + b18.length = k + NativeRustcVmArm.Vm.FinalLevel.b19Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b18_next]] at hpc3
  -- `b19`: `extend(&point, tail)`.
  have hc3 : Core level m0 st3.data folded :=
    hc2.saved hf3 (fun r hr ↦ hk3 r (kept_of (by decide) r hr)) (fun j _ ↦ by rw [hd3]) hfo
  have hwf3 := c.fwf hf3
  refine exec_at (inf hp b19_in_code (by simp [b19])) run_b19 hwf3 hpc3 (c.fmatch hf3)
    fun st4 hm4 hpc4 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b19Offset + b19.length = k + NativeRustcVmArm.Vm.FinalLevel.b20Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b19_next]] at hpc4
  have hf4 : FFr m0 st4.data :=
    Fr.ofBlock hf3 (c.fmatch hf3) hm4 hwf3 rfl rfl rfl (fun _ h ↦ by cases h)
  have hd4' : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 rfl
  have hd4 : st4.data.dmem = m2.dmem := hd4'.trans hd3
  have hc4 : Core level m0 st4.data folded :=
    hc3.saved hf4 (fun r hr ↦ reg_of hm4 (kept_of (by decide) r hr) rfl)
      (fun j _ ↦ by rw [hd4']) hfo
  have y0 : st4.data.regs.X0.toBitVec = loc m0 1576 :=
    reg_val hm4 (r := .X0) (v := .ptr 0 1576) rfl
  have y1 : st4.data.regs.X1.toBitVec = loc m0 1096 :=
    reg_val hm4 (r := .X1) (v := .ptr 0 1096) rfl
  have y2 : st4.data.regs.X2.toNat = mu m0 := by
    rw [← UInt64.toNat_toBitVec]
    show (st4.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [reg_val hm4 (r := .X2) (v := .reg .X20) rfl]
    exact congrArg UInt64.toNat hc3.base.x20
  have hbuf4 : NativeRustcVm.BufEWAt st4.data.dmem (loc m0 1576) 30 w.alphas.toList := by
    rw [hd4]; exact hbuf2
  have htail4 : NativeRustcVm.EWsAt st4.data.dmem (loc m0 1096) tail.toList := by
    rw [hd4]
    exact ewsAt_same htail1 (hsub 1096 480 (by decide)) (by rw [Array.length_toList]; omega)
  have hext2 : ∀ m' : MachineData, BufEWExtendPost 30 st4.data m' →
      SameOutside st4.data.dmem m'.dmem fun q ↦
        InRange (stackBelow st4.data bufExtendStack) bufExtendStack q ∨
          InRange (loc m0 1576) 488 q := fun m' hq ↦
    NativeRustcVm.SameOutside.mono hq.2.1 fun q h ↦ by
      rcases h with h | h
      · rw [y0] at h; exact .inr h
      · exact .inl h
  have hwA : NativeRustcVm.WordAt st4.data.dmem (loc m0 1576) w.alphas.size.toUInt64 := by
    have := hbuf4.2.1; rwa [Array.length_toList] at this
  have hwn : (NativeRustcVm.wordOf st4.data.dmem (loc m0 1576)).toNat = w.alphas.size := by
    rw [NativeRustcVm.wordOf_of_wordAt hwA, Nat.toUInt64, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega)]
  refine c.call hf4 (lo := 1576) (n := 488) hle (by decide) hext hpc4 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono (hext2 m' hq) fun q h ↦ by
      rcases h with h | h
      · exact .inl h
      · exact .inr (.inl h), hq.2.2⟩) fun m5 hf5 hq5 hcs5 ↦ ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [y0, hwn]; exact hn30
    · rw [y0]; exact (c.locIn hf4 hle (o := 1576) (n := 488) (by decide)).1
    · rw [y1, y2]; exact (c.locIn hf4 hle (o := 1096) (n := 16 * mu m0) (by omega)).1
    · rw [y0, y1, y2]; exact NativeRustcVm.Apart.symm (c.apart_locs (by omega) (by decide))
  -- `b20`: the tail fits.
  have hs5 := hext2 m5 hq5
  obtain ⟨hr5, -, hsv5⟩ := hq5
  rw [y0, hwn, y2, ite_eq_left (show w.alphas.size + mu m0 ≤ 30 from hal)] at hr5
  obtain ⟨h5, hbuf5⟩ := hr5
  rw [bufEWOf_eq hbuf4, slice_toList y1 (by rw [y2, Array.length_toList, htn]) htail4,
    ← Array.toList_append] at hbuf5
  have hsub5 : ∀ o len, o + len ≤ 1576 →
      NativeRustcVm.Layout.Same st4.data.dmem m5.dmem (loc m0 o) len := fun o len hol ↦
    c.keep_call hf4 hle (lo := 1576) (n := 488) (NativeRustcVm.SameOutside.mono hs5
      fun q h ↦ by
        rcases h with h | h
        · exact .inl h
        · exact .inr (.inl h)) (by omega) (by decide) (by omega)
  have hc5 : Core level m0 m5 folded := hc4.saved hf5 (core_cs hcs5) (hsub5 40 1024 (by decide)) hfo
  refine c.fblock hp b20_in_code (by simp [b20]) run_b20 rfl rfl rfl hf5
    fun st6 hm6 hpc6 hf6 hd6 hk6 ↦ ?_
  simp only [PcOk] at hpc6
  rw [tbz_one (show (fenv m0 m5 []).regs .X0 = _ from congrArg UInt64.toBitVec h5)] at hpc6
  simp only [Bool.false_eq_true, ↓reduceIte, show k + NativeRustcVmArm.Vm.FinalLevel.b20Offset + b20.length = k + NativeRustcVmArm.Vm.FinalLevel.b21Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b20_next]] at hpc6
  have kk : ∀ r, calleeSaved r = true → st6.data.regs.getXReg r = st1.data.regs.getXReg r :=
    fun r hr ↦ (hk6 r (by cases r <;> rfl)).trans
      ((hcs5 r hr).trans ((reg_of hm4 (r := r) (v := .reg r) (by
        cases r <;> first | rfl | exact absurd hr (by decide)) rfl).trans
          ((hk3 r (by cases r <;> rfl)).trans
            (hcs2 r hr))))
  have htail6 : NativeRustcVm.EWsAt m5.dmem (loc m0 1096) tail.toList :=
    ewsAt_same htail4 (hsub5 1096 480 (by decide)) (by rw [Array.length_toList]; omega)
  refine cont st6 hpc6
    (hc5.saved hf6 (fun r hr ↦ hk6 r (kept_of (by decide) r hr)) (fun j _ ↦ by rw [hd6]) hfo)
    ((congrArg UInt64.toBitVec (kk .X22 rfl)).trans x22) ((kk .X23 rfl).trans x23)
    ((kk .X24 rfl).trans x24) (by rw [hd6]; exact htail6) (by rw [hd6]; exact hbuf5) ?_
  rw [hd6]
  refine c.ts_stk hsv5.2.2 (c.call_stk hf4 hle (by decide) hs5) ?_
  rw [hd4]
  exact c.ts_stk hsv2.2.2 hstk2 hts1

end

end NativeRustcVmArm.Whir.FinalLevel
