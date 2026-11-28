module

public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Tables.TableTerms.Iter
public import NativeRustcVmArm.Tables.TableTerms.Exit

/-!
# `table_terms`: table `i`'s evaluations

From the loop head before table `i`: `b1` reads the table's width (at most `92`, so it goes on),
`b2` writes it as the length of entry `i`'s `values` and calls `read_scalars` into them, `b3`
leaves with `None` when it failed (the model's run fails too, `exit_none`) and goes on with `It`
otherwise (`read_step`).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVmArm.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf BufEWAt)
open NativeRustcVmArm.Bus (after)
open NativeRustcVmArm.Sumcheck (Ctx At)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

omit [Host] in
theorem rs_le : 288 + readScalarsStack ≤ N := by rw [N_eq]; decide

omit [Host] in
/-- A failed table: the whole run fails. -/
theorem R_none (hh : heights.size = 6) (hf : forms.size = 6) {i : Nat} (hi : i < 6) {c : Nat}
    {f : EW} {o : Array (Array EW × Array EW)} {si : TState}
    (hrun : preRun heights forms m0 i s = some ((c, f, o), si))
    (hr : (readScalars (tb i).width).run si = none) : R heights forms m0 s = none := by
  have h1 : preRun heights forms m0 (i + 1) s = none := by
    rw [preRun_succ hh hf hi, hrun]
    show (stp m0 (c, f, o) _).run si = none
    rw [stp_run, hr]
    rfl
  rw [R, run_full hh hf, preRun_none hh hf h1]
  rfl

/-- **Table `i`'s evaluations.** -/
theorem read_step (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hh : heights.size = 6) (hf : forms.size = 6)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    {i : Nat} (hi : i < 6) {c : Nat} {f : EW} {o : Array (Array EW × Array EW)} {si : TState}
    {m : MachineData} (H : Head a s heights forms m0 i (c, f, o) si m)
    (cont : ∀ xs s' m', (readScalars (tb i).width).run si = some (xs, s') →
      It a m0 i o xs s' m' → FW m0 m' (lws m0 i) →
      rg m' .X19 = T + BitVec.ofNat 64 (8 + 40 * i) → m'.regs.X22 = f.c0 →
      m'.regs.X23 = f.c1 → (m'.regs.X28).toNat = (tb i).width →
      Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b4Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b1Offset)⟩ := by
  have hS := Pre.stack h
  have hN := spN h
  have c0 := ctx h
  have hwl := width_le hi
  -- `b1`: the width.
  have tr := tab_rin h hi
  have hwf1 : (E1 m0 m (T + BitVec.ofNat 64 (40 * i)) 40).WF := wf1 hS H.fr.kept tr.1 tr.2.1
  have hx21 : (Sym.reg .X21).eval (E1 m0 m (T + BitVec.ofNat 64 (40 * i)) 40) =
      T + BitVec.ofNat 64 (40 * i) + BitVec.ofInt 64 8 := by
    show rg m .X21 = _
    rw [H.x21, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add,
      Nat.add_comm]
  have hm1 : Match (E1 m0 m (T + BitVec.ofNat 64 (40 * i)) 40) tabS m := match1 hS H.fr.sp hx21
  refine exec_then (hb1 hp) run_b1 hwf1 hm1 fun st1 hm1a hpc1 ↦ ?_
  have hm1' : Match (E1 m0 m (T + BitVec.ofNat 64 (40 * i)) 40) (after b1 tabS) st1.data := by
    rw [Bus.after_eq run_b1]; exact hm1a
  obtain ⟨sp1, mem1, k1, r21, r28⟩ := ok_b1
  have hwd : (wordOf m.dmem (T + BitVec.ofNat 64 (40 * i) + BitVec.ofNat 64 8)).toNat =
      (tb i).width := by
    have := tw_get h H.fr hi (o := 1) (by omega)
    rw [Nat.mul_one] at this
    rw [this, tw_width hi]
  have e28 : rg st1.data .X28 =
      (wordOf m.dmem (T + BitVec.ofNat 64 (40 * i) + BitVec.ofNat 64 8)).toBitVec :=
    (rv hm1' r28).trans (ld1 _ _ _)
  have hc1 : SBool.eval (E1 m0 m (T + BitVec.ofNat 64 (40 * i)) 40)
      (.not (.cmp .ult .W64 (.load 1 8 8) (.lit 93))) = false := by
    show (!(CmpOp.ult.apply .W64 ((Sym.load 1 8 8).eval (E1 m0 m (T + BitVec.ofNat 64 (40 * i)) 40))
      (BitVec.ofNat 64 93))) = false
    rw [ld1, cmp_ult_lit _ _ (by norm_num), hwd, decide_eq_true (by omega)]
    rfl
  simp only [PcOk, hc1, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hfr1 := fr_block0 H.fr hm1 hm1' hwf1 mem1 (sp1.trans rfl)
  have hd1 : st1.data.dmem = m.dmem := dmem_block hm1' hwf1 mem1
  have k1r : ∀ r ∈ [XReg.X19, .X20, .X22, .X23, .X26, .X27, .X29],
      st1.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ rk hm1' (keeps_get k1 hr)
  have fw1 := FW.of_dmem hd1 H.fw
  -- `b2`: the length, `read_scalars`.
  have eo := evi_out h hi
  have hwf2 : (E1 m0 st1.data (evi m0 i) 1968).WF := wf1 hS hfr1.kept ⟨eo.1, eo.2.1⟩ eo.2.2.2.2.1
  have hx27 : (Sym.reg .X27).eval (E1 m0 st1.data (evi m0 i) 1968) =
      evi m0 i + BitVec.ofInt 64 0 := by
    show (st1.data.regs.getXReg .X27).toBitVec = _
    rw [k1r .X27 (by simp)]
    exact H.x27.trans (BitVec.add_zero _).symm
  have hm2 : Match (E1 m0 st1.data (evi m0 i) 1968) evS st1.data := match1 hS hfr1.sp hx27
  refine Bus.Gkr.at_pc (hpc1.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableTerms.b1_next])))
    (exec_then (hb2 hp) run_b2 hwf2 hm2 fun st2 hm2a hpc2 ↦ ?_)
  have hm2' : Match (E1 m0 st1.data (evi m0 i) 1968) (after b2 evS) st2.data := by
    rw [Bus.after_eq run_b2]; exact hm2a
  obtain ⟨sp2, mem2, k2, r0, r1, r2⟩ := ok_b2
  have hfr2 := fr_block (szs := [288, 1968]) hfr1 hN hm2 hm2' hwf2 (sp2.trans rfl) rfl
    (hout_one fun _ hj ↦ evi_outs h hi hj) (by rw [Bus.after_eq run_b2]; decide)
  have hw2 : ∀ w ∈ (after b2 evS).mem, w.r = 1 ∧ w.off + w.n ≤ 1968 := by
    rw [mem2]; intro w hw; simp only [List.mem_singleton] at hw; subst hw; exact ⟨rfl, by decide⟩
  have wr2 : ∀ q, Written (E1 m0 st1.data (evi m0 i) 1968) (after b2 evS) q → Ch m0 i q :=
    fun q hq ↦ .inr (.inl (Bus.Written.inRange (r := 1) rfl (evi_noWrap h hi) hw2 hq))
  have ts2 := ts_keep h hi (hm2'.kept hwf2) (hm2'.sameOutside hwf2) wr2 (hd1 ▸ H.ts)
  have fw2 : FW m0 st2.data (cws m0 ++ lws m0 i) :=
    FW.block hm2' hwf2 (fun p hp ↦ cl_mem hp) (by rw [Bus.after_eq run_b2]; decide) fw1
  have k2r : ∀ r ∈ cs, st2.data.regs.getXReg r = st1.data.regs.getXReg r :=
    fun r hr ↦ rk hm2' (keeps_get k2 hr)
  have hlen2 : NativeRustcVm.WordAt st2.data.dmem (evi m0 i + BitVec.ofNat 64 488)
      (UInt64.ofBitVec (rg st1.data .X28)) :=
    wordAt_of_load hm2' hwf2 (r := 1) (o := 488) (v := .reg .X28) rfl (by omega)
      (by rw [mem2]; decide)
  -- `read_scalars`.
  have hat := Bus.Gkr.Fr.at_ c0 hfr2 (outs_rc h)
  have ex0 : st2.data.regs.X0.toBitVec = m0.regs.X1.toBitVec := by
    show rg st2.data .X0 = _
    rw [rv hm2' r0, ld0, fw1 (56, rg m0 .X1) (by simp [cws])]; rfl
  have ex1 : st2.data.regs.X1.toBitVec = evi m0 i + BitVec.ofNat 64 496 := by
    show rg st2.data .X1 = _
    rw [rv hm2' r1]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [k1r .X27 (by simp)]
    exact congrArg (· + BitVec.ofNat 64 496) H.x27
  have ex2 : st2.data.regs.X2.toNat = (tb i).width := by
    show (rg st2.data .X2).toNat = _
    rw [rv hm2' r2]
    show (rg st1.data .X28).toNat = _
    rw [e28]; exact hwd
  have hle := rs_le
  have hsub : 496 + 16 * (tb i).width ≤ 1968 := by omega
  have hpre : ReadScalarsPre a si st2.data := by
    simp only [ReadScalarsPre]
    rw [ex0, ex1, ex2]
    exact ⟨hfr2.stackOk hS rfl hle, c0.rcAt hat hle, ts2, c0.tstateOk hat hle,
      c0.outOk_sub hat hle (outOk_sub eo hsub)⟩
  have hQ : ∀ m', ReadScalarsPost a si st2.data m' → SameOutside st2.data.dmem m'.dmem
      (fun q ↦ InRange (stackBelow st2.data readScalarsStack) readScalarsStack q ∨ outs m0 q) ∧
      Saved st2.data m' := by
    intro m' hq
    simp only [ReadScalarsPost] at hq
    rw [ex0, ex1, ex2] at hq
    refine ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q hq ↦ ?_, hq.2.2.2.2⟩
    rcases hq with hq | hq | hq
    · exact .inr (.inr (.inr (evi_in h hi
        (NativeRustcVm.InRange.of_sub hq (evi_noWrap h hi) hsub))))
    · exact .inr (.inr (.inl hq))
    · exact .inl hq
  have hpc2' : st2.pc = Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel ∧ retOf st2.data = Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b3Offset) :=
    ⟨hpc2.1, hpc2.2.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableTerms.b2_next]))⟩
  refine Bus.Gkr.Fr.callSpec hfr2 hN hle (fun _ h ↦ nomatch h) slots_le (outs_frame h) (hrs a si)
    hpc2' hpre hQ fun m3 hfr3 hq3 hcs3 ↦ ?_
  have hs3 := (hQ m3 hq3).1
  simp only [ReadScalarsPost] at hq3
  rw [ex0, ex1, ex2] at hq3
  obtain ⟨q0, q1, q2, q3, -⟩ := hq3
  have fw3 : FW m0 m3 (cws m0 ++ lws m0 i) :=
    FW.call hfr2.sp (le_trans rs_le hN) hs3 (fun p hp ↦ cl_le hp)
      (fun p hp j hj ↦ outs_frame_add h (by have := cl_le hp; omega)) fw2
  -- `b3`: the result.
  refine Bus.Gkr.Fr.runBlock hS (by rw [N_eq]; omega) rfl hfr3 (hb3 hp) run_b3 rfl rfl
    (by decide) (by decide) fun st4 hfr4 hd4 hm4 hpc4 ↦ ?_
  have hm4' : Match (E0 m0 m3) (after b3 sF) st4.data := by rw [Bus.after_eq run_b3]; exact hm4
  obtain ⟨-, -, k3⟩ := ok_b3
  have kr : ∀ r ∈ cs, st4.data.regs.getXReg r = st1.data.regs.getXReg r := fun r hr ↦ by
    rw [rk hm4' (keeps_get k3 hr), hcs3 r (cs_saved r hr), k2r r hr]
  have fw4 := FW.of_dmem hd4 fw3
  have hc : SBool.eval (E0 m0 m3) (.cmp .eq .W32 (.reg .X0) (.lit 0)) =
      !((readScalars (tb i).width).run si).isSome := by
    show CmpOp.eq.apply .W32 m3.regs.X0.toBitVec (BitVec.ofNat 64 0) = _
    rw [q0, okWord_eq0]
  simp only [PcOk, hc] at hpc4
  cases hr : (readScalars (tb i).width).run si with
  | none =>
    simp only [hr, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc4
    exact Bus.Gkr.at_pc (hpc4.trans (lbl_6 hp)) (exit_none hp h hfr4
      (fun p hp ↦ fw4 p (List.mem_append_left _ hp)) (R_none hh hf hi H.run hr))
  | some p =>
    obtain ⟨xs, s'⟩ := p
    simp only [hr, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc4
    have hxs : xs.size = (tb i).width := NativeRustcVm.Sumcheck.readScalars_size hr
    have hW3 : ∀ q, (InRange (evi m0 i + BitVec.ofNat 64 496) (16 * (tb i).width) q ∨
        InRange m0.regs.X1.toBitVec tstateBytes q ∨
        InRange (stackBelow st2.data readScalarsStack) readScalarsStack q) →
        Ch m0 i q ∨ InRange m0.regs.X1.toBitVec tstateBytes q := fun q hq ↦ by
      rcases hq with hq | hq | hq
      · exact .inl (.inr (.inl (NativeRustcVm.InRange.of_sub hq (evi_noWrap h hi) hsub)))
      · exact .inr hq
      · exact .inl (.inl (c0.inRange_stack hat hle hq))
    have ev3 : ∀ j (hj : j < o.size), TableEvalAt m3.dmem (evi m0 j) o[j] := fun j hj ↦
      ev_keep h hi (by rw [← H.osz]; exact hj) q3 hW3
        (ev_keep h hi (by rw [← H.osz]; exact hj) (hm2'.sameOutside hwf2)
          (fun q hq ↦ .inl (wr2 q hq))
          (show TableEvalAt st1.data.dmem _ _ by rw [hd1]; exact H.evs j hj))
    -- The length word, kept by the call.
    have hlen3 : NativeRustcVm.WordAt m3.dmem (evi m0 i + BitVec.ofNat 64 488)
        (UInt64.ofBitVec (rg st1.data .X28)) := by
      refine NativeRustcVm.BytesAt.of_sameOutside hlen2 q3 fun j hj hq ↦ ?_
      rw [NativeRustcVm.length_wordBytes] at hj
      rw [NativeRustcVm.addr_add_add] at hq
      have hj' : 488 + j < 1968 := by omega
      rcases hq with hq | hq | hq
      · exact NativeRustcVm.not_inRange_sub (evi_noWrap h hi) hsub hj' (.inl (by omega)) hq
      · exact NativeRustcVm.Apart.not_inRange_add eo.2.2.1 (evi_noWrap h hi)
          (Pre.ts h).footprint.1.2 hj' hq
      · exact NativeRustcVm.Apart.not_inRange_add eo.2.2.2.2.1 (evi_noWrap h hi)
          (Bus.stack_noWrap hS) hj' (c0.inRange_stack hat hle hq)
    have hlenv : UInt64.ofBitVec (rg st1.data .X28) = xs.toList.length.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [e28, UInt64.ofBitVec_toBitVec, show (wordOf m.dmem (T + BitVec.ofNat 64 (40 * i) +
        BitVec.ofNat 64 8)).toNat = (tb i).width from hwd, Array.length_toList, hxs,
        toNat_toUInt64 (by omega)]
    have vals : BufEWAt st4.data.dmem (evi m0 i + BitVec.ofNat 64 488) 92 xs.toList := by
      rw [hd4]
      refine ⟨by rw [Array.length_toList, hxs]; exact hwl, hlenv ▸ hlen3, ?_⟩
      rw [show evi m0 i + BitVec.ofNat 64 488 + 8#64 = evi m0 i + BitVec.ofNat 64 496 from
        NativeRustcVm.addr_add_add _ 488 8]
      exact q1 xs s' hr
    have hsc : ∀ r ∈ [XReg.X19, .X20, .X22, .X23, .X26, .X27, .X29], r ∈ cs := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [cs]
    have g : ∀ r ∈ [XReg.X19, .X20, .X22, .X23, .X26, .X27, .X29],
        st4.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ by
      rw [kr r (hsc r hr), k1r r hr]
    have g21 : rg st4.data .X21 = T + BitVec.ofNat 64 (8 + 40 * (i + 1)) := by
      show (st4.data.regs.getXReg .X21).toBitVec = _
      rw [kr .X21 (by simp)]
      show rg st1.data .X21 = _
      rw [rv hm1' r21]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      show rg m .X21 + _ = _
      rw [H.x21, NativeRustcVm.addr_add_add, show 8 + 40 * i + 40 = 8 + 40 * (i + 1) by ring]
    have G : ∀ {r : XReg}, r ∈ [XReg.X19, .X20, .X22, .X23, .X26, .X27, .X29] →
        rg st4.data r = rg m r := fun hr ↦ by unfold rg; rw [g _ hr]
    refine Bus.Gkr.at_pc (hpc4.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableTerms.b3_next])))
      (cont xs s' st4.data hr ?_ (fun p hp ↦ fw4 p (List.mem_append_right _ hp))
        ((G (by simp)).trans H.x19) ((g .X22 (by simp)).trans H.x22)
        ((g .X23 (by simp)).trans H.x23) ?_)
    · refine ⟨hfr4, fun p hp ↦ fw4 p (List.mem_append_left _ hp), g21,
        (G (by simp)).trans H.x20, (G (by simp)).trans H.x27, (G (by simp)).trans H.x29,
        (G (by simp)).trans H.x26, hd4 ▸ q2 xs s' hr, vals, fun j hj ↦ hd4 ▸ ev3 j hj, H.osz⟩
    · show (st4.data.regs.getXReg .X28).toNat = _
      rw [kr .X28 (by simp)]
      show (rg st1.data .X28).toNat = _
      rw [e28]; exact hwd

end

end NativeRustcVmArm.Tables.TableTerms
