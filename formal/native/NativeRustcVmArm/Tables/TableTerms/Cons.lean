module

public import NativeRustcVmArm.Code.Vm.ConstraintsW.Names
public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Tables.TableTerms.Body

/-!
# `table_terms`: table `i`'s constraints

`b4` saves the running sum at `80`, zeroes the constraints at `112` and calls `constraints_w` on
the table's opcode and evaluations; `b5` calls `dot` on the constraint powers from the cursor and
the constraints: the summand in X0, X1 (`cons_step`).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVmArm.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf BufEWAt)
open NativeRustcVmArm.Bus (after)

public section

theorem cw_le : 288 + constraintsWStack ≤ N := by rw [N_eq]; decide
theorem dot_le : 288 + dotStack ≤ N := by rw [N_eq]; decide

/-- The frame's words the body keeps are below `112`. -/
theorem body_lt {m0 : MachineData} {i : Nat} {x y : BitVec 64} {p : Nat × BitVec 64}
    (hp : p ∈ lws m0 i ++ [(80, x), (88, y)]) : p.1 + 8 ≤ 112 := by
  simp only [lws, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp

theorem cws_lt {m0 : MachineData} {p : Nat × BitVec 64} (hp : p ∈ cws m0) : p.1 + 8 ≤ 112 := by
  have := cl_mem (i := 0) (List.mem_append_left _ hp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  omega

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- **Table `i`'s constraints and their sum** (`b4`, `constraints_w`, `b5`, `dot`). -/
theorem cons_step (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hcw : Spec (Labels.label NativeRustcVmArm.Vm.ConstraintsW.entryLabel) ConstraintsWPre ConstraintsWPost)
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost) {R : MachineState → Prop}
    {i : Nat} (hi : i < 6) {o : Array (Array EW × Array EW)} {xs : Array EW} {s' : TState}
    {m : MachineData} (H : It a m0 i o xs s' m) (hl : FW m0 m (lws m0 i))
    (x19 : rg m .X19 = T + BitVec.ofNat 64 (8 + 40 * i))
    (x28 : (m.regs.X28).toNat = (tb i).width) (hxs : xs.size = (tb i).width)
    (cont : ∀ m', It a m0 i o xs s' m' →
      FW m0 m' (lws m0 i ++ [(80, rg m .X23), (88, rg m .X22)]) →
      rg m' .X19 = T + BitVec.ofNat 64 (8 + 40 * i) → (m'.regs.X28).toNat = (tb i).width →
      (m'.regs.X22).toNat = (tb i).nConstraints → m'.regs.X23 = 8 →
      ewRet m' = dot ((cpw m0).extract (cursorAt i) (cursorAt i + (tb i).nConstraints))
        (constraintsW (tb i).opcode xs) →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b6Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b4Offset)⟩ := by
  have hS := Pre.stack h
  have hN := spN h
  have tr := tab_rin h hi
  have hcl := cursor_le hi
  -- `b4`: the sum saved, the constraints zeroed.
  have hwf4 : (E1 m0 m (T + BitVec.ofNat 64 (40 * i)) 40).WF := wf1 hS H.fr.kept tr.1 tr.2.1
  have hx19 : ∀ m' : MachineData, rg m' .X19 = rg m .X19 →
      (Sym.reg .X19).eval (E1 m0 m' (T + BitVec.ofNat 64 (40 * i)) 40) =
        T + BitVec.ofNat 64 (40 * i) + BitVec.ofInt 64 8 := fun m' he ↦ by
    show rg m' .X19 = _
    rw [he, x19, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add,
      Nat.add_comm]
  have hm4 : Match (E1 m0 m (T + BitVec.ofNat 64 (40 * i)) 40) tab19S m :=
    match1 hS H.fr.sp (hx19 m rfl)
  refine exec_then (hb4 hp) run_b4 hwf4 hm4 fun st4 hm4a hpc4 ↦ ?_
  have hm4' : Match (E1 m0 m (T + BitVec.ofNat 64 (40 * i)) 40) (after b4 tab19S) st4.data := by
    rw [Bus.after_eq run_b4]; exact hm4a
  obtain ⟨sp4, wok4, fok4, l80, l88, k4, r0, r1, r2, r3⟩ := ok_b4
  have hfr4 := fr_block (szs := [288, 40]) H.fr hN hm4 hm4' hwf4 (sp4.trans rfl) rfl
    (hout_none (L := [false, false]) (by decide)) wok4
  have k4r : ∀ r ∈ cs, st4.data.regs.getXReg r = m.regs.getXReg r :=
    fun r hr ↦ rk hm4' (keeps_get k4 hr)
  have It4 : It a m0 i o xs s' st4.data :=
    It.step h hi H hfr4 (hm4'.kept hwf4) (hm4'.sameOutside hwf4)
      (fun q hq ↦ .inl (written_stack hN (wok_frame (by decide) wok4) hq))
      (FW.block hm4' hwf4 (fun p hp ↦ cl_mem (i := 0) (List.mem_append_left _ hp)) fok4 H.cw)
      fun r hr ↦ k4r r (it_cs r hr)
  have fw4 : FW m0 st4.data (lws m0 i ++ [(80, rg m .X23), (88, rg m .X22)]) := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact FW.block hm4' hwf4 (fun p hp ↦ cl_mem (List.mem_append_right _ hp)) fok4 hl p hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · rw [fw_write hm4' hwf4 (o := 80) (by omega), l80]; rfl
      · rw [fw_write hm4' hwf4 (o := 88) (by omega), l88]; rfl
  -- `constraints_w`.
  have ex0 : st4.data.regs.X0.toNat = (tb i).opcode := by
    have := tw_get h H.fr hi (o := 0) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at this
    show (rg st4.data .X0).toNat = _
    rw [rv hm4' r0, ld1, this]
    exact tw_opcode hi
  have ex1 : st4.data.regs.X1.toBitVec = evi m0 i + BitVec.ofNat 64 496 := by
    show rg st4.data .X1 = _
    rw [rv hm4' r1]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    exact congrArg (· + BitVec.ofNat 64 496) H.x27
  have ex2 : st4.data.regs.X2.toNat = (tb i).width := by
    show (rg st4.data .X2).toNat = _
    rw [rv hm4' r2]
    exact x28
  have ex3 : st4.data.regs.X3.toBitVec = base m0 288 + BitVec.ofNat 64 112 := by
    show rg st4.data .X3 = _
    rw [rv hm4' r3, eval_ptr0]
    rfl
  have hle := cw_le
  have hsub : 496 + 16 * (tb i).width ≤ 1968 := by have := width_le hi; omega
  have eos := outOk_sub (evi_out h hi) hsub
  have hpre : ConstraintsWPre st4.data := by
    refine ⟨hfr4.stackOk hS rfl hle, ?_, ?_⟩
    · rw [SliceOk, ex1, ex2]
      exact ⟨Bus.Fr.readable hfr4 ⟨eos.1, eos.2.1⟩, Bus.Fr.offStack hfr4 hS eos.2.2.2.2.1 hle⟩
    · rw [ex3]; exact Bus.local_ok hS hle (by omega) hfr4.kept hfr4.sp
  have hsl4 : slice st4.data st4.data.regs.X1 st4.data.regs.X2 = xs := by
    refine slice_of_ewsAt ?_ (ex2.trans hxs.symm)
    rw [ex1]
    have := It4.vals.2.2
    rwa [show evi m0 i + BitVec.ofNat 64 488 + 8#64 = evi m0 i + BitVec.ofNat 64 496 from
      NativeRustcVm.addr_add_add _ 488 8] at this
  have hpc4' : st4.pc = Labels.label NativeRustcVmArm.Vm.ConstraintsW.entryLabel ∧ retOf st4.data = Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b5Offset) :=
    ⟨hpc4.1, hpc4.2.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableTerms.b4_next]))⟩
  refine Bus.Gkr.Fr.callLocal (X := fun q ↦ InRange (base m0 288 + BitVec.ofNat 64 112) 32 q)
    (o := 112) (n := 32) hfr4 hN hle (fun _ h ↦ nomatch h) (by decide) (by omega) (outs_frame h)
    (fun q hq ↦ .inr hq) hcw hpc4' hpre (fun m' hq ↦ ?_) fun m5 hfr5 hq5 hcs5 hs5 ↦ ?_
  · simp only [ConstraintsWPost] at hq
    obtain ⟨-, -, hc, hsv⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hc fun q hq ↦ ?_, hsv⟩
    rcases hq with hq | hq
    · rw [ex3] at hq; exact .inr hq
    · exact .inl hq
  simp only [ConstraintsWPost] at hq5
  rw [ex0, hsl4, ex3] at hq5
  obtain ⟨q0, q1, -, hsv5⟩ := hq5
  have hnot : ∀ {L : List (Nat × BitVec 64)}, (∀ p ∈ L, p.1 + 8 ≤ 112) → ∀ p ∈ L, ∀ j < 8,
      ¬InRange (base m0 288 + BitVec.ofNat 64 112) 32 (base m0 288 + BitVec.ofNat 64 (p.1 + j)) :=
    fun hL p hp j hj ↦ Bus.Gkr.not_loc (by rw [N_eq] at hN; omega) (by omega)
      (by have := hL p hp; omega) (.inl (by have := hL p hp; omega))
  have It5 : It a m0 i o xs s' m5 :=
    It.call h hi It4 hfr5 hle hs5
      (fun q hq ↦ .inl (Bus.inRange_local hN (by rw [N_eq]; omega) (by omega) hq))
      (hnot fun p hp ↦ cws_lt hp) hsv5
  have fw5 : FW m0 m5 (lws m0 i ++ [(80, rg m .X23), (88, rg m .X22)]) :=
    FW.call hfr4.sp (le_trans hle hN) hs5 (fun p hp ↦ by have := body_lt hp; omega)
      (hnot fun p hp ↦ body_lt hp) fw4
  -- `b5`: the constraint powers from the cursor, `dot`.
  have hwf5 : (E1 m0 m5 (T + BitVec.ofNat 64 (40 * i)) 40).WF := wf1 hS hfr5.kept tr.1 tr.2.1
  have g : ∀ r ∈ cs, m5.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ by
    rw [hcs5 r (cs_saved r hr), k4r r hr]
  have hm5 : Match (E1 m0 m5 (T + BitVec.ofNat 64 (40 * i)) 40) tab19S m5 :=
    match1 hS hfr5.sp (hx19 m5 (by unfold rg; rw [g .X19 (by simp)]))
  refine exec_then (hb5 hp) run_b5 hwf5 hm5 fun st6 hm6a hpc6 ↦ ?_
  have hm6' : Match (E1 m0 m5 (T + BitVec.ofNat 64 (40 * i)) 40) (after b5 tab19S) st6.data := by
    rw [Bus.after_eq run_b5]; exact hm6a
  obtain ⟨sp6, mem6, k6, s0, s1, s2, s3, s22, s23⟩ := ok_b5
  have hfr6 := fr_block0 hfr5 hm5 hm6' hwf5 mem6 (sp6.trans rfl)
  have hd6 : st6.data.dmem = m5.dmem := dmem_block hm6' hwf5 mem6
  have k6r : ∀ r ∈ [XReg.X19, .X20, .X21, .X24, .X25, .X26, .X27, .X28, .X29],
      st6.data.regs.getXReg r = m5.regs.getXReg r := fun r hr ↦ rk hm6' (keeps_get k6 hr)
  have It6 : It a m0 i o xs s' st6.data :=
    It.step h hi It5 hfr6 (hm6'.kept hwf5) (hm6'.sameOutside hwf5)
      (fun q hq ↦ .inl (written_stack hN (by rw [mem6]; intro w hw; cases hw) hq))
      (FW.of_dmem hd6 It5.cw) fun r hr ↦ k6r r (by revert r hr; simp)
  have hnc : (Sym.load 1 16 8).eval (E1 m0 m5 (T + BitVec.ofNat 64 (40 * i)) 40) =
      BitVec.ofNat 64 (tb i).nConstraints := by
    have := tw_get h hfr5 hi (o := 2) (by omega)
    rw [ld1, show (16 : Nat) = 8 * 2 from rfl, this]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact tw_nc hi
  have e0 : st6.data.regs.X0.toBitVec = m0.regs.X2.toBitVec +
      BitVec.ofNat 64 (16 * cursorAt i) := by
    show rg st6.data .X0 = _
    rw [rv hm6' s0, cpS_eval (by omega) It5.x26, ld0, It5.cw (24, rg m0 .X2) (by simp [cws])]
    rfl
  have e1 : st6.data.regs.X1.toNat = (tb i).nConstraints := by
    show (rg st6.data .X1).toNat = _
    rw [rv hm6' s1, nc_eval hcl It5.x26 hnc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e2 : st6.data.regs.X2.toBitVec = base m0 288 + BitVec.ofNat 64 112 := by
    show rg st6.data .X2 = _
    rw [rv hm6' s2, eval_ptr0]
    rfl
  have hcsz := constraintsW_size (tb i).opcode xs
  have e3 : st6.data.regs.X3.toNat = (constraintsW (tb i).opcode xs).size := by
    show (rg st6.data .X3).toNat = _
    rw [rv hm6' s3]
    exact q0
  have hdl := dot_le
  have cpr : ReadIn m0 (m0.regs.X2.toBitVec + BitVec.ofNat 64 (16 * cursorAt i))
      (16 * (tb i).nConstraints) N (wsL m0) := rin_sub (Pre.cp h) (by omega)
  have hpre6 : DotPre st6.data := by
    refine ⟨hfr6.stackOk hS rfl hdl, ?_, ?_⟩
    · rw [SliceOk, e0, e1]
      exact ⟨Bus.Fr.readable hfr6 cpr.1, Bus.Fr.offStack hfr6 hS cpr.2.1 hdl⟩
    · rw [SliceOk, e2, e3]
      exact Bus.local_ok hS hdl (by omega) hfr6.kept hfr6.sp
  have hpc6' : st6.pc = Labels.label NativeRustcVmArm.Vm.Dot.entryLabel ∧ retOf st6.data = Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b6Offset) :=
    ⟨hpc6.1, hpc6.2.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableTerms.b5_next]))⟩
  refine Bus.Gkr.Fr.callSpec hfr6 hN hdl (fun _ h ↦ nomatch h) slots_le (outs_frame h) hdot
    hpc6' hpre6 (fun m' hq ↦ ⟨Bus.changes_zero hq.2.1, hq.2.2⟩) fun m7 hfr7 hq7 hcs7 ↦ ?_
  have g7 : ∀ r ∈ [XReg.X19, .X20, .X21, .X24, .X25, .X26, .X27, .X28, .X29],
      m7.regs.getXReg r = m5.regs.getXReg r := fun r hr ↦ by
    rw [hcs7 r (cs_saved r (body_cs r hr)), k6r r hr]
  have hs7 : SameOutside st6.data.dmem m7.dmem
      (fun q ↦ InRange (stackBelow st6.data dotStack) dotStack q ∨ False) :=
    Bus.changes_zero hq7.2.1
  refine cont m7 (It.call h hi It6 hfr7 hdl hs7 (fun _ h ↦ h.elim) (fun _ _ _ _ h ↦ h) hq7.2.2)
    (FW.call hfr6.sp (le_trans hdl hN) hs7 (fun p hp ↦ by have := body_lt hp; omega)
      (fun _ _ _ _ h ↦ h) (FW.of_dmem hd6 fw5)) ?_ ?_ ?_ ?_ ?_
  · unfold rg; rw [g7 .X19 (by simp), g .X19 (by simp)]; exact x19
  · show (m7.regs.getXReg .X28).toNat = _
    rw [g7 .X28 (by simp), g .X28 (by simp)]; exact x28
  · show (m7.regs.getXReg .X22).toNat = _
    rw [hcs7 .X22 (by decide)]
    show (rg st6.data .X22).toNat = _
    rw [rv hm6' s22, hnc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · apply UInt64.toBitVec_inj.mp
    show rg m7 .X23 = _
    unfold rg
    rw [hcs7 .X23 (by decide)]
    exact rv hm6' s23
  · have hA : slice st6.data st6.data.regs.X0 st6.data.regs.X1 =
        (cpw m0).extract (cursorAt i) (cursorAt i + (tb i).nConstraints) := by
      unfold slice
      rw [e0, e1, ewsOf_in h hfr6 cpr, cpw, arrE,
        ewsOf_sub _ _ (show cursorAt i + (tb i).nConstraints ≤ 2 by omega), extract_toArray]
    have hB : slice st6.data st6.data.regs.X2 st6.data.regs.X3 = constraintsW (tb i).opcode xs :=
      slice_of_ewsAt (by rw [e2, hd6]; exact q1) e3
    rw [hq7.1, hA, hB]

end

end NativeRustcVmArm.Tables.TableTerms
