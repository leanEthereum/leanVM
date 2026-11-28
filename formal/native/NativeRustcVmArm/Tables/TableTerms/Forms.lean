module

public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.Evaluate.Names
public import NativeRustcVmArm.Tables.TableTerms.Eval

/-!
# `table_terms`: table `i`'s forms

`b6`, `b7`, `b8` save the summand and the first two form values in the frame and evaluate the
table's three forms (`eval_step`); `b9` saves the third, loads the table's weight and calls `dot`
on the form powers and the three values (`forms_step`).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVmArm.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf ewOf BufEWAt)
open NativeRustcVmArm.Bus (after)

@[expose] public section

/-- The frame's words through the body of table `i`: the next weight's and height's addresses,
the running sum `f` at `80`, `88` and the summand `sm` at `64`, `72`. -/
def Lb (m0 : MachineData) (i : Nat) (f sm : EW) : List (Nat × BitVec 64) :=
  lws m0 i ++ [(80, f.c1.toBitVec), (88, f.c0.toBitVec), (64, sm.c1.toBitVec),
    (72, sm.c0.toBitVec)]

/-- Table `i`'s weight. -/
abbrev wt (m0 : MachineData) (i : Nat) : EW := (wts m0).getD i 0

end

public section

/-- Three elements of the frame from its words. -/
theorem ewsOf_three (d : Mem 64) (b : BitVec 64) :
    ewsOf d (b + BitVec.ofNat 64 144) 3 =
      [⟨wordOf d (b + BitVec.ofNat 64 144), wordOf d (b + BitVec.ofNat 64 152)⟩,
        ⟨wordOf d (b + BitVec.ofNat 64 160), wordOf d (b + BitVec.ofNat 64 168)⟩,
        ⟨wordOf d (b + BitVec.ofNat 64 176), wordOf d (b + BitVec.ofNat 64 184)⟩] := by
  simp only [ewsOf, ewOf, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, NativeRustcVm.addr_add_add]

/-- A row of three forms evaluated. -/
theorem map_three {fs : Array FormW} (h : fs.size = 3) (g : FormW → EW) :
    fs.map g = #[g (fs.getD 0 #[]), g (fs.getD 1 #[]), g (fs.getD 2 #[])] := by
  apply Array.ext
  · simp [h]
  · intro j h1 h2
    simp only [Array.size_map] at h1
    rw [h] at h1
    simp only [Array.getElem_map, Array.getD_eq_getD_getElem?]
    interval_cases j <;> simp [h]

theorem dot_le' : 288 + dotStack ≤ N := by rw [N_eq]; decide

theorem Lb_le {m0 : MachineData} {i : Nat} {f sm : EW} {p : Nat × BitVec 64}
    (hp : p ∈ Lb m0 i f sm) : p.1 + 8 ≤ 112 := by
  simp only [Lb, lws, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat}
  {forms : Array (Array FormW)} {m0 : MachineData}

/-- **Table `i`'s three forms evaluated** (`b6`, `b7`, `b8`). -/
theorem forms_eval (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmArm.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    {R : MachineState → Prop}
    {i : Nat} (hi : i < 6) {o : Array (Array EW × Array EW)} {xs : Array EW} {s' : TState}
    {m : MachineData} (H : It a m0 i o xs s' m) {f sm : EW}
    (hw : FW m0 m (lws m0 i ++ [(80, f.c1.toBitVec), (88, f.c0.toBitVec)]))
    (x28 : (m.regs.X28).toNat = (tb i).width) (hxs : xs.size = (tb i).width)
    (hsm : ewRet m = sm)
    (cont : ∀ m', It a m0 i o xs s' m' → FW m0 m' (Lb m0 i f sm ++
      [(144, ((fm forms i 0).evaluate xs).c0.toBitVec),
        (152, ((fm forms i 0).evaluate xs).c1.toBitVec),
        (160, ((fm forms i 1).evaluate xs).c0.toBitVec),
        (168, ((fm forms i 1).evaluate xs).c1.toBitVec)]) →
      (∀ r ∈ cs, m'.regs.getXReg r = m.regs.getXReg r) →
      ewRet m' = (fm forms i 2).evaluate xs →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b9Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b6Offset)⟩ := by
  obtain ⟨o6a, o6b, o6c, l64, l72⟩ := ok_b6
  refine eval_step h hev (hb6 hp) run_b6 (j := 0) (by decide) o6a o6b o6c (by decide)
    (by omega) (by omega) l64 l72 hi H (by simp [lws]) hw x28 hxs
    fun m1 It1 fw1 kr1 hv1 ↦ ?_
  rw [NativeRustcVmArm.Vm.TableTerms.b6_length, NativeRustcVmArm.Vm.TableTerms.b6Length]
  obtain ⟨o7a, o7b, o7c, l144, l152⟩ := ok_b7
  refine eval_step h hev (hb7 hp) run_b7 (j := 1) (by decide) o7a o7b o7c (by decide)
    (by omega) (by omega) l144 l152 hi It1 (by simp [lws]) fw1
    (by show (m1.regs.getXReg .X28).toNat = _; rw [kr1 .X28 (by simp)]; exact x28) hxs
    fun m2 It2 fw2 kr2 hv2 ↦ ?_
  rw [NativeRustcVmArm.Vm.TableTerms.b7_length, NativeRustcVmArm.Vm.TableTerms.b7Length]
  obtain ⟨o8a, o8b, o8c, l160, l168⟩ := ok_b8
  refine eval_step h hev (hb8 hp) run_b8 (j := 2) (by decide) o8a o8b o8c (by decide)
    (by omega) (by omega) l160 l168 hi It2 (by simp [lws]) fw2
    (by show (m2.regs.getXReg .X28).toNat = _; rw [kr2 .X28 (by simp), kr1 .X28 (by simp)]
        exact x28) hxs fun m3 It3 fw3 kr3 hv3 ↦ ?_
  rw [NativeRustcVmArm.Vm.TableTerms.b8_length, NativeRustcVmArm.Vm.TableTerms.b8Length]
  refine cont m3 It3 ?_ (fun r hr ↦ by rw [kr3 r hr, kr2 r hr, kr1 r hr]) hv3
  have e64 : rg m .X1 = sm.c1.toBitVec := by rw [← hsm]; rfl
  have e72 : rg m .X0 = sm.c0.toBitVec := by rw [← hsm]; rfl
  have e10 : rg m1 .X0 = ((fm forms i 0).evaluate xs).c0.toBitVec := by rw [← hv1]; rfl
  have e11 : rg m1 .X1 = ((fm forms i 0).evaluate xs).c1.toBitVec := by rw [← hv1]; rfl
  have e20 : rg m2 .X0 = ((fm forms i 1).evaluate xs).c0.toBitVec := by rw [← hv2]; rfl
  have e21 : rg m2 .X1 = ((fm forms i 1).evaluate xs).c1.toBitVec := by rw [← hv2]; rfl
  rw [e64, e72, e10, e11, e20, e21] at fw3
  intro p hp
  exact fw3 p (by simpa [Lb] using hp)

/-- **Table `i`'s forms**: the three values and their `dot` with the form powers. -/
theorem forms_step (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmArm.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost) {R : MachineState → Prop}
    {i : Nat} (hi : i < 6) {o : Array (Array EW × Array EW)} {xs : Array EW} {s' : TState}
    {m : MachineData} (H : It a m0 i o xs s' m) {f sm : EW}
    (hw : FW m0 m (lws m0 i ++ [(80, f.c1.toBitVec), (88, f.c0.toBitVec)]))
    (x28 : (m.regs.X28).toNat = (tb i).width) (hxs : xs.size = (tb i).width)
    (x22 : (m.regs.X22).toNat = (tb i).nConstraints) (hsm : ewRet m = sm)
    (cont : ∀ m', It a m0 i o xs s' m' → FW m0 m' (Lb m0 i f sm) →
      rg m' .X19 = wp m0 + BitVec.ofNat 64 (8 + 16 * i) → m'.regs.X28 = (wt m0 i).c0 →
      m'.regs.X23 = (wt m0 i).c1 → (m'.regs.X22).toNat = (tb i).nConstraints →
      ewRet m' = dot (fpw m0) ((forms.getD i #[]).map (·.evaluate xs)) →
      Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b10Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b6Offset)⟩ := by
  have hS := Pre.stack h
  have hN := spN h
  refine forms_eval hp h hev hi H hw x28 hxs hsm fun m3 It3 fw3 kr hv3 ↦ ?_
  -- `b9`: the third value, the weight, `dot`.
  have wr := w_rin h hi
  have hwf : (E1 m0 m3 (wp m0 + BitVec.ofNat 64 (16 * i)) 16).WF := wf1 hS It3.fr.kept wr.1 wr.2.1
  have f96 : fw m0 m3 96 = wp m0 + BitVec.ofNat 64 (8 + 16 * i) :=
    fw3 (96, _) (by simp [Lb, lws])
  have hm : Match (E1 m0 m3 (wp m0 + BitVec.ofNat 64 (16 * i)) 16) wS m3 := by
    refine match1 hS It3.fr.sp ?_
    rw [ld0, f96, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add,
      Nat.add_comm]
  refine exec_then (hb9 hp) run_b9 hwf hm fun st hma0 hpc ↦ ?_
  have hma : Match (E1 m0 m3 (wp m0 + BitVec.ofNat 64 (16 * i)) 16) (after b9 wS) st.data := by
    rw [Bus.after_eq run_b9]; exact hma0
  obtain ⟨sp9, wok9, fok9, l176, l184, k9, r0, r1, r2, r3, r19, r23, r28⟩ := ok_b9
  have hfr9 := fr_block (szs := [288, 16]) It3.fr hN hm hma hwf (sp9.trans rfl) rfl
    (hout_none (L := [false, false]) (by decide)) wok9
  have k9r : ∀ r ∈ [XReg.X20, .X21, .X22, .X24, .X25, .X26, .X27, .X29],
      st.data.regs.getXReg r = m3.regs.getXReg r := fun r hr ↦ rk hma (keeps_get k9 hr)
  have It9 : It a m0 i o xs s' st.data :=
    It.step h hi It3 hfr9 (hma.kept hwf) (hma.sameOutside hwf)
      (fun q hq ↦ .inl (written_stack hN (wok_frame (by decide) wok9) hq))
      (FW.block hma hwf (fun p hp ↦ cl_mem (i := 0) (List.mem_append_left _ hp)) fok9 It3.cw)
      fun r hr ↦ k9r r (by revert r hr; simp)
  have fw3' := FW.block hma hwf (fun p hp ↦ mem_of_all (by simp [Lb, lws]) hp) fok9 fw3
  have fw9 : FW m0 st.data (Lb m0 i f sm) := fun p hp ↦ fw3' p (List.mem_append_left _ hp)
  -- The three values in the frame.
  have wv : ∀ {o : Nat} {v : UInt64}, fw m0 st.data o = v.toBitVec →
      wordOf st.data.dmem (base m0 288 + BitVec.ofNat 64 o) = v := fun hv ↦
    UInt64.toBitVec_inj.mp hv
  have v144 := fw3' (144, ((fm forms i 0).evaluate xs).c0.toBitVec) (by simp)
  have v152 := fw3' (152, ((fm forms i 0).evaluate xs).c1.toBitVec) (by simp)
  have v160 := fw3' (160, ((fm forms i 1).evaluate xs).c0.toBitVec) (by simp)
  have v168 := fw3' (168, ((fm forms i 1).evaluate xs).c1.toBitVec) (by simp)
  have v176 : fw m0 st.data 176 = m3.regs.X0.toBitVec := by
    rw [fw_write hma hwf (by omega), l176]; rfl
  have v184 : fw m0 st.data 184 = m3.regs.X1.toBitVec := by
    rw [fw_write hma hwf (by omega), l184]; rfl
  have hvals : slice st.data (UInt64.ofBitVec (base m0 288 + BitVec.ofNat 64 144)) 3 =
      #[(fm forms i 0).evaluate xs, (fm forms i 1).evaluate xs, (fm forms i 2).evaluate xs] := by
    unfold slice
    rw [show (3 : UInt64).toNat = 3 from rfl, UInt64.toBitVec_ofBitVec, ewsOf_three,
      wv v144, wv v152, wv v160, wv v168, wv v176, wv v184]
    rw [show (⟨m3.regs.X0, m3.regs.X1⟩ : EW) = ewRet m3 from rfl, hv3]
  -- The arguments.
  have e0 : st.data.regs.X0 = m0.regs.X3 := by
    apply UInt64.toBitVec_inj.mp
    show rg st.data .X0 = _
    rw [rv hma r0, ld0, It3.cw (32, rg m0 .X3) (by simp [cws])]; rfl
  have e1 : st.data.regs.X1 = 3 := UInt64.toBitVec_inj.mp (rv hma r1)
  have e2 : st.data.regs.X2 = UInt64.ofBitVec (base m0 288 + BitVec.ofNat 64 144) := by
    apply UInt64.toBitVec_inj.mp
    show rg st.data .X2 = _
    rw [rv hma r2, eval_ptr0]; rfl
  have e3 : st.data.regs.X3 = 3 := UInt64.toBitVec_inj.mp (rv hma r3)
  have hle := dot_le'
  have fpr := Pre.fp h
  have hpre : DotPre st.data := by
    refine ⟨hfr9.stackOk hS rfl hle, ?_, ?_⟩
    · rw [SliceOk, e0, e1]
      exact ⟨Bus.Fr.readable hfr9 fpr.1, Bus.Fr.offStack hfr9 hS fpr.2.1 hle⟩
    · rw [SliceOk, e2, e3, UInt64.toBitVec_ofBitVec]
      exact Bus.local_ok hS hle (by decide) hfr9.kept hfr9.sp
  have hpc' : st.pc = Labels.label NativeRustcVmArm.Vm.Dot.entryLabel ∧ retOf st.data = Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b10Offset) :=
    ⟨hpc.1, hpc.2.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableTerms.b9_next]))⟩
  refine Bus.Gkr.Fr.callSpec hfr9 hN hle (fun _ h ↦ nomatch h) slots_le (outs_frame h) hdot
    hpc' hpre (fun m' hq ↦ ⟨Bus.changes_zero hq.2.1, hq.2.2⟩) fun m4 hfr4 hq4 hcs4 ↦ ?_
  have hs4 : SameOutside st.data.dmem m4.dmem
      (fun q ↦ InRange (stackBelow st.data dotStack) dotStack q ∨ False) :=
    Bus.changes_zero hq4.2.1
  have wrd : ∀ o, o + 8 ≤ 16 → wordOf m3.dmem (wp m0 + BitVec.ofNat 64 (16 * i) +
      BitVec.ofNat 64 o) = wordOf m0.dmem (wp m0 + BitVec.ofNat 64 (16 * i) +
      BitVec.ofNat 64 o) := fun o ho ↦
    NativeRustcVm.wordOf_congr fun j hj ↦ by
      rw [NativeRustcVm.addr_add_add]
      exact readIn_same h It3.fr wr (o + j) (by omega)
  have hwt : wt m0 i = ewOf m0.dmem (wp m0 + BitVec.ofNat 64 (16 * i)) := by
    rw [wt, wts, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_eq_getElem (by simp [nTables]; omega), Option.getD_some,
      NativeRustcVm.getElem_ewsOf]
  refine cont m4 (It.call h hi It9 hfr4 hle hs4 (fun _ h ↦ h.elim) (fun _ _ _ _ h ↦ h) hq4.2.2)
    (FW.call hfr9.sp (le_trans hle hN) hs4
      (fun p hp ↦ by have := Lb_le hp; omega)
      (fun _ _ _ _ h ↦ h) fw9) ?_ ?_ ?_ ?_ ?_
  · unfold rg; rw [hcs4 .X19 (by decide)]
    show rg st.data .X19 = _
    rw [rv hma r19, ld0, f96]
  · apply UInt64.toBitVec_inj.mp
    show rg m4 .X28 = _
    unfold rg; rw [hcs4 .X28 (by decide)]
    show rg st.data .X28 = _
    rw [rv hma r28, ld1, hwt, wrd 0 (by omega), NativeRustcVm.addr_add_zero]; rfl
  · apply UInt64.toBitVec_inj.mp
    show rg m4 .X23 = _
    unfold rg; rw [hcs4 .X23 (by decide)]
    show rg st.data .X23 = _
    rw [rv hma r23, ld1, hwt, wrd 8 (by omega)]; rfl
  · show (m4.regs.getXReg .X22).toNat = _
    rw [hcs4 .X22 (by decide), k9r .X22 (by simp), kr .X22 (by simp)]; exact x22
  · have hF := Pre.fms h
    have hi' : i < forms.size := by rw [hF.size]; exact hi
    have hrow : (forms.getD i #[]).size = 3 := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some]
      exact hF.row_size i hi'
    rw [hq4.1, e0, e1, e2, e3, hvals, map_three hrow]
    unfold slice
    rw [show (3 : UInt64).toNat = 3 from rfl, ewsOf_in h hfr9 (n := 3) fpr]
    rfl
end

end NativeRustcVmArm.Tables.TableTerms
