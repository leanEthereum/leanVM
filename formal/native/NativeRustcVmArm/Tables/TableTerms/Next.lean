module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Tables.TableTerms.Ext

/-!
# `table_terms`: the end of table `i`

`b12` advances the weight's address and calls `EW::mul` on the weight and the summand plus the
forms' sum (`mul_step`); `b13` adds the product to the running sum, advances the walking registers
and the cursor, and loops to the head before table `i + 1` (or falls to `b14` after the sixth
table) (`next_step`).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Layout NativeRustcVmArm.Vm.TableTerms
open NativeRustcVm (wordOf ewsOf ewOf BufEWAt)
open NativeRustcVmArm.Bus (after)

@[expose] public section

/-- Table `i`'s constraints' sum. -/
abbrev smC (m0 : MachineData) (i : Nat) (xs : Array EW) : EW :=
  dot ((cpw m0).extract (cursorAt i) (cursorAt i + (tb i).nConstraints))
    (constraintsW (tb i).opcode xs)

/-- Table `i`'s forms' sum. -/
abbrev smF (forms : Array (Array FormW)) (m0 : MachineData) (i : Nat) (xs : Array EW) : EW :=
  dot (fpw m0) ((forms.getD i #[]).map (·.evaluate xs))

/-- The accumulator after table `i`. -/
abbrev accN (heights : Array Nat) (forms : Array (Array FormW)) (m0 : MachineData) (i : Nat)
    (f : EW) (o : Array (Array EW × Array EW)) (xs : Array EW) : Acc :=
  (cursorAt i + (tb i).nConstraints, f + wt m0 i * (smC m0 i xs + smF forms m0 i xs),
    o.push (pti heights m0 i, xs))

end

public section

theorem mul_le : 288 + ewMulStack ≤ N := by rw [N_eq]; decide

theorem next_cs : ∀ r ∈ [XReg.X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
    r ∈ cs := by simp [cs]

theorem ew_add_c0 (a b : EW) : (a + b).c0 = a.c0 ^^^ b.c0 := rfl
theorem ew_add_c1 (a b : EW) : (a + b).c1 = a.c1 ^^^ b.c1 := rfl
theorem ew_eta (x : EW) : (⟨x.c0, x.c1⟩ : EW) = x := rfl
theorem ew_mul_eq (a b : EW) : EW.mul a b = a * b := rfl

variable {heights : Array Nat} {forms : Array (Array FormW)} {m0 : MachineData} {s : TState}

/-- The fold over the first `i + 1` rows. -/
theorem preRun_next (hh : heights.size = 6) (hf : forms.size = 6) {i : Nat} (hi : i < 6)
    {f : EW} {o : Array (Array EW × Array EW)} {si s' : TState} {xs : Array EW}
    (hrun : preRun heights forms m0 i s = some ((cursorAt i, f, o), si))
    (hr : (readScalars (tb i).width).run si = some (xs, s')) :
    preRun heights forms m0 (i + 1) s = some (accN heights forms m0 i f o xs, s') := by
  rw [preRun_succ hh hf hi, hrun]
  show (stp m0 (cursorAt i, f, o) _).run si = _
  rw [stp_run, hr]
  rfl

variable [Host] {k : Nat} {a : DecArea}

/-- **The product** (`b12`, `EW::mul`). -/
theorem mul_step (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {R : MachineState → Prop}
    {i : Nat} (hi : i < 6) {f : EW} {o : Array (Array EW × Array EW)} {s' : TState}
    {xs : Array EW} {m : MachineData} (H : It a m0 i o xs s' m)
    (hw : FW m0 m (Lt m0 i f (smC m0 i xs)))
    (x19 : rg m .X19 = wp m0 + BitVec.ofNat 64 (8 + 16 * i))
    (x28 : m.regs.X28 = (wt m0 i).c0) (x23 : m.regs.X23 = (wt m0 i).c1)
    (x24 : m.regs.X24 = (smF forms m0 i xs).c0) (x25 : m.regs.X25 = (smF forms m0 i xs).c1)
    (hpt : BufEWAt m.dmem (evi m0 i) 30 (pti heights m0 i).toList)
    (cont : ∀ m2, It a m0 i o xs s' m2 →
      FW m0 m2 (lws m0 (i + 1) ++ [(80, f.c1.toBitVec), (88, f.c0.toBitVec)]) →
      BufEWAt m2.dmem (evi m0 i) 30 (pti heights m0 i).toList →
      (∀ r ∈ [XReg.X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
        m2.regs.getXReg r = m.regs.getXReg r) →
      Fr m0 288 N slots [] (outs m0) m2 →
      ewRet m2 = wt m0 i * (smC m0 i xs + smF forms m0 i xs) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b13Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b12Offset)⟩ := by
  have hS := Pre.stack h
  have hN := spN h
  have c0 := ctx h
  have hwf := wf0 hS H.fr.kept
  have hm := match0 hS H.fr.sp (m := m)
  refine exec_then (hb12 hp) run_b12 hwf hm fun st hma0 hpc ↦ ?_
  have hma : Match (E0 m0 m) (after b12 sF) st.data := by rw [Bus.after_eq run_b12]; exact hma0
  obtain ⟨sp12, wok12, fok12, l96, k12, r0, r1, r2, r3⟩ := ok_b12
  have hfr1 := fr_block (szs := [288]) H.fr hN hm hma hwf (sp12.trans rfl) rfl
    (hout_none (L := [false]) (by decide)) wok12
  have k12r : ∀ r ∈ [XReg.X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
      st.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ rk hma (keeps_get k12 hr)
  have hwr1 : ∀ q, Written (E0 m0 m) (after b12 sF) q → InRange (stackBelow m0 N) N q :=
    fun q hq ↦ written_stack hN (wok_frame (by decide) wok12) hq
  have It1 : It a m0 i o xs s' st.data :=
    It.step h hi H hfr1 (hma.kept hwf) (hma.sameOutside hwf) (fun q hq ↦ .inl (hwr1 q hq))
      (FW.block hma hwf (L := cws m0) (fun p hp ↦ mem_of_all (by simp [cws]) hp) fok12 H.cw)
      fun r hr ↦ k12r r (by revert r hr; simp)
  have hw' : FW m0 m [(104, rg m0 .X6 + BitVec.ofNat 64 (8 * (i + 1))), (80, f.c1.toBitVec),
      (88, f.c0.toBitVec)] := fun p hp ↦ hw p (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp [Lt])
  have hwL := FW.block hma hwf (fun p hp ↦ mem_of_all (by simp) hp) fok12 hw'
  have fw1 : FW m0 st.data (lws m0 (i + 1) ++ [(80, f.c1.toBitVec), (88, f.c0.toBitVec)]) := by
    intro p hp
    simp only [lws, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · show fw m0 st.data 96 = _
      rw [fw_write hma hwf (by omega), l96, eval_add_lit]
      show rg m .X19 + _ = _
      rw [x19, NativeRustcVm.addr_add_add, show 8 + 16 * i + 16 = 8 + 16 * (i + 1) by ring]
    · exact hwL _ (by simp)
    · exact hwL _ (by simp)
    · exact hwL _ (by simp)
  have pt1 := pt_keep h hi (hma.sameOutside hwf) hwr1 hpt
  -- `EW::mul`.
  have f64 : fw m0 m 64 = (smC m0 i xs).c1.toBitVec := hw (64, _) (by simp [Lt])
  have f72 : fw m0 m 72 = (smC m0 i xs).c0.toBitVec := hw (72, _) (by simp [Lt])
  have e0 : st.data.regs.X0 = (wt m0 i).c0 :=
    UInt64.toBitVec_inj.mp ((rv hma r0).trans (congrArg UInt64.toBitVec x28))
  have e1 : st.data.regs.X1 = (wt m0 i).c1 :=
    UInt64.toBitVec_inj.mp ((rv hma r1).trans (congrArg UInt64.toBitVec x23))
  have e2 : st.data.regs.X2 = (smC m0 i xs + smF forms m0 i xs).c0 := by
    have := Bus.eval_eor (E0 m0 m) .X24 (.load 0 72 8) _ ((ld0 _ 72).trans f72)
    rw [← rv hma r2] at this
    rw [show st.data.regs.X2 = UInt64.ofBitVec (rg st.data .X2) from rfl, this, ew_add_c0,
      show UInt64.ofBitVec ((E0 m0 m).regs .X24) = m.regs.X24 from rfl, x24, UInt64.xor_comm]
  have e3 : st.data.regs.X3 = (smC m0 i xs + smF forms m0 i xs).c1 := by
    have := Bus.eval_eor (E0 m0 m) .X25 (.load 0 64 8) _ ((ld0 _ 64).trans f64)
    rw [← rv hma r3] at this
    rw [show st.data.regs.X3 = UInt64.ofBitVec (rg st.data .X3) from rfl, this, ew_add_c1,
      show UInt64.ofBitVec ((E0 m0 m).regs .X25) = m.regs.X25 from rfl, x25, UInt64.xor_comm]
  have hle := mul_le
  have hpc' : st.pc = Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel ∧ retOf st.data = Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b13Offset) :=
    ⟨hpc.1, hpc.2.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableTerms.b12_next]))⟩
  refine Bus.Gkr.Fr.callSpec hfr1 hN hle (fun _ h ↦ nomatch h) slots_le (outs_frame h) hmul
    hpc' (hfr1.stackOk hS rfl hle)
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun _ h ↦ .inl h, hq.2.2.2⟩)
    fun m2 hfr2 hq2 hcs2 ↦ ?_
  have hat := Bus.Gkr.Fr.at_ c0 hfr1 (outs_rc h)
  have hs2 : SameOutside st.data.dmem m2.dmem
      (fun q ↦ InRange (stackBelow st.data ewMulStack) ewMulStack q ∨ False) :=
    NativeRustcVm.SameOutside.mono hq2.2.2.1 fun _ h ↦ .inl h
  have fw2 : FW m0 m2 (lws m0 (i + 1) ++ [(80, f.c1.toBitVec), (88, f.c0.toBitVec)]) :=
    FW.call hfr1.sp (le_trans hle hN) hs2
      (fun p hp ↦ by
        simp only [lws, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> simp)
      (fun _ _ _ _ h ↦ h) fw1
  obtain ⟨q0, q1, q2, q3⟩ := hq2
  rw [e0, e1, e2, e3, ew_eta, ew_eta, ew_mul_eq] at q0 q1
  refine cont m2 (It.call h hi It1 hfr2 hle hs2 (fun _ h ↦ h.elim) (fun _ _ _ _ h ↦ h) q3)
    fw2 (pt_keep h hi q2 (fun q hq ↦ c0.inRange_stack hat hle hq) pt1)
    (fun r hr ↦ by rw [hcs2 r (cs_saved r (next_cs r hr)), k12r r hr]) hfr2 ?_
  show (⟨m2.regs.X0, m2.regs.X1⟩ : EW) = _
  rw [q0, q1, ew_eta]

/-- **The end of table `i`** (`b12`, `EW::mul`, `b13`). -/
theorem next_step (hp : Placed code k) (h : TableTermsPre a s heights forms m0)
    (hh : heights.size = 6) (hf : forms.size = 6)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {i : Nat} (hi : i < 6) {f : EW} {o : Array (Array EW × Array EW)} {si s' : TState}
    {xs : Array EW} (hrun : preRun heights forms m0 i s = some ((cursorAt i, f, o), si))
    (hr : (readScalars (tb i).width).run si = some (xs, s')) (hosz : o.size = i)
    {m : MachineData} (H : It a m0 i o xs s' m) (hw : FW m0 m (Lt m0 i f (smC m0 i xs)))
    (x19 : rg m .X19 = wp m0 + BitVec.ofNat 64 (8 + 16 * i))
    (x28 : m.regs.X28 = (wt m0 i).c0) (x23 : m.regs.X23 = (wt m0 i).c1)
    (x22 : (m.regs.X22).toNat = (tb i).nConstraints)
    (x24 : m.regs.X24 = (smF forms m0 i xs).c0) (x25 : m.regs.X25 = (smF forms m0 i xs).c1)
    (hpt : BufEWAt m.dmem (evi m0 i) 30 (pti heights m0 i).toList)
    (contL : i + 1 < 6 → ∀ m', Head a s heights forms m0 (i + 1) (accN heights forms m0 i f o xs)
      s' m' → Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b1Offset)⟩)
    (contE : i = 5 → ∀ m', Head a s heights forms m0 6 (accN heights forms m0 i f o xs) s' m' →
      Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b14Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s heights forms m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b12Offset)⟩ := by
  have hS := Pre.stack h
  refine mul_step hp h hmul hi H hw x19 x28 x23 x24 x25 hpt
    fun m2 It2 fw2 pt2 g2 hfr2 hprod ↦ ?_
  refine Bus.Gkr.Fr.runBlock hS (by rw [N_eq]; omega) rfl hfr2 (hb13 hp) run_b13 rfl rfl
    (by decide) (by decide) fun st3 hfr3 hd3 hm3 hpc3 ↦ ?_
  have hm3' : Match (E0 m0 m2) (after b13 sF) st3.data := by rw [Bus.after_eq run_b13]; exact hm3
  obtain ⟨-, -, k13, s19, s20, s22, s23, s26, s27, s29⟩ := ok_b13
  have R2 : ∀ {r : XReg}, r ∈ [XReg.X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29] →
      rg m2 r = rg m r := fun hr ↦ by unfold rg; rw [g2 _ hr]
  have hx29 : (rg m2 .X29).toNat = 240 - 40 * i := by
    rw [R2 (by simp), H.x29, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hc : SBool.eval (E0 m0 m2) (.not (.cmp .eq .W64 (.reg .X29) (.lit 40))) =
      !(decide (i = 5)) := by
    show (!CmpOp.eq.apply .W64 (m2.regs.getXReg .X29).toBitVec (BitVec.ofNat 64 40)) = _
    rw [cmp_eq_lit _ _ (by norm_num)]
    congr 1
    apply decide_eq_decide.mpr
    have : (m2.regs.getXReg .X29).toNat = 240 - 40 * i := hx29
    omega
  have ev3 : ∀ {r : XReg} {v : Sym}, (after b13 sF).reg r = some v →
      rg st3.data r = v.eval (E0 m0 m2) := fun hr ↦ rv hm3' hr
  have h22 : st3.data.regs.X22 = m2.regs.X0 ^^^ f.c0 := by
    have := Bus.eval_eor (E0 m0 m2) .X0 (.load 0 88 8) f.c0
      ((ld0 _ 88).trans (fw2 (88, f.c0.toBitVec) (by simp)))
    rw [← rv hm3' s22] at this
    exact this
  have h23 : st3.data.regs.X23 = m2.regs.X1 ^^^ f.c1 := by
    have := Bus.eval_eor (E0 m0 m2) .X1 (.load 0 80 8) f.c1
      ((ld0 _ 80).trans (fw2 (80, f.c1.toBitVec) (by simp)))
    rw [← rv hm3' s23] at this
    exact this
  have hrun' := preRun_next hh hf hi hrun hr
  have hevs : ∀ j (hj : j < (o.push (pti heights m0 i, xs)).size),
      TableEvalAt st3.data.dmem (evi m0 j) (o.push (pti heights m0 i, xs))[j] := by
    intro j hj
    rw [hd3]
    rw [Array.size_push] at hj
    by_cases hjo : j < o.size
    · rw [Array.getElem_push_lt hjo]
      exact It2.evs j hjo
    · have hje : j = o.size := by omega
      subst hje
      rw [Array.getElem_push_eq, hosz]
      exact ⟨pt2, It2.vals⟩
  have Hn : Head a s heights forms m0 (i + 1) (accN heights forms m0 i f o xs) s' st3.data := by
    refine ⟨hfr3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrun', (cursorAt_succ i).symm, ?_,
      hd3 ▸ It2.ts, hevs⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact FW.of_dmem hd3 It2.cw p hp
      · exact FW.of_dmem hd3 fw2 p (List.mem_append_left _ hp)
    · rw [ev3 s19]; exact It2.x21
    · unfold rg; rw [rk hm3' (keeps_get k13 (by simp))]; exact It2.x21
    · rw [ev3 s20, eval_add_lit]
      show rg m2 .X20 + _ = _
      rw [It2.x20, NativeRustcVm.addr_add_add, show 17784 * i + 17784 = 17784 * (i + 1) by ring]
    · rw [ev3 s27, eval_add_lit]
      show rg m2 .X27 + _ = _
      rw [It2.x27, evi, evi, NativeRustcVm.addr_add_add,
        show 1968 * i + 1968 = 1968 * (i + 1) by ring]
    · rw [ev3 s29]
      apply BitVec.eq_of_toNat_eq
      show (BinOp.apply .sub .W64 (rg m2 .X29) (BitVec.ofNat 64 40)).toNat = _
      rw [sub_lit _ _ (by rw [hx29]; omega), hx29, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [ev3 s26]
      show BinOp.apply .add .W64 (rg m2 .X22) (rg m2 .X26) = _
      have e22 : rg m2 .X22 = BitVec.ofNat 64 (tb i).nConstraints := by
        rw [R2 (by simp)]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := cursor_le hi; omega)]
        exact x22
      rw [e22, It2.x26]
      simp only [BinOp.apply, low_W64, ext_W64]
      rw [BitVec.ofNat_add_ofNat, cursorAt_succ, Nat.add_comm]
    · rw [h22]
      show _ = (f + wt m0 i * (smC m0 i xs + smF forms m0 i xs)).c0
      rw [ew_add_c0, ← hprod]
      exact UInt64.xor_comm _ _
    · rw [h23]
      show _ = (f + wt m0 i * (smC m0 i xs + smF forms m0 i xs)).c1
      rw [ew_add_c1, ← hprod]
      exact UInt64.xor_comm _ _
    · show (o.push _).size = _
      rw [Array.size_push, hosz]
  simp only [PcOk, hc] at hpc3
  by_cases h5 : i = 5
  · have hd : decide (i = 5) = true := decide_eq_true h5
    simp only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    have e6 : i + 1 = 6 := by omega
    rw [e6] at Hn
    exact Bus.Gkr.at_pc (hpc3.trans (addr_eq (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableTerms.b13_next]))) (contE h5 st3.data Hn)
  · have hd : decide (i = 5) = false := decide_eq_false h5
    simp only [hd, Bool.not_false, ↓reduceIte] at hpc3
    exact Bus.Gkr.at_pc (hpc3.trans (lbl_1 hp)) (contL (by omega) st3.data Hn)

end

end NativeRustcVmArm.Tables.TableTerms
