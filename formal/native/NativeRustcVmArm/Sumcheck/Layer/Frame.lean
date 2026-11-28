module

public import NativeRustcVmArm.Code.Vm.SumcheckOfVerifyLayer.Names
public import NativeRustcVmArm.Sumcheck.Layer.Exec
public import NativeRustcVmArm.Sumcheck.Loop

/-!
# `sumcheck` with `verify_layer`'s closure: the frame, the entry, the exits

The 176-byte frame (`FrL`, `Ring.Fr`, outputs the slots and the `TState`): the saved X30, X25,
…, X19 from `112` (`slotsL`), X26 to X29 kept. The loop's head `.L2` after `i < n` rounds (`Inv`:
X19 the output, X20 slot `i`, X21 the point's size, X22 the `TState`, X23 `i`, X24 the slots' end,
X25 the point's coordinate `i` plus `8`, X26 kept, X2, X3 the claim, `Rounds`); `.L7` after the
last (`Done`). `n` is X7 (`LPre`). `entry_spec`: `b0`, `b1` to the head, or to `.L7`
without slots; `exit_done` (`b10`, `b12`): the claim at the output; `exit_fail` (`b11`, `b12`):
`None`.
-/

namespace NativeRustcVmArm.Sumcheck.Layer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SumcheckOfVerifyLayer
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck

@[expose] public section

/-- The saved registers' slots. -/
def slotsL : List (Nat × XReg) :=
  [(112, .X30), (120, .X25), (128, .X24), (136, .X23), (144, .X22), (152, .X21), (160, .X20),
    (168, .X19)]

/-- The callee-saved registers the function keeps. -/
def keepL : List XReg := [.X26, .X27, .X28, .X29]

/-- The `TState`, the output, the slots, the point, the count, the claim at the entry. -/
abbrev tL (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
abbrev outL (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
abbrev slL (m0 : MachineData) : BitVec 64 := m0.regs.X6.toBitVec
abbrev ptL (m0 : MachineData) : BitVec 64 := m0.regs.X4.toBitVec
abbrev claimL (m0 : MachineData) : EW := ⟨m0.regs.X2, m0.regs.X3⟩

/-- The precondition, `n` the slots' count. -/
def LPre [Labels] (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m0 : MachineData) : Prop :=
  SumcheckLayerPre a s pt m0 ∧ n = m0.regs.X7.toNat

/-- The outputs during the loop: the slots and the `TState`. -/
def outsL (m0 : MachineData) (n : Nat) (q : BitVec 64) : Prop :=
  InRange (slL m0) (16 * n) q ∨ InRange (tL m0) tstateBytes q

/-- The frame. -/
abbrev FrL [Labels] (m0 : MachineData) (n : Nat) (m : MachineData) : Prop :=
  Fr m0 176 sumcheckLayerStack slotsL keepL (outsL m0 n) m

/-- The model's run after `i` rounds. -/
abbrev RoundsL (a : DecArea) (s : TState) (pt : Array EW) (m0 : MachineData) (d : Mem 64)
    (i : Nat) (c : EW) : Prop :=
  Rounds d (tL m0) a (slL m0) (claimL m0) (3) (fun j ↦ pt[j]?) s i c

/-- **The loop's invariant** at `.L2`, `i < n` rounds done. -/
structure Inv [Labels] (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m0 : MachineData)
    (i : Nat) (m : MachineData) : Prop where
  fr : FrL m0 n m
  lt : i < n
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  x20 : (m.regs.getXReg .X20).toBitVec = slL m0 + BitVec.ofNat 64 (16 * i)
  x21 : m.regs.getXReg .X21 = m0.regs.X5
  x26 : m.regs.getXReg .X26 = m0.regs.getXReg .X26
  x22 : m.regs.getXReg .X22 = m0.regs.X1
  x23 : (m.regs.getXReg .X23).toNat = i
  x24 : (m.regs.getXReg .X24).toBitVec = slL m0 + BitVec.ofNat 64 (16 * n)
  x25 : (m.regs.getXReg .X25).toBitVec = ptL m0 + BitVec.ofNat 64 (16 * i + 8)
  run : RoundsL a s pt m0 m.dmem i ⟨m.regs.X2, m.regs.X3⟩

/-- At `.L7`: every round done. -/
structure Done [Labels] (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m0 : MachineData)
    (m : MachineData) : Prop where
  fr : FrL m0 n m
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  run : RoundsL a s pt m0 m.dmem n ⟨m.regs.X2, m.regs.X3⟩

end

public section

variable [Host] {a : DecArea} {s : TState} {pt : Array EW} {n : Nat} {m0 : MachineData} {k : Nat}

theorem geo (h : LPre a s pt n m0) :
    Geo a s m0 (tL m0) (outL m0) (slL m0) (3) n sumcheckLayerStack 176 slotsL (outsL m0 n) :=
  ⟨h.2 ▸ h.1.1, fun _ h ↦ h.elim (fun h ↦ .inr (.inl h)) (fun h ↦ .inr (.inr h)), fun _ h ↦ .inr h,
    fun _ h ↦ .inl h, by decide, by decide, by decide, by decide⟩

omit [Host] in
theorem keepL_saved : ∀ r ∈ keepL, calleeSaved r = true := by decide

omit [Host] in
theorem slotsL8 : ∀ p ∈ slotsL, p.1 + 8 ≤ 176 := by decide

/-- **The point kept** in a state of the frame. -/
theorem pt_keep (hpre : LPre a s pt n m0) {m : MachineData} (hf : FrL m0 n m) :
    NativeRustcVm.EWsAt m.dmem (ptL m0) pt.toList := by
  obtain ⟨⟨-, -, hpt, hnw, hst, hat, has⟩, rfl⟩ := id hpre
  have g := geo hpre
  refine NativeRustcVm.BytesAt.of_sameOutside hpt hf.same fun j hj hq ↦ ?_
  rw [NativeRustcVm.length_ewsBytes, Array.length_toList] at hj
  have hin : InRange (ptL m0) (16 * pt.size) (ptL m0 + BitVec.ofNat 64 j) := by
    unfold NoWrap at hnw
    exact NativeRustcVm.inRange_add hj (by omega)
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange hst hnw g.stack_noWrap hin hq
  · exact NativeRustcVm.Apart.not_inRange has hnw g.slOk.2.1 hin hq
  · exact NativeRustcVm.Apart.not_inRange hat hnw g.ctx.fp.1.2 hin hq

/-- **The exits' common part**: from the frame, `ds` (`b10` or `b11`) from `outS` to `.L9`,
then `b12`. -/
theorem exit_of (hp : Placed code k) (hpre : LPre a s pt n m0) {m : MachineData}
    (hf : FrL m0 n m) (hx19 : m.regs.getXReg .X19 = m0.regs.X0) {ds : List Directive} {j : Nat}
    {S1 S2 : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog j) (hx1 : exec ds outS = some (S1, x))
    (hpc1 : ∀ st, PcOk (Env.ofMachine m [(base m0 176, 176), (outL m0, 24)]) x
      (Host.addrOf (j + ds.length)) st → st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b12Offset))
    (hx2 : exec b12 S1 = some (S2, .ret))
    (hok : exitOk S2 176 slotsL keepL = true) (hW : ∀ w ∈ S2.mem, w.r = 1 ∧ w.off + w.n ≤ 24)
    {r : Option ((Array EW × EW) × TState)}
    (hr : r = (sumcheckFn (claimL m0) (3) (fun j ↦ pt[j]?) n).run s)
    (hxs : ∀ xs c s', r = some ((xs, c), s') →
      xs.toList.length ≤ n ∧ NativeRustcVm.EWsAt m.dmem (slL m0) xs.toList)
    (hts : NextAt m.dmem (tL m0) a r)
    (hout : ∀ st : MachineState,
      Match (Env.ofMachine m [(base m0 176, 176), (outL m0, 24)]) S2 st.data →
      OptEWAt st.data.dmem (outL m0) (r.map (·.1.2))) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ SumcheckLayerPost a s pt m0 st.data) ⟨m, Host.addrOf j⟩ := by
  obtain ⟨hpre', rfl⟩ := id hpre
  have g := geo hpre
  have hS := hpre.1.1.1
  have hk12 : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b12Offset) := b12_in_code.trans hp.1 (by simp [b12])
  have hwf : (Env.ofMachine m [(base m0 176, 176), (outL m0, 24)]).WF :=
    Bus.wf_frame2 hS (by decide) hf.kept ⟨g.outOk.1, g.outOk.2.1⟩ g.outOk.2.2.2.2.1
  have hm : Match (Env.ofMachine m [(base m0 176, 176), (outL m0, 24)]) outS m := by
    have := Bus.match_frame2 (r := .X19) (n := 24) hS (by decide) (by decide) hf.sp
    rwa [hx19] at this
  refine exec_then hk hx1 hwf hm fun st1 hm1 hpc1' ↦ ?_
  refine exec_at hk12 hx2 hwf (hpc1 st1 hpc1') hm1 fun st hm' hpc ↦ Eventually.done _ ?_
  obtain ⟨hret, hsv⟩ := Fr.exit hf hm' hwf hok
  have hwr : ∀ q, Written (Env.ofMachine m [(base m0 176, 176), (outL m0, 24)]) S2 q →
      InRange (outL m0) 24 q := fun q hq ↦ Written.inRange (r := 1) rfl g.outOk.2.1 hW hq
  have hs := hm'.sameOutside hwf
  refine ⟨hpc.trans hret, ?_, ?_, hsv⟩
  · rw [← hr]
    refine ⟨hout st hm', fun xs c s' h ↦ g.sl_keep hs (fun q hq ↦ .inr (.inr (hwr q hq)))
      (hxs xs c s' h).1 (hxs xs c s' h).2, fun x s' h ↦
        g.t_keep hs (hm'.kept hwf) (fun q hq ↦ .inr (.inr (hwr q hq))) (hts x s' h)⟩
  · refine NativeRustcVm.SameOutside.mono (NativeRustcVm.SameOutside.trans hf.same hs)
      fun q hq ↦ ?_
    rcases hq with (hq | hq | hq) | hq
    · exact .inr (.inr (.inr hq))
    · exact .inr (.inl hq)
    · exact .inr (.inr (.inl hq))
    · exact .inl (hwr q hq)

/-- **`b10`, `b12`**: every round done, the claim into the output, the exit. -/
theorem exit_done (hp : Placed code k) (hpre : LPre a s pt n m0) {m : MachineData}
    (hd : Done a s pt n m0 m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ SumcheckLayerPost a s pt m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b10Offset)⟩ := by
  obtain ⟨xs, sn, hrun, hsz, hxs, hts⟩ := hd.run
  have hk10 : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b10Offset) := b10_in_code.trans hp.1 (by simp [b10])
  refine exit_of hp hpre hd.fr hd.x19 hk10 run_b10 (fun st h ↦ h.trans (hp.label (j := NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b12Offset) NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.label_9_at))
    (by rw [← after_eq run_b10]; exact run_b12a) (by decide) (by decide) hrun.symm
    (fun xs' c s' h ↦ by cases h; exact ⟨by simp [hsz], hxs⟩) (fun x s' h ↦ by cases h; exact hts)
    fun st hm' ↦ ?_
  have w0 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 1) (o := 0) rfl (by decide)
    (v := .lit 1) (by decide +kernel)
  have w8 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 1) (o := 8) rfl (by decide)
    (v := .reg .X2) (by decide +kernel)
  have w16 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 1) (o := 16) rfl (by decide)
    (v := .reg .X3) (by decide +kernel)
  rw [NativeRustcVm.addr_add_zero] at w0
  refine ⟨w0, ?_⟩
  rw [NativeRustcVm.ewAt_iff]
  refine ⟨w8, ?_⟩
  rw [NativeRustcVm.addr_add_add]
  exact w16

/-- **`b11`, `b12`**: a rejected round, `None` into the output, the exit. -/
theorem exit_fail (hp : Placed code k) (hpre : LPre a s pt n m0) {m : MachineData}
    (hf : FrL m0 n m) (hx19 : m.regs.getXReg .X19 = m0.regs.X0)
    (hnone : (sumcheckFn (claimL m0) (3) (fun j ↦ pt[j]?) n).run s = none) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ SumcheckLayerPost a s pt m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b11Offset)⟩ := by
  have hk11 : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b11Offset) := b11_in_code.trans hp.1 (by simp [b11])
  refine exit_of hp hpre hf hx19 hk11 run_b11 (fun st h ↦ h)
    (by rw [← after_eq run_b11]; exact run_b12b) (by decide) (by decide) (r := none) hnone.symm
    (fun _ _ _ h ↦ (nomatch h)) (fun _ _ h ↦ (nomatch h)) fun st hm' ↦ ?_
  have w0 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 1) (o := 0) rfl (by decide)
    (v := .lit 0) (by decide +kernel)
  rw [NativeRustcVm.addr_add_zero] at w0
  exact w0

omit [Host] in
/-- `x <<< 4` is `16 x`. -/
theorem shl4 (x : BitVec 64) : x <<< 4 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq]
  congr 1
  omega

/-- **The entry**: `b0` saves the registers; without slots at `.L7`, else `b1` and the loop's
head with no round done. -/
theorem entry_spec (hp : Placed code k) (hpre : LPre a s pt n m0) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b10Offset) ∧ Done a s pt n m0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b2Offset) ∧ Inv a s pt n m0 0 st.data))
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b0Offset)⟩ := by
  obtain ⟨hpre', rfl⟩ := id hpre
  have g := geo hpre
  have hS := hpre'.1.1
  have hwf : (Bus.env0 m0 176).WF := Bus.wf_env0 hS (by decide)
  have hm : Match (Bus.env0 m0 176) entryS m0 := Bus.match_entry hS (by decide) (by decide)
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b0Offset) := b0_in_code.trans hp.1 (by simp [b0])
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b1Offset) := b1_in_code.trans hp.1 (by simp [b1])
  have hl7 : Labels.label NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b10Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.b10Offset) NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.label_7_at
  have hts0 := g.ok.2.2.1
  have hpro : ∀ {S : SState} {st : MachineState}, Match (Bus.env0 m0 176) S st.data →
      S.mem = (after b0 entryS).mem → S.sp = .ptr 0 0 →
      (∀ r ∈ keepL, S.reg r = some (.reg r)) →
      FrL m0 m0.regs.X7.toNat st.data ∧ TStateAt st.data.dmem (tL m0) a s := by
    intro S st hmS hmem hsp hkeep
    have hW : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 176 := by
      rw [hmem, after_eq run_b0]; decide +kernel
    refine ⟨Fr.ofPrologue (F := 176) (rs := []) g.hN (by decide) hmS hwf hsp
      (by rw [show slotsOk S slotsL = slotsOk (after b0 entryS) slotsL from by
            simp only [slotsOk, hmem]]
          rw [after_eq run_b0]; decide +kernel) (by decide) hW hkeep, ?_⟩
    refine g.t_keep (hmS.sameOutside hwf) (hmS.kept hwf) (fun q hq ↦ .inl ?_) hts0
    exact g.ctx.inRange_frame
      (Written.inRange rfl (base_noWrap (le_trans (by decide) g.hN)) hW hq)
  refine exec_then hk0 run_b0 hwf hm fun st hm' hpc ↦ ?_
  have hm0 : Match (Bus.env0 m0 176) (after b0 entryS) st.data := by
    rw [after_eq run_b0]; exact hm'
  obtain ⟨hfr, hts⟩ := hpro hm0 rfl (by rw [after_eq run_b0])
    (by rw [after_eq run_b0]; decide +kernel)
  have hc : (SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X7) (.lit 0)).eval (Bus.env0 m0 176) =
      (m0.regs.X7.toBitVec == 0#64) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]; rfl
  simp only [PcOk] at hpc
  rw [hc] at hpc
  have hx2 : st.data.regs.X2 = m0.regs.X2 := UInt64.toBitVec_inj.mp ((hm'.regs .X2 _ rfl).trans rfl)
  have hx3 : st.data.regs.X3 = m0.regs.X3 := UInt64.toBitVec_inj.mp ((hm'.regs .X3 _ rfl).trans rfl)
  by_cases h0 : m0.regs.X7 = 0
  · have h0' : (m0.regs.X7.toBitVec == 0#64) = true := by rw [h0]; rfl
    simp only [h0', ↓reduceIte] at hpc
    refine Eventually.done _ (Or.inl ⟨hpc.trans hl7, hfr,
      UInt64.toBitVec_inj.mp ((hm'.regs .X19 _ rfl).trans rfl), ?_⟩)
    rw [hx2, hx3, show m0.regs.X7.toNat = 0 by simp [h0]]
    exact rounds_zero hts
  · have h0' : (m0.regs.X7.toBitVec == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun h ↦ h0 (UInt64.toBitVec_inj.mp h)
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at hpc
    refine exec_at hk1 run_b1 hwf hpc hm0 fun st1 hm1 hpc1 ↦ ?_
    have hm1' : Match (Bus.env0 m0 176) (after b1 (after b0 entryS)) st1.data := by
      rw [after_eq run_b1]; exact hm1
    obtain ⟨hfr1, hts1⟩ := hpro hm1' (by rw [after_eq run_b1, after_eq run_b0])
      (by rw [after_eq run_b1]) (by rw [after_eq run_b1]; decide +kernel)
    have hn : 0 < m0.regs.X7.toNat :=
      Nat.pos_of_ne_zero fun h ↦ h0 (UInt64.toNat_inj.mp (by simpa using h))
    have hx2' : st1.data.regs.X2 = m0.regs.X2 :=
      UInt64.toBitVec_inj.mp ((hm1.regs .X2 _ rfl).trans rfl)
    have hx3' : st1.data.regs.X3 = m0.regs.X3 :=
      UInt64.toBitVec_inj.mp ((hm1.regs .X3 _ rfl).trans rfl)
    refine Eventually.done _ (Or.inr ⟨hpc1, hfr1, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · exact UInt64.toBitVec_inj.mp ((hm1.regs .X19 _ rfl).trans rfl)
    · rw [hm1.regs .X20 _ rfl]; simp [Sym.eval, Bus.env0]; rfl
    · exact UInt64.toBitVec_inj.mp ((hm1.regs .X21 _ rfl).trans rfl)
    · exact UInt64.toBitVec_inj.mp ((hm1.regs .X26 _ rfl).trans rfl)
    · exact UInt64.toBitVec_inj.mp ((hm1.regs .X22 _ rfl).trans rfl)
    · rw [UInt64.toNat, hm1.regs .X23 _ rfl]; rfl
    · rw [hm1.regs .X24 _ rfl]
      simp only [Sym.eval, BinOp.apply, UnOp.apply, Sym.low_W64, Sym.ext_W64]
      show m0.regs.X6.toBitVec + m0.regs.X7.toBitVec <<< 4 = _
      rw [shl4]
      rfl
    · rw [hm1.regs .X25 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
      rfl
    · rw [hx2', hx3']
      exact rounds_zero hts1
end

end NativeRustcVmArm.Sumcheck.Layer
