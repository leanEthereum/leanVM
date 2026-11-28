module

public import NativeRustcVmArm.Code.Vm.SumcheckOfGkrStep.Names
public import NativeRustcVmArm.Sumcheck.Gkr.Exec
public import NativeRustcVmArm.Sumcheck.Loop

/-!
# `sumcheck` with `gkr_step`'s closure: the frame, the entry, the exits

The 192-byte frame (`FrG`, `Ring.Fr`, outputs the slots and the `TState`): the saved X30 at
`112`, X26, …, X19 from `128` (`slotsG`), X27 to X29 kept. The loop's head `.L2` after `i < n`
rounds (`Inv`: X19 the output, X20 slot `i`, X21 the point's size, X22 the count, X23 the
`TState`, X24 `i`, X25 the slots' end, X26 the point's coordinate `i` plus `8`, X2, X3 the claim,
`Rounds`); `.L7` after the last (`Done`). `entry_spec`: `b0`, `b1` to the head, or to `.L7`
without slots; `exit_done` (`b10`, `b12`): the claim at the output; `exit_fail` (`b11`, `b12`):
`None`.
-/

namespace NativeRustcVmArm.Sumcheck.Gkr

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SumcheckOfGkrStep
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck

@[expose] public section

/-- The saved registers' slots. -/
def slotsG : List (Nat × XReg) :=
  [(112, .X30), (128, .X26), (136, .X25), (144, .X24), (152, .X23), (160, .X22), (168, .X21),
    (176, .X20), (184, .X19)]

/-- The callee-saved registers the function keeps. -/
def keepG : List XReg := [.X27, .X28, .X29]

/-- The `TState`, the output, the slots, the point, the count, the claim at the entry. -/
abbrev tG (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
abbrev outG (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
abbrev slG (m0 : MachineData) : BitVec 64 := m0.regs.X7.toBitVec
abbrev ptG (m0 : MachineData) : BitVec 64 := m0.regs.X5.toBitVec
abbrev cntG (m0 : MachineData) : Nat := m0.regs.X4.toNat
abbrev claimG (m0 : MachineData) : EW := ⟨m0.regs.X2, m0.regs.X3⟩

/-- The outputs during the loop: the slots and the `TState`. -/
def outsG (m0 : MachineData) (n : Nat) (q : BitVec 64) : Prop :=
  InRange (slG m0) (16 * n) q ∨ InRange (tG m0) tstateBytes q

/-- The frame. -/
abbrev FrG [Labels] (m0 : MachineData) (n : Nat) (m : MachineData) : Prop :=
  Fr m0 192 sumcheckGkrStack slotsG keepG (outsG m0 n) m

/-- The model's run after `i` rounds. -/
abbrev RoundsG (a : DecArea) (s : TState) (pt : Array EW) (m0 : MachineData) (d : Mem 64)
    (i : Nat) (c : EW) : Prop :=
  Rounds d (tG m0) a (slG m0) (claimG m0) (cntG m0) (fun j ↦ pt[j]?) s i c

/-- **The loop's invariant** at `.L2`, `i < n` rounds done. -/
structure Inv [Labels] (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m0 : MachineData)
    (i : Nat) (m : MachineData) : Prop where
  fr : FrG m0 n m
  lt : i < n
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  x20 : (m.regs.getXReg .X20).toBitVec = slG m0 + BitVec.ofNat 64 (16 * i)
  x21 : m.regs.getXReg .X21 = m0.regs.X6
  x22 : m.regs.getXReg .X22 = m0.regs.X4
  x23 : m.regs.getXReg .X23 = m0.regs.X1
  x24 : (m.regs.getXReg .X24).toNat = i
  x25 : (m.regs.getXReg .X25).toBitVec = slG m0 + BitVec.ofNat 64 (16 * n)
  x26 : (m.regs.getXReg .X26).toBitVec = ptG m0 + BitVec.ofNat 64 (16 * i + 8)
  run : RoundsG a s pt m0 m.dmem i ⟨m.regs.X2, m.regs.X3⟩

/-- At `.L7`: every round done. -/
structure Done [Labels] (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m0 : MachineData)
    (m : MachineData) : Prop where
  fr : FrG m0 n m
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  run : RoundsG a s pt m0 m.dmem n ⟨m.regs.X2, m.regs.X3⟩

end

public section

variable [Host] {a : DecArea} {s : TState} {pt : Array EW} {n : Nat} {m0 : MachineData} {k : Nat}

theorem geo (h : SumcheckGkrPre a s pt n m0) :
    Geo a s m0 (tG m0) (outG m0) (slG m0) (cntG m0) n sumcheckGkrStack 192 slotsG (outsG m0 n) :=
  ⟨h.1, fun _ h ↦ h.elim (fun h ↦ .inr (.inl h)) (fun h ↦ .inr (.inr h)), fun _ h ↦ .inr h,
    fun _ h ↦ .inl h, by decide, by decide, by decide, by decide⟩

omit [Host] in
theorem keepG_saved : ∀ r ∈ keepG, calleeSaved r = true := by decide

omit [Host] in
theorem slotsG8 : ∀ p ∈ slotsG, p.1 + 8 ≤ 192 := by decide

/-- **The point kept** in a state of the frame. -/
theorem pt_keep (hpre : SumcheckGkrPre a s pt n m0) {m : MachineData} (hf : FrG m0 n m) :
    NativeRustcVm.EWsAt m.dmem (ptG m0) pt.toList := by
  have g := geo hpre
  obtain ⟨-, -, hpt, hnw, hst, hat, has, -⟩ := hpre
  refine NativeRustcVm.BytesAt.of_sameOutside hpt hf.same fun j hj hq ↦ ?_
  rw [NativeRustcVm.length_ewsBytes, Array.length_toList] at hj
  have hin : InRange (ptG m0) (16 * pt.size) (ptG m0 + BitVec.ofNat 64 j) := by
    unfold NoWrap at hnw
    exact NativeRustcVm.inRange_add hj (by omega)
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange hst hnw g.stack_noWrap hin hq
  · exact NativeRustcVm.Apart.not_inRange has hnw g.slOk.2.1 hin hq
  · exact NativeRustcVm.Apart.not_inRange hat hnw g.ctx.fp.1.2 hin hq

/-- **The exits' common part**: from the frame, `ds` (`b10` or `b11`) from `outS` to `.L9`,
then `b12`. -/
theorem exit_of (hp : Placed code k) (hpre : SumcheckGkrPre a s pt n m0) {m : MachineData}
    (hf : FrG m0 n m) (hx19 : m.regs.getXReg .X19 = m0.regs.X0) {ds : List Directive} {j : Nat}
    {S1 S2 : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog j) (hx1 : exec ds outS = some (S1, x))
    (hpc1 : ∀ st, PcOk (Env.ofMachine m [(base m0 192, 192), (outG m0, 24)]) x
      (Host.addrOf (j + ds.length)) st → st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b12Offset))
    (hx2 : exec b12 S1 = some (S2, .ret))
    (hok : exitOk S2 192 slotsG keepG = true) (hW : ∀ w ∈ S2.mem, w.r = 1 ∧ w.off + w.n ≤ 24)
    {r : Option ((Array EW × EW) × TState)}
    (hr : r = (sumcheckFn (claimG m0) (cntG m0) (fun j ↦ pt[j]?) n).run s)
    (hxs : ∀ xs c s', r = some ((xs, c), s') →
      xs.toList.length ≤ n ∧ NativeRustcVm.EWsAt m.dmem (slG m0) xs.toList)
    (hts : NextAt m.dmem (tG m0) a r)
    (hout : ∀ st : MachineState,
      Match (Env.ofMachine m [(base m0 192, 192), (outG m0, 24)]) S2 st.data →
      OptEWAt st.data.dmem (outG m0) (r.map (·.1.2))) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ SumcheckGkrPost a s pt n m0 st.data) ⟨m, Host.addrOf j⟩ := by
  have g := geo hpre
  have hS := hpre.1.1
  have hk12 : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b12Offset) := b12_in_code.trans hp.1 (by simp [b12])
  have hwf : (Env.ofMachine m [(base m0 192, 192), (outG m0, 24)]).WF :=
    Bus.wf_frame2 hS (by decide) hf.kept ⟨g.outOk.1, g.outOk.2.1⟩ g.outOk.2.2.2.2.1
  have hm : Match (Env.ofMachine m [(base m0 192, 192), (outG m0, 24)]) outS m := by
    have := Bus.match_frame2 (r := .X19) (n := 24) hS (by decide) (by decide) hf.sp
    rwa [hx19] at this
  refine exec_then hk hx1 hwf hm fun st1 hm1 hpc1' ↦ ?_
  refine exec_at hk12 hx2 hwf (hpc1 st1 hpc1') hm1 fun st hm' hpc ↦ Eventually.done _ ?_
  obtain ⟨hret, hsv⟩ := Fr.exit hf hm' hwf hok
  have hwr : ∀ q, Written (Env.ofMachine m [(base m0 192, 192), (outG m0, 24)]) S2 q →
      InRange (outG m0) 24 q := fun q hq ↦ Written.inRange (r := 1) rfl g.outOk.2.1 hW hq
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
theorem exit_done (hp : Placed code k) (hpre : SumcheckGkrPre a s pt n m0) {m : MachineData}
    (hd : Done a s pt n m0 m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ SumcheckGkrPost a s pt n m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b10Offset)⟩ := by
  obtain ⟨xs, sn, hrun, hsz, hxs, hts⟩ := hd.run
  have hk10 : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b10Offset) := b10_in_code.trans hp.1 (by simp [b10])
  refine exit_of hp hpre hd.fr hd.x19 hk10 run_b10 (fun st h ↦ h.trans (hp.label (j := NativeRustcVmArm.Vm.SumcheckOfGkrStep.b12Offset) NativeRustcVmArm.Vm.SumcheckOfGkrStep.label_9_at))
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
theorem exit_fail (hp : Placed code k) (hpre : SumcheckGkrPre a s pt n m0) {m : MachineData}
    (hf : FrG m0 n m) (hx19 : m.regs.getXReg .X19 = m0.regs.X0)
    (hnone : (sumcheckFn (claimG m0) (cntG m0) (fun j ↦ pt[j]?) n).run s = none) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ SumcheckGkrPost a s pt n m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b11Offset)⟩ := by
  have hk11 : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b11Offset) := b11_in_code.trans hp.1 (by simp [b11])
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

/-- **The entry**: `b0` saves the registers and loads `n`; without slots at `.L7`, else `b1` and
the loop's head with no round done. -/
theorem entry_spec (hp : Placed code k) (hpre : SumcheckGkrPre a s pt n m0) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b10Offset) ∧ Done a s pt n m0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b2Offset) ∧ Inv a s pt n m0 0 st.data))
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b0Offset)⟩ := by
  have g := geo hpre
  have hS := hpre.1.1
  obtain ⟨-, -, -, -, -, -, -, hn64, hwn, hnw8⟩ := hpre
  have hN := g.hN
  have hSP := m0.regs.SP.toNat_lt
  have hbt := base_toNat (m0 := m0) (F := 192) (le_trans (by decide) hN)
  have hsp192 : base m0 192 + BitVec.ofNat 64 192 = m0.regs.SP.toBitVec := base_add_eq
  have hmap : NativeRustcVm.Mapped m0.dmem (base m0 192) 200 := by
    refine NativeRustcVm.mapped_append_iff (n := 192) (m := 8) |>.2
      ⟨(Bus.frame_mapped hS (le_trans (by decide) (le_refl _))).1, ?_⟩
    rw [hsp192]; exact hwn.mapped
  have hwf : (Env.ofMachine m0 [(base m0 192, 200)]).WF := by
    refine Env.wf_of ⟨⟨hmap, ?_⟩, trivial⟩ (List.pairwise_singleton _ _)
    have := hnw8
    unfold NoWrap at this
    have e : m0.regs.SP.toNat = m0.regs.SP.toBitVec.toNat := rfl
    have h192 : 192 ≤ m0.regs.SP.toNat := le_trans (by decide) hN
    show (base m0 192).toNat + 200 ≤ _
    rw [hbt]; omega
  have hm : Match (Env.ofMachine m0 [(base m0 192, 200)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS (le_trans (by decide) (le_refl _)) rfl,
      trivial⟩ (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero,
        Option.map_some, Option.getD_some]; rw [show BitVec.ofInt 64 192 = BitVec.ofNat 64 192
          from rfl, hsp192]) trivial trivial trivial trivial
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b0Offset) := b0_in_code.trans hp.1 (by simp [b0])
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b1Offset) := b1_in_code.trans hp.1 (by simp [b1])
  have hl7 : Labels.label NativeRustcVmArm.Vm.SumcheckOfGkrStep.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.SumcheckOfGkrStep.b10Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.SumcheckOfGkrStep.b10Offset) NativeRustcVmArm.Vm.SumcheckOfGkrStep.label_7_at
  have hts0 := g.ok.2.2.1
  have hb0 : (Env.ofMachine m0 [(base m0 192, 200)]).base 0 = base m0 192 := rfl
  have hload : (Env.ofMachine m0 [(base m0 192, 200)]).load 0 192 8 = n.toUInt64.toBitVec :=
    load_word (by rw [hb0, hsp192]; exact hwn)
  have hpro : ∀ {S : SState} {st : MachineState},
      Match (Env.ofMachine m0 [(base m0 192, 200)]) S st.data →
      S.mem = (after b0 entryS).mem → S.sp = .ptr 0 0 →
      (∀ r ∈ keepG, S.reg r = some (.reg r)) →
      FrG m0 n st.data ∧ TStateAt st.data.dmem (tG m0) a s := by
    intro S st hmS hmem hsp hkeep
    have hW : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 192 := by
      rw [hmem, after_eq run_b0]; decide +kernel
    refine ⟨Bus.Fr.ofPrologue' (F := 192) (A := 8) (rs := []) hN (by decide) hmS hwf hsp
      (by rw [show slotsOk S slotsG = slotsOk (after b0 entryS) slotsG from by
            simp only [slotsOk, hmem]]
          rw [after_eq run_b0]; decide +kernel) (by decide) hW hkeep, ?_⟩
    refine g.t_keep (hmS.sameOutside hwf) (hmS.kept hwf) (fun q hq ↦ .inl ?_) hts0
    obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hq
    obtain ⟨hr, hle⟩ := hW w hw
    rw [hr] at hb
    cases hb
    refine g.ctx.inRange_frame ?_
    rw [show frAt m0 192 = base m0 192 from rfl,
      Sym.inRange_iff (base_noWrap (m0 := m0) (F := 192) (le_trans (by decide) hN))]
    show (base m0 192).toNat ≤ q.toNat ∧ q.toNat < (base m0 192).toNat + 192
    omega
  refine exec_then hk0 run_b0 hwf hm fun st hm' hpc ↦ ?_
  have hm0 : Match (Env.ofMachine m0 [(base m0 192, 200)]) (after b0 entryS) st.data := by
    rw [after_eq run_b0]; exact hm'
  obtain ⟨hfr, hts⟩ := hpro hm0 rfl (by rw [after_eq run_b0])
    (by rw [after_eq run_b0]; decide +kernel)
  have hc : (SBool.cmp CmpOp.eq RegWidth.W64 (.load 0 192 8) (.lit 0)).eval
      (Env.ofMachine m0 [(base m0 192, 200)]) = (n.toUInt64.toBitVec == 0#64) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]; rw [hload]
  simp only [PcOk] at hpc
  rw [hc] at hpc
  have hx2 : st.data.regs.X2 = m0.regs.X2 := UInt64.toBitVec_inj.mp ((hm'.regs .X2 _ rfl).trans rfl)
  have hx3 : st.data.regs.X3 = m0.regs.X3 := UInt64.toBitVec_inj.mp ((hm'.regs .X3 _ rfl).trans rfl)
  have hnn : n.toUInt64.toNat = n := by simp [Nat.toUInt64]; omega
  by_cases h0 : n = 0
  · have h0' : (n.toUInt64.toBitVec == 0#64) = true := by subst h0; rfl
    simp only [h0', ↓reduceIte] at hpc
    refine Eventually.done _ (Or.inl ⟨hpc.trans hl7, hfr,
      UInt64.toBitVec_inj.mp ((hm'.regs .X19 _ rfl).trans rfl), ?_⟩)
    rw [hx2, hx3, h0]
    exact rounds_zero hts
  · have h0' : (n.toUInt64.toBitVec == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h
      have := congrArg BitVec.toNat h
      simp only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat] at this
      exact h0 (by rw [← hnn]; exact this)
    simp only [h0', Bool.false_eq_true, ↓reduceIte] at hpc
    refine exec_at hk1 run_b1 hwf hpc hm0 fun st1 hm1 hpc1 ↦ ?_
    have hm1' : Match (Env.ofMachine m0 [(base m0 192, 200)]) (after b1 (after b0 entryS))
        st1.data := by
      rw [after_eq run_b1]; exact hm1
    obtain ⟨hfr1, hts1⟩ := hpro hm1' (by rw [after_eq run_b1, after_eq run_b0])
      (by rw [after_eq run_b1]) (by rw [after_eq run_b1]; decide +kernel)
    have hx2' : st1.data.regs.X2 = m0.regs.X2 :=
      UInt64.toBitVec_inj.mp ((hm1.regs .X2 _ rfl).trans rfl)
    have hx3' : st1.data.regs.X3 = m0.regs.X3 :=
      UInt64.toBitVec_inj.mp ((hm1.regs .X3 _ rfl).trans rfl)
    refine Eventually.done _ (Or.inr ⟨hpc1, hfr1, Nat.pos_of_ne_zero h0, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩)
    · exact UInt64.toBitVec_inj.mp ((hm1.regs .X19 _ rfl).trans rfl)
    · rw [hm1.regs .X20 _ rfl]; simp [Sym.eval]; rfl
    · exact UInt64.toBitVec_inj.mp ((hm1.regs .X21 _ rfl).trans rfl)
    · exact UInt64.toBitVec_inj.mp ((hm1.regs .X22 _ rfl).trans rfl)
    · exact UInt64.toBitVec_inj.mp ((hm1.regs .X23 _ rfl).trans rfl)
    · rw [UInt64.toNat, hm1.regs .X24 _ rfl]; rfl
    · rw [hm1.regs .X25 _ rfl]
      simp only [Sym.eval, BinOp.apply, UnOp.apply, Sym.low_W64, Sym.ext_W64]
      rw [hload]
      show m0.regs.X7.toBitVec + n.toUInt64.toBitVec <<< 4 = _
      rw [shl4, UInt64.toNat_toBitVec, hnn]
    · rw [hm1.regs .X26 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
      rfl
    · rw [hx2', hx3']
      exact rounds_zero hts1

end

end NativeRustcVmArm.Sumcheck.Gkr
