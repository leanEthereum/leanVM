module

public import NativeRustcVmArm.Code.Vm.WhirLevels.Names
public import NativeRustcVmArm.Whir.VerifyStackedOpening.Copy
public import NativeRustcVmArm.Whir.VerifyStackedOpening.Exec2

/-!
# `verify_stacked_opening`: `b34`

`b34a` reads the `WhirW`'s address from the stack argument (the word at the entry's SP, which no
step wrote); `b34b` writes WHIR's fresh state (the batched target, no `α`, no glued claim) and sets
`whir_levels`' arguments: at its call (`AtCall`).
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening
open LeanVM.Parameters

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData} {ls : List Whir.Level}

omit [Host] in
/-- The stack argument's word is unchanged in a state of the frame. -/
theorem Parts.arg_same [Labels]
    (h : Parts a s layout target coefficients point slices cs z value m0)
    {st : MachineData} (hf : VFr m0 st) :
    NativeRustcVm.wordOf st.dmem (m0.regs.SP.toBitVec + BitVec.ofNat 64 0) =
      NativeRustcVm.wordOf m0.dmem (m0.regs.SP.toBitVec + BitVec.ofNat 64 0) := by
  refine NativeRustcVm.wordOf_congr fun i hi ↦ hf.same _ fun hq ↦ ?_
  have hnw := h.arg.2
  unfold NoWrap at hnw
  rw [NativeRustcVm.addr_add_add, Nat.zero_add] at hq
  have hin : InRange m0.regs.SP.toBitVec 8 (m0.regs.SP.toBitVec + BitVec.ofNat 64 i) :=
    NativeRustcVm.inRange_add hi (by decide)
  have hN := h.hN
  have hsp : m0.regs.SP.toBitVec.toNat = m0.regs.SP.toNat := rfl
  rcases hq with hq | hq | hq | hq
  · have hnN := base_noWrap (m0 := m0) (F := verifyStackedOpeningStack) hN
    rw [Sym.inRange_iff hnN, base_toNat hN, NativeRustcVm.toNat_add_ofNat (by omega)] at hq
    omega
  · exact hq.2 hin
  · exact NativeRustcVm.Apart.not_inRange h.args h.arg.2 h.so.1.2.1 hin hq
  · exact NativeRustcVm.Apart.not_inRange h.argt h.arg.2 h.ts.footprint.1.2 hin hq

/-- **From `b34`** to the call of `whir_levels`. -/
theorem b34_step (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0) {R : MachineState → Prop}
    (cont : ∀ st : MachineState, AtCall a s layout target cs value ls m0 st.data →
      st.pc = Labels.label NativeRustcVmArm.Vm.WhirLevels.entryLabel ∧ retOf st.data = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b35Offset) →
      Eventually (step1 Host.exe) R st)
    {st : MachineData} (hb : AtB34 a s layout target cs value ls m0 st) :
    Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b34Offset)⟩ := by
  have hc := hb.com
  have hS := h.hS
  have hN := h.hN
  have h34 : (b34a ++ b34b).IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b34Offset) := by
    rw [← b34_split]; exact b34_in_code.trans hp.1 (List.cons_ne_nil _ _)
  obtain ⟨hka, hkb⟩ := List.IsInfixAt.append h34
  have hwB : whirBytes = 63200 := rfl
  -- `b34a`
  let envA := Env.ofMachine st [(base m0 512, 512), (m0.regs.SP.toBitVec, 8)]
  have hwfA : envA.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hc.fr.kept _ (Ring.frame_mapped h.wt.1 (by rw [stack_eq]; decide) i hi),
        base_noWrap (by omega)⟩, ⟨fun i hi ↦ hc.fr.kept _ (h.arg.1 i hi), h.arg.2⟩, trivial⟩
      (List.pairwise_pair.mpr (by
        show Apart (base m0 512) 512 m0.regs.SP.toBitVec 8
        have hsp : m0.regs.SP.toBitVec.toNat = m0.regs.SP.toNat := rfl
        unfold Apart; left; rw [h.base_toNat', hsp]; omega))
  have hmA : Match envA argS st :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned h.wt.1 (by rw [stack_eq]; decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hc.fr.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        show base m0 512 + BitVec.ofInt 64 512 = m0.regs.SP.toBitVec + BitVec.ofInt 64 0
        rw [show BitVec.ofInt 64 512 = BitVec.ofNat 64 512 from rfl, Ring.base_add_eq]
        simp, trivial⟩
  refine exec_then hka run_b34a hwfA hmA fun stA hmA' hpcA ↦ ?_
  have hfA : VFr m0 stA.data := Fr.ofBlock hc.fr hmA hmA' hwfA rfl rfl rfl (by simp)
  have hdA : stA.data.dmem = st.dmem := hmA'.dmem_eq hwfA rfl
  have kA : ∀ r, r ≠ .X6 → stA.data.regs.getXReg r = st.regs.getXReg r :=
    fun r h6 ↦ (rv hmA' (v := .reg r) (by cases r <;> first | rfl | exact absurd rfl h6)).trans rfl
  have e6 : (stA.data.regs.getXReg .X6).toBitVec = pA m0 := by
    refine (hmA'.regs .X6 _ rfl).trans ?_
    show envA.load 1 0 8 = _
    rw [Ring.load_eq_wordOf]
    show (NativeRustcVm.wordOf st.dmem (m0.regs.SP.toBitVec + BitVec.ofNat 64 0)).toBitVec = _
    rw [h.arg_same hc.fr]
    rfl
  simp only [PcOk] at hpcA
  -- `b34b`
  have hfrP : Apart (base m0 512) 512 (pA m0) whirBytes := h.frame_apart h.po.1.2.2.2.2.1
  have hpnw : NoWrap (pA m0) whirBytes := h.po.1.2.1
  let envB := Env.ofMachine stA.data [(base m0 512, 512), (pA m0, 512)]
  have hwfB : envB.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hfA.kept _ (Ring.frame_mapped h.wt.1 (by rw [stack_eq]; decide) i hi),
        base_noWrap (by omega)⟩,
      ⟨fun i hi ↦ hfA.kept _ (h.po.1.1 i (by rw [hwB]; omega)),
        NativeRustcVm.NoWrap.mono hpnw (by rw [hwB]; omega)⟩, trivial⟩
      (List.pairwise_pair.mpr (by
        have := hfrP
        show Apart (base m0 512) 512 (pA m0) 512
        rw [hwB] at this
        unfold Apart at this ⊢
        omega))
  have hb0 : envB.base 0 = base m0 512 := rfl
  have hb1 : envB.regions[1]? = some (pA m0, 512) := rfl
  have hmB : Match envB whir2S stA.data :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned h.wt.1 (by rw [stack_eq]; decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hfA.sp]; simp [Sym.eval])
      ⟨by show (stA.data.regs.getXReg .X6).toBitVec = _; rw [e6]; simp [Sym.eval], trivial⟩
      trivial trivial trivial
  refine exec_at hkb run_b34b hwfB hpcA hmB fun stB hmB' hpcB ↦ ?_
  have hfB : OFr m0 (outsF m0) stB.data :=
    Fr.ofBlockW (Fr.mono_outs hfA fun _ hq ↦ outs_outsF hq) hmB hmB' hwfB rfl rfl
      (fun _ h ↦ absurd h (by simp)) rfl (by rw [stack_eq]; decide) h.hN slots_le
      (writeOk_of hmB' (wr := [1]) (by decide) fun r hr b sz hbr i hi ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        rw [hb1, Option.some.injEq, Prod.mk.injEq] at hbr
        obtain ⟨rfl, rfl⟩ := hbr
        exact .inl (NativeRustcVm.inRange_add (by rw [hwB]; omega) (by
          have := hpnw; unfold NoWrap at this; omega)))
  have hsB : SameOutside stA.data.dmem stB.data.dmem (InRange (pA m0) whirBytes) :=
    NativeRustcVm.SameOutside.mono (hmB'.sameOutside hwfB) fun q hq ↦ by
      have := written_r hwfB hb1 (by decide) hq
      unfold InRange at this ⊢
      rw [hwB]
      omega
  have kB : ∀ r ∈ [XReg.X5, .X26, .X27, .X28, .X29],
      stB.data.regs.getXReg r = stA.data.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact (rv hmB' rfl).trans rfl
  have hfw : FW stA.data.dmem m0 [(16, m0.regs.X0), (24, m0.regs.X4), (32, m0.regs.X5),
      (40, m0.regs.X6), (48, m0.regs.X2)] := by rw [hdA]; exact hc.fw
  have hlvA : LevelsAt stA.data.dmem (loc m0 112) ls := by rw [hdA]; exact hb.lv
  have hlen := hb.len
  have ex5 : stA.data.regs.X5 = ls.length.toUInt64 := (kA .X5 (by decide)).trans hb.x5
  -- the registers
  have e0 : stB.data.regs.X0 = m0.regs.X0 :=
    (rv hmB' (r := .X0) rfl).trans (by
      show UInt64.ofBitVec (envB.load 0 16 8) = _
      rw [fw_load (o := 16) (v := m0.regs.X0) hb0 hfw (by simp)])
  have e1 : stB.data.regs.X1 = layout.stackLog.toUInt64 :=
    (rv hmB' (r := .X1) rfl).trans (by
      show stA.data.regs.getXReg .X21 = _
      rw [kA .X21 (by decide)]; exact hb.x21)
  have e2 : stB.data.regs.X2.toNat = (ls.head?.map (·.fold)).getD 0 := by
    have hx2 := hmB'.regs .X2 _ rfl
    sym_simp at hx2
    have hx5 : envB.regs .X5 = ls.length.toUInt64.toBitVec := by
      show (stA.data.regs.getXReg .X5).toBitVec = _; rw [show stA.data.regs.getXReg .X5 =
        stA.data.regs.X5 from rfl, ex5]
    rw [hx5] at hx2
    cases ls with
    | nil =>
      rw [show ((([] : List Whir.Level).length.toUInt64.toBitVec == 0#64) = true) from rfl] at hx2
      simp only [↓reduceIte] at hx2
      show (stB.data.regs.getXReg .X2).toBitVec.toNat = 0
      rw [hx2]; rfl
    | cons l ls' =>
      have hne : ((l :: ls').length.toUInt64.toBitVec == 0#64) = false := by
        apply beq_eq_false_iff_ne.mpr
        intro he
        have := congrArg BitVec.toNat he
        rw [UInt64.toNat_toBitVec, natCast_toUInt64_toNat (by simp at hlen ⊢; omega)] at this
        simp at this
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hx2
      obtain ⟨hl0, -, -, hw⟩ := hlvA 0 (by simp)
      have hw0 := (NativeRustcVm.wordsAt_cons_iff.mp hw).1
      rw [NativeRustcVm.Transcript.off, Nat.mul_zero, NativeRustcVm.addr_add_zero] at hw0
      have hl112 : envB.load 0 112 8 = l.fold.toUInt64.toBitVec := Ring.load_word hw0
      show (stB.data.regs.getXReg .X2).toBitVec.toNat = l.fold
      rw [hx2, hl112, UInt64.toNat_toBitVec]
      exact natCast_toUInt64_toNat hl0
  have e3 : stB.data.regs.X3.toBitVec = loc m0 56 :=
    (hmB'.regs .X3 _ rfl).trans (by show base m0 512 + BitVec.ofInt 64 56 = _; rfl)
  have e4 : stB.data.regs.X4.toBitVec = loc m0 112 :=
    (hmB'.regs .X4 _ rfl).trans (by show base m0 512 + BitVec.ofInt 64 112 = _; rfl)
  have e6' : stB.data.regs.X6.toBitVec = pA m0 :=
    (hmB'.regs .X6 _ rfl).trans (by show pA m0 + BitVec.ofInt 64 0 = _; simp)
  -- the memory
  have hts : TStateAt stB.data.dmem (tA m0) a (sq s).2 :=
    (show TStateAt stA.data.dmem (tA m0) a (sq s).2 by rw [hdA]; exact hc.ts).frame
      (hmB'.kept hwfB) (fun q hq ↦ ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange h.po.1.2.2.1 hpnw
        h.ts.footprint.1.2 hq ht, fun hd ↦ NativeRustcVm.Apart.not_inRange h.po.1.2.2.2.1 hpnw
        h.ts.footprint.2.1.2 hq hd⟩) hsB
  have hscs : NativeRustcVm.EWsAt stB.data.dmem (scA m0 + BitVec.ofNat 64 8)
      (scalesOf s layout cs).toList := by
    refine NativeRustcVm.BytesAt.of_sameOutside (show NativeRustcVm.EWsAt stA.data.dmem _ _ by
      rw [hdA]; exact hc.scs) hsB fun i hi hq ↦ ?_
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, size_scalesOf] at hi
    have := h.sc8_nw
    exact NativeRustcVm.Apart.not_inRange (h.sc8_apart (NativeRustcVm.Apart.symm h.psc)) h.sc8_nw
      hpnw (NativeRustcVm.inRange_add hi (by unfold NoWrap at this; omega)) hq
  have hfwb : FW stB.data.dmem m0 (basisWords layout cs m0) :=
    fw_block' hmB' hwfB rfl [56, 64, 72, 80, 88, 96, 104] rfl (by decide)
      (by show FW stA.data.dmem m0 _; rw [hdA]; exact hb.fwb)
  have hlv : LevelsAt stB.data.dmem (loc m0 112) ls :=
    levelsAt_keep hlvA hlen hsB fun j hj hq ↦ by
      rw [NativeRustcVm.addr_add_add] at hq
      exact NativeRustcVm.Apart.not_inRange hfrP (base_noWrap (by omega)) hpnw
        (NativeRustcVm.inRange_add (by omega) (by omega)) hq
  have hcl := hb.claim
  rw [← kA .X28 (by decide), ← kA .X29 (by decide), ← kA .X27 (by decide),
    ← kA .X26 (by decide)] at hcl
  have w0 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hmB' hb1 (o := 0) (by decide)
    (v := .bin .eor .W64 (.reg .X28) (.reg .X27)) (by decide)
  have w8 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hmB' hb1 (o := 8) (by decide)
    (v := .bin .eor .W64 (.reg .X29) (.reg .X26)) (by decide)
  have w16 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hmB' hb1 (o := 16) (by decide)
    (v := .lit 0) (by decide)
  have w504 := NativeRustcVmArm.Sumcheck.Match.wordAt_write hmB' hb1 (o := 504) (by decide)
    (v := .lit 0) (by decide)
  have hws : WhirStateAt stB.data.dmem (pA m0) ⟨claimOf s layout target cs value, #[], #[]⟩ := by
    refine ⟨?_, ⟨by simp, w16, fun i hi ↦ absurd hi (by simp)⟩, by simp, w504,
      fun i hi ↦ absurd hi (by simp)⟩
    rw [← hcl]
    refine NativeRustcVm.ewAt_iff.mpr ⟨?_, ?_⟩
    · rw [NativeRustcVm.addr_add_zero] at w0
      sym_simp at w0
      exact w0
    · sym_simp at w8
      exact w8
  simp only [PcOk] at hpcB
  rw [show k + NativeRustcVmArm.Vm.VerifyStackedOpening.b34Offset + b34a.length + b34b.length = k + NativeRustcVmArm.Vm.VerifyStackedOpening.b35Offset from by
    have hsplit : b34a.length + b34b.length = b34.length := by
      rw [← List.length_append]
      rfl
    rw [Nat.add_assoc (k + b34Offset), hsplit, Nat.add_assoc, b34_next]] at hpcB
  exact cont stB ⟨hfB, hts, hscs, hfwb, hb.lad, hlen, hlv, hws, e0, e1, e2, e3, e4,
    (kB .X5 (by simp)).trans ex5, e6'⟩ hpcB

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
