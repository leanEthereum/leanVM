import Rv64Verifier.Proofs.Walk.R17E
import Rv64Verifier.Proofs.Walk.ErrTail

/-!
# `walk` R17, `table_sumcheck`'s call

`tsCall`: from `AtTS`, the call returns to `0x800037ac` having written its result at `S - 928`,
`target` at `S - 1704`, the sponge, the stack and the heap it allocates. `tsBranch`: an `Err`
writes the result and leaves by `errTail₁`; an `Ok` is `AtR18`, the table phase done.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `table_sumcheck`'s writes in `walk`'s frame: the result and `target`. -/
@[rv_addr] def WTS (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 928) 24 ∨ Within a (s.getReg .x2 - 1704) 24

theorem WTS_ok {s u₀ v : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v) {a : Word}
    (ha : WTS s a) : InF s a ∧ ¬ KeepR s u₀ a := by
  rcases ha with ha | ha
  · exact range_ok hpre h (c := 928) (k := 928) (n := 24) rfl (by omega) (by omega) ha
  · exact range_ok hpre h (c := 1704) (k := 1704) (n := 24) rfl (by omega) (by omega) ha

/-- Some transcript stands for any memory. -/
theorem transcriptAt_exists (u : MachineState) (p : Word) : ∃ T, TranscriptAt u p T :=
  ⟨{ proof := { stream := eListAt u (streamPtr u p) (streamLen u p), openings := [] }
     sponge := spongeAt u (p + 8), streamOffset := (u.getMem (p + 344)).toNat
     openingOffset := (u.getMem (p + 352)).toNat, roots := [] }, rfl, rfl, rfl, rfl⟩

/-- `table_sumcheck` returns, or the run dies. -/
theorem tsCall (hTS : TableSumcheckSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ w : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} {PP : Word} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) (hpc : w.pc = 0x80008010) (A : AtTS s u₀ w bus PP) :
    ∃ t, Reaches Image.code w t ∧ ((t.pc = 0x800037ac ∧ Preserves w t ∧
      TableSumcheckPost w t ∧ StepW s w t (WTS s) True) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨t, hr, ⟨hpc', hp, post⟩ | hd⟩ := hTS.call (Reaches.refl w) hpc (tsPre hpre h A)
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have hsl := stackLo_callee A.rest.inv tableSumcheckStack
  have hm : tableSumcheckStack ≤ 8736 := by decide
  refine ⟨t, hr, Or.inl ⟨by rw [hpc', returnAddress, A.x1]; decide, hp, post,
    fun a ha ↦ post.frame a fun i hi hw ↦ ha i hi ?_, post.heap, post.mono, hp .x2 (by decide)⟩⟩
  rw [A.x10, A.target, A.self, hsl] at hw
  rcases hw with hw | hw | hw | hw | hw | hw
  · exact Or.inl (Or.inl hw)
  · exact Or.inl (Or.inr hw)
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨trivial, by rw [tp] at hw ⊢; addr_omega [hw, hb1]⟩)))
  · exact Or.inr (Or.inl (by addr_omega [hw, hb1, hm]))
  · exact Or.inr (Or.inr (Or.inl hw))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hw)))

/-- At `0x800037ac`, `table_sumcheck` having returned `Ok(evs)` at `S - 928`: what `walk` kept of
`u₀`, the evaluations, and the run from the transcript on is `afterTables`. -/
structure AtR18 (OI : MachineState → Word → List (List Opening) → Prop) (s u₀ w u : MachineState)
    (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64)) (lir : BitVec 64)
    (bus : BusResultRust) (evs : List (List E × List E)) : Prop where
  pc : u.pc = 0x800037ac
  rest : Rest s u₀ u
  old : ∀ x : Word, x.toNat + 8 ≤ heapNext u₀ → u.getMem x = u₀.getMem x
  mono : heapNext u₀ ≤ heapNext w
  ok : u.getMem (s.getReg .x2 - 928) ≠ 0xffffffffffffffff
  rowsAt : RowsAt w u (s.getReg .x2 - 928) evs
  x8 : u.getReg .x8 = 6
  regs : ∀ r ∈ ([.x19, .x21, .x25] : List Reg), u.getReg r = u₀.getReg r
  m184 : u.getMem (s.getReg .x2 - 2472) = u₀.getMem (s.getReg .x2 - 920)
  tracks : TracksR OI s u
    (PcsContracts.digestAt u₀ (s.getReg .x2 - 1800), stackShape layout.stackLog lir.toNat)
    (afterTables (bytesAt s (s.getReg .x12) 32) layout rows lir bus evs)

/-- What `table_sumcheck` reads, as the mirror's values. -/
theorem tsArgs_eq {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ w : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} {PP : Word} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) (A : AtTS s u₀ w bus PP) :
    tablesAt w (w.getReg .x11) (w.getReg .x12).toNat = tables ∧
    natsAt w (w.getReg .x13) (w.getReg .x14).toNat = layout.tableLogHeights ∧
    formRowsAt w (w.getReg .x15) (w.getReg .x16).toNat = bus.forms ∧
    eListAt w (w.getReg .x17) (w.getReg .x28).toNat =
      (powers (eAt w (s.getReg .x2 - 152)) 5).take 2 ∧
    eListAt w (w.getReg .x29) (w.getReg .x30).toNat =
      (powers (eAt w (s.getReg .x2 - 152)) 5).drop 2 ∧
    eListAt w (w.getReg .x31) (tsEqLen w).toNat = bus.point ∧
    eAt w (tsTarget w) = dotRust ((powers (eAt w (s.getReg .x2 - 152)) 5).drop 2) bus.totals := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have LI := h.layoutIn
  have hh := h.inv.heap.hi
  have hN : heapNext u₀ ≤ 2 ^ 63 := by simp only [heapNext, heapEnd] at hh ⊢; omega
  have eS (c d : Nat) (hc : d + c ≤ 2656) (hd : c ≤ d) :
      s.getReg .x2 - BitVec.ofNat 64 d + BitVec.ofNat 64 c = s.getReg .x2 - BitVec.ofNat 64 (d - c) := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc, hd]
  have hdrop : (powers (eAt w (s.getReg .x2 - 152)) 5).drop 2 = eListAt w (PP + 48) 3 := by
    rw [← A.powers, MultilinearWords.eListAt_drop]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [A.x11, A.x12]
    refine tablesAt_eq fun i hi ↦ ?_
    have ht := LI.tables
    simp only [Old] at ht
    rw [A.old _ (by addr_omega [ht.2.1, hi]), LI.opcodes i hi]
  · rw [A.x13, A.x14, ← LI.heightsVal]
    have ht := LI.heights
    simp only [Old] at ht
    simp only [natsAt]
    congr 1
    exact readWords_congr fun i hi ↦ A.old _ (by addr_omega [ht.2.1, hi])
  · have hf := h.busAt.forms.2
    have e856 : s.getReg .x2 - 928 + 72 = s.getReg .x2 - 856 := eS 72 928 (by omega) (by omega)
    have e848 : u₀.getMem (s.getReg .x2 - 848) = vecPtr u₀ (s.getReg .x2 - 856) := by
      rw [vecPtr]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    have e840 : u₀.getMem (s.getReg .x2 - 840) = vecLen u₀ (s.getReg .x2 - 856) := by
      rw [vecLen]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    rw [e856] at hf
    rw [A.x15, A.x16, e848, e840, ← hf]
    have fb := h.formsBuf
    have FO := h.forms
    simp only [Old] at fb
    refine formRowsAt_congr A.old hN fb.2.1 (fun i hi ↦ (FO.forms i hi).2.1)
      (fun i hi j hj ↦ (FO.terms i hi j hj).2.1)
  · rw [A.x17, A.x28, ← A.powers, Bus.eListAt_take _ _ (by decide)]; rfl
  · rw [A.x29, A.x30, hdrop]; rfl
  · have hp := h.busAt.point.elems
    have e880 : s.getReg .x2 - 928 + 48 = s.getReg .x2 - 880 := eS 48 928 (by omega) (by omega)
    have e872 : u₀.getMem (s.getReg .x2 - 872) = vecPtr u₀ (s.getReg .x2 - 880) := by
      rw [vecPtr]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    have e864 : u₀.getMem (s.getReg .x2 - 864) = vecLen u₀ (s.getReg .x2 - 880) := by
      rw [vecLen]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    rw [e880, vecEs] at hp
    rw [A.x31, A.eqLen, e872, e864, ← hp]
    have po := h.pointOld
    simp only [Old] at po
    refine Bus.eListAt_congr fun i hi ↦ eAt_congr (A.old _ (by addr_omega [po.2.1, hi]))
      (A.old _ (by addr_omega [po.2.1, hi])) (A.old _ (by addr_omega [po.2.1, hi]))
  · rw [A.target, A.tgt, hdrop]

set_option maxRecDepth 8192 in
/-- From `table_sumcheck`'s entry: `AtR18`, or the `Err` return, or a dead end. -/
theorem tsBranch (hTS : TableSumcheckSpec) (hDN : DropNopSpec) (hDL : DropLayoutSpec)
    {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ w : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} {PP : Word} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) (hpc : w.pc = 0x80008010) (A : AtTS s u₀ w bus PP) :
    ∃ u, Reaches Image.code w u ∧ ((∃ evs, AtR18 OI s u₀ w u layout rows lir bus evs) ∨
      Done OI s u ∨ Dead Image.code u) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨t, hr, ⟨hpc', hp, post, st⟩ | hd⟩ := tsCall hTS hpre h hpc A
  swap
  · exact ⟨t, hr, Or.inr (Or.inr hd)⟩
  have R := A.rest.stepW hpre (fun a ha ↦ WTS_ok hpre A.rest ha) st
  have sp := R.inv.sp
  have e928 : t.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x21 : t.getReg .x21 = s.getReg .x10 := by
    rw [hp .x21 (by decide), A.regs .x21 (by decide), h.x21]
  by_cases he : t.getMem (s.getReg .x2 - 928) = 0xffffffffffffffff
  · -- `Err`: the result's first words, then `errTail₁`
    obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800037ac_spec hpc' (by
      rv_eval [sp]; and_intros <;> valid_access hval [hb1])
    have m₁ := b800037ac_mem_same h₁
    have k₁ := b800037ac_keeps h₁
    have R₁ := R.same m₁ (k₁ .x2 (by decide))
    have hR := hpre.out
    have x21' : u₁.getReg .x21 = s.getReg .x10 := by rw [k₁ .x21 (by decide), x21]
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003fd4_spec
      (b800037ac_pc_taken h₁ (by rw [e928]; exact he)) (by
        rv_eval [x21']
        and_intros <;> exact Region.valid hR (by addr_omega [hR]) (by addr_omega [hR])
          (by addr_omega [hR]))
    have fr₀ := b80003fd4_frame h₂ (by rw [x21']; addr_omega [hR])
    rw [x21'] at fr₀
    have R₂ := R₁.result hpre (n := 24) (by omega) (DFrame.of_memFrame fr₀)
      (b80003fd4_keeps h₂ .x2 (by decide))
    obtain ⟨t', hr₃, hd⟩ := errTail₁ hDN hDL hpre h R₂ (b80003fd4_pc h₂) (by
      rw [← x21', b80003fd4_m_x21_0 h₂, b800037ac_x9 h₁]; rfl)
    exact ⟨t', hr.trans (hr₁.trans (hr₂.trans hr₃)), Or.inr hd⟩
  · -- `Ok`
    obtain ⟨eTab, eHt, eForms, ePow, eDrop, ePt, eTgt⟩ := tsArgs_eq hpre h A
    have htab := (LayoutMirror.buildLayoutRust_rest h.build.2.choose_spec.choose_spec []).2.1
    have hok : vecCap t (w.getReg .x10) ≠ errNiche := by rw [A.x10]; exact he
    -- the rows `table_sumcheck` returned, for every transcript
    have run : ∀ T, TranscriptAt u₀ (tp s) T → ∃ T', (tablePhaseRust layout bus).run T =
        some (evalRowsOf t (s.getReg .x2 - 928), T') ∧ TranscriptAt t (tp s) T' ∧
        RowsAt w t (s.getReg .x2 - 928) (evalRowsOf t (s.getReg .x2 - 928)) := by
      intro T hT
      obtain ⟨T₁, e₁, hT₁⟩ := A.sample T hT
      have hv := post.value T₁ (by rw [A.self]; exact hT₁)
      rw [eTab, eHt, eForms, ePow, eDrop, ePt, eTgt] at hv
      rw [tablePhase_run layout bus htab, e₁, Option.bind_some]
      generalize (tableSumcheckM tables layout.tableLogHeights bus.forms _ _ bus.point _).run T₁ = o
        at hv ⊢
      rcases o with _ | ⟨r, T₂⟩
      · exact absurd hv hok
      · obtain ⟨-, hrows, hT₂⟩ := hv
        rw [A.x10] at hrows
        rw [A.self] at hT₂
        have er := Walk.RowsAt.eq hrows
        subst er
        exact ⟨T₂, rfl, hT₂, hrows⟩
    have ptr : u₀.getMem (tp s) = s.getReg .x13 := h.proofPtr
    obtain ⟨T₀, hT₀⟩ := transcriptAt_exists u₀ (tp s)
    obtain ⟨-, -, -, hrows⟩ := run T₀ hT₀
    have htr := h.tracks
    rw [tail_tables] at htr
    have m₀ := R.mono
    refine ⟨t, hr, Or.inl ⟨_, {
      pc := hpc'
      rest := R
      old := fun x hx ↦ by
        rw [st.getH hpre (fun a ha ↦ (WTS_ok hpre A.rest ha).1) (by have := A.rest.mono; omega)]
        exact A.old x hx
      mono := A.rest.mono
      ok := he
      rowsAt := hrows
      x8 := by rw [hp .x8 (by decide), A.x8]
      regs := fun r hr ↦ by
        have hr' := A.regs r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> rw [hp _ (by decide), hr']
      m184 := by
        rw [show (2472 : Word) = BitVec.ofNat 64 2472 from rfl, st.getF hpre (by addr_omega [hb1])
          (fun i hi hw ↦ by simp only [WTS] at hw; rcases hw with hw | hw <;> addr_omega [hw, hi, hb1])
          fun _ ↦ by rw [tp]; addr_omega [hb1]]
        exact A.m184
      tracks := TracksR.bind htr (keeps_tablePhaseRust layout bus) fun T hT ↦ by
        obtain ⟨T', e, hT', -⟩ := run T hT
        exact ⟨T', e, hT'⟩ }⟩⟩

/-- R17 whole: from `AtR17`, `AtR18`, or the `Err` return, or a dead end. -/
theorem r17 (hD : DuplexSpec) (hP : MultilinearContracts.PowersSpec)
    (hDt : MultilinearContracts.DotSpec) (hTS : TableSumcheckSpec)
    (hDN : DropNopSpec) (hDL : DropLayoutSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) :
    ∃ u, Reaches Image.code u₀ u ∧ ((∃ w evs, AtR18 OI s u₀ w u layout rows lir bus evs) ∨
      Done OI s u ∨ Dead Image.code u) := by
  obtain ⟨u, hr, ⟨hpc, P⟩ | hd⟩ := r17a hD hpre h
  swap
  · exact ⟨u, hr, Or.inr (Or.inr hd)⟩
  obtain ⟨v, hr₁, ⟨hpc₁, PP, P₁⟩ | hd⟩ := r17b hP hDt hpre h hpc P
  swap
  · exact ⟨v, hr.trans hr₁, Or.inr (Or.inr hd)⟩
  obtain ⟨w, hr₂, hpc₂, A⟩ := tsArgs hpre h hpc₁ P₁
  obtain ⟨t, hr₃, ⟨evs, h₃⟩ | hd | hd⟩ := tsBranch hTS hDN hDL hpre h hpc₂ A
  · exact ⟨t, hr.trans (hr₁.trans (hr₂.trans hr₃)), Or.inl ⟨w, evs, h₃⟩⟩
  · exact ⟨t, hr.trans (hr₁.trans (hr₂.trans hr₃)), Or.inr (Or.inl hd)⟩
  · exact ⟨t, hr.trans (hr₁.trans (hr₂.trans hr₃)), Or.inr (Or.inr hd)⟩

end Rv64Verifier.Proofs.Walk
