import Rv64Verifier.Proofs.Walk.R17Calls

/-!
# `walk` R17, `0x800035f0` to `powers`' call

The bus result's pointers spilled, `xi = sample()` (`duplex`, the first three lanes into
`S - 152`), the opcodes' bounds checks and `n_constraints` summed from `.rodata`'s
`N_CONSTRAINTS`, to `powers(xi, n_constraints + 3)`'s entry.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The frame doublewords R17 writes up to `powers`. -/
@[rv_addr] def W17a (s : MachineState) (a : Word) : Prop :=
  a = s.getReg .x2 - 344 ∨ a = s.getReg .x2 - 336 ∨ a = s.getReg .x2 - 2600 ∨
    a = s.getReg .x2 - 2592 ∨ a = s.getReg .x2 - 2472 ∨ a = s.getReg .x2 - 152 ∨
    a = s.getReg .x2 - 144 ∨ a = s.getReg .x2 - 136 ∨ a = s.getReg .x2 - 2624 ∨
    a = s.getReg .x2 - 2496

theorem W17a_ok {s u₀ v : MachineState} (hpre : WalkPre s) (h : Rest s u₀ v) {a : Word}
    (ha : W17a s a) : InF s a ∧ ¬ KeepR s u₀ a := by
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact slot_ok (k := 344) hpre h (by omega) (by omega)
  · exact slot_ok (k := 336) hpre h (by omega) (by omega)
  · exact slot_ok (k := 2600) hpre h (by omega) (by omega)
  · exact slot_ok (k := 2592) hpre h (by omega) (by omega)
  · exact slot_ok (k := 2472) hpre h (by omega) (by omega)
  · exact slot_ok (k := 152) hpre h (by omega) (by omega)
  · exact slot_ok (k := 144) hpre h (by omega) (by omega)
  · exact slot_ok (k := 136) hpre h (by omega) (by omega)
  · exact slot_ok (k := 2624) hpre h (by omega) (by omega)
  · exact slot_ok (k := 2496) hpre h (by omega) (by omega)

/-- At `powers`' entry. -/
structure PrePowers (s u₀ u : MachineState) : Prop where
  rest : Rest s u₀ u
  st : StepW s u₀ u (W17a s) True
  x1 : u.getReg .x1 = 0x8000371c
  x10 : u.getReg .x10 = s.getReg .x2 - 1872
  x11 : u.getReg .x11 = s.getReg .x2 - 152
  x12 : u.getReg .x12 = 5
  x24 : u.getReg .x24 = 2
  x22 : u.getReg .x22 = u₀.getMem (s.getReg .x2 - 864)
  x23 : u.getReg .x23 = u₀.getMem (s.getReg .x2 - 824)
  x8 : u.getReg .x8 = u₀.getMem (s.getReg .x2 - 816)
  x20 : u.getReg .x20 = u₀.getMem (s.getReg .x2 - 872)
  regs : ∀ r ∈ ([.x19, .x21, .x25, .x27] : List Reg), u.getReg r = u₀.getReg r
  m184 : u.getMem (s.getReg .x2 - 2472) = u₀.getMem (s.getReg .x2 - 920)
  m56 : u.getMem (s.getReg .x2 - 2600) = u₀.getMem (s.getReg .x2 - 840)
  m64 : u.getMem (s.getReg .x2 - 2592) = u₀.getMem (s.getReg .x2 - 848)
  m160 : u.getMem (s.getReg .x2 - 2496) = u₀.getMem (s.getReg .x2 - 872)
  sample : ∀ T, TranscriptAt u₀ (tp s) T → ∃ T', TM.sample.run T =
    some (eAt u (s.getReg .x2 - 152), T') ∧ TranscriptAt u (tp s) T'

theorem notW17a {s : MachineState} (hpre : WalkPre s) {k : Nat} (hk : 160 ≤ k ∧ k ≤ 2656)
    (hn : ∀ m ∈ [344, 336, 2600, 2592, 2472, 152, 144, 136, 2624, 2496], m ≤ k - 8 ∨ k < m) :
    ∀ i < 8, ¬ W17a s (s.getReg .x2 - BitVec.ofNat 64 k + BitVec.ofNat 64 i) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hn
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hn
  intro i hi hw
  simp only [W17a] at hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw <;>
    · have := congrArg BitVec.toNat hw
      addr_omega [this, hb1, hk, hi, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10]

/-- Frame doublewords at `S - k` and `S - m` are apart. -/
theorem slot_ne {s : MachineState} (hpre : WalkPre s) {k m : Nat} (hk : k ≤ 2656) (hm : m ≤ 2656)
    (h : m + 8 ≤ k ∨ k < m) {i : Nat} (hi : i < 8) :
    s.getReg .x2 - BitVec.ofNat 64 k + BitVec.ofNat 64 i ≠ s.getReg .x2 - BitVec.ofNat 64 m := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro e
  bv_omega

theorem W17a_tp {s : MachineState} (hpre : WalkPre s) {a : Word} (ha : W17a s a) :
    ¬ Within a (tp s) 368 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rw [tp]
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> addr_omega [hb1]

set_option maxRecDepth 8192 in
theorem r17a (hD : DuplexSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) :
    ∃ u, Reaches Image.code u₀ u ∧ ((u.pc = 0x80007dfc ∧ PrePowers s u₀ u) ∨ Dead Image.code u) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp := h.inv.sp
  have R₀ := Rest.of h.inv
  -- the spills, to `duplex`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800035f0_spec h.pc (by
    rv_eval [sp, h.x22]
    and_intros <;> first | valid_access hval [hb1] | addr_omega [hb1])
  have k₁ := b800035f0_keeps h₁
  have st₁ : StepW s u₀ u₁ (W17a s) False := StepW.ofFrame hpre h.inv.heap (h₁.dframe (by
      rv_eval [sp, h.x22]
      simp only [W17a, true_or, or_true, and_self]))
    (fun a ha ↦ (W17a_ok hpre R₀ ha).1) (k₁ .x2 (by decide))
  have R₁ := R₀.stepW hpre (fun a ha ↦ W17a_ok hpre R₀ ha) st₁
  have etp : tp s = s.getReg .x2 - BitVec.ofNat 64 2448 := rfl
  have ptr₁ : u₁.getMem (tp s) = s.getReg .x13 := by
    rw [etp, R₁.get (keep_slot hpre (by omega)), ← etp]
    exact h.proofPtr
  -- `duplex`
  obtain ⟨v₁, hrv₁, ⟨hpcv₁, hp₁, st₂, tr₂⟩ | hd⟩ := duplexW hD hpre R₁.inv ptr₁ hr₁
    (b800035f0_pc h₁) (by rw [b800035f0_x10 h₁, h.x23])
  swap
  · exact ⟨v₁, hrv₁, Or.inr hd⟩
  have R₂ := R₁.stepW hpre (fun a ha ↦ ha.elim) st₂
  have st₀₂ := (st₁.trans st₂).weaken (W' := W17a s) (T' := True)
    (fun a ha ↦ ha.elim id False.elim) fun _ ↦ trivial
  have sp₂ : v₁.getReg .x2 = s.getReg .x2 - 2656 := R₂.inv.sp
  have x22₂ : v₁.getReg .x22 = s.getReg .x2 - 512 := by
    rw [hp₁ .x22 (by decide), k₁ .x22 (by decide), h.x22]
  have LI := h.layoutIn
  have hTP := NewBuf.region LI.tables.newBuf hpre.heap h.inv.heap (by decide)
  have TPb := LI.tables.newBuf
  simp only [NewBuf] at TPb
  have fW : ∀ a, W17a s a → InF s a := fun a ha ↦ (W17a_ok hpre R₀ ha).1
  have eTP : v₁.getMem (s.getReg .x2 - 2456) = u₀.getMem (s.getReg .x2 - 2456) :=
    st₀₂.getF hpre (by addr_omega [hb1]) (notW17a (k := 2456) hpre (by omega) (by decide))
      fun _ ↦ by rw [tp]; addr_omega [hb1]
  generalize hTPd : u₀.getMem (s.getReg .x2 - 2456) = TP at eTP hTP TPb
  have op (i : Nat) (hi : i < 6) (c : Word) (hc : c = BitVec.ofNat 64 (80 * i + 72)) :
      v₁.getMem (TP + c) = BitVec.ofNat 64 i := by
    rw [st₀₂.getH hpre fW (by
      rw [hc]; rcases TPb.2 with h0 | h0
      · omega
      · addr_omega [h0, hi]), hc]
    have := LI.opcodes i hi
    rwa [hTPd] at this
  have e200 : v₁.getReg .x2 + 200 = s.getReg .x2 - 2456 := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have TPa : TP.toNat % 8 = 0 := TPb.1
  have TPr : TP.toNat + 480 ≤ heapNext u₀ := by rcases TPb.2 with h0 | h0 <;> omega
  -- `xi`'s lanes, the first opcode's bound
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80003634_spec
    (by rw [hpcv₁, returnAddress_eq, b800035f0_x1 h₁]; decide) (by
      rv_eval [sp₂, x22₂, eTP]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Region.valid hTP (by addr_omega [hTP]) (by addr_omega [hTP])
            (by addr_omega [hTP, TPa])
)
  have k₃ := b80003634_keeps h₃
  have W3 : ∀ a, (a = s.getReg .x2 - 152 ∨ a = s.getReg .x2 - 144 ∨ a = s.getReg .x2 - 136) →
      W17a s a := fun a ha ↦ by
    rcases ha with rfl | rfl | rfl <;> simp only [W17a, true_or, or_true]
  have st₃ : StepW s v₁ u₃ (fun a ↦ a = s.getReg .x2 - 152 ∨ a = s.getReg .x2 - 144 ∨
      a = s.getReg .x2 - 136) False := StepW.ofFrame hpre R₂.inv.heap (h₃.dframe (by
      rv_eval [sp₂, x22₂]
      simp only [true_or, or_true, and_self]))
    (fun a ha ↦ fW a (W3 a ha)) (k₃ .x2 (by decide))
  have R₃ := R₂.stepW hpre (fun a ha ↦ W17a_ok hpre R₀ (W3 a ha)) st₃
  have hpc₃ : u₃.pc = 0x8000365c := b80003634_pc_not_taken h₃ (by
    rw [e200, eTP, op 0 (by decide) 72 rfl]; decide)
  have x16₃ : u₃.getReg .x16 = TP := by rw [b80003634_x16 h₃, e200, eTP]
  have op₃ (i : Nat) (hi : i < 6) (c : Word) (hc : c = BitVec.ofNat 64 (80 * i + 72)) :
      u₃.getMem (TP + c) = BitVec.ofNat 64 i := by
    rw [st₃.getH hpre (fun a ha ↦ fW a (W3 a ha)) (by rw [hc]; addr_omega [TPr, hi, R₂.mono]), op i hi c hc]
  -- the other opcodes' bounds
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000365c_spec hpc₃ (by
    rv_eval [x16₃]
    exact Region.valid hTP (by addr_omega [hTP]) (by addr_omega [hTP]) (by addr_omega [hTP, TPa]))
  have m₄ := b8000365c_mem_same h₄
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80003668_spec (b8000365c_pc_not_taken h₄ (by
      rw [x16₃, op₃ 1 (by decide) 152 rfl]; decide)) (by
    rv_eval [b8000365c_keeps h₄ .x16 (by decide), x16₃]
    exact Region.valid hTP (by addr_omega [hTP]) (by addr_omega [hTP]) (by addr_omega [hTP, TPa]))
  have m₅ := b80003668_mem_same h₅
  have x16₄ : u₄.getReg .x16 = TP := (b8000365c_keeps h₄ .x16 (by decide)).trans x16₃
  have x16₅ : u₅.getReg .x16 = TP := (b80003668_keeps h₅ .x16 (by decide)).trans x16₄
  obtain ⟨u₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80003670_spec (b80003668_pc_not_taken h₅ (by
      rw [x16₄, m₄, op₃ 2 (by decide) 232 rfl, b8000365c_x13 h₄]; decide)) (by
    rv_eval [x16₅]
    exact Region.valid hTP (by addr_omega [hTP]) (by addr_omega [hTP]) (by addr_omega [hTP, TPa]))
  have m₆ := b80003670_mem_same h₆
  have x16₆ : u₆.getReg .x16 = TP := (b80003670_keeps h₆ .x16 (by decide)).trans x16₅
  obtain ⟨u₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000367c_spec (b80003670_pc_not_taken h₆ (by
      rw [x16₅, m₅, m₄, op₃ 3 (by decide) 312 rfl]; decide)) (by
    rv_eval [x16₆]
    exact Region.valid hTP (by addr_omega [hTP]) (by addr_omega [hTP]) (by addr_omega [hTP, TPa]))
  have m₇ := b8000367c_mem_same h₇
  have x16₇ : u₇.getReg .x16 = TP := (b8000367c_keeps h₇ .x16 (by decide)).trans x16₆
  obtain ⟨u₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b80003684_spec (b8000367c_pc_not_taken h₇ (by
      rw [x16₆, m₆, m₅, m₄, op₃ 4 (by decide) 392 rfl, b80003670_x14 h₆]; decide)) (by
    rv_eval [x16₇]
    exact Region.valid hTP (by addr_omega [hTP]) (by addr_omega [hTP]) (by addr_omega [hTP, TPa]))
  have m₈ := b80003684_mem_same h₈
  have hpc₈ : u₈.pc = 0x80003690 := b80003684_pc_not_taken h₈ (by
    rw [x16₇, m₇, m₆, m₅, m₄, op₃ 5 (by decide) 472 rfl]; decide)
  -- the registers at `0x80003690`
  have k₈ : ∀ r ∈ ([.x2, .x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
      u₈.getReg r = u₃.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [b80003684_keeps h₈ _ (by decide), b8000367c_keeps h₇ _ (by decide),
      b80003670_keeps h₆ _ (by decide), b80003668_keeps h₅ _ (by decide),
      b8000365c_keeps h₄ _ (by decide)]
  have o10 : u₈.getReg .x10 = BitVec.ofNat 64 0 := by
    rw [b80003684_keeps h₈ .x10 (by decide), b8000367c_keeps h₇ .x10 (by decide),
      b80003670_keeps h₆ .x10 (by decide), b80003668_keeps h₅ .x10 (by decide),
      b8000365c_keeps h₄ .x10 (by decide), b80003634_x10 h₃, e200, eTP, op 0 (by decide) 72 rfl]
  have o11 : u₈.getReg .x11 = BitVec.ofNat 64 1 := by
    rw [b80003684_keeps h₈ .x11 (by decide), b8000367c_keeps h₇ .x11 (by decide),
      b80003670_keeps h₆ .x11 (by decide), b80003668_keeps h₅ .x11 (by decide),
      b8000365c_x11 h₄, x16₃, op₃ 1 (by decide) 152 rfl]
  have o12 : u₈.getReg .x12 = BitVec.ofNat 64 2 := by
    rw [b80003684_keeps h₈ .x12 (by decide), b8000367c_keeps h₇ .x12 (by decide),
      b80003670_keeps h₆ .x12 (by decide), b80003668_x12 h₅, x16₄, m₄, op₃ 2 (by decide) 232 rfl]
  have o13 : u₈.getReg .x13 = BitVec.ofNat 64 3 := by
    rw [b80003684_keeps h₈ .x13 (by decide), b8000367c_keeps h₇ .x13 (by decide),
      b80003670_x13 h₆, x16₅, m₅, m₄, op₃ 3 (by decide) 312 rfl]
  have o15 : u₈.getReg .x15 = BitVec.ofNat 64 4 := by
    rw [b80003684_keeps h₈ .x15 (by decide), b8000367c_x15 h₇, x16₆, m₆, m₅, m₄,
      op₃ 4 (by decide) 392 rfl]
  have o14 : u₈.getReg .x14 = BitVec.ofNat 64 5 := by
    rw [b80003684_x14 h₈, x16₇, m₇, m₆, m₅, m₄, op₃ 5 (by decide) 472 rfl]
  have sp₈ : u₈.getReg .x2 = s.getReg .x2 - 2656 := (k₈ .x2 (by decide)).trans
    ((k₃ .x2 (by decide)).trans sp₂)
  have ro := R₃.inv.rodata hpre
  have ro₈ : RodataOk u₈ := by
    intro p hp
    rw [m₈, m₇, m₆, m₅, m₄]; exact ro p hp
  have r0 : u₈.getMem (BitVec.ofNat 64 0 * 8 + 0xa0000080) = 0 := ro₈.word
  have r1 : u₈.getMem (BitVec.ofNat 64 1 * 8 + 0xa0000080) = 0 := ro₈.word
  have r2 : u₈.getMem (BitVec.ofNat 64 2 * 8 + 0xa0000080) = 0 := ro₈.word
  have r3 : u₈.getMem (BitVec.ofNat 64 3 * 8 + 0xa0000080) = 0 := ro₈.word
  have r4 : u₈.getMem (BitVec.ofNat 64 4 * 8 + 0xa0000080) = 2 := ro₈.word
  have r5 : u₈.getMem (BitVec.ofNat 64 5 * 8 + 0xa0000080) = 0 := ro₈.word
  -- `n_constraints`, to `powers`
  obtain ⟨u₉, hr₉, h₉⟩ := Sym.BlockSpec.reaches b80003690_spec hpc₈ (by
    rv_eval [sp₈, o10, o11, o12, o13, o14, o15]
    and_intros
    all_goals first
      | valid_access hval [hb1]
      | addr_omega [hb1]
      | decide
)
  have k₉ := b80003690_keeps h₉
  have R₈ := R₃.same (fun a ↦ by rw [m₈, m₇, m₆, m₅, m₄]) ((k₈ .x2 (by decide)))
  have st₉ : StepW s u₈ u₉ (fun a ↦ a = s.getReg .x2 - 2624 ∨ a = s.getReg .x2 - 2496) False :=
    StepW.ofFrame hpre R₈.inv.heap
      (h₉.dframe (by rv_eval [sp₈]; simp only [true_or, or_true, and_self]))
      (fun a ha ↦ fW a (by rcases ha with rfl | rfl <;> simp only [W17a, true_or, or_true]))
      (k₉ .x2 (by decide))
  have R₉ := R₈.stepW hpre (fun a ha ↦ W17a_ok hpre R₀
    (by rcases ha with rfl | rfl <;> simp only [W17a, true_or, or_true])) st₉
  have sm₃₈ : StepW s u₃ u₈ (fun _ ↦ False) False :=
    StepW.same R₃.inv.heap (fun a ↦ by rw [m₈, m₇, m₆, m₅, m₄]) (k₈ .x2 (by decide)) _ _
  have st₂₉ := ((st₂.trans st₃).trans sm₃₈).trans st₉
  -- a frame slot `S - k` the steps after the spills do not write
  have keep₁ (c : Word) (k : Nat) (hc : c.toNat = k) (hk1 : 2456 ≤ k) (hk2 : k ≤ 2656)
      (hk : k % 8 = 0 ∧ k ≠ 2624 ∧ k ≠ 2496) : u₉.getMem (s.getReg .x2 - c) =
        u₁.getMem (s.getReg .x2 - c) := by
    obtain rfl : c = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq; rw [hc, BitVec.toNat_ofNat]; omega
    exact st₂₉.getF hpre (by addr_omega [hb1, hk1, hk2]) (fun i hi hw ↦ by
        rcases hw with ((hw | hw | hw | hw) | hw) | hw | hw
        · exact hw
        · exact slot_ne hpre (m := 152) hk2 (by omega) (by omega) hi hw
        · exact slot_ne hpre (m := 144) hk2 (by omega) (by omega) hi hw
        · exact slot_ne hpre (m := 136) hk2 (by omega) (by omega) hi hw
        · exact hw
        · exact slot_ne hpre (m := 2624) hk2 (by omega) (by omega) hi hw
        · exact slot_ne hpre (m := 2496) hk2 (by omega) (by omega) hi hw)
      fun _ ↦ by rw [tp]; addr_omega [hb1, hk1, hk2]
  have ea (c d : Word) (hc : c.toNat + d.toNat = 2656) : u₀.getReg .x2 + c = s.getReg .x2 - d := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have eb (c d : Word) (hc : c.toNat + d.toNat = 2656) : u₈.getReg .x2 + c = s.getReg .x2 - d := by
    rw [sp₈]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hc]
  have chain (r : Reg) (hr : r ∈ ([.x8, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : u₈.getReg r = u₁.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [k₈ _ (by decide), k₃ _ (by decide), hp₁ _ (by decide)]
  have ptrR {v : MachineState} (R : Rest s u₀ v) : v.getMem (tp s) = s.getReg .x13 := by
    rw [etp, R.get (keep_slot hpre (by omega)), ← etp]; exact h.proofPtr
  have ro₀ : u₈.getMem 0xa0000080 = 0 := ro₈.word
  have ro₁ : u₈.getMem 0xa0000088 = 0 := ro₈.word
  have ro₂ : u₈.getMem 0xa0000090 = 0 := ro₈.word
  have ro₃ : u₈.getMem 0xa0000098 = 0 := ro₈.word
  have ro₄ : u₈.getMem 0xa00000a0 = 2 := ro₈.word
  have ro₅ : u₈.getMem 0xa00000a8 = 0 := ro₈.word
  refine ⟨u₉, hrv₁.trans ?_, Or.inl ⟨b80003690_pc h₉, {
    rest := R₉
    st := (st₁.trans st₂₉).weaken (fun a ha ↦ by
        rcases ha with ha | (((ha | ha) | ha) | ha)
        · exact ha
        · exact ha.elim
        · exact W3 a ha
        · exact ha.elim
        · rcases ha with rfl | rfl <;> simp only [W17a, true_or, or_true]) fun _ ↦ trivial
    x1 := b80003690_x1 h₉
    x10 := by rw [b80003690_x10 h₉, sp₈]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x11 := by rw [b80003690_x11 h₉, sp₈]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x12 := h₉.reg_eq .x12 rfl (by
      rv_eval [o10, o11, o12, o13, o14, o15, ro₀, ro₁, ro₂, ro₃, ro₄, ro₅])
    x24 := by
      rw [b80003690_x24 h₉, o10, o11, o12, o13, o14, o15, r0, r1, r2, r3, r4, r5]
      rfl
    x22 := by
      rw [b80003690_x22 h₉, chain .x26 (by decide), b800035f0_x26 h₁, ea 1792 864 rfl]
    x23 := by
      rw [b80003690_x23 h₉, chain .x24 (by decide), b800035f0_x24 h₁, ea 1832 824 rfl]
    x8 := by
      rw [k₉ .x8 (by decide), chain .x8 (by decide), b800035f0_x8 h₁, ea 1840 816 rfl]
    x20 := by
      rw [k₉ .x20 (by decide), chain .x20 (by decide), b800035f0_x20 h₁, ea 1784 872 rfl]
    regs := fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
      rw [k₉ _ (by decide), chain _ (by decide), k₁ _ (by decide)]
    m184 := by
      rw [keep₁ 2472 2472 rfl (by omega) (by omega) (by omega), show s.getReg .x2 - 2472 =
        u₀.getReg .x2 + 184 from (ea 184 2472 rfl).symm, b800035f0_m_x2_184 h₁, h.x11]
    m56 := by
      rw [keep₁ 2600 2600 rfl (by omega) (by omega) (by omega), show s.getReg .x2 - 2600 =
        u₀.getReg .x2 + 56 from (ea 56 2600 rfl).symm, b800035f0_m_x2_56 h₁, ea 1816 840 rfl]
    m64 := by
      rw [keep₁ 2592 2592 rfl (by omega) (by omega) (by omega), show s.getReg .x2 - 2592 =
        u₀.getReg .x2 + 64 from (ea 64 2592 rfl).symm, b800035f0_m_x2_64 h₁, ea 1808 848 rfl]
    m160 := by
      rw [show s.getReg .x2 - 2496 = u₈.getReg .x2 + 160 from (eb 160 2496 rfl).symm,
        b80003690_m_x2_160 h₉, chain .x20 (by decide), b800035f0_x20 h₁, ea 1784 872 rfl]
    sample := fun T hT ↦ by
      have hT₁ := st₁.transcript hpre h.inv h.proofPtr (fun a ha ↦ ⟨fW a ha, W17a_tp hpre ha⟩) hT
      have hT₂ := tr₂ T hT₁
      have hT₃ := st₃.transcript hpre R₂.inv (ptrR R₂)
        (fun a ha ↦ ⟨fW a (W3 a ha), W17a_tp hpre (W3 a ha)⟩) hT₂
      have hT₈ := TranscriptAt.same hpre R₃.inv (ptrR R₃) (fun a ↦ by rw [m₈, m₇, m₆, m₅, m₄]) hT₃
      have hT₉ := st₉.transcript hpre R₈.inv (ptrR R₈) (fun a ha ↦ ⟨fW a (by
        rcases ha with rfl | rfl <;> simp only [W17a, true_or, or_true]), W17a_tp hpre (by
        rcases ha with rfl | rfl <;> simp only [W17a, true_or, or_true])⟩) hT₈
      refine ⟨_, ?_, hT₉⟩
      rw [sample_lanes hT₂.sponge]
      have st₃₉ := sm₃₈.trans st₉
      have g (k : Nat) (hk : 128 ≤ k ∧ k ≤ 152) (c : Word) (hc : c = BitVec.ofNat 64 k) :
          u₉.getMem (s.getReg .x2 - c) = u₃.getMem (s.getReg .x2 - c) := by
        subst hc
        exact st₃₉.getF hpre (by addr_omega [hb1, hk]) (fun i hi hw ↦ by
            rcases hw with hw | hw | hw
            · exact hw
            · exact slot_ne hpre (m := 2624) (by omega) (by omega) (by omega) hi hw
            · exact slot_ne hpre (m := 2496) (by omega) (by omega) (by omega) hi hw)
          fun hf ↦ (hf.elim id id).elim
      have a1 : s.getReg .x2 - 152 + 8 = s.getReg .x2 - 144 := by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      have a2 : s.getReg .x2 - 152 + 16 = s.getReg .x2 - 136 := by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      have b0 : tp s + 136 = v₁.getReg .x2 + 344 := by
        rw [tp, sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      have b1 : tp s + 136 + 8 = v₁.getReg .x2 + 352 := by
        rw [tp, sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      have b2 : tp s + 136 + 16 = v₁.getReg .x2 + 360 := by
        rw [tp, sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      have c0 : s.getReg .x2 - 152 = v₁.getReg .x22 + 360 := by
        rw [x22₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      have c1 : s.getReg .x2 - 144 = v₁.getReg .x22 + 368 := by
        rw [x22₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      have c2 : s.getReg .x2 - 136 = v₁.getReg .x22 + 376 := by
        rw [x22₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
      simp only [eAt]
      rw [a1, a2, g 152 (by omega) 152 rfl, g 144 (by omega) 144 rfl, g 136 (by omega) 136 rfl,
        b1, b2, b0, c0, c1, c2, b80003634_m_x22_360 h₃, b80003634_m_x22_368 h₃,
        b80003634_m_x22_376 h₃] }⟩⟩
  exact hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans (hr₇.trans (hr₈.trans hr₉)))))

end Rv64Verifier.Proofs.Walk
