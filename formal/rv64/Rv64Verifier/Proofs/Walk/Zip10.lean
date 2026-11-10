import Rv64Verifier.Proofs.Walk.Keep10

/-!
# `walk`: the bus blocks' loop's state (R10)

The three `Vec<BusBlock>`s `count`, `push` and `pull` are at `sp + 2144`, `sp + 2240` and
`sp + 2432` (`S - 512`, `S - 416`, `S - 224`). `Vecs10 s u lo P` says they hold `P`, are sound,
reach only memory allocated from `lo` on, and reach pairwise apart memory. At the loop's header
`0x80002e94` (`Zip10 .. i`), `P` is `busBlocksRust` over the first `i` tables.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `busBlocksRust`'s step. -/
def busStep (acc : List BusBlockRust × List BusBlockRust × List BusBlockRust)
    (x : (TableRust × ℕ) × BitVec 64) : List BusBlockRust × List BusBlockRust × List BusBlockRust :=
  let block := fun coordinates ↦ (⟨x.1.2, x.2, coordinates, x.1.1.opcode⟩ : BusBlockRust)
  (acc.1 ++ x.1.1.flushes.push.map block, acc.2.1 ++ x.1.1.flushes.pull.map block,
    acc.2.2 ++ x.1.1.countColumns.map fun l ↦ block [colRust l 0])

theorem busBlocksRust_foldl (T : List TableRust) (H : List ℕ) (R : List (BitVec 64)) :
    busBlocksRust T H R = ((T.zip H).zip R).foldl busStep ([], [], []) := rfl

/-- The blocks of the first `i` tables. -/
def zipPre (A : List E) (i : Nat) : List BusBlockRust × List BusBlockRust × List BusBlockRust :=
  (((tablesRust.zip (tableLogHeightsRust (rowsOf A))).zip (rowsOf A)).take i).foldl busStep
    ([], [], [])

/-- The three `Vec<BusBlock>`s hold `P`, sound, reaching memory from `lo` on, pairwise apart. -/
structure Vecs10 (s u : MachineState) (lo : Nat)
    (P : List BusBlockRust × List BusBlockRust × List BusBlockRust) : Prop where
  push : BlocksOk u (s.getReg .x2 - 416)
  pull : BlocksOk u (s.getReg .x2 - 224)
  count : BlocksOk u (s.getReg .x2 - 512)
  pushV : blocksOf u (s.getReg .x2 - 416) = P.1
  pullV : blocksOf u (s.getReg .x2 - 224) = P.2.1
  countV : blocksOf u (s.getReg .x2 - 512) = P.2.2
  fresh : ∀ x, (blocksFoot u (s.getReg .x2 - 416) x ∨ blocksFoot u (s.getReg .x2 - 224) x ∨
    blocksFoot u (s.getReg .x2 - 512) x) → lo ≤ x.toNat
  d1 : ∀ x, blocksFoot u (s.getReg .x2 - 416) x → ¬ blocksFoot u (s.getReg .x2 - 224) x
  d2 : ∀ x, blocksFoot u (s.getReg .x2 - 416) x → ¬ blocksFoot u (s.getReg .x2 - 512) x
  d3 : ∀ x, blocksFoot u (s.getReg .x2 - 224) x → ¬ blocksFoot u (s.getReg .x2 - 512) x

/-- At the loop's header, `i` tables done. -/
structure Zip10 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo : Nat) (i : Nat) : Prop where
  base : Base10 OI s u A k R Q B lo
  op5 : u.getMem (B + 472) = 5
  vecs : Vecs10 s u lo (zipPre A i)
  lt : i < 6
  x9 : u.getReg .x9 = BitVec.ofNat 64 i
  x18 : u.getReg .x18 = s.getReg .x2 - 1488
  x19 : u.getReg .x19 = s.getReg .x2 - 1344
  x20 : u.getReg .x20 = s.getReg .x2 - 512
  x21 : u.getReg .x21 = 0xa0000400
  n : u.getMem (s.getReg .x2 - 2472) = 6

theorem exL {x : Sym.Expect} {s t : MachineState} (h : x.Holds s t) {w : Word → Prop}
    (hw : ∀ k ∈ x.writes, w (k.eval s)) : Layout.DFrame s t w := fun a ha hw8 ↦
  h.frame a fun k hk he ↦ ha a ⟨le_refl _, by omega⟩ (he ▸ hw k hk)

/-- Empty `Vec`s, `{0, 8, 0}`. -/
theorem blocksOk_empty {u : MachineState} {a : Word} (h0 : u.getMem a = 0) (h8 : u.getMem (a + 8) = 8)
    (h16 : u.getMem (a + 16) = 0) : BlocksOk u a ∧ blocksOf u a = [] ∧ ∀ x, ¬ blocksFoot u a x := by
  have hc : vecCap u a = 0 := h0
  have hp : vecPtr u a = 8 := h8
  have hl : vecLen u a = 0 := h16
  refine ⟨?_, ?_, fun x hx ↦ ?_⟩
  · simp only [BlocksOk, hc, hp, hl]
    exact ⟨⟨rfl, Or.inl rfl⟩, le_refl _, fun j hj ↦ absurd hj (by simp),
      fun x ⟨j, hj, _⟩ ↦ absurd hj (by simp)⟩
  · simp [blocksOf, blocksAt, hl]
  · simp only [blocksFoot, hc, hp, hl] at hx
    rcases hx with hx | ⟨j, hj, _⟩
    · simp only [Within] at hx
      have : (0 : Word).toNat = 0 := rfl
      omega
    · simp at hj

theorem Base10.same {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo : Nat} (hpre : WalkPre s)
    (h : Base10 OI s u A k R Q B lo) (hm : ∀ a, v.getMem a = u.getMem a)
    (sp : v.getReg .x2 = u.getReg .x2) : Base10 OI s v A k R Q B lo := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact h.keep hpre (w := fun _ ↦ False) (Layout.DFrame.of_same hm _) (fun _ h ↦ h.elim)
    ⟨hn ▸ h.inv.heap.lo, hn ▸ h.inv.heap.hi⟩ hn.ge sp

set_option maxRecDepth 8192 in
/-- From `0x80002e40`: the last opcode, the three empty `Vec`s, `min(6, 6)` at `sp + 184`, to the
loop's header with no table done. -/
theorem r10head {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} (hpre : WalkPre s) (h : AtR10 OI s u A k R Q B) :
    ∃ t, Reaches Image.code u t ∧ t.pc = 0x80002e94 ∧ Zip10 OI s t A k R Q B (heapNext u) 0 := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hs0 := hpre.heap.lo
  simp only [heapStart] at hs0
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := h.inv.sp
  have B0 := h.base
  have hB := h.bufB
  have hh := h.inv.heap.hi
  simp only [heapEnd] at hh
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80002e40_spec h.pc (by
    rv_eval [sp, h.x20, h.x18]
    simp only [Sym.validAccess_eight, ne_eq]
    and_intros
    all_goals first
      | (intro he; have := congrArg BitVec.toNat he; addr_omega [this, hb1, hb2, hB, hh, hs0])
      | addr_omega [hb1, hb2, hb3, hB, hh, hs0])
  -- what the block writes: the frame and the last opcode
  have fr₁ : Layout.DFrame u u₁ fun a ↦ Within a (s.getReg .x2 - 2472) 8 ∨
      Within a (s.getReg .x2 - 512) 24 ∨ Within a (s.getReg .x2 - 416) 24 ∨
      Within a (s.getReg .x2 - 224) 24 ∨ Within a (B + 472) 8 :=
    exL h₁ (by
      rv_eval [sp, h.x20, h.x18]
      simp only [Within]
      and_intros <;> addr_omega [hb1, hb2, hB, hh, hs0])
  have hn₁ : heapNext u₁ = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr₁ nextAddr (fun y hy hw ↦ by
      simp only [Within, nextAddr] at hy hw
      rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hy, hw, hb1, hB, hh]) (by decide))
  have hv₁ : HeapOk u₁ := ⟨hn₁ ▸ h.inv.heap.lo, hn₁ ▸ h.inv.heap.hi⟩
  have k₁ := b80002e40_keeps h₁
  have B₁ : Base10 OI s u₁ A k R Q B (heapNext u) := B0.keep hpre fr₁ (fun a ha ↦ by
      simp only [X10, W10, Within] at ha ⊢
      rcases ha with ha | ha | ha | ha | ha
      · exact Or.inl (Or.inr (Or.inl ha))
      all_goals first
        | exact Or.inr ha
        | exact Or.inl (Or.inl ⟨by addr_omega [ha, hb1], by addr_omega [ha, hb1]⟩)) hv₁ hn₁.ge (k₁ .x2 (by decide))
  have hc₁ : (u.getReg .x21).toNat ≤ (u.getReg .x27).toNat := by rw [h.x21, h.x27]
  have pc₁ := b80002e40_pc_not_taken h₁ hc₁
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide)]; exact sp
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80002e70_spec pc₁ (by
    rv_eval [sp₁]
    simp only [Sym.validAccess_eight]
    addr_omega [hb1, hb2, hb3])
  have e184 : u₁.getReg .x2 + 184 = s.getReg .x2 - 2472 := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fr₂ : MemFrame u₁ u₂ (s.getReg .x2 - 2472) 8 := by
    rw [← e184]; exact b80002e70_frame h₂ (by rw [sp₁]; addr_omega [hb1])
  have m₂ (a : Word) (ha : ¬ Within a (s.getReg .x2 - 2472) 8) : u₂.getMem a = u₁.getMem a := fr₂ a ha
  have hn₂ : heapNext u₂ = heapNext u₁ := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (m₂ _ (by simp only [Within, nextAddr]; addr_omega [hb1]))
  have k₂ := b80002e70_keeps h₂
  have B₂ : Base10 OI s u₂ A k R Q B (heapNext u) := B₁.keep hpre (MemFrame.dframe fr₂)
    (fun a ha ↦ Or.inl (Or.inr (Or.inl ha))) ⟨hn₂ ▸ hv₁.lo, hn₂ ▸ hv₁.hi⟩ hn₂.ge
    (k₂ .x2 (by decide))
  have pc₂ := b80002e70_pc h₂
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80002e78_spec pc₂ (by rv_eval [])
  have x27₂ : u₂.getReg .x27 = 6 := by rw [k₂ .x27 (by decide), k₁ .x27 (by decide)]; exact h.x27
  have pc₃ := b80002e78_pc_taken h₃ (by rw [x27₂]; decide)
  have m₃ := b80002e78_mem_same h₃
  have k₃ := b80002e78_keeps h₃
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80002e80_spec pc₃ (by rv_eval [])
  have m₄ := b80002e80_mem_same h₄
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [k₃ .x2 (by decide), k₂ .x2 (by decide)]; exact sp₁
  have B₄ : Base10 OI s u₄ A k R Q B (heapNext u) :=
    (B₂.same hpre m₃ (k₃ .x2 (by decide))).same hpre m₄ (b80002e80_keeps h₄ .x2 (by decide))
  have m24 (a : Word) (ha : ¬ Within a (s.getReg .x2 - 2472) 8) : u₄.getMem a = u₁.getMem a := by
    rw [m₄, m₃, m₂ a ha]
  have e20 : u.getReg .x20 = s.getReg .x2 - 512 := h.x20
  have hz (c d : Nat) (hcd : c + d = 512) (hd : d ≤ 512) (v : Word)
      (hv : u₁.getMem (u.getReg .x20 + BitVec.ofNat 64 c) = v) :
      u₄.getMem (s.getReg .x2 - BitVec.ofNat 64 d) = v := by
    have e : u.getReg .x20 + BitVec.ofNat 64 c = s.getReg .x2 - BitVec.ofNat 64 d := by
      rw [e20]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hcd, hd]
    rw [m24 _ (by simp only [Within]; addr_omega [hb1, hcd, hd]), ← e, hv]
  have x9u : u.getReg .x9 = 8 := h.x9
  have cnt := blocksOk_empty (u := u₄) (a := s.getReg .x2 - 512)
    (hz 0 512 rfl (by decide) 0 (by simpa using b80002e40_m_x20_0 h₁))
    (by
      have := hz 8 504 rfl (by decide) 8 (by rw [← x9u]; exact b80002e40_m_x20_8 h₁)
      refine (congrArg u₄.getMem ?_).trans this; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by
      have := hz 16 496 rfl (by decide) 0 (b80002e40_m_x20_16 h₁)
      refine (congrArg u₄.getMem ?_).trans this; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have psh := blocksOk_empty (u := u₄) (a := s.getReg .x2 - 416)
    (hz 96 416 rfl (by decide) 0 (b80002e40_m_x20_96 h₁))
    (by
      have := hz 104 408 rfl (by decide) 8 (by rw [← x9u]; exact b80002e40_m_x20_104 h₁)
      refine (congrArg u₄.getMem ?_).trans this; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by
      have := hz 112 400 rfl (by decide) 0 (b80002e40_m_x20_112 h₁)
      refine (congrArg u₄.getMem ?_).trans this; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have pul := blocksOk_empty (u := u₄) (a := s.getReg .x2 - 224)
    (hz 288 224 rfl (by decide) 0 (b80002e40_m_x20_288 h₁))
    (by
      have := hz 296 216 rfl (by decide) 8 (by rw [← x9u]; exact b80002e40_m_x20_296 h₁)
      refine (congrArg u₄.getMem ?_).trans this; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by
      have := hz 304 208 rfl (by decide) 0 (b80002e40_m_x20_304 h₁)
      refine (congrArg u₄.getMem ?_).trans this; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have op : u₄.getMem (B + 472) = 5 := by
    rw [m24 _ (by simp only [Within]; addr_omega [hb1, hB, hh]), ← h.x18, b80002e40_m_x18_472 h₁]
    exact h.x8
  refine ⟨u₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), b80002e80_pc h₄, {
    base := B₄
    op5 := op
    vecs := ⟨psh.1, pul.1, cnt.1, psh.2.1, pul.2.1, cnt.2.1,
      fun x hx ↦ by
        rcases hx with hx | hx | hx
        · exact absurd hx (psh.2.2 x)
        · exact absurd hx (pul.2.2 x)
        · exact absurd hx (cnt.2.2 x),
      fun x hx ↦ absurd hx (psh.2.2 x), fun x hx ↦ absurd hx (psh.2.2 x),
      fun x hx ↦ absurd hx (pul.2.2 x)⟩
    lt := by decide
    x9 := b80002e80_x9 h₄
    x18 := by rw [b80002e80_x18 h₄, sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x19 := by rw [b80002e80_x19 h₄, sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x20 := by
      rw [b80002e80_keeps h₄ .x20 (by decide), k₃ .x20 (by decide), k₂ .x20 (by decide),
        k₁ .x20 (by decide)]
      exact h.x20
    x21 := b80002e80_x21 h₄
    n := by rw [m₄, m₃, ← e184]; exact b80002e70_m_x2_184 h₂ }⟩


end Rv64Verifier.Proofs.Walk
