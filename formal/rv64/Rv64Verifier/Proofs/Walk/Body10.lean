import Rv64Verifier.Proofs.Walk.Ext10

/-!
# `walk`: the bus blocks' loop, `push` and `pull` (R10)

From the loop's header (`Zip10 .. i`): the table's height and rows staged at `sp + 1168` and
`sp + 1312`, `push.extend(table.flushes.push.iter().map(block))` and the same for `pull`
(`extend_trusted`, `extCall`), then the opcode's bound check. At `0x80002f5c` (`Mid10`) the
`Vec`s hold the first `i` tables' blocks and the `i`-th table's `push` and `pull` blocks.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem mul80 {i : Nat} (hi : i < 6) :
    BitVec.ofNat 64 i * 64 + BitVec.ofNat 64 i * 16 = BitVec.ofNat 64 (80 * i) := by
  interval_cases i <;> decide

theorem mul8 {i : Nat} (hi : i < 6) : BitVec.ofNat 64 i * 8 = BitVec.ofNat 64 (8 * i) := by
  interval_cases i <;> decide

theorem mul24 (L : Word) : L * 16 + L * 8 = BitVec.ofNat 64 (24 * L.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h16 : (16 : Word).toNat = 16 := rfl
  have h8 : (8 : Word).toNat = 8 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h16, h8]
  omega

/-- The three `Vec`s are kept by writes in the frame apart from their headers. -/
theorem Vecs10.keepFrame {s c t : MachineState} {lo : Nat}
    {P : List BusBlockRust × List BusBlockRust × List BusBlockRust} (hpre : WalkPre s)
    (V : Vecs10 s c lo P) (hc : HeapOk c) (mono : heapNext c ≤ heapNext t) {w : Word → Prop}
    (fr : Layout.DFrame c t w) (hw : ∀ x, w x → (s.getReg .x2 - 2656).toNat ≤ x.toNat ∧
      x.toNat < (s.getReg .x2 - 104).toNat ∧ ¬ Within x (s.getReg .x2 - 512) 24 ∧
      ¬ Within x (s.getReg .x2 - 416) 24 ∧ ¬ Within x (s.getReg .x2 - 224) 24) :
    Vecs10 s t lo P := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hci := hc.hi
  simp only [heapEnd] at hci
  have K (a : Word) (hok : BlocksOk c a) (ha1 : (s.getReg .x2 - 2080).toNat ≤ a.toNat)
      (ha2 : a.toNat + 24 ≤ (s.getReg .x2 - 104).toNat)
      (hh : ∀ x, w x → ¬ Within x a 24) :=
    vecKeep fr hok (by addr_omega [ha2, hb1, hb2]) (fun x hx hwx ↦ hh x hwx hx) (fun x hx hwx ↦ by
      have h1 := hok.foot_below hx
      have h2 := hw x hwx
      simp only [heapStart] at h1
      addr_omega [h1, h2, hci, hb1]) hc mono
  have kp := K _ V.push (by addr_omega [hb1]) (by addr_omega [hb1]) fun x hx ↦ (hw x hx).2.2.2.1
  have kl := K _ V.pull (by addr_omega [hb1]) (by addr_omega [hb1]) fun x hx ↦ (hw x hx).2.2.2.2
  have kc := K _ V.count (by addr_omega [hb1]) (by addr_omega [hb1]) fun x hx ↦ (hw x hx).2.2.1
  refine ⟨kp.1, kl.1, kc.1, by rw [kp.2.1]; exact V.pushV, by rw [kl.2.1]; exact V.pullV,
    by rw [kc.2.1]; exact V.countV, ?_, ?_, ?_, ?_⟩ <;> simp only [kp.2.2, kl.2.2, kc.2.2]
  · exact V.fresh
  · exact V.d1
  · exact V.d2
  · exact V.d3

theorem heightsLe {s : MachineState} {A : List E} {k : Nat} (h : HeadOk s A k) (i : Nat) :
    (tableLogHeightsRust (rowsOf A)).getD i 0 ≤ 32 := by
  refine getD_le (tableLogHeightsRust_le _ fun r hr ↦ ?_) i
  have h1 := List.all_eq_true.mp h.2.2.1 r hr
  simp only [decide_eq_true_eq, BitVec.le_def] at h1
  have : (1#64 <<< maxTableLogRust).toNat = 2 ^ 32 := by decide
  omega

theorem tablesRust_opcode_eq {i : Nat} {t : TableRust} (h : tablesRust[i]? = some t) : t.opcode = i := by
  have e := congrArg (·[i]?) (tablesRust_opcode.trans opcodes_eq)
  simp only [List.getElem?_map, h, Option.map_some] at e
  have hi := tablesRust_some h
  rw [List.getElem?_range (by simp only [nTablesRust]; omega)] at e
  exact Option.some.inj e

/-- The `i`-th opcode, in a state holding all six. -/
theorem opAt {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo : Nat} (h : Base10 OI s u A k R Q B lo)
    (op5 : u.getMem (B + 472) = 5) {i : Nat} (hi : i < 6) :
    u.getMem (B + BitVec.ofNat 64 (80 * i) + 72) = BitVec.ofNat 64 i := by
  have hB := h.bufB
  have hl := h.loLe
  have hhi := h.inv.heap.hi
  simp only [heapEnd] at hhi
  by_cases h5 : i < 5
  · rw [← h.opcodes i h5]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hB, hl, hhi, hi]
  · have : i = 5 := by omega
    subst this
    have e : B + BitVec.ofNat 64 (80 * 5) + 72 = B + 472 := by
      apply BitVec.eq_of_toNat_eq; addr_omega [hB, hl, hhi]
    rw [e, op5]
    rfl

/-- The block of the `i`-th table with coordinates `c`. -/
def blkOf (A : List E) (i : Nat) (c : List FormRust) : BusBlockRust :=
  ⟨(tableLogHeightsRust (rowsOf A)).getD i 0, (rowsOf A).getD i 0, c, i⟩

/-- Past the `i`-th table's `push` and `pull`, before its opcode's check. -/
structure Mid10 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo : Nat) (i : Nat)
    (P : List BusBlockRust × List BusBlockRust × List BusBlockRust) : Prop where
  base : Base10 OI s u A k R Q B lo
  op5 : u.getMem (B + 472) = 5
  vecs : Vecs10 s u lo P
  lt : i < 6
  x9 : u.getReg .x9 = BitVec.ofNat 64 i
  x10 : u.getReg .x10 = BitVec.ofNat 64 i
  x18 : u.getReg .x18 = s.getReg .x2 - 1488
  x19 : u.getReg .x19 = s.getReg .x2 - 1344
  x20 : u.getReg .x20 = s.getReg .x2 - 512
  x21 : u.getReg .x21 = 0xa0000400
  x22 : u.getReg .x22 = B + BitVec.ofNat 64 (80 * i)
  n : u.getMem (s.getReg .x2 - 2472) = 6
  hgt : u.getMem (s.getReg .x2 - 1488) = BitVec.ofNat 64 ((tableLogHeightsRust (rowsOf A)).getD i 0)
  row : u.getMem (s.getReg .x2 - 1344) = (rowsOf A).getD i 0

theorem e94_1736 {s t : MachineState} (h : b80002e94.Holds s t) :
    t.getMem (s.getReg .x2 + 1736) =
      s.getMem ((s.getMem (s.getReg .x2 + (200 : Word)) + ((s.getReg .x9 * (64 : Word)) +
        (s.getReg .x9 * (16 : Word)))) + (32 : Word)) +
      ((s.getMem ((s.getMem (s.getReg .x2 + (200 : Word)) + ((s.getReg .x9 * (64 : Word)) +
        (s.getReg .x9 * (16 : Word)))) + (40 : Word)) * (16 : Word)) +
       (s.getMem ((s.getMem (s.getReg .x2 + (200 : Word)) + ((s.getReg .x9 * (64 : Word)) +
        (s.getReg .x9 * (16 : Word)))) + (40 : Word)) * (8 : Word))) :=
  h.mem_eq 3 (by decide) (by rv_eval []) (by rv_eval [])

set_option maxRecDepth 8192 in
/-- The `i`-th table's `push` and `pull` blocks. -/
theorem zipExt (hE : ExtendBlocksSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u : MachineState} {A : List E} {k : Nat} {R Q B : Word} {lo i : Nat} (hpre : WalkPre s)
    (hpc : u.pc = 0x80002e94) (h : Zip10 OI s u A k R Q B lo i) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨ (t.pc = 0x80002f5c ∧ ∃ tb : TableRust,
      tablesRust[i]? = some tb ∧ Mid10 OI s t A k R Q B lo i
        ((zipPre A i).1 ++ tb.flushes.push.map (blkOf A i),
          (zipPre A i).2.1 ++ tb.flushes.pull.map (blkOf A i), (zipPre A i).2.2))) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have H := h.base
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := H.inv.sp
  have hi := h.lt
  have hB := H.bufB
  have hR := H.bufR
  have hQ := H.bufQ
  have hl := H.loLe
  have hhi := H.inv.heap.hi
  have hs0 := hpre.heap.lo
  simp only [heapEnd, heapStart] at hhi hs0
  obtain ⟨_, _, _, sR, sQ, sB⟩ := H.slots
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80002e94_spec hpc (by
    rv_eval [sp, h.x9, sR, sQ, sB, mul80 hi, mul8 hi]
    simp only [Sym.validAccess_eight]
    and_intros <;> addr_omega [hb1, hb2, hb3, hB, hR, hQ, hl, hhi, hs0, hi])
  -- the table
  have hl6 : i < tablesRust.length := by
    have : tablesRust.length = 6 := rfl
    omega
  obtain ⟨tb, htb⟩ : ∃ tb, tablesRust[i]? = some tb := ⟨_, List.getElem?_eq_getElem hl6⟩
  set tbl := B + BitVec.ofNat 64 (80 * i) with htbl
  have htN : tbl.toNat = B.toNat + 80 * i := by rw [htbl]; addr_omega [hB, hl, hhi, hi]
  clear_value tbl
  have ht80 : 0x20000000 ≤ tbl.toNat ∧ tbl.toNat + 80 ≤ lo ∧ tbl.toNat % 8 = 0 := by omega
  -- the block's effect
  have e200 : u.getMem (u.getReg .x2 + (200 : Word)) = B := by
    rw [sp]; refine (congrArg u.getMem ?_).trans sB; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e176 : u.getMem (u.getReg .x2 + (176 : Word)) = R := by
    rw [sp]; refine (congrArg u.getMem ?_).trans sR; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e192 : u.getMem (u.getReg .x2 + (192 : Word)) = Q := by
    rw [sp]; refine (congrArg u.getMem ?_).trans sQ; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have eX : u.getMem (u.getReg .x2 + (200 : Word)) + ((u.getReg .x9 * (64 : Word)) +
      (u.getReg .x9 * (16 : Word))) = tbl := by
    rw [e200, h.x9, mul80 hi, htbl]
  have e1168 : u.getReg .x2 + 1168 = s.getReg .x2 - 1488 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1312 : u.getReg .x2 + 1312 = s.getReg .x2 - 1344 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1728 : u.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1736 : u.getReg .x2 + 1736 = s.getReg .x2 - 920 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1744 : u.getReg .x2 + 1744 = s.getReg .x2 - 912 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1752 : u.getReg .x2 + 1752 = s.getReg .x2 - 904 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1760 : u.getReg .x2 + 1760 = s.getReg .x2 - 896 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fr₁ : MemFrame u u₁ (s.getReg .x2 - 1488) 600 := by
    rw [← e1168]; exact b80002e94_frame h₁ (by rw [sp]; addr_omega [hb1])
  have k₁ := b80002e94_keeps h₁
  have m₁ (a : Word) (ha : ¬ Within a (s.getReg .x2 - 1488) 600) : u₁.getMem a = u.getMem a :=
    fr₁ a ha
  have hn₁ : heapNext u₁ = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (m₁ _ (by simp only [Within, nextAddr]; addr_omega [hb1]))
  have hv₁ : HeapOk u₁ := ⟨hn₁ ▸ H.inv.heap.lo, hn₁ ▸ H.inv.heap.hi⟩
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide)]; exact sp
  have frw₁ : ∀ x, Within x (s.getReg .x2 - 1488) 600 → (s.getReg .x2 - 2656).toNat ≤ x.toNat ∧
      x.toNat < (s.getReg .x2 - 104).toNat ∧ ¬ Within x (s.getReg .x2 - 512) 24 ∧
      ¬ Within x (s.getReg .x2 - 416) 24 ∧ ¬ Within x (s.getReg .x2 - 224) 24 := fun x hx ↦ by
    simp only [Within] at hx ⊢
    refine ⟨by addr_omega [hx, hb1], by addr_omega [hx, hb1], by addr_omega [hx, hb1],
      by addr_omega [hx, hb1], by addr_omega [hx, hb1]⟩
  have B₁ : Base10 OI s u₁ A k R Q B lo := H.keep hpre (MemFrame.dframe fr₁) (fun x hx ↦ by
      have := frw₁ x hx
      simp only [Within] at hx
      exact Or.inl (Or.inl ⟨by addr_omega [hx, hb1], this.2.1⟩)) hv₁ hn₁.ge (k₁ .x2 (by decide))
  have V₁ := h.vecs.keepFrame hpre H.inv.heap hn₁.ge (MemFrame.dframe fr₁) frw₁
  have T₁ := B₁.tables i tb htb
  rw [← htbl] at T₁
  -- the iterator and the captures
  have mH : u₁.getMem (s.getReg .x2 - 1488) =
      BitVec.ofNat 64 ((tableLogHeightsRust (rowsOf A)).getD i 0) := by
    rw [← e1168, b80002e94_m_x2_1168 h₁, e192, h.x9, mul8 hi]; exact H.heights i hi
  have mR : u₁.getMem (s.getReg .x2 - 1344) = (rowsOf A).getD i 0 := by
    rw [← e1312, b80002e94_m_x2_1312 h₁, e176, h.x9, mul8 hi]; exact H.rows i hi
  have hw32 : u₁.getMem (tbl + 32) = u.getMem (tbl + 32) :=
    m₁ _ (by simp only [Within]; addr_omega [htN, hB, hl, hhi, hb1, hi])
  have hw40 : u₁.getMem (tbl + 40) = u.getMem (tbl + 40) :=
    m₁ _ (by simp only [Within]; addr_omega [htN, hB, hl, hhi, hb1, hi])
  have e24_8 : tbl + 24 + 8 = tbl + 32 := by rw [BitVec.add_assoc]; rfl
  have e24_16 : tbl + 24 + 16 = tbl + 40 := by rw [BitVec.add_assoc]; rfl
  have c0 : u₁.getMem (s.getReg .x2 - 928) = vecPtr u₁ (tbl + 24) := by
    rw [← e1728, b80002e94_m_x2_1728 h₁, eX, vecPtr, e24_8, hw32]
  have c8 : u₁.getMem (s.getReg .x2 - 920) =
      vecPtr u₁ (tbl + 24) + BitVec.ofNat 64 (24 * (vecLen u₁ (tbl + 24)).toNat) := by
    rw [← e1736, e94_1736 h₁, eX, vecPtr, vecLen, e24_8, e24_16, hw32, hw40, mul24]
  have c16 : u₁.getMem (s.getReg .x2 - 912) = s.getReg .x2 - 1488 := by
    rw [← e1744, b80002e94_m_x2_1744 h₁, h.x18]
  have c24 : u₁.getMem (s.getReg .x2 - 904) = s.getReg .x2 - 1344 := by
    rw [← e1752, b80002e94_m_x2_1752 h₁, h.x19]
  have c32 : u₁.getMem (s.getReg .x2 - 896) = tbl := by
    rw [← e1760, b80002e94_m_x2_1760 h₁, eX]
  -- `push.extend`
  have e2240 : u.getReg .x2 + 2240 = s.getReg .x2 - 416 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hVlo (o : Nat) (V : Word) (hV : ∀ x, formVecsDeep u₁ V x → flushesDeep u₁ (tbl + 24) x) :
      ∀ x, formVecsDeep u₁ V x → x.toNat < lo := fun x hx ↦
    B₁.below i hi x (by rw [← htbl]; exact Or.inr (hV x hx))
  have hap (a : Word) (ha : a = s.getReg .x2 - 416 ∨ a = s.getReg .x2 - 224) :
      Apart a 24 (s.getReg .x2 - 1488) 8 ∧ Apart a 24 (s.getReg .x2 - 1344) 8 ∧
        Apart a 24 (s.getReg .x2 - 928) 40 := by
    rcases ha with rfl | rfl <;> simp only [Apart] <;> refine ⟨?_, ?_, ?_⟩ <;> addr_omega [hb1]
  obtain ⟨t₁, hrt₁, hd₁ | ⟨hpct₁, hp₁, B₂, hv₂, mono₂, ⟨w₂, fr₂, hw₂⟩, fk₂, hk₂, ok₂, val₂, foot₂⟩⟩ :=
    extCall hE hpre (b80002e94_pc h₁) B₁ (hdr := s.getReg .x2 - 416) (by addr_omega [hb1])
      (by addr_omega [hb1]) (by addr_omega [hb1, hb3]) (hap _ (Or.inl rfl))
      (by rw [b80002e94_x10 h₁, e2240]) (by rw [b80002e94_x11 h₁, e1728]) V₁.push
      (fun x hx ↦ V₁.fresh x (Or.inl hx)) T₁.ok.push (hVlo 24 _ fun x hx ↦ Or.inl hx) ht80
      c0 c8 c16 c24 c32
  · exact ⟨t₁, hr₁.trans hrt₁, Or.inl hd₁⟩
  have V₂ := V₁.withPush hpre hv₁ hv₂ mono₂ B₁.loLe fr₂ hw₂ ok₂ (by rw [val₂, V₁.pushV]) foot₂
  -- back in `walk`
  have k₁₂ (r : Reg) (hr : r ∈ calleeSaved) (hr' : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x14,
      .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg)) :
      t₁.getReg r = u.getReg r := by rw [hp₁ r hr, k₁ r hr']
  have sp₂ : t₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁₂ .x2 (by decide) (by decide)]; exact sp
  have x22₂ : t₁.getReg .x22 = tbl := by rw [hp₁ .x22 (by decide), b80002e94_x22 h₁, eX]
  have pc₂ : t₁.pc = 0x80002f0c := by rw [hpct₁, returnAddress_eq, b80002e94_x1 h₁]; decide
  have hn₂ := B₂.loLe
  have hhi₂ := hv₂.hi
  simp only [heapEnd] at hhi₂
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80002f0c_spec pc₂ (by
    rv_eval [sp₂, x22₂]
    simp only [Sym.validAccess_eight]
    and_intros <;> addr_omega [hb1, hb2, hb3, htN, hB, hn₂, hhi₂, hi])
  have f1728 : t₁.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fr₃ : MemFrame t₁ u₃ (s.getReg .x2 - 928) 40 := by
    rw [← f1728]; exact b80002f0c_frame h₃ (by rw [sp₂]; addr_omega [hb1])
  have k₃ := b80002f0c_keeps h₃
  have m₃ (a : Word) (ha : ¬ Within a (s.getReg .x2 - 928) 40) : u₃.getMem a = t₁.getMem a := fr₃ a ha
  have hn₃ : heapNext u₃ = heapNext t₁ := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (m₃ _ (by simp only [Within, nextAddr]; addr_omega [hb1]))
  have hv₃ : HeapOk u₃ := ⟨hn₃ ▸ hv₂.lo, hn₃ ▸ hv₂.hi⟩
  have frw₃ : ∀ x, Within x (s.getReg .x2 - 928) 40 → (s.getReg .x2 - 2656).toNat ≤ x.toNat ∧
      x.toNat < (s.getReg .x2 - 104).toNat ∧ ¬ Within x (s.getReg .x2 - 512) 24 ∧
      ¬ Within x (s.getReg .x2 - 416) 24 ∧ ¬ Within x (s.getReg .x2 - 224) 24 := fun x hx ↦ by
    simp only [Within] at hx ⊢
    refine ⟨by addr_omega [hx, hb1], by addr_omega [hx, hb1], by addr_omega [hx, hb1],
      by addr_omega [hx, hb1], by addr_omega [hx, hb1]⟩
  have B₃ : Base10 OI s u₃ A k R Q B lo := B₂.keep hpre (MemFrame.dframe fr₃) (fun x hx ↦ by
      have := frw₃ x hx
      simp only [Within] at hx
      exact Or.inl (Or.inl ⟨by addr_omega [hx, hb1], this.2.1⟩)) hv₃ hn₃.ge (k₃ .x2 (by decide))
  have V₃ := V₂.keepFrame hpre hv₂ hn₃.ge (MemFrame.dframe fr₃) frw₃
  have T₃ := B₃.tables i tb htb
  rw [← htbl] at T₃
  have e24_24 : tbl + 24 + 24 = tbl + 48 := by rw [BitVec.add_assoc]; rfl
  have e48_8 : tbl + 48 + 8 = tbl + 56 := by rw [BitVec.add_assoc]; rfl
  have e48_16 : tbl + 48 + 16 = tbl + 64 := by rw [BitVec.add_assoc]; rfl
  have hw56 : u₃.getMem (tbl + 56) = t₁.getMem (tbl + 56) :=
    m₃ _ (by simp only [Within]; addr_omega [htN, hB, hl, hhi, hb1, hi])
  have hw64 : u₃.getMem (tbl + 64) = t₁.getMem (tbl + 64) :=
    m₃ _ (by simp only [Within]; addr_omega [htN, hB, hl, hhi, hb1, hi])
  have f1736 : t₁.getReg .x2 + 1736 = s.getReg .x2 - 920 := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have f1744 : t₁.getReg .x2 + 1744 = s.getReg .x2 - 912 := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have f1752 : t₁.getReg .x2 + 1752 = s.getReg .x2 - 904 := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have f1760 : t₁.getReg .x2 + 1760 = s.getReg .x2 - 896 := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have d0 : u₃.getMem (s.getReg .x2 - 928) = vecPtr u₃ (tbl + 48) := by
    rw [← f1728, b80002f0c_m_x2_1728 h₃, x22₂, vecPtr, e48_8, hw56]
  have d8 : u₃.getMem (s.getReg .x2 - 920) =
      vecPtr u₃ (tbl + 48) + BitVec.ofNat 64 (24 * (vecLen u₃ (tbl + 48)).toNat) := by
    rw [← f1736, b80002f0c_m_x2_1736 h₃, x22₂, vecPtr, vecLen, e48_8, e48_16, hw56, hw64, mul24]
  have d16 : u₃.getMem (s.getReg .x2 - 912) = s.getReg .x2 - 1488 := by
    rw [← f1744, b80002f0c_m_x2_1744 h₃, k₁₂ .x18 (by decide) (by decide), h.x18]
  have d24 : u₃.getMem (s.getReg .x2 - 904) = s.getReg .x2 - 1344 := by
    rw [← f1752, b80002f0c_m_x2_1752 h₃, k₁₂ .x19 (by decide) (by decide), h.x19]
  have d32 : u₃.getMem (s.getReg .x2 - 896) = tbl := by
    rw [← f1760, b80002f0c_m_x2_1760 h₃, x22₂]
  have e2432 : t₁.getReg .x2 + 2432 = s.getReg .x2 - 224 := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hpl := T₃.ok.pull
  rw [e24_24] at hpl
  obtain ⟨t₂, hrt₂, hd₂ | ⟨hpct₂, hp₂, B₄, hv₄, mono₄, ⟨w₄, fr₄, hw₄⟩, fk₄, hk₄, ok₄, val₄, foot₄⟩⟩ :=
    extCall hE hpre (b80002f0c_pc h₃) B₃ (hdr := s.getReg .x2 - 224) (by addr_omega [hb1])
      (by addr_omega [hb1]) (by addr_omega [hb1, hb3]) (hap _ (Or.inr rfl))
      (by rw [b80002f0c_x10 h₃, e2432]) (by rw [b80002f0c_x11 h₃, f1728]) V₃.pull
      (fun x hx ↦ V₃.fresh x (Or.inr (Or.inl hx))) hpl (fun x hx ↦ B₃.below i hi x (by
        rw [← htbl]; exact Or.inr (Or.inr (by rw [e24_24]; exact hx)))) ht80
      d0 d8 d16 d24 d32
  · exact ⟨t₂, hr₁.trans (hrt₁.trans (hr₃.trans hrt₂)), Or.inl hd₂⟩
  have V₄ := V₃.withPull hpre hv₃ hv₄ mono₄ B₃.loLe fr₄ hw₄ ok₄ (by rw [val₄, V₃.pullV]) foot₄
  -- the opcode's check
  have k₃₄ (r : Reg) (hr : r ∈ calleeSaved) (hr' : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x13,
      .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29,
      .x30, .x31] : List Reg)) : t₂.getReg r = t₁.getReg r := by rw [hp₂ r hr, k₃ r hr']
  have sp₄ : t₂.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₃₄ .x2 (by decide) (by decide)]; exact sp₂
  have x22₄ : t₂.getReg .x22 = tbl := by rw [k₃₄ .x22 (by decide) (by decide)]; exact x22₂
  have pc₄ : t₂.pc = 0x80002f4c := by rw [hpct₂, returnAddress_eq, b80002f0c_x1 h₃]; decide
  -- heap words below `lo` and the frame's words are as at `u₁`
  have hp4 (x : Word) (h1 : 0x20000000 ≤ x.toNat) (h2 : x.toNat + 8 ≤ lo) :
      t₂.getMem x = u.getMem x := by
    rw [hk₄ x h1 h2, m₃ x (by simp only [Within]; addr_omega [h1, h2, hb1, hl, hhi]), hk₂ x h1 h2,
      m₁ x (by simp only [Within]; addr_omega [h1, h2, hb1, hl, hhi])]
  have fw4 (x : Word) (h1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (s.getReg .x2 - 104).toNat) (h3 : Apart x 8 (s.getReg .x2 - 416) 24)
      (h4 : Apart x 8 (s.getReg .x2 - 224) 24) (h5 : Apart x 8 (s.getReg .x2 - 928) 40) :
      t₂.getMem x = u₁.getMem x := by
    rw [fk₄ x h1 h2 h4, m₃ x (by simp only [Within, Apart] at h5 ⊢; addr_omega [h5, hb1]),
      fk₂ x h1 h2 h3]
  have op72 : t₂.getMem (tbl + 72) = BitVec.ofNat 64 i := by
    rw [hp4 _ (by addr_omega [htN, ht80, hl, hhi]) (by addr_omega [htN, ht80, hl, hhi]), htbl]
    exact opAt H h.op5 hi
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80002f4c_spec pc₄ (by
    rv_eval [x22₄]
    simp only [Sym.validAccess_eight]
    addr_omega [htN, ht80, hl, hhi])
  have pc₅ := b80002f4c_pc_taken h₅ (by
    rw [x22₄, op72]; simp only [BitVec.toNat_ofNat]; have : (6 : Word).toNat = 6 := rfl; omega)
  have m₅ := b80002f4c_mem_same h₅
  have k₅ := b80002f4c_keeps h₅
  have hn₅ : heapNext u₅ = heapNext t₂ := by simp only [heapNext, m₅]
  -- the blocks
  have hH := heightsLe H.ok i
  have opU1 : u₁.getMem (tbl + 72) = BitVec.ofNat 64 i := by
    rw [m₁ _ (by simp only [Within]; addr_omega [htN, ht80, hl, hhi, hb1]), htbl]
    exact opAt H h.op5 hi
  have opU3 : u₃.getMem (tbl + 72) = BitVec.ofNat 64 i := by
    rw [m₃ _ (by simp only [Within]; addr_omega [htN, ht80, hl, hhi, hb1]),
      hk₂ _ (by addr_omega [htN, ht80, hl, hhi]) (by addr_omega [htN, ht80, hl, hhi])]
    exact opU1
  have fA (x : Word) (h1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (s.getReg .x2 - 104).toNat) (h3 : Apart x 8 (s.getReg .x2 - 416) 24)
      (h5 : Apart x 8 (s.getReg .x2 - 928) 40) : u₃.getMem x = u₁.getMem x := by
    rw [m₃ x (by simp only [Within, Apart] at h5 ⊢; addr_omega [h5, hb1]), fk₂ x h1 h2 h3]
  have mH3 : u₃.getMem (s.getReg .x2 - 1488) =
      BitVec.ofNat 64 ((tableLogHeightsRust (rowsOf A)).getD i 0) := by
    rw [fA _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])
      (by simp only [Apart]; addr_omega [hb1])]; exact mH
  have mR3 : u₃.getMem (s.getReg .x2 - 1344) = (rowsOf A).getD i 0 := by
    rw [fA _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])
      (by simp only [Apart]; addr_omega [hb1])]; exact mR
  have hblk (x : MachineState) (e1 : x.getMem (s.getReg .x2 - 1488) =
      BitVec.ofNat 64 ((tableLogHeightsRust (rowsOf A)).getD i 0))
      (e2 : x.getMem (s.getReg .x2 - 1344) = (rowsOf A).getD i 0)
      (e3 : x.getMem (tbl + 72) = BitVec.ofNat 64 i) :
      (fun co ↦ (⟨(x.getMem (s.getReg .x2 - 1488)).toNat, x.getMem (s.getReg .x2 - 1344), co,
        (x.getMem (tbl + 72)).toNat⟩ : BusBlockRust)) = blkOf A i := by
    funext co
    simp only [e1, e2, e3, blkOf, BitVec.toNat_ofNat]
    congr 1
    · exact Nat.mod_eq_of_lt (by omega)
    · exact Nat.mod_eq_of_lt (by omega)
  have fpush : formVecsOf u₁ (tbl + 24) = tb.flushes.push := congrArg FlushesRust.push T₁.flushes
  have fpull : formVecsOf u₃ (tbl + 48) = tb.flushes.pull := by
    rw [← e24_24]; exact congrArg FlushesRust.pull T₃.flushes
  simp only [fpush, hblk u₁ mH mR opU1, fpull, hblk u₃ mH3 mR3 opU3] at V₄
  have fw5 (x : Word) (h1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (s.getReg .x2 - 104).toNat) (h3 : Apart x 8 (s.getReg .x2 - 416) 24)
      (h4 : Apart x 8 (s.getReg .x2 - 224) 24) (h5 : Apart x 8 (s.getReg .x2 - 928) 40) :
      u₅.getMem x = u₁.getMem x := by rw [m₅]; exact fw4 x h1 h2 h3 h4 h5
  have kreg (r : Reg) (hr : r ∈ calleeSaved) (h1 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x14,
      .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (h2 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14, .x15, .x16, .x17, .x18,
        .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg))
      (h3 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x13, .x14, .x15, .x16, .x17, .x18, .x19,
        .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg)) :
      u₅.getReg r = u.getReg r := by
    rw [k₅ r h2, k₃₄ r hr h3, k₁₂ r hr h1]
  refine ⟨u₅, hr₁.trans (hrt₁.trans (hr₃.trans (hrt₂.trans hr₅))), Or.inr ⟨pc₅, tb, htb, {
    base := B₄.same hpre m₅ (k₅ .x2 (by decide))
    op5 := by
      rw [m₅, hp4 _ (by addr_omega [hB, hs0, hl, hhi]) (by addr_omega [hB, hl, hhi])]; exact h.op5
    vecs := V₄.keepFrame hpre hv₄ hn₅.ge (Layout.DFrame.of_same m₅ (fun _ ↦ False))
      fun _ h ↦ h.elim
    lt := hi
    x9 := by rw [kreg .x9 (by decide) (by decide) (by decide) (by decide)]; exact h.x9
    x18 := by rw [kreg .x18 (by decide) (by decide) (by decide) (by decide)]; exact h.x18
    x19 := by rw [kreg .x19 (by decide) (by decide) (by decide) (by decide)]; exact h.x19
    x10 := by rw [b80002f4c_x10 h₅, x22₄, op72]
    x20 := by rw [kreg .x20 (by decide) (by decide) (by decide) (by decide)]; exact h.x20
    x21 := by rw [kreg .x21 (by decide) (by decide) (by decide) (by decide)]; exact h.x21
    x22 := by rw [k₅ .x22 (by decide), x22₄, htbl]
    n := by
      rw [fw5 _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])
        (by simp only [Apart]; addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1]),
        m₁ _ (by simp only [Within]; addr_omega [hb1])]
      exact h.n
    hgt := by
      rw [fw5 _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])
        (by simp only [Apart]; addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])]
      exact mH
    row := by
      rw [fw5 _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])
        (by simp only [Apart]; addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])]
      exact mR }⟩⟩

end Rv64Verifier.Proofs.Walk
