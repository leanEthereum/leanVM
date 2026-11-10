import Rv64Verifier.Proofs.Walk.R6C

/-!
# `walk`: a cell's `memory_if` flush, its state

Side 1's cells 1..12 flush `memory_if(flag, prod(fp, o_out, cell), count, &values)`: the counter
`col(count, 0) + prod(flag, count, 1) + prod(flag, count, 0)` is built at `sp + 1096`, moved to
`sp + 1024` and `sp + 952`; `s2`, `s9` and `s10` are reused meanwhile, so the loop's registers are
`IR` and the values' state `IS`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FormOk formOf formBuf flushesDeep OptAt)

/-- `memory_if`'s flag column: `OUT_TWO` for cell 1, `OUT_ALL` past it. -/
def flagOf (c : Nat) : Nat := if c = 1 then 12 else 13

/-- The loop's registers that side 1's `memory_if` path keeps. -/
structure IR (s u : MachineState) (c : Nat) : Prop where
  x8 : u.getReg .x8 = s.getReg .x2 - 200
  x9 : u.getReg .x9 = s.getReg .x2 - 912 + BitVec.ofNat 64 (32 * c)
  x19 : u.getReg .x19 = s.getReg .x2 - 1328 + BitVec.ofNat 64 (32 * c)
  x20 : u.getReg .x20 = s.getReg .x2 - 176
  x21 : u.getReg .x21 = BitVec.ofNat 64 (65 + 13 * 1)
  x22 : u.getReg .x22 = 0xa00001b8 + BitVec.ofNat 64 (8 * c)
  x23 : u.getReg .x23 = BitVec.ofNat 64 c
  x24 : u.getReg .x24 = BitVec.ofNat 64 (65 + 13 * 1 + c)
  x27 : u.getReg .x27 = BitVec.ofNat 64 1

theorem IR.keeps {s u t : MachineState} {c : Nat} {l : List Reg} (h : IR s u c)
    (hk : ∀ r ∈ l, t.getReg r = u.getReg r)
    (hl : ∀ q ∈ ([.x8, .x9, .x19, .x20, .x21, .x22, .x23, .x24, .x27] : List Reg), q ∈ l := by
      decide) : IR s t c :=
  ⟨by rw [hk .x8 (hl _ (by decide))]; exact h.x8, by rw [hk .x9 (hl _ (by decide))]; exact h.x9,
    by rw [hk .x19 (hl _ (by decide))]; exact h.x19, by rw [hk .x20 (hl _ (by decide))]; exact h.x20,
    by rw [hk .x21 (hl _ (by decide))]; exact h.x21, by rw [hk .x22 (hl _ (by decide))]; exact h.x22,
    by rw [hk .x23 (hl _ (by decide))]; exact h.x23, by rw [hk .x24 (hl _ (by decide))]; exact h.x24,
    by rw [hk .x27 (hl _ (by decide))]; exact h.x27⟩

theorem IR.pres {s u t : MachineState} {c : Nat} (h : IR s u c) (hp : Preserves u t) : IR s t c :=
  h.keeps hp

/-- The values' state along the path, the loop's memory state on side 1. -/
structure IS (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) (c : Nat) (F : LayoutMirror.FlushesRust)
    (h0 h1 h2 h3 : Nat) : Prop where
  km : KM OI s u A k R Q B 1 F
  ir : IR s u c
  deep : ∀ x, flushesDeep u (s.getReg .x2 - 1488) x → x.toNat < h0
  v0 : SF u (s.getReg .x2 - 224) (limbForm 1 (LayoutMirror.keccakCellLanesAt false c).1
    (LayoutMirror.keccakCellLanesAt true c).1) h0 h1
  v1 : SF u (s.getReg .x2 - 200) (limbForm 1 (LayoutMirror.keccakCellLanesAt false c).2
    (LayoutMirror.keccakCellLanesAt true c).2) h1 h2
  v2 : SF u (s.getReg .x2 - 176) (LayoutMirror.constantRust 0) h2 h3
  le : h0 ≤ h1 ∧ h1 ≤ h2 ∧ h2 ≤ h3 ∧ h3 ≤ heapNext u
  hB : B ≤ h0

theorem VA.toIS {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {c : Nat} {F : LayoutMirror.FlushesRust}
    {h0 h1 h2 h3 : Nat} (h : VA OI s u A k R Q B 1 c F h0 h1 h2 h3) (hB : B ≤ h0) :
    IS OI s u A k R Q B c F h0 h1 h2 h3 :=
  ⟨h.km, ⟨h.kr.x8, h.kr.x9, h.kr.x19, h.kr.x20, h.kr.x21, h.kr.x22, h.kr.x23, h.x24, h.kr.x27⟩,
    h.deep, h.v0, h.v1, h.v2, h.le, hB⟩

/-- A slot apart from the values array. -/
@[rv_addr] def OffV (s : MachineState) (o : Word) : Prop :=
  InScr s o ∧ InSlot s o 24 ∧
    (o.toNat + 24 ≤ (s.getReg .x2 - 224).toNat ∨ (s.getReg .x2 - 152).toNat ≤ o.toNat)

/-- A callee writing heap from `L` (past the values' buffers), a slot apart from the values array,
its stack, `NEXT` and fresh heap. -/
theorem IS.call {OI : MachineState → Word → List (List Opening) → Prop} {s u t : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {c : Nat} {F : LayoutMirror.FlushesRust}
    {h0 h1 h2 h3 : Nat} {o : Word} {n L : Nat} (hpre : WalkPre s)
    (h : IS OI s u A k R Q B c F h0 h1 h2 h3) (ho : OffV s o)
    (fr : Rv64Verifier.Layout.DFrame u t fun a ↦ Within a o 24 ∨
      (L ≤ a.toNat ∧ a.toNat < heapNext u) ∨ Within a (stackLo u n) n ∨ Within a nextAddr 8 ∨
      Fresh u t a) (hn : n ≤ 8736) (hL : h3 ≤ L) (hL' : L ≤ heapNext u)
    (K : KM OI s t A k R Q B 1 F)
    (D : flushesDeep t (s.getReg .x2 - 1488) = flushesDeep u (s.getReg .x2 - 1488))
    (ir : IR s t c) (hv : HeapOk t) (mono : heapNext u ≤ heapNext t) :
    IS OI s t A k R Q B c F h0 h1 h2 h3 := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  obtain ⟨-, ho', hov⟩ := ho
  have I := h.km.m.inv
  have le := h.le
  have sl (o : Word) (ho : o = s.getReg .x2 - 224 ∨ o = s.getReg .x2 - 200 ∨ o = s.getReg .x2 - 176) :
      InSlot s o 24 := by
    rcases ho with rfl | rfl | rfl <;> simp only [InSlot] <;> addr_omega [hb1, hb3]
  exact {
    km := K
    ir := ir
    deep := fun x hx ↦ h.deep x (by rw [← D]; exact hx)
    v0 := SF.call' hpre I h.v0 fr hn ho' (sl _ (Or.inl rfl)) (by addr_omega [hov, hb1]) (by omega) hL' hv mono
    v1 := SF.call' hpre I h.v1 fr hn ho' (sl _ (Or.inr (Or.inl rfl))) (by addr_omega [hov, hb1]) (by omega)
      hL' hv mono
    v2 := SF.call' hpre I h.v2 fr hn ho' (sl _ (Or.inr (Or.inr rfl))) (by addr_omega [hov, hb1]) hL hL' hv mono
    le := ⟨le.1, le.2.1, le.2.2.1, le_trans le.2.2.2 mono⟩
    hB := h.hB }

/-- `CW`'s frame, as `IS.call` takes it. -/
theorem cw_frame {u t : MachineState} {o : Word} {n : Nat}
    (fr : Rv64Verifier.Layout.DFrame u t (CW u t o n)) :
    Rv64Verifier.Layout.DFrame u t fun a ↦ Within a o 24 ∨
      (heapNext u ≤ a.toNat ∧ a.toNat < heapNext u) ∨ Within a (stackLo u n) n ∨
      Within a nextAddr 8 ∨ Fresh u t a :=
  fr.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ha)))

/-- A block writing only scratch apart from the values array. -/
theorem IS.blk {OI : MachineState → Word → List (List Opening) → Prop} {s u t : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {c : Nat} {F : LayoutMirror.FlushesRust}
    {h0 h1 h2 h3 : Nat} {w : Word → Prop} (hpre : WalkPre s)
    (h : IS OI s u A k R Q B c F h0 h1 h2 h3) (fr : Rv64Verifier.Layout.DFrame u t w)
    (hw : ∀ a, w a → Scr s a ∧ (a.toNat < (s.getReg .x2 - 224).toNat ∨
      (s.getReg .x2 - 152).toNat ≤ a.toNat))
    (ir : IR s t c) (sp : t.getReg .x2 = u.getReg .x2) :
    IS OI s t A k R Q B c F h0 h1 h2 h3 ∧ heapNext t = heapNext u := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have K := KM.scr hpre h.km fr (fun a ha ↦ (hw a ha).1) sp
  have hh := h.km.m.inv.heap
  have le := h.le
  have nb (o : Word) {f : LayoutMirror.FormRust} {lo hi : Nat} (hf : SF u o f lo hi)
      (hlo : o = s.getReg .x2 - 224 ∨ o = s.getReg .x2 - 200 ∨ o = s.getReg .x2 - 176)
      (hhi : hi ≤ heapNext u) : SF t o f lo hi := by
    refine hf.frame fr (fun x hx hwx ↦ ?_) (fun x _ hx hwx ↦ ?_) (by
      rcases hlo with rfl | rfl | rfl <;> addr_omega [hb1]) hh K.2.2.ge
    · have := (hw x hwx).2
      rcases hlo with rfl | rfl | rfl <;> simp only [Within] at hx <;> addr_omega [hx, this, hb1]
    · have hs := (hw x hwx).1
      have hu := hh.hi
      simp only [heapEnd, heapNext] at hu hhi
      simp only [Scr, Within] at hs; rcases hs with c | c | c | c <;> addr_omega [c, hb1, hx, hhi, hu]
  exact ⟨{
    km := K.1
    ir := ir
    deep := fun x hx ↦ h.deep x (by rw [← K.2.1]; exact hx)
    v0 := nb _ h.v0 (Or.inl rfl) (by omega)
    v1 := nb _ h.v1 (Or.inr (Or.inl rfl)) (by omega)
    v2 := nb _ h.v2 (Or.inr (Or.inr rfl)) le.2.2.2
    le := by rw [K.2.2]; exact le
    hB := h.hB }, K.2.2⟩

theorem SF.weak {u : MachineState} {o : Word} {f : LayoutMirror.FormRust} {lo hi lo' hi' : Nat}
    (h : SF u o f lo hi) (h1 : lo' ≤ lo) (h2 : hi ≤ hi') : SF u o f lo' hi' :=
  ⟨h.ok, h.val, fun x hx ↦ ⟨le_trans h1 (h.buf x hx).1, lt_of_lt_of_le (h.buf x hx).2 h2⟩⟩

theorem len_one {u : MachineState} {o : Word} (h : (formOf u o).terms.length = 1) :
    (vecLen u o).toNat = 1 := by
  simpa only [formOf, Rv64Verifier.Layout.termsOf_length] using h

/-- At `0x80001c58`, `add_scaled`'s first call: the address `prod(fp, o_out, cell)` at
`sp + 2312`, `col(count, 0)` at `sp + 1096`, `prod(flag, count, 1)` at `sp + 2240`. -/
structure I1 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) (c : Nat) (F : LayoutMirror.FlushesRust)
    (h0 h1 h2 h3 h4 h5 h6 : Nat) : Prop where
  is : IS OI s u A k R Q B c F h0 h1 h2 h3
  x25 : u.getReg .x25 = BitVec.ofNat 64 (flagOf c)
  x26 : u.getReg .x26 = s.getReg .x2 - 512
  addr : SF u (s.getReg .x2 - 344) (LayoutMirror.prodRust 1 9 c) h3 h4
  col : SF u (s.getReg .x2 - 1560) (LayoutMirror.colRust (65 + 13 * 1 + c) 0) h4 h5
  p1 : SF u (s.getReg .x2 - 416) (LayoutMirror.prodRust (flagOf c) (65 + 13 * 1 + c) 1) h5 h6
  le : h3 ≤ h4 ∧ h4 ≤ h5 ∧ h5 ≤ h6 ∧ h6 ≤ heapNext u

theorem offV_of {s : MachineState} (hpre : WalkPre s) {o : Word}
    (ho : o = s.getReg .x2 - 344 ∨ o = s.getReg .x2 - 1560 ∨ o = s.getReg .x2 - 416 ∨
      o = s.getReg .x2 - 1632 ∨ o = s.getReg .x2 - 1704) : OffV s o := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  refine ⟨fun x hx ↦ ?_, ?_, ?_⟩
  · rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [Within, Scr] at hx ⊢ <;> addr_omega [hx, hb1]
  · rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [InSlot] <;> addr_omega [hb1, hb3]
  · rcases ho with rfl | rfl | rfl | rfl | rfl <;> addr_omega [hb1]

theorem toNat_small {x : Word} {n : Nat} (hx : x = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    x.toNat = n := by
  rw [hx, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn

set_option maxRecDepth 8192 in
/-- From the side branch (`0x80001e40`, side 1, cell `c ≥ 1`) to `add_scaled`'s first call. -/
theorem toI1 (hP : Rv64Verifier.Layout.ProdSpec) (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {c : Nat} {F : LayoutMirror.FlushesRust}
    {h0 h1 h2 h3 : Nat} (hpre : WalkPre s) (h : VA OI s u A k R Q B 1 c F h0 h1 h2 h3)
    (hB : B ≤ h0) (hc : c < 13) (hc1 : 1 ≤ c) (hpc : u.pc = 0x80001e40) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001c58 ∧ ∃ h4 h5 h6,
      I1 OI s t A k R Q B c F h0 h1 h2 h3 h4 h5 h6) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have x23 := h.kr.x23
  have c23 : (u.getReg .x23).toNat = c := toNat_small x23 (by omega)
  obtain ⟨v₁, r₁, g₁⟩ := Sym.BlockSpec.reaches b80001e40_spec hpc (by rv_eval [])
  have k₁ := b80001e40_keeps g₁
  have m₁ := b80001e40_mem_same g₁
  obtain ⟨v₂, r₂, g₂⟩ := Sym.BlockSpec.reaches b80001e44_spec
    (b80001e40_pc_not_taken g₁ (by
      intro he; have := congrArg BitVec.toNat he; rw [c23] at this
      have h0' : (0 : Word).toNat = 0 := rfl; omega)) (by rv_eval [])
  have k₂ := b80001e44_keeps g₂
  have m₂ := b80001e44_mem_same g₂
  have x23₁ : v₁.getReg .x23 = BitVec.ofNat 64 c := by rw [k₁ .x23 (by decide)]; exact x23
  -- to `0x80001c0c`, `s9` = the flag
  have reach : ∃ v, Reaches Image.code u v ∧ v.pc = 0x80001c0c ∧
      (∀ a, v.getMem a = u.getMem a) ∧ v.getReg .x25 = BitVec.ofNat 64 (flagOf c) ∧
      ∀ r ∈ ([.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x26, .x27] : List Reg),
        v.getReg r = u.getReg r := by
    by_cases h1 : c = 1
    · obtain ⟨v₃, r₃, g₃⟩ := Sym.BlockSpec.reaches b80001e4c_spec
        (b80001e44_pc_not_taken g₂ (by rw [x23₁, h1]; rfl)) (by rv_eval [])
      refine ⟨v₃, r₁.trans (r₂.trans r₃), b80001e4c_pc g₃, fun a ↦ by
        rw [b80001e4c_mem_same g₃, m₂, m₁], by rw [b80001e4c_x25 g₃]; simp only [flagOf, h1, ↓reduceIte]; rfl,
        fun r hr ↦ ?_⟩
      have k₃ := b80001e4c_keeps g₃
      rw [k₃ r (by revert r hr; decide), k₂ r (by revert r hr; decide), k₁ r (by revert r hr; decide)]
    · obtain ⟨v₃, r₃, g₃⟩ := Sym.BlockSpec.reaches b80001c08_spec
        (b80001e44_pc_taken g₂ (by
          rw [x23₁]; intro he; have := congrArg BitVec.toNat he
          rw [BitVec.toNat_ofNat] at this; have h1' : (1 : Word).toNat = 1 := rfl; omega))
        (by rv_eval [])
      refine ⟨v₃, r₁.trans (r₂.trans r₃), b80001c08_pc g₃, fun a ↦ by
        rw [b80001c08_mem_same g₃, m₂, m₁], by rw [b80001c08_x25 g₃]; simp only [flagOf, h1, ↓reduceIte]; rfl,
        fun r hr ↦ ?_⟩
      have k₃ := b80001c08_keeps g₃
      rw [k₃ r (by revert r hr; decide), k₂ r (by revert r hr; decide), k₁ r (by revert r hr; decide)]
  obtain ⟨v, rv, pv, mv, x25v, kv⟩ := reach
  have S₀ := ((h.toIS hB).blk hpre (Rv64Verifier.Layout.DFrame.of_same mv (fun _ ↦ False)) (fun _ h ↦ h.elim)
    ((h.toIS hB).ir.keeps kv) (kv .x2 (by decide))).1
  have sp : v.getReg .x2 = s.getReg .x2 - 2656 := S₀.km.m.inv.sp
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : v.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have x26v : v.getReg .x26 = s.getReg .x2 - 512 := by rw [kv .x26 (by decide)]; exact h.kr.x26
  -- `prod(fp, o_out, cell)` into `sp + 2312`
  obtain ⟨w₁, q₁, g₁'⟩ := Sym.BlockSpec.reaches b80001c0c_spec pv (by rv_eval [])
  have kw₁ := b80001c0c_keeps g₁'
  have S₁ := (S₀.blk hpre (Rv64Verifier.Layout.DFrame.of_same (b80001c0c_mem_same g₁') (fun _ ↦ False))
    (fun _ h ↦ h.elim) (S₀.ir.keeps kw₁) (kw₁ .x2 (by decide))).1
  have oA := offV_of hpre (o := s.getReg .x2 - 344) (Or.inl rfl)
  obtain ⟨t₁, hr₁, ⟨hpc₁, hp₁, K₁, D₁, nf₁, fv₁⟩ | hd⟩ := prodCall hP hpre S₁.km (b80001c0c_pc g₁')
    (by rw [b80001c0c_x10 g₁', e 2312 344 (by decide)]) oA.1 oA.2.1
  swap
  · exact ⟨t₁, rv.trans (q₁.trans hr₁), Or.inr hd⟩
  have R₁ := rv.trans (q₁.trans hr₁)
  rw [b80001c0c_x11 g₁', b80001c0c_x12 g₁', b80001c0c_x13 g₁', S₀.ir.x23,
    toNat_small (x := BitVec.ofNat 64 c) rfl (by omega)] at fv₁
  have T₁ := S₁.call hpre oA (cw_frame nf₁.frame) (by decide) S₁.le.2.2.2 le_rfl K₁ D₁ (S₁.ir.pres hp₁)
    nf₁.heap nf₁.mono
  have A₁ := SF.ofNew nf₁ fv₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := K₁.m.inv.sp
  have e₁ (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t₁.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp₁ hNM
  -- `col(count, 0)` into `sp + 1096`
  obtain ⟨w₂, q₂, g₂'⟩ := Sym.BlockSpec.reaches b80001c28_spec
    (by rw [hpc₁, returnAddress_eq, b80001c0c_x1 g₁']; decide) (by rv_eval [])
  have kw₂ := b80001c28_keeps g₂'
  have m₂' := b80001c28_mem_same g₂'
  have S₂ := T₁.blk hpre (Rv64Verifier.Layout.DFrame.of_same m₂' (fun _ ↦ False))
    (fun _ h ↦ h.elim) (T₁.ir.keeps kw₂) (kw₂ .x2 (by decide))
  have I₁ := T₁.km.m.inv
  have hh₁ := nf₁.heap
  have A₂ := A₁.frame (Rv64Verifier.Layout.DFrame.of_same m₂' (fun _ ↦ False)) (fun _ _ h ↦ h)
    (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh₁ S₂.2.ge
  have oC := offV_of hpre (o := s.getReg .x2 - 1560) (Or.inr (Or.inl rfl))
  obtain ⟨t₂, hr₂, ⟨hpc₂, hp₂, K₂, D₂, nf₂, fv₂⟩ | hd⟩ := colCall hC hpre S₂.1.km (b80001c28_pc g₂')
    (by rw [b80001c28_x10 g₂', e₁ 1096 1560 (by decide)]) oC.1 oC.2.1
  swap
  · exact ⟨t₂, R₁.trans (q₂.trans hr₂), Or.inr hd⟩
  have R₂ := R₁.trans (q₂.trans hr₂)
  rw [b80001c28_x11 g₂', b80001c28_x12 g₂', T₁.ir.x24,
    toNat_small (x := BitVec.ofNat 64 (65 + 13 * 1 + c)) rfl (by omega)] at fv₂
  have I₂ := S₂.1.km.m.inv
  have T₂ := S₂.1.call hpre oC (cw_frame nf₂.frame) (by decide) S₂.1.le.2.2.2 le_rfl K₂ D₂
    (S₂.1.ir.pres hp₂) nf₂.heap nf₂.mono
  have C₂ := SF.ofNew nf₂ fv₂
  have A₃ := SF.call hpre I₂ A₂ nf₂.frame (by decide) oC.2.1 oA.2.1 (by addr_omega [hb1])
    (by rw [S₂.2]) nf₂.heap nf₂.mono
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := K₂.m.inv.sp
  have e₂ (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t₂.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp₂ hNM
  -- `prod(flag, count, 1)` into `sp + 2240`
  obtain ⟨w₃, q₃, g₃'⟩ := Sym.BlockSpec.reaches b80001c3c_spec
    (by rw [hpc₂, returnAddress_eq, b80001c28_x1 g₂']; decide) (by rv_eval [])
  have kw₃ := b80001c3c_keeps g₃'
  have m₃' := b80001c3c_mem_same g₃'
  have S₃ := T₂.blk hpre (Rv64Verifier.Layout.DFrame.of_same m₃' (fun _ ↦ False))
    (fun _ h ↦ h.elim) (T₂.ir.keeps kw₃) (kw₃ .x2 (by decide))
  have hh₂ := nf₂.heap
  have A₄ := A₃.frame (Rv64Verifier.Layout.DFrame.of_same m₃' (fun _ ↦ False)) (fun _ _ h ↦ h)
    (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh₂ S₃.2.ge
  have C₄ := C₂.frame (Rv64Verifier.Layout.DFrame.of_same m₃' (fun _ ↦ False)) (fun _ _ h ↦ h)
    (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh₂ S₃.2.ge
  have I₃ := S₃.1.km.m.inv
  have oP := offV_of hpre (o := s.getReg .x2 - 416) (Or.inr (Or.inr (Or.inl rfl)))
  have x25₂ : t₂.getReg .x25 = BitVec.ofNat 64 (flagOf c) := by
    rw [hp₂ .x25 (by decide), kw₂ .x25 (by decide), hp₁ .x25 (by decide), kw₁ .x25 (by decide)]
    exact x25v
  obtain ⟨t₃, hr₃, ⟨hpc₃, hp₃, K₃, D₃, nf₃, fv₃⟩ | hd⟩ := prodCall hP hpre S₃.1.km (b80001c3c_pc g₃')
    (by rw [b80001c3c_x10 g₃', e₂ 2240 416 (by decide)]) oP.1 oP.2.1
  swap
  · exact ⟨t₃, R₂.trans (q₃.trans hr₃), Or.inr hd⟩
  have R₃ := R₂.trans (q₃.trans hr₃)
  have hf13 : flagOf c < 2 ^ 64 := by unfold flagOf; split_ifs <;> omega
  rw [b80001c3c_x11 g₃', b80001c3c_x12 g₃', b80001c3c_x13 g₃', x25₂, T₂.ir.x24,
    toNat_small (x := BitVec.ofNat 64 (flagOf c)) rfl hf13,
    toNat_small (x := BitVec.ofNat 64 (65 + 13 * 1 + c)) rfl (by omega)] at fv₃
  have T₃ := S₃.1.call hpre oP (cw_frame nf₃.frame) (by decide) S₃.1.le.2.2.2 le_rfl K₃ D₃
    (S₃.1.ir.pres hp₃) nf₃.heap nf₃.mono
  have P₃ := SF.ofNew nf₃ fv₃
  have A₅ := SF.call hpre I₃ A₄ nf₃.frame (by decide) oP.2.1 oA.2.1 (by addr_omega [hb1])
    (by have := nf₂.mono; have := S₂.2; have := S₃.2; omega) nf₃.heap nf₃.mono
  have C₅ := SF.call hpre I₃ C₄ nf₃.frame (by decide) oP.2.1 oC.2.1 (by addr_omega [hb1])
    (by rw [S₃.2]) nf₃.heap nf₃.mono
  have x26₃ : t₃.getReg .x26 = s.getReg .x2 - 512 := by
    rw [hp₃ .x26 (by decide), kw₃ .x26 (by decide), hp₂ .x26 (by decide), kw₂ .x26 (by decide),
      hp₁ .x26 (by decide), kw₁ .x26 (by decide)]
    exact x26v
  have x25₃ : t₃.getReg .x25 = BitVec.ofNat 64 (flagOf c) := by
    rw [hp₃ .x25 (by decide), kw₃ .x25 (by decide)]; exact x25₂
  have hS₁ := S₁.le.2.2.2
  have hm₁ := nf₁.mono
  have hm₂ := nf₂.mono
  have hm₃ := nf₃.mono
  have e₂' := S₂.2
  have e₃' := S₃.2
  refine ⟨t₃, R₃, Or.inl ⟨by rw [hpc₃, returnAddress_eq, b80001c3c_x1 g₃']; decide,
    heapNext t₁, heapNext t₂, heapNext t₃, {
      is := T₃
      x25 := x25₃
      x26 := x26₃
      addr := A₅.weak hS₁ le_rfl
      col := by rw [e₂'] at C₅; exact C₅
      p1 := by rw [e₃'] at P₃; exact P₃
      le := ⟨by omega, by omega, by omega, le_rfl⟩ }⟩⟩

end Rv64Verifier.Proofs.Walk
