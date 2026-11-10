import Rv64Verifier.Proofs.Walk.R7B
import Rv64Verifier.Proofs.Walk.AtR10
import Rv64Verifier.Proofs.Bus.Repr

/-!
# `walk`: `tables()`, KECCAK's padding loop (R7)

From `0x80001fbc`: `padding[KECCAK_OUT..].iter_mut().zip(output)` writes `E::new(lane)` for the 25
lanes of `keccak_f` of zeros (`loop`), then `alloc(8, 480)` for the six tables, to `0x80002024`.
There the KECCAK `Table` (padding at `sp + 952`, `Flushes` at `sp + 976`) is the first finished
table of `M8`, the state the other five tables are built in.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4

open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep)

/-! ## The padding, as a list -/

theorem set_getD {xs : List E} {j i : Nat} {v : E} :
    (xs.set j v).getD i 0 = if i = j ∧ j < xs.length then v else xs.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = i
  · subst h
    by_cases hl : j < xs.length
    · simp [hl]
    · simp [hl]
  · simp [h, Ne.symm h]

theorem foldl_set_length (f : Nat → E) (c : Nat) (xs : List E) (m : Nat) :
    ((List.range m).foldl (fun p l ↦ p.set (c + l) (f l)) xs).length = xs.length := by
  induction m with
  | zero => rfl
  | succ m ihm => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_set, ihm]

theorem foldl_set_getD (f : Nat → E) (c : Nat) (xs : List E) (n i : Nat) :
    ((List.range n).foldl (fun p l ↦ p.set (c + l) (f l)) xs).getD i 0 =
      if c ≤ i ∧ i < c + n ∧ i < xs.length then f (i - c) else xs.getD i 0 := by
  induction n with
  | zero => simp only [List.range_zero, List.foldl_nil]; split <;> first | rfl | omega
  | succ n ih =>
    have hl := foldl_set_length f c xs
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, set_getD, hl, ih]
    by_cases h1 : i = c + n
    · subst h1; simp only [true_and, Nat.add_sub_cancel_left]
      by_cases h2 : c + n < xs.length
      · simp [h2]
      · simp only [h2, and_false, ↓reduceIte]
    · simp only [h1, false_and, ↓reduceIte]
      split <;> split <;> first | rfl | omega

/-- The KECCAK table's padding row, as `tables()` builds it. -/
def kPad : List E :=
  (List.range (min ((List.replicate (LayoutMirror.tableWidthsRust.getD LayoutMirror.opKeccakRust 0) (0 : E)).length - LayoutMirror.keccakOutRust)
    (LayoutMirror.keccakFRust (List.replicate LayoutMirror.stateLanesRust 0#64)).length)).foldl
    (fun padding l ↦ padding.set (LayoutMirror.keccakOutRust + l)
      (eNew ((LayoutMirror.keccakFRust (List.replicate LayoutMirror.stateLanesRust 0#64)).getD l 0)))
    (List.replicate (LayoutMirror.tableWidthsRust.getD LayoutMirror.opKeccakRust 0) 0)

/-- The KECCAK `Table`. -/
def kTable : LayoutMirror.TableRust := ⟨LayoutMirror.opKeccakRust, kPad, LayoutMirror.flushesKeccakRust⟩

theorem tablesRust_five : LayoutMirror.tablesRust[5]? = some kTable := rfl

/-- The `i`-th element of the padding after `l` lanes. -/
def padE (l i : Nat) : E :=
  if 40 ≤ i ∧ i < 40 + l then eNew ((LayoutMirror.keccakFRust (List.replicate 25 0#64)).getD (i - 40) 0) else 0

theorem kPad_getD (i : Nat) (hi : i < 92) : kPad.getD i 0 = padE 25 i := by
  have hw : LayoutMirror.tableWidthsRust.getD LayoutMirror.opKeccakRust 0 = 92 := by decide +kernel
  have hl : (LayoutMirror.keccakFRust (List.replicate LayoutMirror.stateLanesRust 0#64)).length = 25 := by
    rw [show LayoutMirror.stateLanesRust = 25 from rfl, LayoutMirror.keccakFRust_zero]; simp
  unfold kPad
  rw [hw, hl, foldl_set_getD]
  simp only [List.length_replicate, show LayoutMirror.keccakOutRust = 40 from rfl, show LayoutMirror.stateLanesRust = 25 from rfl,
    padE]
  have hz : (List.replicate 92 (0 : E)).getD i 0 = 0 := by
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_replicate]; omega), List.getElem_replicate]
  rw [hz]
  split <;> split <;> first | rfl | omega

theorem kPad_length : kPad.length = 92 := by
  have hw : LayoutMirror.tableWidthsRust.getD LayoutMirror.opKeccakRust 0 = 92 := by decide +kernel
  unfold kPad
  rw [foldl_set_length, List.length_replicate, hw]

/-! ## A `Vec` header -/

/-- The `Vec<E>` at `o` of length `n`, its buffer `P` allocated past `L`. -/
structure HVec (u : MachineState) (o : Word) (n : Nat) (P : Word) (L : Nat) : Prop where
  vec : VecOk u o 24 8
  ptr : vecPtr u o = P
  len : vecLen u o = BitVec.ofNat 64 n
  buf : P.toNat % 8 = 0 ∧ L ≤ P.toNat ∧ P.toNat + 24 * n ≤ heapNext u

theorem ZVec.h {u : MachineState} {o P : Word} {n L : Nat} (z : ZVec u o n P L) : HVec u o n P L :=
  ⟨z.vec, z.ptr, z.len, z.buf⟩

theorem HVec.frame {u v : MachineState} {o P : Word} {n L : Nat} {w : Word → Prop}
    (h : HVec u o n P L) (fr : Rv64Verifier.Layout.DFrame u v w)
    (hh : ∀ x, Within x o 24 → ¬ w x) (ho : o.toNat + 24 ≤ 2 ^ 64) (hn : heapNext u ≤ heapNext v) :
    HVec v o n P L := by
  have h0 := fr o (fun x hx ↦ hh x (by simp only [Within] at hx ⊢; addr_omega [hx, ho])) (by omega)
  have h8 := fr (o + 8) (fun x hx ↦ hh x (by simp only [Within] at hx ⊢; addr_omega [hx, ho]))
    (by addr_omega [ho])
  have h16 := fr (o + 16) (fun x hx ↦ hh x (by simp only [Within] at hx ⊢; addr_omega [hx, ho]))
    (by addr_omega [ho])
  have hp := h.ptr
  have hl := h.len
  simp only [vecPtr, vecLen] at hp hl
  exact ⟨vecOk_move h0 h8 h16 hn h.vec, by simp only [vecPtr, h8, hp], by simp only [vecLen, h16, hl],
    ⟨h.buf.1, h.buf.2.1, by have := h.buf.2.2; omega⟩⟩

/-! ## The loop -/

/-- At the padding loop's head after `l` lanes. -/
structure LP (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B D : Nat) (P : Word) (l : Nat) : Prop where
  k7 : K7 OI s u A k R Q B D
  hv : HVec u (s.getReg .x2 - 1704) 92 P D
  lanes : LanesAt u (s.getReg .x2 - 896)
  pad : ∀ i < 92, eAt u (P + BitVec.ofNat 64 (24 * i)) = padE l i

/-- The loop's registers at its head after `l` lanes. -/
structure LR (s u : MachineState) (P : Word) (l : Nat) : Prop where
  x8 : u.getReg .x8 = P + 2208
  x10 : u.getReg .x10 = P + BitVec.ofNat 64 (960 + 24 * l)
  x11 : u.getReg .x11 = BitVec.ofNat 64 (26 - l)
  x23 : u.getReg .x23 = s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * l)

set_option maxRecDepth 8192 in
/-- One lane: the head and the body. -/
theorem lane {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B D : Nat} {P : Word} {l : Nat} (hpre : WalkPre s)
    (h : LP OI s u A k R Q B D P l) (r : LR s u P l) (hl : l < 25) (hpc : u.pc = 0x80001fe0) :
    ∃ t, Reaches Image.code u t ∧ t.pc = 0x80001fe0 ∧ LP OI s t A k R Q B D P (l + 1) ∧
      LR s t P (l + 1) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hu := h.k7.m.inv.heap.hi
  have hb := h.hv.buf
  simp only [heapEnd] at hu
  have hB := h.k7.m.bufQ.2.2.2
  have hD := h.k7.buf.2
  have hBD := h.k7.buf.1
  obtain ⟨u₁, r₁, g₁⟩ := Sym.BlockSpec.reaches b80001fe0_spec hpc trivial
  have k₁ := b80001fe0_keeps g₁
  have m₁ := b80001fe0_mem_same g₁
  have p₁ := b80001fe0_pc_not_taken g₁ (by
    rw [r.x11]; intro he; have := congrArg BitVec.toNat he; addr_omega [this, hl])
  have x10₁ : u₁.getReg .x10 = P + BitVec.ofNat 64 (960 + 24 * l) := (k₁ .x10 (by decide)).trans r.x10
  have x23₁ : u₁.getReg .x23 = s.getReg .x2 - 896 + BitVec.ofNat 64 (8 * l) :=
    (k₁ .x23 (by decide)).trans r.x23
  have hmap : Mapped P 2208 := Or.inl ⟨by have := h.k7.m.bufQ.2.2.1; omega, by omega⟩
  obtain ⟨t, r₂, g₂⟩ := Sym.BlockSpec.reaches b80001fe8_spec p₁ (by
    rv_eval [x10₁, x23₁]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals first
      | exact hmap.valid8 (by addr_omega [hb, hl]) (by addr_omega [hb, hl]) (by addr_omega [hb, hl])
      | valid_access hval [hb1, hl])
  have fr₂ : Rv64Verifier.Layout.DFrame u₁ t fun x ↦ Within x (P + BitVec.ofNat 64 (960 + 24 * l)) 24 :=
    Expect.ldframe g₂ (by
      rv_eval [x10₁, x23₁]
      simp only [Within]
      and_intros <;> addr_omega [hb, hl])
  have fr : Rv64Verifier.Layout.DFrame u t fun x ↦ Within x (P + BitVec.ofNat 64 (960 + 24 * l)) 24 :=
    fun a ha hw ↦ (fr₂ a ha hw).trans (m₁ a)
  have hn : heapNext t = heapNext u := by
    simp only [heapNext]; rw [fr _ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb, hl, hu])
      (by decide)]
  have k₂ := b80001fe8_keeps g₂
  have K := h.k7.step hpre fr (fun a ha ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by
      simp only [Within] at ha; addr_omega [ha, hb, hl, hB, hD, hBD], by
      rw [hn]; simp only [Within] at ha; addr_omega [ha, hb, hl]⟩)))))
    (fun a ha ↦ by
      simp only [K7W, Within] at ha ⊢
      refine ⟨Or.inr ?_, ?_, ?_, ?_⟩ <;> addr_omega [ha, hb, hl, hb1, hu])
    ⟨hn ▸ h.k7.m.inv.heap.lo, hn ▸ h.k7.m.inv.heap.hi⟩ hn.ge ((k₂ .x2 (by decide)).trans (k₁ .x2 (by decide)))
  have keep (y : Word) (hy : y.toNat + 8 ≤ (P + BitVec.ofNat 64 (960 + 24 * l)).toNat ∨
      ((P + BitVec.ofNat 64 (960 + 24 * l)).toNat + 24 ≤ y.toNat ∧ y.toNat + 8 ≤ 2 ^ 64)) :
      t.getMem y = u.getMem y :=
    fr y (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hy]) (by
      rcases hy with hy | hy <;> addr_omega [hy, hb, hl, hu])
  have lane₂ : t.getMem (P + BitVec.ofNat 64 (960 + 24 * l)) =
      (LayoutMirror.keccakFRust (List.replicate 25 0#64)).getD l 0 := by
    rw [← x10₁, b80001fe8_m_x10_0 g₂, x23₁, m₁]; exact h.lanes l hl
  refine ⟨t, r₁.trans r₂, ?_, ⟨K, h.hv.frame fr (fun x hx hw ↦ by
      simp only [Within] at hx hw; addr_omega [hx, hw, hb, hl, hb1, hu]) (by addr_omega [hb1]) hn.ge,
    fun j hj ↦ by rw [keep _ (by addr_omega [hb, hl, hb1, hj, hu])]; exact h.lanes j hj,
    fun i hi ↦ ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact b80001fe8_pc_taken g₂ (by
      rw [x10₁, k₁ .x8 (by decide), r.x8]; intro he
      have := congrArg BitVec.toNat he
      addr_omega [this, hb, hl, hu])
  · by_cases hil : i = 40 + l
    · subst hil
      have e1 : P + BitVec.ofNat 64 (24 * (40 + l)) = P + BitVec.ofNat 64 (960 + 24 * l) := by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb, hl]
      rw [e1, Bus.eAt_const lane₂ (by
          rw [← x10₁, b80001fe8_m_x10_8 g₂]) (by rw [← x10₁, b80001fe8_m_x10_16 g₂])]
      simp only [padE, show 40 ≤ 40 + l by omega, show 40 + l < 40 + (l + 1) by omega, and_self,
        ↓reduceIte, Nat.add_sub_cancel_left]
    · have hne : (P + BitVec.ofNat 64 (24 * i)).toNat + 24 ≤ (P + BitVec.ofNat 64 (960 + 24 * l)).toNat ∨
          (P + BitVec.ofNat 64 (960 + 24 * l)).toNat + 24 ≤ (P + BitVec.ofNat 64 (24 * i)).toNat := by
        addr_omega [hb, hl, hi, hil]
      rw [eAt_congr (keep _ (by addr_omega [hne, hb, hl, hi])) (keep _ (by addr_omega [hne, hb, hl, hi]))
        (keep _ (by addr_omega [hne, hb, hl, hi])), h.pad i hi]
      simp only [padE]
      split <;> split <;> first | rfl | omega
  · rw [k₂ .x8 (by decide), k₁ .x8 (by decide)]; exact r.x8
  · rw [b80001fe8_x10 g₂, x10₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb, hl]
  · rw [k₂ .x11 (by decide), b80001fe0_x11 g₁, r.x11]
    apply BitVec.eq_of_toNat_eq; addr_omega [hl]
  · rw [b80001fe8_x23 g₂, x23₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hl]

end Rv64Verifier.Proofs.Walk
