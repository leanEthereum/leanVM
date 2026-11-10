import Rv64Verifier.Proofs.Field.Contracts
import Rv64Verifier.Blocks.F61

/-!
# `K::inv`

```rust
pub fn inv(self) -> Self {
    let sq = |mut v: Self, n: u32| { for _ in 0..n { v = v.square(); } v };
    let t1 = self;
    let t2 = sq(t1, 1) * t1;
    ...
    let t63 = sq(t60, 3) * t3;
    sq(t63, 1)
}
```

compiled at `0x8000d7f4` (`Blocks/F61.lean`) with every loop unrolled: 62 calls to `K::square`
and 9 to `base_mul`, `a0` carrying the running value and `s0`, `s1`, `s2` the `t`s kept for
later products, and a tail call to `K::square` after the epilogue. Each block between two calls
is one of two shapes: `sqShape` (maybe copy `a0` to a saved register, call `K::square`) and
`mulShape` (`a1` = a saved register, call `base_mul`), checked per block by `rfl`; `sqStep` and
`mulStep` are the two shapes' steps over `InvK`, and `chain` strings them together. The value
reached is `Model.kInv`'s, by `rfl`.
-/

namespace Rv64Verifier.Proofs.Field.KInv
open RiscvZkvm.Rv64 Rv64Verifier.FieldContracts Rv64Verifier.Blocks.F61
open Rv64Verifier.Sym (Expect E reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The callee-saved registers `inv` never touches. -/
def kept : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The saved registers `inv` uses. -/
def saved : List Reg := [.x8, .x9, .x18]

/-- Between calls: `a0` the running value, `σ` the saved registers, the frame in place, and
memory outside the stack untouched. -/
structure InvK (s t : MachineState) (a0 : Word) (σ : Reg → Word) : Prop where
  sp : t.getReg .x2 = s.getReg .x2 - 32
  a0 : t.getReg .x10 = a0
  sv : ∀ r ∈ saved, t.getReg r = σ r
  kept : ∀ r ∈ kept, t.getReg r = s.getReg r
  ra : t.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : t.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : t.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : t.getMem (s.getReg .x2 - 32) = s.getReg .x18
  mem : ∀ a, ¬ Within a (stackLo s kInvStack) kInvStack → t.getMem a = s.getMem a

/-- `σ`, with `r` set to `v` when `upd = some r`. -/
def updσ (σ : Reg → Word) (upd : Option Reg) (v : Word) : Reg → Word :=
  match upd with
  | none => σ
  | some r => Function.update σ r v

/-- The block lists `r` with expression `e`. -/
def regIs (x : Expect) (r : Reg) (e : E) : Bool :=
  (x.regs.find? fun p ↦ Sym.Reg.beqN p.1 r).isSome && E.beq (x.reg r) e

theorem regIs_holds {x : Expect} {s t : MachineState} (h : x.Holds s t) {r : Reg} {e : E}
    (hr : regIs x r e = true) : t.getReg r = e.eval s := by
  simp only [regIs, Bool.and_eq_true] at hr
  rw [h.reg r hr.1, E.beq_eq hr.2]

theorem all_regIs {x : Expect} {s t : MachineState} (h : x.Holds s t) {l : List Reg}
    {f : Reg → E} (hl : (l.all fun r ↦ regIs x r (f r)) = true) :
    ∀ r ∈ l, t.getReg r = (f r).eval s :=
  fun r hr ↦ regIs_holds h (List.all_eq_true.mp hl r hr)

/-- The registers both shapes keep. -/
def keptAll : List Reg := .x2 :: .x10 :: kept

/-- Copy `a0` to `upd`'s register if any, and call `K::square`, returning to `q`. -/
def sqShape (x : Expect) (q : Word) (upd : Option Reg) : Bool :=
  E.beq x.pc (.c 0x8000d670) && regIs x .x1 (.c q) && x.writes.isEmpty && x.obl.isEmpty &&
    (keptAll.all fun r ↦ regIs x r (.reg r)) &&
    (saved.all fun r ↦ regIs x r (.reg (if upd = some r then .x10 else r))) &&
    decide (q &&& 0xfffffffffffffffe = q)

/-- `a1 = r`, and call `base_mul`, returning to `q`. -/
def mulShape (x : Expect) (q : Word) (r : Reg) : Bool :=
  E.beq x.pc (.c 0x8000d774) && regIs x .x1 (.c q) && x.writes.isEmpty && x.obl.isEmpty &&
    regIs x .x11 (.reg r) && ((saved ++ keptAll).all fun r ↦ regIs x r (.reg r)) &&
    decide (r ∈ saved) && decide (q &&& 0xfffffffffffffffe = q)

/-- One step of the chain, or a dead end. -/
theorem chain {s : MachineState} {P Q : MachineState → Prop}
    (h : ∃ u, Reaches Image.code s u ∧ (P u ∨ Dead Image.code u))
    (k : ∀ u, P u → ∃ v, Reaches Image.code u v ∧ (Q v ∨ Dead Image.code v)) :
    ∃ v, Reaches Image.code s v ∧ (Q v ∨ Dead Image.code v) := by
  obtain ⟨u, hu, hP | hd⟩ := h
  · obtain ⟨v, hv, hQ⟩ := k u hP
    exact ⟨v, hu.trans hv, hQ⟩
  · exact ⟨u, hu, Or.inr hd⟩

theorem mem_kept {r : Reg} (h : r ∈ kept) : r ∈ keptAll := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem saved_callee {r : Reg} (h : r ∈ saved) : r ∈ Rv64Verifier.calleeSaved := by
  simp only [saved, Rv64Verifier.calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  tauto

theorem kept_callee {r : Reg} (h : r ∈ kept) : r ∈ Rv64Verifier.calleeSaved := by
  simp only [kept, Rv64Verifier.calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  tauto

/-- A `sqShape` block and its `K::square` call. -/
theorem sqStep (hSq : KSquareSpec) {x : Expect} {p q : Word} {k : Nat}
    (hb : Sym.BlockSpec Image.code p k (fun s ↦ Sym.Oblig.all s x.obl) x.Holds) {upd : Option Reg}
    (hx : sqShape x q upd = true) {s t : MachineState} {a0 : Word} {σ : Reg → Word}
    (ht : t.pc = p ∧ InvK s t a0 σ) :
    ∃ u, Reaches Image.code t u ∧
      ((u.pc = q ∧ InvK s u (Model.kSquare a0) (updσ σ upd a0)) ∨ Dead Image.code u) := by
  simp only [sqShape, Bool.and_eq_true, decide_eq_true_eq] at hx
  obtain ⟨⟨⟨⟨⟨⟨hpc, hra⟩, hw⟩, hobl⟩, hkept⟩, hsv⟩, hq⟩ := hx
  obtain ⟨c, hr, h⟩ := Sym.BlockSpec.reaches hb ht.1 (by
    rw [List.isEmpty_iff.mp hobl]; exact (Sym.Oblig.all_iff _ _).mpr fun _ h ↦ by cases h)
  have hk := all_regIs h hkept
  have hs := all_regIs h hsv
  have hcm : ∀ a, c.getMem a = t.getMem a := h.mem_same (List.isEmpty_iff.mp hw)
  obtain ⟨v, hr₂, ⟨hvpc, hpres, hpost⟩ | hdead⟩ :=
    hSq.call hr (h.pc.trans (E.beq_eq hpc ▸ rfl)) trivial
  swap
  · exact ⟨v, hr₂, Or.inr hdead⟩
  have hc1 : c.getReg .x1 = q := regIs_holds h hra
  have hreg (r : Reg) (hr : r ∈ Rv64Verifier.calleeSaved) (hk' : r ∈ keptAll) :
      v.getReg r = t.getReg r := by
    rw [hpres r hr, hk r hk']; rfl
  refine ⟨v, hr₂, Or.inl ⟨?_, {
    sp := by rw [hreg .x2 (by decide) (by decide), ht.2.sp]
    a0 := by
      rw [hpost.value, hk .x10 (by decide), ← Model.kSquare_eq]
      show Model.kSquare (t.getReg .x10) = _
      rw [ht.2.a0]
    sv := fun r hr ↦ by
      rw [hpres r (saved_callee hr), hs r hr]
      cases upd with
      | none => exact ht.2.sv r hr
      | some u =>
        simp only [updσ]
        by_cases hu : u = r
        · subst hu
          rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), Function.update_self]
          exact ht.2.a0
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ hu (Option.some.inj h))),
            Function.update_of_ne (Ne.symm hu)]
          exact ht.2.sv r hr
    kept := fun r hr ↦ by rw [hreg r (kept_callee hr) (mem_kept hr), ht.2.kept r hr]
    ra := by rw [hpost.mem, hcm, ht.2.ra]
    s0 := by rw [hpost.mem, hcm, ht.2.s0]
    s1 := by rw [hpost.mem, hcm, ht.2.s1]
    s2 := by rw [hpost.mem, hcm, ht.2.s2]
    mem := fun a ha ↦ by rw [hpost.mem, hcm, ht.2.mem a ha] }⟩⟩
  rw [hvpc, returnAddress_eq, hc1]
  exact hq

/-- `sp` as a number. -/
theorem sp_facts {s : MachineState} (h : KInvPre s) :
    0x20 + kInvStack ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧
      (stackLo s kInvStack).toNat = (s.getReg .x2).toNat - kInvStack :=
  h.stack.bounds (by decide) (by decide)

/-- A `mulShape` block and its `base_mul` call. -/
theorem mulStep (hBM : BaseMulSpec) {s : MachineState} (hpre : KInvPre s) {x : Expect}
    {p q : Word} {k : Nat}
    (hb : Sym.BlockSpec Image.code p k (fun s ↦ Sym.Oblig.all s x.obl) x.Holds) {r : Reg}
    (hx : mulShape x q r = true) {t : MachineState} {a0 : Word} {σ : Reg → Word}
    (ht : t.pc = p ∧ InvK s t a0 σ) :
    ∃ u, Reaches Image.code t u ∧
      ((u.pc = q ∧ InvK s u (Model.baseMul a0 (σ r)) σ) ∨ Dead Image.code u) := by
  simp only [mulShape, Bool.and_eq_true, decide_eq_true_eq] at hx
  obtain ⟨⟨⟨⟨⟨⟨⟨hpc, hra⟩, hw⟩, hobl⟩, h11⟩, hkept⟩, hrs⟩, hq⟩ := hx
  have hsp := sp_facts hpre
  have hP := hpre.pool.apart
  obtain ⟨c, hr, h⟩ := Sym.BlockSpec.reaches hb ht.1 (by
    rw [List.isEmpty_iff.mp hobl]; exact (Sym.Oblig.all_iff _ _).mpr fun _ h ↦ by cases h)
  have hk := all_regIs h hkept
  have hcm : ∀ a, c.getMem a = t.getMem a := h.mem_same (List.isEmpty_iff.mp hw)
  have hc2 : c.getReg .x2 = s.getReg .x2 - 32 := by
    rw [hk .x2 (by decide)]; exact ht.2.sp
  have hpre' : BaseMulPre c := {
    stack := ⟨by valid_sub hpre.stack.valid [hsp, hc2], by addr_omega [hsp, hc2]⟩
    pool := {
      word := by
        rw [hcm, ht.2.mem _ (by addr_omega [hP, hsp])]
        exact hpre.pool.word
      apart := by addr_omega [hP, hsp, hc2] } }
  obtain ⟨v, hr₂, ⟨hvpc, hpres, hpost⟩ | hdead⟩ :=
    hBM.call hr (h.pc.trans (E.beq_eq hpc ▸ rfl)) hpre'
  swap
  · exact ⟨v, hr₂, Or.inr hdead⟩
  have hc1 : c.getReg .x1 = q := regIs_holds h hra
  have hreg (r : Reg) (hr : r ∈ Rv64Verifier.calleeSaved) (hk' : r ∈ saved ++ keptAll) :
      v.getReg r = t.getReg r := by
    rw [hpres r hr, hk r hk']; rfl
  have hvold (a : Word) (ha : ¬ Within a (s.getReg .x2 - 144) 112) : v.getMem a = t.getMem a := by
    rw [hpost.frame a (by addr_omega [ha, hc2, hsp]), hcm]
  refine ⟨v, hr₂, Or.inl ⟨?_, {
    sp := by rw [hreg .x2 (by decide) (by decide), ht.2.sp]
    a0 := by
      rw [hpost.value, regIs_holds h h11, hk .x10 (by decide)]
      show (kOf (t.getReg .x10) * kOf (t.getReg r)).toBitVec = _
      rw [← Model.baseMul_eq, ht.2.a0, ht.2.sv r hrs]
      rfl
    sv := fun r hr ↦ by
      rw [hreg r (saved_callee hr) (List.mem_append_left _ hr), ht.2.sv r hr]
    kept := fun r hr ↦ by
      rw [hreg r (kept_callee hr) (List.mem_append_right _ (mem_kept hr)), ht.2.kept r hr]
    ra := by rw [hvold _ (by addr_omega [hsp]), ht.2.ra]
    s0 := by rw [hvold _ (by addr_omega [hsp]), ht.2.s0]
    s1 := by rw [hvold _ (by addr_omega [hsp]), ht.2.s1]
    s2 := by rw [hvold _ (by addr_omega [hsp]), ht.2.s2]
    mem := fun a ha ↦ by rw [hvold a (by addr_omega [ha, hsp]), ht.2.mem a ha] }⟩⟩
  rw [hvpc, returnAddress_eq, hc1]
  exact hq

/-- The prologue and the first square: `s0 = a`, `a0 = a^2`. -/
theorem prologue (hSq : KSquareSpec) {s : MachineState} (hpre : KInvPre s)
    (hpc : s.pc = 0x8000d7f4) :
    ∃ u, Reaches Image.code s u ∧ ((u.pc = 0x8000d814 ∧ InvK s u (Model.kSquare (s.getReg .x10))
      (updσ (fun r ↦ s.getReg r) (some .x8) (s.getReg .x10))) ∨ Dead Image.code u) := by
  have hsp := sp_facts hpre
  obtain ⟨c, hr, h⟩ := Sym.BlockSpec.reaches b8000d7f4_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hsp])
  have k := b8000d7f4_keeps h
  have hm := b8000d7f4_frame h (by addr_omega [hsp])
  obtain ⟨v, hr₂, ⟨hvpc, hpres, hpost⟩ | hdead⟩ := hSq.call hr (b8000d7f4_pc h) trivial
  swap
  · exact ⟨v, hr₂, Or.inr hdead⟩
  refine ⟨v, hr₂, Or.inl ⟨by rw [hvpc, returnAddress_eq, b8000d7f4_x1 h]; decide, {
    sp := by rw [hpres.reg .x2, b8000d7f4_x2 h]
    a0 := by
      rw [hpost.value, k .x10 (by decide), ← Model.kSquare_eq]
      rfl
    sv := fun r hr ↦ by
      rw [hpres r (saved_callee hr)]
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [b8000d7f4_x8 h]; rfl
      · rw [k .x9 (by decide)]; rfl
      · rw [k .x18 (by decide)]; rfl
    kept := fun r hr ↦ by
      rw [hpres r (kept_callee hr), k r (by
        simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)]
    ra := by rw [hpost.mem, b8000d7f4_m_x2_n8 h]
    s0 := by rw [hpost.mem, b8000d7f4_m_x2_n16 h]
    s1 := by rw [hpost.mem, b8000d7f4_m_x2_n24 h]
    s2 := by rw [hpost.mem, b8000d7f4_m_x2_n32 h]
    mem := fun a ha ↦ by rw [hpost.mem, hm a (by addr_omega [ha, hsp])] }⟩⟩

/-- The epilogue and the tail call: `a0` squared, back to the caller. -/
theorem epilogue (hSq : KSquareSpec) {s t : MachineState} (hpre : KInvPre s) {a0 : Word}
    {σ : Reg → Word} (ht : t.pc = 0x8000da6c ∧ InvK s t a0 σ) :
    ∃ u, Reaches Image.code t u ∧ ((u.pc = returnAddress s ∧ Preserves s u ∧
      u.getReg .x10 = Model.kSquare a0 ∧ StackFrame s u kInvStack) ∨ Dead Image.code u) := by
  have hsp := sp_facts hpre
  obtain ⟨c, hr, h⟩ := Sym.BlockSpec.reaches b8000da6c_spec ht.1 (by
    rv_eval [ht.2.sp]
    and_intros <;> valid_access hpre.stack.valid [hsp])
  have k := b8000da6c_keeps h
  have hcm := b8000da6c_mem_same h
  have x1 := b8000da6c_x1 h
  have x2 := b8000da6c_x2 h
  have x8 := b8000da6c_x8 h
  have x9 := b8000da6c_x9 h
  have x18 := b8000da6c_x18 h
  rv_eval [ht.2.sp, ht.2.ra, ht.2.s0, ht.2.s1, ht.2.s2] at x1 x2 x8 x9 x18
  obtain ⟨v, hr₂, ⟨hvpc, hpres, hpost⟩ | hdead⟩ := hSq.call hr (b8000da6c_pc h) trivial
  swap
  · exact ⟨v, hr₂, Or.inr hdead⟩
  refine ⟨v, hr₂, Or.inl ⟨by rw [hvpc, returnAddress, returnAddress, x1], ?_, ?_, ?_⟩⟩
  · refine preserves_of ((hpres.reg .x2).trans x2) ((hpres.reg .x8).trans x8)
      ((hpres.reg .x9).trans x9) ((hpres.reg .x18).trans x18) ?_ fun r hr ↦ ?_
    · rw [hpres.reg .x19, k .x19 (by decide), ht.2.kept .x19 (by decide)]
    · have h1 : r ∈ kept := by
        simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto
      rw [hpres r (kept_callee h1), k r (by
        simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at h1 ⊢; tauto),
        ht.2.kept r h1]
  · rw [hpost.value, k .x10 (by decide), ← Model.kSquare_eq, ht.2.a0]
    rfl
  · intro a ha
    rw [hpost.mem, hcm, ht.2.mem a ha]

/-- `t63` of `K::inv`, as `Model.kInv` computes it. -/
def t63 (a : Word) : Word :=
  let t1 := a
  let t2 := Model.baseMul (Model.kSq t1 1) t1
  let t3 := Model.baseMul (Model.kSq t2 1) t1
  let t6 := Model.baseMul (Model.kSq t3 3) t3
  let t12 := Model.baseMul (Model.kSq t6 6) t6
  let t24 := Model.baseMul (Model.kSq t12 12) t12
  let t48 := Model.baseMul (Model.kSq t24 24) t24
  let t60 := Model.baseMul (Model.kSq t48 12) t12
  Model.baseMul (Model.kSq t60 3) t3

theorem kInv_t63 (a : Word) : Model.kInv a = Model.kSquare (t63 a) := rfl

/-- The 71 blocks and their calls, up to the epilogue with `t63` in `a0`. -/
theorem body (hSq : KSquareSpec) (hBM : BaseMulSpec) {s : MachineState} (hpre : KInvPre s)
    (hpc : s.pc = 0x8000d7f4) :
    ∃ u, Reaches Image.code s u ∧
      ((u.pc = 0x8000da6c ∧ ∃ σ, InvK s u (t63 (s.getReg .x10)) σ) ∨ Dead Image.code u) :=
  chain (prologue hSq hpre hpc) fun _ h ↦
  chain (mulStep hBM hpre b8000d814_spec (q := 0x8000d820) (r := .x8) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d820_spec (q := 0x8000d828) (upd := none) rfl h) fun _ h ↦
  chain (mulStep hBM hpre b8000d828_spec (q := 0x8000d834) (r := .x8) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d834_spec (q := 0x8000d840) (upd := (some .x8)) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d840_spec (q := 0x8000d848) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d848_spec (q := 0x8000d850) (upd := none) rfl h) fun _ h ↦
  chain (mulStep hBM hpre b8000d850_spec (q := 0x8000d85c) (r := .x8) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d85c_spec (q := 0x8000d868) (upd := (some .x9)) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d868_spec (q := 0x8000d870) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d870_spec (q := 0x8000d878) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d878_spec (q := 0x8000d880) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d880_spec (q := 0x8000d888) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d888_spec (q := 0x8000d890) (upd := none) rfl h) fun _ h ↦
  chain (mulStep hBM hpre b8000d890_spec (q := 0x8000d89c) (r := .x9) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d89c_spec (q := 0x8000d8a8) (upd := (some .x9)) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d8a8_spec (q := 0x8000d8b0) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d8b0_spec (q := 0x8000d8b8) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d8b8_spec (q := 0x8000d8c0) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d8c0_spec (q := 0x8000d8c8) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d8c8_spec (q := 0x8000d8d0) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d8d0_spec (q := 0x8000d8d8) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d8d8_spec (q := 0x8000d8e0) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d8e0_spec (q := 0x8000d8e8) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d8e8_spec (q := 0x8000d8f0) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d8f0_spec (q := 0x8000d8f8) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d8f8_spec (q := 0x8000d900) (upd := none) rfl h) fun _ h ↦
  chain (mulStep hBM hpre b8000d900_spec (q := 0x8000d90c) (r := .x9) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d90c_spec (q := 0x8000d918) (upd := (some .x18)) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d918_spec (q := 0x8000d920) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d920_spec (q := 0x8000d928) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d928_spec (q := 0x8000d930) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d930_spec (q := 0x8000d938) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d938_spec (q := 0x8000d940) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d940_spec (q := 0x8000d948) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d948_spec (q := 0x8000d950) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d950_spec (q := 0x8000d958) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d958_spec (q := 0x8000d960) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d960_spec (q := 0x8000d968) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d968_spec (q := 0x8000d970) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d970_spec (q := 0x8000d978) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d978_spec (q := 0x8000d980) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d980_spec (q := 0x8000d988) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d988_spec (q := 0x8000d990) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d990_spec (q := 0x8000d998) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d998_spec (q := 0x8000d9a0) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d9a0_spec (q := 0x8000d9a8) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d9a8_spec (q := 0x8000d9b0) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d9b0_spec (q := 0x8000d9b8) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d9b8_spec (q := 0x8000d9c0) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d9c0_spec (q := 0x8000d9c8) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d9c8_spec (q := 0x8000d9d0) (upd := none) rfl h) fun _ h ↦
  chain (mulStep hBM hpre b8000d9d0_spec (q := 0x8000d9dc) (r := .x18) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d9dc_spec (q := 0x8000d9e4) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d9e4_spec (q := 0x8000d9ec) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d9ec_spec (q := 0x8000d9f4) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d9f4_spec (q := 0x8000d9fc) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000d9fc_spec (q := 0x8000da04) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000da04_spec (q := 0x8000da0c) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000da0c_spec (q := 0x8000da14) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000da14_spec (q := 0x8000da1c) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000da1c_spec (q := 0x8000da24) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000da24_spec (q := 0x8000da2c) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000da2c_spec (q := 0x8000da34) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000da34_spec (q := 0x8000da3c) (upd := none) rfl h) fun _ h ↦
  chain (mulStep hBM hpre b8000da3c_spec (q := 0x8000da48) (r := .x9) rfl h) fun _ h ↦
  chain (sqStep hSq b8000da48_spec (q := 0x8000da50) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000da50_spec (q := 0x8000da58) (upd := none) rfl h) fun _ h ↦
  chain (sqStep hSq b8000da58_spec (q := 0x8000da60) (upd := none) rfl h) fun _ h ↦
  chain (mulStep hBM hpre b8000da60_spec (q := 0x8000da6c) (r := .x8) rfl h) fun _ h ↦
  ⟨_, Reaches.refl _, Or.inl ⟨h.1, _, h.2⟩⟩

/-- **`K::inv` inverts**, zero to zero, given `K::square`'s and `base_mul`'s contracts. -/
theorem k_inv_spec (hSq : KSquareSpec) (hBM : BaseMulSpec) : KInvSpec := by
  intro s hpc hpre
  obtain ⟨u, hu, hd⟩ := chain (body hSq hBM hpre hpc) fun _ h ↦
    let ⟨hpc', _, hσ⟩ := h
    epilogue hSq hpre ⟨hpc', hσ⟩
  rcases hd with ⟨hpc', hpres, hv, hf⟩ | hd
  · refine ⟨u, hu, Or.inl ⟨hpc', hpres, ⟨?_, hf⟩⟩⟩
    rw [hv, ← kInv_t63, ← Model.kInv_eq]
    rfl
  · exact ⟨u, hu, Or.inr hd⟩

end Rv64Verifier.Proofs.Field.KInv
