import Rv64Verifier.Proofs.Walk.R8E

/-!
# `walk`: `tables()`, SET's `bytecode` (R8)

`term(One, ZERO)` into `sp + 2432`, the five operands copied into `P` and the `Vec` {5, `P`, 5} at
`sp + 2432` (`setTerm`), `bytecode(SET_CNT_BC, OP_SET, operands)` (`setBc`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf FormVecOk formVecOf)

/-- The heap from `W` on, below `NEXT`, is what `M8` lets a step write. -/
theorem heapOk {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L)
    {o : Word} {n : Nat} (ho : W ≤ o.toNat) (hn : o.toNat + n ≤ heapNext u) :
    ∀ a, Within a o n → W6 s B u a ∧ M8W s W L a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hu := h.m.inv.heap.hi
  have hb := h.bb
  simp only [heapEnd] at hu
  intro a ha
  simp only [Within] at ha
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))), ?_⟩
  simp only [M8W]
  refine ⟨by omega, ?_, ?_, ?_, fun e he hw ↦ ?_⟩
  · simp only [Within]; addr_omega [ha, hb1, hn, hu]
  · simp only [Within]; addr_omega [ha, hb1, hn, hu]
  · simp only [Within]; addr_omega [ha, hb1, hn, hu]
  · obtain ⟨e1, -, -⟩ := (h.tabs e he).1
    simp only [Within] at hw; addr_omega [ha, hw, hb1, e1, hn, hu]

/-- `FB` across a frame that writes neither its header nor what it reaches. -/
theorem FB.frame' {u v : MachineState} {o : Word} {F : LayoutMirror.FlushesRust} {lo : Nat}
    {w : Word → Prop} (h : FB u o F lo) (fr : Rv64Verifier.Layout.DFrame u v w)
    (hh : ∀ x, Within x o 48 → ¬ w x) (hd : ∀ x, flushesDeep u o x → ¬ w x)
    (ho : o.toNat + 48 ≤ 2 ^ 64) (hheap : HeapOk u) (mono : heapNext u ≤ heapNext v) :
    FB v o F lo ∧ flushesDeep v o = flushesDeep u o := by
  have G := Rv64Verifier.Layout.flushesOf_frame fr h.ok hh hd ho hheap mono
  exact ⟨⟨G.2.1, by rw [G.1]; exact h.val, fun x hx ↦ h.deep x (by rw [← G.2.2.1]; exact hx)⟩, G.2.2.1⟩

/-- Five forms 24 bytes apart from `P`, held by the `Vec` {5, `P`, 5} at `a`. -/
theorem vec5 {v : MachineState} {a P : Word} {lo hi : Nat} {f0 f1 f2 f3 f4 : LayoutMirror.FormRust}
    (c : vecCap v a = 5) (p : vecPtr v a = P) (l : vecLen v a = 5) (pal : P.toNat % 8 = 0)
    (hP : 0x20000000 ≤ P.toNat) (hlo : P.toNat + 120 ≤ lo) (hn : P.toNat + 120 ≤ heapNext v)
    (s0 : SF v P f0 lo hi) (s1 : SF v (P + 24) f1 lo hi) (s2 : SF v (P + 48) f2 lo hi)
    (s3 : SF v (P + 72) f3 lo hi) (s4 : SF v (P + 96) f4 lo hi) :
    FormVecOk v a ∧ formVecOf v a = [f0, f1, f2, f3, f4] := by
  have e5 : (5 : Word).toNat = 5 := rfl
  have q0 : P + BitVec.ofNat 64 (24 * 0) = P := by simp
  have q1 : P + BitVec.ofNat 64 (24 * 1) = P + 24 := rfl
  have q2 : P + BitVec.ofNat 64 (24 * 2) = P + 48 := rfl
  have q3 : P + BitVec.ofNat 64 (24 * 3) = P + 72 := rfl
  have q4 : P + BitVec.ofNat 64 (24 * 4) = P + 96 := rfl
  have g : ∀ i < 5, FormOk v (P + BitVec.ofNat 64 (24 * i)) ∧
      ∀ x, formBuf v (P + BitVec.ofNat 64 (24 * i)) x → lo ≤ x.toNat := by
    intro i hi
    interval_cases i
    · rw [q0]; exact ⟨s0.ok, fun x hx ↦ (s0.buf x hx).1⟩
    · rw [q1]; exact ⟨s1.ok, fun x hx ↦ (s1.buf x hx).1⟩
    · rw [q2]; exact ⟨s2.ok, fun x hx ↦ (s2.buf x hx).1⟩
    · rw [q3]; exact ⟨s3.ok, fun x hx ↦ (s3.buf x hx).1⟩
    · rw [q4]; exact ⟨s4.ok, fun x hx ↦ (s4.buf x hx).1⟩
  refine ⟨⟨⟨?_, by rw [l, c]⟩, ?_, ?_⟩, ?_⟩
  · simp only [RawVecOk, Buf, c, p, e5]
    exact ⟨pal, Or.inr ⟨by simp only [heapStart]; omega, by omega⟩⟩
  · rw [p, l, e5]; exact fun i hi ↦ (g i hi).1
  · rw [p, l, e5]
    rintro x ⟨i, hi, hx⟩ hw
    have := (g i hi).2 x hx
    simp only [Rv64Verifier.Layout.formVecBuf, p, c, e5, Within] at hw
    omega
  · have r5 : List.range 5 = [0, 1, 2, 3, 4] := rfl
    simp only [formVecOf, Rv64Verifier.Layout.formsAt, p, l, e5, r5, List.map_cons, List.map_nil]
    rw [q0, q1, q2, q3, q4, s0.val, s1.val, s2.val, s3.val, s4.val]

/-- SET's operands. -/
abbrev setOps : List LayoutMirror.FormRust :=
  [LayoutMirror.colRust 2 0, LayoutMirror.colRust 3 0, LayoutMirror.colRust 4 0,
    LayoutMirror.colRust 5 0, LayoutMirror.constantRust 0]

set_option maxRecDepth 8192 in
/-- `term(One, ZERO)` into `sp + 2432`, the operands copied into `P` and the `Vec` {5, `P`, 5} at
`sp + 2432`, to `bytecode`'s call. -/
theorem setTerm (hT : Rv64Verifier.Layout.TermSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {F : LayoutMirror.FlushesRust} {lo : Nat} {P : Word} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W (L3 s)) (fb : FB u (s.getReg .x2 - 928) F lo)
    (hS : SFs s u (P.toNat + 120) (setFs s P)) (pal : P.toNat % 8 = 0) (hP : W ≤ P.toNat)
    (pnx : P.toNat + 120 ≤ heapNext u)
    (pdeep : ∀ x, flushesDeep u (s.getReg .x2 - 928) x → x.toNat < P.toNat)
    (m0 : u.getMem (s.getReg .x2 - 512) = 0) (r : SetR u P)
    (x10 : u.getReg .x10 = s.getReg .x2 - 224) (x11 : u.getReg .x11 = s.getReg .x2 - 512)
    (x12 : u.getReg .x12 = 0xa0000068) (x23 : u.getReg .x23 = s.getReg .x2 - 512)
    (x26 : u.getReg .x26 = 5) (x1 : u.getReg .x1 = 0x800021ac) (hpc : u.pc = 0x800050a8) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b94 ∧ M8 OI s t A k R Q B Bb W (L3 s) ∧
      FB t (s.getReg .x2 - 928) F lo ∧ FormVecOk t (s.getReg .x2 - 224) ∧
      formVecOf t (s.getReg .x2 - 224) = setOps ∧ vecPtr t (s.getReg .x2 - 224) = P ∧
      vecLen t (s.getReg .x2 - 224) = 5 ∧ P.toNat + 120 ≤ heapNext t ∧
      (∀ x, flushesDeep t (s.getReg .x2 - 928) x → x.toNat < P.toNat) ∧ SetR t P ∧
      t.getReg .x10 = s.getReg .x2 - 928 ∧ t.getReg .x11 = 7 ∧ t.getReg .x12 = 2 ∧
      t.getReg .x13 = s.getReg .x2 - 224 ∧ t.getReg .x18 = 7 ∧ t.getReg .x23 = s.getReg .x2 - 512 ∧
      t.getReg .x26 = 5 ∧ t.getReg .x1 = 0x80002238) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hu := h.m.inv.heap.hi
  simp only [heapEnd] at hu
  have hb := h.bb
  have hq := h.m.bufQ
  have hs := hpre.heap.lo
  simp only [heapStart] at hs
  have hPlo : 0x20000000 ≤ P.toNat := by omega
  have hFo : InSlot s (s.getReg .x2 - 928) 48 := by simp only [InSlot]; addr_omega [hb1, hb3]
  obtain ⟨t₁, r₁, ⟨pc₁, hp₁, M₁, F₁, hN₁, S₁, D₁⟩ | d⟩ := termSlot hT (o := s.getReg .x2 - 224)
    (m := s.getReg .x2 - 512) hpre h fb hFo hS pnx (by simp only [InSlot]; addr_omega [hb1, hb3])
    (l3_apart hpre (by addr_omega [hb1])) (fun a ha hw ↦ by simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
    (fun e he x hx hw ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> simp only [Within] at hx hw <;> addr_omega [hx, hw, hb1, pnx, hu])
    hpc x10 x11 (by simp only [InSlot]; addr_omega [hb1, hb3]) m0 x12
  swap
  · exact ⟨t₁, r₁, Or.inr d⟩
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := M₁.m.inv.sp
  have R₁ := r.pres hp₁
  have y23 : t₁.getReg .x23 = s.getReg .x2 - 512 := by rw [hp₁.reg .x23]; exact x23
  have y25 : t₁.getReg .x25 = P := R₁.x25
  have y26 : t₁.getReg .x26 = 5 := by rw [hp₁.reg .x26]; exact x26
  have hu₁ := M₁.m.inv.heap.hi
  simp only [heapEnd] at hu₁
  have pn₁ : P.toNat + 120 ≤ heapNext t₁ := by omega
  have hmP : Mapped P 120 := Or.inl ⟨by omega, by omega⟩
  -- the operands into `P`, the `Vec` at `sp + 2432`
  obtain ⟨u₂, r₂, g₂⟩ := Sym.BlockSpec.reaches b800021ac_spec
    (by rw [pc₁, returnAddress_eq, x1]; decide) (by
      rv_eval [sp₁, y23, y25]
      and_intros
      all_goals first
        | valid_access hval [hb1]
        | exact Mapped.valid8 hmP (by addr_omega [pal, hPlo, hu₁, pn₁]) (by addr_omega [pal, hPlo, hu₁, pn₁])
            (by addr_omega [pal, hPlo, hu₁, pn₁])
        | addr_omega [hb1, hPlo, hu₁, pn₁])
  have k₂ := b800021ac_keeps g₂
  have fr₂ : Rv64Verifier.Layout.DFrame t₁ u₂ fun x ↦ Within x (s.getReg .x2 - 224) 24 ∨
      Within x (P + 24) 96 :=
    Expect.ldframe g₂ (by
      rv_eval [sp₁, y23, y25]
      simp only [Within]
      and_intros
      all_goals first
        | exact Or.inl (by addr_omega [hb1])
        | exact Or.inr (by addr_omega [hPlo, hu₁, pn₁]))
  have nw : ∀ x, x.toNat < P.toNat ∨ P.toNat + 120 ≤ x.toNat → x.toNat < heapNext t₁ →
      ¬ (Within x (s.getReg .x2 - 224) 24 ∨ Within x (P + 24) 96) := fun x h1 h2 hw ↦ by
    simp only [Within] at hw
    rcases hw with hw | hw <;> rcases h1 with h1 | h1 <;> addr_omega [hw, h1, h2, hb1, hPlo, hu₁, pn₁]
  have hn₂ : heapNext u₂ = heapNext t₁ := by
    simp only [heapNext]; rw [fr₂ _ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, hPlo, hu₁, pn₁])
      (by decide)]
  have hv₂ : HeapOk u₂ := ⟨hn₂ ▸ M₁.m.inv.heap.lo, hn₂ ▸ M₁.m.inv.heap.hi⟩
  have hW₂ := slotOk hpre M₁ (o := s.getReg .x2 - 224) (n := 24)
    (by simp only [InSlot]; addr_omega [hb1, hb3]) (l3_apart hpre (by addr_omega [hb1]))
  have hP₂ := heapOk hpre M₁ (o := P + 24) (n := 96) (by addr_omega [hP, hPlo, hu₁, pn₁])
    (by addr_omega [hPlo, hu₁, pn₁])
  have M₂ := M₁.step hpre fr₂ (fun a ha ↦ ?_) (fun a ha ↦ ?_) hv₂ hn₂.ge (k₂ .x2 (by decide))
  rotate_left
  · rcases ha with ha | ha
    · exact ((hW₂ a ha).1).mono hn₂.ge
    · exact ((hP₂ a ha).1).mono hn₂.ge
  · rcases ha with ha | ha
    · exact (hW₂ a ha).2
    · exact (hP₂ a ha).2
  have F₂ := F₁.frame' fr₂ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, hPlo, hu₁, pn₁])
    (fun x hx ↦ nw x (Or.inl (pdeep x (by rw [← D₁]; exact hx))) (F₁.ok.deep_below hx).2)
    (by addr_omega [hb1]) M₁.m.inv.heap hn₂.ge
  have sf (o : Word) (f : LayoutMirror.FormRust)
      (he : (o, f) ∈ (s.getReg .x2 - 224, LayoutMirror.constantRust 0) :: setFs s P) :
      SF t₁ o f (P.toNat + 120) (heapNext t₁) := S₁.sf _ he
  have hb : ∀ x, P.toNat + 120 ≤ x.toNat → x.toNat < heapNext t₁ →
      ¬ (Within x (s.getReg .x2 - 224) 24 ∨ Within x (P + 24) 96) := fun x h1 h2 ↦ nw x (Or.inr h1) h2
  have c0 := (sf P (LayoutMirror.colRust 2 0) (by simp)).frame fr₂ (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1, hPlo, hu₁, pn₁])
    hb (by omega) M₁.m.inv.heap hn₂.ge
  have c1 := (sf (s.getReg .x2 - 152) (LayoutMirror.colRust 3 0) (by simp)).move (o := P + 24) fr₂
    (by have := b800021ac_m_x25_24 g₂; rv_eval [sp₁, y23, y25] at this ⊢; exact this)
    (by have := b800021ac_m_x25_32 g₂; rv_eval [sp₁, y23, y25] at this ⊢; exact this)
    (by have := b800021ac_m_x25_40 g₂; rv_eval [sp₁, y23, y25] at this ⊢; exact this)
    hb M₁.m.inv.heap hn₂.ge
  have c2 := (sf (s.getReg .x2 - 1488) (LayoutMirror.colRust 4 0) (by simp)).move (o := P + 48) fr₂
    (by have := b800021ac_m_x25_48 g₂; rv_eval [sp₁, y23, y25] at this ⊢; exact this)
    (by have := b800021ac_m_x25_56 g₂; rv_eval [sp₁, y23, y25] at this ⊢; exact this)
    (by have := b800021ac_m_x25_64 g₂; rv_eval [sp₁, y23, y25] at this ⊢; exact this)
    hb M₁.m.inv.heap hn₂.ge
  have c3 := (sf (s.getReg .x2 - 416) (LayoutMirror.colRust 5 0) (by simp)).move (o := P + 72) fr₂
    (by have := b800021ac_m_x25_72 g₂; rv_eval [sp₁, y23, y25] at this ⊢; exact this)
    (by have := b800021ac_m_x25_80 g₂; rv_eval [sp₁, y23, y25] at this ⊢; exact this)
    (by have := b800021ac_m_x25_88 g₂; rv_eval [sp₁, y23, y25] at this ⊢; exact this)
    hb M₁.m.inv.heap hn₂.ge
  have c4 := (sf (s.getReg .x2 - 224) (LayoutMirror.constantRust 0) (by simp)).move (o := P + 96) fr₂
    (by have := b800021ac_m_x25_96 g₂; rv_eval [sp₁, y23, y25] at this ⊢; exact this)
    (by have := b800021ac_m_x25_104 g₂; rv_eval [sp₁, y23, y25] at this ⊢; exact this)
    (by have := b800021ac_m_x25_112 g₂; rv_eval [sp₁, y23, y25] at this ⊢; exact this)
    hb M₁.m.inv.heap hn₂.ge
  have vc : vecCap u₂ (s.getReg .x2 - 224) = 5 := by
    have := b800021ac_m_x23_288 g₂; simp only [vecCap]; rv_eval [y23, y26] at this ⊢; exact this
  have vp : vecPtr u₂ (s.getReg .x2 - 224) = P := by
    have := b800021ac_m_x23_296 g₂; simp only [vecPtr]; rv_eval [y23, y25] at this ⊢; exact this
  have vl : vecLen u₂ (s.getReg .x2 - 224) = 5 := by
    have := b800021ac_m_x23_304 g₂; simp only [vecLen]; rv_eval [y23, y26] at this ⊢; exact this
  have pn₂ : P.toNat + 120 ≤ heapNext u₂ := by omega
  have V := vec5 vc vp vl pal hPlo (le_refl _) pn₂ c0 c1 c2 c3 c4
  refine ⟨u₂, r₁.trans r₂, Or.inl ⟨b800021ac_pc g₂, M₂, F₂.1, V.1, V.2, vp, vl, pn₂,
    fun x hx ↦ pdeep x (by rw [← D₁, ← F₂.2]; exact hx), R₁.keeps k₂, ?_, b800021ac_x11 g₂,
    b800021ac_x12 g₂, ?_, b800021ac_x18 g₂, by rw [k₂ .x23 (by decide)]; exact y23,
    by rw [k₂ .x26 (by decide)]; exact y26, b800021ac_x1 g₂⟩⟩
  · rw [b800021ac_x10 g₂]; exact spAdd hpre sp₁ (N := 1728) (M := 928) (by decide)
  · rw [b800021ac_x13 g₂]; exact spAdd hpre sp₁ (N := 2432) (M := 224) (by decide)

end Rv64Verifier.Proofs.Walk
