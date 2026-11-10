import Rv64Verifier.Proofs.Walk.Dr1

/-!
# `walk`: `tables()`, DEREF's first stored value (R8)

From `AtDeref`: `col(8, 0)`, `prod(5, 8, 0)`, `prod(6, 8, 0)`, `prod(5, 0, 2)`, `prod(6, 1, 0)` into
`sp + 2432 .. 2552`, their sum into `sp + 1728` (`derefSum0`, at `0x800024b4`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

/-- Each form of a list in a frame slot apart from a region (`addr_omega` with the given facts). -/
macro "forms_tac" " [" ts:term,* "]" : tactic => `(tactic| (
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    and_intros
    all_goals (intro x hx hw; simp only [Within] at hx hw; addr_omega [hx, hw, $ts,*])))

/-- Each form of a list in a frame slot. -/
macro "slots_tac" " [" ts:term,* "]" : tactic => `(tactic| (
    simp only [InSlot, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    and_intros
    all_goals addr_omega [$ts,*]))

theorem DS.same {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o' : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : DS OI s u A k R Q B Bb W L o' F lo lo₂ Fs)
    (hm : ∀ a, v.getMem a = u.getMem a) (sp : v.getReg .x2 = u.getReg .x2) :
    DS OI s v A k R Q B Bb W L o' F lo lo₂ Fs ∧ heapNext v = heapNext u := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact ⟨⟨h.m.same hpre hm sp, h.fb.same hpre h.fo h.m.m.inv.heap hm, h.fo,
    h.sl.same hpre hm h.m.m.inv.heap, by rw [hn]; exact h.hlo₂⟩, hn⟩

/-- The SET table's `Flushes` as the one `DS` keeps while no `Flushes` is under construction. -/
theorem dsStart {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat} {t : LayoutMirror.TableRust}
    (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W (L4 s t)) :
    DS OI s u A k R Q B Bb W (L4 s t) (s.getReg .x2 - 1464) t.flushes B (heapNext u) [] := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have he : (s.getReg .x2 - 1488, t) ∈ L4 s t := by simp
  have fb : FB u (s.getReg .x2 - 1488 + 24) t.flushes B := h.fb he
  have e : s.getReg .x2 - 1488 + 24 = s.getReg .x2 - 1464 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [e] at fb
  exact ⟨h, fb, inSlot_off hpre (by decide), SFs.nil _ _ _, le_refl _⟩

theorem SFh.len1 {s u : MachineState} {lo hi : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    {q : Word} {f : LayoutMirror.FormRust} (h : SFh s u lo hi Fs) (hq : (q, f) ∈ Fs)
    (hf : ∃ m c, f = LayoutMirror.FormRust.term m c) : (vecLen u q).toNat = 1 := by
  obtain ⟨m, c, rfl⟩ := hf
  exact len_term (h.sf _ hq).val


/-- A block's frame at `sp + N` as the frame slot `s - M`. -/
theorem mfr {s u v : MachineState} (hpre : WalkPre s) (sp : u.getReg .x2 = s.getReg .x2 - 2656)
    {N M : Word} {n : Nat} (hNM : N.toNat + M.toNat = 2656)
    (h : MemFrame u v (u.getReg .x2 + N) n) :
    Rv64Verifier.Layout.DFrame u v (Within · (s.getReg .x2 - M) n) := by
  have := MemFrame.dframe h
  rwa [spAdd hpre sp hNM] at this

theorem ptrEq {u v : MachineState} {w : Word → Prop} (fr : Rv64Verifier.Layout.DFrame u v w)
    {a q : Word} (hx : a = q + 8) (ha : ∀ x, Within x (q + 8) 8 → ¬ w x) (hb : (q + 8).toNat + 8 ≤ 2 ^ 64) :
    u.getMem a = vecPtr v q := by
  rw [hx, vecPtr]; exact (fr _ ha hb).symm

theorem lenEq {u v : MachineState} {w : Word → Prop} (fr : Rv64Verifier.Layout.DFrame u v w)
    {a q : Word} (hx : a = q + 16) (ha : ∀ x, Within x (q + 16) 8 → ¬ w x)
    (hb : (q + 16).toNat + 8 ≤ 2 ^ 64) : u.getMem a = vecLen v q := by
  rw [hx, vecLen]; exact (fr _ ha hb).symm

/-- A block's store at `sp + N` as one at a frame slot. -/
macro "mem_tac" " [" ts:Lean.Parser.Tactic.simpLemma,* "] " t:term : tactic => `(tactic| (
    have h' := $t
    rv_eval [$ts,*] at h' ⊢
    exact h'))

/-- A word of the frame missed by a block's frame. -/
macro "apart_tac" " [" ts:term,* "]" : tactic => `(tactic|
    exact fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, $ts,*])

/-- The registers DEREF keeps, `s8` = `z`. -/
structure DRg (s u : MachineState) (z : Word) : Prop where
  x18 : u.getReg .x18 = 7
  x23 : u.getReg .x23 = s.getReg .x2 - 512
  x24 : u.getReg .x24 = z
  x25 : u.getReg .x25 = 8
  x26 : u.getReg .x26 = 5
  x27 : u.getReg .x27 = 6

theorem DRg.keeps {s u t : MachineState} {z : Word} {l : List Reg} (h : DRg s u z)
    (hk : ∀ r ∈ l, t.getReg r = u.getReg r)
    (hl : ∀ r ∈ ([.x18, .x23, .x24, .x25, .x26, .x27] : List Reg), r ∈ l := by decide) : DRg s t z :=
  ⟨by rw [hk .x18 (hl _ (by decide))]; exact h.x18, by rw [hk .x23 (hl _ (by decide))]; exact h.x23,
    by rw [hk .x24 (hl _ (by decide))]; exact h.x24, by rw [hk .x25 (hl _ (by decide))]; exact h.x25,
    by rw [hk .x26 (hl _ (by decide))]; exact h.x26, by rw [hk .x27 (hl _ (by decide))]; exact h.x27⟩

theorem DRg.pres {s u t : MachineState} {z : Word} (h : DRg s u z) (hp : Preserves u t) : DRg s t z :=
  h.keeps hp

/-- DEREF's first stored value, `v3[0] + f_pc v3[0] + f_fp v3[0] + g^2 f_pc pc + f_fp fp`. -/
abbrev store0 : LayoutMirror.FormRust :=
  LayoutMirror.FormRust.sum [LayoutMirror.colRust 8 0, LayoutMirror.prodRust 5 8 0,
    LayoutMirror.prodRust 6 8 0, LayoutMirror.prodRust 5 0 2, LayoutMirror.prodRust 6 1 0]

set_option maxRecDepth 8192 in
/-- The five one-term forms of DEREF's first stored value, to the sum's first `add_scaled`. -/
theorem deref0a (hC : Rv64Verifier.Layout.ColSpec) (hP : Rv64Verifier.Layout.ProdSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} (hpre : WalkPre s)
    (h : AtDeref OI s u A k R Q B Bb) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80002378 ∧
      DS OI s t A k R Q B Bb (heapNext u) (L4 s setT) (s.getReg .x2 - 1464) setT.flushes B
        (heapNext u)
        [(s.getReg .x2 - 128, LayoutMirror.prodRust 6 1 0), (s.getReg .x2 - 152, LayoutMirror.prodRust 5 0 2),
          (s.getReg .x2 - 176, LayoutMirror.prodRust 6 8 0), (s.getReg .x2 - 200, LayoutMirror.prodRust 5 8 0),
          (s.getReg .x2 - 224, LayoutMirror.colRust 8 0)] ∧ DRg s t 0xa0000068) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have r0 : DRg s u 0xa0000068 := ⟨h.rd.x18, h.rd.x23, h.rd.r8.x24, h.rd.x25, h.rd.x26, h.rd.x27⟩
  have D₀ := dsStart hpre h.m
  -- `col(8, 0)` into `sp + 2432`
  obtain ⟨t₁, q₁, ⟨pc₁, hp₁, D₁, -, -, -⟩ | d⟩ := colD hC (o := s.getReg .x2 - 224) hpre D₀
    (inSlot_off hpre (by decide)) (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (fun e he ↦ absurd he List.not_mem_nil) h.pc h.x10
  swap
  · exact ⟨t₁, q₁, Or.inr d⟩
  rw [h.x11, h.x12] at D₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := D₁.m.m.inv.sp
  -- `prod(5, 8, 0)` into `sp + 2456`
  obtain ⟨u₂, q₂, g₂⟩ := Sym.BlockSpec.reaches b80002308_spec (by rw [pc₁, returnAddress_eq, h.x1]; decide)
    trivial
  obtain ⟨E₂, -⟩ := D₁.same hpre (b80002308_mem_same g₂) (b80002308_keeps g₂ .x2 (by decide))
  obtain ⟨t₂, q₂', ⟨pc₂, hp₂, D₂, -, -, -⟩ | d⟩ := prodD hP (o := s.getReg .x2 - 200) hpre E₂
    (inSlot_off hpre (by decide)) (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (by forms_tac [hb1]) (b80002308_pc g₂)
    (by rw [b80002308_x10 g₂]; exact spAdd hpre sp₁ (by decide))
  swap
  · exact ⟨t₂, q₁.trans (q₂.trans q₂'), Or.inr d⟩
  rw [b80002308_x11 g₂, b80002308_x12 g₂, b80002308_x13 g₂] at D₂
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := D₂.m.m.inv.sp
  have Q₂ := q₁.trans (q₂.trans q₂')
  -- `prod(6, 8, 0)` into `sp + 2480`
  obtain ⟨u₃, q₃, g₃⟩ := Sym.BlockSpec.reaches b80002324_spec
    (by rw [pc₂, returnAddress_eq, b80002308_x1 g₂]; decide) trivial
  obtain ⟨E₃, -⟩ := D₂.same hpre (b80002324_mem_same g₃) (b80002324_keeps g₃ .x2 (by decide))
  obtain ⟨t₃, q₃', ⟨pc₃, hp₃, D₃, -, -, -⟩ | d⟩ := prodD hP (o := s.getReg .x2 - 176) hpre E₃
    (inSlot_off hpre (by decide)) (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (by forms_tac [hb1]) (b80002324_pc g₃)
    (by rw [b80002324_x10 g₃]; exact spAdd hpre sp₂ (by decide))
  swap
  · exact ⟨t₃, Q₂.trans (q₃.trans q₃'), Or.inr d⟩
  rw [b80002324_x11 g₃, b80002324_x12 g₃, b80002324_x13 g₃] at D₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := D₃.m.m.inv.sp
  have Q₃ := Q₂.trans (q₃.trans q₃')
  -- `prod(5, 0, 2)` into `sp + 2504`
  obtain ⟨u₄, q₄, g₄⟩ := Sym.BlockSpec.reaches b80002340_spec
    (by rw [pc₃, returnAddress_eq, b80002324_x1 g₃]; decide) trivial
  obtain ⟨E₄, -⟩ := D₃.same hpre (b80002340_mem_same g₄) (b80002340_keeps g₄ .x2 (by decide))
  obtain ⟨t₄, q₄', ⟨pc₄, hp₄, D₄, -, -, -⟩ | d⟩ := prodD hP (o := s.getReg .x2 - 152) hpre E₄
    (inSlot_off hpre (by decide)) (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (by forms_tac [hb1]) (b80002340_pc g₄)
    (by rw [b80002340_x10 g₄]; exact spAdd hpre sp₃ (by decide))
  swap
  · exact ⟨t₄, Q₃.trans (q₄.trans q₄'), Or.inr d⟩
  rw [b80002340_x11 g₄, b80002340_x12 g₄, b80002340_x13 g₄] at D₄
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 2656 := D₄.m.m.inv.sp
  have Q₄ := Q₃.trans (q₄.trans q₄')
  -- `prod(6, 1, 0)` into `sp + 2528`
  obtain ⟨u₅, q₅, g₅⟩ := Sym.BlockSpec.reaches b8000235c_spec
    (by rw [pc₄, returnAddress_eq, b80002340_x1 g₄]; decide) trivial
  obtain ⟨E₅, -⟩ := D₄.same hpre (b8000235c_mem_same g₅) (b8000235c_keeps g₅ .x2 (by decide))
  obtain ⟨t₅, q₅', ⟨pc₅, hp₅, D₅, -, -, -⟩ | d⟩ := prodD hP (o := s.getReg .x2 - 128) hpre E₅
    (inSlot_off hpre (by decide)) (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide))
    (by forms_tac [hb1]) (b8000235c_pc g₅)
    (by rw [b8000235c_x10 g₅]; exact spAdd hpre sp₄ (by decide))
  swap
  · exact ⟨t₅, Q₄.trans (q₅.trans q₅'), Or.inr d⟩
  rw [b8000235c_x11 g₅, b8000235c_x12 g₅, b8000235c_x13 g₅] at D₅
  refine ⟨t₅, Q₄.trans (q₅.trans q₅'), Or.inl ⟨by rw [pc₅, returnAddress_eq, b8000235c_x1 g₅]; decide,
    D₅, ?_⟩⟩
  have a₁ := (r0.pres hp₁).keeps (b80002308_keeps g₂)
  have a₂ := (a₁.pres hp₂).keeps (b80002324_keeps g₃)
  have a₃ := (a₂.pres hp₃).keeps (b80002340_keeps g₄)
  exact ((a₃.pres hp₄).keeps (b8000235c_keeps g₅)).pres hp₅

set_option maxRecDepth 8192 in
/-- DEREF's first stored value summed into `sp + 1728`, to `0x800024b4`. -/
theorem deref0b (hA : Rv64Verifier.Layout.AddScaledSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W lo₂ : Nat} (hpre : WalkPre s)
    (h : DS OI s u A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 1464) setT.flushes B lo₂
        [(s.getReg .x2 - 128, LayoutMirror.prodRust 6 1 0), (s.getReg .x2 - 152, LayoutMirror.prodRust 5 0 2),
          (s.getReg .x2 - 176, LayoutMirror.prodRust 6 8 0), (s.getReg .x2 - 200, LayoutMirror.prodRust 5 8 0),
          (s.getReg .x2 - 224, LayoutMirror.colRust 8 0)]) (r : DRg s u 0xa0000068)
    (hpc : u.pc = 0x80002378) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x800024b4 ∧
      SS OI s t A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 1464) setT.flushes B lo₂ (heapNext u)
        [(s.getReg .x2 - 128, LayoutMirror.prodRust 6 1 0), (s.getReg .x2 - 152, LayoutMirror.prodRust 5 0 2),
          (s.getReg .x2 - 176, LayoutMirror.prodRust 6 8 0), (s.getReg .x2 - 200, LayoutMirror.prodRust 5 8 0),
          (s.getReg .x2 - 224, LayoutMirror.colRust 8 0)] (s.getReg .x2 - 928) store0 ∧
      Keep u t (heapNext u) ∧ DRg s t 0xa00000b0) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := h.m.m.inv.sp
  have y23 := r.x23
  -- the empty sum at `sp + 1728`, the first term
  obtain ⟨v₁, p₁, g₁⟩ := Sym.BlockSpec.reaches b80002378_spec hpc (by
    rv_eval [sp, y23]
    and_intros <;> valid_access hval [hb1])
  have fr₁ := mfr hpre sp (N := 1728) (M := 928) (by decide) (b80002378_frame g₁ (by rw [sp]; addr_omega [hb1]))
  obtain ⟨S₁, -, K₁⟩ := SS.start hpre h (acc := s.getReg .x2 - 928) (inSlot_off hpre (by decide))
    (l4_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide)) (by forms_tac [hb1])
    (by slots_tac [hb1, hb3]) fr₁ (by mem_tac [sp] (b80002378_m_x2_1728 g₁))
    (by have h' := b80002378_m_x2_1736 g₁; rv_eval [sp] at h' ⊢; rw [h', r.x25])
    (by mem_tac [sp] (b80002378_m_x2_1744 g₁)) (b80002378_keeps g₁ .x2 (by decide))
  have r₁ : DRg s v₁ 0xa00000b0 :=
    ⟨by rw [b80002378_keeps g₁ .x18 (by decide)]; exact r.x18, by rw [b80002378_keeps g₁ .x23 (by decide)]; exact y23,
      b80002378_x24 g₁, by rw [b80002378_keeps g₁ .x25 (by decide)]; exact r.x25,
      by rw [b80002378_keeps g₁ .x26 (by decide)]; exact r.x26, by rw [b80002378_keeps g₁ .x27 (by decide)]; exact r.x27⟩
  obtain ⟨t₁, q₁, ⟨pc₁, hp₁, T₁, K₁', -⟩ | d⟩ := S₁.asc hA hpre (q := s.getReg .x2 - 224) (g := LayoutMirror.colRust 8 0)
    (by simp) ⟨_, _, rfl⟩ (b80002378_pc g₁)
    (by rw [b80002378_x10 g₁]; exact spAdd hpre sp (by decide))
    (by rw [b80002378_x11 g₁]; exact ptrEq fr₁ (by rw [y23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002378_x12 g₁]; exact lenEq fr₁ (by rw [y23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (b80002378_x13 g₁)
  swap
  · exact ⟨t₁, p₁.trans q₁, Or.inr d⟩
  have Q₁ := p₁.trans q₁
  have R₁ := r₁.pres hp₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := T₁.m.m.inv.sp
  -- the second term
  obtain ⟨v₂, p₂, g₂⟩ := Sym.BlockSpec.reaches b800023b4_spec
    (by rw [pc₁, returnAddress_eq, b80002378_x1 g₁]; decide) (by
      rv_eval [sp₁, R₁.x23]
      and_intros <;> valid_access hval [hb1])
  have fr₂ := mfr hpre sp₁ (N := 1728) (M := 928) (by decide) (b800023b4_frame g₂ (by rw [sp₁]; addr_omega [hb1]))
  obtain ⟨S₂, -, K₂⟩ := T₁.blk hpre fr₂ (by mem_tac [sp₁] (b800023b4_m_x2_1728 g₂))
    (by mem_tac [sp₁] (b800023b4_m_x2_1736 g₂)) (by mem_tac [sp₁] (b800023b4_m_x2_1744 g₂))
    (b800023b4_keeps g₂ .x2 (by decide))
  obtain ⟨t₂, q₂, ⟨pc₂, hp₂, T₂, K₂', -⟩ | d⟩ := S₂.asc hA hpre (q := s.getReg .x2 - 200) (g := LayoutMirror.prodRust 5 8 0)
    (by simp) ⟨_, _, rfl⟩ (b800023b4_pc g₂)
    (by rw [b800023b4_x10 g₂]; exact spAdd hpre sp₁ (by decide))
    (by rw [b800023b4_x11 g₂]; exact ptrEq fr₂ (by rw [R₁.x23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b800023b4_x12 g₂]; exact lenEq fr₂ (by rw [R₁.x23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b800023b4_x13 g₂]; exact R₁.x24)
  swap
  · exact ⟨t₂, Q₁.trans (p₂.trans q₂), Or.inr d⟩
  have Q₂ := Q₁.trans (p₂.trans q₂)
  have R₂ := (R₁.keeps (b800023b4_keeps g₂)).pres hp₂
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 2656 := T₂.m.m.inv.sp
  -- the third term
  obtain ⟨v₃, p₃, g₃⟩ := Sym.BlockSpec.reaches b800023f4_spec
    (by rw [pc₂, returnAddress_eq, b800023b4_x1 g₂]; decide) (by
      rv_eval [sp₂, R₂.x23]
      and_intros <;> valid_access hval [hb1])
  have fr₃ := mfr hpre sp₂ (N := 1728) (M := 928) (by decide) (b800023f4_frame g₃ (by rw [sp₂]; addr_omega [hb1]))
  obtain ⟨S₃, -, K₃⟩ := T₂.blk hpre fr₃ (by mem_tac [sp₂] (b800023f4_m_x2_1728 g₃))
    (by mem_tac [sp₂] (b800023f4_m_x2_1736 g₃)) (by mem_tac [sp₂] (b800023f4_m_x2_1744 g₃))
    (b800023f4_keeps g₃ .x2 (by decide))
  obtain ⟨t₃, q₃, ⟨pc₃, hp₃, T₃, K₃', -⟩ | d⟩ := S₃.asc hA hpre (q := s.getReg .x2 - 176) (g := LayoutMirror.prodRust 6 8 0)
    (by simp) ⟨_, _, rfl⟩ (b800023f4_pc g₃)
    (by rw [b800023f4_x10 g₃]; exact spAdd hpre sp₂ (by decide))
    (by rw [b800023f4_x11 g₃]; exact ptrEq fr₃ (by rw [R₂.x23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b800023f4_x12 g₃]; exact lenEq fr₃ (by rw [R₂.x23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b800023f4_x13 g₃]; exact R₂.x24)
  swap
  · exact ⟨t₃, Q₂.trans (p₃.trans q₃), Or.inr d⟩
  have Q₃ := Q₂.trans (p₃.trans q₃)
  have R₃ := (R₂.keeps (b800023f4_keeps g₃)).pres hp₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := T₃.m.m.inv.sp
  -- the fourth term
  obtain ⟨v₄, p₄, g₄⟩ := Sym.BlockSpec.reaches b80002434_spec
    (by rw [pc₃, returnAddress_eq, b800023f4_x1 g₃]; decide) (by
      rv_eval [sp₃, R₃.x23]
      and_intros <;> valid_access hval [hb1])
  have fr₄ := mfr hpre sp₃ (N := 1728) (M := 928) (by decide) (b80002434_frame g₄ (by rw [sp₃]; addr_omega [hb1]))
  obtain ⟨S₄, -, K₄⟩ := T₃.blk hpre fr₄ (by mem_tac [sp₃] (b80002434_m_x2_1728 g₄))
    (by mem_tac [sp₃] (b80002434_m_x2_1736 g₄)) (by mem_tac [sp₃] (b80002434_m_x2_1744 g₄))
    (b80002434_keeps g₄ .x2 (by decide))
  obtain ⟨t₄, q₄, ⟨pc₄, hp₄, T₄, K₄', -⟩ | d⟩ := S₄.asc hA hpre (q := s.getReg .x2 - 152) (g := LayoutMirror.prodRust 5 0 2)
    (by simp) ⟨_, _, rfl⟩ (b80002434_pc g₄)
    (by rw [b80002434_x10 g₄]; exact spAdd hpre sp₃ (by decide))
    (by rw [b80002434_x11 g₄]; exact ptrEq fr₄ (by rw [R₃.x23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002434_x12 g₄]; exact lenEq fr₄ (by rw [R₃.x23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002434_x13 g₄]; exact R₃.x24)
  swap
  · exact ⟨t₄, Q₃.trans (p₄.trans q₄), Or.inr d⟩
  have Q₄ := Q₃.trans (p₄.trans q₄)
  have R₄ := (R₃.keeps (b80002434_keeps g₄)).pres hp₄
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 2656 := T₄.m.m.inv.sp
  -- the fifth term
  obtain ⟨v₅, p₅, g₅⟩ := Sym.BlockSpec.reaches b80002474_spec
    (by rw [pc₄, returnAddress_eq, b80002434_x1 g₄]; decide) (by
      rv_eval [sp₄, R₄.x23]
      and_intros <;> valid_access hval [hb1])
  have fr₅ := mfr hpre sp₄ (N := 1728) (M := 928) (by decide) (b80002474_frame g₅ (by rw [sp₄]; addr_omega [hb1]))
  obtain ⟨S₅, -, K₅⟩ := T₄.blk hpre fr₅ (by mem_tac [sp₄] (b80002474_m_x2_1728 g₅))
    (by mem_tac [sp₄] (b80002474_m_x2_1736 g₅)) (by mem_tac [sp₄] (b80002474_m_x2_1744 g₅))
    (b80002474_keeps g₅ .x2 (by decide))
  obtain ⟨t₅, q₅, ⟨pc₅, hp₅, T₅, K₅', -⟩ | d⟩ := S₅.asc hA hpre (q := s.getReg .x2 - 128) (g := LayoutMirror.prodRust 6 1 0)
    (by simp) ⟨_, _, rfl⟩ (b80002474_pc g₅)
    (by rw [b80002474_x10 g₅]; exact spAdd hpre sp₄ (by decide))
    (by rw [b80002474_x11 g₅]; exact ptrEq fr₅ (by rw [R₄.x23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002474_x12 g₅]; exact lenEq fr₅ (by rw [R₄.x23]; rv_eval []) (by apart_tac [hb1]) (by addr_omega [hb1]))
    (by rw [b80002474_x13 g₅]; exact R₄.x24)
  swap
  · exact ⟨t₅, Q₄.trans (p₅.trans q₅), Or.inr d⟩
  have H := h.hlo₂
  have hn1 := T₁.hH
  refine ⟨t₅, Q₄.trans (p₅.trans q₅), Or.inl ⟨by rw [pc₅, returnAddress_eq, b80002474_x1 g₅]; decide,
    T₅, ?_, (R₄.keeps (b80002474_keeps g₅)).pres hp₅⟩⟩
  exact K₁.trans (K₁'.trans (K₂.mono T₁.hH |>.trans (K₂'.trans (K₃.mono T₂.hH |>.trans (K₃'.trans
    (K₄.mono T₃.hH |>.trans (K₄'.trans (K₅.mono T₄.hH |>.trans K₅'))))))))

end Rv64Verifier.Proofs.Walk
