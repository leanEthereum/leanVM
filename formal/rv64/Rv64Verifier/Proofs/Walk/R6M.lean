import Rv64Verifier.Proofs.Walk.R6V

/-!
# `walk`: a cell's `memory` flush

The block at `0x80001df0` moves the cell's values to the values array at `sp + 2432` and branches
on the side (`VA`). On side 0, and for side 1's cell 0, the address is one `prod` into
`sp + 2240`, then `Flushes::memory(address, count, &values)` (`memTail`), back to the loop's
latch at `0x80001d60`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FormOk formOf formBuf flushesDeep OptAt)

theorem cellLanesGetD (odd : Bool) {cell : ℕ} (h : cell < 13) :
    (LayoutMirror.keccakCellLanesRust odd).getD cell (none, none) =
      LayoutMirror.keccakCellLanesAt odd cell := by
  rw [List.getD_eq_getElem?_getD, LayoutMirror.keccakCellLanesRust, List.getElem?_map,
    List.getElem?_range (by simpa [LayoutMirror.keccakCellsRust] using h)]
  rfl

/-- After `0x80001df0`: the cell's values at `sp + 2432`, `sp + 2456`, `sp + 2480`, their buffers
in order from `h0`, past what the `Flushes` reaches; `count` in `s8`. -/
structure VA (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) (σ c : Nat) (F : LayoutMirror.FlushesRust)
    (h0 h1 h2 h3 : Nat) : Prop where
  km : KM OI s u A k R Q B σ F
  kr : KR s u σ c
  x24 : u.getReg .x24 = BitVec.ofNat 64 (65 + 13 * σ + c)
  deep : ∀ x, flushesDeep u (s.getReg .x2 - 1488) x → x.toNat < h0
  v0 : SF u (s.getReg .x2 - 224) (limbForm σ (LayoutMirror.keccakCellLanesAt false c).1
    (LayoutMirror.keccakCellLanesAt true c).1) h0 h1
  v1 : SF u (s.getReg .x2 - 200) (limbForm σ (LayoutMirror.keccakCellLanesAt false c).2
    (LayoutMirror.keccakCellLanesAt true c).2) h1 h2
  v2 : SF u (s.getReg .x2 - 176) (LayoutMirror.constantRust 0) h2 h3
  le : h0 ≤ h1 ∧ h1 ≤ h2 ∧ h2 ≤ h3 ∧ h3 ≤ heapNext u

/-- The cell's values, as the mirror lists them. -/
def cellValues (σ c : Nat) : List LayoutMirror.FormRust :=
  [limbForm σ (LayoutMirror.keccakCellLanesAt false c).1 (LayoutMirror.keccakCellLanesAt true c).1,
    limbForm σ (LayoutMirror.keccakCellLanesAt false c).2 (LayoutMirror.keccakCellLanesAt true c).2,
    LayoutMirror.constantRust 0]

/-- A step that writes no value and nothing the `Flushes` reaches nor `KM`'s words. -/
theorem VA.same {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ c : Nat} {F : LayoutMirror.FlushesRust}
    {h0 h1 h2 h3 : Nat} (hpre : WalkPre s) (h : VA OI s u A k R Q B σ c F h0 h1 h2 h3)
    (hm : ∀ a, v.getMem a = u.getMem a)
    (hk : ∀ r ∈ ([.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg), v.getReg r = u.getReg r) : VA OI s v A k R Q B σ c F h0 h1 h2 h3 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have K := KM.scr hpre h.km (Rv64Verifier.Layout.DFrame.of_same hm (fun _ ↦ False))
    (fun _ h ↦ h.elim) (hk .x2 (by decide))
  have hh := h.km.m.inv.heap
  have fr := Rv64Verifier.Layout.DFrame.of_same hm (fun _ ↦ False)
  exact {
    km := K.1
    kr := h.kr.keeps' hk
    x24 := by rw [hk .x24 (by decide)]; exact h.x24
    deep := fun x hx ↦ h.deep x (by rw [← K.2.1]; exact hx)
    v0 := h.v0.frame fr (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh K.2.2.ge
    v1 := h.v1.frame fr (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh K.2.2.ge
    v2 := h.v2.frame fr (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh K.2.2.ge
    le := by rw [K.2.2]; exact h.le }

set_option maxRecDepth 8192 in
/-- The block at `0x80001df0`: the values moved to `sp + 2432`, `count` into `s8`, the branch on
the side. -/
theorem toVA {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ c : Nat} {F : LayoutMirror.FlushesRust}
    {h0 h1 h2 : Nat} (hpre : WalkPre s) (h : KM OI s u A k R Q B σ F) (r : KR s u σ c)
    (hpc : u.pc = 0x80001df0) (hσ : σ < 2)
    (hdeep : ∀ x, flushesDeep u (s.getReg .x2 - 1488) x → x.toNat < h0)
    (V : Vals s u σ c h0 h1 h2) :
    ∃ t, Reaches Image.code u t ∧ t.pc = (if σ = 0 then 0x80001e54 else 0x80001e40) ∧
      VA OI s t A k R Q B σ c F h0 h1 h2 (heapNext u) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := h.m.inv.sp
  have x8 := r.x8
  have x20 := r.x20
  have x26 := r.x26
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b80001df0_spec hpc (by
    rv_eval [sp, x8, x20, x26]
    and_intros
    all_goals first
      | valid_access hval [hb1]
      | (intro he; have := congrArg BitVec.toNat he; addr_omega [hb1, this]))
  have fr : Rv64Verifier.Layout.DFrame u t (Within · (s.getReg .x2 - 224) 72) := Expect.ldframe ht (by
    rv_eval [sp, x8, x20, x26]
    simp only [Within]
    and_intros <;> addr_omega [hb1])
  have kt := b80001df0_keeps ht
  have K := KM.scr hpre h fr (fun a ha ↦ Or.inr (Or.inr (Or.inr ha))) (kt .x2 (by decide))
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : u.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have e26 (N M : Word) (hNM : N.toNat + M.toNat = 512) : u.getReg .x26 + N = s.getReg .x2 - M := by
    rw [x26]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hNM]
  have e8 (N M : Word) (hNM : N.toNat + M.toNat = 200) : u.getReg .x8 + N = s.getReg .x2 - M := by
    rw [x8]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hNM]
  have e20 (N M : Word) (hNM : N.toNat + M.toNat = 176) : u.getReg .x20 + N = s.getReg .x2 - M := by
    rw [x20]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hNM]
  have hh := h.m.inv.heap
  have nb (lo hi : Nat) (hhi : hi ≤ heapNext u) : ∀ x, lo ≤ x.toNat → x.toNat < hi →
      ¬ Within x (s.getReg .x2 - 224) 72 := fun x _ hx hw ↦ by
    have := hh.hi; simp only [Within, heapEnd] at hw this; simp only [heapNext] at hhi this
    addr_omega [hw, hx, hhi, this, hb1]
  have le := V.le
  have W0 := V.v0.move (o := s.getReg .x2 - 224) fr
    (by rw [← e26 288 224 (by decide), b80001df0_m_x26_288 ht, e 952 1704 (by decide)])
    (by rw [show s.getReg .x2 - 224 + 8 = u.getReg .x26 + 296 by
          rw [x26]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
        b80001df0_m_x26_296 ht, show s.getReg .x2 - 1704 + 8 = u.getReg .x2 + 960 by
          rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show s.getReg .x2 - 224 + 16 = u.getReg .x26 + 304 by
          rw [x26]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
        b80001df0_m_x26_304 ht, show s.getReg .x2 - 1704 + 16 = u.getReg .x2 + 968 by
          rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (nb _ _ (by omega)) hh K.2.2.ge
  have W1 := V.v1.move (o := s.getReg .x2 - 200) fr
    (by rw [← x8, b80001df0_m_x8_0 ht, e 1024 1632 (by decide)])
    (by rw [show s.getReg .x2 - 200 + 8 = u.getReg .x8 + 8 by rw [x8],
        b80001df0_m_x8_8 ht, show s.getReg .x2 - 1632 + 8 = u.getReg .x2 + 1032 by
          rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show s.getReg .x2 - 200 + 16 = u.getReg .x8 + 16 by rw [x8],
        b80001df0_m_x8_16 ht, show s.getReg .x2 - 1632 + 16 = u.getReg .x2 + 1040 by
          rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (nb _ _ (by omega)) hh K.2.2.ge
  have W2 := V.v2.move (o := s.getReg .x2 - 176) fr
    (by rw [← x20, b80001df0_m_x20_0 ht, e 1096 1560 (by decide)])
    (by rw [show s.getReg .x2 - 176 + 8 = u.getReg .x20 + 8 by rw [x20],
        b80001df0_m_x20_8 ht, show s.getReg .x2 - 1560 + 8 = u.getReg .x2 + 1104 by
          rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [show s.getReg .x2 - 176 + 16 = u.getReg .x20 + 16 by rw [x20],
        b80001df0_m_x20_16 ht, show s.getReg .x2 - 1560 + 16 = u.getReg .x2 + 1112 by
          rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (nb _ _ le_rfl) hh K.2.2.ge
  refine ⟨t, hr, ?_, {
    km := K.1
    kr := r.keeps' kt
    x24 := by
      rw [b80001df0_x24 ht, r.x21, r.x23]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    deep := fun x hx ↦ hdeep x (by rw [← K.2.1]; exact hx)
    v0 := W0
    v1 := W1
    v2 := W2
    le := ⟨le.1, le.2.1, le.2.2, by rw [K.2.2]⟩ }⟩
  by_cases h0 : σ = 0
  · simp only [h0, ↓reduceIte]; exact b80001df0_pc_taken ht (by rw [r.x27, h0]; rfl)
  · simp only [h0, ↓reduceIte]; exact b80001df0_pc_not_taken ht (by
      rw [r.x27]; intro he; have := congrArg BitVec.toNat he
      have h00 : (0 : Word).toNat = 0 := rfl
      rw [BitVec.toNat_ofNat, h00] at this; omega)

theorem formsAt3 (u : MachineState) (p : Word) :
    Rv64Verifier.Layout.formsAt u p 3 = [formOf u p, formOf u (p + 24), formOf u (p + 48)] := by
  have h0 : p + BitVec.ofNat 64 (24 * 0) = p := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [Rv64Verifier.Layout.formsAt, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, h0]
  rfl

set_option maxRecDepth 8192 in
/-- From the `prod` call at `0x80001e84` (into `sp + 2240`, its operands in `a1..a3`) through
`Flushes::memory(address, count, &values)` to the latch at `0x80001d60`. -/
theorem memTail (hP : Rv64Verifier.Layout.ProdSpec) (hM : Rv64Verifier.Layout.MemorySpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ c : Nat} {F : LayoutMirror.FlushesRust}
    {h0 h1 h2 h3 : Nat} (hpre : WalkPre s) (h : VA OI s u A k R Q B σ c F h0 h1 h2 h3)
    (hσ : σ < 2) (hc : c < 13) (hpc : u.pc = 0x80001e84) (x10 : u.getReg .x10 = s.getReg .x2 - 416) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001d60 ∧
      KM OI s t A k R Q B σ (F.memory (LayoutMirror.prodRust (u.getReg .x11).toNat
        (u.getReg .x12).toNat (u.getReg .x13).toNat) (65 + 13 * σ + c) (cellValues σ c)) ∧
      KR s t σ c) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80001e84_spec hpc (by rv_eval [])
  have k₁ := b80001e84_keeps h₁
  have V₁ := h.same hpre (b80001e84_mem_same h₁) (fun r hr ↦ k₁ r (by revert r hr; decide))
  have I := V₁.km.m.inv
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  have sA := slotW (n := 3) hpre I (o := s.getReg .x2 - 416) (by simp only [InSlot]; addr_omega [hb1, hb3]) hn
  have pre : Rv64Verifier.Layout.ColPre u₁ := {
    heap := I.heap
    stack := stk_sub hpre I hn (by decide)
    out := by rw [k₁ .x10 (by decide), x10]; exact sA.1
    outFree := by rw [k₁ .x10 (by decide), x10]; exact sA.2.1
    outStack := by rw [k₁ .x10 (by decide), x10]; exact sA.2.2
    rodata := I.rodata hpre }
  obtain ⟨t₁, hr₁', ⟨hpc₁, hp₁, nf, fv⟩ | hd⟩ := hP u₁ (b80001e84_pc h₁) pre
  swap
  · exact ⟨t₁, hr₁.trans hr₁', Or.inr hd⟩
  rw [k₁ .x10 (by decide), x10] at nf fv
  rw [k₁ .x11 (by decide), k₁ .x12 (by decide), k₁ .x13 (by decide)] at fv
  have scrA : InScr s (s.getReg .x2 - 416) := fun x hx ↦ Or.inr (Or.inr (Or.inl (by
    simp only [Within] at hx ⊢; addr_omega [hx, hb1])))
  have K₁ := KM.call hpre V₁.km nf.frame scrA hn nf.heap nf.mono (hp₁ .x2 (by decide))
  have le := V₁.le
  have sl (o : Word) (ho : o = s.getReg .x2 - 224 ∨ o = s.getReg .x2 - 200 ∨ o = s.getReg .x2 - 176) :
      InSlot s o 24 := by
    rcases ho with rfl | rfl | rfl <;> simp only [InSlot] <;> addr_omega [hb1, hb3]
  have slA : InSlot s (s.getReg .x2 - 416) 24 := by simp only [InSlot]; addr_omega [hb1, hb3]
  have W0 := SF.call hpre I V₁.v0 nf.frame hn slA (sl _ (Or.inl rfl)) (by addr_omega [hb1])
    (by omega) nf.heap nf.mono
  have W1 := SF.call hpre I V₁.v1 nf.frame hn slA (sl _ (Or.inr (Or.inl rfl))) (by addr_omega [hb1])
    (by omega) nf.heap nf.mono
  have W2 := SF.call hpre I V₁.v2 nf.frame hn slA (sl _ (Or.inr (Or.inr rfl))) (by addr_omega [hb1])
    (by omega) nf.heap nf.mono
  have kr₁ := V₁.kr.pres hp₁
  have x24 : t₁.getReg .x24 = BitVec.ofNat 64 (65 + 13 * σ + c) := by
    rw [hp₁ .x24 (by decide)]; exact V₁.x24
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80001e8c_spec
    (by rw [hpc₁, returnAddress_eq, b80001e84_x1 h₁]; decide) (by rv_eval [])
  have m₂ := b80001e8c_mem_same h₂
  have k₂ := b80001e8c_keeps h₂
  have K₂ := KM.scr hpre K₁.1 (Rv64Verifier.Layout.DFrame.of_same m₂ (fun _ ↦ False))
    (fun _ h ↦ h.elim) (k₂ .x2 (by decide))
  have fr₂ := Rv64Verifier.Layout.DFrame.of_same m₂ (fun _ ↦ False)
  have hh₁ := nf.heap
  have A₂ := (SF.ofNew nf fv).frame fr₂ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh₁
    K₂.2.2.ge
  have W0' := W0.frame fr₂ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh₁ K₂.2.2.ge
  have W1' := W1.frame fr₂ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh₁ K₂.2.2.ge
  have W2' := W2.frame fr₂ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) hh₁ K₂.2.2.ge
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := K₁.1.m.inv.sp
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : t₁.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp₁ hNM
  have I₂ := K₂.1.m.inv
  have hm : Rv64Verifier.Layout.memoryStack ≤ 8736 := by decide
  have sF := slotW (n := 6) hpre I₂ (o := s.getReg .x2 - 1488) (by simp only [InSlot]; addr_omega [hb1, hb3]) hm
  have sA' := slotW (n := 3) hpre I₂ (o := s.getReg .x2 - 416) (by simp only [InSlot]; addr_omega [hb1, hb3]) hm
  have sV := slotW (n := 9) hpre I₂ (o := s.getReg .x2 - 224) (by simp only [InSlot]; addr_omega [hb1, hb3]) hm
  have a24 : s.getReg .x2 - 224 + 24 = s.getReg .x2 - 200 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a48 : s.getReg .x2 - 224 + 48 = s.getReg .x2 - 176 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - 1488 := by rw [b80001e8c_x10 h₂, e 1168 1488 (by decide)]
  have x11₂ : u₂.getReg .x11 = s.getReg .x2 - 416 := by rw [b80001e8c_x11 h₂, e 2240 416 (by decide)]
  have x13₂ : u₂.getReg .x13 = s.getReg .x2 - 224 := by rw [b80001e8c_x13 h₂, e 2432 224 (by decide)]
  have mpre : Rv64Verifier.Layout.MemoryPre u₂ := {
    heap := I₂.heap
    stack := stk_sub hpre I₂ hm (by decide)
    self := by rw [x10₂]; exact sF.1
    ok := by rw [x10₂]; exact K₂.1.fl.ok
    selfFree := by rw [x10₂]; exact sF.2.1
    selfStack := by rw [x10₂]; exact sF.2.2
    rodata := I₂.rodata hpre
    address := by rw [x11₂]; exact sA'.1
    addressOk := by rw [x11₂]; exact A₂.ok
    addressFree := by rw [x11₂]; exact sA'.2.1
    addressStack := by rw [x11₂]; exact sA'.2.2
    values := by rw [x13₂]; exact sV.1
    valuesOk := by
      rw [x13₂]; intro i hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · simpa using W0'.ok
      · rw [show (24 * 1 : Nat) = 24 from rfl, show BitVec.ofNat 64 24 = (24 : Word) from rfl, a24]
        exact W1'.ok
      · rw [show (24 * 2 : Nat) = 48 from rfl, show BitVec.ofNat 64 48 = (48 : Word) from rfl, a48]
        exact W2'.ok
    valuesFree := by rw [x13₂]; exact sV.2.1
    valuesStack := by rw [x13₂]; exact sV.2.2 }
  obtain ⟨t₂, hr₂', ⟨hpc₂, hp₂, g, gv⟩ | hd⟩ := hM u₂ (b80001e8c_pc h₂) mpre
  swap
  · exact ⟨t₂, hr₁.trans (hr₁'.trans (hr₂.trans hr₂')), Or.inr hd⟩
  rw [x10₂] at g gv
  rw [x11₂, x13₂, b80001e8c_x12 h₂, x24, formsAt3, a24, a48, A₂.val, W0'.val, W1'.val, W2'.val,
    K₂.1.fl.val] at gv
  have K₃ := KM.grow hpre K₂.1 g hm (hp₂ .x2 (by decide)) gv
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80001eac_spec
    (by rw [hpc₂, returnAddress_eq, b80001e8c_x1 h₂]; decide) (by rv_eval [])
  have K₄ := KM.scr hpre K₃ (Rv64Verifier.Layout.DFrame.of_same (b80001eac_mem_same h₃) (fun _ ↦ False))
    (fun _ h ↦ h.elim) (b80001eac_keeps h₃ .x2 (by decide))
  refine ⟨u₃, hr₁.trans (hr₁'.trans (hr₂.trans (hr₂'.trans hr₃))), Or.inl ⟨b80001eac_pc h₃, ?_,
    ((kr₁.keeps' k₂).pres hp₂).keeps' (b80001eac_keeps h₃)⟩⟩
  have e65 : (BitVec.ofNat 64 (65 + 13 * σ + c)).toNat = 65 + 13 * σ + c := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [e65] at K₄
  exact K₄.1

/-- One cell of `flushes_keccak`'s loop on side `σ`, as the mirror runs it. -/
def cellStep (σ : Nat) (F : LayoutMirror.FlushesRust) (c : Nat) : LayoutMirror.FlushesRust :=
  LayoutMirror.keccakCellRust σ (sideLanes σ) (10 + σ) (sideMissing σ) F c

theorem cellStep_zero (F : LayoutMirror.FlushesRust) {c : Nat} (hc : c < 13) :
    cellStep 0 F c = F.memory (LayoutMirror.keccakAddressRust c) (65 + 13 * 0 + c) (cellValues 0 c) := by
  simp only [cellStep, LayoutMirror.keccakCellRust, cellLanesGetD _ hc]
  rfl

theorem cellStep_one (F : LayoutMirror.FlushesRust) :
    cellStep 1 F 0 = F.memory (LayoutMirror.prodRust 1 9 0) (65 + 13 * 1 + 0) (cellValues 1 0) := by
  simp only [cellStep, LayoutMirror.keccakCellRust, cellLanesGetD _ (show 0 < 13 by decide)]
  rfl

/-- The address `prod` of side 0's cell `c`, its operands as the code loads them. -/
theorem address_eq {c : Nat} (hc : c < 13) :
    LayoutMirror.keccakAddressRust c = if c < 4 then LayoutMirror.prodRust 1 (2 + c) 0
      else if c < 8 then LayoutMirror.prodRust 1 6 (c - 4)
      else if c = 8 then LayoutMirror.prodRust 1 7 0 else LayoutMirror.prodRust 1 8 (c - 9) := by
  unfold LayoutMirror.keccakAddressRust
  by_cases h4 : c < 4
  · simp only [h4, ↓reduceIte]
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  · by_cases h8 : c < 8
    · simp only [h4, h8, ↓reduceIte]; rfl
    · by_cases h9 : c = 8
      · subst h9; rfl
      · simp only [h4, h8, h9, ↓reduceIte]; rfl

/-- `O_M`, in `.rodata` at `0xa00001b8`. -/
theorem oM_word {u : MachineState} (h : RodataOk u) {c : Nat} (hc : c < 4) :
    u.getMem (0xa00001b8 + BitVec.ofNat 64 (8 * c)) = BitVec.ofNat 64 (2 + c) := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
  · exact h.word (a := 0xa00001b8) (v := 2)
  · exact h.word (a := 0xa00001c0) (v := 3)
  · exact h.word (a := 0xa00001c8) (v := 4)
  · exact h.word (a := 0xa00001d0) (v := 5)

set_option maxRecDepth 8192 in
/-- Side 0's cells, and side 1's cell 0: the address, then `memory`, to the latch. -/
theorem memPath (hP : Rv64Verifier.Layout.ProdSpec) (hM : Rv64Verifier.Layout.MemorySpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ c : Nat} {F : LayoutMirror.FlushesRust}
    {h0 h1 h2 h3 : Nat} (hpre : WalkPre s) (h : VA OI s u A k R Q B σ c F h0 h1 h2 h3)
    (hσ : σ < 2) (hc : c < 13) (hmem : σ = 0 ∨ c = 0)
    (hpc : u.pc = if σ = 0 then 0x80001e54 else 0x80001e40) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001d60 ∧
      KM OI s t A k R Q B σ (cellStep σ F c) ∧ KR s t σ c) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := h.km.m.inv.sp
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : u.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have x23 := h.kr.x23
  have c23 : (u.getReg .x23).toNat = c := by rw [x23, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have tail (v : MachineState) (hr : Reaches Image.code u v) (hv : VA OI s v A k R Q B σ c F h0 h1 h2 h3)
      (hpcv : v.pc = 0x80001e84) (x10 : v.getReg .x10 = u.getReg .x2 + 2240)
      (hF : F.memory (LayoutMirror.prodRust (v.getReg .x11).toNat (v.getReg .x12).toNat
        (v.getReg .x13).toNat) (65 + 13 * σ + c) (cellValues σ c) = cellStep σ F c) :
      ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001d60 ∧
        KM OI s t A k R Q B σ (cellStep σ F c) ∧ KR s t σ c) ∨ Dead Image.code t) := by
    obtain ⟨t, hr', ht⟩ := memTail hP hM hpre hv hσ hc hpcv (by rw [x10, e 2240 416 (by decide)])
    rw [hF] at ht
    exact ⟨t, hr.trans hr', ht⟩
  have kk (l : List Reg) (v w : MachineState) (hk : ∀ r ∈ l, v.getReg r = w.getReg r)
      (hl : ∀ q ∈ ([.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
        List Reg), q ∈ l := by decide) :
      ∀ r ∈ ([.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
        List Reg), v.getReg r = w.getReg r := fun r hr ↦ hk r (hl r hr)
  by_cases hs : σ = 0
  · subst hs
    simp only [↓reduceIte] at hpc
    obtain ⟨v₁, r₁, g₁⟩ := Sym.BlockSpec.reaches b80001e54_spec hpc (by rv_eval [])
    have V₁ := h.same hpre (b80001e54_mem_same g₁) (kk _ _ _ (b80001e54_keeps g₁))
    have k₁ := b80001e54_keeps g₁
    have toN (x : Word) (n : Nat) (hx : x = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) : x.toNat = n := by
      rw [hx, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn
    by_cases h4 : c < 4
    · obtain ⟨v₂, r₂, g₂⟩ := Sym.BlockSpec.reaches b80001e5c_spec
        (b80001e54_pc_not_taken g₁ (by have : (4 : Word).toNat = 4 := rfl; omega)) (by
          rv_eval [k₁ .x22 (by decide), h.kr.x22]
          refine ValidMemRange.access (a := 0xa00001b8) (n := 4)
            (Rv64Verifier.Layout.validMemRange_of (by decide) (Or.inr ⟨by decide, by decide⟩)) ?_ ?_ ?_ <;>
            addr_omega [h4])
      have V₂ := V₁.same hpre (b80001e5c_mem_same g₂) (kk _ _ _ (b80001e5c_keeps g₂))
      obtain ⟨v₃, r₃, g₃⟩ := Sym.BlockSpec.reaches b80001e80_spec (b80001e5c_pc g₂) (by rv_eval [])
      have V₃ := V₂.same hpre (b80001e80_mem_same g₃) (kk _ _ _ (b80001e80_keeps g₃))
      have k₃ := b80001e80_keeps g₃
      refine tail v₃ (r₁.trans (r₂.trans r₃)) V₃ (b80001e80_pc g₃)
        (by rw [k₃ .x10 (by decide), b80001e5c_x10 g₂, k₁ .x2 (by decide)]) ?_
      rw [cellStep_zero F hc, address_eq hc]
      simp only [h4, ↓reduceIte]
      rw [k₃ .x11 (by decide), k₃ .x12 (by decide), b80001e80_x13 g₃, b80001e5c_x11 g₂,
        b80001e5c_x12 g₂, k₁ .x22 (by decide), h.kr.x22, b80001e54_mem_same g₁,
        oM_word (h.km.m.inv.rodata hpre) h4, toN _ (2 + c) rfl (by omega)]
      rfl
    · obtain ⟨v₂, r₂, g₂⟩ := Sym.BlockSpec.reaches b80001eb0_spec
        (b80001e54_pc_taken g₁ (by have : (4 : Word).toNat = 4 := rfl; omega)) (by rv_eval [])
      have V₂ := V₁.same hpre (b80001eb0_mem_same g₂) (kk _ _ _ (b80001eb0_keeps g₂))
      have k₂ := b80001eb0_keeps g₂
      have c23' : (v₁.getReg .x23).toNat = c := by rw [k₁ .x23 (by decide)]; exact c23
      by_cases h8 : c < 8
      · obtain ⟨v₃, r₃, g₃⟩ := Sym.BlockSpec.reaches b80001eb8_spec
          (b80001eb0_pc_not_taken g₂ (by have : (8 : Word).toNat = 8 := rfl; omega)) (by rv_eval [])
        have V₃ := V₂.same hpre (b80001eb8_mem_same g₃) (kk _ _ _ (b80001eb8_keeps g₃))
        refine tail v₃ (r₁.trans (r₂.trans r₃)) V₃ (b80001eb8_pc g₃)
          (by rw [b80001eb8_x10 g₃, k₂ .x2 (by decide), k₁ .x2 (by decide)]) ?_
        rw [cellStep_zero F hc, address_eq hc]
        simp only [h4, h8, ↓reduceIte]
        rw [b80001eb8_x11 g₃, b80001eb8_x12 g₃, b80001eb8_x13 g₃, k₂ .x23 (by decide),
          k₁ .x23 (by decide), x23]
        have : (BitVec.ofNat 64 c - 4).toNat = c - 4 := by
          have h4' : (4 : Word).toNat = 4 := rfl
          rw [BitVec.toNat_sub, BitVec.toNat_ofNat, h4']; omega
        rw [this]
        rfl
      · obtain ⟨v₃, r₃, g₃⟩ := Sym.BlockSpec.reaches b80001ed0_spec
          (b80001eb0_pc_taken g₂ (by have : (8 : Word).toNat = 8 := rfl; omega)) (by rv_eval [])
        have V₃ := V₂.same hpre (b80001ed0_mem_same g₃) (kk _ _ _ (b80001ed0_keeps g₃))
        have k₃ := b80001ed0_keeps g₃
        by_cases h9 : c = 8
        · subst h9
          have q : v₂.getReg .x23 = v₂.getReg .x10 := by
            rw [b80001eb0_x10 g₂, k₂ .x23 (by decide), k₁ .x23 (by decide), x23]; rfl
          obtain ⟨v₄, r₄, g₄⟩ := Sym.BlockSpec.reaches b80001ed4_spec
            (b80001ed0_pc_not_taken g₃ q) (by rv_eval [])
          have V₄ := V₃.same hpre (b80001ed4_mem_same g₄) (kk _ _ _ (b80001ed4_keeps g₄))
          obtain ⟨v₅, r₅, g₅⟩ := Sym.BlockSpec.reaches b80001e80_spec (b80001ed4_pc g₄) (by rv_eval [])
          have V₅ := V₄.same hpre (b80001e80_mem_same g₅) (kk _ _ _ (b80001e80_keeps g₅))
          have k₅ := b80001e80_keeps g₅
          refine tail v₅ (r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅)))) V₅ (b80001e80_pc g₅)
            (by rw [k₅ .x10 (by decide), b80001ed4_x10 g₄, k₃ .x2 (by decide), k₂ .x2 (by decide),
              k₁ .x2 (by decide)]) ?_
          rw [cellStep_zero F hc, address_eq hc]
          simp only [↓reduceIte]
          rw [k₅ .x11 (by decide), k₅ .x12 (by decide), b80001e80_x13 g₅, b80001ed4_x11 g₄,
            b80001ed4_x12 g₄]
          rfl
        · have q : v₂.getReg .x23 ≠ v₂.getReg .x10 := by
            rw [b80001eb0_x10 g₂, k₂ .x23 (by decide), k₁ .x23 (by decide), x23]
            intro he; have h' := congrArg BitVec.toNat he
            have h8' : (8 : Word).toNat = 8 := rfl
            rw [BitVec.toNat_ofNat, h8'] at h'
            omega
          obtain ⟨v₄, r₄, g₄⟩ := Sym.BlockSpec.reaches b80001ee8_spec (b80001ed0_pc_taken g₃ q)
            (by rv_eval [])
          have V₄ := V₃.same hpre (b80001ee8_mem_same g₄) (kk _ _ _ (b80001ee8_keeps g₄))
          refine tail v₄ (r₁.trans (r₂.trans (r₃.trans r₄))) V₄ (b80001ee8_pc g₄)
            (by rw [b80001ee8_x10 g₄, k₃ .x2 (by decide), k₂ .x2 (by decide), k₁ .x2 (by decide)]) ?_
          rw [cellStep_zero F hc, address_eq hc]
          simp only [h4, h8, h9, ↓reduceIte]
          rw [b80001ee8_x11 g₄, b80001ee8_x12 g₄, b80001ee8_x13 g₄, k₃ .x23 (by decide),
            k₂ .x23 (by decide), k₁ .x23 (by decide), x23]
          have : (BitVec.ofNat 64 c - 9).toNat = c - 9 := by
            have h9' : (9 : Word).toNat = 9 := rfl
            rw [BitVec.toNat_sub, BitVec.toNat_ofNat, h9']; omega
          rw [this]
          rfl
  · have hc0 : c = 0 := hmem.resolve_left hs
    have hs1 : σ = 1 := by omega
    subst hc0 hs1
    simp only [Nat.one_ne_zero, ↓reduceIte] at hpc
    obtain ⟨v₁, r₁, g₁⟩ := Sym.BlockSpec.reaches b80001e40_spec hpc (by rv_eval [])
    have V₁ := h.same hpre (b80001e40_mem_same g₁) (kk _ _ _ (b80001e40_keeps g₁))
    have k₁ := b80001e40_keeps g₁
    obtain ⟨v₂, r₂, g₂⟩ := Sym.BlockSpec.reaches b80001e70_spec
      (b80001e40_pc_taken g₁ (by rw [x23]; rfl)) (by rv_eval [])
    have V₂ := V₁.same hpre (b80001e70_mem_same g₂) (kk _ _ _ (b80001e70_keeps g₂))
    obtain ⟨v₃, r₃, g₃⟩ := Sym.BlockSpec.reaches b80001e80_spec (b80001e70_pc g₂) (by rv_eval [])
    have V₃ := V₂.same hpre (b80001e80_mem_same g₃) (kk _ _ _ (b80001e80_keeps g₃))
    have k₃ := b80001e80_keeps g₃
    refine tail v₃ (r₁.trans (r₂.trans r₃)) V₃ (b80001e80_pc g₃)
      (by rw [k₃ .x10 (by decide), b80001e70_x10 g₂, k₁ .x2 (by decide)]) ?_
    rw [cellStep_one F, k₃ .x11 (by decide), k₃ .x12 (by decide), b80001e80_x13 g₃,
      b80001e70_x11 g₂, b80001e70_x12 g₂]
    rfl

end Rv64Verifier.Proofs.Walk
