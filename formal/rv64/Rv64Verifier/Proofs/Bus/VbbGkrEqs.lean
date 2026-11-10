import Rv64Verifier.Proofs.Bus.VbbGkrClaim

/-!
# `verify_bus_balance`: an iteration's `equalities`

`point.iter().map(|r| Some(r)).collect()`, inlined: `try_allocate_in` for the point's length
(32-byte `Option<E>`s), `reserve` (with room already), and the loop at `0x80006754` writing
`Some(r)` (tag `1`, then `r`) per coordinate, to `0x8000677c`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The fill loop at `0x80006754` after `i` of the `len` coordinates at `pp`, the buffer at `B`. -/
structure Fill (v w : MachineState) (B pp : Word) (len : Nat) (xs : List E) (i : Nat) : Prop where
  x10 : w.getReg .x10 = B + BitVec.ofNat 64 (32 * i) + 8
  x27 : w.getReg .x27 = pp + BitVec.ofNat 64 (24 * i)
  x11 : w.getReg .x11 = pp + BitVec.ofNat 64 (24 * len)
  x24 : w.getReg .x24 = 1
  regs : ∀ r ∈ ([.x2, .x9, .x14, .x15, .x19, .x20, .x21, .x25] : List Reg),
    w.getReg r = v.getReg r
  done : ∀ j < i, optEAt w (B + BitVec.ofNat 64 (32 * j)) = some (xs.getD j 0)
  frame : DFrame v w (Within · B (32 * i))

theorem fillStep {v w : MachineState} {B pp : Word} {len : Nat} {xs : List E} {i : Nat}
    (hB : ValidMemRange B (4 * len)) (hpp : ValidMemRange pp (3 * len))
    (hap : Apart B (32 * len) pp (24 * len)) (hBb : B.toNat + 32 * len < 2 ^ 64)
    (hppb : pp.toNat + 24 * len < 2 ^ 64) (hel : eListAt v pp len = xs)
    (h : Fill v w B pp len xs i) (hi : i < len) (hpc : w.pc = 0x80006754) :
    ∃ w', Reaches Image.code w w' ∧ Fill v w' B pp len xs (i + 1) ∧
      w'.pc = if i + 1 = len then 0x8000677c else 0x80006754 := by
  have x10 := h.x10
  have x27 := h.x27
  obtain ⟨w', hrw, h₁⟩ := Sym.BlockSpec.reaches b80006754_spec hpc (by
    rv_eval [x10, x27]
    and_intros <;> first
      | valid_access hB [hi, hBb]
      | valid_access hpp [hi, hppb]
      | addr_omega [hap, hi, hBb, hppb])
  have k₁ := b80006754_keeps h₁
  have fr := b80006754_frame h₁ (by rw [x10]; addr_omega [hi, hBb])
  rw [x10, show B + BitVec.ofNat 64 (32 * i) + 8 - 8 = B + BitVec.ofNat 64 (32 * i) by
    bv_omega] at fr
  have fr' : DFrame w w' (Within · (B + BitVec.ofNat 64 (32 * i)) 32) := DFrame.of_memFrame fr
  have hm (a : Word) (ha : ∀ t < 8, ¬ Within (a + BitVec.ofNat 64 t) B (32 * (i + 1))) :
      w'.getMem a = v.getMem a := by
    rw [fr' a fun t ht hw ↦ ha t ht (by addr_omega [hw, hi, hBb])]
    exact h.frame a fun t ht hw ↦ ha t ht (by addr_omega [hw, hi, hBb])
  -- the coordinate read
  have hr (j : Nat) (hj : j + 8 ≤ 24) : w.getMem (pp + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 j) =
      v.getMem (pp + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 j) :=
    h.frame _ fun t ht hw ↦ by addr_omega [hw, hap, hi, hBb, hppb, hj, ht]
  have hx : eAt v (pp + BitVec.ofNat 64 (24 * i)) = xs.getD i 0 := by
    rw [← hel, List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hi)]
    simp [eListAt]
  have m0 := b80006754_m_x10_0 h₁
  have m8 := b80006754_m_x10_8 h₁
  have m16 := b80006754_m_x10_16 h₁
  have mn := b80006754_m_x10_n8 h₁
  rw [x10, x27] at m0 m8 m16
  rw [x10] at mn
  refine ⟨w', hrw, {
    x10 := by rw [b80006754_x10 h₁, x10]; bv_omega
    x27 := by rw [b80006754_x27 h₁, x27]; bv_omega
    x11 := by rw [k₁ .x11 (by decide)]; exact h.x11
    x24 := by rw [k₁ .x24 (by decide)]; exact h.x24
    regs := fun r hr' ↦ by rw [k₁ r (mem_of_mem hr' _)]; exact h.regs r hr'
    done := fun j hj ↦ ?_
    frame := hm }, ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [← h.done j hj]
      unfold optEAt
      have e0 : w'.getMem (B + BitVec.ofNat 64 (32 * j)) = w.getMem (B + BitVec.ofNat 64 (32 * j)) :=
        fr' _ fun t ht hw ↦ by addr_omega [hw, hj, hi, hBb, ht]
      rw [e0]
      exact congrArg _ (congrArg _ (eAt_congr (fr' _ fun t ht hw ↦ by addr_omega [hw, hj, hi, hBb, ht])
        (fr' _ fun t ht hw ↦ by addr_omega [hw, hj, hi, hBb, ht])
        (fr' _ fun t ht hw ↦ by addr_omega [hw, hj, hi, hBb, ht])))
    · unfold optEAt
      rw [show B + BitVec.ofNat 64 (32 * j) = B + BitVec.ofNat 64 (32 * j) + 8 - 8 by bv_omega, mn,
        h.x24, ite_eq_right_of_eq_false _ _ (by decide)]
      rw [← hx]
      refine congrArg some (eAt_congr ?_ ?_ ?_)
      · rw [show B + BitVec.ofNat 64 (32 * j) + 8 - 8 + 8 = B + BitVec.ofNat 64 (32 * j) + 8 by
          bv_omega, m0]
        simpa using hr 0 (by omega)
      · rw [show B + BitVec.ofNat 64 (32 * j) + 8 - 8 + 8 + 8 = B + BitVec.ofNat 64 (32 * j) + 8 + 8
          by bv_omega, m8]
        exact hr 8 (by omega)
      · rw [show B + BitVec.ofNat 64 (32 * j) + 8 - 8 + 8 + 16 = B + BitVec.ofNat 64 (32 * j) + 8 + 16
          by bv_omega, m16]
        exact hr 16 (by omega)
  · by_cases he : i + 1 = len
    · simp only [he, ↓reduceIte]
      exact b80006754_pc_not_taken h₁ (by rw [x27, h.x11, ← he]; bv_omega)
    · simp only [he, ↓reduceIte]
      exact b80006754_pc_taken h₁ (by
        rw [x27, h.x11]
        intro hc
        have := congrArg BitVec.toNat hc
        apply he
        addr_omega [this, hi, hppb])

theorem fillLoop {v : MachineState} {B pp : Word} {len : Nat} {xs : List E}
    (hB : ValidMemRange B (4 * len)) (hpp : ValidMemRange pp (3 * len))
    (hap : Apart B (32 * len) pp (24 * len)) (hBb : B.toNat + 32 * len < 2 ^ 64)
    (hppb : pp.toNat + 24 * len < 2 ^ 64) (hel : eListAt v pp len = xs) :
    ∀ m i w, i + m = len → i < len → Fill v w B pp len xs i → w.pc = 0x80006754 →
      ∃ w', Reaches Image.code w w' ∧ Fill v w' B pp len xs len ∧ w'.pc = 0x8000677c := by
  intro m
  induction m with
  | zero => intro i w h1 h2; omega
  | succ m ih =>
    intro i w h1 h2 h hpc
    obtain ⟨w₁, hr₁, h₁, hpc₁⟩ := fillStep hB hpp hap hBb hppb hel h h2 hpc
    by_cases he : i + 1 = len
    · simp only [he, ↓reduceIte] at hpc₁
      rw [he] at h₁
      exact ⟨w₁, hr₁, h₁, hpc₁⟩
    · simp only [he, ↓reduceIte] at hpc₁
      obtain ⟨w₂, hr₂, h₂⟩ := ih (i + 1) w₁ (by omega) (by omega) h₁ hpc₁
      exact ⟨w₂, hr₁.trans hr₂, h₂⟩

/-- A step whose writes `X` lie in what it allocates writes only `A`. -/
theorem StepR.absorb {s v w : MachineState} {A X : Word → Prop}
    (st : StepR s v w fun a ↦ A a ∨ X a) (hX : ∀ a, X a → Fresh v w a) : StepR s v w A :=
  ⟨st.frame.mono fun a ha ↦ by
    rcases ha with (ha | ha) | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hX a ha))))
    · exact Or.inr ha, st.heap, st.mono, st.sp⟩

/-- At `0x8000677c`: `equalities` in `a4`/`a5`, a buffer allocated in the iteration. -/
structure AtEqs (s u v : MachineState) (k : Start) (cnt : E) (P : Word) (st : GkrState)
    (comb : E) : Prop where
  ctx : Ctx s v k cnt P
  regs : ∀ r ∈ ([.x9, .x20, .x21, .x24, .x25] : List Reg), v.getReg r = u.getReg r
  combAt : eAt v (s.getReg .x2 - BitVec.ofNat 64 128) = comb
  claimAt : eAt v (s.getReg .x2 - BitVec.ofNat 64 152) = polyEvalRust st.values comb
  valuesPtr : v.getMem (s.getReg .x2 - 1280) = P
  eqs : optEListAt v (v.getReg .x14) (v.getReg .x15).toNat = st.point.map some
  eqLen : v.getReg .x15 = u.getReg .x21
  eqBuf : NewBuf u v (v.getReg .x14) (32 * (v.getReg .x15).toNat) 8
  step : StepR s u v (Scratch s)

theorem eqsStep (hTA : TryAllocZeroedSpec) (hRF : ReserveFastSpec 0x8001086c)
    {s u v : MachineState} {k : Start} {cnt : E} {P c : Word} {st : GkrState} {comb : E}
    (hpre : BusBalancePre s) (h : AtAlloc s u v k cnt P c st comb) (hpc : v.pc = 0x800049ac)
    (h19 : u.getReg .x19 = P) (h24 : u.getReg .x24 = 1) :
    ∃ w, Reaches Image.code v w ∧ (Dead Image.code w ∨
      (w.pc = 0x8000677c ∧ AtEqs s u w k cnt P st comb)) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have C := h.ctx
  have I := C.inv
  have sp := I.sp
  -- `try_allocate_in`
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := tryAllocStack) hpre I (n := 24) (k := 608)
    (by omega) (by omega) (by omega) (by decide)
  have pre : TryAllocPre .x13 .x14 v := {
    heap := I.heap
    out := by rw [h.x10]; exact regionRange o1 (Nat.le_refl _) (by omega) (by addr_omega [hb1, hb3])
    align := by rw [h.x13]; decide
    size := by rw [h.x14]; decide
    stack := hpre.stack.sub 1344 sp (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [h.x10]; exact o2
    outStack := by rw [h.x10]; exact o3 }
  obtain ⟨v₁, hr₁, ⟨hpc₁, hp₁, post, -⟩ | hd⟩ := hTA.call (Reaches.refl v) hpc pre
  swap
  · exact ⟨v₁, hr₁, Or.inl hd⟩
  have hsl : stackLo v tryAllocStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 48) := by
    simp only [stackLo, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fr₁ := DFrame.of_byteFrame post.frame
  rw [h.x10, hsl] at fr₁
  have st₁ : StepR s v v₁ (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 24) :=
    ⟨fr₁.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ha))), post.heap, post.mono, hp₁.reg .x2⟩
  have J₁ := I.afterR hpre (frameW_slot hpre (k := 608) (n := 24) (by omega) (by omega)) st₁
  have sp₁ : v₁.getReg .x2 = s.getReg .x2 - 1344 := J₁.sp
  have hpc₁' : v₁.pc = 0x800066f4 := by rw [hpc₁, returnAddress_eq, h.x1]; decide
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800066f4_spec hpc₁' (by
    rv_eval [sp₁]
    valid_access hval [hb1])
  have k₂ := b800066f4_keeps h₂
  have m₂ := b800066f4_mem_same h₂
  have e736 : s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  by_cases ht : v₁.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0
  swap
  · obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800066fc_spec
      (b800066f4_pc_not_taken h₂ (by rw [sp₁, e736]; exact ht)) trivial
    exact ⟨u₃, hr₁.trans (hr₂.trans hr₃), Or.inl (dead_of_fetch (by
      rw [b800066fc_pc h₃]; exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  obtain ⟨hcap, hbuf⟩ := post.ok (by rw [h.x10]; exact ht)
  rw [h.x10, h.x11] at hcap
  rw [h.x10, h.x11, h.x14, h.x13, show (8 : Word).toNat = 8 from rfl,
    show (32 : Word).toNat = 32 from rfl] at hbuf
  have I₂ := J₁.same m₂ (k₂ .x2 (by decide))
  -- the `Vec`'s header
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 1344 := I₂.sp
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006700_spec
    (b800066f4_pc_taken h₂ (by rw [sp₁, e736]; exact ht)) (by
      rv_eval [sp₂]
      and_intros <;> valid_access hval [hb1])
  have k₃ := b80006700_keeps h₃
  have fr₃ := b80006700_frame h₃ (by rw [sp₂]; addr_omega [hb1])
  rw [sp₂, e736] at fr₃
  have st₃ : StepR s u₂ u₃ (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 24) :=
    StepR.ofMemFrame I₂.heap fr₃ (fun _ h ↦ h) (by addr_omega [hb1]) (k₃ .x2 (by decide))
  have I₃ := I₂.afterR hpre (frameW_slot hpre (k := 608) (n := 24) (by omega) (by omega)) st₃
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 1344 := I₃.sp
  have e744 : s.getReg .x2 - 1344 + 744 = s.getReg .x2 - BitVec.ofNat 64 608 + 8 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e752 : s.getReg .x2 - 1344 + 752 = s.getReg .x2 - BitVec.ofNat 64 608 + 16 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have c0 := b80006700_m_x2_736 h₃
  have c1 := b80006700_m_x2_744 h₃
  have c2 := b80006700_m_x2_752 h₃
  rw [sp₂, e736, e744, m₂] at c0
  rw [sp₂, e744, e752, m₂] at c1
  rw [sp₂, e752] at c2
  rw [hcap] at c0
  have hv608 : ValidMemRange (s.getReg .x2 - BitVec.ofNat 64 608) 3 :=
    regionRange o1 (Nat.le_refl _) (by omega) (by addr_omega [hb1, hb3])
  have x21₃ : u₃.getReg .x21 = u.getReg .x21 := by
    rw [k₃ .x21 (by decide), k₂ .x21 (by decide), hp₁ .x21 (by decide)]
    exact h.regs .x21 (by decide)
  -- `reserve`, with room already
  obtain ⟨u₄, hr₄, ⟨hpc₄, hp₄, -, hm₄⟩ | hd⟩ := hRF.call (Reaches.refl u₃) (b80006700_pc h₃)
    ⟨by rw [b80006700_x10 h₃, sp₂, e736]; exact hv608, by
      rw [b80006700_x10 h₃, sp₂, e736, b80006700_x11 h₃, k₂ .x21 (by decide),
        hp₁ .x21 (by decide), h.regs .x21 (by decide)]
      simp only [vecLen, vecCap]
      rw [c0, c2]
      simp⟩
  swap
  · exact ⟨u₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl hd⟩
  have I₄ := I₃.same hm₄ (hp₄.reg .x2)
  have sp₄ : u₄.getReg .x2 = s.getReg .x2 - 1344 := I₄.sp
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80006724_spec
    (by rw [hpc₄, returnAddress_eq, b80006700_x1 h₃]; decide) (by
      rv_eval [sp₄]
      and_intros <;> valid_access hval [hb1])
  have k₅ := b80006724_keeps h₅
  have fr₅ := b80006724_frame h₅ (by rw [sp₄]; addr_omega [hb1])
  rw [sp₄, show s.getReg .x2 - 1344 + 64 = s.getReg .x2 - 1280 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at fr₅
  have st₅ : StepR s u₄ u₅ (Within · (s.getReg .x2 - 1280) 8) :=
    StepR.ofMemFrame I₄.heap fr₅ (fun _ h ↦ h) (by addr_omega [hb1]) (k₅ .x2 (by decide))
  have p64 := b80006724_m_x2_64 h₅
  rw [sp₄, show s.getReg .x2 - 1344 + 64 = s.getReg .x2 - 1280 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at p64
  have x14₅ := b80006724_x14 h₅
  have x15₅ := b80006724_x15 h₅
  rw [sp₄, e744, hm₄, c1] at x14₅
  rw [sp₄, e752, hm₄, c2] at x15₅
  have rg₅ (r : Reg) (hr : r ∈ ([.x9, .x19, .x20, .x21, .x24, .x25, .x27] : List Reg)) :
      u₅.getReg r = u.getReg r := by
    rw [k₅ r (mem_of_mem hr _), hp₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _),
      k₂ r (mem_of_mem hr _), hp₁ r (mem_of_mem hr _), h.regs r hr]
  have stPre : StepR s v u₅ fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24 ∨
      Within a (s.getReg .x2 - 1280) 8 :=
    ((((st₁.trans (StepR.same m₂ J₁.heap (k₂ .x2 (by decide)))).trans st₃).trans
      (StepR.same hm₄ I₃.heap (hp₄.reg .x2))).trans st₅).weaken fun a ha ↦ by
        rcases ha with ((((ha | ha) | ha) | ha) | ha)
        · exact Or.inl ha
        · exact False.elim ha
        · exact Or.inl ha
        · exact False.elim ha
        · exact Or.inr ha
  have fW : FrameW s fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24 ∨
      Within a (s.getReg .x2 - 1280) 8 := fun a ha ↦ by
    rcases ha with ha | ha <;> addr_omega [ha, hb1]
  have I₅ := I.afterR hpre fW stPre
  have hsc (a : Word) (ha : Within a (s.getReg .x2 - BitVec.ofNat 64 608) 24 ∨
      Within a (s.getReg .x2 - 1280) 8) : Scratch s a := by
    rcases ha with ha | ha
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
  have pt := h.point.keepG hpre stPre fW
  have hmiss (j : Nat) (hj : j = 128 ∨ j = 152) : ∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) 24 →
      ¬ (Within y (s.getReg .x2 - BitVec.ofNat 64 608) 24 ∨ Within y (s.getReg .x2 - 1280) 8) :=
    fun y hy hw ↦ by rcases hj with rfl | rfl <;> rcases hw with hw | hw <;> addr_omega [hy, hw, hb1]
  have hbx := hbuf
  simp only [NewBuf] at hbx
  have hlenle := pt.le
  have hpb := h.point.buf
  simp only [NewBuf] at hpb
  have hhv₁ := post.heap.hi
  have hmv := h.ctx.inv.mono
  by_cases hz : u.getReg .x21 = 0
  · -- no coordinates
    have hpc₅ := b80006724_pc_taken h₅ (by rw [← k₅ .x21 (by decide), rg₅ .x21 (by decide), hz])
    have hpt0 : st.point = [] := by
      rw [← pt.elems, hz]; rfl
    refine ⟨u₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr ⟨hpc₅, {
      ctx := C.step hpre (stPre.weaken hsc)
      regs := fun r hr ↦ rg₅ r (mem_of_mem hr _)
      combAt := by
        rw [stPre.eAtFrame hpre (by omega) (by omega) (hmiss 128 (Or.inl rfl))]; exact h.combAt
      claimAt := by
        rw [stPre.eAtFrame hpre (by omega) (by omega) (hmiss 152 (Or.inr rfl))]; exact h.claimAt
      valuesPtr := by rw [p64, ← k₅ .x19 (by decide), rg₅ .x19 (by decide), h19]
      eqs := by rw [x15₅, hpt0]; rfl
      eqLen := by rw [x15₅, hz]
      eqBuf := ⟨by rw [x14₅]; exact hbx.1, Or.inl (by rw [x15₅]; rfl)⟩
      step := (h.step.trans (stPre.weaken hsc)).weaken fun a ha ↦ by
        rcases ha with ha | ha <;> exact ha }⟩⟩
  -- the fill loop
  have hpc₅ := b80006724_pc_not_taken h₅ (by rw [← k₅ .x21 (by decide), rg₅ .x21 (by decide)]; exact hz)
  obtain ⟨u₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80006734_spec hpc₅ trivial
  have k₆ := b80006734_keeps h₆
  have m₆ := b80006734_mem_same h₆
  set B := v₁.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 16) with hB
  set pp := u.getReg .x27 with hpp
  set len := (u.getReg .x21).toNat with hlen
  have hl0 : 0 < len := by
    rw [hlen]; exact Nat.pos_of_ne_zero fun h0 ↦ hz (BitVec.eq_of_toNat_eq h0)
  obtain ⟨hB8, hBlo, hBhi⟩ : B.toNat % 8 = 0 ∧ heapNext v ≤ B.toNat ∧
      B.toNat + len * 32 ≤ heapNext v₁ := by
    rcases hbx.2 with h0 | hb
    · omega
    · exact ⟨hbx.1, hb⟩
  obtain ⟨hp8, hplo, hphi⟩ : pp.toNat % 8 = 0 ∧ heapNext s ≤ pp.toNat ∧
      pp.toNat + c.toNat * 24 ≤ heapNext v := by
    rcases hpb.2 with h0 | hb
    · omega
    · exact ⟨hpb.1, hb⟩
  have hm5 := stPre.mono
  have hm1 := st₁.mono
  have hlo := hpre.heap.lo
  have hh5 := I₅.heap.hi
  simp only [heapNext, heapEnd, heapStart] at hBlo hBhi hplo hphi hm5 hm1 hlo hh5 hmv hhv₁
  have hvB : ValidMemRange B (4 * len) :=
    heapRange hB8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have hvp : ValidMemRange pp (3 * len) :=
    heapRange hp8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have hel : eListAt u₆ pp len = st.point := by
    rw [← pt.elems]
    exact eListAt_congr fun i _ ↦ eAt_congr (m₆ _) (m₆ _) (m₆ _)
  have hmul : u.getReg .x21 * 16 + u.getReg .x21 * 8 = BitVec.ofNat 64 (24 * len) := by
    apply BitVec.eq_of_toNat_eq
    have e16 : (16 : Word).toNat = 16 := rfl
    have e8 : (8 : Word).toNat = 8 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, e16, e8, hlen]
    omega
  have F0 : Fill u₆ u₆ B pp len st.point 0 := {
    x10 := by rw [b80006734_x10 h₆, x14₅, x15₅]; simp
    x27 := by rw [k₆ .x27 (by decide), rg₅ .x27 (by decide)]; simp; exact hpp.symm
    x11 := by
      rw [b80006734_x11 h₆, rg₅ .x27 (by decide), rg₅ .x21 (by decide), hmul]
    x24 := by rw [k₆ .x24 (by decide), rg₅ .x24 (by decide), h24]
    regs := fun _ _ ↦ rfl
    done := fun j hj ↦ absurd hj (Nat.not_lt_zero _)
    frame := DFrame.refl _ _ }
  obtain ⟨w, hrw, Fw, hpcw⟩ := fillLoop hvB hvp (by simp only [Apart]; omega) (by omega)
    (by omega) hel len 0 u₆ (by omega) hl0 F0 (b80006734_pc h₆)
  -- the fill as a step allocating nothing, its writes in what the iteration allocated
  have hnw : heapNext w = heapNext u₆ := by
    simp only [heapNext]
    rw [Fw.frame nextAddr fun t ht hw ↦ by simp only [nextAddr] at hw; addr_omega [hw, ht, hBhi, hhv₁]]
  have hn6 : heapNext u₆ = heapNext u₅ := by simp only [heapNext, m₆]
  have stF : StepR s u₅ w fun a ↦ Within a B (32 * len) :=
    ⟨(DFrame.of_same m₆ _).trans Fw.frame fun a ha ↦ Or.inl ha,
      ⟨by rw [hnw, hn6]; exact I₅.heap.lo, by rw [hnw, hn6]; exact I₅.heap.hi⟩,
      by rw [hnw, hn6], by rw [Fw.regs .x2 (by decide), k₆ .x2 (by decide)]⟩
  have hm15 : heapNext v₁ ≤ heapNext u₅ :=
    ((((StepR.same (s := s) (A := fun _ ↦ False) m₂ J₁.heap (k₂ .x2 (by decide))).trans st₃).trans
      (StepR.same (A := fun _ ↦ False) hm₄ I₃.heap (hp₄.reg .x2))).trans st₅).mono
  have stAll : StepR s v w (Scratch s) :=
    ((stPre.trans stF).absorb fun a ha ↦ by
      simp only [Within] at ha
      have h1 := hnw
      simp only [Fresh, heapNext] at h1 hn6 hm15 ⊢
      exact ⟨by omega, by omega⟩).weaken hsc
  have rgw (r : Reg) (hr : r ∈ ([.x9, .x19, .x20, .x21, .x25] : List Reg)) :
      w.getReg r = u.getReg r := by
    rw [Fw.regs r (mem_of_mem hr _), k₆ r (mem_of_mem hr _), rg₅ r (mem_of_mem hr _)]
  have x15w : w.getReg .x15 = u.getReg .x21 := by
    rw [Fw.regs .x15 (by decide), b80006734_x15 h₆, x15₅, rg₅ .x21 (by decide)]
    simp
  have x14w : w.getReg .x14 = B := by rw [Fw.regs .x14 (by decide), k₆ .x14 (by decide), x14₅]
  refine ⟨w, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans hrw))))),
    Or.inr ⟨hpcw, {
    ctx := C.step hpre stAll
    regs := fun r hr ↦ by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact rgw .x9 (by decide)
      rcases List.mem_cons.mp hr with rfl | hr
      · exact rgw .x20 (by decide)
      rcases List.mem_cons.mp hr with rfl | hr
      · exact rgw .x21 (by decide)
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [Fw.x24, h24]
      rcases List.mem_cons.mp hr with rfl | hr
      · exact rgw .x25 (by decide)
      exact absurd hr (List.not_mem_nil)
    combAt := by
      rw [stF.eAtFrame hpre (by omega) (by omega) fun y hy hw ↦ by addr_omega [hy, hw, hb1, hBhi, hhv₁],
        stPre.eAtFrame hpre (by omega) (by omega) (hmiss 128 (Or.inl rfl))]
      exact h.combAt
    claimAt := by
      rw [stF.eAtFrame hpre (by omega) (by omega) fun y hy hw ↦ by addr_omega [hy, hw, hb1, hBhi, hhv₁],
        stPre.eAtFrame hpre (by omega) (by omega) (hmiss 152 (Or.inr rfl))]
      exact h.claimAt
    valuesPtr := by
      rw [stF.word hpre (fun y hy hw ↦ by addr_omega [hy, hw, hb1, hBhi, hhv₁])
        (Or.inl (by addr_omega [hb1])), p64, ← k₅ .x19 (by decide), rg₅ .x19 (by decide), h19]
    eqs := by
      rw [x14w, x15w, ← hlen, optEListAt,
        List.map_congr_left fun j hj ↦ Fw.done j (List.mem_range.mp hj)]
      have hl : st.point.length = len := by rw [← hel, eListAt_length]
      refine List.ext_getElem (by simp [hl]) fun i h1 h2 ↦ ?_
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem _ _ (by simpa [hl] using h1)]
    eqLen := x15w
    eqBuf := by
      rw [x14w, x15w, ← hlen]
      have hmu := h.step.mono
      refine ⟨hB8, Or.inr ⟨?_, ?_⟩⟩ <;> simp only [heapNext] at hnw hn6 hm15 hmu ⊢ <;> omega
    step := (h.step.trans stAll).weaken fun a ha ↦ by rcases ha with ha | ha <;> exact ha }⟩⟩


end Rv64Verifier.Proofs.Bus.VerifyBusBalance
