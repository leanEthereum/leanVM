import Rv64Verifier.Proofs.Walk.R7A

/-!
# `walk`: `tables()`, KECCAK's padding (R6's tail, second part)

From `0x80001f48`: the padding's `Vec` to `sp + 952`, `memset(sp + 1312, 0, 200)`, `keccak_f` of
the zero state there, the bound check on the padding's length, and the state copied to
`sp + 1760`, to `0x80001fbc`: the lanes of `keccak_f` of zeros at `sp + 1760`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep)

theorem vecOk_move {u v : MachineState} {a a' : Word} {size align : Nat}
    (h0 : v.getMem a = u.getMem a') (h8 : v.getMem (a + 8) = u.getMem (a' + 8))
    (h16 : v.getMem (a + 16) = u.getMem (a' + 16)) (hn : heapNext u ≤ heapNext v)
    (h : VecOk u a' size align) : VecOk v a size align := by
  have hr := h.raw
  have hl := h.len
  simp only [RawVecOk, Buf, vecPtr, vecCap, vecLen] at hr hl
  refine ⟨?_, ?_⟩
  · simp only [RawVecOk, Buf, vecPtr, vecCap, h0, h8]
    exact ⟨hr.1, hr.2.imp id fun h' ↦ ⟨h'.1, Nat.le_trans h'.2 hn⟩⟩
  · simp only [vecLen, vecCap, h0, h16]; exact hl

/-- A `ZVec` whose header was copied from `o'` to `o`, its buffer untouched. -/
theorem ZVec.move {u v : MachineState} {o o' P : Word} {n L : Nat} {w : Word → Prop}
    (h : ZVec u o' n P L) (fr : Rv64Verifier.Layout.DFrame u v w)
    (h0 : v.getMem o = u.getMem o') (h8 : v.getMem (o + 8) = u.getMem (o' + 8))
    (h16 : v.getMem (o + 16) = u.getMem (o' + 16))
    (hb : ∀ x, P.toNat ≤ x.toNat → x.toNat < P.toNat + 24 * n → ¬ w x)
    (hn : heapNext u ≤ heapNext v) (hP : P.toNat + 24 * n ≤ 0x78000000) : ZVec v o n P L := by
  have hp := h.ptr
  have hl := h.len
  simp only [vecPtr, vecLen] at hp hl
  refine ⟨vecOk_move h0 h8 h16 hn h.vec, by simp only [vecPtr, h8, hp], by simp only [vecLen, h16, hl],
    fun i hi ↦ ?_, ⟨h.buf.1, h.buf.2.1, by have := h.buf.2.2; omega⟩⟩
  rw [← h.zero i hi]
  have keep (y : Word) (hy : P.toNat ≤ y.toNat ∧ y.toNat + 8 ≤ P.toNat + 24 * n) :
      v.getMem y = u.getMem y :=
    fr y (fun x hx hw ↦ hb x (by simp only [Within] at hx; omega) (by simp only [Within] at hx; omega) hw)
      (by omega)
  have hP8 := h.buf.1
  apply eAt_congr <;> refine keep _ ?_ <;> addr_omega [hi, hP, hP8]

/-- A `ZVec` across a frame that writes neither its header nor its buffer. -/
theorem ZVec.frame {u v : MachineState} {o P : Word} {n L : Nat} {w : Word → Prop}
    (h : ZVec u o n P L) (fr : Rv64Verifier.Layout.DFrame u v w)
    (hh : ∀ x, Within x o 24 → ¬ w x) (ho : o.toNat + 24 ≤ 2 ^ 64)
    (hb : ∀ x, P.toNat ≤ x.toNat → x.toNat < P.toNat + 24 * n → ¬ w x)
    (hn : heapNext u ≤ heapNext v) (hP : P.toNat + 24 * n ≤ 0x78000000) : ZVec v o n P L :=
  h.move fr (fr _ (fun x hx ↦ hh x (by simp only [Within] at hx ⊢; addr_omega [hx, ho])) (by omega))
    (fr _ (fun x hx ↦ hh x (by simp only [Within] at hx ⊢; addr_omega [hx, ho])) (by addr_omega [ho]))
    (fr _ (fun x hx ↦ hh x (by simp only [Within] at hx ⊢; addr_omega [hx, ho])) (by addr_omega [ho]))
    hb hn hP

/-- `stateAt` read back as words. -/
theorem lane_of_state {t : MachineState} {a : Word}
    (h : stateAt t a = keccakF1600 (Vector.replicate 25 0)) {j : Nat} (hj : j < 25) :
    t.getMem (a + BitVec.ofNat 64 (8 * j)) =
      (LayoutMirror.keccakFRust (List.replicate 25 0#64)).getD j 0 := by
  rw [LayoutMirror.keccakFRust_zero, List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map,
    Vector.getElem_toList, ← h]
  simp only [stateAt, Vector.getElem_ofFn, UInt64.toBitVec_ofBitVec]

/-- The lanes of `keccak_f` of zeros, at `a`. -/
def LanesAt (t : MachineState) (a : Word) : Prop :=
  ∀ j < 25, t.getMem (a + BitVec.ofNat 64 (8 * j)) =
    (LayoutMirror.keccakFRust (List.replicate 25 0#64)).getD j 0

set_option maxRecDepth 8192 in
/-- The padding's `Vec` to `sp + 952`, `memset(sp + 1312, 0, 200)`. -/
theorem tail2 (hMS : MemsetSpec 0x800126f4)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B D : Nat} {P : Word} (hpre : WalkPre s)
    (h : K7 OI s u A k R Q B D) (z : ZVec u (s.getReg .x2 - 1368) 92 P D) (hpc : u.pc = 0x80001f48) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001f74 ∧ K7 OI s t A k R Q B D ∧
      ZVec t (s.getReg .x2 - 1704) 92 P D ∧
      t.getMem (s.getReg .x2 - 1360) = P ∧ t.getMem (s.getReg .x2 - 1352) = 92 ∧
      ∀ j < 25, t.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 (8 * j)) = 0) ∨ Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp₀ : u.getReg .x2 = s.getReg .x2 - 2656 := h.m.inv.sp
  have hu := h.m.inv.heap.hi
  have zb := z.buf
  simp only [heapEnd] at hu
  obtain ⟨u₁, r₁, g₁⟩ := Sym.BlockSpec.reaches b80001f48_spec hpc (by
    rv_eval [sp₀]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80001f48_keeps g₁
  have fr₁ : Rv64Verifier.Layout.DFrame u u₁ fun x ↦ Within x (s.getReg .x2 - 1704) 24 :=
    Expect.ldframe g₁ (by
      rv_eval [sp₀]
      simp only [Within]
      and_intros <;> addr_omega [hb1])
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : u.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp₀ hNM
  have hn₁ : heapNext u₁ = heapNext u := by
    simp only [heapNext]; rw [fr₁ _ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
      (by decide)]
  have K₁ := h.step hpre fr₁ (fun x hx ↦ Or.inl (by simp only [Within] at hx ⊢; addr_omega [hx, hb1]))
    (fun x hx ↦ by simp only [K7W, Within] at hx ⊢; refine ⟨Or.inr ?_, ?_, ?_, ?_⟩ <;> addr_omega [hx, hb1, hu, zb])
    ⟨hn₁ ▸ h.m.inv.heap.lo, hn₁ ▸ h.m.inv.heap.hi⟩ hn₁.ge (k₁ .x2 (by decide))
  have z₁ := z.move (o := s.getReg .x2 - 1704) fr₁
    (by rw [← e 952 1704 (by decide), b80001f48_m_x2_952 g₁, e 1288 1368 (by decide)])
    (by rw [show s.getReg .x2 - 1704 + 8 = u.getReg .x2 + 960 from (e 960 1696 (by decide)).trans
          (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]) |>.symm, b80001f48_m_x2_960 g₁,
        e 1296 1360 (by decide)]
        congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [show s.getReg .x2 - 1704 + 16 = u.getReg .x2 + 968 from (e 968 1688 (by decide)).trans
          (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]) |>.symm, b80001f48_m_x2_968 g₁,
        e 1304 1352 (by decide)]
        congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (fun x h1 h2 hw ↦ by simp only [Within] at hw; addr_omega [hw, h1, h2, hb1, hu, zb]) hn₁.ge
    (by omega)
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := K₁.m.inv.sp
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 1344 := by rw [b80001f48_x10 g₁]; exact e 1312 1344 (by decide)
  have x12₁ : (u₁.getReg .x12).toNat = 200 := by rw [b80001f48_x12 g₁]; rfl
  obtain ⟨t, r₂, ⟨hpc₂, hp₂, post⟩ | hd⟩ := hMS.call (Reaches.refl u₁) (b80001f48_pc g₁)
    (show Mapped _ _ by rw [x10₁, x12₁]; addr_omega [hb1, hb2])
  swap
  · exact ⟨t, r₁.trans r₂, Or.inr hd⟩
  have by₂ := post.bytes
  have fr₂ := post.frame.dframe
  rw [x10₁, x12₁, b80001f48_x11 g₁] at by₂
  rw [x10₁, x12₁] at fr₂
  have hn₂ : heapNext t = heapNext u₁ := by
    simp only [heapNext]; rw [fr₂ _ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
      (by decide)]
  have hv : HeapOk t := ⟨hn₂ ▸ K₁.m.inv.heap.lo, hn₂ ▸ K₁.m.inv.heap.hi⟩
  refine ⟨t, r₁.trans r₂, Or.inl ⟨by rw [hpc₂, returnAddress_eq, b80001f48_x1 g₁]; decide,
    K₁.call hpre (o := s.getReg .x2 - 1344) (n := 200) (m := 0) (fr₂.mono fun a ha ↦ Or.inl ha)
      (by addr_omega [hb1]) (fun a ha hw ↦ by simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
      (by decide) hv hn₂.ge (hp₂.reg .x2),
    z₁.frame fr₂ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1]) (by addr_omega [hb1])
      (fun x h1 h2 hw ↦ by simp only [Within] at hw; addr_omega [hw, h1, h2, hb1, hu, zb]) hn₂.ge (by omega), ?_, ?_,
    fun j hj ↦ Transcript.Duplex.getMem_zero_of_bytesAt (by decide) by₂ (by addr_omega [hb1, hb3]) (by omega)
      (by omega)⟩⟩
  · have := z.ptr
    simp only [vecPtr, show s.getReg .x2 - 1368 + 8 = s.getReg .x2 - 1360 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at this
    rw [fr₂ _ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1]) (by addr_omega [hb1]),
      fr₁ _ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1]) (by addr_omega [hb1])]
    exact this
  · have := z.len
    simp only [vecLen, show s.getReg .x2 - 1368 + 16 = s.getReg .x2 - 1352 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at this
    rw [fr₂ _ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1]) (by addr_omega [hb1]),
      fr₁ _ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1]) (by addr_omega [hb1])]
    exact this

/-- Past the KECCAK padding's allocation and the zero state's permutation, before the padding loop:
the lanes of `keccak_f` of zeros at `sp + 1760`. -/
structure K7L (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B D : Nat) (P : Word) : Prop where
  k7 : K7 OI s u A k R Q B D
  z : ZVec u (s.getReg .x2 - 1704) 92 P D
  lanes : LanesAt u (s.getReg .x2 - 896)

set_option maxRecDepth 8192 in
/-- `keccak_f(sp + 1312)` of the zero state, the bound check, the state copied to `sp + 1760`. -/
theorem tail3 (hK : Contracts.KeccakFSpec) (hMC : MemcpySpec 0x800126e4)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B D : Nat} {P : Word} (hpre : WalkPre s)
    (h : K7 OI s u A k R Q B D) (z : ZVec u (s.getReg .x2 - 1704) 92 P D)
    (h8 : u.getMem (s.getReg .x2 - 1360) = P) (h16 : u.getMem (s.getReg .x2 - 1352) = 92)
    (h0 : ∀ j < 25, u.getMem (s.getReg .x2 - 1344 + BitVec.ofNat 64 (8 * j)) = 0)
    (hpc : u.pc = 0x80001f74) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001fbc ∧ K7L OI s t A k R Q B D P ∧
      t.getReg .x8 = P + 2208 ∧ t.getReg .x9 = P ∧ t.getReg .x18 = 2208 ∧
      t.getReg .x23 = s.getReg .x2 - 896) ∨ Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp₀ : u.getReg .x2 = s.getReg .x2 - 2656 := h.m.inv.sp
  have hu := h.m.inv.heap.hi
  have zb := z.buf
  simp only [heapEnd] at hu
  have hro := hpre.stack.rodata
  rw [stackLo_eq, stack_eq] at hro
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : u.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp₀ hNM
  obtain ⟨u₁, r₁, g₁⟩ := Sym.BlockSpec.reaches b80001f74_spec hpc trivial
  have k₁ := b80001f74_keeps g₁
  have m₁ := b80001f74_mem_same g₁
  have I₁ := h.m.inv.same m₁ (k₁ .x2 (by decide))
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 1344 := by rw [b80001f74_x10 g₁]; exact e 1312 1344 (by decide)
  have hkp : Contracts.KeccakFPre u₁ := {
    state := by rw [x10₁]; valid_sub hval [hb1]
    stack := calleeStack hpre I₁ (by decide) (by decide)
    stateStack := by rw [x10₁, stackLo_callee I₁]; addr_omega [hb1]
    tables := keccakTables_of_rodata (I₁.rodata hpre)
    tablesState := by rw [x10₁]; addr_omega [hb1, hro]
    tablesStack := by rw [stackLo_callee I₁]; addr_omega [hb1, hro] }
  obtain ⟨u₂, r₂, ⟨hpc₂, hp₂, post₂⟩ | hd⟩ := hK.call r₁ (b80001f74_pc g₁) hkp
  swap
  · exact ⟨u₂, r₂, Or.inr hd⟩
  have val := stateAt_keccakF post₂.value
  rw [x10₁] at val
  have fr₂' := post₂.frame
  rw [x10₁, stackLo_callee I₁] at fr₂'
  have fr₂ : Rv64Verifier.Layout.DFrame u u₂ fun a ↦ Within a (s.getReg .x2 - 1344) 200 ∨
      Within a (s.getReg .x2 - 2656 - BitVec.ofNat 64 Contracts.keccakFStack) Contracts.keccakFStack :=
    fun a ha hw ↦ by
      rw [fr₂' a (fun h' ↦ ha a (by simp only [Within]; omega) (Or.inl h'))
        (fun h' ↦ ha a (by simp only [Within]; omega) (Or.inr h')), m₁]
  have hn₂ : heapNext u₂ = heapNext u := by
    simp only [heapNext]
    rw [fr₂ _ (fun x hx hw ↦ by
      simp only [Within, Contracts.keccakFStack, Contracts.memStack] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1])
      (by decide)]
  have hv₂ : HeapOk u₂ := ⟨hn₂ ▸ h.m.inv.heap.lo, hn₂ ▸ h.m.inv.heap.hi⟩
  have K₂ := h.call hpre (o := s.getReg .x2 - 1344) (n := 200) (m := Contracts.keccakFStack)
    (fr₂.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by rw [stackLo_callee h.m.inv]; exact ha)))
    (by addr_omega [hb1]) (fun a ha hw ↦ by simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
    (by decide) hv₂ hn₂.ge ((hp₂.reg .x2).trans (k₁ .x2 (by decide)))
  have hst : stateAt u (s.getReg .x2 - 1344) = Vector.replicate 25 0 := by
    apply Vector.ext
    intro j hj
    simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_replicate, h0 j hj]
    rfl
  rw [show stateAt u₁ (s.getReg .x2 - 1344) = stateAt u (s.getReg .x2 - 1344) from
    stateAt_congr fun j _ ↦ m₁ _, hst] at val
  have keep₂ (y : Word) (hy : y.toNat + 8 ≤ (s.getReg .x2 - 1344).toNat ∧
      (s.getReg .x2 - 2656).toNat ≤ y.toNat) : u₂.getMem y = u.getMem y :=
    fr₂ y (fun x hx hw ↦ by
      simp only [Within, Contracts.keccakFStack, Contracts.memStack] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hy, hb1])
      (by addr_omega [hy, hb1])
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 2656 := K₂.m.inv.sp
  obtain ⟨u₃, r₃, g₃⟩ := Sym.BlockSpec.reaches b80001f80_spec
    (by rw [hpc₂, returnAddress_eq, b80001f74_x1 g₁]; decide) (by
      rv_eval [sp₂]
      valid_access hval [hb1])
  have n16 : u₂.getMem (u₂.getReg .x2 + 1304) = 92 := by
    rw [spAdd hpre sp₂ (N := 1304) (M := 1352) (by decide), keep₂ _ (by addr_omega [hb1]), h16]
  have p₃ := b80001f80_pc_taken g₃ (by rw [n16]; decide)
  have m₃ := b80001f80_mem_same g₃
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 2656 := (b80001f80_keeps g₃ .x2 (by decide)).trans sp₂
  obtain ⟨u₄, r₄, g₄⟩ := Sym.BlockSpec.reaches b80001f90_spec p₃ (by
    rv_eval [sp₃]
    valid_access hval [hb1])
  have m₄ := b80001f90_mem_same g₄
  have n8 : u₃.getMem (u₃.getReg .x2 + 1296) = P := by
    rw [sp₃, m₃, ← sp₂, spAdd hpre sp₂ (N := 1296) (M := 1360) (by decide), keep₂ _ (by addr_omega [hb1]), h8]
  have x10₃ : u₃.getReg .x10 = 92 := by rw [b80001f80_x10 g₃, n16]
  have x10₄ : u₄.getReg .x10 = s.getReg .x2 - 896 := by
    rw [b80001f90_x10 g₄, sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x11₄ : u₄.getReg .x11 = s.getReg .x2 - 1344 := by
    rw [b80001f90_x11 g₄, sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x12₄ : (u₄.getReg .x12).toNat = 200 := by rw [b80001f90_x12 g₄]; rfl
  have mm (y : Word) : u₄.getMem y = u₂.getMem y := (m₄ y).trans (m₃ y)
  have sp₄ : u₄.getReg .x2 = s.getReg .x2 - 2656 := (b80001f90_keeps g₄ .x2 (by decide)).trans sp₃
  have I₄ : Inv s u₄ := K₂.m.inv.same mm (sp₄.trans sp₂.symm)
  have hmc : MemcpyPre u₄ := {
    dst := by rw [x10₄, x12₄]; addr_omega [hb1, hb2]
    src := by rw [x11₄, x12₄]; addr_omega [hb1, hb2]
    apart := by rw [x10₄, x11₄, x12₄]; addr_omega [hb1]
    stack := calleeStack hpre I₄ (by decide) (by decide)
    dstStack := by rw [x10₄, x12₄, stackLo_callee I₄]; addr_omega [hb1]
    srcStack := by rw [x11₄, x12₄, stackLo_callee I₄]; addr_omega [hb1] }
  obtain ⟨t, r₅, ⟨hpc₅, hp₅, post₅⟩ | hd⟩ := hMC.call (Reaches.refl u₄) (b80001f90_pc g₄) hmc
  swap
  · exact ⟨t, r₂.trans (r₃.trans (r₄.trans r₅)), Or.inr hd⟩
  have by₅ := post₅.bytes
  have fr₅ := post₅.frame.dframe
  rw [x10₄, x11₄, x12₄] at by₅
  rw [x10₄, x12₄] at fr₅
  have hn₄ : heapNext u₄ = heapNext u₂ := by simp only [heapNext, mm]
  have hn₅ : heapNext t = heapNext u₄ := by
    simp only [heapNext]
    rw [fr₅ _ (fun x hx hw ↦ by
      rw [stackLo_callee I₄] at hw; simp only [Within, memcpyStack] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1])
      (by decide)]
  have K₄ := K₂.step hpre (Rv64Verifier.Layout.DFrame.of_same mm (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (fun _ h ↦ h.elim) ⟨hn₄ ▸ hv₂.lo, hn₄ ▸ hv₂.hi⟩ hn₄.ge (sp₄.trans sp₂.symm)
  have hv₅ : HeapOk t := ⟨hn₅ ▸ K₄.m.inv.heap.lo, hn₅ ▸ K₄.m.inv.heap.hi⟩
  have K₅ := K₄.call hpre (o := s.getReg .x2 - 896) (n := 200) (m := memcpyStack)
    (fr₅.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha))
    (by addr_omega [hb1]) (fun a ha hw ↦ by simp only [Within] at ha hw; addr_omega [ha, hw, hb1])
    (by decide) hv₅ hn₅.ge (hp₅.reg .x2)
  have z₂ := z.frame fr₂ (fun x hx hw ↦ by
      simp only [Within, Contracts.keccakFStack, Contracts.memStack] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1])
    (by addr_omega [hb1]) (fun x h1 h2 hw ↦ by
      simp only [Within, Contracts.keccakFStack, Contracts.memStack] at hw; rcases hw with hw | hw <;> addr_omega [hw, h1, h2, hb1, hu, zb])
    hn₂.ge (by omega)
  have z₅ := (z₂.frame (Rv64Verifier.Layout.DFrame.of_same mm (fun _ ↦ False)) (fun _ _ h ↦ h)
    (by addr_omega [hb1]) (fun _ _ _ h ↦ h) hn₄.ge (by omega)).frame fr₅ (fun x hx hw ↦ by
      rw [stackLo_callee I₄] at hw; simp only [Within, memcpyStack] at hx hw; rcases hw with hw | hw <;> addr_omega [hx, hw, hb1])
    (by addr_omega [hb1]) (fun x h1 h2 hw ↦ by
      rw [stackLo_callee I₄] at hw; simp only [Within, memcpyStack] at hw; rcases hw with hw | hw <;> addr_omega [hw, h1, h2, hb1, hu, zb])
    hn₅.ge (by omega)
  have pc₅ : t.pc = 0x80001fbc := by rw [hpc₅, returnAddress_eq, b80001f90_x1 g₄]; decide
  refine ⟨t, r₂.trans (r₃.trans (r₄.trans r₅)), Or.inl ⟨pc₅, ⟨K₅, z₅, fun j hj ↦ ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [getMem_eq_of_bytesAt by₅ (by addr_omega [hb1, hb3]) (by addr_omega [hb1, hb3]) (by omega) (by omega),
      mm]
    exact lane_of_state val hj
  · rw [hp₅.reg .x8, b80001f90_x8 g₄, n8, x10₃]; rfl
  · rw [hp₅.reg .x9, b80001f90_x9 g₄, n8]
  · rw [hp₅.reg .x18, b80001f90_x18 g₄, x10₃]; rfl
  · rw [hp₅.reg .x23, b80001f90_x23 g₄, sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]

end Rv64Verifier.Proofs.Walk
