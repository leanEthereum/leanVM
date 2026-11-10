import Rv64Verifier.Proofs.Walk.R6U
import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Proofs.Layout.ArithTail

/-!
# `walk`: `tables()`, KECCAK's padding (R6's tail, first part)

From `0x80001f00` (`KM` on side 1, the `Flushes` at `sp + 1168` holding `flushes_keccak()`): the
`Flushes`' header copied to `sp + 976`, then `vec![ZERO; 92]` into `sp + 1288`, to `0x80001f48`.
From here on (`K7`) the KECCAK `Flushes` sits at `sp + 976`, all it reaches in `[B, D)`; a step
keeps it when it writes neither its header, nor `[B, D)`, nor the heights' lengths.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep)

/-- R6's tail: `walk`'s state, the KECCAK `Flushes` at `sp + 976` (all it reaches in `[B, D)`), the
heights' lengths. -/
structure K7 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B D : Nat) : Prop where
  m : M6 OI s u A k R Q B
  ok : FlushesOk u (s.getReg .x2 - 1680)
  val : flushesOf u (s.getReg .x2 - 1680) = LayoutMirror.flushesKeccakRust
  deep : ∀ x, flushesDeep u (s.getReg .x2 - 1680) x → B ≤ x.toNat ∧ x.toNat < D
  buf : B ≤ D ∧ D ≤ heapNext u
  lens : u.getMem (s.getReg .x2 - 2520) = 6 ∧ u.getMem (s.getReg .x2 - 2504) = 0

/-- What a step past the KECCAK `Flushes` may not write. -/
@[rv_addr] def K7W (s : MachineState) (B D : Nat) (a : Word) : Prop :=
  (a.toNat < B ∨ D ≤ a.toNat) ∧ ¬ Within a (s.getReg .x2 - 1680) 48 ∧
    ¬ Within a (s.getReg .x2 - 2520) 8 ∧ ¬ Within a (s.getReg .x2 - 2504) 8

theorem K7.step {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B D : Nat} {w : Word → Prop} (hpre : WalkPre s)
    (h : K7 OI s u A k R Q B D) (fr : Rv64Verifier.Layout.DFrame u v w)
    (hw : ∀ a, w a → W6 s B v a) (hk : ∀ a, w a → K7W s B D a) (hv : HeapOk v)
    (mono : heapNext u ≤ heapNext v) (sp : v.getReg .x2 = u.getReg .x2) : K7 OI s v A k R Q B D := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have G := Rv64Verifier.Layout.flushesOf_frame fr h.ok
    (fun x hx hwx ↦ (hk x hwx).2.1 hx)
    (fun x hx hwx ↦ by have := h.deep x hx; have := (hk x hwx).1; omega)
    (by addr_omega [hb1]) h.m.inv.heap mono
  exact {
    m := h.m.step hpre (fr.mono hw) hv mono sp
    ok := G.2.1
    val := by rw [G.1]; exact h.val
    deep := fun x hx ↦ h.deep x (by rw [← G.2.2.1]; exact hx)
    buf := ⟨h.buf.1, by have := h.buf.2; omega⟩
    lens := ⟨by
        rw [fr _ (fun x hx hwx ↦ (hk x hwx).2.2.1 hx) (by addr_omega [hb1])]; exact h.lens.1,
      by rw [fr _ (fun x hx hwx ↦ (hk x hwx).2.2.2 hx) (by addr_omega [hb1])]; exact h.lens.2⟩ }

/-- A callee writing `n` bytes at a frame slot `o` past the protected words, its stack, `NEXT`
and what it allocates. -/
theorem K7.call {OI : MachineState → Word → List (List Opening) → Prop} {s u t : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B D : Nat} {o : Word} {n m : Nat}
    (hpre : WalkPre s) (h : K7 OI s u A k R Q B D)
    (fr : Rv64Verifier.Layout.DFrame u t fun a ↦ Within a o n ∨ Within a (stackLo u m) m ∨
      Within a nextAddr 8 ∨ Fresh u t a)
    (ho : (s.getReg .x2 - 2080).toNat ≤ o.toNat ∧ o.toNat + n ≤ (s.getReg .x2 - 104).toNat)
    (hoK : ∀ a, Within a o n → ¬ Within a (s.getReg .x2 - 1680) 48) (hm : m ≤ 8736)
    (hv : HeapOk t) (mono : heapNext u ≤ heapNext t) (sp : t.getReg .x2 = u.getReg .x2) :
    K7 OI s t A k R Q B D := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hB := h.m.bufQ.2.2.2
  have hh := hv.hi
  have hu := h.m.inv.heap.hi
  have hP := h.buf.2
  simp only [heapEnd, heapNext] at hh hu hP
  refine h.step hpre fr (fun a ha ↦ ?_) (fun a ha ↦ ?_) hv mono sp
  · rcases ha with ha | ha | ha | ha
    · exact Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, ho, hb1])
    · exact Or.inr (Or.inr (Or.inr (Or.inl (stackLo_w6 hpre h.m.inv hm ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩))))
  · simp only [K7W]
    rcases ha with ha | ha | ha | ha
    · refine ⟨Or.inr ?_, hoK a ha, ?_, ?_⟩ <;> simp only [Within] at ha ⊢ <;> addr_omega [ha, ho, hb1, hP, hu]
    · rw [stackLo_callee h.m.inv] at ha
      refine ⟨Or.inr ?_, ?_, ?_, ?_⟩ <;> simp only [Within] at ha ⊢ <;> addr_omega [ha, hb1, hm, hP, hu]
    · refine ⟨Or.inr ?_, ?_, ?_, ?_⟩ <;> simp only [Within] at ha ⊢ <;> addr_omega [ha, hb1, hP, hu]
    · simp only [Fresh, heapNext] at ha
      refine ⟨Or.inr (by omega), ?_, ?_, ?_⟩ <;> simp only [Within] <;> addr_omega [ha, hb1, hh]

/-- `ZERO` in `.rodata`. -/
theorem zeroE {u : MachineState} (h : RodataOk u) : eAt u 0xa0000068 = 0 := by
  apply eAt_eq_of_limbs
  rv_eval [h.word (a := 0xa0000068) (v := 0), h.word (a := 0xa0000070) (v := 0),
    h.word (a := 0xa0000078) (v := 0)]
  rfl

theorem zero_vmr' : ValidMemRange (0xa0000068 : Word) 3 := by
  intro i hi
  interval_cases i <;> decide

/-- `vec![ZERO; n]` into the frame slot `o`, as `walk` calls it. -/
theorem fromElemPre {s u : MachineState} (hpre : WalkPre s) (h : Inv s u)
    (x10 : InSlot s (u.getReg .x10) 24) (x11 : u.getReg .x11 = 0xa0000068) :
    MultilinearContracts.FromElemPre u := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hn : MultilinearContracts.fromElemStack ≤ 8736 := by decide
  obtain ⟨v1, v2, v3⟩ := slotW hpre h (n := 3) x10 hn
  have hrs := hpre.stack.rodata
  have hab := hpre.stack.above
  rw [stackLo_eq, stack_eq] at hrs
  simp only [heapEnd] at hab
  exact {
    heap := h.heap
    out := v1
    elem := by rw [x11]; exact zero_vmr'
    stack := stk_sub hpre h hn (by decide)
    outFree := v2
    outStack := v3
    elemFree := by rw [x11]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega []
    elemStack := by rw [x11, stackLo_callee h]; addr_omega [hb1, hrs, hn]
    elemOut := by
      rw [x11]; obtain ⟨o1, o2, o3⟩ := x10; addr_omega [hb1, hrs, o1, o2] }

/-- The `Vec<E>` at `o` is `vec![ZERO; n]`, its buffer `P` allocated past `L`. -/
structure ZVec (u : MachineState) (o : Word) (n : Nat) (P : Word) (L : Nat) : Prop where
  vec : VecOk u o 24 8
  ptr : vecPtr u o = P
  len : vecLen u o = BitVec.ofNat 64 n
  zero : ∀ i < n, eAt u (P + BitVec.ofNat 64 (24 * i)) = 0
  buf : P.toNat % 8 = 0 ∧ L ≤ P.toNat ∧ P.toNat + 24 * n ≤ heapNext u

set_option maxRecDepth 8192 in
/-- The KECCAK `Flushes`' header to `sp + 976`, `vec![ZERO; 92]` into `sp + 1288`. -/
theorem tail1 (hFE : MultilinearContracts.FromElemSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} (hpre : WalkPre s)
    (h : KM OI s u A k R Q B 1 LayoutMirror.flushesKeccakRust) (hpc : u.pc = 0x80001f00) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80001f48 ∧ ∃ P, K7 OI s t A k R Q B (heapNext u) ∧
      ZVec t (s.getReg .x2 - 1368) 92 P (heapNext u)) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp₀ : u.getReg .x2 = s.getReg .x2 - 2656 := h.m.inv.sp
  obtain ⟨u₁, r₁, g₁⟩ := Sym.BlockSpec.reaches b80001f00_spec hpc (by
    rv_eval [sp₀]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80001f00_keeps g₁
  have fr₁ : Rv64Verifier.Layout.DFrame u u₁ fun x ↦ Within x (s.getReg .x2 - 1680) 48 :=
    Expect.ldframe g₁ (by
      rv_eval [sp₀]
      simp only [Within]
      and_intros <;> addr_omega [hb1])
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : u.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp₀ hNM
  have f (N M : Word) (hNM : M.toNat ≤ 1680 ∧ N.toNat = 1680 - M.toNat) :
      s.getReg .x2 - 1680 + N = s.getReg .x2 - M := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hNM]
  have f' (N M : Word) (hNM : M.toNat ≤ 1488 ∧ N.toNat = 1488 - M.toNat) :
      s.getReg .x2 - 1488 + N = s.getReg .x2 - M := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hNM]
  have hfd := h.fl.deep
  have hok := h.fl.ok
  have hu := h.m.inv.heap.hi
  simp only [heapEnd] at hu
  have nd : ∀ x, flushesDeep u (s.getReg .x2 - 1488) x → ¬ Within x (s.getReg .x2 - 1680) 48 :=
    fun x hx hw ↦ by
      have := (hok.deep_below hx).2; simp only [Within, heapNext] at hw this hu; addr_omega [hw, this, hb1, hu]
  have hn₁ : heapNext u₁ = heapNext u := by
    simp only [heapNext]; rw [fr₁ _ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1])
      (by decide)]
  have mv := Rv64Verifier.Layout.Arith.flushesOf_move fr₁ hok
    (by rw [← e 976 1680 (by decide), b80001f00_m_x2_976 g₁, e 1168 1488 (by decide)])
    (by rw [f 8 1672 (by decide), ← e 984 1672 (by decide), b80001f00_m_x2_984 g₁,
      e 1176 1480 (by decide), f' 8 1480 (by decide)])
    (by rw [f 16 1664 (by decide), ← e 992 1664 (by decide), b80001f00_m_x2_992 g₁,
      e 1184 1472 (by decide), f' 16 1472 (by decide)])
    (by rw [f 24 1656 (by decide), ← e 1000 1656 (by decide), b80001f00_m_x2_1000 g₁,
      e 1192 1464 (by decide), f' 24 1464 (by decide)])
    (by rw [f 24 1656 (by decide), show s.getReg .x2 - 1656 + 8 = s.getReg .x2 - 1648 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], ← e 1008 1648 (by decide),
      b80001f00_m_x2_1008 g₁, e 1200 1456 (by decide), f' 24 1464 (by decide),
      show s.getReg .x2 - 1464 + 8 = s.getReg .x2 - 1456 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (by rw [f 24 1656 (by decide), show s.getReg .x2 - 1656 + 16 = s.getReg .x2 - 1640 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], ← e 1016 1640 (by decide),
      b80001f00_m_x2_1016 g₁, e 1208 1448 (by decide), f' 24 1464 (by decide),
      show s.getReg .x2 - 1464 + 16 = s.getReg .x2 - 1448 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]])
    (fun x hx hw ↦ nd x hx hw)
    (fun x hx hd ↦ nd x hd hx) h.m.inv.heap hn₁.ge
  have M₁ := h.m.step hpre (fr₁.mono fun x hx ↦ Or.inl (by simp only [Within] at hx ⊢; addr_omega [hx, hb1]))
    ⟨hn₁ ▸ h.m.inv.heap.lo, hn₁ ▸ h.m.inv.heap.hi⟩ hn₁.ge (k₁ .x2 (by decide))
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := M₁.inv.sp
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 1368 := by rw [b80001f00_x10 g₁]; exact e 1288 1368 (by decide)
  have pre := fromElemPre hpre M₁.inv (by rw [x10₁]; simp only [InSlot]; addr_omega [hb1, hb3])
    (b80001f00_x11 g₁)
  obtain ⟨t, r₂, ⟨hpc₂, hp₂, post⟩ | hd⟩ := hFE.call (Reaches.refl u₁) (b80001f00_pc g₁) pre
  swap
  · exact ⟨t, r₁.trans r₂, Or.inr hd⟩
  have fr₂ := post.frame.dframe
  have nb := post.fresh
  have hlen := post.len
  have hel := post.elems
  rw [x10₁] at fr₂
  rw [x10₁, b80001f00_x12 g₁] at nb hlen hel
  rw [b80001f00_x11 g₁, zeroE (M₁.inv.rodata hpre)] at hel
  have hh := post.heap.hi
  simp only [heapEnd] at hh
  simp only [NewBuf, show ((92 : Word)).toNat = 92 from rfl] at nb
  set P := vecPtr t (s.getReg .x2 - 1368) with hP
  have hP2 : heapNext u₁ ≤ P.toNat ∧ P.toNat + 2208 ≤ heapNext t := by omega
  have lens₁ : u₁.getMem (s.getReg .x2 - 2520) = 6 ∧ u₁.getMem (s.getReg .x2 - 2504) = 0 := by
    rw [fr₁ _ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1]) (by addr_omega [hb1]),
      fr₁ _ (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1]) (by addr_omega [hb1])]
    exact h.lens
  have K₁ : K7 OI s u₁ A k R Q B (heapNext u) := {
    m := M₁
    ok := mv.2.1
    val := by rw [mv.1]; exact h.fl.val
    deep := fun x hx ↦ by
      rw [mv.2.2] at hx
      have := (hok.deep_below hx).2
      exact ⟨h.fl.deep x hx, this⟩
    buf := ⟨h.m.bufQ.2.2.2, hn₁.ge⟩
    lens := lens₁ }
  have K₂ := K₁.call hpre (o := s.getReg .x2 - 1368) (n := 24) fr₂ (by addr_omega [hb1])
    (fun a ha hw ↦ by simp only [Within] at ha hw; addr_omega [ha, hw, hb1]) (by decide) post.heap post.mono
    (hp₂.reg .x2)
  refine ⟨t, r₁.trans r₂, Or.inl ⟨by rw [hpc₂, returnAddress_eq, b80001f00_x1 g₁]; decide, P, K₂, {
    vec := by rw [← x10₁]; exact post.vec
    ptr := rfl
    len := hlen
    zero := fun i hi ↦ ?_
    buf := ⟨nb.1, by omega, by omega⟩ }⟩⟩
  have := congrArg (fun l ↦ l.getD i 0) hel
  have e92 : ((92 : Word)).toNat = 92 := rfl
  simp only [vecEs, hlen, e92, eListAt] at this
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map, List.getElem_range] at this
  rw [this, List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hi), List.getElem_replicate]

end Rv64Verifier.Proofs.Walk
