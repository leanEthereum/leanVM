import Rv64Verifier.Proofs.Main.ParseFoot

/-!
# `try_allocate_in` from `ParseRest`

`Wc B`: what a callee writes, `main`'s result slots (`msp + 272` on), the stack below `msp`,
`NEXT` and the heap from `B` on; it misses `main`'s scratch slots (`Wc.keep`). `alloc_call`: a
call of `try_allocate_in` with its result at `msp + 320`, then the block that traps on its error,
to the block after it with a new buffer, the dangling pointer `a2` if empty.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End

/-- What a callee of `ParseRest` writes. -/
def Wc (B : Nat) (a : Word) : Prop :=
  Within a (msp + 272) 80 ∨ Within a (msp - 4096) 4096 ∨ Within a nextAddr 8 ∨
    (B ≤ a.toNat ∧ a.toNat < heapEnd)

theorem Wc.wf {B : Nat} {a : Word} (h : Wc B a) : Wf B a := by
  rcases h with h | h | h | h
  · exact Wf.out h
  · exact Wf.stack h
  · exact Wf.next h
  · exact Wf.heap h.1 h.2

theorem Wc.mono {B B' : Nat} (h : B ≤ B') {a : Word} (ha : Wc B' a) : Wc B a := by
  rcases ha with ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr ⟨le_trans h ha.1, ha.2⟩))

/-- A callee keeps `main`'s scratch slots and what lies between them and its result slots. -/
theorem Wc.keep {t w : MachineState} {B : Nat} (hf : BFrame t w (Wc B)) {a : Word}
    (h8 : a.toNat % 8 = 0) (h1 : (msp + 24).toNat ≤ a.toNat) (h2 : a.toNat + 8 ≤ (msp + 272).toNat) :
    w.getMem a = t.getMem a :=
  hf.getMem h8 fun i hi hw ↦ by
    rcases hw with hw | hw | hw | ⟨hw1, hw2⟩
    · addr_omega [hw, h1, h2, hi]
    · addr_omega [hw, h1, h2, hi]
    · addr_omega [hw, h1, h2, hi]
    · simp only [heapEnd] at hw2; addr_omega [hw2, h1, h2, hi]

theorem m328 : (msp + 320 + 8 : Word) = msp + 328 := by decide
theorem m336 : (msp + 320 + 16 : Word) = msp + 336 := by decide

/-- **A call of `try_allocate_in`** (`a1` elements of `a3` bytes aligned to `a2`, the result at
`msp + 320`), and the block at the return address `A` that traps on its error and goes on to
`N`. -/
theorem alloc_call {u₀ t : MachineState} (hg : PG u₀ t) (hpc : t.pc = 0x80000024)
    (h10 : t.getReg .x10 = msp + 320)
    (hal : 0 < (t.getReg .x12).toNat ∧ (t.getReg .x12).toNat ≤ 16)
    (hsz : 0 < (t.getReg .x13).toNat)
    {A N : Word} {x : Sym.Expect} {k : Nat} (hra : returnAddress t = A)
    (hs : Sym.BlockSpec Image.code A k (fun s ↦ Sym.Oblig.all s x.obl) x.Holds)
    (hobl : ∀ v, v.getReg .x2 = msp → Sym.Oblig.all v x.obl)
    (htaken : ∀ v w, x.Holds v w → v.getMem (v.getReg .x2 + 320) ≠ 0 → w.pc = 0x80000ed4)
    (hnot : ∀ v w, x.Holds v w → v.getMem (v.getReg .x2 + 320) = 0 → w.pc = N)
    (hmem : ∀ v w, x.Holds v w → ∀ a, w.getMem a = v.getMem a)
    (hkeep : ∀ v w, x.Holds v w → ∀ r ∈ calleeSaved, w.getReg r = v.getReg r) :
    ∃ w, Reaches Image.code t w ∧ (Dead Image.code w ∨ (w.pc = N ∧
      (∀ r ∈ calleeSaved, w.getReg r = t.getReg r) ∧ PG u₀ w ∧
      BFrame t w (Wc (heapNext t)) ∧ heapNext t ≤ heapNext w ∧
      w.getMem (msp + 328) = t.getReg .x11 ∧
      InR (w.getMem (msp + 336)) ((t.getReg .x11).toNat * (t.getReg .x13).toNat)
        (t.getReg .x12).toNat (heapNext t) (heapNext w))) := by
  have hsp := hg.sp
  obtain ⟨v, hv, hout⟩ := tryAlloc t hpc {
    heap := hg.heap
    out := by rw [h10]; exact validRange_of (by decide) (by decide) (by decide)
    align := ⟨hal.1, by omega⟩
    size := hsz
    stack := rtStack_msp hsp (by decide) (by decide)
    outFree := by rw [h10]; addr_omega []
    outStack := by rw [h10]; simp only [stackLo, hsp]; addr_omega [] }
  rcases hout with ⟨hpcv, hpres, hpost⟩ | hd
  swap
  · exact ⟨v, hv, Or.inl hd⟩
  have hspv : v.getReg .x2 = msp := (hpres.reg .x2).trans hsp
  have hWc : ∀ a, (Within a (t.getReg .x10) 24 ∨ Within a (stackLo t tryAllocStack) tryAllocStack ∨
      Within a nextAddr 8 ∨ Fresh t v a) → Wc (heapNext t) a := by
    intro a h
    have := hpost.heap.hi
    rcases h with h | h | h | h
    · rw [h10] at h; exact Or.inl (by addr_omega [h])
    · simp only [stackLo, hsp, tryAllocStack] at h; exact Or.inr (Or.inl (by addr_omega [h]))
    · exact Or.inr (Or.inr (Or.inl h))
    · have h2 := h.2
      exact Or.inr (Or.inr (Or.inr ⟨h.1, by simp only [heapEnd] at this ⊢; omega⟩))
  have hfv : BFrame t v (Wc (heapNext t)) := BFrame.mono hpost.frame.byte hWc
  have hgv : PG u₀ v := hg.step hfv (fun a h ↦ (Wc.wf h).mono hg.mono) hspv hpost.heap hpost.mono
  obtain ⟨w, hw, hx⟩ := Sym.BlockSpec.reaches hs (by rw [hpcv, hra]) (hobl v hspv)
  by_cases htag : v.getMem (v.getReg .x2 + 320) ≠ 0
  · obtain ⟨w', hw', hd⟩ := abort (u := w) (by rw [htaken v w hx htag]; decide)
    exact ⟨w', hv.trans (hw.trans hw'), Or.inl hd⟩
  rw [not_not] at htag
  have hm := hmem v w hx
  have hspw : w.getReg .x2 = msp := (hkeep v w hx .x2 (by decide)).trans hspv
  have hz : v.getMem (t.getReg .x10) = 0 := by rw [h10, ← hspv]; exact htag
  obtain ⟨hcap, hbuf⟩ := hpost.ok hz
  have hfw : BFrame v w (Wc (heapNext t)) := BFrame.of_same hm _
  have hnx : heapNext w = heapNext v := by simp only [heapNext, hm]
  refine ⟨w, hv.trans hw, Or.inr ⟨hnot v w hx htag, fun r hr ↦ ?_, hgv.same hm hspw,
    hfv.trans hfw fun _ h ↦ h, by rw [hnx]; exact hpost.mono, ?_, ?_⟩⟩
  · rw [hkeep v w hx r hr, hpres.reg r hr]
  · rw [hm, ← m328, ← h10]; exact hcap
  · rw [hm, ← m336, ← h10, hnx]
    refine ⟨hbuf.1, hbuf.2.imp (fun h0 ↦ ⟨h0, ?_⟩) fun h ↦ h⟩
    have hc : t.getReg .x11 = 0 := BitVec.eq_of_toNat_eq
      ((Nat.mul_eq_zero.mp h0).resolve_right (by omega))
    have hl := hpost.heap.lo
    rw [hpost.dangling hz hc]
    simp only [heapStart] at hl
    omega

end Rv64Verifier.Proofs.Main
