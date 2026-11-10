import Rv64Verifier.Proofs.Transcript.Repr
import Rv64Verifier.Proofs.Runtime.Contracts

/-!
# What the opening's proofs share

* Regions a function reads (`Src`) or writes (`Dst`), its stack the `k` bytes below `sp`.
* `Wr s k w nx`: what a function entered at `s` may have written once `NEXT` is `nx`; `w`, its
  stack, `NEXT` and the heap allocated since. A `Src` region apart from `w` misses it
  (`Src.miss`), so a frame of it keeps the region's words (`DFrame.word`, `DFrame.eAt'`,
  `DFrame.eList`).
* `PInv`: inside a function, the frame on doublewords (`Transcript.DFrame`, which the field
  contracts' two-range frames and the runtime's byte frames both give), the saved registers in
  their slots, `NEXT`. `PInv.step` carries it over a block or a call, `PInv.rodata` keeps
  `.rodata`, `PInv.frame` is the contract's frame at the end.
-/

namespace Rv64Verifier.Pcs
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Transcript

/-- `n` bytes from `a` that a function reads, its stack the `k` bytes below `sp`: empty or an
aligned region of a data window, apart from the stack, the free heap and `NEXT`. -/
structure Src (s : MachineState) (k : Nat) (a : Word) (n : Nat) : Prop where
  region : n = 0 ∨ Region a n
  stack : Apart a n (stackLo s k) k
  free : Outside s a n

/-- `n` bytes from `a` that a function writes: an aligned region apart from the stack, the free
heap, `NEXT` and `.rodata`. -/
structure Dst (s : MachineState) (k : Nat) (a : Word) (n : Nat) : Prop where
  region : Region a n
  stack : Apart a n (stackLo s k) k
  free : Outside s a n
  rodata : Apart a n rodataBase Rv64Verifier.rodataSize

/-- What a function entered at `s`, its stack the `k` bytes below `sp`, may have written once
`NEXT` is `nx`. -/
def Wr (s : MachineState) (k : Nat) (w : Word → Prop) (nx a : Word) : Prop :=
  w a ∨ Within a (stackLo s k) k ∨ Within a nextAddr 8 ∨
    (heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat)

theorem Wr.mono {s : MachineState} {k : Nat} {w : Word → Prop} {nx nx' : Word}
    (hle : nx.toNat ≤ nx'.toNat) {a : Word} (h : Wr s k w nx a) : Wr s k w nx' a := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨h.1, by omega⟩))

theorem Src.bound {s : MachineState} {k : Nat} {a : Word} {n : Nat} (h : Src s k a n) :
    n = 0 ∨ a.toNat + n ≤ 0xc0000000 := by
  rcases h.region with h0 | h0
  · exact Or.inl h0
  · right; simp only [Region, Mapped] at h0; omega

/-- A region read, apart from `w`, misses what the function writes. -/
theorem Src.miss {s : MachineState} {k : Nat} {a : Word} {n : Nat} (h : Src s k a n)
    {w : Word → Prop} (hw : ∀ x, Within x a n → ¬ w x) {nx : Word} (hfit : nx.toNat ≤ heapEnd) :
    ∀ x, Within x a n → ¬ Wr s k w nx x := by
  have hs := h.stack
  have hf := h.free
  simp only [Outside] at hf
  intro x hx hW
  rcases hW with hW | hW | hW | hW
  · exact hw x hx hW
  · addr_omega [hx, hW, hs]
  · addr_omega [hx, hW, hf.2]
  · rcases hf.1 with h1 | h1
    · addr_omega [hx, hW.1, h1]
    · addr_omega [hx, hW.2, h1, hfit]

/-- A word missed by a doubleword frame keeps its value. -/
theorem _root_.Rv64Verifier.Transcript.DFrame.word {s u : MachineState} {W : Word → Prop} (h : DFrame s u W) {p : Word}
    (hm : ∀ x, Within x p 8 → ¬ W x) (hp : p.toNat + 8 ≤ 2 ^ 64) : u.getMem p = s.getMem p :=
  h p fun i hi ↦ hm _ (by addr_omega [hp, hi])

theorem _root_.Rv64Verifier.Transcript.DFrame.eAt' {s u : MachineState} {W : Word → Prop} (h : DFrame s u W) {p : Word}
    (hm : ∀ x, Within x p 24 → ¬ W x) (hp : p.toNat + 24 ≤ 2 ^ 64) : eAt u p = eAt s p :=
  h.eAt fun i hi ↦ hm _ (by addr_omega [hp, hi])

theorem _root_.Rv64Verifier.Transcript.DFrame.eList {s u : MachineState} {W : Word → Prop} (h : DFrame s u W) {p : Word}
    {n : Nat} (hm : ∀ x, Within x p (24 * n) → ¬ W x) (hp : n = 0 ∨ p.toNat + 24 * n ≤ 2 ^ 64) :
    eListAt u p n = eListAt s p n := by
  rcases hp with h0 | hp
  · subst h0; rfl
  · exact h.eListAt fun i hi ↦ hm _ (by addr_omega [hp, hi])

/-! ## Inside a function -/

/-- Inside a function entered at `s`: `sp` is `n` below the entry's, the registers of `slots`
saved at their offsets below the entry's `sp`, those of `kept` unchanged, `NEXT = nx`, and memory
changed only in `Wr s k w nx`. -/
structure PInv (s u : MachineState) (n k : Nat) (slots : List (Nat × Reg)) (kept : List Reg)
    (w : Word → Prop) (nx : Word) : Prop where
  sp : u.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 n
  slots : ∀ p ∈ slots, u.getMem (s.getReg .x2 - BitVec.ofNat 64 p.1) = s.getReg p.2
  kept : ∀ r ∈ kept, u.getReg r = s.getReg r
  mem : DFrame s u (Wr s k w nx)
  next : u.getMem nextAddr = nx
  mono : heapNext s ≤ nx.toNat
  fits : nx.toNat ≤ heapEnd

/-- A step writing `X`, within what may be written and below the slots (the top `m` bytes of
the frame). -/
theorem PInv.step {s u v : MachineState} {n k : Nat} {slots : List (Nat × Reg)}
    {kept : List Reg} {w X : Word → Prop} {nx nx' : Word} (h : PInv s u n k slots kept w nx)
    (m : Nat) (hslots : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 ≤ m) (hsb : m ≤ (s.getReg .x2).toNat)
    (hX : DFrame u v X) (hXsub : ∀ a, X a → Wr s k w nx' a)
    (hXslot : ∀ a, X a → ¬ Within a (s.getReg .x2 - BitVec.ofNat 64 m) m)
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hsp : v.getReg .x2 = u.getReg .x2) (hk : ∀ r ∈ kept, v.getReg r = u.getReg r) :
    PInv s v n k slots kept w nx' := by
  refine ⟨hsp.trans h.sp, fun p hp ↦ ?_, fun r hr ↦ (hk r hr).trans (h.kept r hr),
    (h.mem.mono fun a ha ↦ ha.mono hle).trans hX hXsub, hnx, Nat.le_trans h.mono hle, hend⟩
  obtain ⟨h1, h2⟩ := hslots p hp
  rw [← h.slots p hp]
  exact hX _ fun i hi hx ↦ hXslot _ hx (by addr_omega [h1, h2, hi, hsb])

/-- A block that writes nothing. -/
theorem PInv.same {s u v : MachineState} {n k : Nat} {slots : List (Nat × Reg)}
    {kept : List Reg} {w : Word → Prop} {nx : Word} (h : PInv s u n k slots kept w nx)
    (hm : ∀ a, v.getMem a = u.getMem a) (hsp : v.getReg .x2 = u.getReg .x2)
    (hk : ∀ r ∈ kept, v.getReg r = u.getReg r) : PInv s v n k slots kept w nx :=
  ⟨hsp.trans h.sp, fun p hp ↦ (hm _).trans (h.slots p hp), fun r hr ↦ (hk r hr).trans (h.kept r hr),
    (h.mem.trans (DFrame.of_same hm fun _ ↦ False) fun _ h ↦ h.elim), (hm _).trans h.next,
    h.mono, h.fits⟩

/-- `.rodata`, which nothing the function writes touches. -/
theorem PInv.rodata {s u : MachineState} {n k : Nat} {slots : List (Nat × Reg)}
    {kept : List Reg} {w : Word → Prop} {nx : Word} (h : PInv s u n k slots kept w nx)
    (hro : RodataOk s) (hw : ∀ a, w a → ¬ Within a rodataBase Rv64Verifier.rodataSize)
    (hst : Apart (stackLo s k) k rodataBase Rv64Verifier.rodataSize) : RodataOk u := by
  have hfit := h.fits
  refine hro.dframe h.mem fun a ha hW ↦ ?_
  rcases hW with hW | hW | hW | hW
  · exact hw a hW ha
  · addr_omega [ha, hW, hst]
  · addr_omega [ha, hW]
  · addr_omega [ha, hW.2, hfit]

/-- The contract's frame at the end. -/
theorem PInv.frame {s u : MachineState} {n k : Nat} {slots : List (Nat × Reg)}
    {kept : List Reg} {w : Word → Prop} {nx : Word} (h : PInv s u n k slots kept w nx) :
    DFrame s u fun a ↦ w a ∨ Within a (stackLo s k) k ∨ Within a nextAddr 8 ∨ Fresh s u a := by
  refine h.mem.mono fun a ha ↦ ?_
  have hn : heapNext u = nx.toNat := by simp only [heapNext, h.next]
  rcases ha with ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, hn]; exact ha)))

theorem PInv.heap {s u : MachineState} {n k : Nat} {slots : List (Nat × Reg)}
    {kept : List Reg} {w : Word → Prop} {nx : Word} (h : PInv s u n k slots kept w nx)
    (hs : HeapOk s) : HeapOk u := by
  have hn : heapNext u = nx.toNat := by simp only [heapNext, h.next]
  exact ⟨by rw [hn]; exact Nat.le_trans hs.lo h.mono, by rw [hn]; exact h.fits⟩

/-! ## Regions -/

/-- Aligned doublewords inside a region are a valid range. -/
theorem Region.vrange {a x : Word} {n m : Nat} (h : Region a n) (h1 : a.toNat ≤ x.toNat)
    (h2 : x.toNat + 8 * m ≤ a.toNat + n) (h3 : x.toNat % 8 = 0) : ValidMemRange x m := by
  intro i hi
  have hR := h
  simp only [Region, Mapped] at hR
  exact h.valid (by addr_omega [h1, h2, hi, hR]) (by addr_omega [h1, h2, hi, hR])
    (by addr_omega [h3, h2, hi, hR])

theorem Region.bounds {a : Word} {n : Nat} (h : Region a n) :
    0x20 ≤ a.toNat ∧ a.toNat + n ≤ 0xc0000000 ∧ a.toNat % 8 = 0 := by
  simp only [Region, Mapped] at h
  omega

/-- Bytes in the heap below its end are a region. -/
theorem heap_region {a : Word} {n : Nat} (h1 : 0x20 ≤ a.toNat) (h2 : a.toNat + n ≤ heapEnd)
    (h3 : a.toNat % 8 = 0) : Region a n := by
  simp only [Region, Mapped, heapEnd] at h2 ⊢
  omega

/-- A region read stays one for a callee: its stack within the function's, the free heap only
shrinking. -/
theorem Src.callee {s c : MachineState} {k k' : Nat} {a : Word} {n : Nat} (h : Src s k a n)
    (hlo : (stackLo s k).toNat ≤ (stackLo c k').toNat)
    (hhi : (stackLo c k').toNat + k' ≤ (stackLo s k).toNat + k)
    (hk : (stackLo s k).toNat + k ≤ 2 ^ 64) (hn : heapNext s ≤ heapNext c) : Src c k' a n := by
  have hs := h.stack
  have hf := h.free
  simp only [Outside] at hf ⊢
  refine ⟨h.region, by addr_omega [hs, hlo, hhi, hk], ⟨?_, hf.2⟩⟩
  rcases hf.1 with h1 | h1
  · exact Or.inl (by omega)
  · exact Or.inr h1

/-- Part of a region read. -/
theorem Src.sub {s : MachineState} {k : Nat} {a b : Word} {n m : Nat} (h : Src s k a n)
    (h1 : a.toNat ≤ b.toNat) (h2 : b.toNat + m ≤ a.toNat + n) (h3 : b.toNat % 8 = 0) :
    Src s k b m := by
  have hs := h.stack
  have hf := h.free
  simp only [Outside] at hf ⊢
  refine ⟨?_, by addr_omega [hs, h1, h2], ⟨?_, by addr_omega [hf.2, h1, h2]⟩⟩
  · rcases h.region with h0 | h0
    · left; omega
    · by_cases hm : m = 0
      · exact Or.inl hm
      · right; simp only [Region, Mapped] at h0 ⊢; omega
  · rcases hf.1 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- A prefix of a region read. -/
theorem Src.prefix {s : MachineState} {k : Nat} {a : Word} {n m : Nat} (h : Src s k a n)
    (hm : m ≤ n) : Src s k a m := by
  have hs := h.stack
  have hf := h.free
  simp only [Outside] at hf ⊢
  refine ⟨?_, by simp only [Apart] at hs ⊢; omega, ⟨?_, by simp only [Apart] at hf ⊢; omega⟩⟩
  · rcases h.region with h0 | h0
    · left; omega
    · by_cases hm0 : m = 0
      · exact Or.inl hm0
      · right; simp only [Region, Mapped] at h0 ⊢; omega
  · rcases hf.1 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr h0

end Rv64Verifier.Pcs
