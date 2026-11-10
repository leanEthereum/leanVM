import Rv64Verifier.Proofs.Runtime.Contracts

/-!
# Inside a function: the frame invariant

`FnInv s u n slots kept w nx` holds at a state `u` inside a function entered at `s` with an
`n`-byte stack frame: `sp` is `n` below the entry's, each register of `slots` saved at its offset
below the entry's `sp`, those of `kept` unchanged, `NEXT = nx`, and memory changed only in `w`
(what the function writes besides its frame), the frame, `NEXT` and the heap allocated since entry.
`FnInv.step` carries it over a block or a call whose writes stay in `w`, `NEXT` and the newly
allocated heap; `FnInv.post` gives the contract's frame at the end.
-/

namespace Rv64Verifier.Runtime
open RiscvZkvm.Rv64

structure FnInv (s u : MachineState) (n : Nat) (slots : List (Nat × Reg)) (kept : List Reg)
    (w : Word → Prop) (nx : Word) : Prop where
  sp : u.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 n
  slots : ∀ p ∈ slots, u.getMem (s.getReg .x2 - BitVec.ofNat 64 p.1) = s.getReg p.2
  kept : ∀ r ∈ kept, u.getReg r = s.getReg r
  mem : ByteFrame s u fun a ↦ w a ∨ Within a (stackLo s n) n ∨ Within a nextAddr 8 ∨
    (heapNext s ≤ a.toNat ∧ a.toNat < nx.toNat)
  next : u.getMem nextAddr = nx
  mono : heapNext s ≤ nx.toNat
  fits : nx.toNat ≤ heapEnd

/-- A step whose writes (`W`) stay in `w`, `NEXT` and the heap allocated since entry. The saved
registers lie in the frame's top `m` bytes, which `w` misses. -/
theorem FnInv.step {s u v : MachineState} {n m : Nat} {slots : List (Nat × Reg)}
    {kept : List Reg} {w W : Word → Prop} {nx nx' : Word} (h : FnInv s u n slots kept w nx)
    (hst : RtStack s n) (hn : 8 ≤ n ∧ n % 8 = 0) (hm : m ≤ n)
    (hslots : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 ≤ m)
    (hw : ∀ a, w a → ¬ Within a (stackLo s m) m) (hW : ByteFrame u v W)
    (hWsub : ∀ a, W a → w a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hsp : v.getReg .x2 = u.getReg .x2) (hk : ∀ r ∈ kept, v.getReg r = u.getReg r) :
    FnInv s v n slots kept w nx' := by
  have hb := hst.bounds hn.1 hn.2
  have hab := hst.above
  have hnx8 := hst.next
  refine ⟨hsp.trans h.sp, fun p hp ↦ ?_, fun r hr ↦ (hk r hr).trans (h.kept r hr),
    (h.mem.mono fun a ha ↦ ?_).trans hW fun a ha ↦ ?_, hnx, Nat.le_trans h.mono hle, hend⟩
  · obtain ⟨h1, h2⟩ := hslots p hp
    rw [← h.slots p hp]
    refine hW.getMem fun i hi hWi ↦ ?_
    have hin : Within (s.getReg .x2 - BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i) (stackLo s m) m := by
      addr_omega [h1, h2, hi, hb, hm]
    rcases hWsub _ hWi with hx | hx | hx
    · exact hw _ hx hin
    · addr_omega [hin, hnx8, hx, hb, hm]
    · addr_omega [hin, hab, hx, hend, hb, hm]
  · rcases ha with hx | hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr ⟨hx.1, Nat.lt_of_lt_of_le hx.2 hle⟩))
  · rcases hWsub a ha with hx | hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))

/-- After a prologue that saved `slots` in the frame. -/
theorem FnInv.init {s u : MachineState} {n : Nat} {slots : List (Nat × Reg)} {kept : List Reg}
    {w : Word → Prop} (hheap : HeapOk s) (hst : RtStack s n) (hsp : u.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 n)
    (hslots : ∀ p ∈ slots, u.getMem (s.getReg .x2 - BitVec.ofNat 64 p.1) = s.getReg p.2)
    (hk : ∀ r ∈ kept, u.getReg r = s.getReg r) (hm : MemFrame s u (stackLo s n) n)
    (hu : ∀ a, a.toNat % 8 ≠ 0 → u.getMem a = s.getMem a) (hn : 8 ≤ n ∧ n % 8 = 0) :
    FnInv s u n slots kept w (s.getMem nextAddr) where
  sp := hsp
  slots := hslots
  kept := hk
  mem := (ByteFrame.of_memFrame hm (by have := hst.bounds hn.1 hn.2; omega) hn.2 hu).mono
    fun _ h ↦ Or.inr (Or.inl h)
  next := hm _ (by have := hst.next; addr_omega [this])
  mono := Nat.le_refl _
  fits := hheap.hi

/-- At the end: memory changed only in `w`, the frame, `NEXT` and the heap allocated. -/
theorem FnInv.frame {s u t : MachineState} {n : Nat} {slots : List (Nat × Reg)}
    {kept : List Reg} {w W : Word → Prop} {nx : Word} (h : FnInv s u n slots kept w nx)
    (hW : ByteFrame u t W) (hWsub : ∀ a, W a → w a) (hnx : t.getMem nextAddr = nx) :
    ByteFrame s t fun a ↦ w a ∨ Within a (stackLo s n) n ∨ Within a nextAddr 8 ∨ Fresh s t a :=
  h.mem.trans hW (fun a ha ↦ Or.inl (hWsub a ha)) |>.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, heapNext, hnx]; exact ha)))

/-- `alloc` writes `NEXT` alone. -/
theorem AllocPost.byteFrame {u v : MachineState} (h : AllocPost u v) :
    ByteFrame u v (Within · nextAddr 8) :=
  ByteFrame.of_dwords (fun a _ ha ↦ h.mem a fun h' ↦ ha (by rw [h']; addr_omega []))
    (fun a ha ↦ h.mem a fun h' ↦ ha (by rw [h']; decide))
    fun _ ha ↦ within_of_alignDown (by decide) (by decide) ha

/-- A block that writes nothing. -/
theorem ByteFrame.of_same {u v : MachineState} (h : ∀ a, v.getMem a = u.getMem a)
    (W : Word → Prop) : ByteFrame u v W :=
  ⟨fun a _ ↦ by simp only [byteAt_eq, h], fun a _ ↦ h a⟩

/-! ## Blocks checked against expectations written by hand -/

def cfg : Sym.Config := { noAlias := true }

/-- The callee-saved registers but `sp`. -/
def saved : List Reg := [.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- A block of the image at `e` meets `x`. -/
abbrev Spec (e : Word) (x : Sym.Expect) : Prop :=
  Sym.BlockSpec Image.code e x.steps (fun s ↦ Sym.Oblig.all s x.obl) x.Holds

/-- A block of `n` words of the image at `e`, from one kernel check. -/
theorem spec_of {x : Sym.Expect} {e : Word} (i n : Nat)
    (hrun : (Sym.symRun cfg ((Image.code.words.drop i).take n) e n).any (·.meets cfg x) = true)
    (hpc : e.toNat = Image.code.base.toNat + 4 * i) (h4 : e.toNat % 4 = 0)
    (hr : e.toNat + 4 * n < 2 ^ 64) : Spec e x :=
  Sym.BlockSpec.of_expect hrun (Sym.CodeAt.slice Image.code i n e hpc h4 hr) (fun _ h ↦ h)
    fun _ _ _ h ↦ h

end Rv64Verifier.Runtime
