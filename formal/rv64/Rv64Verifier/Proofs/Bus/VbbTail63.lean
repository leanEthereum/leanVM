import Rv64Verifier.Proofs.Bus.VbbTail62

/-!
# `verify_bus_balance`'s side loop: the selectors' sums' loops

The inlined `E::sum` over the framework selectors (`0x80007b4c`, pointer `a4`) and over the tables'
(`0x80007b9c`, pointer `s4`), each adding an element on the left into `s3`, `s7`, `s2` (`sumLeft`),
reading only (`SumA`, `SumB`, `sumLoopA`, `sumLoopB`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem sumLeft_take_succ (a : E) (l : List E) {j : Nat} (hj : j < l.length) :
    sumLeft a (l.take (j + 1)) = l[j] + sumLeft a (l.take j) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, sumLeft, sumLeft,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `n` elements from `p`, in the heap. -/
def HeapArr (p : Word) (n : Nat) : Prop :=
  p.toNat % 8 = 0 ∧ heapStart ≤ p.toNat ∧ p.toNat + 24 * n ≤ heapEnd

/-- In the framework selectors' loop from `t₀`: `j` of the `n` elements `l` from `p` added to `a`. -/
structure SumA (t₀ t : MachineState) (p : Word) (n : Nat) (a : E) (l : List E) (j : Nat) :
    Prop where
  mem : ∀ x, t.getMem x = t₀.getMem x
  regs : ∀ r ∈ ([.x2, .x15, .x16, .x17, .x20, .x22, .x25] : List Reg), t.getReg r = t₀.getReg r
  x14 : t.getReg .x14 = p + BitVec.ofNat 64 (24 * j)
  x10 : t.getReg .x10 = p + BitVec.ofNat 64 (24 * n)
  sum : eOf3 (t.getReg .x19) (t.getReg .x23) (t.getReg .x18) = sumLeft a (l.take j)

/-- In the tables' selectors' loop from `t₀`: `j` of the `n` elements `l` from `p` added to `a`. -/
structure SumB (t₀ t : MachineState) (p : Word) (n : Nat) (a : E) (l : List E) (j : Nat) :
    Prop where
  mem : ∀ x, t.getMem x = t₀.getMem x
  regs : ∀ r ∈ ([.x2, .x15, .x16, .x17, .x22, .x25] : List Reg), t.getReg r = t₀.getReg r
  x20 : t.getReg .x20 = p + BitVec.ofNat 64 (24 * j)
  x10 : t.getReg .x10 = p + BitVec.ofNat 64 (24 * n)
  sum : eOf3 (t.getReg .x19) (t.getReg .x23) (t.getReg .x18) = sumLeft a (l.take j)

/-- Element `j`'s limbs added to a sum's. -/
theorem sum_step {t₀ t : MachineState} {p : Word} {n : Nat} {a : E} {l : List E} {j : Nat}
    (hl : eListAt t₀ p n = l) (hj : j < n) (hm : ∀ x, t.getMem x = t₀.getMem x)
    {x19 x23 x18 : Word} (hs : eOf3 x19 x23 x18 = sumLeft a (l.take j)) :
    eOf3 (t.getMem (p + BitVec.ofNat 64 (24 * j)) ^^^ x19)
      (t.getMem (p + BitVec.ofNat 64 (24 * j) + 8) ^^^ x23)
      (t.getMem (p + BitVec.ofNat 64 (24 * j) + 16) ^^^ x18) = sumLeft a (l.take (j + 1)) := by
  have hjl : j < l.length := by rw [← hl, eListAt_length]; exact hj
  rw [eOf3_xor, hs, sumLeft_take_succ a l hjl, hm, hm, hm, ← eAt_eq_eOf3]
  congr 1
  subst hl
  rw [eListAt_getElem]

set_option maxRecDepth 8192 in
theorem sumIterA {t₀ t : MachineState} {p : Word} {n : Nat} {a : E} {l : List E} {j : Nat}
    (hp : HeapArr p n) (hl : eListAt t₀ p n = l) (S : SumA t₀ t p n a l j) (hj : j < n)
    (hpc : t.pc = 0x80007b4c) :
    ∃ t', Reaches Image.code t t' ∧ SumA t₀ t' p n a l (j + 1) ∧
      ((j + 1 < n ∧ t'.pc = 0x80007b4c) ∨ (j + 1 = n ∧ t'.pc = 0x80007b6c)) := by
  obtain ⟨P8, Pl, Ph⟩ := hp
  simp only [heapStart, heapEnd] at Pl Ph
  have hv : ValidMemRange p (3 * n) :=
    heapRange P8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have x14 := S.x14
  obtain ⟨t', hr, hh⟩ := Sym.BlockSpec.reaches b80007b4c_spec hpc (by
    rv_eval [x14]; and_intros <;> valid_access hv [Pl, Ph, hj])
  have k := b80007b4c_keeps hh
  refine ⟨t', hr, ⟨fun x ↦ (b80007b4c_mem_same hh x).trans (S.mem x),
    fun r hr ↦ (k r (mem_of_mem hr _)).trans (S.regs r hr), ?_, ?_, ?_⟩, ?_⟩
  · rw [b80007b4c_x14 hh, x14]; apply BitVec.eq_of_toNat_eq; addr_omega [Pl, Ph, hj]
  · rw [k .x10 (by decide)]; exact S.x10
  · rw [b80007b4c_x19 hh, b80007b4c_x23 hh, b80007b4c_x18 hh, x14]
    exact sum_step hl hj S.mem S.sum
  · rcases Nat.lt_or_ge (j + 1) n with hlt | hge
    · refine Or.inl ⟨hlt, b80007b4c_pc_taken hh ?_⟩
      rw [x14, S.x10]; intro he
      have := congrArg BitVec.toNat he
      addr_omega [this, Pl, Ph, hj, hlt]
    · refine Or.inr ⟨by omega, b80007b4c_pc_not_taken hh ?_⟩
      rw [x14, S.x10]; apply BitVec.eq_of_toNat_eq
      addr_omega [Pl, Ph, hj, hge]

theorem sumLoopA {t₀ : MachineState} {p : Word} {n : Nat} {a : E} {l : List E}
    (hp : HeapArr p n) (hl : eListAt t₀ p n = l) :
    ∀ d j t, j + d + 1 = n → SumA t₀ t p n a l j → t.pc = 0x80007b4c →
      ∃ t', Reaches Image.code t t' ∧ SumA t₀ t' p n a l n ∧ t'.pc = 0x80007b6c := by
  intro d
  induction d with
  | zero =>
    intro j t hd S hpc
    obtain ⟨t', hr, S', ⟨hlt, -⟩ | ⟨he, hpc'⟩⟩ := sumIterA hp hl S (by omega) hpc
    · omega
    · rw [he] at S'; exact ⟨t', hr, S', hpc'⟩
  | succ d ih =>
    intro j t hd S hpc
    obtain ⟨t', hr, S', ⟨-, hpc'⟩ | ⟨he, -⟩⟩ := sumIterA hp hl S (by omega) hpc
    · obtain ⟨t'', hr', ht''⟩ := ih (j + 1) t' (by omega) S' hpc'
      exact ⟨t'', hr.trans hr', ht''⟩
    · omega

set_option maxRecDepth 8192 in
theorem sumIterB {t₀ t : MachineState} {p : Word} {n : Nat} {a : E} {l : List E} {j : Nat}
    (hp : HeapArr p n) (hl : eListAt t₀ p n = l) (S : SumB t₀ t p n a l j) (hj : j < n)
    (hpc : t.pc = 0x80007b9c) :
    ∃ t', Reaches Image.code t t' ∧ SumB t₀ t' p n a l (j + 1) ∧
      ((j + 1 < n ∧ t'.pc = 0x80007b9c) ∨ (j + 1 = n ∧ t'.pc = 0x80007bbc)) := by
  obtain ⟨P8, Pl, Ph⟩ := hp
  simp only [heapStart, heapEnd] at Pl Ph
  have hv : ValidMemRange p (3 * n) :=
    heapRange P8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have x20 := S.x20
  obtain ⟨t', hr, hh⟩ := Sym.BlockSpec.reaches b80007b9c_spec hpc (by
    rv_eval [x20]; and_intros <;> valid_access hv [Pl, Ph, hj])
  have k := b80007b9c_keeps hh
  refine ⟨t', hr, ⟨fun x ↦ (b80007b9c_mem_same hh x).trans (S.mem x),
    fun r hr ↦ (k r (mem_of_mem hr _)).trans (S.regs r hr), ?_, ?_, ?_⟩, ?_⟩
  · rw [b80007b9c_x20 hh, x20]; apply BitVec.eq_of_toNat_eq; addr_omega [Pl, Ph, hj]
  · rw [k .x10 (by decide)]; exact S.x10
  · rw [b80007b9c_x19 hh, b80007b9c_x23 hh, b80007b9c_x18 hh, x20]
    exact sum_step hl hj S.mem S.sum
  · rcases Nat.lt_or_ge (j + 1) n with hlt | hge
    · refine Or.inl ⟨hlt, b80007b9c_pc_taken hh ?_⟩
      rw [x20, S.x10]; intro he
      have := congrArg BitVec.toNat he
      addr_omega [this, Pl, Ph, hj, hlt]
    · refine Or.inr ⟨by omega, b80007b9c_pc_not_taken hh ?_⟩
      rw [x20, S.x10]; apply BitVec.eq_of_toNat_eq
      addr_omega [Pl, Ph, hj, hge]

theorem sumLoopB {t₀ : MachineState} {p : Word} {n : Nat} {a : E} {l : List E}
    (hp : HeapArr p n) (hl : eListAt t₀ p n = l) :
    ∀ d j t, j + d + 1 = n → SumB t₀ t p n a l j → t.pc = 0x80007b9c →
      ∃ t', Reaches Image.code t t' ∧ SumB t₀ t' p n a l n ∧ t'.pc = 0x80007bbc := by
  intro d
  induction d with
  | zero =>
    intro j t hd S hpc
    obtain ⟨t', hr, S', ⟨hlt, -⟩ | ⟨he, hpc'⟩⟩ := sumIterB hp hl S (by omega) hpc
    · omega
    · rw [he] at S'; exact ⟨t', hr, S', hpc'⟩
  | succ d ih =>
    intro j t hd S hpc
    obtain ⟨t', hr, S', ⟨-, hpc'⟩ | ⟨he, -⟩⟩ := sumIterB hp hl S (by omega) hpc
    · obtain ⟨t'', hr', ht''⟩ := ih (j + 1) t' (by omega) S' hpc'
      exact ⟨t'', hr.trans hr', ht''⟩
    · omega

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
