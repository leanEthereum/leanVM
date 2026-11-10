import Rv64Verifier.Proofs.Bus.VbbTail22
import Rv64Verifier.Proofs.Layout.Clone
import Rv64Verifier.Proofs.Layout.BusBridge

/-!
# `verify_bus_balance` past the GKR loop: the layout's frames

A run writes only aligned doublewords: `SD` traps when misaligned, a narrower store writes its
doubleword, an accelerator its operands, all aligned (`reaches_unaligned`). So a frame of the
layout's contracts, which says nothing of the doublewords whose bytes wrap past the top of memory,
is one of the bus's (`layoutFrame`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## Unaligned doublewords -/

theorem getMem_setMem_unaligned {s : MachineState} {a b v : Word} (hb : b.toNat % 8 = 0)
    (ha : a.toNat % 8 ≠ 0) : (s.setMem b v).getMem a = s.getMem a :=
  MachineState.getMem_setMem_ne fun h ↦ ha (h ▸ hb)

theorem alignToDword_aligned (x : Word) : (alignToDword x).toNat % 8 = 0 := by
  simp only [alignToDword, toNat_alignDown]
  omega

theorem writeWords_unaligned {a : Word} (ha : a.toNat % 8 ≠ 0) :
    ∀ (s : MachineState) (b : Word) (ws : List Word), b.toNat % 8 = 0 →
      (s.writeWords b ws).getMem a = s.getMem a
  | _, _, [], _ => rfl
  | s, b, w :: ws, hb => by
    simp only [MachineState.writeWords]
    rw [writeWords_unaligned ha _ (b + 8) ws (by
      rw [BitVec.toNat_add, show (8 : Word).toNat = 8 from rfl]; omega)]
    exact getMem_setMem_unaligned hb ha

theorem validDwordRange_aligned {p : Word} {n : Nat} (hn : 0 < n)
    (h : MachineState.validDwordRange p n = true) : p.toNat % 8 = 0 := by
  simp only [MachineState.validDwordRange, List.all_eq_true, List.mem_range] at h
  have := h 0 hn
  simp only [isValidDwordAccess, isAligned8, Bool.and_eq_true, beq_iff_eq] at this
  simpa using this.2

/-- The written block's base is one of the validated ranges'. -/
macro "aligned_tac" : tactic => `(tactic| (
  try casesm* _ ∧ _
  first
  | exact Or.inl (validDwordRange_aligned (n := 25) (by decide) (by with_reducible assumption))
  | exact Or.inl (validDwordRange_aligned (n := 3) (by decide) (by with_reducible assumption))
  | exact Or.inl (validDwordRange_aligned (n := 4) (by decide) (by with_reducible assumption))
  | exact Or.inl (validDwordRange_aligned (n := 6) (by decide) (by with_reducible assumption))
  | exact Or.inl (validDwordRange_aligned (n := 8) (by decide) (by with_reducible assumption))
  | exact Or.inl (validDwordRange_aligned (n := 12) (by decide) (by with_reducible assumption))
  | exact Or.inl (validDwordRange_aligned (n := 16) (by decide) (by with_reducible assumption))))

theorem or3_pos {c a b d : BitVec 12} (h : (c = a ∨ c = b) ∨ c = d) :
    (decide (c = a) || decide (c = b) || decide (c = d)) = true := by
  simp only [Bool.or_eq_true, decide_eq_true_eq]; exact h

theorem or3_neg {c a b d : BitVec 12} (ha : ¬ c = a) (hb : ¬ c = b) (hd : ¬ c = d) :
    ¬ (decide (c = a) || decide (c = b) || decide (c = d)) = true := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]; exact ⟨⟨ha, hb⟩, hd⟩

theorem csrsWrite_aligned {s : MachineState} {csr : BitVec 12} {rs1 : Reg}
    (h : s.csrsValid csr rs1 = true) :
    (s.csrsWrite csr rs1).1.toNat % 8 = 0 ∨ (s.csrsWrite csr rs1).2 = [] := by
  unfold MachineState.csrsValid at h
  unfold MachineState.csrsWrite
  dsimp only at h ⊢
  by_cases c0 : csr = 0x800
  · rw [ite_eq_left c0] at h
    rw [ite_eq_left c0]
    aligned_tac
  by_cases c1 : csr = 0x802
  · rw [ite_eq_right c0, ite_eq_left c1] at h
    rw [ite_eq_right c0, ite_eq_left c1]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c2 : csr = 0x805
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_left c2] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_left c2]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c3 : csr = 0x803
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_left c3] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_left c3]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c4 : csr = 0x804
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_left c4] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_left c4]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c5 : csr = 0x806
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_left c5] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_left c5]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c6 : csr = 0x807
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_left c6] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_left c6]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c7 : csr = 0x808
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_left (or3_pos (Or.inl (Or.inl c7)))] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_left c7]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c8 : csr = 0x809
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_left (or3_pos (Or.inl (Or.inr c8)))] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right c7, ite_eq_left c8]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c9 : csr = 0x80A
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_left (or3_pos (Or.inr c9))] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right c7, ite_eq_right c8, ite_eq_left c9]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c10 : csr = 0x80B
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right (or3_neg c7 c8 c9), ite_eq_left c10] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right c7, ite_eq_right c8, ite_eq_right c9,
      ite_eq_left c10]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c11 : csr = 0x80C
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right (or3_neg c7 c8 c9), ite_eq_right c10,
      ite_eq_left c11] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right c7, ite_eq_right c8, ite_eq_right c9,
      ite_eq_right c10, ite_eq_left c11]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c12 : csr = 0x80D
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right (or3_neg c7 c8 c9), ite_eq_right c10,
      ite_eq_right c11, ite_eq_left c12] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right c7, ite_eq_right c8, ite_eq_right c9,
      ite_eq_right c10, ite_eq_right c11, ite_eq_left c12]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c13 : csr = 0x80E
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right (or3_neg c7 c8 c9), ite_eq_right c10,
      ite_eq_right c11, ite_eq_right c12, ite_eq_left (or3_pos (Or.inl (Or.inl c13)))] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right c7, ite_eq_right c8, ite_eq_right c9,
      ite_eq_right c10, ite_eq_right c11, ite_eq_right c12, ite_eq_left c13]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c14 : csr = 0x80F
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right (or3_neg c7 c8 c9), ite_eq_right c10,
      ite_eq_right c11, ite_eq_right c12, ite_eq_left (or3_pos (Or.inl (Or.inr c14)))] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right c7, ite_eq_right c8, ite_eq_right c9,
      ite_eq_right c10, ite_eq_right c11, ite_eq_right c12, ite_eq_right c13, ite_eq_left c14]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c15 : csr = 0x810
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right (or3_neg c7 c8 c9), ite_eq_right c10,
      ite_eq_right c11, ite_eq_right c12, ite_eq_left (or3_pos (Or.inr c15))] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right c7, ite_eq_right c8, ite_eq_right c9,
      ite_eq_right c10, ite_eq_right c11, ite_eq_right c12, ite_eq_right c13, ite_eq_right c14,
      ite_eq_left c15]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  by_cases c16 : csr = 0x819
  · rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right (or3_neg c7 c8 c9), ite_eq_right c10,
      ite_eq_right c11, ite_eq_right c12, ite_eq_right (or3_neg c13 c14 c15), ite_eq_left c16] at h
    rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
      ite_eq_right c5, ite_eq_right c6, ite_eq_right c7, ite_eq_right c8, ite_eq_right c9,
      ite_eq_right c10, ite_eq_right c11, ite_eq_right c12, ite_eq_right c13, ite_eq_right c14,
      ite_eq_right c15, ite_eq_left c16]
    try simp only [Bool.and_eq_true] at h
    aligned_tac
  rw [ite_eq_right c0, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4,
    ite_eq_right c5, ite_eq_right c6, ite_eq_right (or3_neg c7 c8 c9), ite_eq_right c10,
    ite_eq_right c11, ite_eq_right c12, ite_eq_right (or3_neg c13 c14 c15), ite_eq_right c16] at h
  cases h

theorem isValidDwordAccess_aligned {a : Word} (h : isValidDwordAccess a = true) :
    a.toNat % 8 = 0 := by
  simp only [isValidDwordAccess, isAligned8, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- One step keeps every unaligned doubleword. -/
theorem rstep_unaligned {s t : MachineState} (h : RiscvZkvm.Rv64.step s = some t) {a : Word}
    (ha : a.toNat % 8 ≠ 0) : t.getMem a = s.getMem a := by
  unfold RiscvZkvm.Rv64.step at h
  rcases hc : s.code s.pc with _ | i
  · rw [hc] at h; cases h
  rw [hc] at h
  cases i <;> simp only at h <;> (repeat' split at h) <;> (try cases h) <;>
    simp only [execInstrBr, MachineState.getMem_setPC, MachineState.getMem_setReg]
  all_goals first
    | rfl
    | (split <;> simp only [MachineState.getMem_setPC])
    | exact getMem_setMem_unaligned (isValidDwordAccess_aligned ‹_›) ha
    | (simp only [MachineState.setWord32, MachineState.setByte, MachineState.setHalfword]
       exact getMem_setMem_unaligned (alignToDword_aligned _) ha)
    | (rename_i hv
       simp only [Bool.and_eq_true] at hv
       rw [getMem_setMem_unaligned (isValidDwordAccess_aligned hv.2) ha,
         getMem_setMem_unaligned (isValidDwordAccess_aligned hv.1) ha])
    | (rename_i hv
       simp only [MachineState.execCsrs]
       rcases csrsWrite_aligned hv with h1 | h1
       · exact writeWords_unaligned ha _ _ _ h1
       · rw [h1]; rfl)

/-- A run keeps every unaligned doubleword. -/
theorem steps_unaligned {code : Code} {a : Word} (ha : a.toNat % 8 ≠ 0) :
    ∀ (n : Nat) (s t : MachineState), Steps code n s t → t.getMem a = s.getMem a
  | 0, _, _, h => by cases h; rfl
  | n + 1, s, t, ⟨s', hs, h⟩ => by
    rw [steps_unaligned ha n s' t h]
    simp only [step] at hs
    split at hs
    · cases hs
    · exact rstep_unaligned hs ha
    · cases hs; simp only [MachineState.getMem_setPC, MachineState.getMem_setReg]
    · cases hs; simp only [MachineState.getMem_setPC, MachineState.getMem_setReg]

theorem reaches_unaligned {code : Code} {s t : MachineState} (h : Reaches code s t) {a : Word}
    (ha : a.toNat % 8 ≠ 0) : t.getMem a = s.getMem a :=
  let ⟨n, hn⟩ := h
  steps_unaligned ha n s t hn

/-- A layout contract's frame, along a run, is one of the bus's. -/
theorem layoutFrame {s t : MachineState} {w : Word → Prop} (hr : Reaches Image.code s t)
    (h : Layout.DFrame s t w) : DFrame s t w := by
  intro a ha
  by_cases h8 : a.toNat % 8 = 0
  · have hlt := a.isLt
    refine h a (fun x hx hw ↦ ?_) (by omega)
    have hx' := hx
    simp only [Within] at hx'
    have e : a + BitVec.ofNat 64 (x.toNat - a.toNat) = x := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := x.isLt
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    exact ha (x.toNat - a.toNat) (by omega) (by rw [e]; exact hw)
  · exact reaches_unaligned hr h8

/-! ## A row of empty forms -/

/-- The `j`-th form of the `Vec<Form>` at `a`. -/
def cellAt (t : MachineState) (a : Word) (j : Nat) : Word := vecPtr t a + BitVec.ofNat 64 (24 * j)

/-- A row of `vec![Form::default(); 3]`: a `Vec` of three empty forms of capacity zero, its buffer
allocated from `b` on. -/
structure RowOk (b t : MachineState) (a : Word) : Prop where
  vec : VecOk t a 24 8
  len : vecLen t a = 3
  buf : NewBuf b t (vecPtr t a) ((vecCap t a).toNat * 24) 8
  cells : ∀ j < 3, vecCap t (cellAt t a j) = 0 ∧ vecLen t (cellAt t a j) = 0 ∧
    (vecPtr t (cellAt t a j)).toNat % 8 = 0

theorem RowOk.cap {b t : MachineState} {a : Word} (h : RowOk b t a) : 3 ≤ (vecCap t a).toNat := by
  have := h.vec.len
  rw [h.len] at this
  exact this

/-- The row's buffer lies in the heap allocated from `b` on. -/
theorem RowOk.bufIn {b t : MachineState} {a : Word} (h : RowOk b t a) :
    (vecPtr t a).toNat % 8 = 0 ∧ heapNext b ≤ (vecPtr t a).toNat ∧
      (vecPtr t a).toNat + (vecCap t a).toNat * 24 ≤ heapNext t := by
  have hb := h.buf
  have hc := h.cap
  simp only [NewBuf] at hb
  rcases hb.2 with h0 | h0
  · omega
  · exact ⟨hb.1, h0⟩

theorem RowOk.widen {b b' t : MachineState} {a : Word} (h : RowOk b t a)
    (hm : heapNext b' ≤ heapNext b) : RowOk b' t a := by
  have hb := h.buf
  simp only [NewBuf] at hb
  exact ⟨h.vec, h.len, ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨by omega, h'.2⟩⟩, h.cells⟩

/-- A row whose header words and buffer a frame keeps. -/
theorem RowOk.move {b t v : MachineState} {a a' : Word} {w : Word → Prop} (h : RowOk b t a')
    (fr : DFrame t v w) (hm : heapNext t ≤ heapNext v)
    (h0 : v.getMem a = t.getMem a') (h8 : v.getMem (a + 8) = t.getMem (a' + 8))
    (h16 : v.getMem (a + 16) = t.getMem (a' + 16))
    (hbuf : ∀ x, Within x (vecPtr t a') ((vecCap t a').toNat * 24) → ¬ w x) :
    RowOk b v a := by
  obtain ⟨q0, q1, q2⟩ := h.bufIn
  have hc := h.cap
  have hp : vecPtr v a = vecPtr t a' := h8
  have hcp : vecCap v a = vecCap t a' := h0
  have hl : vecLen v a = vecLen t a' := h16
  have hbd : (vecPtr t a').toNat + (vecCap t a').toNat * 24 ≤ 2 ^ 64 := by
    have := (t.getMem nextAddr).isLt
    simp only [heapNext] at q2
    omega
  have bw (j : Nat) (hj : j < 3) (k : Nat) (hk : k ≤ 16) :
      v.getMem (vecPtr t a' + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 k) =
        t.getMem (vecPtr t a' + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 k) :=
    fr _ fun i hi hw ↦ hbuf _ (by simp only [Within]; addr_omega [hbd, hj, hk, hi, hc]) hw
  have hvec := h.vec
  refine ⟨⟨?_, ?_⟩, by rw [hl]; exact h.len, ?_, fun j hj ↦ ?_⟩
  · have hraw := hvec.raw
    simp only [RawVecOk, Buf, hp, hcp] at hraw ⊢
    exact ⟨hraw.1, hraw.2.imp id fun h' ↦ ⟨h'.1, Nat.le_trans h'.2 hm⟩⟩
  · rw [hcp, hl]; exact hvec.len
  · have hb := h.buf
    simp only [NewBuf, hp, hcp] at hb ⊢
    exact ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
  · obtain ⟨c0, c1, c2⟩ := h.cells j hj
    have c0' : t.getMem (vecPtr t a' + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 0) = 0 := by
      rw [add_ofNat_zero]; exact c0
    have c1' : t.getMem (vecPtr t a' + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 16) = 0 := c1
    have c2' : (t.getMem (vecPtr t a' + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 8)).toNat % 8 =
      0 := c2
    simp only [cellAt, vecCap, vecLen, vecPtr] at ⊢
    rw [h8]
    refine ⟨?_, ?_, ?_⟩
    · show v.getMem (vecPtr t a' + BitVec.ofNat 64 (24 * j)) = 0
      rw [← add_ofNat_zero (vecPtr t a' + BitVec.ofNat 64 (24 * j)), bw j hj 0 (by omega)]
      exact c0'
    · show v.getMem (vecPtr t a' + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 16) = 0
      rw [bw j hj 16 (by omega)]; exact c1'
    · show (v.getMem (vecPtr t a' + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 8)).toNat % 8 = 0
      rw [bw j hj 8 (by omega)]; exact c2'

/-- A row's statement value: three empty forms. -/
theorem RowOk.value {b t : MachineState} {a : Word} (h : RowOk b t a) :
    formVecAt t a = List.replicate 3 {} := by
  have e : ∀ j ∈ List.range 3,
      (formAt t (vecPtr t a + BitVec.ofNat 64 (24 * j))).toSpec = ({} : Form) := by
    intro j hj
    have hz := (h.cells j (List.mem_range.mp hj)).2.1
    simp only [cellAt] at hz
    simp only [formAt, hz]
    rfl
  simp only [formVecAt, h.len, show (3 : Word).toNat = 3 from rfl]
  rw [List.map_congr_left e, List.map_const', List.length_range]

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
