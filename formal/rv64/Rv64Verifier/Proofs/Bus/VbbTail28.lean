import Rv64Verifier.Proofs.Bus.VbbTail27

/-!
# `verify_bus_balance` past the side loop: what the heap keeps

From the side loop's last iteration to the return, the heap allocated since the entry and below
`z`'s `NEXT` (the claims, the points) is kept (`HeapKept`), and with it every `Vec` it holds
(`NewVecE.heapKept`, `ClaimsOk.heapKept`); the matrix's forms keep their values
(`formRowsAt_keep`); a step writing the frame below the saved registers, `NEXT`, the heap from the
entry's `NEXT` on and the result keeps the transcript (`Inv.transcriptW`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- The heap from `s`'s `NEXT` up to `B`, kept from `u` to `t`. -/
def HeapKept (s u t : MachineState) (B : Nat) : Prop :=
  ∀ x : Word, heapNext s ≤ x.toNat → x.toNat + 8 ≤ B → t.getMem x = u.getMem x

theorem eListAt_heapKept {s u t : MachineState} {B : Nat} (hk : HeapKept s u t B)
    (hu : heapNext u ≤ heapEnd) (hB : heapNext u ≤ B) {p : Word} {m k : Nat}
    (hb : NewBuf s u p m 8) (hm : 24 * k ≤ m) : eListAt t p k = eListAt u p k := by
  refine eListAt_congr fun i hi ↦ ?_
  simp only [NewBuf] at hb
  simp only [heapNext, heapEnd] at hu hB
  rcases hb.2 with h0 | ⟨b1, b2⟩
  · omega
  simp only [heapNext] at b1 b2
  have bw (j : Nat) (hj : j + 8 ≤ 24) : t.getMem (p + BitVec.ofNat 64 (24 * i) +
      BitVec.ofNat 64 j) = u.getMem (p + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 j) :=
    hk _ (by simp only [heapNext]; addr_omega [b1, b2, hu, hi, hm, hj])
      (by addr_omega [b1, b2, hu, hB, hi, hm, hj])
  exact eAt_congr (by simpa using bw 0 (by omega)) (bw 8 (by omega)) (bw 16 (by omega))

theorem _root_.Rv64Verifier.Transcript.NewVecE.heapKept {s u t : MachineState} {B : Nat}
    {a b : Word} {xs : List E} (h : NewVecE s u a xs) (hk : HeapKept s u t B)
    (hu : heapNext u ≤ heapEnd) (hB : heapNext u ≤ B) (hm : heapNext u ≤ heapNext t)
    (e0 : t.getMem b = u.getMem a) (e8 : t.getMem (b + 8) = u.getMem (a + 8))
    (e16 : t.getMem (b + 16) = u.getMem (a + 16)) : NewVecE s t b xs :=
  h.transfer e0 e8 e16 hm
    (eListAt_heapKept hk hu hB h.buf (by have := h.vec.len; omega))

/-- A doubleword `j` bytes into `a`, with `a` in the kept heap. -/
theorem HeapKept.at {s u t : MachineState} {B : Nat} (hk : HeapKept s u t B)
    (hB : B ≤ heapEnd) {a : Word} {m : Nat}
    (h1 : heapNext s ≤ a.toNat) (h2 : a.toNat + m ≤ B) {j : Nat} (hj : j + 8 ≤ m) :
    t.getMem (a + BitVec.ofNat 64 j) = u.getMem (a + BitVec.ofNat 64 j) := by
  simp only [heapNext, heapEnd] at hB h1
  exact hk _ (by simp only [heapNext]; addr_omega [h1, h2, hB, hj])
    (by addr_omega [h1, h2, hB, hj])

theorem ClaimAt.heapKept {s u t : MachineState} {B : Nat} {a : Word} {c : ColumnClaim}
    (h : ClaimAt s u a c) (hk : HeapKept s u t B) (hu : heapNext u ≤ heapEnd) (hBu : heapNext u ≤ B)
    (hB : B ≤ heapEnd) (hm : heapNext u ≤ heapNext t) (h1 : heapNext s ≤ a.toNat)
    (h2 : a.toNat + 56 ≤ B) : ClaimAt s t a c := by
  have w (j : Nat) (hj : j + 8 ≤ 56) := hk.at hB h1 h2 hj
  refine ⟨h.vec.heapKept hk hu hBu hm (by simpa using w 0 (by omega)) (w 8 (by omega))
    (w 16 (by omega)), ?_, ?_, h.lo.move (w 8 (by omega)) (w 16 (by omega)) hm⟩
  · rw [show a + 24 = a + BitVec.ofNat 64 24 from rfl, w 24 (by omega)]; exact h.column
  · rw [← h.value]
    have e40 : a + 32 + 8 = a + BitVec.ofNat 64 40 := by rw [BitVec.add_assoc]; rfl
    have e48 : a + 32 + 16 = a + BitVec.ofNat 64 48 := by rw [BitVec.add_assoc]; rfl
    exact eAt_congr (w 32 (by omega)) (by rw [e40]; exact w 40 (by omega))
      (by rw [e48]; exact w 48 (by omega))

theorem ClaimsOk.heapKept {s u t : MachineState} {B : Nat} {cap ptr len : Word}
    {cs : List ColumnClaim} (h : ClaimsOk s u cap ptr len cs) (hk : HeapKept s u t B)
    (hu : heapNext u ≤ heapEnd) (hBu : heapNext u ≤ B) (hB : B ≤ heapEnd)
    (hm : heapNext u ≤ heapNext t) (hl : 0 < len.toNat) : ClaimsOk s t cap ptr len cs := by
  obtain ⟨⟨hle, hbuf, hlen, hcl⟩, hap⟩ := h
  have hb := hbuf
  simp only [NewBuf] at hb
  have hb2 : heapNext s ≤ ptr.toNat ∧ ptr.toNat + 56 * cap.toNat ≤ heapNext u := by
    rcases hb.2 with h0 | h0
    · omega
    · exact h0
  have hc (i : Nat) (hi : i < len.toNat) : (ptr + BitVec.ofNat 64 (56 * i)).toNat =
      ptr.toNat + 56 * i := by
    simp only [heapNext, heapEnd] at hu hb2; addr_omega [hb2, hi, hle, hu]
  refine ⟨⟨hle, ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩, hlen, fun i hi ↦ ?_⟩,
    fun i hi ↦ ?_⟩
  · have hi' : i < len.toNat := by omega
    exact (hcl i hi).heapKept hk hu hBu hB hm (by rw [hc i hi']; omega)
      (by rw [hc i hi']; have : 56 * i + 56 ≤ 56 * cap.toNat := by omega
          omega)
  · have hs := hc i hi
    have w (j : Nat) (hj : j + 8 ≤ 56) :=
      hk.at hB (a := ptr + BitVec.ofNat 64 (56 * i)) (m := 56) (by omega)
        (by have : 56 * i + 56 ≤ 56 * cap.toNat := by omega
            omega) hj
    have e0 : vecCap t (ptr + BitVec.ofNat 64 (56 * i)) = vecCap u (ptr + BitVec.ofNat 64 (56 * i)) :=
      by simpa [vecCap] using w 0 (by omega)
    have e8 : vecPtr t (ptr + BitVec.ofNat 64 (56 * i)) = vecPtr u (ptr + BitVec.ofNat 64 (56 * i)) :=
      w 8 (by omega)
    rw [e0, e8]
    exact hap i hi

/-- Two ranges no byte of which is in both are apart. -/
theorem apart_of_disjoint {a b : Word} {n m : Nat} (h : ∀ x, Within x a n → ¬ Within x b m) : Apart a n b m := by
  simp only [Apart]
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨h1, h2, h3, h4⟩ := hc
  rcases Nat.lt_or_ge a.toNat b.toNat with hl | hl
  · exact h b ⟨by omega, by omega⟩ ⟨le_refl _, by omega⟩
  · exact h a ⟨le_refl _, by omega⟩ ⟨hl, by omega⟩

/-- The forms' rows keep their value when their rows' headers and forms do. -/
theorem formRowsAt_keep {t t' : MachineState} {P : Word} {n : Nat}
    (hrows : ∀ i < n, vecLen t (rowAt P i) = 3)
    (hrow : ∀ i < n, ∀ k < 3, t'.getMem (rowAt P i + BitVec.ofNat 64 (8 * k)) =
      t.getMem (rowAt P i + BitVec.ofNat 64 (8 * k)))
    (hform : ∀ i < n, ∀ j < 3,
      Layout.formOf t' (cellAt t (rowAt P i) j) = Layout.formOf t (cellAt t (rowAt P i) j)) :
    formRowsAt t' P n = formRowsAt t P n := by
  have hp (i : Nat) (hi : i < n) : vecPtr t' (rowAt P i) = vecPtr t (rowAt P i) := by
    have h := hrow i hi 1 (by omega)
    simp only [Nat.mul_one] at h
    exact h
  have hl (i : Nat) (hi : i < n) : vecLen t' (rowAt P i) = vecLen t (rowAt P i) := by
    have h := hrow i hi 2 (by omega)
    simp only [show 8 * 2 = 16 from rfl] at h
    exact h
  simp only [formRowsAt]
  refine List.map_congr_left fun i hi ↦ ?_
  have hi' := List.mem_range.mp hi
  have hr : P + BitVec.ofNat 64 (24 * i) = rowAt P i := rfl
  rw [hr]
  simp only [formVecAt, hl i hi', hrows i hi']
  refine List.map_congr_left fun j hj ↦ ?_
  have hj' := List.mem_range.mp hj
  have e := hform i hi' j (by simpa [hrows i hi'] using hj')
  simp only [cellAt] at e
  simp only [Layout.formAt_eq, hp i hi', e]

/-- A step writing only the frame below the saved registers, `NEXT`, the heap from the entry's
`NEXT` on and the result keeps the transcript. -/
theorem Inv.transcriptW {s u v : MachineState} (hpre : BusBalancePre s) (h : Inv s u)
    (hf : DFrame u v fun a ↦ Within a (s.getReg .x2 - 4544) 4440 ∨ Within a nextAddr 8 ∨
      (heapNext s ≤ a.toNat ∧ a.toNat < heapEnd) ∨ Within a (s.getReg .x10) 120)
    {T : TState} (hT : TranscriptAt u (s.getReg .x12) T) : TranscriptAt v (s.getReg .x12) T := by
  obtain ⟨e0, e1, e2⟩ := h.stream hpre
  have hS := hpre.self.self
  have ss := hpre.selfStack
  have sf := hpre.selfFree
  have so := hpre.selfOut
  have ps := hpre.proofStack
  have po := hpre.proofOut
  have pf := hpre.proofFree
  have bf := hpre.streamFree
  rw [stackLo_eq, stack_eq] at ss ps
  simp only [ProofApart] at ps po
  simp only [Outside, heapNext, heapEnd] at pf bf sf
  have loc (lo : Word) (n : Nat) (h1 : Apart lo n (s.getReg .x2 - 4544) 4544)
      (h2 : Apart lo n nextAddr 8) (h3 : lo.toNat + n ≤ (s.getMem nextAddr).toNat ∨
        0x78000000 ≤ lo.toNat) (h4 : Apart lo n (s.getReg .x10) 120) :
      Misses (fun a ↦ Within a (s.getReg .x2 - 4544) 4440 ∨ Within a nextAddr 8 ∨
        (heapNext s ≤ a.toNat ∧ a.toNat < heapEnd) ∨ Within a (s.getReg .x10) 120) lo n :=
    fun y hy hl ↦ by
      simp only [heapNext, heapEnd] at hl
      rcases hl with hl | hl | hl | hl
      · addr_omega [hy, hl, h1]
      · addr_omega [hy, hl, h2]
      · addr_omega [hy, hl, h3]
      · addr_omega [hy, hl, h4]
  refine hf.transcriptAt hT (h.tok hpre) (loc _ _ (by addr_omega [ss, hS]) (by addr_omega [sf.2, hS])
    (by addr_omega [sf.1, hS]) (by addr_omega [so, hS])) ?_ ?_
    (loc _ _ (by addr_omega [ss, hS]) (by addr_omega [sf.2, hS]) (by addr_omega [sf.1, hS])
      (by addr_omega [so, hS]))
  · rw [e0]; exact loc _ _ ps.1 pf.2 pf.1 po.1
  · rw [e1, e2]; exact loc _ _ ps.2 bf.2 bf.1 po.2

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
