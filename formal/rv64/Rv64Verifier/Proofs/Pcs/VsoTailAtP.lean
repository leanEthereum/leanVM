import Rv64Verifier.Proofs.Pcs.VsoTailAtK

/-!
# `verify_stacked_opening`'s level tail: the pending claims kept

`PendOk.keep`: a frame that misses the heap allocated between `t` and `u` and the pending claims'
header keeps `PendOk`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- The pending claims' words and buffers, read at `r` as at `u`. -/
theorem PendOk.words {t u r : MachineState} {A : Word}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {X : Word → Prop}
    (hP : PendOk u t A pend) (hu : HeapOk u) (hF : DFrame u r X)
    (hX : ∀ y, heapNext t ≤ y.toNat → y.toNat < heapNext u → ¬ X y) {i : ℕ}
    (hi : i < (vecLen u A).toNat) {o : ℕ} (ho : o + 8 ≤ 80) :
    r.getMem (vecPtr u A + BitVec.ofNat 64 (80 * i) + BitVec.ofNat 64 o) =
      u.getMem (vecPtr u A + BitVec.ofNat 64 (80 * i) + BitVec.ofNat 64 o) := by
  have hraw := hP.vec.raw
  simp only [RawVecOk, Buf] at hraw
  have hl := hP.vec.len
  have hhi := hu.hi
  simp only [heapEnd] at hhi
  rcases hraw.2 with h0 | h0
  · omega
  refine hF _ fun j hj hw ↦ ?_
  have hW : Within (vecPtr u A + BitVec.ofNat 64 (80 * i) + BitVec.ofNat 64 o + BitVec.ofNat 64 j)
      (vecPtr u A) ((vecCap u A).toNat * 80) := by
    simp only [Within]; addr_omega [h0, hi, hl, ho, hj, hhi]
  have hf := hP.fresh _ (Or.inl hW)
  exact hX _ hf.1 hf.2 hw

/-- A byte of the pending claims' buffers is fresh between `t` and `u`. -/
theorem PendOk.bytes {t u : MachineState} {A : Word}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} (hP : PendOk u t A pend) {y : Word}
    (hy : PBufs u A y) : heapNext t ≤ y.toNat ∧ y.toNat < heapNext u :=
  hP.fresh y hy

theorem addOf (e : Word) (a b : ℕ) :
    e + BitVec.ofNat 64 a + BitVec.ofNat 64 b = e + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Element `i`'s words at `r` as at `u`: the intro's header, the weight's tag and the point's
header. -/
theorem PendOk.elem {t u r : MachineState} {A : Word}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {X : Word → Prop}
    (hP : PendOk u t A pend) (hu : HeapOk u) (hF : DFrame u r X)
    (hX : ∀ y, heapNext t ≤ y.toNat → y.toNat < heapNext u → ¬ X y) {i : ℕ}
    (hi : i < (vecLen u A).toNat) :
    vecCap r (vecPtr u A + BitVec.ofNat 64 (80 * i)) =
        vecCap u (vecPtr u A + BitVec.ofNat 64 (80 * i)) ∧
      vecPtr r (vecPtr u A + BitVec.ofNat 64 (80 * i)) =
          vecPtr u (vecPtr u A + BitVec.ofNat 64 (80 * i)) ∧
      vecLen r (vecPtr u A + BitVec.ofNat 64 (80 * i)) =
          vecLen u (vecPtr u A + BitVec.ofNat 64 (80 * i)) ∧
      r.getMem ((vecPtr u A + BitVec.ofNat 64 (80 * i)) + 24) =
          u.getMem ((vecPtr u A + BitVec.ofNat 64 (80 * i)) + 24) ∧
      vecCap r ((vecPtr u A + BitVec.ofNat 64 (80 * i)) + 24 + 8) =
          vecCap u ((vecPtr u A + BitVec.ofNat 64 (80 * i)) + 24 + 8) ∧
      vecPtr r ((vecPtr u A + BitVec.ofNat 64 (80 * i)) + 24 + 8) =
          vecPtr u ((vecPtr u A + BitVec.ofNat 64 (80 * i)) + 24 + 8) ∧
      vecLen r ((vecPtr u A + BitVec.ofNat 64 (80 * i)) + 24 + 8) =
          vecLen u ((vecPtr u A + BitVec.ofNat 64 (80 * i)) + 24 + 8) := by
  set e := vecPtr u A + BitVec.ofNat 64 (80 * i) with he
  have kw (o : ℕ) (ho : o + 8 ≤ 80) : r.getMem (e + BitVec.ofNat 64 o) =
      u.getMem (e + BitVec.ofNat 64 o) := hP.words hu hF hX hi ho
  refine ⟨?_, kw 8 (by omega), kw 16 (by omega), kw 24 (by omega), ?_, ?_, ?_⟩
  · have := kw 0 (by omega); rw [add_ofNat_zero] at this; exact this
  · show r.getMem (e + BitVec.ofNat 64 24 + BitVec.ofNat 64 8) =
      u.getMem (e + BitVec.ofNat 64 24 + BitVec.ofNat 64 8)
    rw [addOf]; exact kw 32 (by omega)
  · show r.getMem (e + BitVec.ofNat 64 24 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) =
      u.getMem (e + BitVec.ofNat 64 24 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8)
    rw [addOf, addOf]; exact kw 40 (by omega)
  · show r.getMem (e + BitVec.ofNat 64 24 + BitVec.ofNat 64 8 + BitVec.ofNat 64 16) =
      u.getMem (e + BitVec.ofNat 64 24 + BitVec.ofNat 64 8 + BitVec.ofNat 64 16)
    rw [addOf, addOf]; exact kw 48 (by omega)

/-- A byte of the pending claims' buffers at `r` is one at `u`. -/
theorem PendOk.pbufs {t u r : MachineState} {A : Word}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {X : Word → Prop}
    (hP : PendOk u t A pend) (hu : HeapOk u) (hF : DFrame u r X)
    (hX : ∀ y, heapNext t ≤ y.toNat → y.toNat < heapNext u → ¬ X y)
    (h8 : vecPtr r A = vecPtr u A) {i : ℕ} (hi : i < (vecLen u A).toNat) {y : Word}
    (hy : Within y (vecPtr r (vecPtr r A + BitVec.ofNat 64 (80 * i)))
        ((vecCap r (vecPtr r A + BitVec.ofNat 64 (80 * i))).toNat * 24) ∨
      InBufs r (vecPtr r A + BitVec.ofNat 64 (80 * i) + 24) y) :
    Within y (vecPtr u (vecPtr u A + BitVec.ofNat 64 (80 * i)))
        ((vecCap u (vecPtr u A + BitVec.ofNat 64 (80 * i))).toNat * 24) ∨
      InBufs u (vecPtr u A + BitVec.ofNat 64 (80 * i) + 24) y := by
  obtain ⟨c0, c8, c16, c24, d0, d8, d16⟩ := hP.elem hu hF hX hi
  have hood := (hP.ood i hi).1
  rw [h8] at hy
  rcases hy with hy | hy
  · rw [c8, c0] at hy; exact Or.inl hy
  · right
    simp only [InBufs] at hy ⊢
    rw [c24, ite_eq_left_of_eq_true _ _ (eq_true hood)] at hy
    rw [ite_eq_left_of_eq_true _ _ (eq_true hood)]
    rw [d8, d16] at hy
    exact hy

/-- **`PendOk` kept** by a frame missing the pending claims' header and the heap allocated
between `t` and `u`. -/
theorem PendOk.keep {t u r : MachineState} {A : Word}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {X : Word → Prop}
    (hP : PendOk u t A pend) (hu : HeapOk u) (hF : DFrame u r X)
    (hX : ∀ y, heapNext t ≤ y.toNat → y.toNat < heapNext u → ¬ X y)
    (h0 : vecCap r A = vecCap u A) (h8 : vecPtr r A = vecPtr u A) (h16 : vecLen r A = vecLen u A)
    (hur : heapNext u ≤ heapNext r) :
    PendOk r t A pend ∧ ∀ y, PBufs r A y → y.toNat < heapNext u := by
  have pb (y : Word) (hy : PBufs r A y) : PBufs u A y := by
    rcases hy with hy | ⟨i, hi, hy⟩
    · rw [h8, h0] at hy; exact Or.inl hy
    · rw [h16] at hi
      exact Or.inr ⟨i, hi, hP.pbufs hu hF hX h8 hi hy⟩
  have hraw := hP.vec.raw
  simp only [RawVecOk, Buf] at hraw
  refine ⟨{ vec := ⟨?_, by rw [h16, h0]; exact hP.vec.len⟩
            elems := ?_
            intro := fun i hi ↦ ?_
            ood := fun i hi ↦ ?_
            fresh := fun y hy ↦ ?_
            self := fun i hi y hy ↦ ?_ }, fun y hy ↦ (hP.fresh y (pb y hy)).2⟩
  · simp only [RawVecOk, Buf]
    rw [h8, h0]
    exact ⟨hraw.1, hraw.2.imp id fun h ↦ ⟨h.1, by omega⟩⟩
  · rw [h8, h16, ← hP.elems]
    simp only [pendAt]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    obtain ⟨c0, c8, c16, c24, d0, d8, d16⟩ := hP.elem hu hF hX hi
    have hood := (hP.ood i hi).1
    have hI := hP.intro i hi
    have hIr := hI.raw
    simp only [RawVecOk, Buf] at hIr
    have hIl := hI.len
    have hO := (hP.ood i hi).2
    have hOr := hO.raw
    simp only [RawVecOk, Buf] at hOr
    have hOl := hO.len
    have hhi := hu.hi
    simp only [heapEnd] at hhi
    refine Prod.ext ?_ ?_
    · simp only [vecEs]
      rw [c8, c16]
      refine hF.eListAt fun k hk ↦ ?_
      rcases hIr.2 with hz | hz
      · omega
      have hW : Within (vecPtr u (vecPtr u A + BitVec.ofNat 64 (80 * i)) + BitVec.ofNat 64 k)
          (vecPtr u (vecPtr u A + BitVec.ofNat 64 (80 * i)))
          ((vecCap u (vecPtr u A + BitVec.ofNat 64 (80 * i))).toNat * 24) := by
        simp only [Within]; addr_omega [hz, hk, hIl, hhi]
      have hf := hP.fresh _ (Or.inr ⟨i, hi, Or.inl hW⟩)
      exact hX _ hf.1 hf.2
    · simp only [weightAt]
      rw [c24, ite_eq_left_of_eq_true _ _ (eq_true hood), ite_eq_left_of_eq_true _ _ (eq_true hood)]
      congr 1
      simp only [vecEs]
      rw [d8, d16]
      refine hF.eListAt fun k hk ↦ ?_
      rcases hOr.2 with hz | hz
      · omega
      have hW : InBufs u (vecPtr u A + BitVec.ofNat 64 (80 * i) + 24)
          (vecPtr u (vecPtr u A + BitVec.ofNat 64 (80 * i) + 24 + 8) + BitVec.ofNat 64 k) := by
        rw [InBufs, ite_eq_left_of_eq_true _ _ (eq_true hood)]
        simp only [Within]; addr_omega [hz, hk, hOl, hhi]
      have hf := hP.fresh _ (Or.inr ⟨i, hi, Or.inr hW⟩)
      exact hX _ hf.1 hf.2
  · rw [h16] at hi
    rw [h8]
    obtain ⟨c0, c8, c16, -, -, -, -⟩ := hP.elem hu hF hX hi
    have hI := hP.intro i hi
    have hIr := hI.raw
    simp only [RawVecOk, Buf] at hIr
    refine ⟨?_, by rw [c16, c0]; exact hI.len⟩
    simp only [RawVecOk, Buf]
    rw [c8, c0]
    exact ⟨hIr.1, hIr.2.imp id fun h ↦ ⟨h.1, by omega⟩⟩
  · rw [h16] at hi
    rw [h8]
    obtain ⟨-, -, -, c24, d0, d8, d16⟩ := hP.elem hu hF hX hi
    obtain ⟨hood, hO⟩ := hP.ood i hi
    have hOr := hO.raw
    simp only [RawVecOk, Buf] at hOr
    refine ⟨by rw [c24]; exact hood, ?_, by rw [d16, d0]; exact hO.len⟩
    simp only [RawVecOk, Buf]
    rw [d8, d0]
    exact ⟨hOr.1, hOr.2.imp id fun h ↦ ⟨h.1, by omega⟩⟩
  · have := hP.fresh y (pb y hy)
    exact ⟨this.1, by omega⟩
  · rw [h16] at hi
    rw [h8, h0]
    rw [h8] at hy
    exact hP.self i hi y (by
      have := hP.pbufs hu hF hX h8 hi (by rw [h8]; exact hy)
      exact this)

end Rv64Verifier.Proofs.Pcs.Vso
