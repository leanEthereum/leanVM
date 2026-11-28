/-
  LeanVM.Protocol.Relation.Link.GroupLinksDeg

  The index claim less the index side's sum is a polynomial of total degree at most
  `linkGroupError` in the drawn challenges.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupLinksWeights
public import LeanVM.Protocol.Relation.Link.GroupOneHot

/-!
# The index side's sum, of degree `linkGroupError`

`polyFn_groupF`: `v ↦ indexClaim − Σ_r linkIdxAt(v, r)` is of total degree at most
`max(m + 3 + BYTECODE_SLOT_BITS, W + 1)`. At Boolean `(r, χ, q)` the row summand is
`lk_rowSummand`'s sum, whose shares are, in the draw: the state's `eq(ζ, r)·ŝ` and
`shift_eq(ζ, r)·ŝ'` (`W + 1`), the row weight `ω = θ_t·eq(τ, u)` (`m + 1`) times the program's
weights (`η_bc·eq(α, s)` or `η_mem·μ·γ`, `BYTECODE_SLOT_BITS + 1`) or the memory's
`η_mem·μ·γ` (`3`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

@[expose] public section

/-! ## Sums of polynomial functions -/

theorem polyFn_list_sum {β : Type} {n D : ℕ} (f : β → (Fin n → E) → E) :
    ∀ (l : List β), (∀ b ∈ l, PolyFn n D (f b)) → PolyFn n D fun v ↦ (l.map fun b ↦ f b v).sum
  | [], _ => ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ by simp
  | b :: l, h => ((h b (by simp)).add_le (polyFn_list_sum f l fun c hc ↦ h c (by simp [hc]))).congr
      fun v ↦ by simp

/-- A sum over the accesses zipped with their `μ`, filtered by the access. -/
theorem polyFn_zip_sum {β : Type} {n D : ℕ} (P : β → Bool) (F : β → E → (Fin n → E) → E)
    (hF : ∀ b (m : (Fin n → E) → E), PolyFn n 1 m → PolyFn n D fun v ↦ F b (m v) v) :
    ∀ (L : List β) {g : (Fin n → E) → List E}, Lin n g →
      PolyFn n D fun v ↦ (((L.zip (g v)).filter fun x ↦ P x.1).map fun x ↦ F x.1 x.2 v).sum
  | [], _, _ => ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ by simp
  | b :: L, g, hg => by
    rcases h0 : (g 0) with _ | ⟨h, tl⟩
    · refine ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ ?_
      have : g v = [] := List.eq_nil_of_length_eq_zero (by rw [hg.1 v 0, h0]; rfl)
      simp [this]
    · have hcons : ∀ v, g v = (g v).getD 0 0 :: (g v).tail := by
        intro v
        obtain ⟨a, l, hal⟩ := List.exists_cons_of_length_eq_add_one (by rw [hg.1 v 0, h0]; rfl)
        rw [hal]; rfl
      have ih := polyFn_zip_sum P F hF L hg.tail
      have hb := hF b _ (hg.getD 0)
      by_cases hP : P b = true
      · refine (hb.add_le ih).congr fun v ↦ ?_
        rw [hcons v]
        simp [hP]
      · refine ih.congr fun v ↦ ?_
        rw [hcons v]
        simp [hP]

theorem polyFn_zip_sum' {β : Type} {n D : ℕ} (F : β → E → (Fin n → E) → E)
    (hF : ∀ b (m : (Fin n → E) → E), PolyFn n 1 m → PolyFn n D fun v ↦ F b (m v) v)
    (L : List β) {g : (Fin n → E) → List E} (hg : Lin n g) :
    PolyFn n D fun v ↦ ((L.zip (g v)).map fun x ↦ F x.1 x.2 v).sum :=
  (polyFn_zip_sum (fun _ ↦ true) F hF L hg).congr fun v ↦ by simp

/-! ## The challenges' degrees -/

section Deg

variable {n : ℕ} {ch : (Fin n → E) → LinkCh} (hL : LinCh n ch)
  (hα : (ch 0).alpha.length ≤ bytecodeSlotBits)
include hL

include hα in
theorem polyFn_slot (s : ℕ) : PolyFn n bytecodeSlotBits fun v ↦ (eqKernel (ch v).alpha).getD s 0 :=
  (polyFn_eqKernel_getD hL.alpha s).mono hα

theorem polyFn_gm (i : ℕ) : PolyFn n 1 fun v ↦ (ch v).gammaMem.getD i 0 := hL.gammaMem.getD i

omit hL in
theorem polyFn_lkRead (pointer : ℕ) (G : (Fin n → E) → E → Form → E) {D : ℕ}
    (hG : ∀ (m : (Fin n → E) → E) sc, PolyFn n 1 m → PolyFn n D fun v ↦ G v (m v) sc)
    (m : (Fin n → E) → E) (hm : PolyFn n 1 m) (rd : Read) :
    PolyFn n D fun v ↦ lkRead pointer (G v) (m v) rd := by
  cases rd with
  | word p sc =>
    by_cases hp : p = pointer
    · exact (hG m sc hm).congr fun v ↦ by simp [lkRead, hp]
    · exact ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ by simp [lkRead, hp]
  | slot s sc => exact ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ by simp [lkRead]
  | frame s sc => exact ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ by simp [lkRead]
  | pc s sc => exact ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ by simp [lkRead]

include hα in
/-- Each slot weight is of degree at most `BYTECODE_SLOT_BITS + 1`. -/
theorem polyFn_weights (tables : List Table) (t : ℕ) {s : ℕ} (hs : s < 2 ^ bytecodeSlotBits) :
    let w := fun v ↦ slotWeights tables (eqKernel (ch v).alpha)
      ((ch v).gammaMem.getD 0 0, (ch v).gammaMem.getD 1 0) (ch v).mu (ch v).etaMem (ch v).etaBc
    PolyFn n (bytecodeSlotBits + 1) (fun v ↦ ((w v).omega.getD t []).getD s 0) ∧
    PolyFn n (bytecodeSlotBits + 1) (fun v ↦ ((w v).pc.getD t []).getD s 0) ∧
    PolyFn n (bytecodeSlotBits + 1) (fun v ↦ ((w v).frame.getD t []).getD s 0) := by
  intro w
  have h3 : 3 ≤ bytecodeSlotBits + 1 := by decide
  by_cases ht : t < tables.length
  · have hw := fun v ↦ slotWeights_getD tables (eqKernel (ch v).alpha)
      ((ch v).gammaMem.getD 0 0, (ch v).gammaMem.getD 1 0) (ch v).mu (ch v).etaMem (ch v).etaBc ht
    have hc := fun v ↦ tsw_closed (tables.getD t default) (eqKernel (ch v).alpha)
      ((ch v).gammaMem.getD 0 0, (ch v).gammaMem.getD 1 0) ((ch v).mu.getD t []) (ch v).etaMem (ch v).etaBc hs
    have hreads : ∀ (sel : ℕ → Read → E) (gi : ℕ),
        PolyFn n (bytecodeSlotBits + 1) fun v ↦ (((tables.getD t default).links.memory.zip ((ch v).mu.getD t [])).map
          fun x ↦ (x.1.reads.map fun rd ↦ (ch v).etaMem * x.2 * (ch v).gammaMem.getD gi 0 * sel s rd).sum).sum := by
      intro sel gi
      refine polyFn_zip_sum' (fun (b : Access) m v ↦ (b.reads.map fun rd ↦ (ch v).etaMem * m * (ch v).gammaMem.getD gi 0 *
        sel s rd).sum) (fun b m hm ↦ polyFn_list_sum _ _ fun rd _ ↦
          ((hL.etaMem.mul hm).mul (polyFn_gm hL gi) |>.mul (PolyFn.const (sel s rd))).mono (by omega))
        _ (hL.mu t)
    refine ⟨?_, ?_, ?_⟩
    · have hops : PolyFn n (bytecodeSlotBits + 1) fun v ↦ ((tables.getD t default).links.bytecodeLink.operands.map
          fun op ↦ (op.1.map fun s' ↦ if s' = s then (ch v).etaBc * (eqKernel (ch v).alpha).getD (op.1.headD 0) 0
            else 0).sum).sum :=
        polyFn_list_sum _ _ fun op _ ↦ polyFn_list_sum _ _ fun s' _ ↦ by
          by_cases h : s' = s
          · exact (hL.etaBc.mul (polyFn_slot hL hα _)).congr fun v ↦ by split_ifs; rfl
          · exact ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ by split_ifs; rfl
      have h3' : PolyFn n (bytecodeSlotBits + 1) fun v ↦ if s = 3 then (ch v).etaBc * (eqKernel (ch v).alpha).getD 3 0
          else 0 := by
        by_cases h : s = 3
        · exact (hL.etaBc.mul (polyFn_slot hL hα _)).congr fun v ↦ by split_ifs; rfl
        · exact ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ by split_ifs; rfl
      refine ((h3'.add_le hops).add_le (hreads lkSlotRead 1)).congr fun v ↦ ?_
      simp only [w]
      rw [(hw v).1, (hc v).1]
    · refine (hreads lkPcRead 1).congr fun v ↦ ?_
      simp only [w]
      rw [(hw v).2.1, (hc v).2.1]
    · have hf : PolyFn n (bytecodeSlotBits + 1) fun v ↦ (((tables.getD t default).links.memory.zip ((ch v).mu.getD t [])).map
          fun x ↦ (ch v).etaMem * x.2 * (ch v).gammaMem.getD 0 0 * lkFrameAddr s x.1 +
            (x.1.reads.map fun rd ↦ (ch v).etaMem * x.2 * (ch v).gammaMem.getD 1 0 * lkFrameRead s rd).sum).sum :=
        polyFn_zip_sum' (fun (b : Access) m v ↦ (ch v).etaMem * m * (ch v).gammaMem.getD 0 0 * lkFrameAddr s b +
            (b.reads.map fun rd ↦ (ch v).etaMem * m * (ch v).gammaMem.getD 1 0 * lkFrameRead s rd).sum)
          (fun b m hm ↦ (((hL.etaMem.mul hm).mul (polyFn_gm hL 0) |>.mul (PolyFn.const _)).mono (by omega)).add_le
            (polyFn_list_sum _ _ fun rd _ ↦
              ((hL.etaMem.mul hm).mul (polyFn_gm hL 1) |>.mul (PolyFn.const _)).mono (by omega)))
          _ (hL.mu t)
      refine hf.congr fun v ↦ ?_
      simp only [w]
      rw [(hw v).2.2, (hc v).2.2]
  · have h0 : ∀ v, (w v).omega.getD t [] = [] ∧ (w v).pc.getD t [] = [] ∧ (w v).frame.getD t [] = [] := by
      intro v
      simp only [w, slotWeights]
      refine ⟨?_, ?_, ?_⟩ <;> exact List.getD_eq_default _ _ (by simp; omega)
    refine ⟨?_, ?_, ?_⟩ <;> refine ((PolyFn.const 0).mono (Nat.zero_le _)).congr fun v ↦ ?_
    · rw [(h0 v).1]; simp
    · rw [(h0 v).2.1]; simp
    · rw [(h0 v).2.2]; simp

include hα in
/-- The program side's sums are of degree at most `BYTECODE_SLOT_BITS + 1`. -/
theorem polyFn_programSums (layout : Layout) (split : Split) :
    PolyFn n (bytecodeSlotBits + 1) (fun v ↦ (programSums layout (ch v) split).1) ∧
    PolyFn n (bytecodeSlotBits + 1) (fun v ↦ (programSums layout (ch v) split).2) := by
  have hW := fun t s (hs : s < 2 ^ bytecodeSlotBits) ↦ polyFn_weights hL hα layout.tables t hs
  have h16 : ∀ s ∈ range (2 ^ bytecodeSlotBits - 4), s + 4 < 2 ^ bytecodeSlotBits := fun s hs ↦ by
    have := mem_range.mp hs; omega
  refine ⟨?_, ?_⟩
  · refine (PolyFn.finsetSum _ fun t _ ↦ ?_).congr fun v ↦ by
      have h := programSums_closed layout (ch v) split
      simp only at h
      rw [h]
    refine (((hW t 3 (by decide)).1.mul (PolyFn.const _)).mul (PolyFn.const _) |>.mono (by omega)).add_le
      (PolyFn.finsetSum _ fun s hs ↦ ?_)
    exact (((hW t _ (h16 s hs)).1.mul (PolyFn.const _)).mono (by omega)).add_le
      (((hW t _ (h16 s hs)).2.1.mul (PolyFn.const _)).mono (by omega))
  · refine (PolyFn.finsetSum _ fun t _ ↦ PolyFn.finsetSum _ fun s hs ↦ ?_).congr fun v ↦ by
      have h := programSums_closed layout (ch v) split
      simp only at h
      rw [h]
    exact ((hW t _ (h16 s hs)).2.2.mul (PolyFn.const _)).mono (by omega)

end Deg

end

end LeanVM.Protocol.Relation
