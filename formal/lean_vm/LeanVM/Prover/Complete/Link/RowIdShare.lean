/-
  LeanVM.Prover.Complete.Link.RowIdShare

  An executed row's pointer reads, regrouped as the index side's terms: the state at the cycle
  pointer, the program at the program pointer, each access at its cell, the word reads.
-/

module

public import LeanVM.Prover.Complete.Link.RowIdTable
public import LeanVM.Prover.Complete.Link.BalanceSum

/-!
# A row's pointer reads, regrouped

A table's pointer columns are the cycle pointer, the program pointer and the memory pointers, each
access at one memory pointer and each word read at one (`ptrsRest`, decided). So the pointer
columns' reads at an executed row (`ptrVal`) regroup per access and per word read
(`ptrSum_eq`): the state and its successor at the cycle pointer, `X_ω + P_fp·fp` at the program
pointer, `η_mem·Y·μ·gate·shEq` per access, and `η_mem·γ_word·M_1` times the word reads.
-/

@[expose] public section

namespace LeanVM.Prover.Complete.RowId

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover Finset
open LeanVM.Protocol.KeccakGkr (eqAt)

/-! ## The tables' pointers -/

/-- A table's pointer columns: the cycle pointer, the program pointer, then the memory pointers,
distinct, every access and every word read at a memory pointer. -/
def ptrsRest (links : Links) : Bool :=
  decide links.pointers.Nodup &&
    links.pointers.take 2 == [links.stateLink.cycle, links.bytecodeLink.pointer] &&
    links.memory.all fun a ↦ (links.pointers.drop 2).contains a.pointer &&
      a.reads.all fun rd ↦ match rd with
        | .word p _ => (links.pointers.drop 2).contains p
        | _ => true

theorem ptrsRest_tables : ∀ t < nTables, ptrsRest (tables.getD t default).links = true := by
  decide +kernel

theorem ptrsRest_spec {links : Links} (h : ptrsRest links = true) :
    links.pointers = links.stateLink.cycle :: links.bytecodeLink.pointer :: links.pointers.drop 2 ∧
      links.pointers.Nodup ∧ (∀ a ∈ links.memory, a.pointer ∈ links.pointers.drop 2) ∧
      ∀ a ∈ links.memory, ∀ p sc, Read.word p sc ∈ a.reads → p ∈ links.pointers.drop 2 := by
  simp only [ptrsRest, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨⟨hnd, htake⟩, hmem⟩ := h
  refine ⟨?_, hnd, fun a ha ↦ (hmem a ha).1, fun a ha p sc hr ↦ by simpa using (hmem a ha).2 _ hr⟩
  rw [← List.take_append_drop 2 links.pointers, htake]
  simp

/-! ## Regrouping by a key -/

theorem sum_filter_ite {α : Type} (P : α → Prop) [DecidablePred P] (F : α → E) :
    ∀ L : List α, ((L.filter P).map F).sum = (L.map fun x ↦ if P x then F x else 0).sum
  | [] => by simp
  | x :: L => by
    by_cases h : P x <;> simp [h, sum_filter_ite P F L]

theorem sum_filter_iteB {α : Type} (P : α → Bool) (F : α → E) :
    ∀ L : List α, ((L.filter P).map F).sum = (L.map fun x ↦ if P x = true then F x else 0).sum
  | [] => by simp
  | x :: L => by
    by_cases h : P x = true <;> simp [h, sum_filter_iteB P F L]

theorem sum_ite_key (c : E) {k₀ : ℕ} : ∀ K : List ℕ, K.Nodup → k₀ ∈ K →
    (K.map fun p ↦ if k₀ = p then c else 0).sum = c
  | [], _, h => by simp at h
  | a :: K, hnd, h => by
    rw [List.nodup_cons] at hnd
    by_cases ha : k₀ = a
    · subst ha
      have : (K.map fun p ↦ if k₀ = p then c else 0).sum = 0 :=
        List.sum_eq_zero fun x hx ↦ by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
          exact ite_eq_right fun (e : k₀ = p) ↦ hnd.1 (e ▸ hp)
      simp [this]
    · have hk : k₀ ∈ K := by simpa [ha] using h
      simp [ha, sum_ite_key c K hnd.2 hk]

/-- **Regrouping**: summing, over distinct keys, the elements of each key gives every element
once, when every element's key is among them. -/
theorem sum_regroup {α : Type} (key : α → ℕ) (F : α → E) (K : List ℕ) (hK : K.Nodup) :
    ∀ L : List α, (∀ x ∈ L, key x ∈ K) →
      (K.map fun p ↦ (L.map fun x ↦ if key x = p then F x else 0).sum).sum = (L.map F).sum
  | [], _ => by simp
  | x :: L, h => by
    have ih := sum_regroup key F K hK L fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, List.sum_cons]
    rw [List.sum_map_add, ih, sum_ite_key _ K hK (h x List.mem_cons_self)]

theorem map_zipIdx_ge {f : ℕ × ℕ → E} {g : ℕ → E} (hfg : ∀ p k, 2 ≤ k → f (p, k) = g p) :
    ∀ (l : List ℕ) (n : ℕ), 2 ≤ n → (l.zipIdx n).map f = l.map g
  | [], _, _ => rfl
  | p :: l, n, hn => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, hfg p n hn, map_zipIdx_ge hfg l (n + 1) (by omega)]

/-! ## A row's pointer reads -/

section Row

variable (W : Witness) (inp : RowInputs) (t : ℕ) (r : List E)

theorem accessesAt_nil {links : Links} {mu : List E} {p : ℕ}
    (h : ∀ a ∈ links.memory, a.pointer ≠ p) : accessesAt links mu p = [] := by
  unfold accessesAt
  refine List.filter_eq_nil_iff.mpr fun am ham ↦ ?_
  simpa using h am.1 (List.of_mem_zip ham).1

/-- A memory pointer `p`'s reads at row `u`, per access and per word read. -/
theorem ptrVal_mem (u p k : ℕ) (hk : 2 ≤ k) :
    ptrVal W inp t r (ptrAt W t p u) u p k =
      (((tables.getD t default).links.memory.zip (inp.ch.mu.getD t [])).map fun am ↦
        if am.1.pointer = p then inp.ch.etaMem * inp.yMem * am.2 * omegaU W inp t u *
          gateOf (rowValue (W.tableCols t) u) am.1 *
          shEq W.chunks r (ptrAt W t am.1.pointer u) am.1.shift else 0).sum +
      omegaU W inp t u * (inp.ch.etaMem * inp.ch.gammaMem.getD 1 0 * inp.m1) *
        ((wordReads (tables.getD t default).links (inp.ch.mu.getD t []) 1).map fun pf ↦
          if pf.1 = p then eqAt r (ptrAt W t pf.1 u) * pf.2.evaluate (rowValue (W.tableCols t) u)
          else 0).sum := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  unfold ptrVal
  simp only [rowCoefs, LeanVM.Protocol.Tables.sumE_eq, add_zero]
  have hacc : accessesAt (tables.getD t default).links (inp.ch.mu.getD t []) p =
      ((tables.getD t default).links.memory.zip (inp.ch.mu.getD t [])).filter
        fun am ↦ decide (am.1.pointer = p) := rfl
  rw [hacc, sum_filter_iteB (fun am : Access × E ↦ !decide (am.1.shift = 0)),
    sum_filter_iteB (fun am : Access × E ↦ decide (am.1.pointer = p)),
    sum_filter_iteB (fun am : Access × E ↦ decide (am.1.pointer = p))]
  rw [mul_add, add_mul, add_right_comm]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [← List.sum_map_mul_left, ← List.sum_map_mul_right, ← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun am _ ↦ ?_)
    by_cases hp : am.1.pointer = p
    · by_cases hs : am.1.shift = 0
      · simp only [hp, hs, gateOf, shEq_zero, decide_true, ↓reduceIte, Bool.not_true,
          Bool.false_eq_true, add_zero]
        ring
      · simp only [hp, hs, gateOf, decide_true, decide_false, ↓reduceIte, Bool.not_false,
          mul_zero, zero_mul, zero_add]
    · simp only [hp, decide_false, ↓reduceIte, mul_zero, zero_mul, Bool.false_eq_true, add_zero]
  · rw [← List.sum_map_mul_left, ← List.sum_map_mul_right, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun pf _ ↦ ?_)
    by_cases hp : pf.1 = p
    · simp only [hp, ↓reduceIte]; ring
    · simp only [hp, ↓reduceIte, mul_zero, zero_mul]

/-- **An executed row's pointer reads, regrouped**: the state and its successor at the cycle
pointer, the program at the program pointer, each access at its cell, the word reads. -/
theorem ptrSum_eq {t : ℕ} (ht : t < nTables) (u : ℕ) :
    ((tables.getD t default).links.pointers.zipIdx.map fun pk ↦
        ptrVal W inp t r (ptrAt W t pk.1 u) u pk.1 pk.2).sum =
      (inp.eqZeta * (stateValues inp.ch (tables.getD t default).links (rowValue (W.tableCols t) u)).1 +
          inp.shiftZeta *
            (stateValues inp.ch (tables.getD t default).links (rowValue (W.tableCols t) u)).2) *
          eqAt r (ptrAt W t (tables.getD t default).links.stateLink.cycle u) +
        omegaU W inp t u * (inp.xBc + inp.pFp * rowValue (W.tableCols t) u
          (tables.getD t default).links.stateLink.fp) *
          eqAt r (ptrAt W t (tables.getD t default).links.bytecodeLink.pointer u) +
        (((tables.getD t default).links.memory.zip (inp.ch.mu.getD t [])).map fun am ↦
          inp.ch.etaMem * inp.yMem * am.2 * omegaU W inp t u *
            gateOf (rowValue (W.tableCols t) u) am.1 *
            shEq W.chunks r (ptrAt W t am.1.pointer u) am.1.shift).sum +
        omegaU W inp t u * (inp.ch.etaMem * inp.ch.gammaMem.getD 1 0 * inp.m1) *
          gatedVal (fun p ↦ eqAt r (ptrAt W t p u)) (rowValue (W.tableCols t) u)
            (wordReads (tables.getD t default).links (inp.ch.mu.getD t []) 1) := by
  obtain ⟨hsplit, hnd, hmem, hrd⟩ := ptrsRest_spec (ptrsRest_tables t ht)
  set links := (tables.getD t default).links with hlinks
  have hnd' := hnd
  rw [hsplit, List.nodup_cons, List.nodup_cons, List.mem_cons, not_or] at hnd'
  obtain ⟨⟨hcb, hcr⟩, hbr, hrnd⟩ := hnd'
  have hnil : ∀ q ∉ links.pointers.drop 2, accessesAt links (inp.ch.mu.getD t []) q = [] :=
    fun q hq ↦ accessesAt_nil fun a ha e ↦ hq (e ▸ hmem a ha)
  rw [hsplit, List.zipIdx_cons, List.zipIdx_cons, List.map_cons, List.map_cons, List.sum_cons,
    List.sum_cons,
    map_zipIdx_ge (g := fun p ↦ ptrVal W inp t r (ptrAt W t p u) u p 2)
      (fun p k hk ↦ by rw [ptrVal_mem W inp t r u p k hk, ptrVal_mem W inp t r u p 2 le_rfl]) _ _
      (by omega)]
  simp only [ptrVal_mem W inp t r u _ 2 le_rfl]
  rw [List.sum_map_add, sum_regroup (fun am : Access × E ↦ am.1.pointer) _ _ hrnd _
      (fun am ham ↦ hmem am.1 (List.of_mem_zip ham).1)]
  rw [← hlinks, List.sum_map_mul_left,
    sum_regroup (fun pf : ℕ × Form ↦ pf.1) _ _ hrnd _ (fun pf hpf ↦ by
      obtain ⟨a, ha, sc, hr⟩ := wordReads_keys _ _ _ pf hpf
      exact hrd a ha pf.1 sc hr)]
  have h0 : ptrVal W inp t r (ptrAt W t links.stateLink.cycle u) u links.stateLink.cycle 0 =
      (inp.eqZeta * (stateValues inp.ch links (rowValue (W.tableCols t) u)).1 +
        inp.shiftZeta * (stateValues inp.ch links (rowValue (W.tableCols t) u)).2) *
        eqAt r (ptrAt W t links.stateLink.cycle u) := by
    unfold ptrVal
    dsimp only
    rw [hnil _ hcr]
    simp only [rowCoefs, List.filter_nil, List.map_nil, List.sum_nil, add_zero, mul_zero, zero_add]
    rfl
  have h1 : ptrVal W inp t r (ptrAt W t links.bytecodeLink.pointer u) u links.bytecodeLink.pointer
      (0 + 1) = omegaU W inp t u * (inp.xBc + inp.pFp * rowValue (W.tableCols t) u
        links.stateLink.fp) * eqAt r (ptrAt W t links.bytecodeLink.pointer u) := by
    unfold ptrVal
    dsimp only
    rw [hnil _ hbr]
    simp only [rowCoefs, List.filter_nil, List.map_nil, List.sum_nil, add_zero]
    rfl
  rw [h0, h1, gatedVal]
  ring

end Row

end LeanVM.Prover.Complete.RowId

end
