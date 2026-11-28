/-
  LeanVM.Prover.Complete.Link.ColumnStep

  One pointer column's terms in a bound table's sum are its part of the pointer-column rounds' sum.
-/

module

public import LeanVM.Prover.Complete.Link.ColumnTerms

/-!
# One pointer column, bound

`corner_termsVal_rowPointerStep`: the terms `rowPointerStep` adds for a pointer column, read at the
bound tables and times the table's corner factor, are the column's part (`colTerm`) at the row
point (`columnOf`), where the bound functional tables read the column's values (`Functionals.values`
of its slices) and every shift is at most `maxShift`. Every shifted read regroups by its shift
(`sum_shift_regroup`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open Finset

theorem sum_map_comm {α : Type} (L : List α) (n : ℕ) (f : ℕ → α → E) :
    ∑ s ∈ range n, (L.map (f s)).sum = (L.map fun a ↦ ∑ s ∈ range n, f s a).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [sum_add_distrib, ih]

/-- **The shifted reads, regrouped by their shift.** -/
theorem sum_shift_regroup {α : Type} (L : List α) (sh : α → ℕ) (K : α → E) (V : ℕ → E) (M : ℕ)
    (hS : ∀ a ∈ L, sh a ≤ M) :
    (L.map fun a ↦ if sh a = 0 then 0 else K a * V (sh a - 1)).sum =
      ((List.range M).map fun s ↦ (L.map fun a ↦ if sh a = s + 1 then K a else 0).sum * V s).sum := by
  rw [sum_map_range]
  simp only [← List.sum_map_mul_right]
  rw [sum_map_comm]
  refine congrArg List.sum (List.map_congr_left fun a ha ↦ ?_)
  have h := hS a ha
  by_cases h0 : sh a = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    rw [sum_eq_single (sh a - 1)]
    · rw [ite_eq_left (show sh a = sh a - 1 + 1 by omega)]
    · intro s _ hs
      rw [ite_eq_right (show ¬ sh a = s + 1 by omega), zero_mul]
    · intro hs
      exact absurd (mem_range.mpr (by omega)) hs

theorem prod_gate (ev : ℕ → E) (g : Option ℕ) :
    (((g.map fun g ↦ #[3 + g]).getD #[]).toList.map ev).prod = (g.map fun g ↦ ev (3 + g)).getD 1 := by
  cases g <;> simp

theorem getD_map_mul_range (n s : ℕ) (f : ℕ → E) (c : E) (hs : s < n) :
    (((List.range n).map f).map (c * ·)).getD s 0 = c * f s := by
  simp [List.getD_eq_getElem?_getD, hs]

theorem termsVal_foldl_push2 {α : Type} (ev : ℕ → E) (g h : α → E × Array ℕ) :
    ∀ (L : List α) (T : Array (E × Array ℕ)),
      termsVal ev (L.foldl (fun T i ↦ (T.push (g i)).push (h i)) T) =
        termsVal ev T + (L.map fun i ↦ termVal ev (g i) + termVal ev (h i)).sum :=
  termsVal_foldl ev _ _ fun T i ↦ by rw [termsVal_push, termsVal_push, add_assoc]

theorem termsVal_foldl_pushIf {α : Type} (ev : ℕ → E) (p : α → Prop) [DecidablePred p]
    (g : α → E × Array ℕ) : ∀ (L : List α) (T : Array (E × Array ℕ)),
      termsVal ev (L.foldl (fun T x ↦ if p x then T else T.push (g x)) T) =
        termsVal ev T + (L.map fun x ↦ if p x then 0 else termVal ev (g x)).sum :=
  termsVal_foldl ev _ _ fun T x ↦ by
    by_cases hx : p x
    · simp [hx]
    · simp [hx, termsVal_push]

/-- **One pointer column's terms, bound, are its part of the pointer-column rounds' sum.** -/
theorem corner_termsVal_rowPointerStep (W : Witness) (inp : RowInputs) (t q₀ : ℕ) (rt : RowTable)
    (chi : List E) (acc : Array (Array E) × Array (E × Array ℕ) × ℕ) (pk : ℕ × ℕ)
    (hd : 1 ≤ W.chunks.d)
    (hD : ∀ j < 2 * W.chunks.d, rt.prods.at (acc.2.2 + 2 + j) =
      (inp.functionals.values W.chunks
        (columnSlices ((W.tableCols t).getD pk.1 #[]) (chi.take rt.height))).getD j 0)
    (hT : ∀ am ∈ accessesAt (tables.getD t default).links (inp.ch.mu.getD t []) pk.1, am.1.shift ≠ 0 →
      rt.prods.at (acc.2.2 + 2 + 2 * W.chunks.d +
          (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) pk.1).idxOf am.1.shift) =
        (inp.functionals.values W.chunks
          (columnSlices ((W.tableCols t).getD pk.1 #[]) (chi.take rt.height))).getD
          (2 * W.chunks.d + am.1.shift - 1) 0)
    (hS : ∀ am ∈ accessesAt (tables.getD t default).links (inp.ch.mu.getD t []) pk.1,
      am.1.shift ≤ inp.maxShift) :
    rt.corner * termsVal rt.prods.at (rowPointerStep W inp t q₀ acc pk).2.1 =
      rt.corner * termsVal rt.prods.at acc.2.1 +
        colTerm W.chunks.d inp.maxShift inp.functionals.mirrors
          (columnOf W inp t q₀ rt chi acc.2.2 pk.1 pk.2) := by
  obtain ⟨tabs, terms, pos⟩ := acc
  obtain ⟨pointer, k⟩ := pk
  dsimp only at hD hT hS ⊢
  unfold rowPointerStep columnOf colTerm
  dsimp only
  rw [termsVal_foldl_push2, termsVal_foldl_pushIf, termsVal_push, termsVal_push]
  set ev := rt.prods.at with hev
  set vals := inp.functionals.values W.chunks
    (columnSlices ((W.tableCols t).getD pointer #[]) (List.take rt.height chi)) with hvals
  set d := W.chunks.d with hdd
  set L := accessesAt (tables.getD t default).links (inp.ch.mu.getD t []) pointer with hL
  set R := ((List.range (d - 1)).map fun i ↦ vals.getD (1 + i) 0).prod with hR
  have hrest : (((List.range (d - 1)).map fun x ↦ pos + 2 + 1 + x).map ev).prod = R := by
    rw [List.map_map]
    refine congrArg List.prod (List.map_congr_left fun i hi ↦ ?_)
    have := List.mem_range.mp hi
    simp only [Function.comp, show pos + 2 + 1 + i = pos + 2 + (1 + i) by omega]
    exact hD _ (by omega)
  simp only [termVal, Array.toList_append, List.map_append, List.prod_append, List.map_cons,
    List.prod_cons, List.map_nil, List.prod_nil, prod_gate, hrest]
  set sh := shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) pointer
  have eS : (L.map fun x ↦ if x.1.shift = 0 then 0 else inp.ch.etaMem * inp.yMem * x.2 *
      (ev 0 * 1 * (x.1.gate.map fun g ↦ ev (3 + g)).getD 1 *
        (ev (pos + 2 + 2 * d + sh.idxOf x.1.shift) * 1) * R)).sum =
      ((List.range inp.maxShift).map fun s ↦ (L.map fun x ↦ if x.1.shift = s + 1 then
        inp.ch.etaMem * inp.yMem * x.2 * ev 0 * (x.1.gate.map fun g ↦ ev (3 + g)).getD 1
        else 0).sum * (vals.getD (2 * d + s) 0 * R)).sum := by
    rw [← sum_shift_regroup L (·.1.shift) _ (fun s ↦ vals.getD (2 * d + s) 0 * R) _ hS]
    refine congrArg List.sum (List.map_congr_left fun x hx ↦ ?_)
    by_cases h0 : x.1.shift = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte]
      rw [hT x hx h0, show 2 * d + x.1.shift - 1 = 2 * d + (x.1.shift - 1) by omega]
      ring
  have eRS : ((List.range inp.maxShift).map fun s ↦
      (((List.range inp.maxShift).map fun s ↦ sumE (L.map fun x ↦ if x.1.shift = s + 1 then
        inp.ch.etaMem * inp.yMem * x.2 * ev 0 * (x.1.gate.map fun g ↦ ev (3 + g)).getD 1
        else 0)).map (rt.corner * ·)).getD s 0 * vals.getD (2 * d + s) 0 * R).sum =
      rt.corner * ((List.range inp.maxShift).map fun s ↦ (L.map fun x ↦ if x.1.shift = s + 1 then
        inp.ch.etaMem * inp.yMem * x.2 * ev 0 * (x.1.gate.map fun g ↦ ev (3 + g)).getD 1
        else 0).sum * (vals.getD (2 * d + s) 0 * R)).sum := by
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun s hs ↦ ?_)
    rw [getD_map_mul_range _ _ _ _ (List.mem_range.mp hs), LeanVM.Prover.Complete.sumE_eq_sum]
    ring
  have eRC : ((List.range d).map fun i ↦
      (((List.range d).map fun i ↦ ev 0 * inp.cert * inp.ch.eps.getD (q₀ + k) 0 *
        inp.ch.nu.getD i 0).map (rt.corner * ·)).getD i 0 * vals.getD i 0 * vals.getD (d + i) 0 +
      inp.functionals.mirrors.getD i 0 *
        (((List.range d).map fun i ↦ ev 0 * inp.cert * inp.ch.eps.getD (q₀ + k) 0 *
          inp.ch.nu.getD i 0).map (rt.corner * ·)).getD i 0).sum =
      rt.corner * ((List.range d).map fun i ↦
        inp.cert * inp.ch.eps.getD (q₀ + k) 0 * inp.ch.nu.getD i 0 *
          (ev 0 * (ev (pos + 2 + i) * (ev (pos + 2 + d + i) * 1))) +
        inp.cert * inp.ch.eps.getD (q₀ + k) 0 * inp.ch.nu.getD i 0 *
          inp.functionals.mirrors.getD i 0 * (ev 0 * 1)).sum := by
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun i hi ↦ ?_)
    have hi' := List.mem_range.mp hi
    rw [getD_map_mul_range _ _ _ _ hi', hD i (by omega),
      show pos + 2 + d + i = pos + 2 + (d + i) by omega, hD (d + i) (by omega)]
    ring
  rw [eS, eRS, eRC, show ev (pos + 2) = vals.getD 0 0 from hD 0 (by omega)]
  ring

end LeanVM.Prover.Complete

end
