/-
  LeanVM.Prover.Complete.Link.RowIdPtr

  A pointer column's step at an executed row of one-hot words, and at a padding row.
-/

module

public import LeanVM.Prover.Complete.Link.RowIdBase
public import LeanVM.Prover.Complete.Link.OneHot

/-!
# A pointer column at a row

`chunkFacts_of`: `Chunks.new`'s chunks have `ChunkFacts`. `stepVal_exec`: at an executed row whose
pointer word is one-hot at `σ`, the step's value is `(ω·c_ω + c_act)·eq(r, σ)` plus each shifted
access's `η_mem·Y·μ·ω·gate·shEq σ s`, the mirror terms cancelling; `stepVal_pad`: zero where `ω`
and `act` are.
-/

@[expose] public section

namespace LeanVM.Prover.Complete.RowId

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover Finset
open LeanVM.Protocol.KeccakGkr (eqAt eqKernel_getD eqKernel_length)

/-! ## The chunks -/

theorem exclusivePrefix_last : ∀ (ws : List ℕ), ws ≠ [] →
    (exclusivePrefix ws).getD (ws.length - 1) 0 + ws.getD (ws.length - 1) 0 = ws.sum
  | [], h => absurd rfl h
  | [a], _ => by simp [exclusivePrefix]
  | a :: b :: rest, _ => by
    have ih := exclusivePrefix_last (b :: rest) (by simp)
    rw [exclusivePrefix_cons]
    simp only [List.length_cons, Nat.add_sub_cancel, List.getD_cons_succ, List.sum_cons] at ih ⊢
    have hl : rest.length < (exclusivePrefix (b :: rest)).length := by
      simp [length_exclusivePrefix]
    rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hl]
    rcases rest with _ | ⟨c, rest⟩
    · simp at ih ⊢; omega
    · simp only [List.length_cons, List.getD_cons_succ, List.sum_cons] at ih ⊢
      omega

theorem chunkFacts_of {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) : ChunkFacts c := by
  obtain ⟨hok, -⟩ := chunksOK_new h
  have hs := new_shifts h
  refine ⟨hs, ?_, hok.1, fun σ i hi v hv ↦ bits_encode hok σ hi hv⟩
  obtain ⟨hd, -, -, -, hlast, -⟩ := hok
  have hne : c.widths ≠ [] := by
    intro h0; unfold Chunks.d at hd; rw [h0] at hd; simp at hd
  have := exclusivePrefix_last c.widths hne
  unfold Chunks.is Chunks.w Chunks.d at hlast
  rw [hs] at hlast
  omega

/-! ## The step's tables at a row -/

section Tab

variable (W : Witness) (inp : RowInputs) (t : ℕ)

theorem tv_stepTabs_coef {u : ℕ} (hu : u < 2 ^ W.layout.tableLogHeights.getD t 0) (p k : ℕ) :
    tv (stepTabs W inp t p k) u 0 = (rowCoefs inp (tables.getD t default).links
        (inp.ch.mu.getD t []) k p (rowValue (W.tableCols t) u)).1 ∧
      tv (stepTabs W inp t p k) u 1 = (rowCoefs inp (tables.getD t default).links
        (inp.ch.mu.getD t []) k p (rowValue (W.tableCols t) u)).2 := by
  have hu' := hu
  simp only [List.getD_eq_getElem?_getD] at hu'
  constructor <;> simp [tv, stepTabs, Array.getD_eq_getD_getElem?, hu']

theorem tv_stepTabs_fn {p u : ℕ} (hu : u < ((W.tableCols t).getD p #[]).size) (k : ℕ) {i : ℕ}
    (hi : i < 2 * W.chunks.d) :
    tv (stepTabs W inp t p k) u (2 + i) =
      evalChunk W.chunks (inp.functionals.tables.getD i (0, [])).2
        (kToNat (((W.tableCols t).getD p #[]).getD u 0)) (inp.functionals.tables.getD i (0, [])).1 := by
  unfold stepTabs
  dsimp only
  rw [Array.append_assoc, show 2 + i = (#[(Array.ofFn fun u ↦ rowCoefs inp (tables.getD t default).links
      (inp.ch.mu.getD t []) k p (rowValue (W.tableCols t) u.val)).map (·.1),
      (Array.ofFn fun u ↦ rowCoefs inp (tables.getD t default).links
      (inp.ch.mu.getD t []) k p (rowValue (W.tableCols t) u.val)).map (·.2)]).size + i by simp,
    tv_append_right, tv_append_left _ _ (by simp; omega)]
  have hu' := hu
  simp only [Array.getD_eq_getD_getElem?] at hu'
  simp [tv, hi, functionalTable, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hu']

theorem tv_stepTabs_shift {p u : ℕ} (hu : u < ((W.tableCols t).getD p #[]).size) (k : ℕ) {j : ℕ}
    (hj : j < (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) p).length) :
    tv (stepTabs W inp t p k) u (2 + 2 * W.chunks.d + j) =
      evalChunk W.chunks (inp.functionals.tables.getD (2 * W.chunks.d +
          (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) p)[j] - 1) (0, [])).2
        (kToNat (((W.tableCols t).getD p #[]).getD u 0))
        (inp.functionals.tables.getD (2 * W.chunks.d +
          (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) p)[j] - 1) (0, [])).1 := by
  unfold stepTabs
  dsimp only
  rw [show 2 + 2 * W.chunks.d + j = (#[(Array.ofFn fun u ↦ rowCoefs inp (tables.getD t default).links
      (inp.ch.mu.getD t []) k p (rowValue (W.tableCols t) u.val)).map (·.1),
      (Array.ofFn fun u ↦ rowCoefs inp (tables.getD t default).links
      (inp.ch.mu.getD t []) k p (rowValue (W.tableCols t) u.val)).map (·.2)] ++
      ((List.range (2 * W.chunks.d)).map fun i ↦ functionalTable W.chunks ((W.tableCols t).getD p #[])
        (inp.functionals.tables.getD i (0, []))).toArray).size + j by simp; omega,
    tv_append_right]
  have hu' := hu
  simp only [Array.getD_eq_getD_getElem?] at hu'
  have hj' := hj
  simp only [List.getD_eq_getElem?_getD] at hj'
  simp [tv, functionalTable, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hu',
    List.getElem?_eq_getElem hj']

end Tab

/-! ## The step's value -/

section Val

variable (W : Witness) (inp : RowInputs) (t q₀ : ℕ)

/-- **A padding row**: where `ω` and `act` vanish, so does the step. -/
theorem stepVal_pad (T : Array (Array E)) (u p k : ℕ) (h0 : tv T u 0 = 0) (h1 : tv T u 1 = 0) :
    stepVal W inp t q₀ T u p k = 0 := by
  unfold stepVal
  simp [h0, h1]

/-- **An executed row** whose pointer word is one-hot at `σ`: the pointer read at `r`, and each
shifted access read inside its window; the mirror terms cancel. -/
theorem stepVal_exec {r : List E} (hc : ChunkFacts W.chunks) (hok : ChunksOK W.chunks)
    (hr : r.length = W.chunks.width) (hfn : inp.functionals = Functionals.new W.chunks r inp.maxShift)
    (T : Array (Array E)) (u p k σ : ℕ)
    (hms : ∀ am ∈ accessesAt (tables.getD t default).links (inp.ch.mu.getD t []) p,
      am.1.shift ≤ inp.maxShift)
    (hu : u < 2 ^ W.layout.tableLogHeights.getD t 0)
    (hws : ((W.tableCols t).getD p #[]).size = 2 ^ W.layout.tableLogHeights.getD t 0)
    (hword : ((W.tableCols t).getD p #[]).getD u 0 = K.ofBits (W.chunks.encode σ))
    (h1 : tv T u 1 = 1)
    (hgate : ∀ am ∈ accessesAt (tables.getD t default).links (inp.ch.mu.getD t []) p, ∀ g ∈ am.1.gate,
      tv T u (3 + g) = rowValue (W.tableCols t) u g) :
    stepVal W inp t q₀ T u p k =
      (tv T u 0 * (rowCoefs inp (tables.getD t default).links (inp.ch.mu.getD t []) k p
          (rowValue (W.tableCols t) u)).1 +
        (rowCoefs inp (tables.getD t default).links (inp.ch.mu.getD t []) k p
          (rowValue (W.tableCols t) u)).2) * eqAt r σ +
      (((accessesAt (tables.getD t default).links (inp.ch.mu.getD t []) p).filter
          (fun am ↦ !decide (am.1.shift = 0))).map fun am ↦
        inp.ch.etaMem * inp.yMem * am.2 * tv T u 0 *
          (am.1.gate.map (rowValue (W.tableCols t) u)).getD 1 *
          shEq W.chunks r σ am.1.shift).sum := by
  have hd := hc.pos
  have hk : kToNat (((W.tableCols t).getD p #[]).getD u 0) = W.chunks.encode σ := by
    rw [hword, kToNat_ofBits, Nat.mod_eq_of_lt (encode_lt hok σ)]
  have hus : u < ((W.tableCols t).getD p #[]).size := by rw [hws]; exact hu
  have hD : ∀ i < W.chunks.d, tv (stepTabs W inp t p k) u (2 + i) = eqAt (W.chunks.part r i) (W.chunks.digit σ i) := by
    intro i hi
    rw [tv_stepTabs_fn W inp t hus k (by omega), hk, hfn, fn_D W.chunks r _ hi]
    exact evalChunk_D hc r hr σ hi
  have hDbar : ∀ i < W.chunks.d, tv (stepTabs W inp t p k) u (2 + (W.chunks.d + i)) =
      evalChunk W.chunks (eqKernel (W.chunks.part r i)).reverse (W.chunks.encode σ) i := by
    intro i hi
    rw [tv_stepTabs_fn W inp t hus k (by omega), hk, hfn, fn_Dbar W.chunks r _ hi]
  have hrest : stepRest W inp t u p k = restProd W.chunks r σ := by
    unfold stepRest restProd
    exact congrArg _ (List.map_congr_left fun i hi ↦ hD (i + 1) (by
      have := List.mem_range.mp hi; omega))
  have h2 : tv (stepTabs W inp t p k) u 2 = eqAt (W.chunks.part r 0) (W.chunks.digit σ 0) := hD 0 hd
  obtain ⟨hc1, hc2⟩ := tv_stepTabs_coef W inp t hu p k
  unfold stepVal
  dsimp only
  rw [h1, hc1, hc2, h2, hrest]
  have hcert : ((List.range W.chunks.d).map fun i ↦ inp.cert * inp.ch.eps.getD (q₀ + k) 0 *
      inp.ch.nu.getD i 0 * (tv T u 0 * (tv (stepTabs W inp t p k) u (2 + i) *
        tv (stepTabs W inp t p k) u (2 + (W.chunks.d + i)) + inp.functionals.mirrors.getD i 0))).sum = 0 := by
    refine List.sum_eq_zero fun x hx ↦ ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    rw [hD i hi', hDbar i hi', hfn, fn_mirror W.chunks r _ hi', ← evalChunk_D hc r hr σ hi',
      cert_zero hc r hr σ hi', mul_zero, mul_zero]
  rw [hcert, add_zero]
  have hshift : ∀ am ∈ (accessesAt (tables.getD t default).links (inp.ch.mu.getD t []) p).filter
      (fun am ↦ !decide (am.1.shift = 0)),
      inp.ch.etaMem * inp.yMem * am.2 * (tv T u 0 *
        (am.1.gate.map fun g ↦ tv T u (3 + g)).getD 1 *
        tv (stepTabs W inp t p k) u (2 + 2 * W.chunks.d +
          (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) p).idxOf am.1.shift) *
        restProd W.chunks r σ) =
      inp.ch.etaMem * inp.yMem * am.2 * tv T u 0 *
        (am.1.gate.map (rowValue (W.tableCols t) u)).getD 1 * shEq W.chunks r σ am.1.shift := by
    intro am ham
    obtain ⟨hmem, hne⟩ := List.mem_filter.mp ham
    have hne' : am.1.shift ≠ 0 := by simpa using hne
    have hin := mem_shiftsAt hmem hne'
    have hidx := List.idxOf_lt_length_of_mem hin
    have hget : (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) p)[
        (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) p).idxOf am.1.shift] =
        am.1.shift := List.getElem_idxOf hidx
    have hg : (am.1.gate.map fun g ↦ tv T u (3 + g)).getD 1 =
        (am.1.gate.map (rowValue (W.tableCols t) u)).getD 1 := by
      cases hga : am.1.gate with
      | none => rfl
      | some g => simp [hgate am hmem g (by simp [hga])]
    rw [tv_stepTabs_shift W inp t hus k hidx, hget, hk, hfn,
      fn_T W.chunks r _ (by omega) (hms am hmem) hd, hg]
    have hl0 : (W.chunks.part r 0).length = W.chunks.widths.getD 0 0 := length_part hc r hr hd
    have hdig := digit_lt_part hc r hr hd σ
    rw [evalChunk_pow W.chunks _ _ 0 (W.chunks.digit σ 0) (fun j hj ↦ hc.bits σ 0 hd j (by
        simpa [linkWindowShift, eqKernel_length, hl0] using hj))
        (by simpa [linkWindowShift, eqKernel_length] using hdig),
      getD_linkWindowShift _ _ (by rw [eqKernel_length]; exact hdig)]
    rw [← window_rest hc r hr σ am.1.shift]
    ring
  rw [List.map_congr_left hshift, ← prod_D hc r hr σ]
  ring

end Val

end LeanVM.Prover.Complete.RowId

end
