/-
  LeanVM.Prover.Complete.Link.RowIdTable

  A table's sum over its rows, on one-hot pointer words: its pointers' reads over the executed
  rows, and its base terms over all its rows.
-/

module

public import LeanVM.Prover.Complete.Link.RowIdPtr

/-!
# A table's cube sum

`cubeSum_rowProds`: table `t`'s sum over its `2^h` rows (`rowProds`), where every pointer column
is one-hot on the executed rows, is the sum over its executed rows of its pointer columns' reads
(`ptrVal`: `(ω·c_ω + c_act)·eq(r, σ)` and the shifted accesses) plus the sum over all its rows of
its base terms (`baseVal`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete.RowId

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover Finset
open LeanVM.Protocol.KeccakGkr (eqAt)

section Table

variable (W : Witness) (inp : RowInputs) (t q₀ : ℕ)

/-- `ω_F` at row `u`. -/
def omegaU (u : ℕ) : E :=
  (omegaTable (inp.ch.theta.getD t 0) inp.ch.tau (W.layout.tableLogHeights.getD t 0)
    (W.rows.getD t 0)).getD u 0

/-- Pointer column `p` (the `k`-th) of table `t` at an executed row `u`, its word one-hot at `σ`. -/
def ptrVal (r : List E) (σ u p k : ℕ) : E :=
  let col := rowValue (W.tableCols t) u
  let links := (tables.getD t default).links
  let mu := inp.ch.mu.getD t []
  let cf := rowCoefs inp links mu k p col
  (omegaU W inp t u * cf.1 + cf.2) * eqAt r σ +
    (((accessesAt links mu p).filter (fun am ↦ !decide (am.1.shift = 0))).map fun am ↦
      inp.ch.etaMem * inp.yMem * am.2 * omegaU W inp t u * (am.1.gate.map col).getD 1 *
        shEq W.chunks r σ am.1.shift).sum

/-- Table `t`'s base terms at row `u`. -/
def baseVal (u : ℕ) : E :=
  let col := rowValue (W.tableCols t) u
  ((tableBlocks inp.ch t inp.eq0 (some inp.jump)).map fun b ↦
    (if b.onEq then (eqTable (inp.ch.tau.take (W.layout.tableLogHeights.getD t 0))).getD u 0
      else omegaU W inp t u) * (b.gate.map col).getD 1 * b.form.evaluate col).sum

theorem formVars_tableBlocks (ch : LinkChallenges) {t : ℕ} (ht : t < nTables) (scale : E)
    (jump : Option (List E)) : ∀ b ∈ tableBlocks ch t scale jump,
      FormVars (tables.getD t default).width b.form ∧
        ∀ g ∈ b.gate, g < (tables.getD t default).width := by
  obtain ⟨hu, hg⟩ := formVars_payloadForms ch ht (ch.mu.getD t [])
  intro b hb
  unfold tableBlocks at hb
  dsimp only at hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ⟨(FormVars.empty _).addScaled hu _, by simp⟩
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨⟨g, f⟩, hgf, rfl⟩ := List.mem_map.mp hb
    exact ⟨(FormVars.empty _).addScaled (hg _ hgf).2 _, by simpa using (hg _ hgf).1⟩
  · split at hb
    · split at hb
      · rename_i hc
        simp only [List.mem_singleton] at hb
        subst hb
        have ht5 : t = opJump := by
          revert hc
          have : t < 6 := ht
          interval_cases t <;> decide
        subst ht5
        exact ⟨jump_vars _, by simp⟩
      · simp at hb
    · simp at hb

theorem getD_map_ofK (a : Array K) (u : ℕ) : (a.map ofK).getD u 0 = ofK (a.getD u 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[u]? with
  | none => exact (map_zero (algebraMap K E)).symm
  | some x => rfl

theorem omegaU_of_ge {u : ℕ} (hu : W.rows.getD t 0 ≤ u) : omegaU W inp t u = 0 := by
  have h' : ¬ u < W.rows[t]?.getD 0 := by simp only [List.getD_eq_getElem?_getD] at hu; omega
  simp only [omegaU, omegaTable, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    List.getD_eq_getElem?_getD, h', ↓reduceIte]
  split <;> rfl

theorem sum_map_flatMap {α β : Type} (f : α → List β) (g : β → E) :
    ∀ L : List α, ((L.flatMap f).map g).sum = (L.map fun x ↦ ((f x).map g).sum).sum
  | [] => by simp
  | x :: L => by simp [List.flatMap_cons, sum_map_flatMap f g L]

/-- The tables `rowProds` starts its pointer fold from. -/
theorem rowInit_eq : rowInit W inp t = ((rowInit W inp t).1, #[], (rowInit W inp t).1.size) := by
  simp [rowInit]; omega

theorem tv_rowInit {X : Array (Array E)} {u : ℕ} (hu : u < 2 ^ W.layout.tableLogHeights.getD t 0) :
    tv ((rowInit W inp t).1 ++ X) u 0 = omegaU W inp t u ∧
      tv ((rowInit W inp t).1 ++ X) u 1 = (if u < W.rows.getD t 0 then 1 else 0) ∧
      tv ((rowInit W inp t).1 ++ X) u 2 =
        (eqTable (inp.ch.tau.take (W.layout.tableLogHeights.getD t 0))).getD u 0 ∧
      ∀ v < (tables.getD t default).width,
        tv ((rowInit W inp t).1 ++ X) u (3 + v) = rowValue (W.tableCols t) u v := by
  have hs : (rowInit W inp t).1.size = 3 + (tables.getD t default).width := by simp [rowInit]; omega
  refine ⟨?_, ?_, ?_, fun v hv ↦ ?_⟩
  · rw [tv_append_left _ _ (by omega)]; simp [tv, rowInit, omegaU]
  · rw [tv_append_left _ _ (by omega)]
    have hu' := hu
    simp only [List.getD_eq_getElem?_getD] at hu'
    simp [tv, rowInit, Array.getD_eq_getD_getElem?, hu']
  · rw [tv_append_left _ _ (by omega)]; simp [tv, rowInit]
  · rw [tv_append_left _ _ (by omega)]
    unfold rowInit
    dsimp only
    rw [show 3 + v = (#[omegaTable (inp.ch.theta.getD t 0) inp.ch.tau (W.layout.tableLogHeights.getD t 0)
        (W.rows.getD t 0), Array.ofFn (n := 2 ^ W.layout.tableLogHeights.getD t 0) fun u ↦
          if u.val < W.rows.getD t 0 then (1 : E) else 0,
        eqTable (inp.ch.tau.take (W.layout.tableLogHeights.getD t 0))]).size + v by simp,
      tv_append_right]
    simp only [tv, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range hv, Option.map_some, Option.getD_some, columnE]
    rw [← Array.getD_eq_getD_getElem?, getD_map_ofK]
    simp only [rowValue, Array.getD_eq_getD_getElem?]

theorem termAt_tables (P : Prods) (u : ℕ) : termAt P u = termAt ⟨P.tables, #[]⟩ u := rfl

/-- **Table `t`'s sum over its rows**: its pointer columns' reads over the executed rows, where
every pointer word is one-hot, plus its base terms over all its rows. -/
theorem cubeSum_rowProds {r : List E} (σf : ℕ → ℕ → ℕ) (ht : t < nTables)
    (hc : ChunkFacts W.chunks) (hok : ChunksOK W.chunks) (hr : r.length = W.chunks.width)
    (hfn : inp.functionals = Functionals.new W.chunks r inp.maxShift)
    (hms : ∀ a ∈ (tables.getD t default).links.memory, a.shift ≤ inp.maxShift)
    (hn : W.rows.getD t 0 ≤ 2 ^ W.layout.tableLogHeights.getD t 0)
    (hsize : ∀ c < (tables.getD t default).width,
      ((W.tableCols t).getD c #[]).size = 2 ^ W.layout.tableLogHeights.getD t 0)
    (hoh : ∀ p ∈ (tables.getD t default).links.pointers,
      OneHotWords W.chunks ((W.tableCols t).getD p #[]) (W.rows.getD t 0) (σf p)) :
    cubeSum (2 ^ W.layout.tableLogHeights.getD t 0) (rowProds W inp t q₀).1 =
      ∑ u ∈ range (W.rows.getD t 0), ((tables.getD t default).links.pointers.zipIdx.map fun pk ↦
          ptrVal W inp t r (σf pk.1 u) u pk.1 pk.2).sum +
        ∑ u ∈ range (2 ^ W.layout.tableLogHeights.getD t 0), baseVal W inp t u := by
  have hd := hc.pos
  obtain ⟨-, hptr⟩ := tables_pointers t ht
  have hwid := (tables_pointers t ht).1
  obtain ⟨X, Y, hR, hY⟩ := pointerFold W inp t q₀ hd (tables.getD t default).links.pointers.zipIdx
    (rowInit W inp t).1 #[]
  rw [rowProds_eq]
  dsimp only
  rw [rowInit_eq, hR]
  dsimp only
  unfold cubeSum
  have hsplit : ∀ u ∈ range (2 ^ W.layout.tableLogHeights.getD t 0),
      termsAt ⟨(rowInit W inp t).1 ++ X, (tableBlocks inp.ch t inp.eq0 (some inp.jump)).foldl
        rowBaseStep (#[].toList ++ Y).toArray⟩ u =
      (if u < W.rows.getD t 0 then ((tables.getD t default).links.pointers.zipIdx.map fun pk ↦
          ptrVal W inp t r (σf pk.1 u) u pk.1 pk.2).sum else 0) + baseVal W inp t u := by
    intro u hu
    have hu' := mem_range.mp hu
    obtain ⟨hT0, hT1, hT2, hT3⟩ := tv_rowInit W inp t (X := X) hu'
    rw [termsAt_eq_sum, foldl_rowBaseStep, termAt_tables]
    simp only [List.nil_append, List.map_append, List.sum_append]
    congr 1
    · have h := hY u #[]
      rw [Array.append_empty] at h
      rw [h]
      split
      · next hun =>
        refine congrArg _ (List.map_congr_left fun pk hpk ↦ ?_)
        obtain ⟨p, k⟩ := pk
        have hp : p ∈ (tables.getD t default).links.pointers := List.fst_mem_of_mem_zipIdx hpk
        have hpw := hptr p hp
        obtain ⟨-, hword⟩ := hoh p hp u hun
        rw [stepVal_exec W inp t q₀ hc hok hr hfn _ u p k (σf p u)
          (fun am ham ↦ hms am.1 (List.of_mem_zip (List.mem_filter.mp ham).1).1) hu'
          (hsize p (by rw [hwid]; exact hpw)) hword (by rw [hT1, ite_eq_left hun])
          (fun am ham g hg ↦ hT3 g (tables_vars t ht |>.2.2 am.1
            (List.of_mem_zip (List.mem_filter.mp ham).1).1 |>.2.2 g hg)), hT0]
        rfl
      · next hun =>
        refine List.sum_eq_zero fun x hx ↦ ?_
        obtain ⟨⟨p, k⟩, -, rfl⟩ := List.mem_map.mp hx
        exact stepVal_pad W inp t q₀ _ u p k (by rw [hT0, omegaU_of_ge W inp t (by omega)])
          (by rw [hT1, ite_eq_right hun])
    · rw [sum_map_flatMap]
      unfold baseVal
      dsimp only
      refine congrArg _ (List.map_congr_left fun b hb ↦ ?_)
      obtain ⟨hbv, hbg⟩ := formVars_tableBlocks inp.ch ht _ _ b hb
      rw [baseTerms_val _ u _ (rowValue (W.tableCols t) u) hT3 b hbv hbg]
      cases b.onEq <;> simp [hT0, hT2]
  rw [sum_congr rfl hsplit, sum_add_distrib, ← sum_range_add_sum_Ico _ hn]
  rw [sum_congr rfl fun u hu ↦ ite_eq_left (mem_range.mp hu),
    sum_eq_zero fun u hu ↦ ite_eq_right (by have := (mem_Ico.mp hu).1; omega), add_zero]

end Table

end LeanVM.Prover.Complete.RowId

end
