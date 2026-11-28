/-
  LeanVM.Prover.Complete.Link.TailRowTable

  One honest table after the row rounds: what its bound tables read, and its pointer columns'
  coefficients, shifts and certificate weights in the verifier's terms.
-/

module

public import LeanVM.Prover.Complete.Link.TailRowBase
public import LeanVM.Prover.Complete.Link.Steps

/-!
# One table after the row rounds

`boundAt`: table `t` bound at `χ`, its first tables read `ω` (`omegaTable`'s extension), the
activity (`lessThan`), `eq(τ, ·)` (`eqEval`) and its columns' extensions (`mcolOf`), its corner is
`Π (1 + x)` over `χ.drop h`, and its pointer columns are `colSpec` of its pointers.
`colSpec_coef`, `colSpec_shifts`, `colSpec_certs`: each pointer column's coefficient, shift
coefficients and certificate weights are the verifier's (`vCoef`, `vShift`) at any values `vcol`
agreeing with the columns' extensions on the non-pointer columns, times the corner.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers Finset
open LeanVM.Protocol.Hotwire (eqAt)

/-- Table `t`'s column `c` extended at `pt`. -/
noncomputable def mcolOf (W : Witness) (t : ℕ) (pt : List E) (c : ℕ) : E :=
  mleK ((W.tableCols t).getD c #[]) pt

theorem mleA_act (pt : List E) (n : ℕ) (hn : n ≤ 2 ^ pt.length) :
    mleA (Array.ofFn (n := 2 ^ pt.length) fun u ↦ if u.val < n then (1 : E) else 0) pt =
      lessThan pt n := by
  rw [lessThan, LeanVM.Protocol.Hotwire.one_add_paddingWeight_eq_mle pt n hn,
    mleA_eq_mle _ _ (by simp)]
  unfold LeanVM.Protocol.Hotwire.mle
  refine sum_congr rfl fun u hu ↦ ?_
  simp [Array.getD_eq_getD_getElem?, mem_range.mp hu]

theorem mleA_eqTable (p pt : List E) (h : p.length = pt.length) : mleA (eqTable p) pt = eqEval p pt := by
  rw [mleA_eq_sum _ _ (by rw [Keccak.size_eqTable, h]), LeanVM.Protocol.Hotwire.eqEval_eq_sum p pt h, h]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [eqTable_getD_eqAt, ite_eq_left (by rw [h]; exact mem_range.mp hj)]

theorem size_tableCols_le (W : Witness) (t : ℕ) : (W.tableCols t).size ≤ tableWidths.getD t 0 := by
  simp only [Witness.tableCols, Array.size_extract]
  omega

theorem rowSum_tableCols {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) {t : ℕ} (ht : t < nTables) (pt : List E)
    (hpt : pt.length = W.layout.tableLogHeights.getD t 0) :
    rowSum (W.tableCols t) pt = mcolOf W t pt := by
  funext c
  refine rowSum_eq_mleK _ _ _ ?_
  by_cases hc : c < tableWidths.getD t 0
  · exact Or.inl (by rw [size_tableCols_getD hW ht hc, hpt])
  · right
    have := size_tableCols_le W t
    simp [Array.getD_eq_getD_getElem?, show (W.tableCols t).size ≤ c by omega]

section Bound

variable {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog} {W : Witness}
  (hW : witness? prog input ex = some W) (x : LinkProverPre) (chi : List E)
  (hchi : chi.length = linkNRows W) (htau : x.ch.tau.length = linkNRows W)

include hW hchi htau in
/-- **Table `t` after the row rounds.** -/
theorem boundAt {t : ℕ} (ht : t < nTables) :
    let rt := (chi.foldl rowFold (linkRowStart W x)).getD t default
    let h := W.layout.tableLogHeights.getD t 0
    let inp := linkRowInputs W x
    rt.height = h ∧ rt.corner = prodE ((chi.drop h).map (1 + ·)) ∧
      rt.prods.at 0 = mleA (omegaTable (inp.ch.theta.getD t 0) inp.ch.tau h (W.rows.getD t 0))
        (chi.take h) ∧
      rt.prods.at 1 = lessThan (chi.take h) (W.rows.getD t 0) ∧
      rt.prods.at 2 = eqEval (inp.ch.tau.take h) (chi.take h) ∧
      (∀ c < (tables.getD t default).width, rt.prods.at (3 + c) = mcolOf W t (chi.take h) c) ∧
      columnsAt W inp t (pointerStarts.getD t 0) rt chi =
        (tables.getD t default).links.pointers.zipIdx.map fun pk ↦
          colSpec W inp t (pointerStarts.getD t 0) rt chi pk.1 pk.2 := by
  dsimp only
  obtain ⟨-, steps, -, -, hl, -, -, -, -⟩ := witness?_spec hW
  obtain ⟨hwid, -⟩ := tables_pointers t ht
  set h := W.layout.tableLogHeights.getD t 0 with hhdef
  have hh : h ≤ chi.length := hchi ▸ le_foldl_max _ _
  have hrt := rowStart_getD W x chi ht hh
  set inp := linkRowInputs W x with hinp
  set rt := (chi.foldl rowFold (linkRowStart W x)).getD t default with hrtdef
  set r := (tables.getD t default).links.pointers.zipIdx.foldl
    (rowPointerStep W inp t (pointerStarts.getD t 0)) (rowInit W inp t) with hr
  have hrp := rowProds_eq W inp t (pointerStarts.getD t 0)
  rw [← hr] at hrp
  have hheight : rt.height = h := by rw [hrt]
  have hlen : (chi.take h).length = h := by rw [List.length_take, min_eq_left hh]
  have hat : ∀ f, rt.prods.at f = mleA (r.1.getD f #[]) (chi.take rt.height) := by
    intro f
    rw [hrt, at_foldl, hrp]
  have hpre : (rowInit W inp t).1.toList <+: r.1.toList := foldl_rowPointerStep_prefix W inp t _ _ _
  have hinitL : (rowInit W inp t).1.toList =
      omegaTable (inp.ch.theta.getD t 0) inp.ch.tau h (W.rows.getD t 0) ::
        (Array.ofFn (n := 2 ^ h) fun u ↦ if u.val < W.rows.getD t 0 then (1 : E) else 0) ::
        eqTable (inp.ch.tau.take h) ::
        (List.range (tables.getD t default).width).map (columnE (W.tableCols t)) := by
    simp only [hhdef, rowInit, Array.toList_append, List.cons_append, List.nil_append]
    rfl
  have hinit : ∀ f < 3 + (tables.getD t default).width, rt.prods.at f =
      mleA (((rowInit W inp t).1.toList).getD f #[]) (chi.take h) := by
    intro f hf
    rw [hat, Keccak.getD_toList r.1, getD_of_prefix hpre (by rw [hinitL]; simp at hf ⊢; omega), hheight]
  have hrows : W.rows.getD t 0 ≤ 2 ^ h := by
    obtain ⟨-, hrw, -⟩ := buildLayout_spec hl
    exact hrw ▸ rows_le_height hl ht
  have htake : (inp.ch.tau.take h).length = (chi.take h).length := by
    rw [List.length_take, hlen, show inp.ch.tau.length = linkNRows W from htau]
    exact min_eq_left (hchi ▸ hh)
  refine ⟨hheight, by rw [hrt, tailRow_prodE_eq_prod], ?_, ?_, ?_, fun c hc ↦ ?_, ?_⟩
  · rw [hinit 0 (by omega), hinitL]; rfl
  · rw [hinit 1 (by omega), hinitL, List.getD_cons_succ, List.getD_cons_zero]
    rw [← mleA_act (chi.take h) _ (by rw [hlen]; exact hrows), hlen]
  · rw [hinit 2 (by omega), hinitL, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
      mleA_eqTable _ _ htake]
  · rw [hinit (3 + c) (by omega), hinitL, Nat.add_comm, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_cons_succ, getD_map_range_arr _ _ _ hc]
    rfl
  · rw [columnsAt_eq, foldl_columnStep_eq W inp t _ rt chi r.1 hat _ (rowInit W inp t)
      ([], 3 + (tables.getD t default).width) (by simp [rowInit]; omega) (by simp [rowInit])
      (List.prefix_refl _)]
    simp

end Bound

/-! ## The pointer columns in the verifier's terms -/

theorem lt_of_mem_nonPtr {t c : ℕ} (h : c ∈ nonPtr t) : c < (tables.getD t default).width := by
  unfold nonPtr at h
  exact List.mem_range.mp (List.mem_filter.mp h).1

theorem directAt_congr (links : Links) (mu : List E) (p : ℕ) {col col' : ℕ → E}
    (h : ∀ a ∈ links.memory, ∀ g, a.gate = some g → col g = col' g) :
    directAt links mu p col = directAt links mu p col' := by
  unfold directAt
  refine congrArg List.sum (List.map_congr_left fun am ham ↦ ?_)
  have ha := mem_memory_of_accessesAt ham
  rcases hg : am.1.gate with _ | g
  · rfl
  · simp [h _ ha g hg]

theorem readsAt_congr (links : Links) (mu : List E) (p : ℕ) {col col' : ℕ → E}
    (h : ∀ a ∈ links.memory, ∀ p' scale, Read.word p' scale ∈ a.reads →
      ∀ m ∈ scale.terms, ∀ v ∈ m.1, col v = col' v) :
    readsAt links mu p col = readsAt links mu p col' := by
  unfold readsAt
  refine congrArg List.sum (List.map_congr_left fun am ham ↦ ?_)
  have ha := (List.of_mem_zip ham).1
  refine congrArg List.sum (List.map_congr_left fun rd hrd ↦ ?_)
  cases rd with
  | word p' scale => simp only [wordAt]; rw [evaluate_congr (h _ ha p' scale hrd)]
  | _ => rfl

section Spec

variable {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog} {W : Witness}
  (hW : witness? prog input ex = some W) (x : LinkProverPre) (chi : List E)
  (hchi : chi.length = linkNRows W) (htau : x.ch.tau.length = linkNRows W)

include hW hchi htau in
/-- **A pointer column's coefficients, shifts and certificate weights, in the verifier's terms**,
at any values `vcol` agreeing with the columns' extensions off the pointer columns. -/
theorem colSpec_eq {t : ℕ} (ht : t < nTables) (vcol : ℕ → E)
    (hv : ∀ c ∈ nonPtr t, vcol c = mcolOf W t (chi.take (W.layout.tableLogHeights.getD t 0)) c)
    (p k : ℕ) :
    let rt := (chi.foldl rowFold (linkRowStart W x)).getD t default
    let inp := linkRowInputs W x
    let links := (tables.getD t default).links
    let mu := inp.ch.mu.getD t []
    let sg := fun (a b : E) ↦ 1 + inp.ch.gammaState.getD 0 0 * a + inp.ch.gammaState.getD 1 0 * b
    let c := colSpec W inp t (pointerStarts.getD t 0) rt chi p k
    c.coef = rt.corner * vCoef inp.ch (rt.prods.at 1) (rt.prods.at 0) inp.eqZeta inp.shiftZeta
        (sg (vcol links.stateLink.pc) (vcol links.stateLink.fp))
        (sg (links.stateLink.next.1.evaluate vcol) (links.stateLink.next.2.evaluate vcol))
        inp.xBc inp.pFp inp.yMem inp.m1 vcol links mu p k ∧
      (∀ s < inp.maxShift, c.shifts.getD s 0 =
        rt.corner * vShift inp.ch (rt.prods.at 0) inp.yMem vcol links mu p s) ∧
      (∀ i < W.chunks.d, c.certs.getD i 0 = rt.corner * (rt.prods.at 0 * inp.cert *
        inp.ch.eps.getD (pointerStarts.getD t 0 + k) 0 * inp.ch.nu.getD i 0)) ∧
      c.values = inp.functionals.values W.chunks c.slices ∧ c.slices.length = 64 := by
  intro rt inp links mu sg c
  have hf := tableFacts ht
  obtain ⟨hheight, -, -, -, -, hcol, -⟩ := boundAt hW x chi hchi htau ht
  set h := W.layout.tableLogHeights.getD t 0
  have hh : h ≤ chi.length := hchi ▸ le_foldl_max _ _
  have hlen : (chi.take rt.height).length = h := by
    rw [hheight, List.length_take, min_eq_left hh]
  obtain ⟨m1, m2⟩ := mleA_coefTable W inp hf k p (chi.take rt.height) hlen
  have hrs : rowSum (W.tableCols t) (chi.take rt.height) = mcolOf W t (chi.take h) := by
    rw [rowSum_tableCols hW ht _ hlen, hheight]
  rw [hrs] at m1 m2
  -- the columns the verifier reads
  have hmv : ∀ c ∈ nonPtr t, mcolOf W t (chi.take h) c = vcol c := fun c hc ↦ (hv c hc).symm
  have hPv : ∀ c ∈ nonPtr t, rt.prods.at (3 + c) = vcol c := fun c hc ↦ by
    rw [hcol c (lt_of_mem_nonPtr hc), hmv c hc]
  have hform : ∀ f : Form, formIn (nonPtr t) f = true →
      f.evaluate (mcolOf W t (chi.take h)) = f.evaluate vcol := fun f hf' ↦
    evaluate_congr fun m hm v hvm ↦ hmv v (formIn_spec hf' m hm v hvm)
  have hformA : ∀ f : Form, formAff (nonPtr t) f = true →
      f.evaluate (mcolOf W t (chi.take h)) = f.evaluate vcol := fun f hf' ↦
    evaluate_congr fun m hm v hvm ↦ hmv v ((formAff_spec hf').2 m hm v hvm)
  have hgate : ∀ a ∈ links.memory, ∀ g, a.gate = some g → mcolOf W t (chi.take h) g = vcol g :=
    fun a ha g hg ↦ hmv g (hf.gate a ha g hg)
  have hreads : ∀ a ∈ links.memory, ∀ p' scale, Read.word p' scale ∈ a.reads →
      ∀ m ∈ scale.terms, ∀ v ∈ m.1, mcolOf W t (chi.take h) v = vcol v :=
    fun a ha p' scale hrd m hm v hvm ↦ hmv v ((formAff_spec (hf.reads a ha _ hrd)).2 m hm v hvm)
  refine ⟨?_, fun s hs ↦ ?_, fun i hi ↦ ?_, rfl, length_columnSlices _ _⟩
  · show rt.corner * (rt.prods.at 0 * _ + rt.prods.at 1 * _) = _
    rw [m1, m2]
    match k with
    | 0 =>
      simp only [rowCoefs, stateValues, vCoef, sg, hmv _ hf.pc, hmv _ hf.fp, hformA _ hf.next1,
        hformA _ hf.next2]
      ring
    | 1 =>
      simp only [rowCoefs, vCoef, hmv _ hf.fp]
      ring
    | k + 2 =>
      rw [rowCoefs_mem, directAt_congr (tables.getD t default).links _ p hgate,
        readsAt_congr (tables.getD t default).links _ p hreads]
      simp only [vCoef]
      ring
  · simp only [c, colSpec, tailRowColAt, List.map_map]
    rw [getD_map_range_E _ _ _ hs, vShift]
    simp only [Function.comp, sumE_eq_sum]
    rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun am ham ↦ ?_)
    have ha := mem_memory_of_accessesAt ham
    obtain ⟨a, m⟩ := am
    have hg : ((a.gate.map fun g ↦ rt.prods.at (3 + g)).getD 1) = (a.gate.map vcol).getD 1 := by
      rcases hga : a.gate with _ | g
      · rfl
      · simp [hPv g (hf.gate a ha g hga)]
    simp only [hg]
    split_ifs <;> ring
  · simp only [c, colSpec, tailRowColAt, List.map_map]
    rw [getD_map_range_E _ _ _ hi]
    rfl

end Spec

end LeanVM.Prover.Complete

end
