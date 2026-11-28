/-
  LeanVM.Protocol.Relation.Link.GroupJump

  The drawn group's count when a `JUMP` constraint fails: the weight of `JUMP`'s identity `j` is
  `Σ_u eq(τ, u)·id_j(row u)`, a nonzero polynomial of degree at most `m` in the drawn challenges.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupOneHot
public import LeanVM.Protocol.Relation.Link.Affine

/-!
# A `JUMP` constraint failing

`JUMP`'s coefficients enter the row side's fold only through `base` (`rowStep_base`), table by table
(`stepAdd`), and only a table with constraints adds them: `JUMP` alone (`tables_constraints_nil`).
So the weight `linkB … r (j + 1)` of `JUMP`'s identity `j` is the cube sum of
`eq(0, q)·corner_J·eq(τ, χ)·id_j(values_J)` (`rowSummand_jump`), the values the ones the stack sends
`JUMP` (`sent_honest`). At a Boolean point they are the row's non-pointer columns, which are all
`JUMP`'s identities read (`jump_nonPointer`), so (`linkB_jump_closed`)

  `linkB … r (j + 1) = Σ_{u < 2^h_J} eq(τ, u)·id_j(row u)`,

independent of `r`, of degree `h_J ≤ m` in the draw (`polyFn_linkB_jump`) and equal to the failing
identity at `τ` the failing row's bits (`tauPick`). Wherever it is nonzero the draw is doomed
(`groupDoom_of_B`), so at most `m·|E|^N` draws escape (`card_notDoom_of_not_constraints`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Protocol.Hotwire Finset

@[expose] public section

open Classical

/-! ## The row side's `sent` and `base` -/

theorem rowStep_sent (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi : List E)
    (acc : LinkRowSide) (x : Table × ℕ) :
    (rowStep layout ch a jump eqQ chi acc x).sent =
      acc.sent.drop (nonPointerOf layout x.2 x.1).length := by
  rw [rowStep_def]
  exact foldl_ptrStep_sent _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The values the row side reads before table `t`. -/
def sentBefore (layout : Layout) (t : ℕ) : ℕ :=
  ∑ t' ∈ range t, (nonPointerOf layout t' (layout.tables.getD t' default)).length

theorem rowFold_sent_base (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi message : List E) :
    ∀ n : ℕ,
    (((List.range n).map fun t ↦ (layout.tables.getD t default, t)).foldl
      (rowStep layout ch a jump eqQ chi) (rowStart layout message)).sent =
        (rowStart layout message).sent.drop (sentBefore layout n) ∧
    (((List.range n).map fun t ↦ (layout.tables.getD t default, t)).foldl
      (rowStep layout ch a jump eqQ chi) (rowStart layout message)).base =
        ∑ t ∈ range n, stepAdd layout ch a jump chi
          ((rowStart layout message).sent.drop (sentBefore layout t)) (layout.tables.getD t default, t)
  | 0 => by simp [rowStart, sentBefore]
  | n + 1 => by
    obtain ⟨h1, h2⟩ := rowFold_sent_base layout ch a jump eqQ chi message n
    rw [List.range_succ, List.map_append, List.foldl_append, List.map_singleton, List.foldl_cons,
      List.foldl_nil, rowStep_sent, rowStep_base, h1, h2, sum_range_succ, List.drop_drop]
    refine ⟨?_, rfl⟩
    congr 1
    simp only [sentBefore, sum_range_succ]

/-- **`base` over every table**: what each table adds, from the values left before it. -/
theorem rowSideOf_base (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi message : List E) :
    (rowSideOf layout ch a jump eqQ chi message).base = ∑ t ∈ range layout.tables.length,
      stepAdd layout ch a jump chi ((rowStart layout message).sent.drop (sentBefore layout t))
        (layout.tables.getD t default, t) := by
  have h := (rowFold_sent_base layout ch a jump eqQ chi message layout.tables.length).2
  rw [← zipIdx_eq_map] at h
  exact h

/-- Table `x`'s values, as the row side reads them from `sent`. -/
def valuesOf (layout : Layout) (sent : List E) (x : Table × ℕ) : List E :=
  (List.range x.1.width).map fun c ↦
    (((nonPointerOf layout x.2 x.1).zip (sent.take (nonPointerOf layout x.2 x.1).length)).lookup c).getD 0

/-- **What `jump` adds** to a table's step: its identities under `eq(τ, χ)`, if it has any. -/
theorem stepAdd_sub (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump chi sent : List E)
    (x : Table × ℕ) :
    stepAdd layout ch a jump chi sent x - stepAdd layout ch a [] chi sent x =
      if 0 < x.1.nConstraints then
        prodE ((chi.drop (heightOf layout x.2)).map (1 + ·)) *
          (eqEval (ch.tau.take (heightOf layout x.2)) (chi.take (heightOf layout x.2)) *
            sumE (List.zipWith (· * ·) jump (x.1.constraints (valuesOf layout sent x))))
      else 0 := by
  unfold stepAdd tableBaseOf valuesOf heightOf
  dsimp only
  split_ifs
  · rw [List.zipWith_nil_left, sumE_nil]
    ring
  · ring

/-! ## The tables' constraints -/

theorem tables_constraints_nil {t : ℕ} (ht : t < nTables) (h4 : t ≠ 4) (v : List E) :
    (tables.getD t default).constraints v = [] := by
  have h6 : t < 6 := ht
  interval_cases t <;> first | rfl | omega

theorem tables_nConstraints {t : ℕ} (ht : t < nTables) (h4 : t ≠ 4) :
    (tables.getD t default).nConstraints = 0 := by
  rw [Table.nConstraints, tables_constraints_nil ht h4, List.length_nil]

theorem jump_nConstraints : 0 < (tables.getD 4 default).nConstraints := by
  rw [Table.nConstraints, jump_links.2.2.2]
  simp [jumpConstraints]

/-- `JUMP`'s identities read its columns `0..8`, none a pointer. -/
theorem jump_nonPointer : ∀ c < 9, c ∈ (List.range (tables.getD 4 default).width).filter
    fun c ↦ !((tables.map (·.links.pointers)).getD 4 []).contains c := by
  decide +kernel

/-- **`jump`'s part of `base`**: `JUMP`'s identities alone. -/
theorem rowSideOf_jump_sub (layout : Layout) (hT : layout.tables = tables) (ch : LinkCh) (a : IdxAt)
    (jump eqQ chi message : List E) :
    (rowSideOf layout ch a jump eqQ chi message).base - (rowSideOf layout ch a [] eqQ chi message).base =
      prodE ((chi.drop (heightOf layout 4)).map (1 + ·)) *
        (eqEval (ch.tau.take (heightOf layout 4)) (chi.take (heightOf layout 4)) *
          sumE (List.zipWith (· * ·) jump (jumpConstraints (valuesOf layout
            ((rowStart layout message).sent.drop (sentBefore layout 4)) (tables.getD 4 default, 4))))) := by
  rw [rowSideOf_base, rowSideOf_base, ← sum_sub_distrib, hT, tables_length, sum_eq_single 4]
  · rw [stepAdd_sub, jump_links.2.2.2]
    simp only [jump_nConstraints, ↓reduceIte]
  · intro t ht h4
    rw [stepAdd_sub, tables_nConstraints (mem_range.mp ht) h4]
    simp
  · intro h
    exact absurd (mem_range.mpr (by decide)) h

/-! ## The stack's values at a Boolean point -/

theorem take_drop_flatten : ∀ (L : List (List E)) (t : ℕ), t < L.length →
    (L.flatten.drop (∑ i ∈ range t, (L.getD i []).length)).take (L.getD t []).length = L.getD t []
  | [], t, h => absurd h (by simp)
  | l :: L, 0, _ => by simp
  | l :: L, t + 1, h => by
    have ih := take_drop_flatten L t (by simpa using h)
    rw [sum_range_succ', List.flatten_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm, ← List.drop_drop, List.drop_left]
    exact ih

/-- Table `t`'s values on the stack at the row point: its non-pointer columns' extensions. -/
def chunkOf (layout : Layout) {μ : ℕ} (q : Column μ) (chi : List E) (t : ℕ) : List E :=
  (nonPointerOf layout t (layout.tables.getD t default)).map fun c ↦
    rowMle (chi.take (heightOf layout t)) (columnValue layout q (globalColumnBases.getD t 0 + c))

theorem honestValues_chunks (layout : Layout) {μ : ℕ} (q : Column μ) (chi : List E) :
    honestValues layout q chi = ((List.range layout.tables.length).map (chunkOf layout q chi)).flatten := by
  rw [honestValues, zipIdx_eq_map, List.map_map]
  rfl

theorem rowStart_sent_honest (layout : Layout) {μ : ℕ} (q : Column μ) (chi qPoint : List E) :
    (rowStart layout (honestMessage layout q chi qPoint)).sent = honestValues layout q chi := by
  show (honestMessage layout q chi qPoint).take (nValuesOf layout) = _
  rw [honestMessage, List.take_left' (length_honestValues layout q chi)]

/-- **The stack sends table `t` its chunk.** -/
theorem sent_honest (layout : Layout) {μ : ℕ} (q : Column μ) (chi qPoint : List E) {t : ℕ}
    (ht : t < layout.tables.length) :
    (((rowStart layout (honestMessage layout q chi qPoint)).sent.drop (sentBefore layout t)).take
      (nonPointerOf layout t (layout.tables.getD t default)).length) = chunkOf layout q chi t := by
  have hg : ∀ i < layout.tables.length,
      ((List.range layout.tables.length).map (chunkOf layout q chi)).getD i [] = chunkOf layout q chi i :=
    fun i hi ↦ by rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  have h := take_drop_flatten ((List.range layout.tables.length).map (chunkOf layout q chi)) t
    (by simpa using ht)
  rw [hg t ht, sum_congr rfl fun i hi ↦ by
    rw [hg i ((mem_range.mp hi).trans ht)]] at h
  rw [rowStart_sent_honest, honestValues_chunks]
  simpa [sentBefore, chunkOf] using h

theorem lookup_zip_map (f : ℕ → E) {c : ℕ} : ∀ l : List ℕ, c ∈ l → (l.zip (l.map f)).lookup c = some (f c)
  | [], h => absurd h List.not_mem_nil
  | k :: l, h => by
    by_cases hc : c = k
    · subst hc
      simp
    · have := lookup_zip_map f l (by simpa [hc] using h)
      have hb : (c == k) = false := by simpa using hc
      simp [List.lookup, hb, this]

theorem valuesOf_getD (layout : Layout) (sent : List E) (x : Table × ℕ) (f : ℕ → E)
    (hs : sent.take (nonPointerOf layout x.2 x.1).length = (nonPointerOf layout x.2 x.1).map f)
    {c : ℕ} (hc : c ∈ nonPointerOf layout x.2 x.1) :
    (valuesOf layout sent x).getD c 0 = f c := by
  have hw : c < x.1.width := by
    unfold nonPointerOf at hc
    exact List.mem_range.mp (List.mem_filter.mp hc).1
  rw [valuesOf, List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_map, List.getElem_range, hs,
    lookup_zip_map f _ hc, Option.getD_some]

/-- `JUMP`'s identity `j` on row `u`. -/
def jumpId (layout : Layout) {μ : ℕ} (q : Column μ) (j u : ℕ) : E :=
  (jumpConstraints (rowValues layout q 4 u)).getD j 0

/-- **`JUMP`'s values at a Boolean row point** are its row's, where its identities read them. -/
theorem jumpConstraints_bool (layout : Layout) (hT : layout.tables = tables) {μ : ℕ} (q : Column μ)
    (qPoint : List E) (jx : ℕ) :
    jumpConstraints (valuesOf layout
      ((rowStart layout (honestMessage layout q (boolL (linkRows layout) jx) qPoint)).sent.drop
        (sentBefore layout 4)) (tables.getD 4 default, 4)) =
      jumpConstraints (rowValues layout q 4 (jx % 2 ^ heightOf layout 4)) := by
  have h4 : 4 < layout.tables.length := by rw [hT, tables_length]; decide
  have hs := sent_honest layout q (boolL (linkRows layout) jx) qPoint h4
  rw [hT] at hs
  have hv : ∀ c < 9, (valuesOf layout
      ((rowStart layout (honestMessage layout q (boolL (linkRows layout) jx) qPoint)).sent.drop
        (sentBefore layout 4)) (tables.getD 4 default, 4)).getD c 0 =
      (rowValues layout q 4 (jx % 2 ^ heightOf layout 4)).getD c 0 := by
    intro c hc
    have hmem : c ∈ nonPointerOf layout 4 (tables.getD 4 default) := by
      unfold nonPointerOf
      rw [hT]
      exact jump_nonPointer c hc
    rw [valuesOf_getD layout _ (tables.getD 4 default, 4) _ (by rw [hs, chunkOf, hT]) hmem,
      take_boolL (heightOf_le layout 4), rowMle_boolL (Nat.mod_lt _ (Nat.two_pow_pos _)),
      rowValues_getD hT q _ (by rw [jump_links.2.2.1]; omega)]
    rfl
  rw [jumpConstraints_eq, jumpConstraints_eq, hv 0 (by norm_num), hv 1 (by norm_num),
    hv 2 (by norm_num), hv 3 (by norm_num), hv 4 (by norm_num), hv 5 (by norm_num),
    hv 6 (by norm_num), hv 7 (by norm_num), hv 8 (by norm_num)]

/-! ## The weight in closed form -/

theorem eqEval_boolL : ∀ (pt : List E) (u : ℕ), eqEval pt (boolL pt.length u) = eqAt pt u
  | [], u => by simp [eqEval, boolL]
  | z :: zs, u => by
    have hu : boolL (zs.length + 1) u = (if u % 2 = 1 then 1 else 0) :: boolL zs.length (u / 2) := by
      have := boolL_succ zs.length (u % 2) (u / 2) (Nat.mod_lt _ (by norm_num))
      rwa [show u % 2 + 2 * (u / 2) = u by omega] at this
    rw [List.length_cons, hu, Tables.eqEval_cons, eqEval_boolL zs, eqAt_cons]
    congr 1
    split_ifs
    · linear_combination Tables.two_eq_zero_E
    · linear_combination z * Tables.two_eq_zero_E

theorem unitFresh_succ_head (j : Fin 4) : (unitFresh j.succ).getD 0 0 = 0 := by
  fin_cases j <;> rfl

theorem sumE_unit_jump (j : Fin 4) (ids : List E) (hids : ids.length = 4) :
    sumE (List.zipWith (· * ·) ((unitFresh j.succ).drop 1) ids) = ids.getD j 0 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, ids = [a, b, c, d] := by
    match ids, hids with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  fin_cases j <;> simp [unitFresh, List.ofFn_succ, sumE]

/-- **`JUMP`'s coefficient `j` adds** `eq(0, q)` times `jump`'s part of `base`. -/
theorem rowSummand_jump (layout : Layout) (hT : layout.tables = tables) (chunks : Chunks) {μ : ℕ}
    (q : Column μ) (theta0 : E) (drawn r x : List E) (j : Fin 4) :
    rowSummand layout chunks q theta0 drawn r (unitFresh j.succ) x -
        rowSummand layout chunks q theta0 drawn r [] x =
      prodE ((x.drop (linkRows layout)).map (1 + ·)) *
        (prodE (((x.take (linkRows layout)).drop (heightOf layout 4)).map (1 + ·)) *
          (eqEval ((linkCh layout chunks theta0 drawn).tau.take (heightOf layout 4))
              ((x.take (linkRows layout)).take (heightOf layout 4)) *
            (jumpConstraints (valuesOf layout
              ((rowStart layout (honestMessage layout q (x.take (linkRows layout))
                (x.drop (linkRows layout)))).sent.drop (sentBefore layout 4))
              (tables.getD 4 default, 4))).getD j 0)) := by
  set ch := linkCh layout chunks theta0 drawn
  set a := idxAt layout chunks ch r (honestM1 layout chunks q r) (linkSplit layout r)
  set chi := x.take (linkRows layout)
  set qPoint := x.drop (linkRows layout)
  set msg := honestMessage layout q chi qPoint
  have hrest := (rowSideOf_aff layout hT ch a (eqKernel qPoint) chi msg).1
  have e : rowSummand layout chunks q theta0 drawn r (unitFresh j.succ) x =
      lastOf layout chunks ch r ((unitFresh j.succ).getD 0 0) qPoint (msg.drop (nValuesOf layout))
        (rowSideOf layout ch a ((unitFresh j.succ).drop 1) (eqKernel qPoint) chi msg) := rfl
  have e0 : rowSummand layout chunks q theta0 drawn r [] x =
      lastOf layout chunks ch r 0 qPoint (msg.drop (nValuesOf layout))
        (rowSideOf layout ch a [] (eqKernel qPoint) chi msg) := rfl
  rw [e, e0, unitFresh_succ_head, lastOf_rest _ _ _ _ _ _ _ (hrest _), add_sub_cancel_left,
    rowSideOf_jump_sub layout hT, sumE_unit_jump j _ (by simp [jumpConstraints])]

/-- **The weight of `JUMP`'s identity `j` in closed form**: `Σ_{u < 2^h_J} eq(τ, u)·id_j(row u)`. -/
theorem linkB_jump_closed (layout : Layout) (hT : layout.tables = tables) (chunks : Chunks) {μ : ℕ}
    (q : Column μ) (theta0 : E) (drawn r : List E) (j : Fin 4)
    (hτ : (linkCh layout chunks theta0 drawn).tau.length = linkRows layout) :
    linkB layout chunks q theta0 drawn r j.succ = ∑ u ∈ range (2 ^ heightOf layout 4),
      eqAt ((linkCh layout chunks theta0 drawn).tau.take (heightOf layout 4)) u * jumpId layout q j u := by
  have hh := heightOf_le layout 4
  have hτh : ((linkCh layout chunks theta0 drawn).tau.take (heightOf layout 4)).length =
      heightOf layout 4 := by rw [List.length_take, hτ]; exact min_eq_left hh
  simp only [linkB, linkIdxAt, linkRow, cube, List.length_nil, Nat.sub_zero, linkRowVars]
  rw [sumTail_split, sumTail_split, ← sum_sub_distrib,
    ← sum_range_ite_lt (Nat.pow_le_pow_right (by norm_num) hh)]
  refine sum_congr rfl fun jx hjx ↦ ?_
  have hjx' := mem_range.mp hjx
  rw [sumTail_eq_sum, sumTail_eq_sum, ← sum_sub_distrib]
  simp only [List.nil_append]
  rw [sum_congr rfl fun jq _ ↦ rowSummand_jump layout hT chunks q theta0 drawn r _ j]
  simp only [List.take_left' (length_boolL _ _), List.drop_left' (length_boolL _ _)]
  rw [sum_congr rfl fun jq hjq ↦ by rw [prodE_eq_prod, prod_one_add_boolL _ _ (mem_range.mp hjq)],
    take_boolL hh, prodE_drop_boolL hh hjx']
  simp only [jumpConstraints_bool layout hT q, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range, Nat.two_pow_pos, ↓reduceIte]
  split_ifs with hlt
  · have he := eqEval_boolL ((linkCh layout chunks theta0 drawn).tau.take (heightOf layout 4)) jx
    rw [hτh] at he
    rw [Nat.mod_eq_of_lt hlt, he]
    rfl
  · rfl

/-! ## The count -/

/-- The pick: `τ` the bits of `u0`, every other coordinate zero. -/
def tauPick (layout : Layout) (chunks : Chunks) (u0 : ℕ) : Fin (linkDrawn layout chunks + 1) → E :=
  fun k ↦ if tauOff layout ≤ k.val ∧ k.val < tauOff layout + linkRows layout then
    (if u0.testBit (k.val - tauOff layout) then 1 else 0) else 0

section Count

variable {layout : Layout} {chunks : Chunks} (hch : Chunks.new chunks.width = some chunks)
include hch

theorem tau_tauPick {h : ℕ} (hh : h ≤ linkRows layout) (u0 : ℕ) :
    (chV layout chunks (tauPick layout chunks u0)).tau.take h = boolL h u0 := by
  refine List.ext_getElem (by rw [List.length_take, chV_tau_length hch, length_boolL]; omega)
    fun k h1 h2 ↦ ?_
  rw [length_boolL] at h2
  rw [List.getElem_take, ← List.getD_eq_getElem _ 0, chV_tau hch _ (by omega)]
  simp only [boolL, List.getElem_ofFn, boolPt, tauPick]
  split_ifs <;> first | omega | simp_all

/-- **The weight of `JUMP`'s identity `j`** is a polynomial of degree `h_J` in the draw. -/
theorem polyFn_linkB_jump (hT : layout.tables = tables) {μ : ℕ} (q : Column μ) (r : List E)
    (j : Fin 4) :
    PolyFn (linkDrawn layout chunks + 1) (heightOf layout 4)
      (fun v ↦ linkB layout chunks q ((List.ofFn v).headD 0) (List.ofFn v).tail r j.succ) := by
  have hN := linkDrawn_eq layout chunks hch
  have hh := heightOf_le layout 4
  refine PolyFn.congr ?_ fun v ↦
    (linkB_jump_closed layout hT chunks q _ _ r j (chV_tau_length hch v)).symm
  refine PolyFn.finsetSum _ fun u _ ↦ ?_
  have heq : PolyFn (linkDrawn layout chunks + 1) (heightOf layout 4) fun v ↦
      eqAt ((chV layout chunks v).tau.take (heightOf layout 4)) u := by
    have hlen : ∀ v, ((chV layout chunks v).tau.take (heightOf layout 4)).length = heightOf layout 4 := by
      intro v
      rw [List.length_take, chV_tau_length hch v]
      exact min_eq_left hh
    refine polyFn_eqAt (heightOf layout 4) (fun v ↦ (chV layout chunks v).tau.take (heightOf layout 4))
      hlen (fun k hk ↦ ?_) u
    have hkm : k < linkRows layout := by omega
    refine (PolyFn.var ⟨tauOff layout + k, by simp only [nuOff] at hN; omega⟩).congr fun v ↦ ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_take]
    simp only [hk, ↓reduceIte]
    rw [← List.getD_eq_getElem?_getD, chV_tau hch v hkm]
  exact (heq.mul (PolyFn.const (jumpId layout q j u))).mono (by omega)

end Count

/-- **A `JUMP` constraint failing**: at most `m·|E|^N` draws escape the group's doom, within
`linkGroupError`. -/
theorem card_notDoom_of_not_constraints {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (hA : Announced bytecode layout ρ) {μ : ℕ} (q : Column μ) {chunks : Chunks}
    (hch : Chunks.new (linkWidth layout) = some chunks) (hJ : ¬ ConstraintsHold layout q) :
    (univ.filter fun v ↦ ¬ GroupDoomAt layout q chunks v).card ≤
      linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks := by
  have hch' : Chunks.new chunks.width = some chunks := by rw [Chunks.new_width hch]; exact hch
  have hT := (announced_facts hA).2.1
  unfold ConstraintsHold at hJ
  push Not at hJ
  obtain ⟨t, ht, u0, hu0, c, hc, hne⟩ := hJ
  have ht4 : t = 4 := by
    by_contra h4
    rw [tableAt_eq hT, tables_constraints_nil ht h4] at hc
    exact List.not_mem_nil hc
  subst ht4
  rw [tableAt_eq hT, jump_links.2.2.2] at hc
  obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hc
  have hj4 : j < 4 := by simpa [jumpConstraints] using hj
  have hid : jumpId layout q j u0 = c := by rw [jumpId, List.getD_eq_getElem _ _ hj, hje]
  have hu0' : u0 < 2 ^ heightOf layout 4 := hu0
  refine card_not_doom_le (polyFn_linkB_jump hch' hT q (List.replicate chunks.width 0) ⟨j, hj4⟩)
    (x0 := tauPick layout chunks u0) ?_
    (fun v hv ↦ groupDoom_of_B (Fin.succ ⟨j, hj4⟩) _ (List.length_replicate ..) hv) ?_
  · rw [linkB_jump_closed layout hT chunks q _ _ _ _ (chV_tau_length hch' _),
      tau_tauPick hch' (heightOf_le layout 4), sum_eq_single u0]
    · rw [eqAt_boolL hu0' hu0', hid]
      simpa using hne
    · intro u hu hne'
      rw [eqAt_boolL (mem_range.mp hu) hu0']
      simp [hne']
    · intro h
      exact absurd (mem_range.mpr hu0') h
  · have := heightOf_le layout 4
    unfold linkGroupError
    omega

end

end LeanVM.Protocol.Relation
