/-
  LeanVM.Prover.Complete.Link.Column

  `ColumnSplit` on the honest witness: after the row rounds, the rows' claim is the pointer
  columns' cube sum.
-/

module

public import LeanVM.Prover.Complete.Link.ColumnStep

/-!
# The pointer columns' split

After the row rounds at `χ` every table is bound at `χ.take h` (`foldl_rowTableFold`), its value
the sum of its terms at the bound tables. `rowPointerStep`'s tables only grow, each pointer column's
functional tables at its position (`rowPointerStep_toList`), so the bound tables at a column's
position are its functional tables' extensions, the functionals of its slices (`mleA_functionalTable`,
for chunks whose one-hot blocks lie inside the word, `chunks_wordShift`), and every shift is at most
`maxShift` (`tables_shift_le`). So each table's corner times its value is its columns' parts plus
its base (`rowPart_eq`), and summed over the tables the rows' claim is the cube sum of
`columnProds` (`cubeSum_columnProds`): `columnSplit_of`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Protocol.Verifier.Defers Finset

/-! ## The chunks and the tables -/

/-- Every chunk's one-hot block lies inside the word. -/
def chunksInWord (w : ℕ) : Bool :=
  match Chunks.new w with
  | some c => (List.range c.d).all fun i ↦ decide (c.wordShifts.getD i 0 + 2 ^ c.widths.getD i 0 ≤ 64)
  | none => true

theorem chunksInWord_all : ∀ w < 25, chunksInWord w = true := by decide +kernel

theorem chunks_wordShift {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) {i : ℕ} (hi : i < c.d) :
    c.wordShifts.getD i 0 + 2 ^ c.widths.getD i 0 ≤ 64 := by
  have hw := (Wire.Chunks.new_le h).1
  have hc := (Wire.Chunks.new_le h).1
  have hw' : w ≤ 24 := by
    unfold Chunks.new at h
    split at h
    · rename_i hb; exact hb.2
    · cases h
  have := chunksInWord_all w (by omega)
  unfold chunksInWord at this
  rw [h] at this
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at this
  exact this i hi

theorem tables_shift_le : ∀ t < nTables, ∀ a ∈ (tables.getD t default).links.memory,
    a.shift ≤ tables.foldl (fun m t ↦ max m t.links.maxShift) 0 := by
  decide +kernel

theorem mem_memory_of_accessesAt {links : Links} {mu : List E} {p : ℕ} {am : Access × E}
    (h : am ∈ accessesAt links mu p) : am.1 ∈ links.memory :=
  (List.of_mem_zip (List.mem_filter.mp h).1).1

theorem mem_foldl_shifts (L : List (Access × E)) :
    ∀ (ss : List ℕ), (∀ s ∈ ss, s ∈ L.foldl (fun ss (a, _) ↦
        if a.shift = 0 ∨ ss.contains a.shift then ss else ss ++ [a.shift]) ss) ∧
      ∀ am ∈ L, am.1.shift ≠ 0 → am.1.shift ∈ L.foldl (fun ss (a, _) ↦
        if a.shift = 0 ∨ ss.contains a.shift then ss else ss ++ [a.shift]) ss := by
  induction L with
  | nil => intro ss; exact ⟨fun s hs ↦ hs, fun am h ↦ absurd h List.not_mem_nil⟩
  | cons am L ih =>
    intro ss
    obtain ⟨a, m⟩ := am
    have hstep : ∀ s ∈ ss, s ∈ (if a.shift = 0 ∨ ss.contains a.shift then ss else ss ++ [a.shift]) := by
      intro s hs; split <;> simp [hs]
    have hself : a.shift ≠ 0 → a.shift ∈ (if a.shift = 0 ∨ ss.contains a.shift then ss
        else ss ++ [a.shift]) := by
      intro h0
      split
      · rename_i hc
        rcases hc with hc | hc
        · exact absurd hc h0
        · simpa using hc
      · simp
    obtain ⟨ih1, ih2⟩ := ih (if a.shift = 0 ∨ ss.contains a.shift then ss else ss ++ [a.shift])
    refine ⟨fun s hs ↦ ih1 _ (hstep s hs), fun am ham h0 ↦ ?_⟩
    rcases List.mem_cons.mp ham with rfl | ham
    · exact ih1 _ (hself h0)
    · exact ih2 am ham h0

/-- A nonzero shift of a pointer column's accesses is among its shifts. -/
theorem mem_shiftsAt {links : Links} {mu : List E} {p : ℕ} {am : Access × E}
    (h : am ∈ accessesAt links mu p) (h0 : am.1.shift ≠ 0) : am.1.shift ∈ shiftsAt links mu p :=
  (mem_foldl_shifts _ []).2 am h h0

/-! ## The functionals' tables -/

/-- Every functional's table fits its chunk's block, inside the word. -/
def FunctionalsFit (chunks : Chunks) (f : Functionals) : Prop :=
  ∀ e ∈ f.tables, e.2.length ≤ 2 ^ chunks.widths.getD e.1 0 ∧
    chunks.wordShifts.getD e.1 0 + e.2.length ≤ 64

theorem length_part_le (chunks : Chunks) (r : List E) (i : ℕ) :
    (chunks.part r i).length ≤ chunks.widths.getD i 0 := by
  simp [Chunks.part]

theorem functionalsFit_new {w : ℕ} {chunks : Chunks} (h : Chunks.new w = some chunks) (r : List E)
    (maxShift : ℕ) : FunctionalsFit chunks (Functionals.new chunks r maxShift) := by
  have hd := one_le_d h
  have hk : ∀ i < chunks.d, (eqKernel (chunks.part r i)).length ≤ 2 ^ chunks.widths.getD i 0 ∧
      chunks.wordShifts.getD i 0 + (eqKernel (chunks.part r i)).length ≤ 64 := by
    intro i hi
    have h1 := chunks_wordShift h hi
    have h2 : (eqKernel (chunks.part r i)).length ≤ 2 ^ chunks.widths.getD i 0 := by
      rw [Protocol.Hotwire.eqKernel_length]
      exact Nat.pow_le_pow_right (by norm_num) (length_part_le chunks r i)
    exact ⟨h2, by omega⟩
  have hz : ∀ (n : ℕ) (f : ℕ → List E), (List.range n).zip ((List.range n).map f) =
      (List.range n).map fun i ↦ (i, f i) := by
    intro n f
    apply List.ext_getElem <;> simp
  have hhead : ((List.range chunks.d).map fun i ↦ eqKernel (chunks.part r i)).headD [] =
      eqKernel (chunks.part r 0) := by
    obtain ⟨d', hd'⟩ : ∃ d', chunks.d = d' + 1 := ⟨chunks.d - 1, by omega⟩
    rw [hd', List.range_succ_eq_map]
    simp
  intro e he
  simp only [Functionals.new, hz, List.mem_append, List.mem_map, List.mem_range] at he
  rcases he with (⟨i, hi, rfl⟩ | ⟨_, ⟨i, hi, rfl⟩, rfl⟩) | ⟨s, -, rfl⟩
  · exact hk i hi
  · simpa using hk i hi
  · rw [hhead]
    simpa [linkWindowShift] using hk 0 hd

theorem mleA_functional_getD (chunks : Chunks) (f : Functionals) (hfit : FunctionalsFit chunks f)
    (words : Array K) (pt : List E) (hw : words.size = 2 ^ pt.length) {j : ℕ}
    (hj : j < f.tables.length) :
    mleA (functionalTable chunks words (f.tables.getD j (0, []))) pt =
      (f.values chunks (columnSlices words pt)).getD j 0 := by
  have he : f.tables.getD j (0, []) ∈ f.tables := by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  obtain ⟨h1, h2⟩ := hfit _ he
  rw [show f.tables.getD j (0, []) = ((f.tables.getD j (0, [])).1, (f.tables.getD j (0, [])).2) from rfl,
    mleA_functionalTable chunks words pt hw _ _ h1 h2]
  simp [Functionals.values, List.getD_eq_getElem?_getD, hj]

theorem length_functionals_new (chunks : Chunks) (r : List E) (maxShift : ℕ) :
    (Functionals.new chunks r maxShift).tables.length = 2 * chunks.d + maxShift := by
  simp [Functionals.new]
  omega

/-! ## `rowPointerStep`'s tables -/

theorem rowPointerStep_toList (W : Witness) (inp : RowInputs) (t q₀ : ℕ)
    (acc : Array (Array E) × Array (E × Array ℕ) × ℕ) (pk : ℕ × ℕ) :
    ∃ A B : Array E, (rowPointerStep W inp t q₀ acc pk).1.toList = acc.1.toList ++ [A, B] ++
      ((List.range (2 * W.chunks.d)).map fun i ↦ functionalTable W.chunks
        ((W.tableCols t).getD pk.1 #[]) (inp.functionals.tables.getD i (0, []))) ++
      ((shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) pk.1).map fun s ↦
        functionalTable W.chunks ((W.tableCols t).getD pk.1 #[])
          (inp.functionals.tables.getD (2 * W.chunks.d + s - 1) (0, []))) := by
  obtain ⟨tabs, terms, pos⟩ := acc
  unfold rowPointerStep
  dsimp only
  simp only [Array.toList_append, List.append_assoc, List.cons_append, List.nil_append]
  exact ⟨_, _, rfl⟩

theorem rowPointerStep_pos (W : Witness) (inp : RowInputs) (t q₀ : ℕ)
    (acc : Array (Array E) × Array (E × Array ℕ) × ℕ) (pk : ℕ × ℕ) :
    (rowPointerStep W inp t q₀ acc pk).2.2 = acc.2.2 + 2 + 2 * W.chunks.d +
      (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) pk.1).length := by
  obtain ⟨tabs, terms, pos⟩ := acc
  rfl

theorem rowPointerStep_size (W : Witness) (inp : RowInputs) (t q₀ : ℕ)
    (acc : Array (Array E) × Array (E × Array ℕ) × ℕ) (pk : ℕ × ℕ) :
    (rowPointerStep W inp t q₀ acc pk).1.size = acc.1.size + 2 + 2 * W.chunks.d +
      (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) pk.1).length := by
  obtain ⟨A, B, h⟩ := rowPointerStep_toList W inp t q₀ acc pk
  rw [← Array.length_toList, h]
  simp
  omega

theorem foldl_rowPointerStep_prefix (W : Witness) (inp : RowInputs) (t q₀ : ℕ) :
    ∀ (L : List (ℕ × ℕ)) (acc : Array (Array E) × Array (E × Array ℕ) × ℕ),
      acc.1.toList <+: (L.foldl (rowPointerStep W inp t q₀) acc).1.toList
  | [], _ => List.prefix_refl _
  | pk :: L, acc => by
    rw [List.foldl_cons]
    refine List.IsPrefix.trans ?_ (foldl_rowPointerStep_prefix W inp t q₀ L _)
    obtain ⟨A, B, h⟩ := rowPointerStep_toList W inp t q₀ acc pk
    rw [h, List.append_assoc, List.append_assoc]
    exact List.prefix_append _ _

theorem getD_of_prefix {l1 l2 : List (Array E)} (h : l1 <+: l2) {i : ℕ} (hi : i < l1.length) :
    l2.getD i #[] = l1.getD i #[] := by
  obtain ⟨u, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

/-! ## A table's pointer columns, bound -/

section Couple

variable (W : Witness) (inp : RowInputs) (t q₀ : ℕ) (rt : RowTable) (chi : List E)
  (T : Array (Array E))

/-- The bound tables at a column's functional positions read its values. -/
theorem stepHyps
    (hat : ∀ f, rt.prods.at f = mleA (T.getD f #[]) (chi.take rt.height))
    (hfit : FunctionalsFit W.chunks inp.functionals)
    (hlen : inp.functionals.tables.length = 2 * W.chunks.d + inp.maxShift)
    (acc : Array (Array E) × Array (E × Array ℕ) × ℕ) (pk : ℕ × ℕ)
    (hS : ∀ am ∈ accessesAt (tables.getD t default).links (inp.ch.mu.getD t []) pk.1,
      am.1.shift ≤ inp.maxShift)
    (hw : ((W.tableCols t).getD pk.1 #[]).size = 2 ^ (chi.take rt.height).length)
    (hpos : acc.2.2 = acc.1.size)
    (hpre : (rowPointerStep W inp t q₀ acc pk).1.toList <+: T.toList) :
    (∀ j < 2 * W.chunks.d, rt.prods.at (acc.2.2 + 2 + j) =
      (inp.functionals.values W.chunks
        (columnSlices ((W.tableCols t).getD pk.1 #[]) (chi.take rt.height))).getD j 0) ∧
    (∀ am ∈ accessesAt (tables.getD t default).links (inp.ch.mu.getD t []) pk.1, am.1.shift ≠ 0 →
      rt.prods.at (acc.2.2 + 2 + 2 * W.chunks.d +
          (shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) pk.1).idxOf am.1.shift) =
        (inp.functionals.values W.chunks
          (columnSlices ((W.tableCols t).getD pk.1 #[]) (chi.take rt.height))).getD
          (2 * W.chunks.d + am.1.shift - 1) 0) := by
  obtain ⟨A, B, hst⟩ := rowPointerStep_toList W inp t q₀ acc pk
  rw [hst] at hpre
  set sh := shiftsAt (tables.getD t default).links (inp.ch.mu.getD t []) pk.1
  refine ⟨fun j hj ↦ ?_, fun am ham h0 ↦ ?_⟩
  · rw [hat, Keccak.getD_toList T, getD_of_prefix hpre (by simp; omega), hpos]
    rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp),
      show acc.1.size + 2 + j - (acc.1.toList ++ [A, B]).length = j by simp]
    rw [Keccak.getD_toList] at *
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
      Option.getD_some]
    rw [← List.getD_eq_getElem?_getD]
    exact mleA_functional_getD _ _ hfit _ _ hw (by omega)
  · have hmem := mem_shiftsAt ham h0
    have hidx : sh.idxOf am.1.shift < sh.length := List.idxOf_lt_length_of_mem hmem
    have hsh := hS am ham
    rw [hat, Keccak.getD_toList T, getD_of_prefix hpre (by simp; omega), hpos,
      List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
      List.length_range, Array.length_toList,
      show acc.1.size + 2 + 2 * W.chunks.d + sh.idxOf am.1.shift - (acc.1.size + (0 + 1 + 1) +
        2 * W.chunks.d) = sh.idxOf am.1.shift by omega]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hidx,
      Option.map_some, Option.getD_some, List.getElem_idxOf]
    rw [← List.getD_eq_getElem?_getD]
    exact mleA_functional_getD _ _ hfit _ _ hw (by omega)

/-- **A table's pointer columns, bound**: the terms the pointer-column fold adds, times the corner,
are the columns' parts. -/
theorem foldl_couple
    (hat : ∀ f, rt.prods.at f = mleA (T.getD f #[]) (chi.take rt.height))
    (hd : 1 ≤ W.chunks.d) (hfit : FunctionalsFit W.chunks inp.functionals)
    (hlen : inp.functionals.tables.length = 2 * W.chunks.d + inp.maxShift)
    (hS : ∀ p, ∀ am ∈ accessesAt (tables.getD t default).links (inp.ch.mu.getD t []) p,
      am.1.shift ≤ inp.maxShift) :
    ∀ (L : List (ℕ × ℕ)) (acc : Array (Array E) × Array (E × Array ℕ) × ℕ)
      (cacc : List ColumnAt × ℕ),
      (∀ pk ∈ L, ((W.tableCols t).getD pk.1 #[]).size = 2 ^ (chi.take rt.height).length) →
      acc.2.2 = acc.1.size → cacc.2 = acc.2.2 →
      (L.foldl (rowPointerStep W inp t q₀) acc).1.toList <+: T.toList →
      rt.corner * termsVal rt.prods.at (L.foldl (rowPointerStep W inp t q₀) acc).2.1 +
          (cacc.1.map (colTerm W.chunks.d inp.maxShift inp.functionals.mirrors)).sum =
        rt.corner * termsVal rt.prods.at acc.2.1 +
          ((L.foldl (columnStep W inp t q₀ rt chi) cacc).1.map
            (colTerm W.chunks.d inp.maxShift inp.functionals.mirrors)).sum
  | [], acc, cacc, _, _, _, _ => rfl
  | pk :: L, acc, cacc, hw, hpos, hc, hpre => by
    rw [List.foldl_cons] at hpre ⊢
    rw [List.foldl_cons]
    have hpre1 := (foldl_rowPointerStep_prefix W inp t q₀ L _).trans hpre
    obtain ⟨hD, hT⟩ := stepHyps W inp t q₀ rt chi T hat hfit hlen acc pk (hS pk.1)
      (hw pk List.mem_cons_self) hpos hpre1
    have step := corner_termsVal_rowPointerStep W inp t q₀ rt chi acc pk hd hD hT (hS pk.1)
    have ih := foldl_couple hat hd hfit hlen hS L (rowPointerStep W inp t q₀ acc pk)
      (columnStep W inp t q₀ rt chi cacc pk) (fun pk' h ↦ hw pk' (List.mem_cons_of_mem _ h))
      (by rw [rowPointerStep_pos, rowPointerStep_size, hpos])
      (by rw [rowPointerStep_pos, ← hc]; rfl) hpre
    have hcs : (columnStep W inp t q₀ rt chi cacc pk).1 =
        cacc.1 ++ [columnOf W inp t q₀ rt chi acc.2.2 pk.1 pk.2] := by
      rw [← hc]; rfl
    rw [hcs, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton] at ih
    linear_combination ih + step

end Couple

/-! ## A table's value, split -/

theorem foldl_push_prefix {α : Type} (f : Array (E × Array ℕ) → α → Array (E × Array ℕ))
    (hf : ∀ T x, ∃ Y, (f T x).toList = T.toList ++ Y) :
    ∀ (L : List α) (T : Array (E × Array ℕ)), ∃ Y, (L.foldl f T).toList = T.toList ++ Y
  | [], T => ⟨[], by simp⟩
  | x :: L, T => by
    obtain ⟨Y1, h1⟩ := hf T x
    obtain ⟨Y2, h2⟩ := foldl_push_prefix f hf L (f T x)
    exact ⟨Y1 ++ Y2, by rw [List.foldl_cons, h2, h1, List.append_assoc]⟩

theorem rowBaseStep_prefix (T : Array (E × Array ℕ)) (b : Block) :
    ∃ Y, (rowBaseStep T b).toList = T.toList ++ Y := by
  unfold rowBaseStep
  dsimp only
  exact foldl_push_prefix _ (fun T m ↦ by obtain ⟨v, c⟩ := m; exact ⟨_, Array.toList_push⟩) _ _

/-- A table's terms split at its column terms. -/
theorem termsVal_split (ev : ℕ → E) (A T : Array (E × Array ℕ)) (Y : List (E × Array ℕ))
    (h : T.toList = A.toList ++ Y) :
    termsVal ev T = termsVal ev A + termsVal ev (T.extract A.size T.size) := by
  have hl : T.size = A.size + Y.length := by rw [← Array.length_toList, h]; simp
  have hY : (T.extract A.size T.size).toList = Y := by
    simp [Array.toList_extract, h, hl]
  unfold termsVal
  rw [h, hY, List.map_append, List.sum_append]

theorem baseAt_eq (rt : RowTable) :
    baseAt rt = rt.corner * termsVal rt.prods.at
      (rt.prods.terms.extract rt.columnTerms rt.prods.terms.size) := by
  unfold baseAt
  rw [← termsVal_eq_foldl]

theorem rowStart_getD (W : Witness) (x : LinkProverPre) (chi : List E) {t : ℕ} (ht : t < nTables)
    (hh : W.layout.tableLogHeights.getD t 0 ≤ chi.length) :
    (chi.foldl rowFold (linkRowStart W x)).getD t default =
      { prods := (chi.take (W.layout.tableLogHeights.getD t 0)).foldl Prods.fold
          (rowProds W (linkRowInputs W x) t (pointerStarts.getD t 0)).1
        height := W.layout.tableLogHeights.getD t 0
        bound := W.layout.tableLogHeights.getD t 0
        corner := ((chi.drop (W.layout.tableLogHeights.getD t 0)).map (1 + ·)).prod
        columnTerms := (rowProds W (linkRowInputs W x) t (pointerStarts.getD t 0)).2 } := by
  unfold linkRowStart
  rw [foldl_rowFold_ofFn, Keccak.getD_ofFn' _ ht]
  rcases hrp : rowProds W (linkRowInputs W x) t (pointerStarts.getD t 0) with ⟨P0, ct⟩
  dsimp only
  rw [foldl_rowTableFold chi _ (Nat.zero_le _)]
  simp only [Nat.sub_zero, zero_add, one_mul, RowTable.mk.injEq, true_and]
  exact ⟨min_eq_left hh, trivial⟩

/-- **A table's part of the rows' claim, bound**: its pointer columns' parts and its base. -/
theorem rowPart_eq {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (x : LinkProverPre) (chi : List E)
    (hchi : chi.length = linkNRows W) {t : ℕ} (ht : t < nTables) :
    rowPart ((chi.foldl rowFold (linkRowStart W x)).getD t default) =
      ((columnsAt W (linkRowInputs W x) t (pointerStarts.getD t 0)
          ((chi.foldl rowFold (linkRowStart W x)).getD t default) chi).map
        (colTerm W.chunks.d (linkRowInputs W x).maxShift (linkRowInputs W x).functionals.mirrors)).sum +
        baseAt ((chi.foldl rowFold (linkRowStart W x)).getD t default) := by
  obtain ⟨-, hch, -, -⟩ := linkSizes hW
  have hd := one_le_d hch
  obtain ⟨hwid, hptr⟩ := tables_pointers t ht
  have hh : W.layout.tableLogHeights.getD t 0 ≤ chi.length := hchi ▸ le_foldl_max _ _
  set inp := linkRowInputs W x with hinp
  set st := chi.foldl rowFold (linkRowStart W x)
  have hrt := rowStart_getD W x chi ht hh
  set rt := st.getD t default
  set h := W.layout.tableLogHeights.getD t 0
  set r := (tables.getD t default).links.pointers.zipIdx.foldl
    (rowPointerStep W inp t (pointerStarts.getD t 0)) (rowInit W inp t) with hr
  have hrp := rowProds_eq W inp t (pointerStarts.getD t 0)
  rw [← hr] at hrp
  have hat : ∀ f, rt.prods.at f = mleA (r.1.getD f #[]) (chi.take rt.height) := by
    intro f
    rw [hrt, at_foldl, hrp]
  have hcouple := foldl_couple W inp t (pointerStarts.getD t 0) rt chi r.1 hat hd
    (functionalsFit_new hch _ _) (length_functionals_new _ _ _)
    (fun p am ham ↦ tables_shift_le t ht _ (mem_memory_of_accessesAt ham))
    (tables.getD t default).links.pointers.zipIdx (rowInit W inp t) ([], 3 + (tables.getD t default).width)
    (fun pk hpk ↦ by
      rw [hrt, List.length_take, min_eq_left hh]
      exact size_tableCols_getD hW ht (hwid ▸ hptr _ (List.fst_mem_of_mem_zipIdx hpk)))
    (by simp [rowInit]; omega) rfl (List.prefix_refl _)
  rw [← hr] at hcouple
  have hinit : termsVal rt.prods.at (rowInit W inp t).2.1 = 0 := by simp [rowInit, termsVal]
  rw [hinit, mul_zero, zero_add, List.map_nil, List.sum_nil, add_zero, ← columnsAt_eq] at hcouple
  obtain ⟨Y, hY⟩ := foldl_push_prefix rowBaseStep rowBaseStep_prefix
    (tableBlocks inp.ch t inp.eq0 (some inp.jump)) r.2.1
  have hterms : rt.prods.terms = (tableBlocks inp.ch t inp.eq0 (some inp.jump)).foldl rowBaseStep r.2.1 := by
    rw [hrt]; simp only; rw [foldl_fold_terms, hrp]
  have hct : rt.columnTerms = r.2.1.size := by rw [hrt]; simp only; rw [hrp]
  rw [baseAt_eq]
  unfold rowPart
  rw [show rt.height - rt.bound = 0 by rw [hrt]; simp, pow_zero, ← value_eq_cubeSum_one,
    value_eq_termsVal, hct, hterms, termsVal_split _ _ _ _ hY, mul_add, hcouple]

/-! ## The split -/

theorem sum_toList_map {α : Type} [Inhabited α] (a : Array α) (f : α → E) :
    (a.toList.map f).sum = ((List.range a.size).map fun i ↦ f (a.getD i default)).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [Array.getD_eq_getD_getElem?, show i < a.size by simpa using h1]

theorem sum_map_flatMap {α β : Type} (g : α → List β) (f : β → E) :
    ∀ L : List α, ((L.flatMap g).map f).sum = (L.map fun t ↦ ((g t).map f).sum).sum
  | [] => rfl
  | t :: L => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_map_flatMap g f L, List.map_cons,
      List.sum_cons]

/-- **`ColumnSplit` on the honest witness**: after the row rounds, the rows' claim is the pointer
columns' cube sum. -/
theorem columnSplit_of {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    {W : Witness} (hA : Admitted prog input t ρ W) : ColumnSplit W := by
  have hW := hA.witness
  obtain ⟨-, hch, -, -⟩ := linkSizes hW
  have hd := one_le_d hch
  intro y x hp chi hchi
  dsimp only
  set st := chi.foldl rowFold (linkRowStart W x) with hst
  have hsize : st.size = nTables := by
    rw [hst]; unfold linkRowStart; rw [foldl_rowFold_ofFn, Array.size_ofFn]
  unfold rowClaim linkColumnProds
  rw [cubeSum_columnProds _ _ hd _ _ _ _ ((log2Ceil_le_iff _ _).mp le_rfl), sum_toList_map, hsize]
  rw [List.map_congr_left fun u hu ↦ rowPart_eq hW x chi hchi (List.mem_range.mp hu),
    List.sum_map_add]
  unfold linkColumns linkBase
  rw [sum_map_flatMap, LeanVM.Prover.Complete.sumE_eq_sum]
  rfl

end LeanVM.Prover.Complete

end
