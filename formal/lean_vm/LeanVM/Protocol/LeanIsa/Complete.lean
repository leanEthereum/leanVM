/-
  LeanVM.Protocol.LeanIsa.Complete

  The adaptor's completeness direction: a witness satisfying leanISA's constraint system stacks
  into a column satisfying the leanISA instance's relation, and is read back off it.
-/

module

public import LeanVM.Protocol.LeanIsa.Sound
public import LeanVM.Protocol.ToArkLib.Refinement
import LeanVM.Arithmetization.Completeness.Satisfied

/-!
# The adaptor, completeness

`m3Holds_stackOf`: a witness `w` satisfying `SatisfiedBy prog input w` stacks, at the sizes it
carries (`Sizes.ofWitness`, which `sizes_of_satisfiedBy` shows it has), into a column satisfying
`M3Holds` of the leanISA instance; `m3Honest_stackOf` adds that every padding row of the stack
holds its table's public padding row (`paddingHonest_stackOf`), the relation the protocol's
completeness starts from. `witnessOf_stackOf`: reading a witness back off that stack
gives `w`'s opcode tables within their widths, its two blocks, its public input and its image.

The stack agrees with the witness (`agrees_stackOf`): its committed columns are the witness's
cells (`column_stackOf`), and its limb columns are the cells the honest Flock column carries at
the specification's slots (`column_limb_stackOf`), which are the witness's limbs by
`FlockSpec.slots_gen`, since every `BLAKE2S` row compresses (`limbsCompress_of_satisfiedBy`).
Past a table's rows the stack holds the padding row (`paddingHonest_stackOf`): zero committed
cells, and at a padding block of the Flock region Flock's padding instance, which compresses
(`padLimbs_compress`, checked in the kernel). Then the bus and count clauses follow from the
equivalences of `LeanIsa/Relation.lean`, the constraint clause from them on the executed rows and
from the padding row on the others (`padRow_constraints`); the public lines from the two public words of the image
(`image_words`), which the seed rows put in the memory columns (`memLimb_stackOf`); and the Flock
clause from `FlockSpec.holds_gen`, the region being the honest column of the limbs
(`flockColumn_stackOf`).

`leanIsaRefinement` packages the soundness direction as the spine's `Refinement` from `M3Rel` to
`SatisfiedBy`, the witness map the knowledge transport needs.

A witness's rows may carry cells past their component's width, which no constraint reads and
the stack drops: the read-back is cell for cell within the width.
-/

namespace LeanVM.Protocol.LeanIsa

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization CompPoly CMlPolynomialEval
open Air.Flat (Component EnsembleWitness)

@[expose] public section

variable (F : FlockSpec) (prog : Program) (s : Sizes) (w : EnsembleWitness (leanIsaEnsemble prog))

/-! ## Reading the stack of a witness -/

/-- A cell of a stack inside a block's window is the block's cell. -/
private theorem stackColumn_get (t : (blocks prog s).Tables K) (b : Fin (blocks prog s).n)
    (x : Fin (2 ^ (blocks prog s).size b)) :
    ((blocks prog s).stackColumn t (leanIsaμ prog s)).values[x.val + (blocks prog s).offset b]'(by
      have := (blocks prog s).offset_add_pow_le_total b
      have := blocks_fits prog s
      have := x.isLt
      omega) = (t b)[x] := by
  rw [← (blocks prog s).unstack_getElem (blocks_fits prog s) _ b x.isLt]
  exact congrArg (·[x]) ((blocks prog s).unstack_stackAt t (blocks_fits prog s) 0 b)

/-- A witness's column, transported along an equality of columns. -/
private theorem witnessColumn_congr {c c' : Col} (h : c' = c) (x : Fin (2 ^ kappa prog s c')) :
    (witnessColumn F prog s w c')[x] =
      (witnessColumn F prog s w c)[(Fin.cast (by rw [h]) x : Fin (2 ^ kappa prog s c))] := by
  subst h
  rfl

/-- A committed column of the stack of a witness is the witness's column. -/
theorem column_stackOf (c : Col) (h : ¬ IsLimb c) (x : Fin (2 ^ kappa prog s c)) :
    ((leanIsaInstance F prog s).column (stackOf F prog s w) c).values.get x =
      (witnessColumn F prog s w c)[x] := by
  refine (column_committed F prog s _ c h x).trans ?_
  have hsz := size_blockOf prog s c h
  have hx : x.val < 2 ^ (blocks prog s).size (blockOf c h) := by rw [hsz]; exact x.isLt
  refine (stackColumn_get prog s _ (blockOf c h) ⟨x.val, hx⟩).trans ?_
  exact witnessColumn_congr F prog s w (stackOrder_blockOf prog s c h) _

/-- Limb `k` of row `x` of the stack of a witness is the limb the honest Flock column carries at
slot `k` of block `x`. -/
theorem column_limb_stackOf (k : Fin 18) (x : Fin (2 ^ s.τ 5)) :
    ((leanIsaInstance F prog s).column (stackOf F prog s w) (limbCol k)).values.get x =
      slotLimbs F.slot (F.gen (blake2sLimbs prog s w)) x k :=
  (column_limb F prog s _ k x).trans
    ((column_committed F prog s _ flockCol not_isLimb_flockCol (cubeIndex (F.slot k) x)).symm.trans
      (column_stackOf F prog s w flockCol not_isLimb_flockCol (cubeIndex (F.slot k) x)))

/-- A raw `BLAKE2S` row is a compression exactly when its limbs, cells `9 … 26`, are. -/
private theorem blake2sRelation_array (row : Array K) (data : ProverData K) :
    Blake2sRelation (valueFromOffset Blake2sRow 0 (Environment.fromArray row data)) ↔
      LimbsCompress fun k ↦ row[9 + (k : ℕ)]?.getD 0 := by
  unfold Blake2sRelation LimbsCompress
  simp [valueFromOffset, explicit_provable_type, circuit_norm]

/-! ## Rows of the two blocks -/

/-- The cells of a memory-block row: the finalize count at `1`, the limbs at `2, 3, 4`. -/
private theorem memRow_cells (idx cnt : K) (m : Vector K 3) :
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[1]?.getD 0 = cnt ∧
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[2]?.getD 0 = m[0] ∧
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[3]?.getD 0 = m[1] ∧
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[4]?.getD 0 = m[2] := by
  simp [explicit_provable_type, ProvableStruct.componentsToElements, ProvableStruct.toComponents,
    toComponents, circuit_norm]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Vector.getElem_append] <;> simp <;>
    rw [Vector.getElem_append] <;> simp

/-- Cell `memRowCell k` of a memory-block row is its column `k`: a limb, or the finalize count. -/
private theorem memRow_cell (idx cnt : K) (m : Vector K 3) (k : Fin 4) :
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[memRowCell k]?.getD 0 =
      ![m[0], m[1], m[2], cnt] k := by
  obtain ⟨c1, c2, c3, c4⟩ := memRow_cells idx cnt m
  fin_cases k
  exacts [c2, c3, c4, c1]

/-- The finalize count of a bytecode-block row is its cell `1`. -/
private theorem bytecodeRow_cell (i : Fin (2 ^ prog.logSize)) (c : K) :
    (toElements (bytecodeRowOf prog i c)).toArray[1]?.getD 0 = c := by
  simp [bytecodeRowOf, explicit_provable_type, ProvableStruct.componentsToElements,
    ProvableStruct.toComponents, toComponents, circuit_norm]
  rw [Vector.getElem_append]
  simp
  rw [Vector.getElem_append]
  simp

/-! ## The sizes of a witness -/

variable {F prog s w}

/-- The sizes a witness carries: its memory size and its tables' row counts. -/
def witnessSizes (w : EnsembleWitness (leanIsaEnsemble prog)) (h : 0 < (imageOf w.data).1) :
    Sizes :=
  ⟨(imageOf w.data).1, h, fun j ↦ (opTable w j).table.length⟩

/-- `Sizes.ofWitness` returns the sizes the witness carries. -/
theorem eq_of_ofWitness (hs : Sizes.ofWitness w = some s) :
    ∃ h, s = witnessSizes w h := by
  unfold Sizes.ofWitness at hs
  split_ifs at hs with h
  exact ⟨h, (Option.some.inj hs).symm⟩

/-- A witness satisfying the constraint system has its sizes. -/
theorem sizes_of_satisfiedBy {input : PublicInput} (h : SatisfiedBy prog input w) :
    ∃ s, Sizes.ofWitness w = some s := by
  unfold Sizes.ofWitness
  have hp : 0 < (imageOf w.data).1 := lt_of_lt_of_le (by decide) h.caps.minLogMem_le
  simp only [hp, dite_true]
  exact ⟨_, rfl⟩

/-! ## The stack of a witness agrees with it -/

/-- A cell of a table, as a row's cell. -/
private theorem cellOf_eq (t : Air.Flat.Table K) {x : ℕ} (hx : x < t.table.length) (i : ℕ) :
    cellOf t x i = (t.table[x]'hx)[i]?.getD 0 := by
  rw [cellOf, List.getElem?_eq_getElem hx]
  rfl

/-- Every executed `BLAKE2S` row of a witness satisfying the constraint system has compressing
limbs. -/
theorem limbsCompress_of_satisfiedBy {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) (x : Fin (2 ^ s.τ 5)) (hx : x.val < s.rows 5) :
    LimbsCompress (blake2sLimbs prog s w)[x] := by
  obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
  have hx' : x.val < (tableAt w 5).table.length := hx
  have hv := h.blake2s_valid _ (List.getElem_mem hx')
  rw [blake2sRowAt, blake2sRelation_array] at hv
  have hl : (blake2sLimbs prog _ w)[x] = fun k : Fin 18 ↦ cellOf (tableAt w 5) x (9 + k) := by
    refine (Vector.getElem_ofFn _).trans (funext fun k ↦ ?_)
    simp only [hx, ↓reduceIte]
  rw [hl]
  simp only [cellOf_eq _ hx']
  exact hv

/-- Within its width, an opcode table of a witness satisfying the constraint system is the
stack's executed rows. -/
private theorem cells_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) (j : Fin 6) (x : Fin ((witnessSizes w hp).rows j))
    (i : Fin (opcodeComponent j).width) :
    cellOf (opTable w j) x i =
      (leanIsaInstance F prog (witnessSizes w hp)).row
        (stackOf F prog (witnessSizes w hp) w) (opIdx j)
          (Fin.castLE ((witnessSizes w hp).rows_le j) x) i := by
  have hs : Sizes.ofWitness w = some (witnessSizes w hp) := by
    unfold Sizes.ofWitness
    simp only [hp, dite_true]
    rfl
  by_cases hl : IsLimb ⟨opIdx j, i⟩
  · have hj : j = 5 := Fin.ext (by have := congrArg Fin.val hl.1; simp [opIdx] at this; omega)
    subst hj
    have h1 : 9 ≤ i.val := hl.2.1
    have h2 : i.val < 27 := hl.2.2
    have hk : i.val - 9 < 18 := by omega
    have hi : i = ⟨9 + (i.val - 9), by rw [Nat.add_sub_cancel' h1]; exact i.isLt⟩ :=
      Fin.ext (by simp only; omega)
    have hx : (Fin.castLE ((witnessSizes w hp).rows_le 5) x).val < (witnessSizes w hp).rows 5 :=
      x.isLt
    rw [hi]
    refine Eq.symm ((column_limb_stackOf F prog _ w ⟨i.val - 9, hk⟩ _).trans ?_)
    refine (congrFun (F.slots_gen _ _ (limbsCompress_of_satisfiedBy h hs _ hx)) _).trans ?_
    refine (congrFun (Vector.getElem_ofFn _) _).trans ?_
    simp only [hx, ↓reduceIte]
    rfl
  · refine Eq.symm ((column_stackOf F prog _ w ⟨opIdx j, i⟩ hl _).trans ?_)
    exact Vector.getElem_ofFn _

/-- The memory block of a witness satisfying the constraint system is the stack's. -/
private theorem memRows_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) :
    memBlockRows w = memBlockRowsOf F prog (witnessSizes w hp)
      (stackOf F prog (witnessSizes w hp) w) := by
  obtain ⟨idx, cnt, hrows⟩ := h.seed_rows
  have hlen : (memBlockRows w).length = 2 ^ (imageOf w.data).1 := by
    rw [hrows, List.length_ofFn]
  have hrow : ∀ x : Fin (2 ^ (imageOf w.data).1),
      (memBlockRows w)[x.val]'(by rw [hlen]; exact x.isLt) =
        (toElements (⟨idx x, cnt x, #v[((imageOf w.data).2 x).limb 0,
          ((imageOf w.data).2 x).limb 1, ((imageOf w.data).2 x).limb 2]⟩ : MemRow K)).toArray :=
    fun x ↦ by simp only [hrows, List.getElem_ofFn]
  have hidx : ∀ x : Fin (2 ^ (imageOf w.data).1), idx x = gpow x := fun x ↦ by
    have := h.index_columns x.val (by rw [hlen]; exact x.isLt)
    rw [hrow, memRowAt_toElements] at this
    exact this
  have hcell : ∀ (k : Fin 4) (x : Fin (2 ^ (imageOf w.data).1)),
      cell F prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) (memCol k) x =
        ((memBlockRows w)[x.val]'(by rw [hlen]; exact x.isLt))[memRowCell k]?.getD 0 :=
    fun k x ↦ (column_stackOf F prog (witnessSizes w hp) w (memCol k) (fun hk ↦ by
      have := congrArg Fin.val hk.1; simp [memCol, opIdx] at this) x).trans
        ((Vector.getElem_ofFn _).trans (cellOf_eq _ _ _))
  rw [hrows, memBlockRowsOf]
  refine congrArg List.ofFn (funext fun x ↦ ?_)
  simp only [hcell, hrow x, hidx x, memRow_cell]
  rfl

/-- The bytecode block of a witness satisfying the constraint system is the stack's. -/
private theorem bytecodeRows_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) :
    bytecodeBlockRows w = bytecodeBlockRowsOf F prog (witnessSizes w hp)
      (stackOf F prog (witnessSizes w hp) w) := by
  obtain ⟨cntFin, hrows⟩ := h.bytecode_rows
  have hlen : (bytecodeBlockRows w).length = 2 ^ prog.logSize := by
    rw [hrows, List.length_ofFn]
  have hrow : ∀ i : Fin (2 ^ prog.logSize),
      (bytecodeBlockRows w)[i.val]'(by rw [hlen]; exact i.isLt) =
        (toElements (bytecodeRowOf prog i (cntFin i))).toArray :=
    fun i ↦ by simp only [hrows, List.getElem_ofFn]
  have hcell : ∀ i : Fin (2 ^ prog.logSize),
      cell F prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) bfcntCol i =
        ((bytecodeBlockRows w)[i.val]'(by rw [hlen]; exact i.isLt))[1]?.getD 0 :=
    fun i ↦ (column_stackOf F prog (witnessSizes w hp) w bfcntCol (by decide) i).trans
      ((Vector.getElem_ofFn _).trans (cellOf_eq _ _ _))
  rw [hrows, bytecodeBlockRowsOf]
  refine congrArg List.ofFn (funext fun i ↦ ?_)
  simp only [hcell, hrow i, bytecodeRow_cell]

/-- The stack of a witness satisfying the constraint system agrees with it. -/
theorem agrees_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) : Agrees F s (stackOf F prog s w) w := by
  obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
  exact ⟨fun j ↦ rfl, cells_stackOf h hp, memRows_stackOf h hp, bytecodeRows_stackOf h hp⟩

/-! ## The relation of the stack -/

/-- A limb column of the memory on the stack of a witness satisfying the constraint system is
that limb of the image the data names. -/
private theorem memLimb_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) (k : Fin 3) (x : Fin (2 ^ (imageOf w.data).1)) :
    cell F prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) (memCol k.castSucc) x =
      ((imageOf w.data).2 x).limb k := by
  obtain ⟨idx, cnt, hrows⟩ := h.seed_rows
  have hlen : (memBlockRows w).length = 2 ^ (imageOf w.data).1 := by
    rw [hrows, List.length_ofFn]
  refine (column_stackOf F prog (witnessSizes w hp) w (memCol k.castSucc) (fun hk ↦ by
    have := congrArg Fin.val hk.1; simp [memCol, opIdx] at this) x).trans
      ((Vector.getElem_ofFn _).trans ((cellOf_eq _ (by rw [hlen]; exact x.isLt) _).trans ?_))
  have hrow : (memBlockRows w)[x.val]'(by rw [hlen]; exact x.isLt) =
      (toElements (⟨idx x, cnt x, #v[((imageOf w.data).2 x).limb 0,
        ((imageOf w.data).2 x).limb 1, ((imageOf w.data).2 x).limb 2]⟩ : MemRow K)).toArray := by
    simp only [hrows, List.getElem_ofFn]
  simp only [hrow, memRow_cell]
  fin_cases k <;> rfl

/-- The image a witness satisfying the constraint system names holds the public words at
`g^0` and `g^1`. -/
private theorem image_words {input : PublicInput} (h : SatisfiedBy prog input w)
    (h0 : 0 < 2 ^ (imageOf w.data).1) (h1 : 1 < 2 ^ (imageOf w.data).1) :
    (imageOf w.data).2 ⟨0, h0⟩ = input.word0 ∧ (imageOf w.data).2 ⟨1, h1⟩ = input.word1 := by
  have hκ : (imageOf w.data).1 < 64 := lt_of_le_of_lt h.caps.le_maxLogMem (by decide)
  have e0 := (MemImage.read_gpow hκ (imageOf w.data).2 ⟨0, h0⟩).symm.trans h.word0_eq
  have e1 := (MemImage.read_gpow hκ (imageOf w.data).2 ⟨1, h1⟩).symm.trans h.word1_eq
  exact ⟨Option.some.inj e0, Option.some.inj e1⟩

/-- The Flock region of the stack of a witness is the honest column of its `BLAKE2S` limbs. -/
private theorem flockColumn_stackOf :
    (leanIsaInstance F prog s).flockColumn (flockRegion prog s F) (stackOf F prog s w) =
      F.gen (blake2sLimbs prog s w) := by
  suffices hv : ((leanIsaInstance F prog s).flockColumn (flockRegion prog s F)
      (stackOf F prog s w)).values = (F.gen (blake2sLimbs prog s w)).values by
    revert hv
    generalize F.gen (blake2sLimbs prog s w) = c
    intro hv
    cases c
    exact congrArg Column.mk hv
  refine Vector.ext fun y hy ↦ ?_
  simp only [M3Instance.flockColumn, Vector.getElem_cast]
  exact column_stackOf F prog s w flockCol not_isLimb_flockCol ⟨y, hy⟩

/-- The stack of a witness satisfying the constraint system holds the public lines: its memory
columns' first two cells are the public words' limbs. -/
private theorem publicLinesHold_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) :
    (leanIsaInstance F prog s).PublicLinesHold input (stackOf F prog s w) := by
  obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
  have h0 : 0 < 2 ^ (imageOf w.data).1 := Nat.two_pow_pos _
  have h1 : 1 < 2 ^ (imageOf w.data).1 := Nat.one_lt_two_pow hp.ne'
  obtain ⟨w0, w1⟩ := image_words h h0 h1
  have hl : ∀ k : Fin 3,
      cell F prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) (memCol k.castSucc)
        ⟨0, h0⟩ = input.word0.limb k ∧
      cell F prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) (memCol k.castSucc)
        ⟨1, h1⟩ = input.word1.limb k := fun k ↦
    ⟨(memLimb_stackOf h hp k _).trans (congrArg (·.limb k) w0),
      (memLimb_stackOf h hp k _).trans (congrArg (·.limb k) w1)⟩
  intro l hl'
  have hls : (publicLines prog (witnessSizes w hp) input).toList =
      [⟨memCol 0, input.lanes 0, input.lanes 2, false, hp⟩,
        ⟨memCol 1, input.lanes 1, input.lanes 3, false, hp⟩, ⟨memCol 2, 0, 0, false, hp⟩] := rfl
  change l ∈ (publicLines prog (witnessSizes w hp) input).toList at hl'
  rw [hls] at hl'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
  rcases hl' with rfl | rfl | rfl
  · exact ⟨(hl 0).1.trans (by simp [PublicInput.word0]),
      (hl 0).2.trans (by simp [PublicInput.word1])⟩
  · exact ⟨(hl 1).1.trans (by simp [PublicInput.word0]),
      (hl 1).2.trans (by simp [PublicInput.word1])⟩
  · exact ⟨(hl 2).1.trans (by simp [PublicInput.word0]),
      (hl 2).2.trans (by simp [PublicInput.word1])⟩

/-! ## Honest padding -/

/-- The limbs a padding row of the `BLAKE2S` table holds (`padRow`): Flock's padding instance. -/
def padLimbs : Fin 18 → K := fun k ↦ padRow (opIdx 5) ⟨9 + k, by rw [width_blake2s]; omega⟩

/-- Flock's padding instance is a compression, of BLAKE2s-256 of `64` zero bytes: checked in the
kernel. -/
theorem padLimbs_compress : LimbsCompress padLimbs := by
  decide +kernel

/-- The padding row is zero off the `BLAKE2S` limbs. -/
theorem padRow_of_not_isLimb :
    ∀ (j : Fin 6) (i : Fin (width (opIdx j))), ¬ IsLimb ⟨opIdx j, i⟩ → padRow (opIdx j) i = 0 := by
  decide +kernel

/-- **The padding is honest.** On the stack of any witness, at the sizes it carries, every padding row holds its table's public padding row: the committed cells are
zero past the table's rows, and the limbs the Flock region carries at a padding block are the
padding instance, when it compresses. -/
theorem paddingHonest_stackOf (hs : Sizes.ofWitness w = some s)
    (hpad : LimbsCompress padLimbs) :
    (leanIsaInstance F prog s).PaddingHonest (stackOf F prog s w) := by
  obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
  rintro ⟨j, hj⟩ x hx
  funext i
  have h9 : j < 9 := hj
  match j, hj, h9, x, hx, i with
  | 0, _, _, x, hx, _ => exact absurd (lt_of_lt_of_le x.isLt hx) (lt_irrefl _)
  | 1, _, _, x, hx, _ => exact absurd (lt_of_lt_of_le x.isLt hx) (lt_irrefl _)
  | 2, _, _, x, hx, _ => exact absurd (lt_of_lt_of_le x.isLt hx) (lt_irrefl _)
  | j + 3, hj, h9, x, hx, i =>
    have hrows : (opTable w ⟨j, by omega⟩).table.length ≤ x.val := hx
    by_cases hl : IsLimb ⟨⟨j + 3, hj⟩, i⟩
    · have hj5 : j = 5 := by have := congrArg Fin.val hl.1; simp [opIdx] at this; omega
      subst hj5
      have h1 : 9 ≤ i.val := hl.2.1
      have h2 : i.val < 27 := hl.2.2
      have hw : (leanIsaInstance F prog (witnessSizes w hp)).width ⟨5 + 3, hj⟩ = 37 :=
        width_blake2s
      obtain ⟨k, rfl⟩ : ∃ k : Fin 18,
          i = ⟨9 + k.val, by clear hl h1 h2; have := k.isLt; rw [hw]; omega⟩ :=
        ⟨⟨i.val - 9, by omega⟩, Fin.ext (by simp only; omega)⟩
      let x' : Fin (2 ^ (witnessSizes w hp).τ 5) := x
      have hx' : (witnessSizes w hp).rows 5 ≤ x'.val := hx
      have hrow : (blake2sLimbs prog (witnessSizes w hp) w)[x'] = padLimbs := by
        refine (Vector.getElem_ofFn _).trans (funext fun k ↦ ?_)
        simp only [padLimbs, show ¬ x'.val < (witnessSizes w hp).rows 5 from Nat.not_lt.mpr hx',
          ↓reduceIte]
      refine (column_limb_stackOf F prog (witnessSizes w hp) w k x').trans ?_
      refine (congrFun (F.slots_gen _ x' (hrow ▸ hpad)) k).trans ?_
      exact congrFun hrow k
    · refine (column_stackOf F prog (witnessSizes w hp) w ⟨⟨j + 3, hj⟩, i⟩ hl x).trans ?_
      refine Eq.trans ?_ (padRow_of_not_isLimb ⟨j, by omega⟩ i hl).symm
      refine (Vector.getElem_ofFn _).trans ?_
      simp [cellOf, List.getElem?_eq_none hrows]

/-- The constraint polynomials of the opcode tables but `JUMP` are none. -/
theorem opcode_constraints_nil :
    ∀ j : Fin 6, j ≠ 4 → (opcodeTable j).constraints.length = 0 := by
  decide +kernel

/-- The zero row of the `JUMP` table. -/
private def jumpZeroRow : JumpRow K := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The zero row with zero local witnesses is fourteen zeros. -/
private theorem jumpRaw_zero : jumpRaw jumpZeroRow 0 0 = Array.replicate 14 0 := by
  simp [jumpRaw, rawRow, jumpZeroRow, explicit_provable_type,
    ProvableStruct.componentsToElements, ProvableStruct.toComponents, toComponents, circuit_norm]
  rfl

/-- The `JUMP` table has fourteen columns. -/
private theorem width_jump : (opcodeComponent 4).width = 14 := by decide +kernel

/-- `JUMP`'s constraint polynomials vanish at the zero row: `b + v_cond · w` and
`v_cond · (b + 1)` at zero. -/
theorem jump_constraints_zero :
    ∀ C ∈ (opcodeTable 4).constraints, C.eval (fun _ ↦ (0 : K)) = 0 := by
  have hl := List.isEmpty_iff.mp (opcode_lookups 4)
  refine (toM3_constraints_iff (opcodeComponent 4) channelSep channelDir counted hl (fun _ ↦ 0)
    (fun _ _ ↦ #[])).mpr ?_
  have he : (Array.ofFn fun _ : Fin (opcodeComponent 4).width ↦ (0 : K)) =
      jumpRaw jumpZeroRow 0 0 := by
    rw [jumpRaw_zero]
    exact Array.ext (by simp [width_jump]) (fun i _ _ ↦ by simp)
  rw [he]
  exact jumpRaw_constraints jumpZeroRow 0 0 (by simp [jumpZeroRow]) (by simp [jumpZeroRow]) _

/-- Every opcode table's constraints vanish at its padding row: zero but for the `BLAKE2S` limbs,
a table without constraints. -/
theorem padRow_constraints (j : Fin 6) :
    ∀ C ∈ (opcodeTable j).constraints, C.eval (padRow (opIdx j)) = 0 := by
  by_cases h4 : j = 4
  · subst h4
    have hz : padRow (opIdx 4) = fun _ ↦ 0 := funext fun i ↦
      padRow_of_not_isLimb 4 i fun hi ↦ by have := congrArg Fin.val hi.1; simp [opIdx] at this
    rw [hz]
    exact jump_constraints_zero
  · intro C hC
    exact absurd (List.length_pos_of_mem hC) (by rw [opcode_constraints_nil j h4]; omega)

/-- **The adaptor, completeness.** A witness satisfying leanISA's constraint system on the input
stacks, at the sizes it carries, into a column satisfying the leanISA instance's relation, given
that Flock's padding instance compresses (`padLimbs_compress`): the executed rows are the
witness's, the padding rows its tables' padding rows. -/
theorem m3Holds_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) (hpad : LimbsCompress padLimbs) :
    M3Holds (leanIsaInstance F prog s) input (stackOf F prog s w) := by
  have hA := agrees_stackOf (F := F) h hs
  have hP := paddingHonest_stackOf (F := F) hs hpad
  refine ⟨?_, (balanced_iff_pairs hA).mpr fun k ↦ ?_, (countsNonzero_iff hA).mp h.counts_nonzero,
    ?_, ?_⟩
  · intro j' C hC x
    rcases j' with ⟨_ | _ | _ | j, hj⟩
    · exact absurd hC List.not_mem_nil
    · exact absurd hC List.not_mem_nil
    · exact absurd hC List.not_mem_nil
    · have h9 : (leanIsaInstance F prog s).ntab = 9 := rfl
      by_cases hx : x.val < s.rows ⟨j, by omega⟩
      · have hmem : opTable w ⟨j, by omega⟩ ∈ w.allTables :=
          EnsembleWitness.mem_allTables_of_mem_tables _ (mem_tables_iff.mpr ⟨⟨j, by omega⟩, rfl⟩)
        exact (opcode_constraints_iff hA ⟨j, by omega⟩).mp (h.constraints _ hmem) ⟨x.val, hx⟩ C hC
      · rw [hP ⟨j + 3, hj⟩ x (Nat.not_lt.mp hx)]
        exact padRow_constraints ⟨j, by omega⟩ C hC
  · fin_cases k
    exacts [h.state_balanced, h.mem_balanced, h.bytecode_balanced]
  · exact publicLinesHold_stackOf h hs
  · intro r hr
    obtain rfl := Option.mem_def.mp hr |> Option.some.inj |>.symm
    rw [flockColumn_stackOf]
    exact F.region_holds_gen _ rfl rfl _

/-- **The adaptor, completeness, with honest padding.** A witness satisfying leanISA's constraint
system stacks, at the sizes it carries, into a column satisfying the leanISA instance's relation
whose padding rows hold the public padding row, the relation the protocol's completeness starts
from. -/
theorem m3Honest_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) (hpad : LimbsCompress padLimbs) :
    M3Honest (leanIsaInstance F prog s) input (stackOf F prog s w) :=
  ⟨m3Holds_stackOf h hs hpad, paddingHonest_stackOf (F := F) hs hpad⟩

/-- **The witness read back.** Reading a witness back off the stack of a witness satisfying the
constraint system gives the witness's opcode tables within their widths, its memory and bytecode
blocks, its public input and the image its data names. -/
theorem witnessOf_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) :
    (∀ (j : Fin 6) (x : Fin (s.rows j)) (i : Fin (opcodeComponent j).width),
      cellOf (opTable (witnessOf F prog s (stackOf F prog s w)) j) x i = cellOf (opTable w j) x i) ∧
    memBlockRows (witnessOf F prog s (stackOf F prog s w)) = memBlockRows w ∧
    bytecodeBlockRows (witnessOf F prog s (stackOf F prog s w)) = bytecodeBlockRows w ∧
    (witnessOf F prog s (stackOf F prog s w)).publicInput = w.publicInput ∧
    imageOf (witnessOf F prog s (stackOf F prog s w)).data = imageOf w.data := by
  have hA := agrees_stackOf (F := F) h hs
  have hB := agrees_witnessOf F prog s (stackOf F prog s w)
  refine ⟨fun j x i ↦ (hB.cells j x i).trans (hA.cells j x i).symm,
    hB.memRows.trans hA.memRows.symm, hB.bytecodeRows.trans hA.bytecodeRows.symm, ?_, ?_⟩
  · obtain ⟨c00, c01, c10, c11, -, -⟩ := publicLines_cells F prog s _ (publicLinesHold_stackOf h hs)
    show publicInputOf F prog s (stackOf F prog s w) = _
    rw [h.public_input_eq, publicInputOf, PublicIO.ofInput, c00, c01, c10, c11]
  · obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
    rw [imageOf_witnessOf F prog _ _ h.caps.le_maxLogMem]
    refine image_sigma_eq rfl _ _ fun x ↦ ?_
    exact (congr (congr (congrArg E.ofLimbs (memLimb_stackOf h hp 0 x))
      (memLimb_stackOf h hp 1 x)) (memLimb_stackOf h hp 2 x)).trans (ofLimbs_limb _)

/-! ## The refinement -/

/-- `SatisfiedBy` as a relation on the protocol's statements: the public input, no oracle. -/
def satisfiedByRel (prog : Program) :
    Set ((PublicInput × ∀ i, NoOracle i) × EnsembleWitness (leanIsaEnsemble prog)) :=
  {p | SatisfiedBy prog p.1.1 p.2}

/-- The adaptor as a refinement: on admissible sizes, reading the witness off the stack maps the
protocol's relation into leanISA's. -/
def leanIsaRefinement (F : FlockSpec) (prog : Program) (s : Sizes) (hs : s.Admissible prog) :
    Refinement (M3Rel (leanIsaInstance F prog s)) (satisfiedByRel prog) where
  map _ q := witnessOf F prog s q
  map_valid _ q h := satisfiedBy_witnessOf F prog s q hs h

end

end LeanVM.Protocol.LeanIsa
