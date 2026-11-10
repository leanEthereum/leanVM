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
cells (`column_stackOf`); its input lanes are the slots `0 … 24` of the honest `QKECCAK`, which
are the witness's input lanes (`word_stackOf`, `keccakWitness_getElem`), and the columns riding
its spare slots `50 … 63` are the witness's cells of them (`column_spare`); its output lanes are the
permutation of those, which are the witness's output lanes because every `KECCAK` row permutes
(`SatisfiedBy.keccak_valid`). Past a table's rows the stack holds the padding row
(`paddingHonest_stackOf`): zero committed cells, spare columns and input lanes, and output lanes Keccak-f[1600] of
the zero state (`padRow_outCol`). Then the bus and count clauses follow from the equivalences of
`LeanIsa/Relation.lean`, the constraint clause from them on the executed rows and from the padding
row on the others (`padRow_constraints`); the public lines from the two public words of the image
(`image_words`), which the seed rows put in the memory columns (`memLimb_stackOf`); and the Keccak
region clause from how the honest `QKECCAK` is built: its slots `25 … 49` are the first twelve
rounds of its slots `0 … 24`, step by step (`keccakHolds_stackOf`).

`leanIsaRefinement` packages the soundness direction as the spine's `Refinement` from `M3Rel` to
`SatisfiedBy`, the witness map the knowledge transport needs.

A witness's rows may carry cells past their component's width, which no constraint reads and
the stack drops: the read-back is cell for cell within the width.
-/

namespace LeanVM.Protocol.LeanIsa

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization CompPoly CMlPolynomialEval
open Air.Flat (Component EnsembleWitness)

@[expose] public section

variable (prog : LeanIsaProgram) (s : Sizes) {κ : ℕ} (w : EnsembleWitness (leanIsaEnsemble prog κ))

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
    (witnessColumn prog s w c')[x] =
      (witnessColumn prog s w c)[(Fin.cast (by rw [h]) x : Fin (2 ^ kappa prog s c))] := by
  subst h
  rfl

/-- A committed column of the stack of a witness is the witness's column. -/
theorem column_stackOf (c : Col) (h : ¬ IsVirtual c) (x : Fin (2 ^ kappa prog s c)) :
    ((leanIsaInstance prog s).column (stackOf prog s w) c).values.get x =
      (witnessColumn prog s w c)[x] := by
  refine (column_committed prog s _ c h x).trans ?_
  have hsz := size_blockOf prog s c h
  have hx : x.val < 2 ^ (blocks prog s).size (blockOf c h) := by rw [hsz]; exact x.isLt
  refine (stackColumn_get prog s _ (blockOf c h) ⟨x.val, hx⟩).trans ?_
  exact witnessColumn_congr prog s w (stackOrder_blockOf prog s c h) _

/-- Word `x` of slot `slot` of the Keccak region of the stack of a witness is the witness's
`QKECCAK` there. -/
theorem word_stackOf (slot : ℕ) (hslot : slot < 64) (x : Fin (2 ^ s.τ 5)) :
    (keccakRegion prog s).word
        ((leanIsaInstance prog s).keccakColumn (keccakRegion prog s) (stackOf prog s w)) slot x =
      (keccakWitness prog s w)[x.val + 2 ^ s.τ 5 * slot]'(slot_lt x slot hslot) :=
  (word_eq_column prog s _ slot hslot x).trans
    (column_stackOf prog s w keccakCol not_isVirtual_keccakCol _)

/-- The witness's `QKECCAK` at word `x` of slot `slot`: an input lane, a lane after twelve
rounds, or the row's cell of a spare column. -/
theorem keccakWitness_getElem (slot : ℕ) (hslot : slot < 64) (x : ℕ) (hx : x < 2 ^ s.τ 5)
    (h : x + 2 ^ s.τ 5 * slot < 2 ^ (s.τ 5 + 6)) :
    (keccakWitness prog s w)[x + 2 ^ s.τ 5 * slot]'h =
      if h : slot < 25 then inLaneOf prog s w x ⟨slot, h⟩
      else if h' : slot < 50 then
        stateLanes (keccakSegment 0 (laneState (inLaneOf prog s w x))) ⟨slot - 25, by omega⟩
      else cellOf (tableAt w 5) x (spareColumn (slot - 50)) := by
  have hp : 0 < 2 ^ s.τ 5 := Nat.two_pow_pos _
  have hd : (x + 2 ^ s.τ 5 * slot) / 2 ^ s.τ 5 = slot := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx, Nat.zero_add]
  have hm : (x + 2 ^ s.τ 5 * slot) % 2 ^ s.τ 5 = x := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  unfold keccakWitness
  simp only [Vector.getElem_ofFn, hd, hm]

/-- **The Keccak region of the stack of a witness holds**: at every step, its slots `25 … 49`
are the first twelve rounds of its slots `0 … 24`, as the honest `QKECCAK` is built. -/
theorem keccakHolds_stackOf :
    (keccakRegion prog s).Holds
      ((leanIsaInstance prog s).keccakColumn (keccakRegion prog s) (stackOf prog s w)) := by
  intro x
  have hin : (fun l : Fin 25 ↦ (keccakRegion prog s).word
      ((leanIsaInstance prog s).keccakColumn (keccakRegion prog s) (stackOf prog s w)) (0 + l)
        x) = inLaneOf prog s w x := by
    funext l
    rw [Nat.zero_add]
    refine (word_stackOf prog s w l (by omega) x).trans ?_
    rw [keccakWitness_getElem prog s w l (by omega) _ x.isLt, dite_eq_left l.isLt]
  have hmid : (fun l : Fin 25 ↦ (keccakRegion prog s).word
      ((leanIsaInstance prog s).keccakColumn (keccakRegion prog s) (stackOf prog s w)) (25 + l)
        x) = stateLanes (keccakSegment 0 (laneState (inLaneOf prog s w x))) := by
    funext l
    refine (word_stackOf prog s w (25 + l) (by omega) x).trans ?_
    rw [keccakWitness_getElem prog s w (25 + l) (by omega) _ x.isLt,
      dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 1
    ext
    simp
  simp only [KeccakRegion.state]
  rw [hin, hmid, laneState_stateLanes]

/-- The stack of a witness satisfies the Keccak predicate. -/
theorem aux_stackOf : (leanIsaInstance prog s).aux (stackOf prog s w) := by
  intro r hr
  obtain rfl := (Option.some.inj hr).symm
  exact keccakHolds_stackOf prog s w

/-! ## Rows of the two blocks -/

/-- The cells of a memory-block row: the limbs at `0, 1`, the finalize count at `3`. -/
private theorem memRow_cells (m : Vector K 2) (idx cnt : K) :
    (toElements (⟨m, idx, cnt⟩ : MemRow K)).toArray[0]?.getD 0 = m[0] ∧
    (toElements (⟨m, idx, cnt⟩ : MemRow K)).toArray[1]?.getD 0 = m[1] ∧
    (toElements (⟨m, idx, cnt⟩ : MemRow K)).toArray[3]?.getD 0 = cnt := by
  simp [explicit_provable_type, ProvableStruct.componentsToElements, ProvableStruct.toComponents,
    toComponents, circuit_norm]
  refine ⟨?_, ?_, ?_⟩ <;> rw [Vector.getElem_append] <;> simp

/-- Cell `memRowCell k` of a memory-block row is its column `k`: a limb, or the finalize count. -/
private theorem memRow_cell (m : Vector K 2) (idx cnt : K) (k : Fin 3) :
    (toElements (⟨m, idx, cnt⟩ : MemRow K)).toArray[memRowCell k]?.getD 0 =
      ![m[0], m[1], cnt] k := by
  obtain ⟨c0, c1, c3⟩ := memRow_cells m idx cnt
  fin_cases k
  exacts [c0, c1, c3]

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

variable {prog s w}

/-- The sizes a witness carries: its memory size and its tables' row counts. -/
def witnessSizes (w : EnsembleWitness (leanIsaEnsemble prog κ)) (h : 0 < (imageOf w.data).1) :
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

/-- The input lanes of an executed `KECCAK` row of a witness are its cells `15 … 39`. -/
private theorem inLaneOf_executed (x : ℕ) (hx : x < s.rows 5) (l : Fin 25) :
    inLaneOf prog s w x l = cellOf (tableAt w 5) x (15 + l) := by
  simp [inLaneOf, hx]

/-- Every executed `KECCAK` row of a witness satisfying the constraint system permutes: its
output lane `l` is lane `l` of Keccak-f[1600] of its input lanes. -/
theorem outLane_of_satisfiedBy {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) (x : ℕ) (hx : x < s.rows 5) (l : Fin 25) :
    cellOf (tableAt w 5) x (40 + l) =
      stateLanes (keccakF1600 (laneState (inLaneOf prog s w x))) l := by
  obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
  have hx' : x < (tableAt w 5).table.length := hx
  have hv := congrFun (h.keccak_valid _ (List.getElem_mem hx')) l
  simp only [KeccakRow.outLanes, keccakRowAt_lout] at hv
  rw [cellOf_eq _ hx', hv]
  congr 3
  funext l'
  rw [inLaneOf_executed x hx, cellOf_eq _ hx', KeccakRow.inLanes, keccakRowAt_lin]

/-- Within its width, an opcode table of a witness satisfying the constraint system is the
stack's executed rows. -/
private theorem cells_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) (j : Fin 6) (x : Fin ((witnessSizes w hp).rows j))
    (i : Fin (opcodeComponent j).width) :
    cellOf (opTable w j) x i =
      (leanIsaInstance prog (witnessSizes w hp)).row
        (stackOf prog (witnessSizes w hp) w) (opIdx j)
          (Fin.castLE ((witnessSizes w hp).rows_le j) x) i := by
  have hs : Sizes.ofWitness w = some (witnessSizes w hp) := by
    unfold Sizes.ofWitness
    simp only [hp, dite_true]
    rfl
  by_cases hl : IsLane ⟨opIdx j, i⟩
  · have hj : j = 5 := Fin.ext (by have := congrArg Fin.val hl.1; simp [opIdx] at this; omega)
    subst hj
    have h1 : 15 ≤ i.val := hl.2.1
    have h2 : i.val < 65 := hl.2.2
    have hx : (Fin.castLE ((witnessSizes w hp).rows_le 5) x).val < (witnessSizes w hp).rows 5 :=
      x.isLt
    have hw : (opcodeComponent 5).width = 92 := width_keccak
    by_cases ho : 40 ≤ i.val
    · obtain ⟨l, rfl⟩ : ∃ l : Fin 25,
          i = ⟨40 + l.val, by clear hl h1 h2 ho; have := l.isLt; rw [hw]; omega⟩ :=
        ⟨⟨i.val - 40, by omega⟩, Fin.ext (by simp only; omega)⟩
      refine Eq.trans ?_ (column_outCol_of_aux prog _ _ (aux_stackOf prog _ w) l _).symm
      refine (outLane_of_satisfiedBy h hs x x.isLt l).trans ?_
      simp only [KeccakRegion.state, Nat.zero_add]
      congr 3
      funext l'
      refine Eq.trans ?_ (word_stackOf prog _ w l' (by omega) _).symm
      refine Eq.trans ?_ (keccakWitness_getElem prog _ w l' (by omega) x.val
        (lt_of_lt_of_le x.isLt ((witnessSizes w hp).rows_le 5)) _).symm
      rw [dite_eq_left l'.isLt]
    · obtain ⟨l, rfl⟩ : ∃ l : Fin 25,
          i = ⟨15 + l.val, by clear hl h1 h2 ho; have := l.isLt; rw [hw]; omega⟩ :=
        ⟨⟨i.val - 15, by omega⟩, Fin.ext (by simp only; omega)⟩
      refine Eq.trans ?_ (column_inCol prog _ _ l _).symm
      refine Eq.trans ?_ (word_stackOf prog _ w l (by omega) _).symm
      refine Eq.trans ?_ (keccakWitness_getElem prog _ w l (by omega) x.val
        (lt_of_lt_of_le x.isLt ((witnessSizes w hp).rows_le 5)) _).symm
      rw [dite_eq_left l.isLt]
      exact (inLaneOf_executed x x.isLt l).symm
  · by_cases hsp : IsSpare ⟨opIdx j, i⟩
    · have hj : j = 5 := Fin.ext (by have := congrArg Fin.val hsp.1; simp [opIdx] at this; omega)
      subst hj
      obtain ⟨h50, hcol⟩ := qSlot_spare hsp
      have hx : x.val < 2 ^ (witnessSizes w hp).τ 5 :=
        lt_of_lt_of_le x.isLt ((witnessSizes w hp).rows_le 5)
      refine Eq.trans ?_ (column_spare prog _ _ _ hsp
        (Fin.castLE ((witnessSizes w hp).rows_le 5) x)).symm
      refine Eq.trans ?_ (word_stackOf prog _ w _ (qSlot _).isLt _).symm
      refine Eq.trans ?_ (keccakWitness_getElem prog _ w _ (qSlot _).isLt x.val hx _).symm
      rw [dite_eq_right (by omega), dite_eq_right (by omega), hcol]
      rfl
    · refine Eq.symm ((column_stackOf prog _ w ⟨opIdx j, i⟩
        (fun hv ↦ hv.lane_or_spare.elim hl hsp) _).trans ?_)
      exact Vector.getElem_ofFn _

/-- The memory block of a witness satisfying the constraint system is the stack's. -/
private theorem memRows_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) :
    memBlockRows w = memBlockRowsOf prog (witnessSizes w hp)
      (stackOf prog (witnessSizes w hp) w) := by
  obtain ⟨idx, cnt, hrows⟩ := h.seed_rows
  have hlen : (memBlockRows w).length = 2 ^ (imageOf w.data).1 := by
    rw [hrows, List.length_ofFn]
  have hrow : ∀ x : Fin (2 ^ (imageOf w.data).1),
      (memBlockRows w)[x.val]'(by rw [hlen]; exact x.isLt) =
        (toElements (⟨#v[((imageOf w.data).2 x).limb 0, ((imageOf w.data).2 x).limb 1], idx x,
          cnt x⟩ : MemRow K)).toArray :=
    fun x ↦ by simp only [hrows, List.getElem_ofFn]
  have hidx : ∀ x : Fin (2 ^ (imageOf w.data).1), idx x = addressOfIndex x := fun x ↦ by
    have := h.index_columns x.val (by rw [hlen]; exact x.isLt)
    rw [hrow, memRowAt_toElements] at this
    exact this
  have hcell : ∀ (k : Fin 3) (x : Fin (2 ^ (imageOf w.data).1)),
      cell prog (witnessSizes w hp) (stackOf prog (witnessSizes w hp) w) (memCol k) x =
        ((memBlockRows w)[x.val]'(by rw [hlen]; exact x.isLt))[memRowCell k]?.getD 0 :=
    fun k x ↦ (column_stackOf prog (witnessSizes w hp) w (memCol k) (fun hk ↦ by
      have := congrArg Fin.val hk.1; simp [memCol, opIdx] at this) x).trans
        ((Vector.getElem_ofFn _).trans (cellOf_eq _ _ _))
  rw [hrows, memBlockRowsOf]
  refine congrArg List.ofFn (funext fun x ↦ ?_)
  simp only [hcell, hrow x, hidx x, memRow_cell]
  rfl

/-- The bytecode block of a witness satisfying the constraint system is the stack's. -/
private theorem bytecodeRows_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) :
    bytecodeBlockRows w = bytecodeBlockRowsOf prog (witnessSizes w hp)
      (stackOf prog (witnessSizes w hp) w) := by
  obtain ⟨cntFin, hrows⟩ := h.bytecode_rows
  have hlen : (bytecodeBlockRows w).length = 2 ^ prog.logSize := by
    rw [hrows, List.length_ofFn]
  have hrow : ∀ i : Fin (2 ^ prog.logSize),
      (bytecodeBlockRows w)[i.val]'(by rw [hlen]; exact i.isLt) =
        (toElements (bytecodeRowOf prog i (cntFin i))).toArray :=
    fun i ↦ by simp only [hrows, List.getElem_ofFn]
  have hcell : ∀ i : Fin (2 ^ prog.logSize),
      cell prog (witnessSizes w hp) (stackOf prog (witnessSizes w hp) w) bfcntCol i =
        ((bytecodeBlockRows w)[i.val]'(by rw [hlen]; exact i.isLt))[1]?.getD 0 :=
    fun i ↦ (column_stackOf prog (witnessSizes w hp) w bfcntCol (by decide) i).trans
      ((Vector.getElem_ofFn _).trans (cellOf_eq _ _ _))
  rw [hrows, bytecodeBlockRowsOf]
  refine congrArg List.ofFn (funext fun i ↦ ?_)
  simp only [hcell, hrow i, bytecodeRow_cell]

/-- The stack of a witness satisfying the constraint system agrees with it. -/
theorem agrees_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) : Agrees s (stackOf prog s w) w := by
  obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
  exact ⟨fun j ↦ rfl, cells_stackOf h hp, memRows_stackOf h hp, bytecodeRows_stackOf h hp⟩

/-! ## The relation of the stack -/

/-- A limb column of the memory on the stack of a witness satisfying the constraint system is
that limb of the image the data names. -/
private theorem memLimb_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) (k : Fin 2) (x : Fin (2 ^ (imageOf w.data).1)) :
    cell prog (witnessSizes w hp) (stackOf prog (witnessSizes w hp) w) (memCol k.castSucc) x =
      ((imageOf w.data).2 x).limb k := by
  obtain ⟨idx, cnt, hrows⟩ := h.seed_rows
  have hlen : (memBlockRows w).length = 2 ^ (imageOf w.data).1 := by
    rw [hrows, List.length_ofFn]
  refine (column_stackOf prog (witnessSizes w hp) w (memCol k.castSucc) (fun hk ↦ by
    have := congrArg Fin.val hk.1; simp [memCol, opIdx] at this) x).trans
      ((Vector.getElem_ofFn _).trans ((cellOf_eq _ (by rw [hlen]; exact x.isLt) _).trans ?_))
  have hrow : (memBlockRows w)[x.val]'(by rw [hlen]; exact x.isLt) =
      (toElements (⟨#v[((imageOf w.data).2 x).limb 0, ((imageOf w.data).2 x).limb 1], idx x,
        cnt x⟩ : MemRow K)).toArray := by
    simp only [hrows, List.getElem_ofFn]
  simp only [hrow, memRow_cell]
  fin_cases k <;> rfl

/-- The image a witness satisfying the constraint system names holds the public words at
`g^0` and `g^1`. -/
private theorem image_words {input : PublicInput} (h : SatisfiedBy prog input w)
    (h0 : 0 < 2 ^ (imageOf w.data).1) (h1 : 1 < 2 ^ (imageOf w.data).1) :
    (imageOf w.data).2 ⟨0, h0⟩ = input.word0 ∧ (imageOf w.data).2 ⟨1, h1⟩ = input.word1 := by
  have hκ : (imageOf w.data).1 < 64 := lt_of_le_of_lt h.caps.le_maxLogMem (by decide)
  have e0 := (MemoryImage.read_gpow hκ (imageOf w.data).2 ⟨0, h0⟩).symm.trans h.word0_eq
  have e1 := (MemoryImage.read_gpow hκ (imageOf w.data).2 ⟨1, h1⟩).symm.trans h.word1_eq
  exact ⟨Option.some.inj e0, Option.some.inj e1⟩

/-- The stack of a witness satisfying the constraint system holds the public lines: its memory
columns' first two cells are the public words' limbs. -/
private theorem publicLinesHold_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) :
    (leanIsaInstance prog s).PublicLinesHold input (stackOf prog s w) := by
  obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
  have h0 : 0 < 2 ^ (imageOf w.data).1 := Nat.two_pow_pos _
  have h1 : 1 < 2 ^ (imageOf w.data).1 := Nat.one_lt_two_pow hp.ne'
  obtain ⟨w0, w1⟩ := image_words h h0 h1
  have hl : ∀ k : Fin 2,
      cell prog (witnessSizes w hp) (stackOf prog (witnessSizes w hp) w) (memCol k.castSucc)
        ⟨0, h0⟩ = input.word0.limb k ∧
      cell prog (witnessSizes w hp) (stackOf prog (witnessSizes w hp) w) (memCol k.castSucc)
        ⟨1, h1⟩ = input.word1.limb k := fun k ↦
    ⟨(memLimb_stackOf h hp k _).trans (congrArg (·.limb k) w0),
      (memLimb_stackOf h hp k _).trans (congrArg (·.limb k) w1)⟩
  intro l hl'
  have hls : (publicLines prog (witnessSizes w hp) input).toList =
      [⟨memCol 0, input.lanes 0, input.lanes 2, false, hp⟩,
        ⟨memCol 1, input.lanes 1, input.lanes 3, false, hp⟩] := rfl
  change l ∈ (publicLines prog (witnessSizes w hp) input).toList at hl'
  rw [hls] at hl'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
  rcases hl' with rfl | rfl
  · exact ⟨(hl 0).1.trans (by simp [PublicInput.word0]),
      (hl 0).2.trans (by simp [PublicInput.word1])⟩
  · exact ⟨(hl 1).1.trans (by simp [PublicInput.word0]),
      (hl 1).2.trans (by simp [PublicInput.word1])⟩

/-! ## Honest padding -/

/-- The padding row is zero off the `KECCAK` output lanes. -/
theorem padRow_of_not_isOut (j : Fin 6) (i : Fin (width (opIdx j)))
    (h : ¬ IsOut ⟨opIdx j, i⟩) : padRow (opIdx j) i = 0 := by
  by_cases hj : j = 5
  · subst hj
    rw [padRow_keccak, dite_eq_right]
    exact fun h' ↦ h ⟨rfl, h'⟩
  · exact padRow_of_ne_keccak j hj i

/-- **The padding row's output lanes** are Keccak-f[1600] of the zero state, the permutation of
its input lanes. -/
theorem padRow_outCol (l : Fin 25) :
    padRow (opIdx 5) (outCol l).2 = stateLanes (keccakF1600 (laneState fun _ ↦ 0)) l := by
  refine (padRow_keccak (outCol l).2).trans ?_
  rw [dite_eq_left (by simp [outCol]; omega)]
  congr 1
  ext
  simp [outCol]

/-- **The padding is honest.** On the stack of any witness, at the sizes it carries, every
padding row holds its table's public padding row: the committed cells and the input lanes are
zero past the table's rows, and the output lanes are then Keccak-f[1600] of the zero state. -/
theorem paddingHonest_stackOf (hs : Sizes.ofWitness w = some s) :
    (leanIsaInstance prog s).PaddingHonest (stackOf prog s w) := by
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
    by_cases hl : IsLane ⟨⟨j + 3, hj⟩, i⟩
    · have hj5 : j = 5 := by have := congrArg Fin.val hl.1; simp [opIdx] at this; omega
      subst hj5
      have h1 : 15 ≤ i.val := hl.2.1
      have h2 : i.val < 65 := hl.2.2
      have hw : (leanIsaInstance prog (witnessSizes w hp)).width ⟨5 + 3, hj⟩ = 92 :=
        width_keccak
      let x' : Fin (2 ^ (witnessSizes w hp).τ 5) := x
      have hx' : (witnessSizes w hp).rows 5 ≤ x'.val := hx
      have hzero : inLaneOf prog (witnessSizes w hp) w x' = fun _ ↦ 0 := by
        funext l
        simp [inLaneOf, Nat.not_lt.mpr hx']
      by_cases ho : 40 ≤ i.val
      · obtain ⟨l, rfl⟩ : ∃ l : Fin 25,
            i = ⟨40 + l.val, by clear hl h1 h2 ho; have := l.isLt; rw [hw]; omega⟩ :=
          ⟨⟨i.val - 40, by omega⟩, Fin.ext (by simp only; omega)⟩
        refine (column_outCol_of_aux prog _ _ (aux_stackOf prog _ w) l x').trans ?_
        refine Eq.trans ?_ (padRow_outCol l).symm
        simp only [KeccakRegion.state, Nat.zero_add]
        refine congrArg (fun st ↦ stateLanes (keccakF1600 (laneState st)) l) (funext fun l' ↦ ?_)
        refine (word_stackOf prog _ w l' (by omega) _).trans ?_
        rw [keccakWitness_getElem prog _ w l' (by omega) _ x'.isLt, dite_eq_left l'.isLt, hzero]
      · obtain ⟨l, rfl⟩ : ∃ l : Fin 25,
            i = ⟨15 + l.val, by clear hl h1 h2 ho; have := l.isLt; rw [hw]; omega⟩ :=
          ⟨⟨i.val - 15, by omega⟩, Fin.ext (by simp only; omega)⟩
        refine (column_inCol prog _ _ l x').trans ?_
        refine (word_stackOf prog _ w l (by omega) _).trans ?_
        rw [keccakWitness_getElem prog _ w l (by omega) _ x'.isLt, dite_eq_left l.isLt, hzero]
        exact (padRow_of_not_isOut 5 _ fun h ↦ by have := h.2.1; simp at this; omega).symm
    · by_cases hsp : IsSpare ⟨⟨j + 3, hj⟩, i⟩
      · have hj5 : j = 5 := by have := congrArg Fin.val hsp.1; simp [opIdx] at this; omega
        subst hj5
        obtain ⟨h50, hcol⟩ := qSlot_spare hsp
        let x' : Fin (2 ^ (witnessSizes w hp).τ 5) := x
        refine (column_spare prog _ _ _ hsp x').trans ?_
        refine (word_stackOf prog _ w _ (qSlot _).isLt x').trans ?_
        rw [keccakWitness_getElem prog _ w _ (qSlot _).isLt _ x'.isLt, dite_eq_right (by omega),
          dite_eq_right (by omega), hcol]
        refine Eq.trans ?_ (padRow_of_not_isOut 5 _ hsp.not_isOut).symm
        have hnone : (tableAt w 5).table[x.val]? = none := List.getElem?_eq_none hrows
        simp [cellOf, x', hnone]
      · refine (column_stackOf prog (witnessSizes w hp) w ⟨⟨j + 3, hj⟩, i⟩
          (fun hv ↦ hv.lane_or_spare.elim hl hsp) x).trans ?_
        refine Eq.trans ?_ (padRow_of_not_isOut ⟨j, by omega⟩ i fun ho ↦ hl ho.isLane).symm
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

/-- Every opcode table's constraints vanish at its padding row: zero but for the `KECCAK` output
lanes, of a table without constraints. -/
theorem padRow_constraints (j : Fin 6) :
    ∀ C ∈ (opcodeTable j).constraints, C.eval (padRow (opIdx j)) = 0 := by
  by_cases h4 : j = 4
  · subst h4
    have hz : padRow (opIdx 4) = fun _ ↦ 0 := funext fun i ↦
      padRow_of_not_isOut 4 i fun hi ↦ by have := congrArg Fin.val hi.1; simp [opIdx] at this
    rw [hz]
    exact jump_constraints_zero
  · intro C hC
    exact absurd (List.length_pos_of_mem hC) (by rw [opcode_constraints_nil j h4]; omega)

/-- **The adaptor, completeness.** A witness satisfying leanISA's constraint system on the input
stacks, at the sizes it carries, into a column satisfying the leanISA instance's relation: the
executed rows are the witness's, the padding rows its tables' padding rows. -/
theorem m3Holds_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) :
    M3Holds (leanIsaInstance prog s) input (stackOf prog s w) := by
  have hA := agrees_stackOf h hs
  have hP := paddingHonest_stackOf hs
  refine ⟨?_, (balanced_iff_pairs hA).mpr fun k ↦ ?_, (countsNonzero_iff hA).mp h.counts_nonzero,
    ?_, ?_⟩
  · intro j' C hC x
    rcases j' with ⟨_ | _ | _ | j, hj⟩
    · exact absurd hC List.not_mem_nil
    · exact absurd hC List.not_mem_nil
    · exact absurd hC List.not_mem_nil
    · have h9 : (leanIsaInstance prog s).ntab = 9 := rfl
      by_cases hx : x.val < s.rows ⟨j, by omega⟩
      · have hmem : opTable w ⟨j, by omega⟩ ∈ w.tables := mem_tables_iff.mpr ⟨⟨j, by omega⟩, rfl⟩
        exact (opcode_constraints_iff hA ⟨j, by omega⟩).mp (h.constraints _ hmem) ⟨x.val, hx⟩ C hC
      · rw [hP ⟨j + 3, hj⟩ x (Nat.not_lt.mp hx)]
        exact padRow_constraints ⟨j, by omega⟩ C hC
  · fin_cases k
    exacts [h.state_balanced, h.mem_balanced, h.bytecode_balanced]
  · exact publicLinesHold_stackOf h hs
  · intro r hr
    obtain rfl := Option.mem_def.mp hr |> Option.some.inj |>.symm
    exact keccakHolds_stackOf prog s w

/-- **The adaptor, completeness, with honest padding.** A witness satisfying leanISA's constraint
system stacks, at the sizes it carries, into a column satisfying the leanISA instance's relation
whose padding rows hold the public padding row, the relation the protocol's completeness starts
from. -/
theorem m3Honest_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) :
    M3Honest (leanIsaInstance prog s) input (stackOf prog s w) :=
  ⟨m3Holds_stackOf h hs, paddingHonest_stackOf hs⟩

/-- **The witness read back.** Reading a witness back off the stack of a witness satisfying the
constraint system gives the witness's opcode tables within their widths, its memory and bytecode
blocks, its public input and the image its data names. -/
theorem witnessOf_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hs : Sizes.ofWitness w = some s) :
    (∀ (j : Fin 6) (x : Fin (s.rows j)) (i : Fin (opcodeComponent j).width),
      cellOf (opTable (witnessOf prog s (stackOf prog s w)) j) x i = cellOf (opTable w j) x i) ∧
    memBlockRows (witnessOf prog s (stackOf prog s w)) = memBlockRows w ∧
    bytecodeBlockRows (witnessOf prog s (stackOf prog s w)) = bytecodeBlockRows w ∧
    (witnessOf prog s (stackOf prog s w)).publicInput = w.publicInput ∧
    imageOf (witnessOf prog s (stackOf prog s w)).data = imageOf w.data := by
  have hA := agrees_stackOf h hs
  have hκ : s.logMem < 64 := by
    obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
    exact lt_of_le_of_lt h.caps.le_maxLogMem (by decide)
  have hr : ∀ j, s.rows j ≤ UInt64.size := by
    obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
    exact fun j ↦ (opTable w j).length_le
  have hB := agrees_witnessOf prog s (stackOf prog s w) hκ hr
  refine ⟨fun j x i ↦ (hB.cells j x i).trans (hA.cells j x i).symm,
    hB.memRows.trans hA.memRows.symm, hB.bytecodeRows.trans hA.bytecodeRows.symm, ?_, ?_⟩
  · obtain ⟨c00, c01, c10, c11⟩ := publicLines_cells prog s _ (publicLinesHold_stackOf h hs)
    show publicInputOf prog s (stackOf prog s w) = _
    rw [h.public_input_eq, publicInputOf, PublicIO.ofInput, c00, c01, c10, c11]
  · obtain ⟨hp, rfl⟩ := eq_of_ofWitness hs
    rw [imageOf_witnessOf prog _ _ h.caps.le_maxLogMem]
    refine image_sigma_eq rfl _ _ fun x ↦ ?_
    exact (congr (congrArg E.ofLimbs (memLimb_stackOf h hp 0 x))
      (memLimb_stackOf h hp 1 x)).trans (ofLimbs_limb _)

/-! ## The refinement -/

/-- `SatisfiedBy` as a relation on the protocol's statements: the public input, no oracle; its
witnesses are those of the ensemble at the memory log-size `κ`. -/
def satisfiedByRel (prog : LeanIsaProgram) (κ : ℕ) :
    Set ((PublicInput × ∀ i, NoOracle i) × EnsembleWitness (leanIsaEnsemble prog κ)) :=
  {p | SatisfiedBy prog p.1.1 p.2}

/-- The adaptor as a refinement: on admissible sizes, reading the witness off the stack maps the
protocol's relation into leanISA's, at the announced memory log-size (leanVM's
`layout(prog, log_mem, …)` fixes the instance by it). -/
def leanIsaRefinement (prog : LeanIsaProgram) (s : Sizes) (hs : s.Admissible prog) :
    Refinement (M3Rel (leanIsaInstance prog s)) (satisfiedByRel prog s.logMem) where
  map _ q := witnessOf prog s q
  map_valid _ q h := satisfiedBy_witnessOf prog s q hs h

end

end LeanVM.Protocol.LeanIsa
