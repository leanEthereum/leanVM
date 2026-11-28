/-
  LeanVM.Protocol.Relation.Link.KeccakStep

  Each executed `KECCAK` row takes one leanISA step under the link's relation and `KeccakRel`.
-/

module

public import LeanVM.Protocol.Relation.Link.Steps
public import LeanVM.Protocol.Relation.Placement
public import LeanVM.Semantics.KeccakCells
import LeanVM.Semantics.Lemmas
import LeanVM.Parameters.Field
import LeanVM.Protocol.Tables

/-!
# `KECCAK`'s rows

`links_keccak` reads thirteen cells framed at the instruction's offsets (`keccakReadAccess`) and
writes thirteen at `fp·o_out·g^c` (`keccakWriteAccess`), each cell's limbs the layout's lanes as
its flag selects (`layoutLimb`). At a flag `0` or `1` a limb is the lane's column
(`layoutLimb_evaluate`), so a read cell's word is `laneCells` of the input lanes with the free limb
(`readWord_eq`), a written one's `laneCells` of the output lanes (`writeWord_eq`). The input lanes are
`q_keccak`'s slots (`columnRow_inputLane`), so the state the read cells hold is `keccakInput`, and
under `KeccakRel` the output lanes are its permutation (`keccakOutput_of_keccakRel`):
`rowStep_keccak`.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Arithmetization

@[expose] public section

/-! ## Forms -/

/-- A term's value, `c · Π column(i)`. -/
def termValue (col : ℕ → E) (t : List ℕ × E) : E := t.1.foldl (fun acc i ↦ acc * col i) t.2

theorem foldl_mul_start (col : ℕ → E) : ∀ (m : List ℕ) (c : E),
    m.foldl (fun acc i ↦ acc * col i) c = c * m.foldl (fun acc i ↦ acc * col i) 1
  | [], c => by simp
  | i :: m, c => by
    simp only [List.foldl_cons, one_mul]
    rw [foldl_mul_start col m (c * col i), foldl_mul_start col m (col i)]
    ring

theorem termValue_add (col : ℕ → E) (m : List ℕ) (c c' : E) :
    termValue col (m, c + c') = termValue col (m, c) + termValue col (m, c') := by
  simp only [termValue]
  rw [foldl_mul_start col m (c + c'), foldl_mul_start col m c, foldl_mul_start col m c']
  ring

theorem termValue_mul (col : ℕ → E) (m : List ℕ) (w c : E) :
    termValue col (m, w * c) = w * termValue col (m, c) := by
  simp only [termValue]
  rw [foldl_mul_start col m (w * c), foldl_mul_start col m c]
  ring

theorem Form.evaluate_eq (f : Form) (col : ℕ → E) :
    f.evaluate col = (f.terms.map (termValue col)).sum := by
  rw [Form.evaluate, Tables.sumE_eq]
  rfl

theorem addTerm_sum (col : ℕ → E) : ∀ (L : List (List ℕ × E)) (m : List ℕ) (c : E),
    ((addTerm L m c).map (termValue col)).sum =
      (L.map (termValue col)).sum + termValue col (m, c)
  | [], m, c => by simp [addTerm]
  | (m', c') :: rest, m, c => by
    simp only [addTerm]
    split_ifs with h
    · subst h
      simp only [List.map_cons, List.sum_cons, termValue_add]
      ring
    · simp only [List.map_cons, List.sum_cons, addTerm_sum col rest m c]
      ring

theorem foldl_addTerm_sum (col : ℕ → E) (w : E) : ∀ (G L : List (List ℕ × E)),
    ((G.foldl (fun acc t ↦ addTerm acc t.1 (w * t.2)) L).map (termValue col)).sum =
      (L.map (termValue col)).sum + w * (G.map (termValue col)).sum
  | [], L => by simp
  | t :: G, L => by
    rw [List.foldl_cons, foldl_addTerm_sum col w G, addTerm_sum, termValue_mul]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem Form.addScaled_evaluate (f h : Form) (w : E) (col : ℕ → E) :
    (f.addScaled h w).evaluate col = f.evaluate col + w * h.evaluate col := by
  simp only [Form.evaluate_eq, Form.addScaled]
  exact foldl_addTerm_sum col w h.terms f.terms

theorem Form.foldl_add_evaluate (col : ℕ → E) : ∀ (forms : List Form) (f : Form),
    (forms.foldl Form.add f).evaluate col = f.evaluate col + (forms.map (·.evaluate col)).sum
  | [], f => by simp
  | x :: xs, f => by
    rw [List.foldl_cons, Form.foldl_add_evaluate col xs, Form.add, Form.addScaled_evaluate]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem Form.sum_evaluate (forms : List Form) (col : ℕ → E) :
    (Form.sum forms).evaluate col = (forms.map (·.evaluate col)).sum := by
  rw [Form.sum, Form.foldl_add_evaluate, Form.empty_evaluate, zero_add]

theorem Form.prod_evaluate (a b e : ℕ) (col : ℕ → E) :
    (Form.prod a b e).evaluate col = gpow e * col a * col b := by
  rw [Form.evaluate_eq]
  simp only [Form.prod, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    termValue, List.foldl_cons, List.foldl_nil]
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]
    ring

/-- A column's value, `0` for none. -/
def optCol (col : ℕ → E) : Option ℕ → E
  | some i => col i
  | none => 0

/-- **A layout limb at a flag `0` or `1`** is the column of the layout the flag selects. -/
theorem layoutLimb_evaluate (even odd : Option ℕ) (flag : ℕ) (missing : Option ℕ) (col : ℕ → E)
    (b : Bool) (hb : col flag = if b then 1 else 0) :
    (layoutLimb even odd flag missing).evaluate col =
      optCol col (if b then odd.orElse (fun _ ↦ missing) else even.orElse (fun _ ↦ missing)) := by
  simp only [layoutLimb]
  generalize even.orElse (fun _ ↦ missing) = a
  generalize odd.orElse (fun _ ↦ missing) = a'
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢ <;> by_cases hab : a = a'
  · subst hab
    rw [ite_eq_left_of_eq_true _ _ (eq_self a)]
    cases a <;> simp [optCol, Form.const_evaluate, Form.col_evaluate, gpow_eq_ofK]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hab), Form.sum_evaluate]
    cases a <;> cases a' <;> simp [hb, optCol, Form.col_evaluate, Form.prod_evaluate, gpow_eq_ofK]
  · subst hab
    rw [ite_eq_left_of_eq_true _ _ (eq_self a)]
    cases a <;> simp [optCol, Form.const_evaluate, Form.col_evaluate, gpow_eq_ofK]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hab), Form.sum_evaluate]
    cases a <;> cases a' <;>
      simp [hb, optCol, Form.col_evaluate, Form.prod_evaluate, gpow_eq_ofK, ← add_assoc,
        CharTwo.add_self_eq_zero]

/-! ## `KECCAK`'s links -/

/-- Read cell `cell`'s operand and its step past the operand's cell. -/
def keccakPart (cell : ℕ) : ℕ × ℕ :=
  if cell < 4 then (cell, 0) else if cell < 8 then (4, cell - 4) else if cell = 8 then (5, 0)
  else (6, cell - 9)

/-- A cell's word: its two limbs, each the lane its layout's flag selects. -/
def keccakCellValue (lanes flag : ℕ) (missing : Option ℕ) (cell : ℕ) : Form :=
  let lane := fun (l : Option ℕ) ↦ l.map (lanes + ·)
  let limb := fun (e o : Option ℕ) ↦ layoutLimb (lane e) (lane o) flag missing
  let e := (keccakCellLanes false).getD cell (none, none)
  let o := (keccakCellLanes true).getD cell (none, none)
  (limb e.1 o.1).addScaled (limb e.2 o.2) eY

/-- Read cell `cell`: framed at its operand's slot, its step past the operand's cell, its free limb
the column `free`. -/
def keccakReadAccess (cell : ℕ) : Access :=
  { pointer := keccakIx + (keccakPart cell).1, shift := (keccakPart cell).2, gate := none,
    address := {}, frame := some (keccakOffsetSlot (keccakPart cell).1, (keccakPart cell).2)
    value := keccakCellValue keccakIn 3 (some 7) cell, reads := [] }

/-- Written cell `cell`: at `g^cell·fp·o_out`, gated by `out_two` or `out_all` past cell `0`. -/
def keccakWriteAccess (cell : ℕ) : Access :=
  { pointer := keccakIx + 7, shift := cell,
    gate := if cell = 0 then none else if cell = 1 then some 5 else some 6
    address := Form.prod 1 2 cell, frame := none, value := keccakCellValue keccakOut 4 none cell
    reads := [] }

theorem keccak_links : (tables.getD 5 default).links.stateLink =
      { cycle := 67, pc := 0, fp := 1, next := (Form.col 0 1, Form.col 1 0) } ∧
    (tables.getD 5 default).links.memory =
      (List.range 13).map keccakReadAccess ++ (List.range 13).map keccakWriteAccess ∧
    (tables.getD 5 default).links.bytecodeLink.operands =
      [([11], Form.col 2 0), ([12], Form.col 3 0), ([13], Form.col 4 0), ([14], Form.col 5 0),
        ([15], Form.col 6 0)] := ⟨rfl, rfl, rfl⟩

theorem keccakCellLanes_getD (odd : Bool) {cell : ℕ} (hc : cell < 13) :
    (keccakCellLanes odd).getD cell (none, none) = cellLanes odd cell := by
  simp [keccakCellLanes, keccakCells, hc, cellLanes]

/-- **A cell's word at a layout flag `0` or `1`**: its limbs the columns of the lanes the layout
puts there, `missing` where it puts none. -/
theorem keccakCellValue_evaluate (lanes flag : ℕ) (missing : Option ℕ) {cell : ℕ} (hc : cell < 13)
    (col : ℕ → E) (b : Bool) (hb : col flag = if b then 1 else 0) :
    (keccakCellValue lanes flag missing cell).evaluate col =
      optCol col (((cellLanes b cell).1.map (lanes + ·)).orElse fun _ ↦ missing) +
        eY * optCol col (((cellLanes b cell).2.map (lanes + ·)).orElse fun _ ↦ missing) := by
  simp only [keccakCellValue, Form.addScaled_evaluate, keccakCellLanes_getD _ hc]
  rw [layoutLimb_evaluate _ _ _ _ _ b hb, layoutLimb_evaluate _ _ _ _ _ b hb]
  cases b <;> rfl

theorem cellLanes_lt : ∀ b : Bool, ∀ cell < 13,
    ((cellLanes b cell).1.getD 0) < 25 ∧ ((cellLanes b cell).2.getD 0) < 25 := by
  decide

/-! ## The lanes' columns -/

theorem keccakBase_five : globalColumnBases.getD 5 0 = 48 := by decide +kernel

theorem keccak_cols : ∀ c < 33, keccakOutputLane (globalColumnBases.getD 5 0 + c) = none := by
  decide +kernel

theorem keccak_outCols : ∀ l < 25, keccakOutputLane (globalColumnBases.getD 5 0 + (33 + l)) = some l := by
  decide +kernel

theorem qkeccakSlot_inputLane : ∀ l < 25, qkeccakSlot (48 + (8 + l)) = some l := by decide +kernel

theorem qkeccakSlot_qkeccak : qkeccakSlot qkeccak = none := by decide +kernel

/-- **An input lane is its slot of `q_keccak`**: input lane `l`'s row `u` is `q_keccak`'s row
`l·2^h + u`, `h` the `KECCAK` table's log-height. -/
theorem columnRow_inputLane {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (h : buildLayout bytecode lm rows = some layout) {μ : ℕ} (q : Column μ) {l : ℕ} (hl : l < 25)
    (u : ℕ) :
    columnRow layout q (48 + (8 + l)) u =
      columnRow layout q qkeccak (l * 2 ^ keccakHeight layout + u) := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      generalize List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows tableLogFloors = hs
      rcases hst : stack (columnKappas tables lm hs) with ⟨offsets, sl⟩
      simp only [columnRow, keccakHeight]
      have hlen : (columnKappas tables lm hs).length = 116 := by rw [columnKappas_eq]; simp
      have hkc : (columnKappas tables lm hs)[48 + (8 + l)]? = some (hs.getD 5 0) := by
        have := columnKappas_table lm hs (t := 5) (j := 8 + l) (by decide)
          (by rw [tableWidths_eq]; simp; omega)
        rw [keccakBase_five] at this
        simp only [List.getD_eq_getElem?_getD] at this
        rw [List.getElem?_eq_getElem (by omega)] at this ⊢
        simpa using this
      have hkq : (columnKappas tables lm hs)[qkeccak]? =
          some (hs.getD 5 0 + qkeccakSlotBits) := by
        rw [columnKappas_eq]; simp [qkeccak, opKeccak]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, zero_add,
        hkc, hkq, Option.map_some, Option.getD_some, qkeccakSlot_inputLane l hl,
        qkeccakSlot_qkeccak]
      rcases offsets.lookup qkeccak with _ | o
      · rfl
      · simp only [Option.map_some, Nat.shiftLeft_eq, show opKeccak = 5 from rfl, add_assoc]
    · cases h

/-! ## The cells' words -/

/-- Input lane `l` at row `u`, as a word. -/
def keccakInLanes (layout : Layout) {μ : ℕ} (q : Column μ) (u : ℕ) (l : Fin 25) : K :=
  tableWord layout q 5 (keccakIn + l) u

/-- **The input lanes are the permutation's input** the relation reads off `q_keccak`. -/
theorem keccakInput_eq {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (hA : Announced bytecode layout ρ) {μ : ℕ} (q : Column μ) (u : ℕ) :
    laneState (keccakInLanes layout q u) = keccakInput layout q u := by
  obtain ⟨lm, rows, hB⟩ := announced_build hA
  simp only [laneState, keccakInput, qkeccakLane]
  congr 1
  funext l
  rw [keccakInLanes, tableWord, keccakBase_five, show keccakIn = 8 from rfl,
    columnRow_inputLane hB q l.isLt u]

/-- **A read cell's word**, at the input layout's flag: the cell of the input lanes, its free limb
the column `free`. -/
theorem readWord_eq {layout : Layout} {μ : ℕ} {q : Column μ} {chunks : Chunks} (u k : ℕ)
    {cell : ℕ} (hc : cell < 13) (b : Bool) (hb : tableValue layout q 5 3 u = if b then 1 else 0) :
    accessWord layout q chunks 5 u k (keccakReadAccess cell) =
      laneCells (keccakInLanes layout q u) b (tableWord layout q 5 7 u) ⟨cell, hc⟩ := by
  simp only [accessWord, keccakReadAccess, List.map_nil, List.sum_nil, add_zero]
  rw [keccakCellValue_evaluate _ 3 _ hc (fun c ↦ tableValue layout q 5 c u) b hb]
  have hlimb : ∀ l? : Option ℕ, l?.getD 0 < 25 →
      optCol (fun c ↦ tableValue layout q 5 c u) ((l?.map (keccakIn + ·)).orElse fun _ ↦ some 7) =
        ofK (laneLimb (keccakInLanes layout q u) (tableWord layout q 5 7 u) l?) := by
    rintro (_ | l) hl
    · exact tableValue_ofK q u (keccak_cols 7 (by norm_num))
    · simp only [Option.getD_some] at hl
      simp only [Option.map_some, Option.orElse_some, optCol, laneLimb, hl, dite_true, keccakInLanes]
      exact tableValue_ofK q u (keccak_cols _ (by rw [show keccakIn = 8 from rfl]; omega))
  obtain ⟨h1, h2⟩ := cellLanes_lt b cell hc
  rw [hlimb _ h1, hlimb _ h2, word_of_limbs]
  rfl

/-- **A written cell's word**, at the output layout's flag: the cell of the output lanes, its free
limb zero. -/
theorem writeWord_eq {layout : Layout} {μ : ℕ} {q : Column μ} {chunks : Chunks} (u k : ℕ)
    {cell : ℕ} (hc : cell < 13) (b : Bool) (hb : tableValue layout q 5 4 u = if b then 1 else 0) :
    accessWord layout q chunks 5 u k (keccakWriteAccess cell) =
      laneCells (stateLanes (keccakOutput layout q u)) b 0 ⟨cell, hc⟩ := by
  simp only [accessWord, keccakWriteAccess, List.map_nil, List.sum_nil, add_zero]
  rw [keccakCellValue_evaluate _ 4 _ hc (fun c ↦ tableValue layout q 5 c u) b hb]
  have hlimb : ∀ l? : Option ℕ, l?.getD 0 < 25 →
      optCol (fun c ↦ tableValue layout q 5 c u) ((l?.map (keccakOut + ·)).orElse fun _ ↦ none) =
        ofK (laneLimb (stateLanes (keccakOutput layout q u)) 0 l?) := by
    rintro (_ | l) hl
    · exact ofK_zero.symm
    · simp only [Option.getD_some] at hl
      simp only [Option.map_some, Option.orElse_some, optCol, laneLimb, hl, dite_true, stateLanes]
      rw [tableValue, columnValue, show keccakOut = 33 from rfl, keccak_outCols l hl]
  obtain ⟨h1, h2⟩ := cellLanes_lt b cell hc
  rw [hlimb _ h1, hlimb _ h2, word_of_limbs]
  rfl

/-! ## The step -/

theorem keccakSlot_lt : ∀ c : Fin 13, keccakOffsetSlot (keccakPart c).1 < 16 := by decide

/-- Read cell `c`'s offset is its operand's slot, `g^step` past it. -/
theorem keccakInputCellOffset_eq (om : Fin 4 → K) (otail ob8 ocap oout : K) (inOdd outOdd : Bool)
    (outCells : KeccakOutputCells) (c : Fin 13) :
    keccakInputCellOffset om otail ob8 ocap c = g ^ (keccakPart c).2 *
      (instructionSlots (.keccak om otail ob8 ocap oout inOdd outOdd outCells))[
        keccakOffsetSlot (keccakPart c).1]'(keccakSlot_lt c) := by
  fin_cases c <;>
    simp [keccakInputCellOffset, keccakPart, keccakOffsetSlot, instructionSlots, instructionEntry]

theorem ofK_flag (b : Bool) : ofK (layoutFlagWord b) = if b then 1 else 0 := by
  cases b
  · exact ofK_zero
  · exact ofK_one

/-- **Every executed `KECCAK` row takes its leanISA step** under the link's relation and
`KeccakRel`. -/
theorem rowStep_keccak {program : LeanIsaProgram} {layout : Layout} {ρ : ℕ} {μ : ℕ}
    {q : Column μ} {chunks : Chunks} (hA : Announced (bytecodeWords program) layout ρ)
    (hM : MemoryHolds layout q chunks) (hP : ProgramHolds layout q chunks)
    (hK : KeccakRel layout q) (u : ℕ) (hu : u < tableRowCount layout 5) :
    RowStep program layout q ⟨⟨5, by decide⟩, ⟨u, hu⟩⟩ := by
  obtain ⟨-, hT, -⟩ := announced_facts hA
  obtain ⟨hk, -, hfetch, hop, hbc, hops⟩ := fetch_of_row hA hP (t := 5) (by decide) hu
  obtain ⟨hst, hmem, hopnd⟩ := keccak_links
  refine ⟨_, _, rowState_regs hT q _,
    rowNext_step hT q _ (by rw [tableAt_eq hT]; simp only [hst]), ?_⟩
  rw [step_of_fetch_eq_some hfetch]
  have hfp : (tableAt layout 5).links.stateLink.fp = 1 := by rw [tableAt_eq hT, hst]
  have hfpV : tableValue layout q 5 1 u = ofK (tableWord layout q 5 1 u) := by
    have := (tableValue_state hT q (t := 5) (by decide) u).2
    rwa [hfp] at this
  have hcol : ∀ c < 33, tableValue layout q 5 c u = ofK (tableWord layout q 5 c u) :=
    fun c hc ↦ tableValue_ofK q u (keccak_cols c hc)
  rw [tableAt_eq hT, hopnd] at hops
  have hopc : ∀ s c, ([s], Form.col c 0) ∈ [([11], Form.col 2 0), ([12], Form.col 3 0),
      ([13], Form.col 4 0), ([14], Form.col 5 0), ([15], Form.col 6 0)] →
      bcWord layout s (rowBc layout q chunks 5 u) = tableValue layout q 5 c u := fun s c hm ↦ by
    have := hops _ hm
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Form.col_evaluate, gpow_eq_ofK, pow_zero, ofK_one, one_mul] at this
    exact this
  have hrow : u < 2 ^ keccakHeight layout :=
    lt_of_lt_of_le hu (tableRows_le_height hA (t := 5) (by decide))
  generalize hI : program.instructions ⟨_, hk⟩ = ins at hop hbc
  cases ins with
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    have e11 := hopc 11 2 (by simp)
    have e12 := hopc 12 3 (by simp)
    have e13 := hopc 13 4 (by simp)
    have e14 := hopc 14 5 (by simp)
    have e15 := hopc 15 6 (by simp)
    rw [hbc 11 (by norm_num)] at e11
    have ho : ofK oout = tableValue layout q 5 2 u := e11
    rw [hbc 12 (by norm_num)] at e12
    rw [hbc 13 (by norm_num)] at e13
    rw [hbc 14 (by norm_num)] at e14
    rw [hbc 15 (by norm_num)] at e15
    have hin : tableValue layout q 5 3 u = if inOdd then 1 else 0 := by
      rw [← e12]; exact ofK_flag inOdd
    have hout : tableValue layout q 5 4 u = if outOdd then 1 else 0 := by
      rw [← e13]; exact ofK_flag outOdd
    show execute (memoryImage layout q)
      ⟨tableWord layout q 5 (tableAt layout 5).links.stateLink.pc u,
        tableWord layout q 5 (tableAt layout 5).links.stateLink.fp u⟩
      (.keccak om otail ob8 ocap oout inOdd outOdd outCells) =
      some ⟨g * tableWord layout q 5 (tableAt layout 5).links.stateLink.pc u,
        tableWord layout q 5 (tableAt layout 5).links.stateLink.fp u⟩
    rw [hfp]
    refine (execute_keccak_eq_some_iff _ _ _ _ _ _ _ _ _ _ _).mpr
      ⟨laneCells (keccakInLanes layout q u) inOdd (tableWord layout q 5 7 u),
        laneCells (stateLanes (keccakOutput layout q u)) outOdd 0, ?_, ?_, ?_, rfl⟩
    · intro c
      have ha : keccakReadAccess c ∈ (tableAt layout 5).links.memory := by
        rw [tableAt_eq hT, hmem]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr c.isLt, rfl⟩)
      have h := read_of_access hA hM (t := 5) (by decide) hu ha
        (by simp [accessGate, keccakReadAccess])
        (A := tableWord layout q 5 1 u * keccakInputCellOffset om otail ob8 ocap c) (by
          simp only [accessAddress, keccakReadAccess, Form.empty_evaluate, zero_add]
          rw [hbc _ (keccakSlot_lt c), hfp, hfpV,
            keccakInputCellOffset_eq om otail ob8 ocap oout inOdd outOdd outCells c, gpow_eq_ofK,
            ofK_mul, ofK_mul]
          ring)
      rw [h, readWord_eq u _ c.isLt inOdd hin]
    · intro c hc
      have ha : keccakWriteAccess c ∈ (tableAt layout 5).links.memory := by
        rw [tableAt_eq hT, hmem]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr c.isLt, rfl⟩)
      have hg : accessGate layout q 5 u (keccakWriteAccess c) ≠ 0 := by
        simp only [accessGate, keccakWriteAccess]
        split_ifs with h0 h1
        · exact one_ne_zero
        · show tableValue layout q 5 5 u ≠ 0
          rw [← e14]
          rcases outCells with _ | _ | _
          · simp only [KeccakOutputCells.cellCount] at hc; omega
          · show ofK (1 : K) ≠ 0
            rw [ofK_one]; exact one_ne_zero
          · show ofK (1 : K) ≠ 0
            rw [ofK_one]; exact one_ne_zero
        · show tableValue layout q 5 6 u ≠ 0
          rw [← e15]
          rcases outCells with _ | _ | _
          · simp only [KeccakOutputCells.cellCount] at hc; omega
          · simp only [KeccakOutputCells.cellCount] at hc; omega
          · show ofK (1 : K) ≠ 0
            rw [ofK_one]; exact one_ne_zero
      have h := read_of_access hA hM (t := 5) (by decide) hu ha hg
        (A := tableWord layout q 5 1 u * (g ^ c.val * oout)) (by
          simp only [accessAddress, keccakWriteAccess, add_zero]
          rw [Form.prod_evaluate, hfpV, ← ho, gpow_eq_ofK, ofK_mul, ofK_mul]
          ring)
      rw [h, writeWord_eq u _ c.isLt outOdd hout]
    · intro c _
      rw [stateOfCells_laneCells, keccakInput_eq hA q u, ← keccakOutput_of_keccakRel hK hrow,
        cellsOfState_eq_laneCells]
  | _ => simp [opIndex, LeanIsaInstruction.opcode] at hop

/-- **`KECCAK`'s rows take their leanISA step** under the link's relation and `KeccakRel`. -/
theorem keccakRowSteps_of_rel {program : LeanIsaProgram} {layout : Layout} {ρ : ℕ} {μ : ℕ}
    {q : Column μ} (hA : Announced (bytecodeWords program) layout ρ) (hrel : LinkRel layout q)
    (hK : KeccakRel layout q) : KeccakRowSteps program layout q := by
  obtain ⟨chunks, -, -, -, hM, hP, -⟩ := hrel
  exact fun u hu ↦ rowStep_keccak hA hM hP hK u hu

end

end LeanVM.Protocol.Relation
