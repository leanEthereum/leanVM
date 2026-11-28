/-
  LeanVM.Prover.Complete.Link.BalanceKeccak

  An honest `KECCAK` row's share of the index balance is zero.
-/

module

public import LeanVM.Prover.Complete.Link.BalanceRows
public import LeanVM.Semantics.KeccakCells
import LeanVM.Semantics.Lemmas

/-!
# The honest `KECCAK` rows balance

A `KECCAK` row's thirteen read cells hold its input state's lanes in the input layout, the limb
holding no lane its `free` column (`laneCells_stateOfCells`), and its written cells the output
state's in the output layout (`cellsOfState_eq_laneCells`); each access's committed value is
`layout_limb` of those lane columns under the layout flag (`layoutLimb_eval`), so it is the word
at its cell. A written cell past those the instruction writes has its gate zero.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Extraction LeanVM.Protocol.Relation

/-! ## Layout limbs -/

/-- A column read through an optional index, `0` for none. -/
def optVal (col : ℕ → E) : Option ℕ → E
  | some i => col i
  | none => 0

theorem prod_eval (a b e : ℕ) (col : ℕ → E) :
    (Form.prod a b e).evaluate col = gpow e * col a * col b := by
  simp only [Form.prod, Form.evaluate, sumE, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_nil, zero_add]
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]; ring

theorem sum_eval (col : ℕ → E) (fs : List Form) :
    (Form.sum fs).evaluate col = (fs.map (·.evaluate col)).sum := by
  unfold Form.sum
  suffices h : ∀ (f : Form), (fs.foldl Form.add f).evaluate col = f.evaluate col + (fs.map (·.evaluate col)).sum by
    rw [h, Form.evaluate_empty, zero_add]
  induction fs with
  | nil => intro f; simp
  | cons f' fs ih =>
    intro f
    rw [List.foldl_cons, ih, Form.add, Form.evaluate_addScaled]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- **A layout limb** reads its even column under flag `0`, its odd one under flag `1`. -/
theorem layoutLimb_eval (e o : Option ℕ) (flag : ℕ) (missing : Option ℕ) (col : ℕ → E)
    (hf : col flag = 0 ∨ col flag = 1) :
    (layoutLimb e o flag missing).evaluate col =
      if col flag = 0 then optVal col (e.orElse fun _ ↦ missing)
      else optVal col (o.orElse fun _ ↦ missing) := by
  have h2 : (2 : E) = 0 := LeanVM.Protocol.Tables.two_eq_zero_E
  unfold layoutLimb
  dsimp only
  generalize e.orElse (fun _ ↦ missing) = a
  generalize o.orElse (fun _ ↦ missing) = b
  split_ifs with hab h0 h0
  · subst hab; cases a <;> simp [optVal, Form.evaluate_const, col_eval]
  · subst hab; cases a <;> simp [optVal, Form.evaluate_const, col_eval]
  · rw [sum_eval]
    rcases a with _ | a <;> rcases b with _ | b <;>
      simp [optVal, col_eval, prod_eval, gpow_zero', h0]
  · have h1 : col flag = 1 := hf.resolve_left h0
    rw [sum_eval]
    rcases a with _ | a <;> rcases b with _ | b <;>
      simp [optVal, col_eval, prod_eval, gpow_zero', h1]
    · linear_combination col a * h2
    · linear_combination col a * h2

/-! ## `KECCAK`'s accesses -/

/-- A cell's committed value: its two limbs' layout limbs over the lane columns from `lanes`. -/
def kValue (lanes flag : ℕ) (missing : Option ℕ) (cell : ℕ) : Form :=
  let lane := fun (l : Option ℕ) ↦ l.map (lanes + ·)
  let limb := fun (e o : Option ℕ) ↦ layoutLimb (lane e) (lane o) flag missing
  let e := (keccakCellLanes false).getD cell (none, none)
  let o := (keccakCellLanes true).getD cell (none, none)
  (limb e.1 o.1).addScaled (limb e.2 o.2) eY

/-- A read cell's operand and its step past the operand's cell. -/
def kPart (cell : ℕ) : ℕ × ℕ :=
  if cell < 4 then (cell, 0) else if cell < 8 then (4, cell - 4) else if cell = 8 then (5, 0)
  else (6, cell - 9)

/-- Read cell `c`'s access. -/
def kRead (cell : ℕ) : Access :=
  ⟨58 + (kPart cell).1, (kPart cell).2, none, {}, some (4 + (kPart cell).1, (kPart cell).2),
    kValue 8 3 (some 7) cell, []⟩

/-- Written cell `c`'s access. -/
def kWrite (cell : ℕ) : Access :=
  ⟨65, cell, if cell = 0 then none else if cell = 1 then some 5 else some 6, Form.prod 1 2 cell, none,
    kValue 33 4 none cell, []⟩

theorem keccak_memory : (tables.getD opKeccak default).links.memory =
    (List.range 13).map kRead ++ (List.range 13).map kWrite := rfl

/-! ## A `KECCAK` row -/

/-- A `KECCAK` row's head columns and lanes. -/
theorem keccak_row_cols {κ : ℕ} (ctx : FillCtx κ) (k : ℕ) (pc fp : K) (slot : ℕ) (om : Fin 4 → K)
    (otail ob8 ocap oout : K) (inOdd outOdd : Bool) (outCells : KeccakOutputCells) :
    let row := rowOf ctx k ⟨pc, fp, slot, .keccak om otail ob8 ocap oout inOdd outOdd outCells⟩
    let input := keccakInputIn ctx.memIdx ctx.img fp om otail ob8 ocap
    let S := stateOfCells input inOdd
    row.getD 0 0 = pc ∧ row.getD 1 0 = fp ∧ row.getD 2 0 = oout ∧
      row.getD 3 0 = layoutFlagWord inOdd ∧ row.getD 4 0 = layoutFlagWord outOdd ∧
      row.getD 7 0 = (if inOdd then (input 0).limb 0 else (input 8).limb 1) ∧
      (∀ l, l < 25 → row.getD (8 + l) 0 = laneK S l) ∧
      ∀ l, l < 25 → row.getD (33 + l) 0 = laneK (keccakF1600 S) l := by
  intro row input S
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun l hl ↦ ?_, fun l hl ↦ ?_⟩
  rotate_left 6
  · simp only [row, rowOf, Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.size_append,
      Array.size_ofFn, List.size_toArray, List.length_map, List.length_cons, List.length_nil]
    split_ifs <;> first | omega | simp [input, S, hl, show 8 + l - 8 = l by omega]
  · simp only [row, rowOf, Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.size_append,
      Array.size_ofFn, List.size_toArray, List.length_map, List.length_cons, List.length_nil]
    split_ifs <;> first | omega | simp [input, S, hl, show 33 + l - (8 + 25) = l by omega]
  all_goals simp only [row, rowOf, Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.size_append,
      Array.size_ofFn, List.size_toArray, List.length_map, List.length_cons, List.length_nil]
  all_goals simp [input]

/-! ## A cell's committed value -/

theorem keccakCellLanes_getD (odd : Bool) {c : ℕ} (hc : c < 13) :
    (keccakCellLanes odd).getD c (none, none) = cellLanes odd c := by
  simp [keccakCellLanes, cellLanes, List.getD_eq_getElem?_getD, keccakCells, hc]

theorem cellLanes_lt (odd : Bool) {c : ℕ} (hc : c < 13) :
    (∀ l ∈ (cellLanes odd c).1, l < 25) ∧ ∀ l ∈ (cellLanes odd c).2, l < 25 := by
  unfold cellLanes
  split_ifs <;> simp <;> omega

theorem lane_opt (col : ℕ → E) (lanes : ℕ) (missing : Option ℕ) (L : Fin 25 → K) (free : K)
    (hL : ∀ l (hl : l < 25), col (lanes + l) = ofK (L ⟨l, hl⟩)) (hm : optVal col missing = ofK free)
    (x : Option ℕ) (hx : ∀ l ∈ x, l < 25) :
    optVal col ((x.map (lanes + ·)).orElse fun _ ↦ missing) = ofK (laneLimb L free x) := by
  cases x with
  | none => simpa [optVal, laneLimb] using hm
  | some l =>
    have hl := hx l rfl
    simp [optVal, laneLimb, hl, hL l hl]

/-- **A cell's committed value is the word of its lanes** in the layout its flag names. -/
theorem kValue_eval (lanes flag : ℕ) (missing : Option ℕ) (col : ℕ → E) (L : Fin 25 → K) (free : K)
    (odd : Bool) (hf : col flag = ofK (layoutFlagWord odd))
    (hL : ∀ l (hl : l < 25), col (lanes + l) = ofK (L ⟨l, hl⟩)) (hm : optVal col missing = ofK free)
    {c : ℕ} (hc : c < 13) :
    (kValue lanes flag missing c).evaluate col = laneCells L odd free ⟨c, hc⟩ := by
  have hfl : col flag = 0 ∨ col flag = 1 := by
    cases odd
    · simp [layoutFlagWord, hf]
    · simp [layoutFlagWord, hf]
  unfold kValue
  dsimp only
  rw [Form.evaluate_addScaled, layoutLimb_eval _ _ _ _ _ hfl, layoutLimb_eval _ _ _ _ _ hfl,
    keccakCellLanes_getD _ hc, keccakCellLanes_getD _ hc, laneCells, ← word_of_limbs]
  have hlt := cellLanes_lt odd hc
  cases odd
  · have h0 : col flag = 0 := by simp [hf, layoutFlagWord]
    rw [ite_eq_left h0, ite_eq_left h0, lane_opt col lanes missing L free hL hm _ hlt.1,
      lane_opt col lanes missing L free hL hm _ hlt.2]
  · have h0 : col flag ≠ 0 := by simp [hf, layoutFlagWord]
    rw [ite_eq_right h0, ite_eq_right h0, lane_opt col lanes missing L free hL hm _ hlt.1,
      lane_opt col lanes missing L free hL hm _ hlt.2]

/-! ## `KECCAK`'s accesses balance -/

/-- `acc_of_cell` for an access whose gate is one. -/
theorem acc_of_cell1 (ch : LinkChallenges) {κ : ℕ} (img : MemoryImage κ) (col : ℕ → E) (B : ℕ → E)
    (fp G : E) (Z Y : ℕ → E) (a : Access) (c : ℕ) (hc : c < 2 ^ κ)
    (hY : Y c = ch.gammaMem.getD 0 0 * gpow c + ch.gammaMem.getD 1 0 * img ⟨c, hc⟩ + ch.gammaMem.getD 3 0)
    (hg : gateOf col a = 1)
    (haddr : a.address.evaluate col + frameVal B fp a = gpow c)
    (hval : a.value.evaluate col + ((a.reads.map (readWordVal Z col)).sum +
      (a.reads.map (readProgVal B fp G)).sum) = img ⟨c, hc⟩) :
    gateOf col a * Y c = gateOf col a * committedOf ch col a + ch.gammaMem.getD 0 0 * frameVal B fp a +
      ch.gammaMem.getD 1 0 * ((a.reads.map (readWordVal Z col)).sum +
        (a.reads.map (readProgVal B fp G)).sum) := by
  rw [hg, hY, ← haddr, ← hval, committedOf]
  ring

/-- A read cell of a `KECCAK` row reads the word at its cell. -/
theorem acc_kread (ch : LinkChallenges) {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) {chunks : Chunks}
    (hc : ChunksOK chunks) (hκw : κ ≤ chunks.width) (row : Array K) (Z Y B : ℕ → E) (G : E)
    (fp o : K) (c : ℕ) (hc13 : c < 13)
    (hY : ∀ j (hj : j < 2 ^ κ), Y j = ch.gammaMem.getD 0 0 * gpow j + ch.gammaMem.getD 1 0 * img ⟨j, hj⟩ +
      ch.gammaMem.getD 3 0)
    (hfp : rowCol row 1 = ofK fp)
    (hrow : row.getD (58 + (kPart c).1) 0 = (⟨powIndex κ, img, chunks⟩ : FillCtx κ).cell (fp * o))
    (hB : B (4 + (kPart c).1) = ofK o) {v0 vc : E} (h0 : img.read (fp * o) = some v0)
    (hr : img.read (fp * (g ^ (kPart c).2 * o)) = some vc)
    (hval : (kValue 8 3 (some 7) c).evaluate (rowCol row) = vc) :
    gateOf (rowCol row) (kRead c) * Y (rowPtr chunks row (kRead c).pointer + (kRead c).shift) =
      gateOf (rowCol row) (kRead c) * committedOf ch (rowCol row) (kRead c) +
        ch.gammaMem.getD 0 0 * frameVal B (rowCol row 1) (kRead c) +
        ch.gammaMem.getD 1 0 * (((kRead c).reads.map (readWordVal Z (rowCol row))).sum +
          ((kRead c).reads.map (readProgVal B (rowCol row 1) G)).sum) := by
  obtain ⟨i, hi, -, hxi⟩ := read_cell hκ img h0
  obtain ⟨j, hj, hvj, -⟩ := read_cell hκ img hr
  have hs : (kPart c).2 < 64 := by unfold kPart; split_ifs <;> simp <;> omega
  have hji := index_shift hκ (s := (kPart c).2) i.isLt j.isLt hs hi (by rw [← hj]; ring)
  have hp : rowPtr chunks row (kRead c).pointer = i := rowPtr_cell hκ img hc hκw hrow hxi
  have hsh : (kRead c).shift = (kPart c).2 := rfl
  rw [hp, hsh, ← hji]
  refine acc_of_cell ch img _ _ _ _ _ _ _ j j.isLt (hY _ _) rfl ?_ ?_
  · show ({} : Form).evaluate (rowCol row) + rowCol row 1 * (gpow (kPart c).2 * B (4 + (kPart c).1)) = gpow j
    rw [Form.evaluate_empty, zero_add, hfp, hB, frame_gpow hi, hji, gpow, gpow, gpow, pow_add]
    ring
  · show (kValue 8 3 (some 7) c).evaluate (rowCol row) + (([] : List E).sum + ([] : List E).sum) = _
    rw [List.sum_nil, add_zero, add_zero, hval, hvj]

/-- A written cell of a `KECCAK` row, written, holds the word at its cell. -/
theorem acc_kwrite (ch : LinkChallenges) {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) {chunks : Chunks}
    (hc : ChunksOK chunks) (hκw : κ ≤ chunks.width) (row : Array K) (Z Y B : ℕ → E) (G : E)
    (fp oout : K) (c : ℕ)
    (hY : ∀ j (hj : j < 2 ^ κ), Y j = ch.gammaMem.getD 0 0 * gpow j + ch.gammaMem.getD 1 0 * img ⟨j, hj⟩ +
      ch.gammaMem.getD 3 0)
    (hfp : rowCol row 1 = ofK fp) (hout : rowCol row 2 = ofK oout)
    (hrow : row.getD 65 0 = (⟨powIndex κ, img, chunks⟩ : FillCtx κ).cell (fp * oout))
    (hg : gateOf (rowCol row) (kWrite c) = 1) (hc13 : c < 13) {v0 vc : E}
    (h0 : img.read (fp * oout) = some v0) (hr : img.read (fp * (g ^ c * oout)) = some vc)
    (hval : (kValue 33 4 none c).evaluate (rowCol row) = vc) :
    gateOf (rowCol row) (kWrite c) * Y (rowPtr chunks row (kWrite c).pointer + (kWrite c).shift) =
      gateOf (rowCol row) (kWrite c) * committedOf ch (rowCol row) (kWrite c) +
        ch.gammaMem.getD 0 0 * frameVal B (rowCol row 1) (kWrite c) +
        ch.gammaMem.getD 1 0 * (((kWrite c).reads.map (readWordVal Z (rowCol row))).sum +
          ((kWrite c).reads.map (readProgVal B (rowCol row 1) G)).sum) := by
  obtain ⟨i, hi, -, hxi⟩ := read_cell hκ img h0
  obtain ⟨j, hj, hvj, -⟩ := read_cell hκ img hr
  have hji := index_shift hκ (s := c) i.isLt j.isLt (by omega) hi (by rw [← hj]; ring)
  have hp : rowPtr chunks row (kWrite c).pointer = i := rowPtr_cell hκ img hc hκw hrow hxi
  have hsh : (kWrite c).shift = c := rfl
  rw [hp, hsh, ← hji]
  refine acc_of_cell1 ch img _ _ _ _ _ _ _ j j.isLt (hY _ _) hg ?_ ?_
  · show (Form.prod 1 2 c).evaluate (rowCol row) + 0 = gpow j
    rw [prod_eval, add_zero, hfp, hout, mul_assoc, ← ofK_mul, hi, ofK_gpow, hji, gpow, gpow, gpow,
      pow_add]
    ring
  · show (kValue 33 4 none c).evaluate (rowCol row) + (([] : List E).sum + ([] : List E).sum) = _
    rw [List.sum_nil, add_zero, add_zero, hval, hvj]

/-- A written cell past those the instruction writes: its gate is zero. -/
theorem acc_kwrite0 (ch : LinkChallenges) (row : Array K) (Z Y B : ℕ → E) (G : E) (t c : ℕ)
    (hg : gateOf (rowCol row) (kWrite c) = 0) :
    gateOf (rowCol row) (kWrite c) * Y t =
      gateOf (rowCol row) (kWrite c) * committedOf ch (rowCol row) (kWrite c) +
        ch.gammaMem.getD 0 0 * frameVal B (rowCol row 1) (kWrite c) +
        ch.gammaMem.getD 1 0 * (((kWrite c).reads.map (readWordVal Z (rowCol row))).sum +
          ((kWrite c).reads.map (readProgVal B (rowCol row 1) G)).sum) := by
  rw [hg]
  simp [frameVal, kWrite]

/-! ## A `KECCAK` row's cells -/

/-- `KECCAK`'s operand `p`: `m_0 … m_3`, `tail`, `b8`, `cap`, `out`. -/
def opnd (om : Fin 4 → K) (otail ob8 ocap oout : K) (p : ℕ) : K :=
  [om 0, om 1, om 2, om 3, otail, ob8, ocap, oout].getD p 0

/-- Read cell `c` is `s` cells past its operand's, the operand's first cell `c0`. -/
theorem kread_facts (om : Fin 4 → K) (otail ob8 ocap oout : K) {c : ℕ} (hc : c < 13) :
    keccakInputCellOffset om otail ob8 ocap ⟨c, hc⟩ = g ^ (kPart c).2 * opnd om otail ob8 ocap oout (kPart c).1 ∧
      (∃ c0 : Fin 13, keccakInputCellOffset om otail ob8 ocap c0 = opnd om otail ob8 ocap oout (kPart c).1) ∧
      (kPart c).1 < 7 := by
  interval_cases c
  all_goals refine ⟨by simp [keccakInputCellOffset, kPart, opnd], ?_, by simp [kPart]⟩
  · exact ⟨0, by simp [keccakInputCellOffset, kPart, opnd]⟩
  · exact ⟨1, by simp [keccakInputCellOffset, kPart, opnd]⟩
  · exact ⟨2, by simp [keccakInputCellOffset, kPart, opnd]⟩
  · exact ⟨3, by simp [keccakInputCellOffset, kPart, opnd]⟩
  iterate 4 exact ⟨4, by simp [keccakInputCellOffset, kPart, opnd]⟩
  · exact ⟨8, by simp [keccakInputCellOffset, kPart, opnd]⟩
  all_goals exact ⟨9, by simp [keccakInputCellOffset, kPart, opnd]⟩

/-- A written cell's gate: one for the cells the instruction writes, zero past them. -/
theorem kgate (outCells : KeccakOutputCells) {c : ℕ} (hc : c < 13) (row : Array K)
    (h5 : rowCol row 5 = ofK (keccakOutputFlags outCells).1)
    (h6 : rowCol row 6 = ofK (keccakOutputFlags outCells).2) :
    gateOf (rowCol row) (kWrite c) = if c < outCells.cellCount then 1 else 0 := by
  unfold gateOf kWrite
  interval_cases c <;> cases outCells <;>
    simp [h5, h6, keccakOutputFlags, layoutFlagWord, KeccakOutputCells.cellCount]

/-! ## `KECCAK` -/

theorem keccak_operands : (tables.getD 5 default).links.bytecodeLink.operands =
    [([11], Form.col 2 0), ([12], Form.col 3 0), ([13], Form.col 4 0), ([14], Form.col 5 0),
      ([15], Form.col 6 0)] := rfl

theorem share_keccak (ch : LinkChallenges) {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) {chunks : Chunks}
    (hc : ChunksOK chunks) (hκw : κ ≤ chunks.width) (ω : E) (k σ : ℕ) (hσ : σ < 2 ^ chunks.width)
    (r r' : Registers K) (om : Fin 4 → K) (otail ob8 ocap oout : K) (inOdd outOdd : Bool)
    (outCells : KeccakOutputCells) (hpc : r.pc = addressOfIndex σ)
    (hex : executeWith img.read r (.keccak om otail ob8 ocap oout inOdd outOdd outCells) = some r')
    (Y X words P : ℕ → E)
    (hT : TargetsOK ch img 5 σ (slotE (.keccak om otail ob8 ocap oout inOdd outOdd outCells)) Y X words P) :
    rowBal ch (tables.getD 5 default) (ch.mu.getD 5 [])
      (rowCol (rowOf ⟨powIndex κ, img, chunks⟩ k
        ⟨r.pc, r.fp, σ, .keccak om otail ob8 ocap oout inOdd outOdd outCells⟩)) ω
      (fun a ↦ rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k
        ⟨r.pc, r.fp, σ, .keccak om otail ob8 ocap oout inOdd outOdd outCells⟩) a.pointer + a.shift)
      (rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k
        ⟨r.pc, r.fp, σ, .keccak om otail ob8 ocap oout inOdd outOdd outCells⟩))
      (rowPtr chunks (rowOf ⟨powIndex κ, img, chunks⟩ k
        ⟨r.pc, r.fp, σ, .keccak om otail ob8 ocap oout inOdd outOdd outCells⟩)
        (tables.getD 5 default).links.bytecodeLink.pointer) Y X words P = 0 := by
  obtain ⟨input, output, hin, hout, hrel, -⟩ :=
    (execute_keccak_eq_some_iff img r om otail ob8 ocap oout inOdd outOdd outCells r').mp hex
  have hinput : keccakInputIn (powIndex κ) img r.fp om otail ob8 ocap = input := by
    funext c
    show (readIn (powIndex κ) img _).getD 0 = _
    rw [show readIn (powIndex κ) img = img.read from funext fun a ↦ by
      rw [readIn, gLogIn_powIndex hκ]; rfl, hin c]
    rfl
  obtain ⟨r0, r1, r2, r3, r4, r7, rin, rout⟩ :=
    keccak_row_cols ⟨powIndex κ, img, chunks⟩ k r.pc r.fp σ om otail ob8 ocap oout inOdd outOdd outCells
  obtain ⟨p58, p59, p60, p61, p62, p63, p64, p65, p66, -⟩ :=
    keccak_row_ptrs ⟨powIndex κ, img, chunks⟩ k r.pc r.fp σ om otail ob8 ocap oout inOdd outOdd outCells
  obtain ⟨f5, f6⟩ :=
    keccak_row_flags ⟨powIndex κ, img, chunks⟩ k r.pc r.fp σ om otail ob8 ocap oout inOdd outOdd outCells
  dsimp only at r0 r1 r2 r3 r4 r7 rin rout p58 p59 p60 p61 p62 p63 p64 p65 p66 f5 f6
  simp only [hinput] at r7 rin rout
  generalize hrow : rowOf ⟨powIndex κ, img, chunks⟩ k
    ⟨r.pc, r.fp, σ, .keccak om otail ob8 ocap oout inOdd outOdd outCells⟩ = row at *
  have c1 : rowCol row 1 = ofK r.fp := by rw [rowCol, r1]
  have c2 : rowCol row 2 = ofK oout := by rw [rowCol, r2]
  have c3 : rowCol row 3 = ofK (layoutFlagWord inOdd) := by rw [rowCol, r3]
  have c4 : rowCol row 4 = ofK (layoutFlagWord outOdd) := by rw [rowCol, r4]
  have c5 : rowCol row 5 = ofK (keccakOutputFlags outCells).1 := by rw [rowCol, f5]
  have c6 : rowCol row 6 = ofK (keccakOutputFlags outCells).2 := by rw [rowCol, f6]
  have c7 : rowCol row 7 = ofK (freeLimb input inOdd) := by
    rw [rowCol, r7]; cases inOdd <;> rfl
  have cin : ∀ l (hl : l < 25), rowCol row (8 + l) = ofK (stateLanes (stateOfCells input inOdd) ⟨l, hl⟩) :=
    fun l hl ↦ by rw [rowCol, rin l hl]; rfl
  have cout : ∀ l (hl : l < 25),
      rowCol row (33 + l) = ofK (stateLanes (keccakF1600 (stateOfCells input inOdd)) ⟨l, hl⟩) :=
    fun l hl ↦ by rw [rowCol, rout l hl]; rfl
  have hopnd : ∀ p < 7, row.getD (58 + p) 0 =
      (⟨powIndex κ, img, chunks⟩ : FillCtx κ).cell (r.fp * opnd om otail ob8 ocap oout p) := by
    intro p hp
    interval_cases p
    · exact p58
    · exact p59
    · exact p60
    · exact p61
    · exact p62
    · exact p63
    · exact p64
  have hslot : ∀ p < 7, slotE (.keccak om otail ob8 ocap oout inOdd outOdd outCells) (4 + p) =
      ofK (opnd om otail ob8 ocap oout p) := by
    intro p hp
    interval_cases p <;> simp [slotE, instructionSlots, instructionEntry, opnd]
  have hcount : 0 < outCells.cellCount := by cases outCells <;> decide
  have h0out : img.read (r.fp * oout) = some (output ⟨0, by omega⟩) := by
    have := hout ⟨0, by omega⟩ hcount
    rwa [pow_zero, one_mul] at this
  refine share_of ch img chunks 5 row ω σ _ Y X words P ?_ hT ?_
    (show ofK (addressOfIndex 5) = gpow 5 from ofK_gpow 5) ?_ (by decide +kernel) (by decide +kernel) ?_
  · rw [show (tables.getD 5 default).links.bytecodeLink.pointer = 66 from rfl, rowPtr, p66]
    exact headD_indices_encode hc hσ
  · rw [show (tables.getD 5 default).links.bytecodeLink.pc = 0 from rfl, rowCol, r0, hpc, ofK_gpow]
  · intro op hop
    rw [keccak_operands] at hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, col_eval]
    · rw [c2]; rfl
    · rw [c3]; rfl
    · rw [c4]; rfl
    · rw [c5]; rfl
    · rw [c6]; rfl
  · intro a ha
    rw [show (tables.getD 5 default).links.stateLink.fp = 1 from rfl]
    rw [show (5 : ℕ) = opKeccak from rfl, keccak_memory] at ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨c, hc', rfl⟩ := List.mem_map.mp ha
      have hc13 := List.mem_range.mp hc'
      obtain ⟨hF1, ⟨c0, hF2⟩, hp7⟩ := kread_facts om otail ob8 ocap oout hc13
      refine acc_kread ch hκ img hc hκw row _ Y _ _ r.fp (opnd om otail ob8 ocap oout (kPart c).1) c hc13
        hT.1 c1 (hopnd _ hp7) (hslot _ hp7) (v0 := input c0) (vc := input ⟨c, hc13⟩)
        (by rw [← hF2]; exact hin c0) (by rw [← hF1]; exact hin _) ?_
      rw [kValue_eval 8 3 (some 7) _ (stateLanes (stateOfCells input inOdd)) (freeLimb input inOdd) inOdd
        c3 cin c7 hc13, laneCells_stateOfCells]
    · obtain ⟨c, hc', rfl⟩ := List.mem_map.mp ha
      have hc13 := List.mem_range.mp hc'
      have hg := kgate outCells hc13 row c5 c6
      by_cases hcc : c < outCells.cellCount
      · rw [ite_eq_left hcc] at hg
        refine acc_kwrite ch hκ img hc hκw row _ Y _ _ r.fp oout c hT.1 c1 c2 p65 hg hc13 h0out
          (hout ⟨c, hc13⟩ hcc) ?_
        rw [kValue_eval 33 4 none _ (stateLanes (keccakF1600 (stateOfCells input inOdd))) 0 outOdd c4 cout
          (by simp [optVal]) hc13, hrel ⟨c, hc13⟩ hcc, cellsOfState_eq_laneCells]
      · rw [ite_eq_right hcc] at hg
        exact acc_kwrite0 ch row _ Y _ _ _ c hg

end LeanVM.Prover.Complete

end
