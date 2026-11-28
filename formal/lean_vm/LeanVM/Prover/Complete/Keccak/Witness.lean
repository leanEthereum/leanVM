/-
  LeanVM.Prover.Complete.Keccak.Witness

  What the honest witness's `q_keccak` column and `KECCAK` output columns hold: the statements the
  Keccak reduction's completeness starts from.
-/

module

public import LeanVM.Prover.Complete.Prefix
public import LeanVM.Prover.Complete.Keccak.Exec.Mle
public import LeanVM.Protocol.Keccak.Candidate
public import LeanVM.Protocol.Relation.Placement

/-!
# The witness's Keccak columns

The witness (`witness?`, `Statement/Prover/Columns.lean`) writes `q_keccak` slot by slot over the
`KECCAK` table's rows `R` at the height `2^h`: slot `l < 25` the rows' input lanes (zero past the
rows), slot `25 + l` lane `l` of the state twelve rounds in (`segment 0`, of the zero state past
the rows). Every row of the table holds a state's lanes as its input and the permutation's lanes as
its output (`kRow_rowsOf`), and a padding row the zero state's permutation (`paddingRow_out`).

* `midAgree_witness`: the committed middle state is twelve rounds of the input, at every step, so
  at every point.
* `outClaimsTrueMid_witness`: the output columns' extensions at a point are the last twelve rounds
  from the committed middle state's.
* `mleK_eq_sum`, `mleA_bitSlice`: the extensions of a column and of its bit slices as sums.
-/

@[expose] public section

namespace LeanVM.Prover.Complete.Keccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Prover Finset
open LeanVM.Protocol.KeccakGkr (eqAt bitE stepMle laneWord roundsFrom outClaimsTrueMid midAgree)

/-! ## Extensions as sums -/

theorem mleK_eq_sum (t : Array K) (pt : List E) (ht : t.size = 2 ^ pt.length) :
    mleK t pt = ∑ w ∈ range (2 ^ pt.length), eqAt pt w * ofK (t.getD w 0) := by
  rw [mleK_eq, LeanVM.Protocol.KeccakGkr.multilinearEval_eq pt _ (by simp [ht])]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  have hw' : w < t.size := ht ▸ Finset.mem_range.1 hw
  simp [List.getD_eq_getElem?_getD, hw', Array.getD_eq_getD_getElem?]

theorem mleA_bitSlice (col : Array K) (pt : List E) (ht : col.size = 2 ^ pt.length) (i : ℕ) :
    mleA (bitSlice col i) pt =
      ∑ w ∈ range (2 ^ pt.length), eqAt pt w * bitE ((col.getD w 0).toBitVec.getLsbD i) := by
  rw [mleA_eq, LeanVM.Protocol.KeccakGkr.multilinearEval_eq pt _ (by simp [bitSlice, ht])]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  have hw' : w < col.size := ht ▸ Finset.mem_range.1 hw
  simp only [bitSlice, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, Array.toList_map,
    List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hw', Option.map_some,
    Option.getD_some]
  cases (col[w]'hw').toBitVec.getLsbD i <;> rfl

/-! ## Arrays -/

theorem getD_append_left {α : Type} (a b : Array α) {i : ℕ} (h : i < a.size) (d : α) :
    (a ++ b).getD i d = a.getD i d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_left h]

theorem getD_append_right {α : Type} (a b : Array α) {i : ℕ} (h : a.size ≤ i) (d : α) :
    (a ++ b).getD i d = b.getD (i - a.size) d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_right h]

theorem getD_ofFn' {α : Type} {n : ℕ} (f : Fin n → α) {i : ℕ} (h : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem lane_laneK (S : KeccakState) (l : ℕ) : K.lane (laneK S l) = Keccak.lane S l := by
  simp [K.lane, laneK, K.ofLane, BF64.toBitVec_ofBitVec]

/-! ## The rows of the `KECCAK` table -/

theorem keccakIn_eq : keccakIn = 8 := rfl

theorem keccakOut_eq : keccakOut = 33 := rfl

/-- A row of the `KECCAK` table: its input lanes a state's, its output lanes the permutation's. -/
def KRow (r : Array K) : Prop :=
  ∃ S : KeccakState, (∀ l < 25, r.getD (keccakIn + l) 0 = laneK S l) ∧
    ∀ l < 25, r.getD (keccakOut + l) 0 = laneK (keccakF1600 S) l

theorem kRow_rowOf {κ : ℕ} (ctx : FillCtx κ) (cycle : ℕ) (st : Step)
    (h : opTableIdx st.ins.opcode = opKeccak) : KRow (rowOf ctx cycle st) := by
  obtain ⟨pc, fp, slot, ins⟩ := st
  cases ins with
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    simp only [rowOf]
    refine ⟨stateOfCells (keccakInputIn ctx.memIdx ctx.img fp om otail ob8 ocap) inOdd,
      fun l hl ↦ ?_, fun l hl ↦ ?_⟩
    · rw [keccakIn_eq, getD_append_left _ _ (by simp; omega), getD_append_left _ _ (by simp; omega),
        getD_append_left _ _ (by simp; omega), getD_append_right _ _ (by simp),
        getD_ofFn' _ (by simp; omega)]
      simp
    · rw [keccakOut_eq, getD_append_left _ _ (by simp; omega), getD_append_left _ _ (by simp; omega),
        getD_append_right _ _ (by simp), getD_ofFn' _ (by simp; omega)]
      simp
  | _ => simp [LeanIsaInstruction.opcode, opTableIdx, opKeccak, opXor, opMul, opSet, opDeref,
      opJump] at h

theorem getD_modify_of_ne {α : Type} (a : Array α) {i j : ℕ} (hij : i ≠ j) (f : α → α) (d : α) :
    (a.modify i f).getD j d = a.getD j d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_modify, hij]

theorem getD_modify_self {α : Type} (a : Array α) (i : ℕ) (x : α → α) (d : α) :
    (a.modify i x).getD i d = if i < a.size then x (a.getD i d) else a.getD i d := by
  by_cases hi : i < a.size
  · simp [Array.getD_eq_getD_getElem?, hi, Array.getElem_modify]
  · simp [Array.getD_eq_getD_getElem?, hi]

theorem mem_getD_modify {α : Type} (a : Array (Array α)) (i : ℕ) (x : Array α → Array α)
    {r : α} (hr : r ∈ (a.modify i x).getD i #[]) : r ∈ x (a.getD i #[]) ∨ (r ∈ a.getD i #[]) := by
  rw [getD_modify_self] at hr
  by_cases hi : i < a.size
  · simp only [hi, ↓reduceIte] at hr
    exact Or.inl hr
  · simp only [hi, ↓reduceIte] at hr
    exact Or.inr hr

/-- **Every row of the `KECCAK` table is a permutation's.** -/
theorem kRow_rowsOf {κ : ℕ} (ctx : FillCtx κ) (steps : Array Step) :
    ∀ r ∈ (rowsOf ctx steps).getD opKeccak #[], KRow r := by
  unfold rowsOf
  rw [← Array.foldl_toList]
  suffices h : ∀ (L : List (Step × ℕ)) (tabs : Array (Array (Array K))),
      (∀ r ∈ tabs.getD opKeccak #[], KRow r) →
      ∀ r ∈ (L.foldl (fun tabs (p : Step × ℕ) ↦
        tabs.modify (opTableIdx p.1.ins.opcode) (·.push (rowOf ctx p.2 p.1))) tabs).getD
          opKeccak #[], KRow r from
    h _ _ (by simp [Array.getD_eq_getD_getElem?, nTables, opKeccak])
  intro L
  induction L with
  | nil => intro tabs h; exact h
  | cons p L ih =>
    intro tabs h
    refine ih _ fun r hr ↦ ?_
    dsimp only at hr
    by_cases hi : opTableIdx p.1.ins.opcode = opKeccak
    · rw [hi] at hr
      rcases mem_getD_modify _ _ _ hr with hr | hr
      · rcases Array.mem_push.1 hr with hr | rfl
        · exact h r hr
        · exact kRow_rowOf ctx p.2 p.1 hi
      · exact h r hr
    · rw [getD_modify_of_ne _ hi] at hr
      exact h r hr

/-! ## The columns -/

theorem colsOf_qkeccak {κ : ℕ} (img : MemoryImage κ) (tabs : Array (Array (Array K)))
    (logs : List ℕ) :
    (colsOf img tabs logs).getD qkeccak #[] =
      qkeccakColumn (tabs.getD opKeccak #[]) (logs.getD opKeccak 0) := by
  unfold colsOf
  rw [getD_ofFn' _ (by decide)]
  simp [memory0, memory1, qkeccak]

theorem tableOf_keccakOut (l : ℕ) :
    tableOf (globalColumnBases.getD opKeccak 0 + (keccakOut + l)) = opKeccak := by
  rw [keccakBase_eq, keccakOut_eq]
  unfold tableOf
  simp [nTables, List.range_succ, globalColumnBases_eq, opKeccak]

theorem colsOf_keccakOut {κ : ℕ} (img : MemoryImage κ) (tabs : Array (Array (Array K)))
    (logs : List ℕ) {l : ℕ} (hl : l < 25) :
    (colsOf img tabs logs).getD (globalColumnBases.getD opKeccak 0 + (keccakOut + l)) #[] =
      tableColumn (tabs.getD opKeccak #[]) (paddingRow opKeccak) (logs.getD opKeccak 0)
        (keccakOut + l) := by
  have hc : globalColumnBases.getD opKeccak 0 + (keccakOut + l) < nColumns := by
    rw [keccakBase_eq, keccakOut_eq, show nColumns = 116 by decide]; omega
  unfold colsOf
  rw [getD_ofFn' _ hc]
  have h0 : globalColumnBases.getD opKeccak 0 + (keccakOut + l) ≠ memory0 := by
    rw [keccakBase_eq, keccakOut_eq]; simp only [memory0]; omega
  have h1 : globalColumnBases.getD opKeccak 0 + (keccakOut + l) ≠ memory1 := by
    rw [keccakBase_eq, keccakOut_eq]; simp only [memory1]; omega
  have h2 : globalColumnBases.getD opKeccak 0 + (keccakOut + l) ≠ qkeccak := by
    rw [keccakBase_eq, keccakOut_eq]; simp only [qkeccak]; omega
  simp only [h0, h1, h2, ↓reduceIte, tableOf_keccakOut l]
  rw [getD_ofFn' _ (by decide), Nat.add_sub_cancel_left]

theorem tableColumn_getD (R : Array (Array K)) (pad : Array K) (h i : ℕ) {x : ℕ} (hx : x < 2 ^ h) :
    (tableColumn R pad h i).getD x 0 = if x < R.size then cellAt R x i else pad.getD i 0 := by
  unfold tableColumn
  rw [getD_ofFn' _ hx]

theorem tableColumn_size (R : Array (Array K)) (pad : Array K) (h i : ℕ) :
    (tableColumn R pad h i).size = 2 ^ h := by
  simp [tableColumn]

/-- A padding row's output lanes are the zero state's permutation. -/
theorem paddingRow_out {l : ℕ} (hl : l < 25) :
    (paddingRow opKeccak).getD (keccakOut + l) 0 = laneK (keccakF1600 zeroState) l := by
  have hp : (tables.getD opKeccak default).padding =
      (List.replicate keccakColumns.length (0 : E)).zipIdx.map fun (p, i) ↦
        if keccakOut ≤ i ∧ i < keccakOut + keccakStateLanes then
          eOfNat (Keccak.lane (keccakF1600 (Vector.replicate 25 0)) (i - keccakOut)).toNat
        else p := rfl
  have hlen : keccakColumns.length = 68 := by decide
  unfold paddingRow
  rw [hp, hlen, keccakOut_eq]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_zipIdx, List.getElem?_replicate, show 33 + l < 68 by omega, ↓reduceIte,
    Option.map_some, Option.getD_some]
  have hc : (33 ≤ 0 + (33 + l) ∧ 0 + (33 + l) < 33 + keccakStateLanes) := by
    simp [keccakStateLanes]; omega
  simp only [hc, and_self, ↓reduceIte, limb_eOfNat, zeroState, laneK]
  simp only [show 0 + (33 + l) - 33 = l by omega]
  simp [K.ofLane, K.ofBits]

/-! ## `q_keccak` -/

theorem qkeccakSlotBits_six : qkeccakSlotBits = 6 := by decide

theorem qkeccakColumn_size (R : Array (Array K)) (h : ℕ) :
    (qkeccakColumn R h).size = 2 ^ (h + 6) := by
  simp [qkeccakColumn, qkeccakSlotBits_six]

theorem qkeccakColumn_getD (R : Array (Array K)) (h : ℕ) {x k : ℕ} (hx : x < 2 ^ h)
    (hk : k < 64) :
    (qkeccakColumn R h).getD (x + 2 ^ h * k) 0 =
      if k < keccakStateLanes then (if x < R.size then cellAt R x (keccakIn + k) else 0)
      else if k < qkeccakSlots then
        laneK (if x < R.size then segment 0 (inState R x) else segment 0 zeroState)
          (k - keccakStateLanes)
      else if x < R.size then cellAt R x (spareLocal (k - qkeccakSlots))
      else (paddingRow opKeccak).getD (spareLocal (k - qkeccakSlots)) 0 := by
  have hi : x + 2 ^ h * k < 2 ^ (h + qkeccakSlotBits) := by
    rw [qkeccakSlotBits_six, pow_add]
    have : 2 ^ h * k + 2 ^ h ≤ 2 ^ h * 64 := by nlinarith
    omega
  have hmod : (x + 2 ^ h * k) % 2 ^ h = x := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  have hdiv : (x + 2 ^ h * k) / 2 ^ h = k := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]
  unfold qkeccakColumn
  rw [getD_ofFn' _ hi]
  simp only [hmod, hdiv]
  rw [getD_ofFn' _ hx]

/-! ## The states `q_keccak` holds -/

theorem qkeccakSlots_eq : qkeccakSlots = 50 := by decide

theorem state_ext {a b : KeccakState} (h : ∀ l < 25, Keccak.lane a l = Keccak.lane b l) : a = b :=
  Vector.ext fun l hl ↦ by
    rw [← LeanVM.Protocol.KeccakGkr.lane_eq a hl, ← LeanVM.Protocol.KeccakGkr.lane_eq b hl]
    exact h l hl

theorem lane_inState_rows (R : Array (Array K)) (x : ℕ) {l : ℕ} (hl : l < 25) :
    Keccak.lane (inState R x) l = K.lane (cellAt R x (keccakIn + l)) := by
  rw [LeanVM.Protocol.KeccakGkr.lane_eq _ hl, inState, Vector.getElem_ofFn]

theorem lane_zeroState (l : ℕ) : Keccak.lane zeroState l = 0 := by
  simp only [Keccak.lane, zeroState, Array.getD_eq_getD_getElem?, Vector.toArray_replicate,
    Array.getElem?_replicate]
  split <;> rfl

/-- The state at a step of the witness's `q_keccak`: its row's input, the zero state past the
rows. -/
def stepState (R : Array (Array K)) (x : ℕ) : KeccakState :=
  if x < R.size then inState R x else zeroState

/-- The witness's `q_keccak` as words. -/
def qkCol (R : Array (Array K)) (h : ℕ) : ℕ → K := fun n ↦ (qkeccakColumn R h).getD n 0

theorem inState_qk_zero (R : Array (Array K)) (h : ℕ) {x : ℕ} (hx : x < 2 ^ h) :
    LeanVM.Protocol.KeccakGkr.inState h (qkCol R h) 0 x = stepState R x := by
  refine state_ext fun l hl ↦ ?_
  rw [LeanVM.Protocol.KeccakGkr.lane_inState h _ 0 x hl, qkCol,
    show 25 * 0 + l = l by omega, qkeccakColumn_getD R h hx (k := l) (by omega)]
  simp only [show l < keccakStateLanes by simp [keccakStateLanes]; omega, ↓reduceIte, stepState]
  by_cases hxR : x < R.size
  · simp only [hxR, ↓reduceIte, lane_inState_rows R x hl]
  · simp only [hxR, ↓reduceIte, lane_zeroState]
    rfl

theorem segment_zero (a : KeccakState) : segment 0 a = roundsFrom 0 12 a := by
  unfold segment roundsFrom
  rw [Nat.mul_zero]

theorem laneWord_eq (a : KeccakState) (l : ℕ) : laneWord a l = laneK a l := by
  unfold laneWord laneK
  rfl

theorem inState_qk_one (R : Array (Array K)) (h : ℕ) {x : ℕ} (hx : x < 2 ^ h) :
    LeanVM.Protocol.KeccakGkr.inState h (qkCol R h) 1 x = segment 0 (stepState R x) := by
  refine state_ext fun l hl ↦ ?_
  rw [LeanVM.Protocol.KeccakGkr.lane_inState h _ 1 x hl, qkCol,
    qkeccakColumn_getD R h hx (k := 25 * 1 + l) (by omega)]
  have h1 : ¬ 25 * 1 + l < keccakStateLanes := by simp [keccakStateLanes]
  have h2 : 25 * 1 + l < qkeccakSlots := by rw [qkeccakSlots_eq]; omega
  simp only [h1, h2, ↓reduceIte, lane_laneK, show 25 * 1 + l - keccakStateLanes = l by
    simp [keccakStateLanes], stepState]
  by_cases hxR : x < R.size <;> simp only [hxR, ↓reduceIte]

/-- **The committed middle state is twelve rounds of the input**, at every step, so at every
point. -/
theorem midAgree_witness (R : Array (Array K)) (h : ℕ) (inst : List E) :
    midAgree h (qkCol R h) inst := fun l hl ↦ by
  unfold LeanVM.Protocol.KeccakGkr.stepMle
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' := Finset.mem_range.1 hx
  have hpt : laneWord (roundsFrom 0 12 (LeanVM.Protocol.KeccakGkr.inState h (qkCol R h) 0 x)) l =
      qkCol R h (x + 2 ^ h * (25 + l)) := by
    rw [inState_qk_zero R h hx', qkCol, qkeccakColumn_getD R h hx' (k := 25 + l) (by omega)]
    have h1 : ¬ 25 + l < keccakStateLanes := by simp [keccakStateLanes]
    have h2 : 25 + l < qkeccakSlots := by rw [qkeccakSlots_eq]; omega
    simp only [h1, h2, ↓reduceIte, show 25 + l - keccakStateLanes = l by
      simp [keccakStateLanes], stepState, laneWord_eq, segment_zero]
    by_cases hxR : x < R.size <;> simp only [hxR, ↓reduceIte]
  dsimp only
  rw [hpt]

theorem cellAt_eq (R : Array (Array K)) {x : ℕ} (hx : x < R.size) (i : ℕ) :
    cellAt R x i = R[x].getD i 0 := by
  simp [cellAt, Array.getElem?_eq_getElem hx, Array.getD_eq_getD_getElem?]

/-- **The output columns are the last twelve rounds from the committed middle state**, at every
point. -/
theorem outClaimsTrueMid_witness (R : Array (Array K)) (hR : ∀ r ∈ R, KRow r) (h : ℕ)
    {inst : List E} (hi : inst.length = h) {output : List E}
    (ho : ∀ l < 25, output.getD l 0 =
      mleK (tableColumn R (paddingRow opKeccak) h (keccakOut + l)) inst) :
    outClaimsTrueMid h (qkCol R h) inst output := fun l hl ↦ by
  rw [ho l hl, mleK_eq_sum _ _ (by rw [tableColumn_size, hi]), hi]
  unfold LeanVM.Protocol.KeccakGkr.stepMle
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' := Finset.mem_range.1 hx
  have hpt : laneWord (roundsFrom 12 12 (LeanVM.Protocol.KeccakGkr.inState h (qkCol R h) 1 x)) l =
      (tableColumn R (paddingRow opKeccak) h (keccakOut + l)).getD x 0 := by
    rw [inState_qk_one R h hx', tableColumn_getD _ _ _ _ hx', segment_zero,
      ← LeanVM.Protocol.KeccakGkr.keccakF_eq, laneWord_eq]
    unfold stepState
    by_cases hxR : x < R.size
    · obtain ⟨S, hin, hout⟩ := hR R[x] (Array.getElem_mem hxR)
      have hS : inState R x = S := state_ext fun l' hl' ↦ by
        rw [lane_inState_rows R x hl', cellAt_eq R hxR, hin l' hl', lane_laneK]
      simp only [hxR, ↓reduceIte, hS, cellAt_eq R hxR, hout l hl]
    · simp only [hxR, ↓reduceIte, paddingRow_out hl]
  dsimp only
  rw [hpt]

end LeanVM.Prover.Complete.Keccak

end
