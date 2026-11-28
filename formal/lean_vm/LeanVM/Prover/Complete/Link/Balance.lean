/-
  LeanVM.Prover.Complete.Link.Balance

  The index side's lookups balance on the honest witness: `IndexBalance W` for every admitted `W`.
-/

module

public import LeanVM.Prover.Complete.Link.BalanceKeccak
import LeanVM.Semantics.Lemmas

/-!
# The balance on the honest witness

The balance's cube sum is the sum of the executed rows' shares (`cubeSum_balance`, the pointers
naming their cells by `scatterOK_of`); on the honest witness the index side's targets are the
memory's words and the program's slots (`targetsOK_witness`), and each executed row is a step of
the run (`rowValue_witness`, `step_succ`), so its share is zero, table by table (`share_xor` …
`share_keccak`). Hence `indexBalance_of : Admitted … → IndexBalance W`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Extraction LeanVM.Protocol.Relation

/-! ## The honest targets -/

theorem buildLayout_bytecode {bc : List K} {lm : ℕ} {rows : List ℕ} {L : Layout}
    (h : buildLayout bc lm rows = some L) : L.bytecode = bc := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · cases h

theorem powers_getD' (base : E) : ∀ (n b : ℕ), b < n → (powersFrom 1 base n).getD b 0 = base ^ b := by
  suffices h : ∀ (acc : E) (n b : ℕ), b < n → (powersFrom acc base n).getD b 0 = acc * base ^ b by
    intro n b hb; rw [h 1 n b hb, one_mul]
  intro acc n
  induction n generalizing acc with
  | zero => intro b hb; omega
  | succ n ih =>
    intro b hb
    rcases b with _ | b
    · simp [powersFrom]
    · rw [powersFrom, List.getD_cons_succ, ih _ b (by omega), pow_succ]; ring

theorem gjAt_eq (W : Witness) {j : ℕ} (hj : j < 2 ^ W.chunks.width) : gjAt W j = gpow j := by
  rw [gjAt, Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  exact powers_getD' gen _ _ hj

theorem getD_ofFn_lt {α : Type} {n : ℕ} (f : Fin n → α) (d : α) {j : ℕ} (hj : j < n) :
    (Array.ofFn f).getD j d = f ⟨j, hj⟩ := by
  simp [Array.getD_eq_getD_getElem?, hj]

theorem sumE_map_add {α : Type} (L : List α) (f h : α → E) :
    sumE (L.map fun x ↦ f x + h x) = sumE (L.map f) + sumE (L.map h) := by
  simp only [LeanVM.Protocol.Tables.sumE_eq, List.sum_map_add]

theorem wts_getD (ch : LinkChallenges) {op : ℕ} (hop : op < nTables) :
    (wts ch).omega.getD op [] = (tableSlotWeights (tables.getD op default) ch.slot
        (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) (ch.mu.getD op []) ch.etaMem ch.etaBc).1 ∧
      (wts ch).pc.getD op [] = (tableSlotWeights (tables.getD op default) ch.slot
        (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) (ch.mu.getD op []) ch.etaMem ch.etaBc).2.1 ∧
      (wts ch).frame.getD op [] = (tableSlotWeights (tables.getD op default) ch.slot
        (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) (ch.mu.getD op []) ch.etaMem ch.etaBc).2.2 := by
  have : nTables = 6 := rfl
  rw [this] at hop
  interval_cases op <;> exact ⟨rfl, rfl, rfl⟩

theorem opIndex_eq (o : Opcode) : opIndex o = opTableIdx o := by cases o <;> rfl

/-- **The index side's targets on the honest witness**, at a row of table `t` whose instruction
`ins` is at `σ`. -/
theorem targetsOK_witness {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog} {ρ : ℕ}
    {W : Witness} (hA : Admitted prog input ex ρ W) (ch : LinkChallenges)
    (hgm : ch.gammaMem.getD 2 0 = ch.gammaMem.getD 1 0 * eY) (σ : Fin (2 ^ prog.logSize)) :
    TargetsOK ch ex.memory (opTableIdx (prog.instructions σ).opcode) σ (slotE (prog.instructions σ))
      (idxAt W ch 3) (idxAt W ch 5) (idxAt W ch 10) (idxAt W ch 12) := by
  have hv := hA.valid
  have hW := hA.witness
  obtain ⟨-, hcols, hl, -⟩ := witness_steps hW hv
  obtain ⟨-, -, -, hκw, hlw⟩ := width_witness hW hv
  have hlm : W.layout.logMemory = ex.logMemorySize := (buildLayout_spec hl).1
  have hbc : W.layout.bytecode = bytecodeWords prog := buildLayout_bytecode hl
  have hκN : 2 ^ ex.logMemorySize ≤ 2 ^ W.chunks.width := Nat.pow_le_pow_right (by norm_num) hκw
  have hσN : (σ : ℕ) < 2 ^ W.chunks.width :=
    lt_of_lt_of_le σ.isLt (Nat.pow_le_pow_right (by norm_num) hlw)
  have hm0 : W.cols.getD memory0 #[] = Array.ofFn (n := 2 ^ ex.logMemorySize) fun x ↦
      (ex.memory x).limb 0 := by
    rw [hcols, colsOf_getD _ _ _ (by decide)]; rfl
  have hm1 : W.cols.getD memory1 #[] = Array.ofFn (n := 2 ^ ex.logMemorySize) fun x ↦
      (ex.memory x).limb 1 := by
    rw [hcols, colsOf_getD _ _ _ (by decide)]; rfl
  have hN : bcN W = 2 ^ prog.logSize := by
    rw [bcN, hbc, List.size_toArray, length_bytecodeWords, Nat.shiftRight_eq_div_pow,
      show bytecodeSlotBits = 4 from rfl, show (2 : ℕ) ^ 4 = 16 from rfl,
      Nat.mul_div_cancel_left _ (by norm_num)]
  have hslot : ∀ s < 16, ofK (bcSlot W s σ) = slotE (prog.instructions σ) s := by
    intro s hs
    rw [bcSlot, hN, hbc, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      ← List.getD_eq_getElem?_getD, bytecodeWords_getD prog hs σ.isLt, slotE]
    congr 1
    simp [List.getD_eq_getElem?_getD, hs]
  have hop : opcodeOf (bcSlot W 3 σ) = opTableIdx (prog.instructions σ).opcode := by
    rw [bcSlot, hN, hbc, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      ← List.getD_eq_getElem?_getD, bytecodeWords_getD prog (by norm_num) σ.isLt, opcodeOf_slot3,
      opIndex_eq]
  obtain ⟨wO, wP, wF⟩ := wts_getD ch (opTableIdx_lt (prog.instructions σ).opcode)
  refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_, ?_, ?_⟩
  · rw [idxAt_three, getD_ofFn_lt _ _ (lt_of_lt_of_le hj hκN)]
    dsimp only
    rw [hlm, ite_eq_left hj, hm0, hm1, getD_ofFn_lt _ _ hj, getD_ofFn_lt _ _ hj, hgm,
      show (powers gen (2 ^ W.chunks.width)).toArray.getD j 0 = gjAt W j from rfl,
      gjAt_eq W (lt_of_lt_of_le hj hκN)]
    linear_combination (ch.gammaMem.getD 1 0) * word_limbs (ex.memory ⟨j, hj⟩)
  · rw [idxAt_ten, getD_ofFn_lt _ _ (lt_of_lt_of_le hj hκN)]
    dsimp only
    rw [hlm, ite_eq_left hj, hm0, hm1, getD_ofFn_lt _ _ hj, getD_ofFn_lt _ _ hj, word_limbs]
  · rw [idxAt_five, getD_ofFn_lt _ _ hσN]
    dsimp only
    rw [ite_eq_left (by rw [hN]; exact σ.isLt), gjAt_eq W hσN, sumE_map_add, hop, wO, wP]
    unfold slotSum
    refine congrArg (_ + ·) (congrArg₂ (· + ·) ?_ ?_)
    · refine congrArg sumE (List.map_congr_left fun i hi ↦ ?_)
      rw [hslot _ (by simp [bytecodeSlotBits] at hi; omega)]
    · refine congrArg sumE (List.map_congr_left fun i hi ↦ ?_)
      rw [hslot _ (by simp [bytecodeSlotBits] at hi; omega)]
  · rw [idxAt_twelve, getD_ofFn_lt _ _ hσN]
    dsimp only
    rw [ite_eq_left (by rw [hN]; exact σ.isLt), hop, wF]
    unfold slotSum
    refine congrArg sumE (List.map_congr_left fun i hi ↦ ?_)
    rw [hslot _ (by simp [bytecodeSlotBits] at hi; omega)]

/-! ## The rows -/

/-- **A step of a valid run fetches its instruction**: its counter is `g^i`, its slot `i`. -/
theorem fetch_stateAt {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    (hv : ValidExecution prog input ex) {k : ℕ} (hk : k < ex.stepCount) :
    ∃ i : Fin (2 ^ prog.logSize), (stateAt ex k).pc = addressOfIndex i ∧
      stepOf prog (stateAt ex k) = ⟨(stateAt ex k).pc, (stateAt ex k).fp, i, prog.instructions i⟩ := by
  obtain ⟨r1, h1, hne⟩ := run_intermediate hv.2 hk
  obtain ⟨r2, h2, -⟩ := run_prefix (m := k + 1) (n := ex.stepCount - (k + 1))
    (by rw [show k + 1 + (ex.stepCount - (k + 1)) = ex.stepCount by omega]; exact hv.2)
  rw [run_add k 1, h1] at h2
  change run prog ex.memory 1 r1 = some r2 at h2
  rw [run_succ_of_ne_final hne] at h2
  obtain ⟨r2', hs, -⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨ins, hf, -⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨i, hi, hins⟩ := (prog.fetch_eq_some_iff).mp hf
  have hst : stateAt ex k = r1 := by simp [stateAt, h1]
  refine ⟨i, by rw [hst]; exact hi, ?_⟩
  rw [hst]
  simp [stepOf, hf, (gLog?_spec (logSize_lt prog)).mpr hi, hins]

/-- **An executed row's share of the balance is zero** on the honest witness. -/
theorem rowShare_zero {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog} {ρ : ℕ}
    {W : Witness} (hA : Admitted prog input ex ρ W) (ch : LinkChallenges)
    (hgm : ch.gammaMem.getD 2 0 = ch.gammaMem.getD 1 0 * eY) {t : ℕ} (ht : t < nTables) {u : ℕ}
    (hu : u < W.rows.getD t 0) : rowShare W ch t u = 0 := by
  have hv := hA.valid
  have hW := hA.witness
  obtain ⟨hc, -, -, hκw, hlw⟩ := width_witness hW hv
  have hκ := logMemorySize_lt hv
  rw [rows_witness hW hv ht] at hu
  have hpt := mem_tablePairs (List.getElem_mem hu)
  obtain ⟨hk, hq⟩ := tablePairs_step (List.getElem_mem hu)
  have hcol : colAt W t u = rowCol (rowOf (fillCtx ex W) (tablePairs (traceSteps ex) t)[u].2
      (tablePairs (traceSteps ex) t)[u].1) := rowValue_witness hW hv ht hu
  have hptr : ∀ p, ptrAt W t p u = rowPtr W.chunks (rowOf (fillCtx ex W)
      (tablePairs (traceSteps ex) t)[u].2 (tablePairs (traceSteps ex) t)[u].1) p := by
    intro p; rw [ptrAt, word_witness hW hv ht hu]; rfl
  unfold rowShare
  rw [hcol]
  simp only [hptr]
  generalize (tablePairs (traceSteps ex) t)[u] = q at hpt hk hq ⊢
  obtain ⟨st, k⟩ := q
  dsimp only at hpt hk hq ⊢
  obtain ⟨i, hpc, hst⟩ := fetch_stateAt hv hk
  have hex := step_succ hv hk
  rw [hst] at hex
  rw [hq, hst] at hpt ⊢
  dsimp only at hpt hex
  subst hpt
  have hT := targetsOK_witness hA ch hgm i
  have hσ : (i : ℕ) < 2 ^ W.chunks.width :=
    lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hlw)
  change executeWith ex.memory.read (stateAt ex k) (prog.instructions i) = _ at hex
  generalize prog.instructions i = ins at hT hex ⊢
  cases ins with
  | xor oA oB oC =>
    exact share_xor ch hκ ex.memory hc hκw _ k i hσ _ _ oA oB oC hpc hex _ _ _ _ hT
  | mulNative oA oB oC =>
    exact share_mul ch hκ ex.memory hc hκw _ k i hσ _ _ oA oB oC hpc hex _ _ _ _ hT
  | setConstant o kk =>
    exact share_set ch hκ ex.memory hc hκw _ k i hσ _ _ o kk hpc hex _ _ _ _ hT
  | deref o1 o2 o3 mode =>
    exact share_deref ch hκ ex.memory hc hκw _ k i hσ _ _ o1 o2 o3 mode hpc hex _ _ _ _ hT
  | jump oc od ofr =>
    exact share_jump ch hκ ex.memory hc hκw _ k i hσ _ _ oc od ofr hpc hex _ _ _ _ hT
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    exact share_keccak ch hκ ex.memory hc hκw _ k i hσ _ _ om otail ob8 ocap oout inOdd outOdd outCells
      hpc hex _ _ _ _ hT

/-- **The lookups balance** on the honest witness of every admitted execution: the index side's
memory, program, payload, word-read and frame-read terms sum to zero. -/
theorem indexBalance_of {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    {W : Witness} (hA : Admitted prog input t ρ W) : IndexBalance W := by
  intro theta0 drawn _
  dsimp only
  rw [cubeSum_balance _ _ (scatterOK_of hA)]
  exact Finset.sum_eq_zero fun tt htt ↦ Finset.sum_eq_zero fun u hu ↦
    rowShare_zero hA _ rfl (Finset.mem_range.mp htt) (Finset.mem_range.mp hu)

end LeanVM.Prover.Complete

end
