/-
  LeanVM.Prover.Complete.Link.ScatterHonest

  The honest witness's pointers name their cells: `ScatterOK W` for every admitted `W`.
-/

module

public import LeanVM.Prover.Complete.Link.BalanceSum
public import LeanVM.Prover.Complete.Link.Steps
import LeanVM.Semantics.Lemmas

/-!
# The honest pointers are one-hot and read inside their windows

Every pointer column of an honest row holds the one-hot word of the cycle, the instruction or a
memory cell (`rowOf_ptrs`), each below `2^W`; an access with a shift is `KECCAK`'s, whose blocks
the execution keeps in one window (`KeccakBlocksInWindows`), and a gated output cell is one the
instruction writes. So `scatterOK_of : Admitted … → ScatterOK W`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Extraction

/-! ## The pointer columns of a row -/

theorem keccak_pointers :
    (tables.getD opKeccak default).links.pointers = [67, 66, 58, 59, 60, 61, 62, 63, 64, 65] := by
  decide +kernel

/-- A `KECCAK` row's pointer columns. -/
theorem keccak_row_ptrs {κ : ℕ} (ctx : FillCtx κ) (k : ℕ) (pc fp : K) (slot : ℕ) (om : Fin 4 → K)
    (otail ob8 ocap oout : K) (inOdd outOdd : Bool) (outCells : KeccakOutputCells) :
    let row := rowOf ctx k ⟨pc, fp, slot, .keccak om otail ob8 ocap oout inOdd outOdd outCells⟩
    row.getD 58 0 = ctx.cell (fp * om 0) ∧ row.getD 59 0 = ctx.cell (fp * om 1) ∧
      row.getD 60 0 = ctx.cell (fp * om 2) ∧ row.getD 61 0 = ctx.cell (fp * om 3) ∧
      row.getD 62 0 = ctx.cell (fp * otail) ∧ row.getD 63 0 = ctx.cell (fp * ob8) ∧
      row.getD 64 0 = ctx.cell (fp * ocap) ∧ row.getD 65 0 = ctx.cell (fp * oout) ∧
      row.getD 66 0 = ctx.ptr slot ∧ row.getD 67 0 = ctx.ptr k := by
  intro row
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [row, rowOf, Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.size_append,
      Array.size_ofFn, List.size_toArray, List.length_map, List.length_cons, List.length_nil] <;>
    simp

/-- **A row's pointer columns** hold the cycle's, the instruction's or a cell's one-hot word. -/
theorem rowOf_ptrs {κ : ℕ} (ctx : FillCtx κ) (k : ℕ) (st : Step) :
    ∀ p ∈ (tables.getD (opTableIdx st.ins.opcode) default).links.pointers,
      (rowOf ctx k st).getD p 0 = ctx.ptr k ∨ (rowOf ctx k st).getD p 0 = ctx.ptr st.slot ∨
        ∃ a, (rowOf ctx k st).getD p 0 = ctx.cell a := by
  obtain ⟨pc, fp, slot, ins⟩ := st
  cases ins with
  | xor =>
    intro p hp
    rw [show (tables.getD (opTableIdx (LeanIsaInstruction.xor _ _ _).opcode) default).links.pointers =
      [6, 5, 2, 3, 4] from rfl] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr ⟨_, rfl⟩)
  | mulNative =>
    intro p hp
    rw [show (tables.getD (opTableIdx (LeanIsaInstruction.mulNative _ _ _).opcode) default).links.pointers =
      [8, 7, 4, 5, 6] from rfl] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr ⟨_, rfl⟩)
  | setConstant =>
    intro p hp
    rw [show (tables.getD (opTableIdx (LeanIsaInstruction.setConstant _ _).opcode) default).links.pointers =
      [4, 3, 2] from rfl] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr ⟨_, rfl⟩)
  | deref =>
    intro p hp
    rw [show (tables.getD (opTableIdx (LeanIsaInstruction.deref _ _ _ _).opcode) default).links.pointers =
      [9, 8, 5, 6, 7] from rfl] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr ⟨_, rfl⟩)
  | jump =>
    intro p hp
    rw [show (tables.getD (opTableIdx (LeanIsaInstruction.jump _ _ _).opcode) default).links.pointers =
      [13, 12, 9, 10, 11] from rfl] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr ⟨_, rfl⟩)
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    intro p hp
    change p ∈ (tables.getD opKeccak default).links.pointers at hp
    rw [keccak_pointers] at hp
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hbc, hcyc⟩ :=
      keccak_row_ptrs ctx k pc fp slot om otail ob8 ocap oout inOdd outOdd outCells
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hcyc
    · exact Or.inr (Or.inl hbc)
    · exact Or.inr (Or.inr ⟨_, h0⟩)
    · exact Or.inr (Or.inr ⟨_, h1⟩)
    · exact Or.inr (Or.inr ⟨_, h2⟩)
    · exact Or.inr (Or.inr ⟨_, h3⟩)
    · exact Or.inr (Or.inr ⟨_, h4⟩)
    · exact Or.inr (Or.inr ⟨_, h5⟩)
    · exact Or.inr (Or.inr ⟨_, h6⟩)
    · exact Or.inr (Or.inr ⟨_, h7⟩)

/-! ## `KECCAK`'s reads -/

/-- Every cell `readCells` reads succeeds. -/
theorem readCells_spec {read : K → Option E} {fp : K} {off : Fin 13 → K} {out : Fin 13 → E}
    (h : readCells read fp off = some out) : ∀ c, read (fp * off c) = some (out c) := by
  unfold readCells at h
  suffices key : ∀ (L : List (Fin 13)) (out : Fin 13 → E), L.foldr
      (fun c (acc : Option (Fin 13 → E)) ↦ do
        let v ← read (fp * off c)
        let rest ← acc
        pure fun c' ↦ if c' = c then v else rest c') (some fun _ ↦ (0 : E)) = some out →
      ∀ c ∈ L, read (fp * off c) = some (out c) from fun c ↦ key _ out h c (List.mem_finRange c)
  intro L
  induction L with
  | nil => intro _ _ c hc; cases hc
  | cons c L ih =>
    intro out h c' hc'
    simp only [List.foldr_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, rest, hrest, rfl⟩ := h
    by_cases he : c' = c
    · subst he; simp [hv]
    · rcases List.mem_cons.mp hc' with rfl | hm
      · exact absurd rfl he
      · simp only [he, ↓reduceIte]; exact ih rest hrest c' hm

/-- Every cell `readFirstCells` reads succeeds. -/
theorem readFirstCells_spec {read : K → Option E} {fp : K} {off : Fin 13 → K} {n : ℕ}
    {out : Fin 13 → E} (h : readFirstCells read fp off n = some out) :
    ∀ c : Fin 13, c.val < n → read (fp * off c) = some (out c) := by
  unfold readFirstCells at h
  suffices key : ∀ (L : List (Fin 13)) (out : Fin 13 → E), L.foldr
      (fun c (acc : Option (Fin 13 → E)) ↦ if c.val < n then do
        let v ← read (fp * off c)
        let rest ← acc
        pure fun c' ↦ if c' = c then v else rest c' else acc) (some fun _ ↦ (0 : E)) = some out →
      ∀ c ∈ L, c.val < n → read (fp * off c) = some (out c) from
    fun c hc ↦ key _ out h c (List.mem_finRange c) hc
  intro L
  induction L with
  | nil => intro _ _ c hc; cases hc
  | cons c L ih =>
    intro out h c' hc' hn
    simp only [List.foldr_cons] at h
    by_cases hcn : c.val < n
    · simp only [hcn, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v, hv, rest, hrest, rfl⟩ := h
      by_cases he : c' = c
      · subst he; simp [hv]
      · rcases List.mem_cons.mp hc' with rfl | hm
        · exact absurd rfl he
        · simp only [he, ↓reduceIte]; exact ih rest hrest c' hm hn
    · simp only [hcn, ↓reduceIte] at h
      rcases List.mem_cons.mp hc' with rfl | hm
      · exact absurd hn hcn
      · exact ih out h c' hm hn

/-- The index of the cell `s` past a cell. -/
theorem index_shift {κ : ℕ} (hκ : κ < 64) {a : K} {i j s : ℕ} (hi : i < 2 ^ κ) (hj : j < 2 ^ κ)
    (hs : s < 64) (ha : a = addressOfIndex i) (hb : g ^ s * a = addressOfIndex j) : j = i + s := by
  have h63 : 2 ^ κ ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine gpow_injOn (show j < 2 ^ 64 - 1 by omega) (show i + s < 2 ^ 64 - 1 by omega) ?_
  show g ^ j = g ^ (i + s)
  have hb' : g ^ s * a = g ^ j := hb
  rw [← hb', ha, pow_add, mul_comm]

/-- **A read `s` cells past `i` inside `i`'s window of `16`** stays in the pointer's window. -/
theorem window_ok {chunks : Chunks} (hc : ChunksOK chunks) {κ : ℕ} (hκw : κ ≤ chunks.width)
    {i s n : ℕ} (hwin : i % 16 + n ≤ 16) (hs : s < n) (his : i + s < 2 ^ κ) :
    chunks.shifted i s = some (i + s) ∧ i + s < 2 ^ chunks.width := by
  have hw := lt_of_lt_of_le his (Nat.pow_le_pow_right (by norm_num) hκw)
  refine ⟨?_, hw⟩
  have h0 : chunks.widths.getD 0 0 = min chunks.width windowBits := hc.2.2.2.2.2.2
  unfold Chunks.shifted
  rw [h0]
  split_ifs with h
  · rfl
  · exfalso
    apply h
    by_cases h4 : windowBits ≤ chunks.width
    · rw [min_eq_right h4]
      show i % 16 + s < 16
      omega
    · rw [min_eq_left (by omega), Nat.mod_eq_of_lt (by omega)]
      exact hw

/-! ## The windows of the run -/

theorem windows_run {prog : LeanIsaProgram} {κ : ℕ} (L : MemoryImage κ) :
    ∀ k n (r : Registers K), keccakBlocksInWindowsInRun prog L n r →
      run prog L n r = some (Registers.final prog) → k < n →
      KeccakBlocksInWindowsAt κ ((run prog L k r).getD Registers.initial).fp
        (stepOf prog ((run prog L k r).getD Registers.initial)).ins := by
  intro k
  induction k with
  | zero =>
    intro n r hw hrun hk
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hr : r ≠ Registers.final prog := fun he ↦ by rw [run_succ_of_eq he] at hrun; cases hrun
    rw [run_succ_of_ne_final hr] at hrun
    obtain ⟨r', hs, -⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨ins, hf, -⟩ := Option.bind_eq_some_iff.mp hs
    have hs' : step prog L r = some r' := hs
    unfold keccakBlocksInWindowsInRun at hw
    rw [hf, hs'] at hw
    simp only [run, Option.getD_some, stepOf, hf]
    exact hw.1
  | succ k ih =>
    intro n r hw hrun hk
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hr : r ≠ Registers.final prog := fun he ↦ by rw [run_succ_of_eq he] at hrun; cases hrun
    rw [run_succ_of_ne_final hr] at hrun
    obtain ⟨r', hs, hrun'⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨ins, hf, -⟩ := Option.bind_eq_some_iff.mp hs
    have hs' : step prog L r = some r' := hs
    unfold keccakBlocksInWindowsInRun at hw
    rw [hf, hs'] at hw
    have hk' : run prog L (k + 1) r = run prog L k r' := by
      rw [run_succ_of_ne_final hr, hs']; rfl
    rw [hk']
    exact ih m r' hw.2 hrun' (by omega)

/-- **Every step's `KECCAK` keeps its blocks in windows.** -/
theorem windows_stateAt {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    (hv : ValidExecution prog input ex) (hw : ex.KeccakBlocksInWindows) {k : ℕ} (hk : k < ex.stepCount) :
    KeccakBlocksInWindowsAt ex.logMemorySize (stateAt ex k).fp (stepOf prog (stateAt ex k)).ins :=
  windows_run ex.memory k _ _ hw hv.2 hk

/-! ## The honest witness -/

/-- A successful read: the cell's index and its word. -/
theorem read_cell {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) {a : K} {v : E}
    (h : img.read a = some v) : ∃ i : Fin (2 ^ κ), a = addressOfIndex i ∧ img i = v ∧
      addressIndex? κ a = some i :=
  let ⟨i, hi, hv⟩ := (MemoryImage.read_eq_some_iff hκ img).mp h
  ⟨i, hi, hv, (gLog?_spec hκ).mpr hi⟩

theorem headD_indices_encode {c : Chunks} (hc : ChunksOK c) {σ : ℕ} (hσ : σ < 2 ^ c.width) :
    (c.indices (kToNat (K.ofBits (c.encode σ)))).headD 0 = σ := by
  rw [kToNat_ofBits, Nat.mod_eq_of_lt (encode_lt hc _), indices_encode hc hσ]
  rfl

theorem indices_ofBits {c : Chunks} (hc : ChunksOK c) {σ : ℕ} (hσ : σ < 2 ^ c.width) :
    c.indices (kToNat (K.ofBits (c.encode σ))) = [σ] := by
  rw [kToNat_ofBits, Nat.mod_eq_of_lt (encode_lt hc _), indices_encode hc hσ]

/-- **An honest pointer word is one-hot** below `2^W`. -/
theorem ptr_honest {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog} {ρ : ℕ}
    {W : Witness} (hA : Admitted prog input ex ρ W) {t u p : ℕ} (ht : t < nTables)
    (hu : u < W.rows.getD t 0) (hp : p ∈ (tables.getD t default).links.pointers) :
    ∃ σ < 2 ^ W.chunks.width, ((W.tableCols t).getD p #[]).getD u 0 = K.ofBits (W.chunks.encode σ) := by
  have hv := hA.valid
  have hW := hA.witness
  obtain ⟨-, -, hT, hκw, hlw⟩ := width_witness hW hv
  rw [rows_witness hW hv ht] at hu
  rw [word_witness hW hv ht hu]
  have hpt := mem_tablePairs (List.getElem_mem hu)
  obtain ⟨hk, hq⟩ := tablePairs_step (List.getElem_mem hu)
  generalize (tablePairs (traceSteps ex) t)[u] = q at hpt hk hq ⊢
  rw [← hpt] at hp
  rcases rowOf_ptrs (fillCtx ex W) q.2 q.1 p hp with h | h | ⟨a, h⟩
  · exact ⟨q.2, by omega, h⟩
  · refine ⟨q.1.slot, ?_, h⟩
    rw [hq]
    exact lt_of_lt_of_le (slot_stepOf _ _) (Nat.pow_le_pow_right (by norm_num) hlw)
  · obtain ⟨h1, h2⟩ := cell_oneHot hW hv a
    exact ⟨_, h1, h.trans h2⟩

theorem shifts_zero : ∀ t < opKeccak, (tables.getD t default).links.memory.all (·.shift == 0) = true := by
  decide +kernel

/-- `KECCAK`'s accesses: unshifted, a read in the tail or cap run (pointers `62`, `64`), or a written
cell past the first (pointer `65`, gated by `out_two` or `out_all`). -/
theorem keccak_mem_shape : (tables.getD opKeccak default).links.memory.all (fun a ↦
    a.shift == 0 || (a.gate == none && (a.pointer == 62 || a.pointer == 64) && decide (a.shift < 4)) ||
      (a.pointer == 65 && decide (a.shift < 13) &&
        ((a.shift == 1 && a.gate == some 5) || (decide (2 ≤ a.shift) && a.gate == some 6)))) = true := by
  decide +kernel

/-- A `KECCAK` row's output flags. -/
theorem keccak_row_flags {κ : ℕ} (ctx : FillCtx κ) (k : ℕ) (pc fp : K) (slot : ℕ) (om : Fin 4 → K)
    (otail ob8 ocap oout : K) (inOdd outOdd : Bool) (outCells : KeccakOutputCells) :
    let row := rowOf ctx k ⟨pc, fp, slot, .keccak om otail ob8 ocap oout inOdd outOdd outCells⟩
    row.getD 5 0 = (keccakOutputFlags outCells).1 ∧ row.getD 6 0 = (keccakOutputFlags outCells).2 := by
  intro row
  refine ⟨?_, ?_⟩ <;>
    simp only [row, rowOf, Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.size_append,
      Array.size_ofFn, List.size_toArray, List.length_map, List.length_cons, List.length_nil] <;>
    simp

theorem ptrAt_of {W : Witness} {t p u σ : ℕ} (hc : ChunksOK W.chunks) (hσ : σ < 2 ^ W.chunks.width)
    (h : ((W.tableCols t).getD p #[]).getD u 0 = K.ofBits (W.chunks.encode σ)) : ptrAt W t p u = σ := by
  rw [ptrAt, h, headD_indices_encode hc hσ]

/-- **The honest witness's pointers name their cells.** -/
theorem scatterOK_of {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog} {ρ : ℕ}
    {W : Witness} (hA : Admitted prog input ex ρ W) : ScatterOK W := by
  have hv := hA.valid
  have hW := hA.witness
  obtain ⟨hc, -, -, hκw, -⟩ := width_witness hW hv
  have part1 : ∀ t < nTables, ∀ u < W.rows.getD t 0, ∀ p ∈ (tables.getD t default).links.pointers,
      W.chunks.indices (kToNat (((W.tableCols t).getD p #[]).getD u 0)) = [ptrAt W t p u] ∧
        ptrAt W t p u < 2 ^ W.chunks.width := by
    intro t ht u hu p hp
    obtain ⟨σ, hσ, h⟩ := ptr_honest hA ht hu hp
    rw [ptrAt_of hc hσ h, h, indices_ofBits hc hσ]
    exact ⟨rfl, hσ⟩
  refine ⟨part1, ?_⟩
  intro t ht u hu a ha hg
  have hpa := ((ptr_mem ht).2 a ha).1
  have hlt := (part1 t ht u hu _ hpa).2
  have unshifted : a.shift = 0 → W.chunks.shifted (ptrAt W t a.pointer u) a.shift =
      some (ptrAt W t a.pointer u + a.shift) ∧ ptrAt W t a.pointer u + a.shift < 2 ^ W.chunks.width :=
    fun h0 ↦ by rw [h0, shifted_zero, add_zero]; exact ⟨rfl, hlt⟩
  by_cases h5 : t < opKeccak
  · exact unshifted (by simpa using List.all_eq_true.mp (shifts_zero t h5) a ha)
  have ht5 : t = opKeccak := by
    have : nTables = opKeccak + 1 := rfl
    omega
  subst ht5
  have hshape := List.all_eq_true.mp keccak_mem_shape a ha
  by_cases hs0 : a.shift = 0
  · exact unshifted hs0
  -- the step of the row
  have hu' := hu
  rw [rows_witness hW hv ht] at hu'
  have hpt := mem_tablePairs (List.getElem_mem hu')
  obtain ⟨hk, hq⟩ := tablePairs_step (List.getElem_mem hu')
  have hword := fun c ↦ word_witness hW hv ht hu' c
  have hcol : colAt W opKeccak u = fun c ↦ ofK ((rowOf (fillCtx ex W)
      (tablePairs (traceSteps ex) opKeccak)[u].2 (tablePairs (traceSteps ex) opKeccak)[u].1).getD c 0) :=
    rowValue_witness hW hv ht hu'
  have hptr : ∀ p, ptrAt W opKeccak p u = (W.chunks.indices (kToNat ((rowOf (fillCtx ex W)
      (tablePairs (traceSteps ex) opKeccak)[u].2 (tablePairs (traceSteps ex) opKeccak)[u].1).getD p 0))).headD 0 :=
    fun p ↦ by rw [ptrAt, hword]
  rw [hptr]
  rw [hcol] at hg
  generalize (tablePairs (traceSteps ex) opKeccak)[u] = q at hpt hk hq hg ⊢
  obtain ⟨st, k⟩ := q
  dsimp only at hpt hk hq hg ⊢
  have hex := step_succ hv hk
  have hwin := windows_stateAt hv hA.windows hk
  rw [← hq] at hex hwin
  obtain ⟨pc, fp, slot, ins⟩ := st
  have hfp : fp = (stateAt ex k).fp := congrArg Step.fp hq
  cases ins with
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    obtain ⟨-, -, -, -, h62, -, h64, h65, -, -⟩ :=
      keccak_row_ptrs (fillCtx ex W) k pc fp slot om otail ob8 ocap oout inOdd outOdd outCells
    obtain ⟨f5, f6⟩ :=
      keccak_row_flags (fillCtx ex W) k pc fp slot om otail ob8 ocap oout inOdd outOdd outCells
    dsimp only at hwin hex
    rw [← hfp] at hwin
    obtain ⟨wTail, wCap, wOut⟩ := hwin
    have hκ := logMemorySize_lt hv
    rcases hI : readCells ex.memory.read (stateAt ex k).fp (keccakInputCellOffset om otail ob8 ocap) with
      _ | input
    · simp [executeWith, hI] at hex
    rcases hO : readFirstCells ex.memory.read (stateAt ex k).fp (fun c ↦ g ^ c.val * oout)
      outCells.cellCount with _ | output
    · simp [executeWith, hI, hO] at hex
    have rI := readCells_spec hI
    have rO := readFirstCells_spec hO
    rw [← hfp] at rI rO
    -- a run of cells `s` past `fp·o`, all read, inside `o`'s window
    have run_ok : ∀ (o : K) (n s : ℕ), s < n → n ≤ 13 →
        (∀ i ∈ addressIndex? ex.logMemorySize (fp * o), i.val % 16 + n ≤ 16) →
        (∀ c < n, ∃ v, ex.memory.read (fp * (g ^ c * o)) = some v) →
        W.chunks.shifted ((W.chunks.indices (kToNat ((fillCtx ex W).cell (fp * o)))).headD 0) s =
          some ((W.chunks.indices (kToNat ((fillCtx ex W).cell (fp * o)))).headD 0 + s) ∧
        (W.chunks.indices (kToNat ((fillCtx ex W).cell (fp * o)))).headD 0 + s < 2 ^ W.chunks.width := by
      intro o n s hs hn hw hr
      obtain ⟨v0, h0⟩ := hr 0 (by omega)
      rw [pow_zero, one_mul] at h0
      obtain ⟨i, hi, -, hxi⟩ := read_cell hκ ex.memory h0
      obtain ⟨vs, hvs⟩ := hr s hs
      obtain ⟨j, hj, -, -⟩ := read_cell hκ ex.memory hvs
      have hji := index_shift hκ (s := s) i.isLt j.isLt (by omega) hi (by rw [← hj]; ring)
      have hcell : (W.chunks.indices (kToNat ((fillCtx ex W).cell (fp * o)))).headD 0 = i := by
        rw [cell_eq, cellIndex_witness hv, hxi]
        exact headD_indices_encode hc (lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) hκw))
      rw [hcell]
      exact window_ok hc hκw (hw i hxi) hs (by rw [← hji]; exact j.isLt)
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hshape
    rcases hshape with (h0 | ⟨⟨hgn, hp⟩, hs4⟩) | ⟨⟨hp, hs13⟩, hgs⟩
    · exact absurd h0 hs0
    · rcases hp with hp | hp <;> rw [hp]
      · rw [h62]
        refine run_ok otail 4 a.shift hs4 (by norm_num) wTail fun c hc4 ↦ ⟨input ⟨4 + c, by omega⟩, ?_⟩
        have := rI ⟨4 + c, by omega⟩
        simpa [keccakInputCellOffset, show ¬ 4 + c < 4 by omega, show 4 + c < 8 by omega] using this
      · rw [h64]
        refine run_ok ocap 4 a.shift hs4 (by norm_num) wCap fun c hc4 ↦ ⟨input ⟨9 + c, by omega⟩, ?_⟩
        have := rI ⟨9 + c, by omega⟩
        simpa [keccakInputCellOffset, show ¬ 9 + c < 4 by omega, show ¬ 9 + c < 8 by omega,
          show 9 + c ≠ 8 by omega] using this
    · rw [hp, h65]
      have hcount : a.shift < outCells.cellCount := by
        rcases hgs with ⟨h1, hg5⟩ | ⟨h2, hg6⟩
        · rw [gateOf, hg5] at hg
          simp only [Option.map_some, Option.getD_some, f5] at hg
          cases outCells <;> simp_all [keccakOutputFlags, layoutFlagWord, KeccakOutputCells.cellCount]
        · rw [gateOf, hg6] at hg
          simp only [Option.map_some, Option.getD_some, f6] at hg
          cases outCells <;> simp_all [keccakOutputFlags, layoutFlagWord, KeccakOutputCells.cellCount]
      have hn : outCells.cellCount ≤ 13 := by cases outCells <;> simp [KeccakOutputCells.cellCount]
      exact run_ok oout outCells.cellCount a.shift hcount hn wOut fun c hc ↦
        ⟨_, rO ⟨c, by omega⟩ hc⟩
  | _ =>
    simp only [LeanIsaInstruction.opcode, opTableIdx] at hpt
    exact absurd hpt (by decide)

end LeanVM.Prover.Complete

end
