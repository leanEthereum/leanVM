/-
  LeanVM.Protocol.Relation.Link.Valid

  The link's relation gives a valid execution, the extracted one, once every executed row takes one
  leanISA step.
-/

module

public import LeanVM.Protocol.Relation.Iface
public import LeanVM.Protocol.Relation.Link.Chain
import LeanVM.Semantics.Lemmas
import LeanVM.Parameters.Generator
import LeanVM.Parameters.Field

/-!
# The relation's meaning: the chain

`valid_of_rowSteps`: at a layout `readAnnouncedSizes` accepts for a program's bytecode, a stack
whose state link holds (`StateHolds`, at the link's chunks), whose memory holds the public input
(`PubRel`), and each of whose executed rows takes one leanISA step from its state to its successor
on the memory read off the stack (`RowStep`), gives a valid execution, the extracted one
(`candidate`): the state link's identity makes the rows a chain of the cycles
(`Hotwire.linkHolds_sound`, the cycle count below `2^W`), the chain runs (`chain_states`,
`run_first_final`), and it halts at `firstFinal`, the least cycle of a row in the final state
(`firstFinal_spec`).

What is left of the relation's meaning is `RowStep` for each table (`Link/Steps.lean`): the
row's instruction (the program lookup), its reads (the memory lookup), its constraints, and for
`KECCAK` the permutation (`KeccakRel`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Protocol.Hotwire LeanVM.Protocol.Compile

@[expose] public section

/-! ## States as registers -/

/-- Registers as the link reads a state, `(pc, fp)` in `E`. -/
def regE (r : Registers K) : Fin 2 → E := ![ofK r.pc, ofK r.fp]

theorem regE_injective : Function.Injective regE := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [regE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
  rw [ofK_injective h0, ofK_injective h1]

/-- **A row takes one leanISA step**: its state and successor are registers, and the step from the
one on the memory read off the stack is the other. -/
def RowStep (program : LeanIsaProgram) (layout : Layout) {μ : ℕ} (q : Column μ)
    (x : LinkRow layout) : Prop :=
  ∃ r r' : Registers K, rowState layout q x = regE r ∧ rowNext layout q x = regE r' ∧
    step program (memoryImage layout q) r = some r'

/-! ## The layout -/

/-- What `buildLayout` gives, beyond `buildLayout_facts`: the memory's bounds and a row count per
table. -/
theorem buildLayout_sizes {bytecode : List K} {logMemory : ℕ} {tableRows : List ℕ}
    {layout : Layout} (h : buildLayout bytecode logMemory tableRows = some layout) :
    minLogMemory ≤ layout.logMemory ∧ layout.logMemory ≤ maxLogMemory ∧
      layout.tableRows.length = nTables := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hc.1, hc.2.1, hc.2.2.2.2.2⟩
    · cases h

/-- **What an announced layout is**: the program and `tables()`, a program of
`2^(BYTECODE_SLOT_BITS + log_bytecode)` words, the memory's bounds, a row count per table. -/
theorem announced_facts {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (h : Announced bytecode layout ρ) :
    layout.bytecode = bytecode ∧ layout.tables = tables ∧
      bytecode.length >>> bytecodeSlotBits = 2 ^ layout.logBytecode ∧
      minLogMemory ≤ layout.logMemory ∧ layout.logMemory ≤ maxLogMemory ∧
      layout.tableRows.length = nTables := by
  have hf := readSizes_facts h
  refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_⟩
  unfold Announced readAnnouncedSizes at h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨l, hl, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  have he := VerifierProgram.returns_ret h
  simp only [Prod.mk.injEq] at he
  rw [he.1]
  exact buildLayout_sizes (returns_liftOption hl)

/-- The program's bytecode has `16·2^logSize` words. -/
theorem length_bytecodeWords (program : LeanIsaProgram) :
    (bytecodeWords program).length = 16 * 2 ^ program.logSize := by
  simp [bytecodeWords, List.length_flatMap]
  ring

/-- At the program's own bytecode, the layout's program log-size is the program's. -/
theorem logBytecode_eq {program : LeanIsaProgram} {layout : Layout} {ρ : ℕ}
    (h : Announced (bytecodeWords program) layout ρ) : layout.logBytecode = program.logSize := by
  have h2 := (announced_facts h).2.2.1
  rw [length_bytecodeWords, Nat.shiftRight_eq_div_pow, show bytecodeSlotBits = 4 from rfl,
    show (2 : ℕ) ^ 4 = 16 from rfl, Nat.mul_div_cancel_left _ (by norm_num)] at h2
  exact (Nat.pow_right_injective le_rfl h2).symm

/-- `gpow` is `g`'s power, in `E`. -/
theorem gpow_eq_ofK (n : ℕ) : gpow n = ofK (g ^ n) := by
  show gen ^ n = algebraMap K E (g ^ n)
  rw [map_pow]
  rfl

/-- The link's initial state is leanISA's. -/
theorem regE_initial : regE Registers.initial = linkInit := by
  funext i
  fin_cases i <;> simp [regE, linkInit, Registers.initial]

/-- The link's final state is leanISA's. -/
theorem regE_final {program : LeanIsaProgram} {layout : Layout} (h : layout.logBytecode = program.logSize) :
    regE (Registers.final program) = linkFinal layout := by
  funext i
  fin_cases i <;> simp [regE, linkFinal, Registers.final, LeanIsaProgram.pcFinal, h, gpow_eq_ofK]

/-! ## The rows -/

/-- The executed rows are the cycle count. -/
theorem sum_range_getD (l : List ℕ) :
    ∑ i ∈ Finset.range l.length, l.getD i 0 = l.foldl (· + ·) 0 := by
  rw [← List.sum_eq_foldl]
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, ← ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem card_linkRow {layout : Layout} (h : layout.tableRows.length = nTables) :
    Fintype.card (LinkRow layout) = linkCycles layout := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  show ∑ i : Fin nTables, layout.tableRows.getD i 0 = layout.tableRows.foldl (· + ·) 0
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ layout.tableRows.getD i 0), ← h]
  exact sum_range_getD _

/-- The cycle count is below `2^W` at the link's width. -/
theorem linkCycles_lt {layout : Layout} {chunks : Chunks} (h : linkChunks layout = some chunks) :
    linkCycles layout < 2 ^ chunks.width := by
  rw [Chunks.new_width h, linkWidth, pointerWidth]
  have hb : linkCycles layout < 2 ^ bitLength (linkCycles layout) := by
    unfold bitLength
    split_ifs with h0
    · rw [h0]; norm_num
    · exact Nat.lt_log2_self
  exact hb.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- With no rows, the state link makes the initial state the final one. -/
theorem init_eq_final_of_zero {layout : Layout} {μ : ℕ} {q : Column μ} {chunks : Chunks}
    (hs : StateHolds layout q chunks) (hcard : Fintype.card (LinkRow layout) = 0)
    (hT : linkCycles layout = 0) : linkInit = linkFinal layout := by
  have h := hs 0 (Nat.two_pow_pos _)
  have hempty : IsEmpty (LinkRow layout) := Fintype.card_eq_zero_iff.mp hcard
  rw [hT] at h
  simp only [scatter, fiber, Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty] at h
  have h2 : aug linkInit - aug (linkFinal layout) = 0 := by simpa using h.symm
  exact aug_injective (sub_eq_zero.mp h2)

/-! ## The state columns -/

/-- Every table's `pc` and `fp` are its local columns `0` and `1`, which are no `KECCAK` output
lane. -/
theorem stateCols : ∀ t < nTables, (tables.getD t default).links.stateLink.pc = 0 ∧
    (tables.getD t default).links.stateLink.fp = 1 ∧
    keccakOutputLane (globalColumnBases.getD t 0 + 0) = none ∧
    keccakOutputLane (globalColumnBases.getD t 0 + 1) = none := by
  decide +kernel

/-- A state column's value is its committed word. -/
theorem tableValue_state {layout : Layout} (hT : layout.tables = tables) {μ : ℕ} (q : Column μ)
    {t : ℕ} (ht : t < nTables) (u : ℕ) :
    tableValue layout q t (tableAt layout t).links.stateLink.pc u =
        ofK (tableWord layout q t (tableAt layout t).links.stateLink.pc u) ∧
      tableValue layout q t (tableAt layout t).links.stateLink.fp u =
        ofK (tableWord layout q t (tableAt layout t).links.stateLink.fp u) := by
  obtain ⟨hpc, hfp, h0, h1⟩ := stateCols t ht
  simp only [tableAt, hT, hpc, hfp, tableValue, tableWord, columnValue]
  rw [h0, h1]
  exact ⟨rfl, rfl⟩

/-- A row's registers are its state words. -/
theorem regs_of_rowState {layout : Layout} (hT : layout.tables = tables) {μ : ℕ} {q : Column μ}
    {x : LinkRow layout} {r : Registers K} (h : rowState layout q x = regE r) :
    tableWord layout q x.1 (tableAt layout x.1).links.stateLink.pc x.2 = r.pc ∧
      tableWord layout q x.1 (tableAt layout x.1).links.stateLink.fp x.2 = r.fp := by
  obtain ⟨hpc, hfp⟩ := tableValue_state hT q x.1.isLt x.2
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [rowState, regE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    hpc, hfp] at h0 h1
  exact ⟨ofK_injective h0, ofK_injective h1⟩

/-! ## The first cycle in the final state -/

theorem foldl_min_le_init (L : List ℕ) (a : ℕ) : L.foldl min a ≤ a := by
  induction L generalizing a with
  | nil => exact le_rfl
  | cons b L ih => exact (ih _).trans (min_le_left _ _)

theorem foldl_min_le_mem {L : List ℕ} {c : ℕ} (hc : c ∈ L) (a : ℕ) : L.foldl min a ≤ c := by
  induction L generalizing a with
  | nil => simp at hc
  | cons b L ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact (foldl_min_le_init L _).trans (min_le_right _ _)
    · exact ih hc _

theorem foldl_min_cases (L : List ℕ) (a : ℕ) : L.foldl min a = a ∨ L.foldl min a ∈ L := by
  induction L generalizing a with
  | nil => exact .inl rfl
  | cons b L ih =>
    rcases ih (min a b) with h | h
    · rw [List.foldl_cons, h]
      rcases min_choice a b with h' | h'
      · exact .inl h'
      · exact .inr (by rw [h']; exact List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ h)

/-- The final cycles are the cycles of the rows in the final state. -/
theorem mem_finalCycles {layout : Layout} {μ : ℕ} {q : Column μ} {chunks : Chunks} {c : ℕ} :
    c ∈ finalCycles layout q chunks ↔ ∃ x : LinkRow layout,
      tableWord layout q x.1 (tableAt layout x.1).links.stateLink.pc x.2 =
          g ^ (2 ^ layout.logBytecode - 1) ∧
        tableWord layout q x.1 (tableAt layout x.1).links.stateLink.fp x.2 = 1 ∧
        (rowCycle layout q chunks x : ℕ) = c := by
  simp only [finalCycles, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, u, hu, hx⟩
    split_ifs at hx with hf
    · exact ⟨⟨⟨t, ht⟩, ⟨u, hu⟩⟩, hf.1, hf.2, Option.some.inj hx⟩
  · rintro ⟨⟨⟨t, ht⟩, ⟨u, hu⟩⟩, hpc, hfp, rfl⟩
    exact ⟨t, ht, u, hu, by simp only at hpc hfp; simp [hpc, hfp, rowCycle]⟩

/-! ## The relation's meaning, from the rows' steps -/

open Classical in
/-- **A valid execution from the chain**: at an announced layout, the state link, the public input
and a leanISA step per executed row give a valid execution, the extracted one. -/
theorem valid_of_rowSteps (program : LeanIsaProgram) (input : PublicInput) (layout : Layout)
    (ρ : ℕ) {μ : ℕ} (q : Column μ) (hA : Announced (bytecodeWords program) layout ρ)
    {chunks : Chunks} (hch : linkChunks layout = some chunks) (hs : StateHolds layout q chunks)
    (hpub : PubRel layout input q) (hsteps : ∀ x : LinkRow layout, RowStep program layout q x) :
    ValidExecution program input (candidate program layout q) := by
  obtain ⟨-, hT, -, hmin, hmax, hlen⟩ := announced_facts hA
  have hlb := logBytecode_eq hA
  have hcard := card_linkRow (layout := layout) hlen
  have hW := linkCycles_lt hch
  have hc : ValidChain (linkCycles layout) (rowCycle layout q chunks) (rowState layout q)
      (rowNext layout q) linkInit (linkFinal layout) := linkHolds_sound hcard hW hs
  choose regs regs' hstate hnext hstep using hsteps
  have hfinE := regE_final hlb
  obtain ⟨S, hS0, hST, hSt⟩ := chain_states hc regs regs' Registers.initial
    (Registers.final program)
    (fun u h ↦ regE_injective ((hstate u).symm.trans (h.trans regE_initial.symm)))
    (fun u v h ↦ regE_injective ((hnext u).symm.trans (h.trans (hstate v))))
    (fun u h ↦ regE_injective ((hnext u).symm.trans (h.trans hfinE.symm)))
    (fun h0 ↦ regE_injective (regE_initial.trans ((init_eq_final_of_zero hs (hcard.trans h0) h0).trans
      hfinE.symm)))
  have hsteps' : ∀ t < linkCycles layout, step program (memoryImage layout q) (S t) =
      some (S (t + 1)) := fun t ht ↦ by
    obtain ⟨u, -, h1, h2⟩ := hSt t ht
    rw [h1, h2]
    exact hstep u
  -- A row is in the final state exactly when its words are.
  have hfinal : ∀ x : LinkRow layout, regs x = Registers.final program ↔
      (tableWord layout q x.1 (tableAt layout x.1).links.stateLink.pc x.2 =
          g ^ (2 ^ layout.logBytecode - 1) ∧
        tableWord layout q x.1 (tableAt layout x.1).links.stateLink.fp x.2 = 1) := fun x ↦ by
    obtain ⟨hpc, hfp⟩ := regs_of_rowState hT (hstate x)
    rw [hpc, hfp, hlb]
    constructor
    · rintro h; rw [h]; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      cases hr : regs x
      simp only [hr] at h1 h2
      simp [Registers.final, LeanIsaProgram.pcFinal, h1, h2]
  set n := (finalCycles layout q chunks).foldl min (linkCycles layout) with hn
  have hn_le : n ≤ linkCycles layout := foldl_min_le_init _ _
  have hfirst : ∀ t < n, S t ≠ Registers.final program := by
    intro t ht hSf
    obtain ⟨u, hu, h1, -⟩ := hSt t (by omega)
    have hmem : t ∈ finalCycles layout q chunks :=
      mem_finalCycles.mpr ⟨u, ((hfinal u).mp (h1 ▸ hSf)).1, ((hfinal u).mp (h1 ▸ hSf)).2, hu⟩
    have := foldl_min_le_mem hmem (linkCycles layout)
    rw [← hn] at this
    omega
  have hnF : S n = Registers.final program := by
    rcases foldl_min_cases (finalCycles layout q chunks) (linkCycles layout) with h | h
    · rw [← hn] at h; rw [h, hST]
    · rw [← hn] at h
      obtain ⟨x, hpc, hfp, hx⟩ := mem_finalCycles.mp h
      have hxT : n < linkCycles layout := hx ▸ hc.lt x
      obtain ⟨u, hu, h1, -⟩ := hSt n hxT
      have hux : u = x := (hc.existsUnique n hxT).unique hu hx
      rw [h1, hux]
      exact (hfinal x).mpr ⟨hpc, hfp⟩
  refine ⟨⟨hmin, hmax, ?_, ?_⟩, ?_⟩
  · have hκ : layout.logMemory < 64 := by simp only [maxLogMemory] at hmax; omega
    have h0 : (0 : ℕ) < 2 ^ layout.logMemory := Nat.two_pow_pos _
    have := MemoryImage.read_gpow hκ (memoryImage layout q) ⟨0, h0⟩
    simp only [candidate] at this ⊢
    rw [this]
    simp [memoryImage, PublicInput.word0, hpub.1, hpub.2.1]
  · have hκ : layout.logMemory < 64 := by simp only [maxLogMemory] at hmax; omega
    have h1 : (1 : ℕ) < 2 ^ layout.logMemory :=
      Nat.one_lt_two_pow (by simp only [minLogMemory] at hmin; omega)
    have := MemoryImage.read_gpow hκ (memoryImage layout q) ⟨1, h1⟩
    simp only [candidate] at this ⊢
    rw [this]
    simp [memoryImage, PublicInput.word1, hpub.2.2.1, hpub.2.2.2]
  · show run program (memoryImage layout q) (firstFinal layout q) Registers.initial = _
    rw [firstFinal, hch, ← hS0]
    exact run_first_final program _ S (linkCycles layout) n hsteps' hn_le hnF hfirst

end

end LeanVM.Protocol.Relation
