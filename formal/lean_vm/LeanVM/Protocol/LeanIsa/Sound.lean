/-
  LeanVM.Protocol.LeanIsa.Sound

  The adaptor's soundness direction: a stack satisfying the leanISA instance's relation carries a
  witness satisfying leanISA's constraint system.
-/

module

public import LeanVM.Protocol.LeanIsa.Relation

/-!
# The adaptor, soundness

`satisfiedBy_witnessOf`: if the announced sizes are admissible and the stack `q` satisfies
`M3Holds` of the leanISA instance on the input, then the witness read off `q` (`witnessOf`)
satisfies `SatisfiedBy` on it. Every conjunct of `SatisfiedBy` comes from one clause of `M3Holds`,
from admissibility, or from how the witness is read:

* the Clean constraints, the three channel pairs' balances and the nonzero read counts from the
  constraints, the bus and the count clauses, through the witness agreeing with its stack
  (`agrees_witnessOf`, with the equivalences of `LeanIsa/Relation.lean`);
* the public input and the two public words from the three public lines, which fix the first two
  cells of the memory columns (`publicLines_cells`), and the image the data names, which is the
  memory columns at the announced size (`imageOf_witnessOf`);
* the caps from admissibility; the index column, the seed rows and the bytecode rows by
  construction;
* **the BLAKE2s validity** (`blake2sRowsValid_witnessOf`) from the Flock clause. leanISA's
  `Blake2sRowsValid` asks every `BLAKE2S` row to satisfy `Blake2sRelation`, the compression on its
  eighteen limbs. The instance never commits the limbs: it reads them off the Flock region at the
  specification's slots, so the limbs of row `x` are the cells block `x` of the region carries
  there (`slotLimbs_flockColumn`). The Flock clause says every block satisfies the R1CS with the
  constant pinned, and `FlockSpec.compress_of_holds` turns that into the compression at the slots.
  No hypothesis beyond `M3Holds` is needed: the compression is proved, not assumed.

Admissibility is a hypothesis because `Caps` does not follow from `M3Holds`: the compiled
verifier checks the announced sizes before the protocol starts.
-/

namespace LeanVM.Protocol.LeanIsa

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization CompPoly CMlPolynomialEval
open Air.Flat (Component EnsembleWitness)

@[expose] public section

/-- A raw `BLAKE2S` row of at least twenty-seven cells is a compression exactly when its limbs,
cells `9 … 26`, are. -/
theorem blake2sRelation_ofFn {n : ℕ} (r : Fin n → K) (hn : 27 ≤ n) (data : ProverData K) :
    Blake2sRelation (valueFromOffset Blake2sRow 0 (Environment.fromArray (Array.ofFn r) data)) ↔
      LimbsCompress fun k ↦ r ⟨9 + k, by omega⟩ := by
  unfold Blake2sRelation LimbsCompress
  simp [valueFromOffset, explicit_provable_type, circuit_norm, Array.getElem?_ofFn,
    show 9 < n by omega, show 10 < n by omega, show 11 < n by omega, show 12 < n by omega,
    show 13 < n by omega, show 14 < n by omega, show 15 < n by omega, show 16 < n by omega,
    show 17 < n by omega, show 18 < n by omega, show 19 < n by omega, show 20 < n by omega,
    show 21 < n by omega, show 22 < n by omega, show 23 < n by omega, show 24 < n by omega,
    show 25 < n by omega, show 26 < n by omega]

variable (F : FlockSpec) (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- The `BLAKE2S` rows of the witness read off a stack are the rows of opcode table `5`. -/
private theorem blake2sRows_witnessOf :
    blake2sRows (witnessOf F prog s q) = opcodeRows F prog s q 5 := rfl

/-- **The BLAKE2s validity.** On a stack whose Flock region satisfies the region predicate, every
`BLAKE2S` row of the witness read off it is a compression: its limbs are the cells the region's
block carries at the specification's slots, and the specification's soundness makes them a
compression. -/
theorem blake2sRowsValid_witnessOf (h : (leanIsaInstance F prog s).aux q) :
    Blake2sRowsValid (witnessOf F prog s q) := by
  intro row hrow
  rw [blake2sRows_witnessOf, opcodeRows, List.mem_ofFn] at hrow
  obtain ⟨x, rfl⟩ := hrow
  refine (blake2sRelation_ofFn _ (le_trans (by decide : 27 ≤ 37) width_blake2s.ge) _).mpr ?_
  have hc := F.compress_of_holds _ (h (flockRegion prog s F) rfl) (Fin.castLE (s.rows_le 5) x)
  exact (congrArg LimbsCompress (slotLimbs_flockColumn F prog s q _)).mp hc

/-! ## The witness agrees with its stack -/

/-- The opcode tables of the witness read off a stack are the stack's rows. -/
private theorem opTable_witnessOf (j : Fin 6) :
    (opTable (witnessOf F prog s q) j).table = opcodeRows F prog s q j := by
  fin_cases j <;> rfl

/-- The witness read off a stack agrees with it. -/
theorem agrees_witnessOf : Agrees F s q (witnessOf F prog s q) where
  length j := by rw [opTable_witnessOf, opcodeRows, List.length_ofFn]
  cells j x i := by
    rw [cellOf, opTable_witnessOf, opcodeRows]
    have hlt : (i : ℕ) < (shape prog s).width (opIdx j) := i.isLt
    simp only [List.getElem?_ofFn, Array.getElem?_ofFn, Option.bind_some, Fin.is_lt, dite_true,
      hlt, Option.getD_some]
    rfl
  memRows := rfl
  bytecodeRows := rfl

/-! ## The image and the public input -/

/-- The prover data's `"mem"` table is the image read off the memory columns. -/
private theorem memRows_witnessOf : memRows (witnessOf F prog s q).data = imageRows F prog s q := by
  simp [memRows, witnessOf, dataOf]

/-- Two images are equal when their sizes are and their words agree. -/
theorem image_sigma_eq {κ κ' : ℕ} (h : κ = κ') (f : MemImage κ) (g : MemImage κ')
    (hfg : ∀ i : Fin (2 ^ κ), f i = g (Fin.cast (by rw [h]) i)) :
    (⟨κ, f⟩ : (κ : ℕ) × MemImage κ) = ⟨κ', g⟩ := by
  subst h
  congr
  funext i
  exact hfg i

/-- The word of the image at index `x`: the three memory columns' cells. -/
abbrev imageWord (x : Fin (2 ^ s.logMem)) : E :=
  E.ofLimbs (cell F prog s q (memCol 0) x) (cell F prog s q (memCol 1) x)
    (cell F prog s q (memCol 2) x)

/-- Within the memory cap, the image the witness's data names is the memory columns, word by
word, at the announced memory size. -/
theorem imageOf_witnessOf (h : s.logMem ≤ maxLogMem) :
    imageOf (witnessOf F prog s q).data = ⟨s.logMem, imageWord F prog s q⟩ := by
  unfold imageOf
  rw [memRows_witnessOf]
  have hsz : (imageRows F prog s q).size = 2 ^ s.logMem := Array.size_ofFn
  refine image_sigma_eq (by rw [hsz, Nat.log_pow (by norm_num), Nat.min_eq_left h]) _ _
    fun i ↦ ?_
  have hi : (i : ℕ) < 2 ^ s.logMem := hsz ▸ (i.isLt.trans_le (by
    rw [hsz, Nat.log_pow (by norm_num), Nat.min_eq_left h]))
  simp [imageRows, hi]
  rfl

/-- The three public lines fix the first two cells of the three memory columns. -/
theorem publicLines_cells {input : PublicInput}
    (hp : (leanIsaInstance F prog s).PublicLinesHold input q) :
    cell0 F prog s q 0 = input.lanes 0 ∧ cell1 F prog s q 0 = input.lanes 2 ∧
      cell0 F prog s q 1 = input.lanes 1 ∧ cell1 F prog s q 1 = input.lanes 3 ∧
      cell0 F prog s q 2 = 0 ∧ cell1 F prog s q 2 = 0 := by
  have h0 := hp _ (List.mem_cons_self (l := [_, _]))
  have h1 := hp _ (List.mem_cons_of_mem _ (List.mem_cons_self (l := [_])))
  have h2 := hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self (l := []))))
  exact ⟨h0.1, h0.2, h1.1, h1.2, h2.1, h2.2⟩

/-! ## The constraints and the caps -/

/-- A component with neither constraints nor lookups holds on every row. -/
private theorem constraintsHold_of_nil (c : Component K) (h₁ : c.rowOperations.constraints = [])
    (h₂ : c.rowOperations.lookups = []) (env : Environment K) :
    c.operations.ConstraintsHold env := by
  rw [Air.Flat.Component.constraintsHold_iff, Operations.ConstraintsHold, h₁, h₂]
  simp

/-- On a stack whose constraint polynomials vanish, every table of the witness read off it
satisfies its Clean constraints. -/
theorem constraints_witnessOf (hcv : (leanIsaInstance F prog s).ConstraintsVanish q) :
    (witnessOf F prog s q).Constraints := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact fun _ _ ↦ constraintsHold_of_nil _ rfl rfl _
  · obtain ⟨⟨j, hj⟩, rfl⟩ := mem_tables_iff.mp ht
    by_cases h6 : j < 6
    · exact (opcode_constraints_iff (agrees_witnessOf F prog s q) ⟨j, h6⟩).mpr
        fun x C hC ↦ hcv (opIdx ⟨j, h6⟩) C hC _
    · have : j = 6 ∨ j = 7 := by omega
      rcases this with rfl | rfl
      · intro row _
        rw [tableAt_component]
        exact constraintsHold_of_nil _ rfl rfl _
      · intro row _
        rw [tableAt_component]
        exact constraintsHold_of_nil _ rfl rfl _

/-- The tables of the witness read off a stack have the announced row counts. -/
private theorem table_length_witnessOf (j : Fin 8) :
    (tableAt (witnessOf F prog s q) j).table.length =
      ![s.rows 0, s.rows 1, s.rows 2, s.rows 3, s.rows 4, s.rows 5, 2 ^ s.logMem,
        2 ^ prog.logSize] j := by
  fin_cases j <;> exact List.length_ofFn

/-- On admissible sizes, the witness read off a stack is within the caps. -/
theorem caps_witnessOf (hs : s.Admissible prog) : Caps (witnessOf F prog s q) := by
  obtain ⟨hmin, hmax, hrows, -⟩ := hs
  have himg := imageOf_witnessOf F prog s q hmax
  refine ⟨?_, ?_, ?_, ⟨?_⟩⟩
  · rw [himg]
    exact hmin
  · rw [himg]
    exact hmax
  · intro t ht
    obtain ⟨j, rfl⟩ := mem_tables_iff.mp ht
    rw [table_length_witnessOf F prog s q j]
    fin_cases j
    exacts [hrows 0, hrows 1, hrows 2, hrows 3, hrows 4, hrows 5,
      Nat.pow_le_pow_right (by norm_num) hmax,
      Nat.pow_le_pow_right (by norm_num) prog.logSize_le]
  · rw [memRows_witnessOf, himg]
    exact Array.size_ofFn

/-- The seed rows are the image, for an image given as a dependent pair. -/
private def SeedRowsAre {prog : Program} (w : EnsembleWitness (leanIsaEnsemble prog))
    (d : (κ : ℕ) × MemImage κ) : Prop :=
  ∃ idx cntFin : Fin (2 ^ d.1) → K, memBlockRows w = List.ofFn fun i ↦
    (toElements (⟨idx i, cntFin i, #v[(d.2 i).limb 0, (d.2 i).limb 1, (d.2 i).limb 2]⟩ :
      MemRow K)).toArray

/-- `SeedRowsAreTheImage` is `SeedRowsAre` of the image the data names. -/
private theorem seedRows_iff {prog : Program} (w : EnsembleWitness (leanIsaEnsemble prog)) :
    SeedRowsAreTheImage w ↔ SeedRowsAre w (imageOf w.data) := Iff.rfl

/-! ## The adaptor -/

/-- **The adaptor, soundness.** If the announced sizes are admissible and the stack `q`
satisfies the leanISA instance's relation on the input, then the witness read off `q` satisfies
leanISA's constraint system on it. -/
theorem satisfiedBy_witnessOf {input : PublicInput} (hs : s.Admissible prog)
    (h : M3Holds (leanIsaInstance F prog s) input q) :
    SatisfiedBy prog input (witnessOf F prog s q) := by
  obtain ⟨hcv, hbal, hcnt, hpl, haux⟩ := h
  have hmax : s.logMem ≤ maxLogMem := hs.2.1
  have hA := agrees_witnessOf F prog s q
  have hpairs := (balanced_iff_pairs hA).mp hbal
  have himg := imageOf_witnessOf F prog s q hmax
  obtain ⟨c00, c01, c10, c11, c20, c21⟩ := publicLines_cells F prog s q hpl
  have hκ : s.logMem < 64 := lt_of_le_of_lt hmax (by decide)
  refine ⟨?_, constraints_witnessOf F prog s q hcv, hpairs 0, hpairs 1, hpairs 2,
    (countsNonzero_iff hA).mpr hcnt, caps_witnessOf F prog s q hs, ?_, ?_, ⟨_, rfl⟩,
    blake2sRowsValid_witnessOf F prog s q haux, ?_, ?_⟩
  · show publicInputOf F prog s q = PublicIO.ofInput input
    rw [publicInputOf, PublicIO.ofInput, c00, c01, c10, c11]
  · intro i hi
    show (memRowAt _ ((memBlockRowsOf F prog s q)[i]'hi)).idx = gpow i
    simp only [memBlockRowsOf, List.getElem_ofFn, memRowAt_toElements]
  · rw [seedRows_iff, himg]
    refine ⟨fun x ↦ gpow x, fun x ↦ cell F prog s q (memCol 3) x, ?_⟩
    show memBlockRowsOf F prog s q = _
    simp only [memBlockRowsOf, imageWord, limb_ofLimbs]
    rfl
  · rw [himg]
    have := MemImage.read_gpow hκ (imageWord F prog s q) ⟨0, Nat.two_pow_pos _⟩
    refine this.trans ?_
    show some (E.ofLimbs (cell0 F prog s q 0) (cell0 F prog s q 1) (cell0 F prog s q 2)) = _
    rw [c00, c10, c20]
    rfl
  · rw [himg]
    have := MemImage.read_gpow hκ (imageWord F prog s q)
      ⟨1, Nat.one_lt_two_pow s.logMem_pos.ne'⟩
    refine this.trans ?_
    show some (E.ofLimbs (cell1 F prog s q 0) (cell1 F prog s q 1) (cell1 F prog s q 2)) = _
    rw [c01, c11, c21]
    rfl

end

end LeanVM.Protocol.LeanIsa
