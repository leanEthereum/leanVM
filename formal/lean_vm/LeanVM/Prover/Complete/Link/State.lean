/-
  LeanVM.Prover.Complete.Link.State

  The index side's state terms telescope along the run's states.
-/

module

public import LeanVM.Prover.Complete.Link.Steps
public import LeanVM.Prover.Complete.Link.IndexSplit
import LeanVM.Parameters.Field

/-!
# The state chain telescopes

The index side's state terms (`stateProds`, `Link/IndexSplit.lean`) are
`Σ_j eq(ζ, j)·A(j) + eq(ζ, j + 1)·B(j)`, `A` and `B` each executed row's state `ŝ = 1 + γ_pc·pc +
γ_fp·fp` and its successor's, scattered at its cycle pointer (`indexArrays_zero`,
`indexArrays_one`). On the honest witness:

* the cycle pointers are one-hot at the rows' cycles, so each sum against `A` or `B` is a sum over
  the executed rows (`sum_stateScatter`, from `Link/OneHot.lean`);
* row `u` of table `t` is the trace's step at its cycle `k`, its state the run's state `r_k` and
  its successor form (`Links.stateLink.next`) the state `r_{k+1}` its instruction executes to
  (`stateValues_rowOf`: `pc' = g·pc`, `fp' = fp`, or `JUMP`'s `pc_next`, `fp_next`;
  `stateWeight_witness`);
* the rows are the steps, once each (`sum_tablePairs`), so the sum is
  `Σ_{k < T} eq(ζ, k)·ŝ(r_k) + eq(ζ, k + 1)·ŝ(r_{k+1})`, which telescopes in characteristic two
  (`sum_telescope`) to `eq(ζ, 0)·ŝ(r_0) + eq(ζ, T)·ŝ(r_T)` (`stateProds_telescope`);
* `r_0 = (1, 1)`, `r_T = (g^(2^logBytecode − 1), 1)` and `T = Σ table_rows`
  (`indexStateIdentity_of`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Prover LeanVM.Extraction
open Finset

/-- A step other than `JUMP` goes to the next instruction in the same frame. -/
theorem executeWith_next {read : K → Option E} {r r' : Registers K} {ins : LeanIsaInstruction}
    (hj : ins.opcode ≠ .jump) (h : executeWith read r ins = some r') : r' = r.next := by
  cases ins <;> simp [executeWith, LeanIsaInstruction.opcode, Option.bind_eq_some_iff] at h hj <;>
    (repeat obtain ⟨_, h⟩ := h) <;> rfl

/-- `ŝ_γ = 1 + γ_pc·pc + γ_fp·fp`, a state as the index side weighs it. -/
def stateHat (ch : LinkChallenges) (r : Registers K) : E :=
  1 + ch.gammaState.getD 0 0 * ofK r.pc + ch.gammaState.getD 1 0 * ofK r.fp

/-- A table's state values from its `pc`, `fp` and successor columns. -/
theorem stateValues_of (ch : LinkChallenges) {links : Links} {col : ℕ → E} {r r' : Registers K}
    (hpc : links.stateLink.pc = 0) (hfp : links.stateLink.fp = 1) (h0 : col 0 = ofK r.pc)
    (h1 : col 1 = ofK r.fp) (hn1 : links.stateLink.next.1.evaluate col = ofK r'.pc)
    (hn2 : links.stateLink.next.2.evaluate col = ofK r'.fp) :
    stateValues ch links col = (stateHat ch r, stateHat ch r') := by
  simp only [stateValues, hpc, hfp, h0, h1, hn1, hn2, stateHat]

theorem limb_zero_iff {x : E} (hx : IsInK x) : x.limb 0 = 0 ↔ x = 0 := by
  obtain ⟨a, rfl⟩ := (isInK_iff x).mp hx
  simp only [limb_ofK, Fin.isValue, Fin.val_zero, ↓reduceIte]
  exact ⟨fun h ↦ by rw [h]; exact map_zero (algebraMap K E),
    fun h ↦ ofK_injective (h.trans (map_zero (algebraMap K E)).symm)⟩

/-- **A row's state values are its step's**: the state it steps from and the state it reaches. -/
theorem stateValues_rowOf {κ : ℕ} (hκ : κ < 64) (img : MemoryImage κ) (chunks : Chunks)
    (k : ℕ) {r r' : Registers K} (slot : ℕ) {ins : LeanIsaInstruction}
    (h : executeWith img.read r ins = some r') (ch : LinkChallenges) :
    stateValues ch (tables.getD (opTableIdx ins.opcode) default).links
        (fun c ↦ ofK ((rowOf ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, slot, ins⟩).getD c 0)) =
      (stateHat ch r, stateHat ch r') := by
  have hs := rowOf_state ⟨powIndex κ, img, chunks⟩ k ⟨r.pc, r.fp, slot, ins⟩
  obtain ⟨hpc, hfp, -⟩ := LeanVM.Protocol.Relation.stateCols _ (opTableIdx_lt ins.opcode)
  refine stateValues_of ch hpc hfp (by rw [hs.2.1]) (by rw [hs.2.2.1]) ?_ ?_
  all_goals
    by_cases hj : ins.opcode = .jump
    swap
    · have hnext : (tables.getD (opTableIdx ins.opcode) default).links.stateLink.next =
          (Form.col 0 1, Form.col 1 0) := by
        cases ins <;> simp [LeanIsaInstruction.opcode] at hj <;> rfl
      rw [executeWith_next hj h, hnext]
      simp only [LeanVM.Protocol.Relation.Form.col_evaluate, hs.2.1, hs.2.2.1, Registers.next,
        LeanVM.Protocol.Relation.gpow_eq_ofK, pow_one, pow_zero, ← ofK_mul, one_mul]
    · cases ins <;> simp [LeanIsaInstruction.opcode] at hj
      rename_i oc od of
      have hread : readIn (powIndex κ) img = img.read := by
        funext a
        unfold readIn MemoryImage.read
        rw [gLogIn_powIndex hκ]
      have hnext : (tables.getD opJump default).links.stateLink.next =
          (Form.col 5 0, Form.col 6 0) := rfl
      simp [executeWith, Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, d, hd, f, hf, ⟨hic, -, -⟩, rfl⟩ := h
      simp only [opTableIdx, LeanIsaInstruction.opcode, hnext,
        LeanVM.Protocol.Relation.Form.col_evaluate, LeanVM.Protocol.Relation.gpow_eq_ofK,
        pow_zero, rowOf, FillCtx.limbs, limbsIn, hread, hc, hd, hf]
      by_cases hc0 : c = 0
      · have hl : c.limb 0 = 0 := (limb_zero_iff hic).mpr hc0
        simp only [hl]
        simp [hc0, Registers.next, mul_comm]
      · have hl : c.limb 0 ≠ 0 := fun h ↦ hc0 ((limb_zero_iff hic).mp h)
        simp [hc0, hl]


/-! ## The index side's state arrays -/

theorem foldl_vec_get {α β : Type} {n : ℕ} (F : Vector α n → β → Vector α n) (G : α → β → α)
    (i : Fin n) (hF : ∀ v b, (F v b)[i] = G v[i] b) :
    ∀ (L : List β) (v : Vector α n), (L.foldl F v)[i] = L.foldl G v[i]
  | [], _ => rfl
  | b :: L, v => by rw [List.foldl_cons, List.foldl_cons, foldl_vec_get F G i hF L, hF]

/-- Row `u` of table `t`'s state (`k = 0`) or successor (`k = 1`), as the index side weighs it. -/
def stateWeight (W : Witness) (ch : LinkChallenges) (k t u : ℕ) : E :=
  if k = 0 then (stateValues ch (tables.getD t default).links (rowValue (W.tableCols t) u)).1
  else (stateValues ch (tables.getD t default).links (rowValue (W.tableCols t) u)).2

/-- The states scattered at the cycle pointers (`k = 0`) or the successors (`k = 1`). -/
def stateScatter (W : Witness) (ch : LinkChallenges) (k : ℕ) (a : Array E) (t : ℕ) : Array E :=
  scatterWords W.chunks ((W.tableCols t).getD (tables.getD t default).links.stateLink.cycle #[])
    (W.rows.getD t 0) 0 (stateWeight W ch k t) a

theorem indexArrays_zero (W : Witness) (ch : LinkChallenges) :
    (indexArrays W ch).getD 0 #[] =
      (List.range nTables).foldl (stateScatter W ch 0) (Array.replicate (2 ^ W.chunks.width) 0) :=
  foldl_vec_get _ _ 0 (fun _ _ ↦ rfl) _ _

theorem indexArrays_one (W : Witness) (ch : LinkChallenges) :
    (indexArrays W ch).getD 1 #[] =
      (List.range nTables).foldl (stateScatter W ch 1) (Array.replicate (2 ^ W.chunks.width) 0) :=
  foldl_vec_get _ _ 1 (fun _ _ ↦ rfl) _ _


theorem size_foldl_stateScatter (W : Witness) (ch : LinkChallenges) (k : ℕ) (L : List ℕ)
    (a : Array E) : (L.foldl (stateScatter W ch k) a).size = a.size := by
  induction L generalizing a with
  | nil => rfl
  | cons t L ih => rw [List.foldl_cons, ih, stateScatter, size_scatterWords]

/-- **A sum against a state array is a sum over the executed rows**, each at its cycle. -/
theorem sum_stateScatter {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex)
    (ch : LinkChallenges) (k : ℕ) (f : ℕ → E) : ∀ n ≤ nTables,
      ∑ j ∈ range (2 ^ W.chunks.width), f j * ((List.range n).foldl (stateScatter W ch k)
          (Array.replicate (2 ^ W.chunks.width) 0)).getD j 0 =
        ∑ t ∈ range n, ∑ u ∈ range (W.rows.getD t 0),
          f (rowCycle (traceSteps ex) t u) * stateWeight W ch k t u
  | 0, _ => by
    simp only [List.range_zero, List.foldl_nil, Finset.range_zero, Finset.sum_empty]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    simp [Array.getD_eq_getD_getElem?, Finset.mem_range.mp hj]
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ,
      ← sum_stateScatter hW hv ch k f n (by omega)]
    have ha := size_foldl_stateScatter W ch k (List.range n) (Array.replicate (2 ^ W.chunks.width) 0)
    rw [Array.size_replicate] at ha
    generalize (List.range n).foldl (stateScatter W ch k) (Array.replicate (2 ^ W.chunks.width) 0) = a
      at ha ⊢
    rw [← ha, stateScatter, sum_mul_scatterWords_zero (width_witness hW hv).1
      (cycle_oneHot hW hv (by omega)) _ a ha]


/-- **An executed row's state and successor** are the run's states at its cycle and the next. -/
theorem stateWeight_witness {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex)
    (ch : LinkChallenges) {t u : ℕ} (ht : t < nTables) (hu : u < W.rows.getD t 0) :
    rowCycle (traceSteps ex) t u < ex.stepCount ∧
      stateWeight W ch 0 t u = stateHat ch (stateAt ex (rowCycle (traceSteps ex) t u)) ∧
      stateWeight W ch 1 t u = stateHat ch (stateAt ex (rowCycle (traceSteps ex) t u + 1)) := by
  rw [rows_witness hW hv ht] at hu
  have hpt := mem_tablePairs (List.getElem_mem hu)
  obtain ⟨hk, hst⟩ := tablePairs_step (List.getElem_mem hu)
  have hrc : rowCycle (traceSteps ex) t u = (tablePairs (traceSteps ex) t)[u].2 := by
    simp [rowCycle, hu]
  simp only [stateWeight, rowValue_witness hW hv ht hu, hrc, ↓reduceIte, one_ne_zero]
  generalize (tablePairs (traceSteps ex) t)[u] = p at hpt hk hst ⊢
  obtain ⟨st, k⟩ := p
  dsimp only at hpt hk hst ⊢
  subst hst
  have key := stateValues_rowOf (logMemorySize_lt hv) ex.memory W.chunks k
    (stepOf prog (stateAt ex k)).slot (step_succ hv hk) ch
  rw [hpt] at key
  exact ⟨hk, congrArg Prod.fst key, congrArg Prod.snd key⟩


/-! ## The telescope -/

open LeanVM.Protocol.Hotwire (eqAt) in
theorem getD_eqTable_eqAt (pt : List E) (j : ℕ) :
    (eqTable pt).getD j 0 = if j < 2 ^ pt.length then eqAt pt j else 0 := by
  rw [Keccak.getD_toList, Keccak.toList_eqTable, LeanVM.Protocol.Hotwire.eqKernel_getD]

/-- In characteristic two, consecutive pairs telescope to the ends. -/
theorem sum_telescope (a : ℕ → E) : ∀ T, ∑ k ∈ range T, (a k + a (k + 1)) = a 0 + a T
  | 0 => by simp [CharTwo.add_self_eq_zero]
  | T + 1 => by
    rw [Finset.sum_range_succ, sum_telescope a T]
    linear_combination CharTwo.add_self_eq_zero (a T)

theorem stateProds_cubeSum (W : Witness) (ch : LinkChallenges) (m : ℕ) :
    cubeSum m (stateProds W ch) = ∑ j ∈ range m,
      ((eqTable ch.zeta).getD j 0 * ((indexArrays W ch).getD 0 #[]).getD j 0 +
        (Array.ofFn (n := 2 ^ W.chunks.width) fun j ↦ (eqTable ch.zeta).getD (j.val + 1) 0).getD j 0 *
          ((indexArrays W ch).getD 1 #[]).getD j 0) := by
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [termsAt_eq]
  have h6 : (indexArrays W ch).getD 6 #[] = eqTable ch.zeta := rfl
  have h7 : (indexArrays W ch).getD 7 #[] =
      Array.ofFn (n := 2 ^ W.chunks.width) fun j ↦ (eqTable ch.zeta).getD (j.val + 1) 0 := rfl
  simp only [stateProds, List.foldl_cons, List.foldl_nil, termAt, ← Array.foldl_toList,
    List.toList_toArray]
  rw [h6, h7]
  ring

open LeanVM.Protocol.Hotwire (eqAt) in
/-- **The state terms telescope**: on the honest witness, at any `ζ` of the pointer width and any
`γ`, `Σ_j eq(ζ, j)·A(j) + eq(ζ, j + 1)·B(j) = eq(ζ, 0)·ŝ(r_0) + eq(ζ, T)·ŝ(r_T)`. -/
theorem stateProds_telescope {prog : LeanIsaProgram} {input : PublicInput} {ex : Execution prog}
    {W : Witness} (hW : witness? prog input ex = some W) (hv : ValidExecution prog input ex)
    (ch : LinkChallenges) (hz : ch.zeta.length = W.chunks.width) :
    cubeSum (2 ^ W.chunks.width) (stateProds W ch) =
      eqAt ch.zeta 0 * stateHat ch (stateAt ex 0) +
        eqAt ch.zeta ex.stepCount * stateHat ch (stateAt ex ex.stepCount) := by
  have hT := (width_witness hW hv).2.2.1
  set a : ℕ → E := fun k ↦ eqAt ch.zeta k * stateHat ch (stateAt ex k) with ha
  rw [stateProds_cubeSum, Finset.sum_add_distrib, indexArrays_zero, indexArrays_one,
    sum_stateScatter hW hv ch 0 _ nTables le_rfl, sum_stateScatter hW hv ch 1 _ nTables le_rfl,
    ← Finset.sum_add_distrib]
  have hrow : ∀ t ∈ range nTables, (∑ u ∈ range (W.rows.getD t 0),
      (eqTable ch.zeta).getD (rowCycle (traceSteps ex) t u) 0 * stateWeight W ch 0 t u) +
      (∑ u ∈ range (W.rows.getD t 0),
        (Array.ofFn (n := 2 ^ W.chunks.width) fun j ↦ (eqTable ch.zeta).getD (j.val + 1) 0).getD
          (rowCycle (traceSteps ex) t u) 0 * stateWeight W ch 1 t u) =
      ∑ u ∈ range (tablePairs (traceSteps ex) t).length,
        (((tablePairs (traceSteps ex) t)[u]?).map fun p ↦ a p.2 + a (p.2 + 1)).getD 0 := by
    intro t ht
    have ht := Finset.mem_range.mp ht
    rw [← Finset.sum_add_distrib, ← rows_witness hW hv ht]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    have hu := Finset.mem_range.mp hu
    obtain ⟨hk, h0, h1⟩ := stateWeight_witness hW hv ch ht hu
    have hu' := hu
    rw [rows_witness hW hv ht] at hu'
    have hrc : rowCycle (traceSteps ex) t u = (tablePairs (traceSteps ex) t)[u].2 := by
      simp [rowCycle, hu']
    rw [List.getElem?_eq_getElem hu', Option.map_some, Option.getD_some, ← hrc, h0, h1,
      getD_eqTable_eqAt, Keccak.getD_ofFn' _ (by omega), getD_eqTable_eqAt, hz,
      ite_eq_left (show rowCycle (traceSteps ex) t u < 2 ^ W.chunks.width by omega),
      ite_eq_left (show rowCycle (traceSteps ex) t u + 1 < 2 ^ W.chunks.width by omega)]
  rw [Finset.sum_congr rfl hrow, sum_tablePairs, length_traceSteps]
  rw [Finset.sum_congr rfl fun k hk ↦ by
    rw [getElem?_traceSteps ex (Finset.mem_range.mp hk), Option.map_some, Option.getD_some]]
  exact sum_telescope a ex.stepCount


/-! ## The identity -/

/-- **The index side's state terms telescope** on the honest witness of every admitted execution:
`Σ_j eq(ζ, j)·A(j) + eq(ζ, j + 1)·B(j) = eq(ζ, 0)·ŝ_init + eq(ζ, T)·ŝ_fin`. -/
theorem indexStateIdentity_of {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {ρ : ℕ} {W : Witness} (hA : Admitted prog input t ρ W) : IndexStateIdentity W := by
  intro theta0 drawn hlen
  dsimp only
  have hz := length_zeta tables rfl (linkNRows W) W.chunks.width W.chunks.d theta0 drawn hlen
  generalize LinkChallenges.ofDraw tables (linkNRows W) W.chunks.width W.chunks.d theta0 drawn = ch
    at hz ⊢
  have hle : ∀ j, linkEqAt ch.zeta j = LeanVM.Protocol.Hotwire.eqAt ch.zeta j := fun j ↦
    LeanVM.Protocol.Hotwire.linkEqAt_eq _ _
  rw [stateProds_telescope hA.witness hA.valid _ hz, stateAt_zero, stateAt_stepCount hA.valid,
    hle, hle]
  obtain ⟨hr, -, hl, -⟩ := witness_steps hA.witness hA.valid
  have hT : W.layout.tableRows.foldl (· + ·) 0 = t.stepCount := by
    rw [foldl_add_eq_sum, (buildLayout_spec hl).2.1, (width_witness hA.witness hA.valid).2.1]
  rw [hT, logBytecode_witness hl]
  simp only [stateHat, Registers.initial, Registers.final, LeanIsaProgram.pcFinal,
    LeanVM.Protocol.Relation.ofK_one, LeanVM.Protocol.Relation.gpow_eq_ofK, addressOfIndex]

end LeanVM.Prover.Complete

end
