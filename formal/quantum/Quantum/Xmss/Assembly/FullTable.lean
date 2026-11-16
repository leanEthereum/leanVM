module

public import Quantum.Xmss.Assembly.MassSources
public import Quantum.Xmss.Assembly.TableComp
public import Quantum.Xmss.Assembly.GameT

@[expose] public section

/-!
# Runtime 1 with the full honest table hardwired

The honest computation `fullComp S₀` of every hidden value of a table (design R0, section 3): the
scheme seed `S`, the parameter `P`, the chain starts' hashes, then every value position by
MassSources' `posM` and every label's randomizer base, tabulated over their (huge) finite index
types (`tabulate`, through `Fintype.equivFin`, so that no enumeration of the index type is ever
unfolded). Its cells `fullHw L` are runtime 1's hardwired table.

* `fst_honestEval_fullComp`: the computation returns `(L.param, valueAt L)`.
* `tableLe_fullHw`: the cells the template game programs (`tableHw L`) lie in `fullHw L`, with its
  values: every in-table slot's honest input is hashed by `fullComp`.
* `winProb_eq_uavg_full`: **G0 is the table average of runtime 1 with `fullHw L` hardwired,
  running the grind-only game `gameReadsT`** (G1 → G2 by `qrpm_game_eq_reads`, the two signers by
  `evalDistMap_gameReads_eq_gameReadsT`, G2 → runtime 1 by `spongeEvalDistMap_eq_avg_runtime1` at
  `fullComp`, whose result determines `gameReadsT` up to the unused keys, `gameReadsT_keys`).
-/

open MeasureTheory
open scoped ENNReal

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma HashSig.OverPermutation

/-! ## Tabulating a computation over a finite type -/

section tabulate

variable (f : QueryImpl HashSpec Id)

/-- **A computation for every index of a finite type**, run in the order of `Fintype.equivFin`. -/
noncomputable def tabulate {ι β : Type} [Fintype ι] (c : ι → OracleComp HashSpec β) :
    OracleComp HashSpec (ι → β) :=
  sequenceFin (fun k ↦ c ((Fintype.equivFin ι).symm k)) >>= fun g ↦
    pure fun i ↦ g (Fintype.equivFin ι i)

theorem eval_hashQ (input : HashInput) : evalWithAnswerFn f (hashQ input) = f input :=
  rfl

/-- The tabulated values are the values. -/
theorem eval_tabulate {ι β : Type} [Fintype ι] (c : ι → OracleComp HashSpec β) :
    evalWithAnswerFn f (tabulate c) = fun i ↦ evalWithAnswerFn f (c i) := by
  rw [tabulate, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure]
  funext i
  simp only [Equiv.symm_apply_apply]

theorem mem_queries_bind_left {α β : Type} (x : OracleComp HashSpec α)
    (k : α → OracleComp HashSpec β) {q : HashInput} (h : q ∈ queries f x) :
    q ∈ queries f (x >>= k) := by
  rw [queries, trace_bind]
  exact List.mem_append_left _ h

theorem mem_queries_sequenceFin {β : Type} {q : HashInput} :
    ∀ {n : ℕ} (c : Fin n → OracleComp HashSpec β) (i : Fin n), q ∈ queries f (c i) →
      q ∈ queries f (sequenceFin c)
  | 0, _, i, _ => i.elim0
  | n + 1, c, i, h => by
    simp only [sequenceFin]
    cases i using Fin.cases with
    | zero => exact mem_queries_bind_left f _ _ h
    | succ j =>
      exact mem_queries_bind_right f _ _ (mem_queries_bind_left f _ _
        (mem_queries_sequenceFin (fun k : Fin n ↦ c k.succ) j h))

/-- Every query of a tabulated computation is a query of the tabulation. -/
theorem mem_queries_tabulate {ι β : Type} [Fintype ι] (c : ι → OracleComp HashSpec β) (i : ι)
    {q : HashInput} (h : q ∈ queries f (c i)) : q ∈ queries f (tabulate c) := by
  refine mem_queries_bind_left f _ _
    (mem_queries_sequenceFin f _ (Fintype.equivFin ι i) ?_)
  show q ∈ queries f (c ((Fintype.equivFin ι).symm (Fintype.equivFin ι i)))
  rw [Equiv.symm_apply_apply]
  exact h

end tabulate

/-! ## The full honest computation -/

section full

/-- The derivation `P ‖ A_rnd(l, e) ‖ S ‖ M` of a label's randomizer base. -/
def rbIn (lab : RLabel) (P : PublicParameter) (S : MasterSeed) : HashInput :=
  thInput P (tweakFields 7 0 (layerHi lab.layer 0) lab.key) (littleEndianBytes 32 S ++ lab.msg)

/-- The computation of a hidden value from the parameter `P`, the scheme seed `S` and the chain
starts' hashes `Cs`: a position's by `posM`, a label's randomizer base by its derivation. -/
def fullVal (P : PublicParameter) (S : MasterSeed) (Cs : CsIdx → HashOutput) :
    HPos → OracleComp HashSpec Digest
  | .inl q => posM q P Cs
  | .inr lab => hashQ (rbIn lab P S) >>= fun o ↦ pure (truncateHash o)

theorem fullVal_inl (P : PublicParameter) (S : MasterSeed) (Cs : CsIdx → HashOutput) (q : ValPos) :
    fullVal P S Cs (.inl q) = posM q P Cs :=
  rfl

theorem fullVal_inr (P : PublicParameter) (S : MasterSeed) (Cs : CsIdx → HashOutput)
    (lab : RLabel) :
    fullVal P S Cs (.inr lab) = hashQ (rbIn lab P S) >>= fun o ↦ pure (truncateHash o) :=
  rfl

/-- The chain starts' hashes, then every hidden value, from the scheme seed `S` and the parameter
`P`. -/
noncomputable def fullFrom (S : MasterSeed) (P : PublicParameter) :
    OracleComp HashSpec (PublicParameter × (HPos → Digest)) :=
  tabulate (fun j : CsIdx ↦ hashQ (csInput P S j)) >>= fun Cs ↦
    tabulate (fullVal P S Cs) >>= fun v ↦ pure (P, v)

/-- **The full honest computation** from the master seed `S₀`: the scheme seed, the parameter, the
chain starts' hashes, and every hidden value (`HPos`). -/
noncomputable def fullComp (S0 : MasterSeed) :
    OracleComp HashSpec (PublicParameter × (HPos → Digest)) :=
  hashQ (seedTag ++ littleEndianBytes 32 S0) >>= fun S ↦
    hashQ (paramInput S) >>= fun o ↦ fullFrom S (truncateHash o)

/-- **Runtime 1's table**: the cells the full honest computation reads, with their values. -/
noncomputable def fullHw (L : HonestTable) : Hw X Z :=
  readsHw (honestEval L.keys L.perm (fullComp L.masterSeed)).2

variable (L : HonestTable)

theorem hash_seedIn_eq :
    spongeOut (spongePerm L.keys L.perm) (seedTag ++ littleEndianBytes 32 L.masterSeed) = L.seed :=
  rfl

theorem truncateHash_paramInput_eq :
    truncateHash (spongeOut (spongePerm L.keys L.perm) (paramInput L.seed)) = L.param :=
  rfl

theorem eval_csTab :
    evalWithAnswerFn (spongeOut (spongePerm L.keys L.perm))
      (tabulate fun j : CsIdx ↦ hashQ (csInput L.param L.seed j)) = csHash L := by
  rw [eval_tabulate]
  rfl

/-- The full computation's queries include those of `fullFrom` at the table's seed and parameter. -/
theorem mem_queries_fullComp {q : HashInput}
    (h : q ∈ queries (spongeOut (spongePerm L.keys L.perm)) (fullFrom L.seed L.param)) :
    q ∈ queries (spongeOut (spongePerm L.keys L.perm)) (fullComp L.masterSeed) := by
  unfold fullComp
  refine mem_queries_bind_right _ _ _ (mem_queries_bind_right _ _ _ ?_)
  rw [eval_hashQ, eval_hashQ, hash_seedIn_eq, truncateHash_paramInput_eq]
  exact h

/-- **The full computation returns the table's parameter and hidden values.** -/
theorem fst_honestEval_fullComp :
    (honestEval L.keys L.perm (fullComp L.masterSeed)).1 = (L.param, valueAt L) := by
  rw [fst_honestEval, fullComp, evalWithAnswerFn_bind, eval_hashQ, evalWithAnswerFn_bind,
    eval_hashQ, hash_seedIn_eq, truncateHash_paramInput_eq, fullFrom, evalWithAnswerFn_bind,
    eval_csTab, evalWithAnswerFn_bind, eval_tabulate, evalWithAnswerFn_pure]
  refine Prod.ext rfl (funext fun p ↦ ?_)
  rcases p with (⟨l, e, i, j⟩ | ⟨l, level, index⟩) | lab
  · exact eval_chainM L l e i j.val
  · exact eval_treeM L l level.val index.val
  · show evalWithAnswerFn (spongeOut (spongePerm L.keys L.perm))
        (fullVal L.param L.seed (csHash L) (.inr lab)) = valueAt L (.inr lab)
    rw [fullVal_inr, evalWithAnswerFn_bind]
    rfl

/-- **Every in-table slot's honest input is hashed by the full computation.** -/
theorem slotInput_mem_fullComp {s : Slot} (hs : InTable s) :
    slotInput (pubOf L) s (valuePos L) ∈
      queries (spongeOut (spongePerm L.keys L.perm)) (fullComp L.masterSeed) := by
  refine mem_queries_fullComp L ?_
  unfold fullFrom
  refine mem_queries_bind_right _ _ _ ?_
  rw [eval_csTab]
  refine mem_queries_bind_left _ _ _ (mem_queries_tabulate _ _ (Sum.inl (slotOutPos s)) ?_)
  rw [fullVal_inl]
  exact slotInput_mem_queries L hs

theorem cellK_mem_inputReads (s : Slot) (v : ValPos → Digest) {j : ℕ}
    (hj : j < nBlocks (pubOf L) s) :
    ∃ a, SpongeRead.k (srcCellK (pubOf L) s v j) a ∈
      inputReads L.keys L.perm (slotInput (pubOf L) s v) := by
  have hj' : j < (blocks (slotInput (pubOf L) s v)).length := by
    rwa [length_blocks_slotInput]
  exact ⟨_, roundReads_subset_spongeReads L.perm L.keys.1 L.keys.2.1 L.keys.2.2
    (blocks (slotInput (pubOf L) s v)) hj' _ List.mem_cons_self⟩

theorem cellK'_mem_inputReads (s : Slot) (v : ValPos → Digest) {j : ℕ}
    (hj : j < nBlocks (pubOf L) s) :
    ∃ a, SpongeRead.k' (srcCellK' (pubOf L) s v j) a ∈
      inputReads L.keys L.perm (slotInput (pubOf L) s v) := by
  have hj' : j < (blocks (slotInput (pubOf L) s v)).length := by
    rwa [length_blocks_slotInput]
  exact ⟨_, roundReads_subset_spongeReads L.perm L.keys.1 L.keys.2.1 L.keys.2.2
    (blocks (slotInput (pubOf L) s v)) hj' _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

end full

/-! ## The template's table lies in the full table -/

section hwle

theorem readsHw_fst_of_mem {R : List (SpongeRead X Z)} {t : SpongeKeys X Z}
    (hR : ∀ e ∈ R, e.AnsweredBy t) {z : Z} {a : X} (he : SpongeRead.h z a ∈ R) :
    (readsHw R).1 z = some (t.1 z) := by
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
    (List.findSome?_isSome_iff.mpr ⟨_, he, by simp [SpongeRead.atH]⟩ :
      (R.findSome? (SpongeRead.atH z)).isSome)
  obtain ⟨e', he', he'a⟩ := List.exists_of_findSome?_eq_some ha'
  cases e' with
  | h z' b =>
    simp only [SpongeRead.atH, Option.ite_none_right_eq_some, Option.some.injEq] at he'a
    obtain ⟨rfl, rfl⟩ := he'a
    exact ha'.trans (congrArg some (hR _ he').symm)
  | k _ _ => simp [SpongeRead.atH] at he'a
  | k' _ _ => simp [SpongeRead.atH] at he'a

theorem readsHw_snd_fst_of_mem {R : List (SpongeRead X Z)} {t : SpongeKeys X Z}
    (hR : ∀ e ∈ R, e.AnsweredBy t) {x : X} {a : Z} (he : SpongeRead.k x a ∈ R) :
    (readsHw R).2.1 x = some (t.2.1 x) := by
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
    (List.findSome?_isSome_iff.mpr ⟨_, he, by simp [SpongeRead.atK]⟩ :
      (R.findSome? (SpongeRead.atK x)).isSome)
  obtain ⟨e', he', he'a⟩ := List.exists_of_findSome?_eq_some ha'
  cases e' with
  | k x' b =>
    simp only [SpongeRead.atK, Option.ite_none_right_eq_some, Option.some.injEq] at he'a
    obtain ⟨rfl, rfl⟩ := he'a
    exact ha'.trans (congrArg some (hR _ he').symm)
  | h _ _ => simp [SpongeRead.atK] at he'a
  | k' _ _ => simp [SpongeRead.atK] at he'a

theorem readsHw_snd_snd_of_mem {R : List (SpongeRead X Z)} {t : SpongeKeys X Z}
    (hR : ∀ e ∈ R, e.AnsweredBy t) {x : X} {a : Z} (he : SpongeRead.k' x a ∈ R) :
    (readsHw R).2.2 x = some (t.2.2 x) := by
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp
    (List.findSome?_isSome_iff.mpr ⟨_, he, by simp [SpongeRead.atK']⟩ :
      (R.findSome? (SpongeRead.atK' x)).isSome)
  obtain ⟨e', he', he'a⟩ := List.exists_of_findSome?_eq_some ha'
  cases e' with
  | k' x' b =>
    simp only [SpongeRead.atK', Option.ite_none_right_eq_some, Option.some.injEq] at he'a
    obtain ⟨rfl, rfl⟩ := he'a
    exact ha'.trans (congrArg some (hR _ he').symm)
  | h _ _ => simp [SpongeRead.atK'] at he'a
  | k _ _ => simp [SpongeRead.atK'] at he'a

end hwle

section tableLe

variable (L : HonestTable)

theorem mem_reads_fullComp {e : SpongeRead X Z} {s : Slot} (hs : InTable s)
    (he : e ∈ inputReads L.keys L.perm (slotInput (pubOf L) s (valuePos L))) :
    e ∈ (honestEval L.keys L.perm (fullComp L.masterSeed)).2 := by
  rw [snd_honestEval]
  exact List.mem_flatMap.mpr ⟨_, slotInput_mem_fullComp L hs, he⟩

/-- **The template's table lies in the full table**: every cell the template game programs at `L`
is read by the full computation, with its value in `L.keys`. -/
theorem tableLe_fullHw : HwLe (tableHw L) (fullHw L) := by
  have hR := honestEval_answeredBy L.perm L.keys (fullComp L.masterSeed)
  refine ⟨fun z ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · by_cases h : ∃ a, HwProg.programH z a ∈ progSet L
    · right
      obtain ⟨a, ha⟩ := h
      rw [tableHw_fst ha]
      obtain ⟨s, hs, j, hj, hz⟩ := mem_pathH (L := L) ⟨a, ha⟩
      obtain ⟨b, hb⟩ := mem_hCells.mp (cellH_mem_hCells_inputReads L s (valuePos L) hj)
      rw [hz] at hb
      exact (readsHw_fst_of_mem hR (mem_reads_fullComp L hs hb)).symm
    · left
      simp only [tableHw, h, ↓reduceIte]
  · by_cases h : ∃ a, HwProg.programK x a ∈ progSet L
    · right
      obtain ⟨a, ha⟩ := h
      rw [tableHw_snd_fst ha]
      obtain ⟨s, hs, j, hj, hx⟩ := mem_pathK (L := L) ⟨a, ha⟩
      obtain ⟨b, hb⟩ := cellK_mem_inputReads L s (valuePos L) hj
      rw [hx] at hb
      exact (readsHw_snd_fst_of_mem hR (mem_reads_fullComp L hs hb)).symm
    · left
      simp only [tableHw, h, ↓reduceIte]
  · by_cases h : ∃ a, HwProg.programK' x a ∈ progSet L
    · right
      obtain ⟨a, ha⟩ := h
      rw [tableHw_snd_snd ha]
      obtain ⟨s, hs, j, hj, hx⟩ := mem_pathK' (L := L) ⟨a, ha⟩
      obtain ⟨b, hb⟩ := cellK'_mem_inputReads L s (valuePos L) hj
      rw [hx] at hb
      exact (readsHw_snd_snd_of_mem hR (mem_reads_fullComp L hs hb)).symm
    · left
      simp only [tableHw, h, ↓reduceIte]

end tableLe

/-! ## G0 is runtime 1 with the full table hardwired -/

section reads

/-- An average over three coordinates of a type `Θ ≃ S × P × K` is the uniform average; the
summands are the values at `E` of measures `m`, the inner weights and index sets named (`w`, `u`),
so that the sums match `smul_sum_sum_smul_apply` syntactically. -/
theorem uavg_eq_avg3 {Θ S P K γ : Type*} [Fintype Θ] [Fintype S] [Fintype P] [Fintype K]
    [MeasurableSpace γ] (e : Θ ≃ S × P × K) (F : Θ → ℝ≥0∞) (u : P → Finset K)
    (w : P → K → ℝ≥0∞) (m : S → P → K → Measure γ) (E : Set γ) (hu : ∀ p, u p = Finset.univ)
    (hw : ∀ p k, w p k = (Fintype.card K : ℝ≥0∞)⁻¹)
    (hm : ∀ s p k, m s p k E = F (e.symm (s, p, k))) :
    uavg F = (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ s, ((Fintype.card P : ℝ≥0∞)⁻¹ *
      ∑ p, ∑ k ∈ u p, w p k * m s p k E) := by
  have hc : (Fintype.card Θ : ℝ≥0∞)⁻¹ = (Fintype.card S : ℝ≥0∞)⁻¹ *
      ((Fintype.card P : ℝ≥0∞)⁻¹ * (Fintype.card K : ℝ≥0∞)⁻¹) := by
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.natCast_ne_top _))) (Or.inl (ENNReal.natCast_ne_top _)),
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [hu, hw, hm]
  rw [uavg, hc, ← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- The honest table as master seed, permutation and keys. -/
def fullSplit : HonestTable ≃ MasterSeed × Equiv.Perm (X × Z) × SpongeKeys X Z where
  toFun L := (L.masterSeed, L.perm, L.keys)
  invFun x := ⟨x.2.2, x.2.1, x.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The randomizer search does not read the public keys. -/
theorem grindR_keys (M : Type) [Fintype M] [DecidableEq M] (upd : TrialUpd M)
    (P : PublicParameter) (π : Equiv.Perm (X × Z)) (t t' : SpongeKeys X Z) (B : QReg) (l : Layer)
    (e : KeyIndex) (message : HashInput) (base : Randomizer) :
    ∀ n trial, grindR M upd ⟨P, π, t⟩ B l e message base n trial =
      grindR M upd ⟨P, π, t'⟩ B l e message base n trial
  | 0, _ => rfl
  | n + 1, trial => by
    rw [grindR, grindR]
    simp only [grindR_keys M upd P π t t' B l e message base n]

/-- `gameReadsT` does not read the public keys. -/
theorem gameReadsT_keys (M : Type) [Fintype M] [DecidableEq M] (P : PublicParameter)
    (π : Equiv.Perm (X × Z)) (t t' : SpongeKeys X Z) (v : HPos → Digest)
    (A : Adversary (X × Z)) :
    gameReadsT M ⟨P, π, t⟩ v A = gameReadsT M ⟨P, π, t'⟩ v A := by
  have h : signLayerR M ⟨P, π, t⟩ v = signLayerR M ⟨P, π, t'⟩ v := by
    funext B lab
    rw [signLayerR, signLayerR, grindR_keys]
  unfold gameReadsT signAtR
  simp only [h, noKey, pkOf]

/-- Fixed keys for the public data of the grind-only game (it does not read them). -/
def keys₀ : SpongeKeys X Z :=
  (fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0)

/-- **The grind-only game from the full computation's result** and `π`. -/
noncomputable def yT (A : Adversary (X × Z)) (π : Equiv.Perm (X × Z))
    (b : (PublicParameter × (HPos → Digest)) × List (SpongeRead X Z)) :
    QComp (hwReadSpec X Z Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  gameReadsT Unit ⟨b.1.1, π, keys₀⟩ b.1.2 A

theorem yT_honestEval (A : Adversary (X × Z)) (L : HonestTable) :
    yT A L.perm (honestEval L.keys L.perm (fullComp L.masterSeed)) =
      gameReadsT Unit (pubOf L) (valueAt L) A := by
  rw [yT, fst_honestEval_fullComp]
  exact gameReadsT_keys Unit L.param L.perm keys₀ L.keys (valueAt L) A

/-- The law of runtime 1 with `fullHw L` hardwired, running the grind-only game at `L`. -/
noncomputable def fullLaw (A : Adversary (X × Z)) (L : HonestTable) : Measure Bool :=
  (spongeHardwiredReadRuntime X Z (fullHw L) ()).evalDistMap .instruments
    (gameReadsT Unit (pubOf L) (valueAt L) A) (SubState.basis ()) fun p ↦ p.2.2

/-- The win probability of runtime 1 with `fullHw L` hardwired, running the grind-only game. -/
noncomputable def p1F (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  fullLaw A L {true}

theorem readsLaw_eq (A : Adversary (X × Z)) (L : HonestTable) :
    (spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()).evalDistMap .instruments
        (gameReads Unit L.perm A (honestEval L.keys L.perm
          (schemeWithHashFromSeed.keygen L.masterSeed))) (SubState.basis ()) (fun p ↦ p.2.2) =
      (spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()).evalDistMap .instruments
        (yT A L.perm (honestEval L.keys L.perm (fullComp L.masterSeed))) (SubState.basis ())
        (fun p ↦ p.2.2) := by
  rw [yT_honestEval]
  exact evalDistMap_gameReads_eq_gameReadsT L () A _ _

theorem hwLaw_eq (A : Adversary (X × Z)) (L : HonestTable) :
    (spongeHardwiredReadRuntime X Z (readsHw (honestEval L.keys L.perm
        (fullComp L.masterSeed)).2) ()).evalDistMap .instruments
        (yT A L.perm (honestEval L.keys L.perm (fullComp L.masterSeed))) (SubState.basis ())
        (fun p ↦ p.2.2) = fullLaw A L := by
  rw [yT_honestEval, fullLaw, fullHw]

/-- **G2 with the grind-only signer is runtime 1 with the full table**, at a master seed and `π`:
the average over `t` of the read runtime on `gameReads` after honest key generation. -/
theorem sum_reads_eq_fullLaw (A : Adversary (X × Z)) (S0 : MasterSeed) (π : Equiv.Perm (X × Z)) :
    ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ •
        (spongeFnReadRuntime X Z t (hwEmpty X Z) ()).evalDistMap .instruments
          (gameReads Unit π A (honestEval t π (schemeWithHashFromSeed.keygen S0)))
          (SubState.basis ()) (fun p ↦ p.2.2) =
      ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ • fullLaw A ⟨t, π, S0⟩ :=
  calc _ = ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ •
        (spongeFnReadRuntime X Z t (hwEmpty X Z) ()).evalDistMap .instruments
          (yT A π (honestEval t π (fullComp S0))) (SubState.basis ()) (fun p ↦ p.2.2) :=
        Finset.sum_congr rfl fun t _ ↦ congrArg (HSMul.hSMul _) (readsLaw_eq A ⟨t, π, S0⟩)
    _ = ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ •
        (spongeHardwiredReadRuntime X Z (readsHw (honestEval t π (fullComp S0)).2) ()).evalDistMap
          .instruments (yT A π (honestEval t π (fullComp S0))) (SubState.basis ())
          (fun p ↦ p.2.2) :=
        spongeEvalDistMap_eq_avg_runtime1 π (fullComp S0) () .instruments (yT A π)
          (SubState.basis ()) fun p ↦ p.2.2
    _ = _ := Finset.sum_congr rfl fun t _ ↦ congrArg (HSMul.hSMul _) (hwLaw_eq A ⟨t, π, S0⟩)

/-- The keys as an index set per permutation (named, for syntactic matching of sums). -/
def univK (_ : Equiv.Perm (X × Z)) : Finset (SpongeKeys X Z) :=
  Finset.univ

/-- The uniform weight of the keys (named, for syntactic matching of sums). -/
noncomputable def keysW (_ : Equiv.Perm (X × Z)) (_ : SpongeKeys X Z) : ℝ≥0∞ :=
  (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹

/-- `fullLaw` at the table of a master seed, a permutation and keys. -/
noncomputable def fullLawPT (A : Adversary (X × Z)) (S0 : MasterSeed) (π : Equiv.Perm (X × Z))
    (t : SpongeKeys X Z) : Measure Bool :=
  fullLaw A ⟨t, π, S0⟩

/-- The win probability at a master seed, as the average over `π` and `t` of `fullLawPT`. -/
theorem prob_game_eq_avg_fullLawPT (A : Adversary (X × Z)) (S0 : MasterSeed) :
    qrpmEvalDistMap .instruments (game keccakStateEquiv S0 A) (SubState.basis ())
        (fun _ p ↦ p.2.2) {true} =
      (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ * ∑ π ∈ Finset.univ,
        ∑ t ∈ univK π, keysW π t * fullLawPT A S0 π t {true} := by
  have hμ : qrpmEvalDistMap .instruments (game keccakStateEquiv S0 A) (SubState.basis ())
        (fun _ p ↦ p.2.2) =
      (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ • ∑ π ∈ Finset.univ,
        ∑ t ∈ univK π, keysW π t • fullLawPT A S0 π t :=
    (qrpm_game_eq_reads (M := Unit) () S0 A (SubState.basis ()) fun p ↦ p.2.2).trans
      (congrArg (HSMul.hSMul _) (Finset.sum_congr rfl fun π _ ↦
        (sum_reads_eq_fullLaw A S0 π).trans (Finset.sum_congr (rfl : Finset.univ = univK π)
          fun t _ ↦ congr_arg₂ HSMul.hSMul (rfl : _ = keysW π t)
            (rfl : fullLaw A ⟨t, π, S0⟩ = fullLawPT A S0 π t))))
  exact (congrArg (fun μ : Measure Bool ↦ μ {true}) hμ).trans
    (smul_sum_sum_smul_apply _ Finset.univ univK keysW (fullLawPT A S0) {true})

/-- **G0 is the table average of runtime 1 with the full table hardwired, running the grind-only
game** (Security's `readsT` as an equality, with `Lt := fullHw`). -/
theorem winProb_eq_uavg_full (A : Adversary (X × Z)) :
    winProb keccakStateEquiv A = uavg (fun L ↦
      (spongeHardwiredReadRuntime X Z (fullHw L) ()).evalDistMap .instruments
        (gameReadsT Unit (pubOf L) (valueAt L) A) (SubState.basis ()) (fun p ↦ p.2.2) {true}) :=
  calc winProb keccakStateEquiv A
      = (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ * ∑ S0 : MasterSeed,
          qrpmEvalDistMap .instruments (game keccakStateEquiv S0 A) (SubState.basis ())
            (fun _ p ↦ p.2.2) {true} := by
        rw [winProb, card_masterSeed, Nat.cast_pow, Nat.cast_ofNat]
    _ = (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ * ∑ S0 : MasterSeed,
          ((Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ * ∑ π ∈ Finset.univ,
            ∑ t ∈ univK π, keysW π t * fullLawPT A S0 π t {true}) :=
        congrArg (HMul.hMul _) (Finset.sum_congr rfl fun S0 _ ↦ prob_game_eq_avg_fullLawPT A S0)
    _ = uavg (p1F A) :=
        (uavg_eq_avg3 fullSplit (p1F A) univK keysW (fullLawPT A) {true} (fun _ ↦ rfl)
          (fun _ _ ↦ rfl) fun s p k ↦ congrArg (fun μ : Measure Bool ↦ μ {true})
            (rfl : fullLawPT A s p k = fullLaw A (fullSplit.symm (s, p, k)))).symm

end reads

end Quantum.Xmss.Assembly

end
