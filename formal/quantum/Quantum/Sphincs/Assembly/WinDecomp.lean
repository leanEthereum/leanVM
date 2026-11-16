module

public import Quantum.Sphincs.Assembly.EndReads
public import Quantum.Xmss.Assembly.TrialHit

@[expose] public section

/-!
# The winning runs of leanSPHINCS's event-side game, off the trial-hit and conflict events

`endReads` for the canonical game at `strPol` and template data `(pub, v)` (contract C4):
the win weight of `gameR strPol A pub v` in `runtimeR m₀` is at most the event weight of
`Bad (evData pub v) progCap` at the end of the game, the read error of the verification's
`verifyBlocks` reads of each function, and the masses at the end of the game of the two
exceptions of PrefixFacts' `prefixWinFactsOff`, each a named term: `trialHitMass` (`TrialHit pub v`)
and `hConflictMass` (`HConflict pub v`) (`endReads_wGame_trialHit`).

* **Masses of decompressed events** (`decProjS`, `eventMassDecS`): the weight at the end of the
  game of an event of the decompressed register, through its projector in the compressed basis.
  The mass of a union is at most the sum (`eventMassDecS_union_le`, from the diagonal form of the
  conjugated projector, leanXMSS's `trace_conj_kron_proj`).
* **The prefix invariant off an event** (`PreWinOff`): every winning branch of the prefix is, in
  the decompressed basis, in the event or has PrefixFacts' `PreFactsS`; on good data it holds off
  `TrialHit pub v ∪ HConflict pub v` (`preWinOff_of_good`, from `prefixWinFactsOff`).
* **The winning runs** (local notation `winSig`, `dec_winSig`, `trace_winSig_le`): one run per
  prefix outcome and run of the verification's reads, when the winning condition holds (`runSig`,
  written out as in EndReads); recorded in the decompressed basis (no empty cell, the reads the
  honest verification's against the register's functions) and,
  off the event, with Classify's `WinFacts` (`winFacts_of_preFacts` with `dbGrade W ≤ progCap`,
  `grade_branch₂_sph`), hence in `Bad` when the view holds the reads (`mem_bad_of_agrees`).
* **The bound** (`endReads_wGame_off`, then `endReads_wGame_trialHit` on good data).
-/

open Matrix IPFunctor OracleSpec
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Message)
open Quantum.Xmss (X Z extProgCharge)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT initU NoBot NoBotDb regFns
  runSig runSig_of_not runSig_posSemidef conj_runSig_of ofReal_trace_conj_runSig
  trace_conj_branch_true_le_eventWeight ofReal_trace_branch_le_one evalDistMap_winBit
  noBot_branch₂ querySupportedOn_inter querySupportedOn_conj_compressReg suppTo_readsProgram
  trace_le_of_off map_toSpongeRead_ofSpongeRead readLiftQ heldBy_hwView_of_noBot answeredBy_fill
  ofReal_le_add_mul_add readError_nonneg isChargeBound_of_bind₂ trace_conj_kron_proj
  initU_posSemidef)

namespace Quantum.Sphincs.Assembly

/-! ## Masses of decompressed events -/

section masses

/-- **The weight of a union of two diagonal events** in the basis conjugated by `C` is at most the
sum of their weights. -/
theorem re_trace_conj_kron_proj_or_le {I H : Type} [Fintype I] [DecidableEq I] [Fintype H]
    [DecidableEq H] (C : Matrix H H ℂ) (hC : C * C = 1) (hCh : Cᴴ = C) (f₁ f₂ : H → Prop)
    {d₁ : DecidablePred f₁} {d₂ : DecidablePred f₂} {d : DecidablePred fun s ↦ f₁ s ∨ f₂ s}
    {σ : Matrix (I × H) (I × H) ℂ} (hσ : σ.PosSemidef) :
    (MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ
        (C * diagonal (fun s ↦ if f₁ s ∨ f₂ s then (1 : ℂ) else 0) * C)) σ).trace.re ≤
      (MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ
          (C * diagonal (fun s ↦ if f₁ s then (1 : ℂ) else 0) * C)) σ).trace.re +
        (MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ
          (C * diagonal (fun s ↦ if f₂ s then (1 : ℂ) else 0) * C)) σ).trace.re := by
  have hg : ∀ (f : H → Prop) (d : DecidablePred f) (s : H),
      (@ite ℂ (f s) (d s) 1 0) * (@ite ℂ (f s) (d s) 1 0) = @ite ℂ (f s) (d s) 1 0 := by
    intro f d s
    split_ifs <;> simp
  have hgs : ∀ (f : H → Prop) (d : DecidablePred f) (s : H),
      star (@ite ℂ (f s) (d s) 1 0) = @ite ℂ (f s) (d s) 1 0 := by
    intro f d s
    split_ifs <;> simp
  rw [trace_conj_kron_proj C hC hCh _ (hg _ d) (hgs _ d),
    trace_conj_kron_proj C hC hCh _ (hg f₁ d₁) (hgs f₁ d₁),
    trace_conj_kron_proj C hC hCh _ (hg f₂ d₂) (hgs f₂ d₂), Complex.re_sum, Complex.re_sum,
    Complex.re_sum, ← Finset.sum_add_distrib]
  have hP : (MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ C) σ).PosSemidef :=
    hσ.mul_mul_conjTranspose_same _
  refine Finset.sum_le_sum fun m _ ↦ ?_
  have hd : 0 ≤ (MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ C) σ m m).re :=
    (Complex.nonneg_iff.mp hP.diag_nonneg).1
  generalize MatrixMap.conj ((1 : Matrix I I ℂ) ⊗ₖ C) σ m m = y at hd ⊢
  by_cases h1 : f₁ m.2 <;> by_cases h2 : f₂ m.2 <;> simp [h1, h2]
  linarith

set_option synthInstance.maxSize 2000 in
/-- The projector on an event of the decompressed register, in the compressed basis. -/
noncomputable def decProjS (E : Set (HwReg X Z (Finset HPos × Selections)))
    [DecidablePred (· ∈ E)] :
    Matrix (HwReg X Z (Finset HPos × Selections)) (HwReg X Z (Finset HPos × Selections)) ℂ :=
  compressReg X Z (Finset HPos × Selections) * diagonal (fun s ↦ if s ∈ E then 1 else 0) *
    compressReg X Z (Finset HPos × Selections)

set_option synthInstance.maxSize 2000 in
/-- **The mass of a decompressed event** at the end of the canonical game at `strPol`. -/
noncomputable def eventMassDecS (m₀ : Finset HPos × Selections) (A : SAdversary) (pub : Pub)
    (v : (s : HPos) → XD s) (E : Set (HwReg X Z (Finset HPos × Selections)))
    [DecidablePred (· ∈ E)] : ℝ≥0∞ :=
  (runtimeR m₀).eventWeight .instruments (decProjS E) (gameR strPol A pub v)
    ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)

set_option synthInstance.maxSize 2000 in
/-- **The trial-hit mass**: the weight, at the end of the game, of the decompressed registers where
some trial of a key on the value it signs reads a cell the template may program
(`TrialHit pub v`). -/
noncomputable def trialHitMass (m₀ : Finset HPos × Selections) (A : SAdversary) (pub : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  @eventMassDecS m₀ A pub v (TrialHit pub v) (Classical.decPred _)

set_option synthInstance.maxSize 2000 in
/-- **The conflict mass**: the weight, at the end of the game, of the decompressed registers where
two distinct held `H_msg` calls share their `h`-cell (`HConflict pub v`). -/
noncomputable def hConflictMass (m₀ : Finset HPos × Selections) (A : SAdversary) (pub : Pub)
    (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  @eventMassDecS m₀ A pub v (HConflict pub v) (Classical.decPred _)

set_option synthInstance.maxSize 2000 in
/-- **The mass of a union is at most the sum of the masses.** -/
theorem eventMassDecS_union_le (m₀ : Finset HPos × Selections) (A : SAdversary) (pub : Pub)
    (v : (s : HPos) → XD s) (E₁ E₂ : Set (HwReg X Z (Finset HPos × Selections)))
    [d₁ : DecidablePred (· ∈ E₁)] [d₂ : DecidablePred (· ∈ E₂)] [d : DecidablePred (· ∈ E₁ ∪ E₂)] :
    eventMassDecS m₀ A pub v (E₁ ∪ E₂) ≤
      eventMassDecS m₀ A pub v E₁ + eventMassDecS m₀ A pub v E₂ := by
  unfold eventMassDecS QuantumRuntime.eventWeight decProjS
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun p ↦ (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  exact re_trace_conj_kron_proj_or_le (compressReg X Z (Finset HPos × Selections))
    compressReg_mul_self conjTranspose_compressReg (· ∈ E₁) (· ∈ E₂) (d := d)
    (((runtimeR m₀).run .instruments (gameR strPol A pub v)).posSemidef_branch_apply p
      (initU_posSemidef (X := X) (Z := Z) m₀))

set_option synthInstance.maxSize 2000 in
/-- **The mass of the union of the two exceptions** is at most the trial-hit mass plus the conflict
mass. -/
theorem eventMassDecS_exc_le (m₀ : Finset HPos × Selections) (A : SAdversary) (pub : Pub)
    (v : (s : HPos) → XD s) :
    @eventMassDecS m₀ A pub v (TrialHit pub v ∪ HConflict pub v) (Classical.decPred _) ≤
      trialHitMass m₀ A pub v + hConflictMass m₀ A pub v :=
  @eventMassDecS_union_le m₀ A pub v _ _ (Classical.decPred _) (Classical.decPred _)
    (Classical.decPred _)

end masses

/-! ## The prefix invariant off an event -/

section preWinOff

set_option synthInstance.maxSize 2000 in
/-- **The prefix invariant off a decompressed event `E`**: on every winning branch of the prefix
at `strPol`, in the decompressed basis, the register is in `E` or has the prefix facts. -/
def PreWinOff (m₀ : Finset HPos × Selections) (A : SAdversary) (pub : Pub)
    (v : (s : HPos) → XD s) (E : Set (HwReg X Z (Finset HPos × Selections))) : Prop :=
  ∀ pre, winCondS pre = true →
    QuerySupportedOn (fun p : Unit × HwReg X Z (Finset HPos × Selections) ↦ p.2)
      {s | s ∉ E → PreFactsS pub v pre s.2}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset HPos × Selections))
        (((runtimeR m₀).run₂ .instruments (prefixR strPol A pub v)).branch pre (initU m₀)))

set_option synthInstance.maxSize 2000 in
/-- **On good data, the prefix invariant holds off the trial-hit and conflict events**
(`prefixWinFactsOff`). -/
theorem preWinOff_of_good {m₀ : Finset HPos × Selections} {pub : Pub} {v : (s : HPos) → XD s}
    (hpd : PathsDisjoint pub.xw pub.keys.1 (valsOf v)) (hsepK : HmsgSep pub v)
    (hsepH : HmsgHSep pub v) (hm₀l : AsgFree m₀.1) (hm₀ : m₀.2 = fun _ ↦ none) (A : SAdversary) :
    PreWinOff m₀ A pub v (TrialHit pub v ∪ HConflict pub v) := fun pre hw ↦
  (prefixWinFactsOff hpd hsepK hsepH hm₀l hm₀ A pre hw).mono fun _ hs hE ↦
    hs (fun h ↦ hE (Or.inl h)) fun h ↦ hE (Or.inr h)

end preWinOff

/-! ## The decomposition of the winning runs -/

/- The verification's read program at `(pub, v)` on `pre`, written out (EndReads: never wrapped
in a definition). -/
local notation "verRd " pub:max v:max pre:max =>
  realizeT v (readLiftQ goodAll (readsProgram Selections (Pub.perm pub) (QReg.of Unit)
    (schemeWithHash.verify (Prod.fst pre) (Prod.fst (Prod.snd pre)))))

/- **The runs of the winning outcomes**: a winning prefix outcome `i.1` followed by a run `i.2` of
the verification's reads that accepts (`runSig`), written out for the same reason. -/
local notation "winSig " m₀:max A:max pub:max v:max i:max =>
  runSig m₀ (prefixR strPol A pub v) (fun pre ↦ verRd pub v pre)
    (fun pre a ↦ winCondS pre && Prod.fst a) i

section decomp

variable {m₀ : Finset HPos × Selections} {A : SAdversary} {pub : Pub} {v : (s : HPos) → XD s}

set_option synthInstance.maxSize 2000 in
/-- The program-call bound of the game holds for its prefix. -/
theorem progCalls_prefix_of_game
    (hprog : IFreeM.IsChargeBound (gameR strPol A pub v)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap) :
    IFreeM.IsChargeBound (prefixR strPol A pub v)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap := by
  rw [gameR_eq] at hprog
  exact isChargeBound_of_bind₂ hprog

set_option synthInstance.maxSize 2000 in
/-- **The prefix's branch in the decompressed basis**: no empty cell, at most `progCap`
hardwired cells, and, off `E`, the prefix facts. -/
theorem dec_winPre {E : Set (HwReg X Z (Finset HPos × Selections))}
    (hprog : IFreeM.IsChargeBound (gameR strPol A pub v)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap)
    (hpre : PreWinOff m₀ A pub v E)
    (pre : PublicKey × (Forgery × SignLog Message (Option Signature)))
    (hw : winCondS pre = true) :
    QuerySupportedOn (fun p : Unit × HwReg X Z (Finset HPos × Selections) ↦ p.2)
      {s | NoBot s ∧ (dbGrade s.2.1 ≤ progCap ∧ (s ∉ E → PreFactsS pub v pre s.2))}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset HPos × Selections))
        (((runtimeR m₀).run₂ .instruments (prefixR strPol A pub v)).branch pre (initU m₀))) :=
  querySupportedOn_inter (noBot_branch₂ m₀ (prefixR strPol A pub v) pre)
    (querySupportedOn_inter (querySupportedOn_conj_compressReg (P := fun b ↦ dbGrade b.1 ≤ progCap)
      (grade_branch₂_sph m₀ (progCalls_prefix_of_game hprog) pre)) (hpre pre hw))

set_option synthInstance.maxSize 2000 in
/-- **A winning run of the verification's reads in the decompressed basis**: the prefix's facts
kept off `E`, and the run's outcome the honest verification against the register's functions. -/
theorem dec_winSig {E : Set (HwReg X Z (Finset HPos × Selections))}
    (hprog : IFreeM.IsChargeBound (gameR strPol A pub v)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap)
    (hpre : PreWinOff m₀ A pub v E)
    (i : (PublicKey × (Forgery × SignLog Message (Option Signature))) ×
      (Bool × List (SpongeRead X Z))) :
    QuerySupportedOn (fun p : Unit × HwReg X Z (Finset HPos × Selections) ↦ p.2)
      {s | (winCondS i.1 && i.2.1) = true ∧
        ((NoBot s ∧ (dbGrade s.2.1 ≤ progCap ∧ (s ∉ E → PreFactsS pub v i.1 s.2))) ∧
          i.2 = honestEval (regFns s) pub.perm (schemeWithHash.verify i.1.1 i.1.2.1))}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset HPos × Selections))
        (winSig m₀ A pub v i)) := by
  by_cases h : (winCondS i.1 && i.2.1) = true
  · rw [conj_runSig_of m₀ (prefixR strPol A pub v) (fun pre ↦ verRd pub v pre)
      (fun pre a ↦ winCondS pre && Prod.fst a) i h]
    have hw : winCondS i.1 = true := ((Bool.and_eq_true _ _).mp h).1
    exact (suppTo_readsProgram (m₀ := m₀) (v := v) (good := goodAll) pub.perm (QReg.of Unit)
      (schemeWithHash.verify i.1.1 i.1.2.1) _ _ (dec_winPre hprog hpre i.1 hw) i.2).mono
        fun _ hs ↦ ⟨h, hs⟩
  · rw [runSig_of_not m₀ (prefixR strPol A pub v) (fun pre ↦ verRd pub v pre)
      (fun pre a ↦ winCondS pre && Prod.fst a) i h, map_zero]
    exact querySupportedOn_zero _ _

set_option synthInstance.maxSize 2000 in
/-- **A winning run off `E`**: its weight is at most its weight in `Bad (evData pub v) progCap`, the
read error of the verification's reads, and its weight in `E` (`trace_le_of_off`). -/
theorem trace_winSig_le {E : Set (HwReg X Z (Finset HPos × Selections))}
    [DecidablePred (· ∈ Bad (S := HPos) (evData pub v) progCap)] [DecidablePred (· ∈ E)]
    (hprog : IFreeM.IsChargeBound (gameR strPol A pub v)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap)
    (hpre : PreWinOff m₀ A pub v E)
    (i : (PublicKey × (Forgery × SignLog Message (Option Signature))) ×
      (Bool × List (SpongeRead X Z))) :
    (winSig m₀ A pub v i).trace.re ≤
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ
        hwProjector (Bad (S := HPos) (evData pub v) progCap)) (winSig m₀ A pub v i)).trace.re +
        readError X Z verifyBlocks verifyBlocks verifyBlocks * (winSig m₀ A pub v i).trace.re +
          (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ decProjS E)
            (winSig m₀ A pub v i)).trace.re := by
  have hrec : QuerySupportedOn (fun y : Unit × HwReg X Z (Finset HPos × Selections) ↦ y.2)
      {s | NoBotDb s.1 ∧ DbReg.Agrees (verLog i) (hwView s.2.1 s.1)}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset HPos × Selections))
        (winSig m₀ A pub v i)) := (dec_winSig hprog hpre i).mono fun s hs ↦ by
    obtain ⟨-, ⟨hnb, -⟩, ha⟩ := hs
    have hc : VerCounts i.2.2 := by
      rw [ha]
      exact verCounts_honest _ _ _ _
    refine ⟨hnb, ?_⟩
    rw [verLog_of_counts hc, agrees_iff_forall_heldBy, map_toSpongeRead_ofSpongeRead]
    intro e he
    rw [ha] at he
    exact heldBy_hwView_of_noBot hnb (honestEval_answeredBy pub.perm _ _ e he)
  have hoff : QuerySupportedOn (fun y : Unit × HwReg X Z (Finset HPos × Selections) ↦ y.2)
      {s | s ∉ E → (∃ S dig, WinFacts (evData pub v) progCap S (rndOf v) dig i.1.2.2 i.1.2.1
        s.2.1 s.2.2) ∧ i.1.1 = (evData pub v).pk ∧
        ∀ U : Dbs X Z, (∀ e ∈ (verLog i).map toSpongeRead, e.HeldBy U) →
          (honestEval U.fill pub.perm (schemeWithHash.verify i.1.1 i.1.2.1)).1 = true ∧
            ∀ e ∈ (honestEval U.fill pub.perm (schemeWithHash.verify i.1.1 i.1.2.1)).2,
              e.HeldBy U}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset HPos × Selections))
        (winSig m₀ A pub v i)) := (dec_winSig hprog hpre i).mono fun s hs hsE ↦ by
    obtain ⟨hw, ⟨-, hgr, hpf⟩, ha⟩ := hs
    have hpf := hpf hsE
    have hc : VerCounts i.2.2 := by
      rw [ha]
      exact verCounts_honest _ _ _ _
    refine ⟨winFacts_of_preFacts hpf hgr, hpf.1, fun U hU ↦ ?_⟩
    rw [verLog_of_counts hc, map_toSpongeRead_ofSpongeRead, ha] at hU
    have hcg : honestEval U.fill pub.perm (schemeWithHash.verify i.1.1 i.1.2.1) =
        honestEval (regFns s) pub.perm (schemeWithHash.verify i.1.1 i.1.2.1) :=
      honestEval_congr pub.perm _ fun e he ↦ answeredBy_fill (hU e he)
    rw [hcg]
    refine ⟨?_, hU⟩
    rw [← ha]
    exact ((Bool.and_eq_true _ _).mp hw).2
  exact trace_le_of_off (Bad (S := HPos) (evData pub v) progCap) E (verLog i)
    (readCount_verLog_le i .h) (readCount_verLog_le i .k) (readCount_verLog_le i .k')
    (runSig_posSemidef m₀ _ _ _ i) hrec
    (fun b ↦ (∃ S dig, WinFacts (evData pub v) progCap S (rndOf v) dig i.1.2.2 i.1.2.1 b.1 b.2) ∧
      i.1.1 = (evData pub v).pk ∧
      ∀ U : Dbs X Z, (∀ e ∈ (verLog i).map toSpongeRead, e.HeldBy U) →
        (honestEval U.fill pub.perm (schemeWithHash.verify i.1.1 i.1.2.1)).1 = true ∧
          ∀ e ∈ (honestEval U.fill pub.perm (schemeWithHash.verify i.1.1 i.1.2.1)).2,
            e.HeldBy U)
    (fun _ _ hf hag ↦ by
      obtain ⟨⟨S, dig, hf⟩, hpk, hver⟩ := hf
      rw [hpk] at hver
      exact mem_bad_of_agrees hf (verLog i) hver hag)
    hoff

end decomp

/-! ## `endReads` off a decompressed event -/

section final

variable {m₀ : Finset HPos × Selections} {A : SAdversary} {pub : Pub} {v : (s : HPos) → XD s}

set_option synthInstance.maxSize 2000 in
/-- **`endReads` for the canonical game off a decompressed event**: on runs with at most `progCap`
program calls and given the prefix invariant off `E` (`PreWinOff`), the win weight of the game at
`strPol` in `runtimeR m₀` is at most the event weight of `Bad (evData pub v) progCap` at the end of
the game, plus the read error of the verification's `verifyBlocks` reads of each function, plus
the mass of `E` at the end of the game. -/
theorem endReads_wGame_off {E : Set (HwReg X Z (Finset HPos × Selections))}
    [DecidablePred (· ∈ Bad (S := HPos) (evData pub v) progCap)] [DecidablePred (· ∈ E)]
    (hprog : IFreeM.IsChargeBound (gameR strPol A pub v)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap)
    (hpre : PreWinOff m₀ A pub v E) :
    (runtimeR m₀).evalDistMap .instruments (gameR strPol A pub v) (SubState.basis ()) winObs
        {true} ≤
      (runtimeR m₀).eventWeight .instruments (hwProjector (Bad (S := HPos) (evData pub v) progCap))
          (gameR strPol A pub v)
          ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) +
        ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks) +
          eventMassDecS m₀ A pub v E := by
  set Q := hwProjector (Bad (S := HPos) (evData pub v) progCap)
  set err := readError X Z verifyBlocks verifyBlocks verifyBlocks
  have herr : 0 ≤ err := readError_nonneg _ _ _
  have hi : ∀ i, ENNReal.ofReal (winSig m₀ A pub v i).trace.re ≤
      ENNReal.ofReal (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ Q)
        (winSig m₀ A pub v i)).trace.re +
        ENNReal.ofReal err * ENNReal.ofReal (winSig m₀ A pub v i).trace.re +
        ENNReal.ofReal (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ decProjS E)
          (winSig m₀ A pub v i)).trace.re := fun i ↦
    ofReal_le_add_mul_add herr (trace_winSig_le hprog hpre i)
  have hwin : (runtimeR m₀).evalDistMap .instruments (gameR strPol A pub v) (SubState.basis ())
      winObs {true} ≤ ∑' i, ENNReal.ofReal (winSig m₀ A pub v i).trace.re := by
    rw [show winObs = Quantum.Xmss.Assembly.winBit from rfl, evalDistMap_winBit,
      gameR_eq_verReads]
    have h := ofReal_trace_conj_runSig m₀ (prefixR strPol A pub v) (fun pre ↦ verRd pub v pre)
      (fun pre a ↦ winCondS pre && a.1) 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    exact h.le
  have hev : ∑' i, ENNReal.ofReal (MatrixMap.conj
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ Q) (winSig m₀ A pub v i)).trace.re ≤
      (runtimeR m₀).eventWeight .instruments Q (gameR strPol A pub v)
        ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
    have h := ofReal_trace_conj_runSig m₀ (prefixR strPol A pub v) (fun pre ↦ verRd pub v pre)
      (fun pre a ↦ winCondS pre && a.1) ((1 : Matrix Unit Unit ℂ) ⊗ₖ Q)
    rw [← gameR_eq_verReads] at h
    exact h.symm.le.trans (trace_conj_branch_true_le_eventWeight m₀ (gameR strPol A pub v) _)
  have hdec : ∑' i, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ decProjS E)
      (winSig m₀ A pub v i)).trace.re ≤ eventMassDecS m₀ A pub v E := by
    have h := ofReal_trace_conj_runSig m₀ (prefixR strPol A pub v) (fun pre ↦ verRd pub v pre)
      (fun pre a ↦ winCondS pre && a.1) ((1 : Matrix Unit Unit ℂ) ⊗ₖ decProjS E)
    rw [← gameR_eq_verReads] at h
    exact h.symm.le.trans (trace_conj_branch_true_le_eventWeight m₀ (gameR strPol A pub v) _)
  have hmass : ∑' i, ENNReal.ofReal (winSig m₀ A pub v i).trace.re ≤ 1 := by
    have h := ofReal_trace_conj_runSig m₀ (prefixR strPol A pub v) (fun pre ↦ verRd pub v pre)
      (fun pre a ↦ winCondS pre && a.1) 1
    simp only [MatrixMap.conj_one, LinearMap.id_apply] at h
    rw [← gameR_eq_verReads] at h
    exact h.symm.le.trans (ofReal_trace_branch_le_one m₀ (gameR strPol A pub v) true)
  calc (runtimeR m₀).evalDistMap .instruments (gameR strPol A pub v) (SubState.basis ()) winObs
        {true}
      ≤ ∑' i, ENNReal.ofReal (winSig m₀ A pub v i).trace.re := hwin
    _ ≤ ∑' i, (ENNReal.ofReal (MatrixMap.conj
          ((1 : Matrix Unit Unit ℂ) ⊗ₖ Q) (winSig m₀ A pub v i)).trace.re +
          ENNReal.ofReal err * ENNReal.ofReal (winSig m₀ A pub v i).trace.re +
          ENNReal.ofReal (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ decProjS E)
            (winSig m₀ A pub v i)).trace.re) := ENNReal.tsum_le_tsum hi
    _ = ∑' i, ENNReal.ofReal (MatrixMap.conj
          ((1 : Matrix Unit Unit ℂ) ⊗ₖ Q) (winSig m₀ A pub v i)).trace.re +
          ENNReal.ofReal err * ∑' i, ENNReal.ofReal (winSig m₀ A pub v i).trace.re +
          ∑' i, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ decProjS E)
            (winSig m₀ A pub v i)).trace.re := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ ≤ _ := by
        refine add_le_add (add_le_add hev ?_) hdec
        exact (mul_le_mul_right hmass _).trans_eq (mul_one _)

set_option synthInstance.maxSize 2000 in
/-- **`endReads` for leanSPHINCS's event-side game on good data** (`strPol`, template data
`(pub, v)`): on runs with at most `progCap` program calls, from a memory with no mark and no
selection, with disjoint honest paths of in-table slots, no in-table `k`-cell an `H_msg` block and
no in-table `h`-cell an `H_msg` `h`-cell, the win weight is at most the event weight of
`Bad (evData pub v) progCap` at the end of the game, the read error of the verification's reads,
the trial-hit mass and the conflict mass. -/
theorem endReads_wGame_trialHit [DecidablePred (· ∈ Bad (S := HPos) (evData pub v) progCap)]
    (hpd : PathsDisjoint pub.xw pub.keys.1 (valsOf v)) (hsepK : HmsgSep pub v)
    (hsepH : HmsgHSep pub v) (hm₀l : AsgFree m₀.1) (hm₀ : m₀.2 = fun _ ↦ none)
    (hprog : IFreeM.IsChargeBound (gameR strPol A pub v)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap) :
    (runtimeR m₀).evalDistMap .instruments (gameR strPol A pub v) (SubState.basis ()) winObs
        {true} ≤
      (runtimeR m₀).eventWeight .instruments (hwProjector (Bad (S := HPos) (evData pub v) progCap))
          (gameR strPol A pub v)
          ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) +
        ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks) +
          trialHitMass m₀ A pub v + hConflictMass m₀ A pub v := by
  have h := @endReads_wGame_off m₀ A pub v (TrialHit pub v ∪ HConflict pub v) _
    (Classical.decPred _) hprog (preWinOff_of_good hpd hsepK hsepH hm₀l hm₀ A)
  rw [add_assoc _ (trialHitMass m₀ A pub v)]
  exact h.trans (add_le_add le_rfl (eventMassDecS_exc_le m₀ A pub v))

end final

end Quantum.Sphincs.Assembly

end
