module

public import Quantum.Par.Lockstep

@[expose] public section

/-!
# The lockstep simulation with rounds of every port

As `Quantum.Par.lockRound`, but the calls of `k` and `k'` are rounds too: a round of `w`
permutation calls becomes two rounds of `h` (all slots) and eight rounds of `k` or `k'`, each on
the slots of one direction (`lockRoundR`), with local gates in between. Every call is a call of a
round, so the hidden-value hybrid charges every call through the union bound of its round. Against
every runtime that reads its functions in the basis of a unitary, `lockRoundR` runs as the
serialized simulation (`branch_run₂_simulate_seqCalls_eq_lockRoundR`).
-/

open IPFunctor Matrix
open scoped ENNReal Kronecker

namespace Quantum.Par

open Quantum Quantum.Sponge QuantumRuntime SubInstrument

section defs

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] {w : ℕ} {E : QReg}

variable (X Z) in
/-- The signature of the lockstep simulation with rounds of every port. -/
abbrev lockSpecR : QuantumOracleSpec.{0, 0} :=
  parSpec (spongeSpec X Z) (id : SpongePort → SpongePort)

/-- Decidable equality of the slots outside a set. -/
instance instDecidableEqSlotsSub (P : Fin w → Prop) [DecidablePred P] :
    DecidableEq ({i // ¬ P i} → SlotT X Z) :=
  inferInstance

variable (X Z) in
/-- The rest of the lockstep register beside the states of the slots in `P`. -/
abbrev subRest (P : Fin w → Prop) [DecidablePred P] (m : ℕ) (E : QReg) : QReg :=
  QReg.of (((Fin m → (X × Z) × (X × Z)) × ({i // ¬ P i} → SlotT X Z)) × E)

/-- The states of the slots in `P`, enumerated by `σ`, split off the lockstep register. -/
def subSplit (P : Fin w → Prop) [DecidablePred P] {m : ℕ} (σ : Fin m ≃ {i // P i}) :
    (Fin w → SlotT X Z) × E ≃
      (Fin m → X × Z) × (((Fin m → (X × Z) × (X × Z)) × ({i // ¬ P i} → SlotT X Z)) × E) where
  toFun x := (fun j ↦ (x.1 (σ j)).1, ((fun j ↦ (x.1 (σ j)).2, fun i ↦ x.1 i.1), x.2))
  invFun y := (fun i ↦ if h : P i then (y.1 (σ.symm ⟨i, h⟩), y.2.1.1 (σ.symm ⟨i, h⟩))
    else y.2.1.2 ⟨i, h⟩, y.2.2)
  left_inv x := by
    refine Prod.ext (funext fun i ↦ ?_) rfl
    by_cases h : P i
    · simp [h]
    · simp [h]
  right_inv y := by
    refine Prod.ext (funext fun j ↦ ?_) (Prod.ext (Prod.ext (funext fun j ↦ ?_)
      (funext fun i ↦ ?_)) rfl)
    · simp [(σ j).2]
    · simp [(σ j).2]
    · simp [i.2]

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
theorem subSplit_symm_apply (P : Fin w → Prop) [DecidablePred P] {m : ℕ}
    (σ : Fin m ≃ {i // P i})
    (y : (Fin m → X × Z) × (((Fin m → (X × Z) × (X × Z)) × ({i // ¬ P i} → SlotT X Z)) × E)) :
    (subSplit P σ).symm y = (fun i ↦ if h : P i then (y.1 (σ.symm ⟨i, h⟩),
      y.2.1.1 (σ.symm ⟨i, h⟩)) else y.2.1.2 ⟨i, h⟩, y.2.2) :=
  rfl

/-- The enumeration of the slots in `P`. -/
noncomputable def subEnum (P : Fin w → Prop) [DecidablePred P] :
    Fin (Fintype.card {i // P i}) ≃ {i // P i} :=
  (Fintype.equivFin {i // P i}).symm

/-- The split of the lockstep register for a round of port `p` on the slots in `P`, the states
read as inputs of `p` through `e`. -/
noncomputable def subEquiv (p : SpongePort) (e : (X × Z) ≃ spongeIn X Z p) (P : Fin w → Prop)
    [DecidablePred P] :
    (Fin w → SlotT X Z) × E ≃ (Fin (Fintype.card {i // P i}) → spongeIn X Z p) ×
      (((Fin (Fintype.card {i // P i}) → (X × Z) × (X × Z)) × ({i // ¬ P i} → SlotT X Z)) × E) :=
  (subSplit P (subEnum P)).trans ((Equiv.arrowCongr (Equiv.refl _) e).prodCongr (Equiv.refl _))

/-- **A round of port `p` on the slots in `P`**, the states read as inputs of `p` through `e`. -/
noncomputable def subRound (p : SpongePort) (e : (X × Z) ≃ spongeIn X Z p) (P : Fin w → Prop)
    [DecidablePred P] : QComp (lockSpecR X Z) (lockReg X Z w E) (lockReg X Z w E) Unit :=
  QuantumComp₂.queryBind (spec := lockSpecR X Z)
    (.inr (.round (Fintype.card {i // P i}) fun _ ↦ p)) (subRest X Z P _ E) (subEquiv p e P)
    fun _ ↦ isoGate (fun y ↦ (subEquiv p e P).symm y) (subEquiv p e P).symm.injective

/-- The local gate of permutations of the registers of all slots. -/
noncomputable def gateAll (g : Fin w → Equiv.Perm (SlotT X Z)) :
    QComp (lockSpecR X Z) (lockReg X Z w E) (lockReg X Z w E) Unit :=
  isoGate (Prod.map (Equiv.piCongrRight g) (id : E → E))
    ((Equiv.piCongrRight g).injective.prodMap Function.injective_id)

/-- The permutation of a slot by its direction. -/
def byDir (p : PermutationPort) (a b : Equiv.Perm (SlotT X Z)) : Equiv.Perm (SlotT X Z) :=
  match p with
  | .forward => a
  | .inverse => b

variable (π : Equiv.Perm (X × Z)) (dir : Fin w → PermutationPort)

/-- **The lockstep round with rounds of every port**: two rounds of `h` on all slots and eight
rounds of `k` or `k'` on the slots of one direction, with local gates in between. -/
noncomputable def lockRoundR {A B : QReg} (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E)
    (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B) : QComp (lockSpecR X Z) A B Unit :=
  ((isoGate (copyAll dir ℓ) (copyAll_injective dir ℓ)).bind fun _ ↦
    (subRound .k (Equiv.refl _) fun i ↦ dir i = .forward).bind fun _ ↦
    (gateAll fun i ↦ byDir (dir i) (stateE π) (stateE (negRate X Z))).bind fun _ ↦
    (subRound .k' (Equiv.refl _) fun i ↦ dir i = .forward).bind fun _ ↦
    (subRound .h (Equiv.prodComm X Z) fun _ ↦ True).bind fun _ ↦
    (gateAll fun i ↦ byDir (dir i) (stateE (negRate X Z) * addT)
      (stateE (negCap X Z) * stateE (negRate X Z))).bind fun _ ↦
    (subRound .k' (Equiv.refl _) fun i ↦ dir i = .inverse).bind fun _ ↦
    (gateAll fun i ↦ byDir (dir i) 1
      (stateE (negCap X Z) * stateE π⁻¹ * stateE (negCap X Z))).bind fun _ ↦
    (subRound .k (Equiv.refl _) fun i ↦ dir i = .inverse).bind fun _ ↦
    (gateAll fun i ↦ byDir (dir i) 1 (addT * stateE (negCap X Z))).bind fun _ ↦
    (subRound .k (Equiv.refl _) fun i ↦ dir i = .inverse).bind fun _ ↦
    (gateAll fun i ↦ byDir (dir i) 1 (stateE π)).bind fun _ ↦
    (subRound .k' (Equiv.refl _) fun i ↦ dir i = .inverse).bind fun _ ↦
    (subRound .h (Equiv.prodComm X Z) fun _ ↦ True).bind fun _ ↦
    (gateAll fun i ↦ byDir (dir i) (stateE (negCap X Z) * stateE (negRate X Z)) 1).bind fun _ ↦
    (subRound .k' (Equiv.refl _) fun i ↦ dir i = .forward).bind fun _ ↦
    (gateAll fun i ↦ byDir (dir i)
      (stateE (negCap X Z) * stateE π⁻¹ * stateE (negCap X Z)) 1).bind fun _ ↦
    (subRound .k (Equiv.refl _) fun i ↦ dir i = .forward).bind fun _ ↦
    gateAll fun i ↦ byDir (dir i) (stateE (negCap X Z)) 1).bind
  fun _ ↦ coGate (uncopyAll dir post) (uncopyAll_injective dir post)

end defs

/-! ## Semantics against a read runtime -/

section sem

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] {w : ℕ} {E D : QReg} (σ₀ : SubState D) (rd : D → SpongeKeys X Z)

variable (D) in
/-- The parallel read runtime with rounds of every port. -/
noncomputable abbrev readParR : QuantumRuntime (lockSpecR X Z) :=
  (readRuntime D σ₀ rd).par id

theorem runsAs_gateAll (g : Fin w → Equiv.Perm (SlotT X Z)) :
    RunsAs (readParR D σ₀ rd) (gateAll (E := E) g) (allMap fun i _ ↦ g i) :=
  (runsAs_isoGate _ _).congr fun _ ↦ rfl

theorem runsAs_subRound (p : SpongePort) (e : (X × Z) ≃ spongeIn X Z p) (P : Fin w → Prop)
    [DecidablePred P] :
    RunsAs (readParR D σ₀ rd) (subRound (E := E) p e P)
      (allMap fun i s ↦ if P i then stateE (e.trans ((spongeKeyEquiv (rd s) p).trans e.symm))
        else 1) := by
  unfold subRound
  have : Unique ((lockSpecR X Z).Result (.inr (.round (Fintype.card {i // P i}) fun _ ↦ p))) :=
    inferInstanceAs (Unique (Fin _ → Unit))
  refine (RunsAs.queryBind (R := readParR D σ₀ rd)
    (i := .inr (.round (Fintype.card {i // P i}) fun _ ↦ p)) _
    (fun r ↦ branch_roundStep_basis (R := readRuntime D σ₀ rd)
      (G := fun p s ↦ spongeKeyEquiv (rd s) p) (fun p r ↦ readRuntime_branch p r) _ r) _ _
    fun _ ↦ runsAs_isoGate _ _).congr fun q ↦ ?_
  refine Prod.ext (Prod.ext (funext fun i ↦ ?_) rfl) rfl
  change ((subSplit P (subEnum P)).symm ((fun j ↦ e.symm (spongeKeyEquiv (rd q.2) p
    (e (q.1.1 (subEnum P j)).1))), (((fun j ↦ (q.1.1 (subEnum P j)).2),
      fun i ↦ q.1.1 i.1), q.1.2))).1 i = _
  rw [subSplit_symm_apply]
  by_cases h : P i
  · simp only [h, ↓reduceDIte, ↓reduceIte, allMap, Equiv.apply_symm_apply]
    rfl
  · simp [h, allMap]

omit [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] in
theorem negCap_cap_negCap_apply (k : X → Z) (u : X × Z) :
    negCap X Z (capacityRound k (negCap X Z u)) = (capacityRound k)⁻¹ u := by
  simp [negCap, capacityRound_inv_apply, sub_eq_add_neg, add_comm]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
theorem negRate_rate_negRate_apply (h : Z → X) (u : X × Z) :
    negRate X Z (rateRound h (negRate X Z u)) = (rateRound h)⁻¹ u := by
  simp [negRate, rateRound_inv_apply, sub_eq_add_neg, add_comm]

theorem runsAs_subRound_k (P : Fin w → Prop) [DecidablePred P] :
    RunsAs (readParR D σ₀ rd) (subRound (E := E) .k (Equiv.refl _) P)
      (allMap fun i s ↦ if P i then stateE (capacityRound (rd s).2.1) else 1) :=
  (runsAs_subRound σ₀ rd .k (Equiv.refl _) P).congr fun q ↦ congrArg (fun g ↦ allMap g q)
    (funext fun _ ↦ funext fun _ ↦ by congr 1; exact Equiv.ext fun _ ↦ rfl)

theorem runsAs_subRound_k' (P : Fin w → Prop) [DecidablePred P] :
    RunsAs (readParR D σ₀ rd) (subRound (E := E) .k' (Equiv.refl _) P)
      (allMap fun i s ↦ if P i then stateE (capacityRound (rd s).2.2) else 1) :=
  (runsAs_subRound σ₀ rd .k' (Equiv.refl _) P).congr fun q ↦ congrArg (fun g ↦ allMap g q)
    (funext fun _ ↦ funext fun _ ↦ by congr 1; exact Equiv.ext fun _ ↦ rfl)

theorem runsAs_subRound_h (P : Fin w → Prop) [DecidablePred P] :
    RunsAs (readParR D σ₀ rd) (subRound (E := E) .h (Equiv.prodComm X Z) P)
      (allMap fun i s ↦ if P i then stateE (rateRound (rd s).1) else 1) :=
  (runsAs_subRound σ₀ rd .h (Equiv.prodComm X Z) P).congr fun q ↦ congrArg (fun g ↦ allMap g q)
    (funext fun _ ↦ funext fun _ ↦ by congr 1; exact Equiv.ext fun _ ↦ rfl)

variable (π : Equiv.Perm (X × Z)) (dir : Fin w → PermutationPort)

/-- **The lockstep round with rounds runs as the round of the permutation oracle read off the
register.** -/
theorem runsAs_lockRoundR {A B : QReg} (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E)
    (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B) :
    RunsAs (readParR D σ₀ rd) (lockRoundR π dir ℓ post) (fun q : A × D ↦
      (post ((fun i ↦ oracleEquiv (portPerm (spongePerm (rd q.2) π) (dir i)) ((ℓ q.1).1 i) :
        ∀ i, (qrpmSpec (X × Z)).Out (dir i)), (ℓ q.1).2), q.2)) := by
  unfold lockRoundR
  refine RunsAs.bind_coGate ((runsAs_isoGate _ _).bind
    ((runsAs_subRound_k σ₀ rd _).bind ((runsAs_gateAll σ₀ rd _).bind
    ((runsAs_subRound_k' σ₀ rd _).bind ((runsAs_subRound_h σ₀ rd _).bind
    ((runsAs_gateAll σ₀ rd _).bind ((runsAs_subRound_k' σ₀ rd _).bind
    ((runsAs_gateAll σ₀ rd _).bind ((runsAs_subRound_k σ₀ rd _).bind
    ((runsAs_gateAll σ₀ rd _).bind ((runsAs_subRound_k σ₀ rd _).bind
    ((runsAs_gateAll σ₀ rd _).bind ((runsAs_subRound_k' σ₀ rd _).bind
    ((runsAs_subRound_h σ₀ rd _).bind ((runsAs_gateAll σ₀ rd _).bind
    ((runsAs_subRound_k' σ₀ rd _).bind ((runsAs_gateAll σ₀ rd _).bind
    ((runsAs_subRound_k σ₀ rd _).bind (runsAs_gateAll σ₀ rd _)))))))))))))))))))
    _ _ _ fun q ↦ ?_
  refine Prod.ext (Prod.ext (funext fun i ↦ ?_) ?_) rfl
  · simp only [Function.comp_apply, Prod.map, allMap, copyAll, uncopyAll, id,
      Equiv.symm_apply_apply]
    cases hd : dir i
    · simp only [byDir, ↓reduceIte, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
        reduceCtorEq, stateE_apply, addT_apply, negCap_cap_negCap_apply,
        negRate_rate_negRate_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      rfl
    · simp only [byDir, ↓reduceIte, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
        reduceCtorEq, stateE_apply, addT_apply, negCap_cap_negCap_apply,
        negRate_rate_negRate_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
      rfl
  · simp [Function.comp_apply, Prod.map, allMap, copyAll, uncopyAll]

/-- **Lockstep with rounds = serialized simulation, against a read runtime.** -/
theorem branch_run₂_simulate_seqCalls_read_R {A B : QReg}
    (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E) (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B)
    (rs : RoundResult (qrpmSpec (X × Z)) dir) :
    ((readRuntime D σ₀ rd).run₂ .instruments
        (simulate LocalSig.Interp.instruments π (seqCalls dir E ℓ post))).branch rs =
      ((readParR D σ₀ rd).run₂ .instruments (lockRoundR π dir ℓ post)).branch () := by
  have h1 : (readRuntime D σ₀ rd).run₂ .instruments
      (simulate LocalSig.Interp.instruments π (seqCalls dir E ℓ post)) =
        (permReadRuntime D σ₀ π rd).run₂ .instruments (seqCalls dir E ℓ post) :=
    congrArg (fun P ↦ DSubInstrument.comap (QuantumComp₂.leafEquiv B
      (RoundResult (qrpmSpec (X × Z)) dir)) (QuantumComp₂.leafEquiv B _).injective P)
      (run_simulate_read σ₀ rd (L := LocalSig.instruments.{0})
        (W := QuantumComp₂.Leaf B (RoundResult (qrpmSpec (X × Z)) dir))
        LocalSig.Interp.instruments π (seqCalls dir E ℓ post))
  rw [h1, branch_run₂_seqCalls_basis (fun p r ↦ permReadRuntime_branch σ₀ rd π p r)]
  exact (runsAs_lockRoundR σ₀ rd π dir ℓ post).symm

end sem

/-! ## Runtimes that read their functions in a unitary basis -/

section transfer

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] (R : QuantumRuntime (spongeSpec X Z)) (U : Matrix R.D R.D ℂ)
  (hU : U ∈ unitaryGroup R.D ℂ) (rd : R.D → SpongeKeys X Z) (hR : IsReadRuntime R U rd)

include hU hR in
/-- **Lockstep with rounds = serialized simulation**, against every runtime that reads its
functions in the basis of a unitary. -/
theorem branch_run₂_simulate_seqCalls_eq_lockRoundR (π : Equiv.Perm (X × Z)) {w : ℕ}
    (dir : Fin w → PermutationPort) (E : QReg) {A B : QReg}
    (ℓ : A ≃ roundIn (qrpmSpec (X × Z)) dir × E) (post : roundOut (qrpmSpec (X × Z)) dir × E ≃ B)
    (rs : RoundResult (qrpmSpec (X × Z)) dir) :
    (R.run₂ .instruments (simulate LocalSig.Interp.instruments π (seqCalls dir E ℓ post))).branch
        rs = ((R.par id).run₂ .instruments (lockRoundR π dir ℓ post)).branch () := by
  have hpar : (R.par id).run₂ .instruments (lockRoundR π dir ℓ post) =
      R.run₂ .instruments (IFreeM.substitute (parToSeq (spec := spongeSpec X Z) id)
        (lockRoundR π dir ℓ post)) :=
    congrArg (fun P ↦ DSubInstrument.comap (QuantumComp₂.leafEquiv B Unit)
      (QuantumComp₂.leafEquiv B Unit).injective P)
      (R.run_substitute_parToSeq id (lockRoundR π dir ℓ post)).symm
  have hpar' : (readParR R.D R.init rd).run₂ .instruments (lockRoundR π dir ℓ post) =
      (readRuntime R.D R.init rd).run₂ .instruments
        (IFreeM.substitute (parToSeq (spec := spongeSpec X Z) id) (lockRoundR π dir ℓ post)) :=
    congrArg (fun P ↦ DSubInstrument.comap (QuantumComp₂.leafEquiv B Unit)
      (QuantumComp₂.leafEquiv B Unit).injective P)
      ((readRuntime R.D R.init rd).run_substitute_parToSeq id (lockRoundR π dir ℓ post)).symm
  have e1 := branch_run₂_eq_conj_read R U hU rd hR
    (simulate LocalSig.Interp.instruments π (seqCalls dir E ℓ post)) rs
  have e2 := branch_run₂_eq_conj_read R U hU rd hR
    (IFreeM.substitute (parToSeq (spec := spongeSpec X Z) id) (lockRoundR π dir ℓ post)) ()
  have e3 := branch_run₂_simulate_seqCalls_read_R R.init rd π dir ℓ post rs
  refine e1.trans (Eq.trans ?_ (e2.symm.trans (congrArg (fun P ↦ P.branch ()) hpar.symm)))
  exact congrArg (fun L ↦ MatrixMap.conj ((1 : Matrix B B ℂ) ⊗ₖ Uᴴ) ∘ₗ L ∘ₗ
    MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ U)) (e3.trans (congrArg (fun P ↦ P.branch ()) hpar'))

end transfer

end Quantum.Par

end
