import KeccakGkr.Protocol

/-!
# Soundness

`protocol_sound`: for any committed column and any prover, with arbitrary private memory and
randomness, the probability that the verifier ends holding true claims on the column while the
statement is false is at most `(n + 10 + D (3n + 84) + 32) / |E|`. For Keccak, `D = 12` and
`κ = n + 4` steps' variables, this is the `(37 κ + 902) / |E|` of `§keccak:soundness`.
-/

open Polynomial OracleComp
open scoped ENNReal

namespace KeccakGkr

variable {E : Type} [Field E] [CharP E 2] [Fintype E] [DecidableEq E] [SampleableType E]
variable (P : Perm) (D : ℕ) {n : ℕ} (Q : Column n) (x : E)

/-! ## The start -/

/-- The data the layers carry is good for the prover: the statement is false, `c_st` true. -/
def FalsePx (c : Ctx E n) : Prop := ¬ Statement P D Q x c.rl c.rp c.v ∧ OutClaim Q x c

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem segDiff_ne (hx : WordBasis x) (hc : ¬ Chain P D Q) :
    ∃ i p ℓ, segDiff P D Q x i p ℓ ≠ 0 := by
  simp only [Chain, not_forall] at hc
  obtain ⟨i, p, hip⟩ := hc
  obtain ⟨⟨ℓ, z⟩, hj⟩ := Function.ne_iff.mp hip
  refine ⟨i, p, ℓ, fun h => hj ?_⟩
  have := hx (fun z => segState P D Q false D i p (ℓ, z) - Q i p (slotCube true ℓ) z) (by
    simpa [segDiff, word, colWord, ← Finset.sum_sub_distrib, sub_mul] using h) z
  exact sub_eq_zero.mp this

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem segDiff_eq_zero (hc : Chain P D Q) (i : Cube 4) (p : Cube n) (ℓ : Lane) :
    segDiff P D Q x i p ℓ = 0 := by
  simp only [segDiff, hc i p, word, colWord, segInput, sub_self]

/-- After `r_low`: the first segment is wrong, and `r_low` hides it in every pack. -/
def StartGood₁ (rl : Fin 4 → E) : Prop := ¬ Chain P D Q ∧ ∀ p ℓ, diffLow P D Q x rl p ℓ = 0

/-- After `r_pack`: the first segment is wrong, and the step point hides it. -/
def StartGood₂ (a : (Fin 4 → E) × (Fin n → E)) : Prop :=
  ¬ Chain P D Q ∧ ∀ ℓ, diffStep P D Q x a.1 a.2 ℓ = 0

/-- After `r_seg` and `r_lane`: the statement is false, and `ρ` hides it. -/
def StartGood₄ (a : Pre E n) : Prop :=
  ¬ Statement P D Q x a.1.1.1 a.1.1.2 a.1.2 ∧ mle (startTable P D Q x a.1.1.1 a.1.1.2 a.1.2) a.2 = 0

theorem start_sound (hx : WordBasis x) :
    (start P D Q x).Sound (fun _ => True) (ClaimGood P D Q D (FalsePx P D Q x))
      ((n + 10) / Fintype.card E) := by
  have h1 : (Phase.sample (Fin 4 → E) fun (_ : Unit) rl => rl).Sound (fun _ => True)
      (StartGood₁ P D Q x) (4 / Fintype.card E) := by
    refine Phase.sample_sound fun _ _ => ?_
    by_cases hc : Chain P D Q
    · exact le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun _ h => h.1 hc) zero_le
    · obtain ⟨i, p, ℓ, hne⟩ := segDiff_ne P D Q x hx hc
      have hg : (fun i => segDiff P D Q x i p ℓ) ≠ 0 := fun h => hne (congrFun h i)
      refine (prEvent_mono _ _ (fun rl => mle (fun i => segDiff P D Q x i p ℓ) rl = 0)
        fun rl h => h.2 p ℓ).trans ?_
      simpa using prob_mle_eq_zero_le _ hg
  have h2 : (Phase.sample (Fin n → E) fun (rl : Fin 4 → E) rp => (rl, rp)).Sound
      (fun rl => ¬ StartGood₁ P D Q x rl) (StartGood₂ P D Q x) (n / Fintype.card E) := by
    refine Phase.sample_sound fun rl hrl => ?_
    by_cases hc : Chain P D Q
    · exact le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun _ h => h.1 hc) zero_le
    · simp only [StartGood₁, hc, not_false_eq_true, true_and, not_forall] at hrl
      obtain ⟨p, ℓ, hne⟩ := hrl
      have hg : (fun p => diffLow P D Q x rl p ℓ) ≠ 0 := fun h => hne (congrFun h p)
      exact (prEvent_mono _ _ (fun rp => mle (fun p => diffLow P D Q x rl p ℓ) rp = 0)
        fun rp h => h.2 ℓ).trans (prob_mle_eq_zero_le _ hg)
  have h3 : (Phase.receive (Lane → E) (fun (a : (Fin 4 → E) × (Fin n → E)) v => (a, v))
      fun a ℓ => outEval P D Q x ℓ a.1 a.2).Sound (fun a => ¬ StartGood₂ P D Q x a)
        (fun a => StartGood₂ P D Q x a.1) 0 :=
    Phase.receive_sound fun _ h _ => h
  have h4 : (Phase.sample (Fin 6 → E) fun (a : ((Fin 4 → E) × (Fin n → E)) × (Lane → E)) ρ =>
      (a, ρ)).Sound (fun a => ¬ StartGood₂ P D Q x a.1) (StartGood₄ P D Q x)
        (6 / Fintype.card E) := by
    refine Phase.sample_sound fun a ha => ?_
    by_cases hst : Statement P D Q x a.1.1 a.1.2 a.2
    · exact le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun _ h => h.1 hst) zero_le
    · have hne : startTable P D Q x a.1.1 a.1.2 a.2 ≠ 0 := by
        intro h0
        by_cases hc : Chain P D Q
        · simp only [Statement, hc, true_and, not_forall] at hst
          obtain ⟨ℓ, hℓ⟩ := hst
          have := congrFun h0 (Fin.cons true (laneCube ℓ))
          simp only [startTable, Fin.cons_zero, ite_true, Fin.tail_cons,
            pad_enc laneCube laneCube_injective, Pi.zero_apply, sub_eq_zero] at this
          exact hℓ this.symm
        · simp only [StartGood₂, hc, not_false_eq_true, true_and, not_forall] at ha
          obtain ⟨ℓ, hℓ⟩ := ha
          have := congrFun h0 (Fin.cons false (laneCube ℓ))
          simp only [startTable, Fin.cons_zero, Bool.false_eq_true, ite_false, Fin.tail_cons,
            pad_enc laneCube laneCube_injective, Pi.zero_apply] at this
          exact hℓ this
      exact (prEvent_mono _ _ _ fun ρ h => h.2).trans (by simpa using prob_mle_eq_zero_le _ hne)
  have h5 : (Phase.receive E (fun (a : Pre E n) cst => some (mkCtx a cst, firstClaim x (mkCtx a cst)))
      fun a => outTotal Q x a.1.1.1 a.1.1.2 a.2).Sound (fun a => ¬ StartGood₄ P D Q x a)
        (ClaimGood P D Q D (FalsePx P D Q x)) 0 := by
    refine Phase.receive_sound fun a ha cst h => ha ?_
    obtain ⟨⟨hst, hout⟩, hcl⟩ := h
    refine ⟨hst, ?_⟩
    have hid := firstClaim_identity P D Q x (mkCtx a cst)
    rw [← hcl, sub_self, zero_add, sub_eq_zero.mpr hout] at hid
    exact hid.symm
  refine (h1.comp (h2.comp (h3.comp (h4.comp h5)))).mono (fun _ h => h) (fun _ h => h)
    (le_of_eq ?_)
  simp only [ENNReal.div_eq_inv_mul, zero_add, add_zero]
  ring

/-! ## The openings -/

/-- After the opening of `c_st`: the statement is false, the last claim and the claim on the
column's words both true. -/
def OutGood : Option (OutStage E n) → Prop
  | none => False
  | some s => ¬ Statement P D Q x s.1.rl s.1.rp s.1.v ∧ s.2.1.Holds P D Q 0 ∧
      colEval Q x s.1.rl s.1.rp s.2.2.1 = s.2.2.2

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem total_outSum (cc : Ctx E n × Claim E n) :
    (outSum Q x).total cc = outTotal Q x cc.1.rl cc.1.rp cc.1.ρ :=
  total_out Q x _ _ _ _

theorem outOpen_sound :
    (outOpen Q x).Sound (fun st => ¬ ClaimGood P D Q 0 (FalsePx P D Q x) st)
      (OutGood P D Q x) (12 / Fintype.card E) := by
  set Pout : Ctx E n × Claim E n → Prop :=
    fun cc => ¬ Statement P D Q x cc.1.rl cc.1.rp cc.1.v ∧ cc.2.Holds P D Q 0
  have o1 : (Phase.compute fun (st : Option (Ctx E n × Claim E n)) =>
      st.map fun cc => (cc, cc.1.cst)).Sound
        (fun st => ¬ ClaimGood P D Q 0 (FalsePx P D Q x) st) ((outSum Q x).True' Pout) 0 := by
    refine Phase.compute_sound fun st hst h => ?_
    rcases st with _ | ⟨c, cl⟩
    · exact h
    · obtain ⟨⟨hst', hcl⟩, hc⟩ := h
      exact hst ⟨⟨hst', hc.trans (total_outSum Q x _)⟩, hcl⟩
  have o2 := sumcheck_sound 6 (outSum Q x) Pout
  have o3 : (Phase.receive E checkOut fun st =>
      match st with
      | some s => colEval Q x s.1.1.rl s.1.1.rp s.2.1
      | none => 0).Sound (fun st => ¬ (outSum Q x).Good Pout st) (OutGood P D Q x) 0 := by
    refine Phase.receive_sound fun st hst cout h => hst ?_
    rcases st with _ | ⟨cc, fo, v⟩
    · exact h
    · simp only [checkOut, Option.bind_some] at h
      split_ifs at h with hc
      · obtain ⟨hst', hcl, hcol⟩ := h
        refine ⟨⟨hst', hcl⟩, ?_⟩
        simp only at hc hcol ⊢
        rw [hc, ← hcol]
        rfl
      · exact h.elim
  refine (o1.comp (o2.comp o3)).mono (fun _ h => h) (fun _ h => h) (le_of_eq ?_)
  simp only [ENNReal.div_eq_inv_mul, zero_add, add_zero]
  push_cast
  ring

/-- Before the opening of the last claim: the statement is false, the claim on the column's
words true. -/
def InPx (s : OutStage E n) : Prop :=
  ¬ Statement P D Q x s.1.rl s.1.rp s.1.v ∧ colEval Q x s.1.rl s.1.rp s.2.2.1 = s.2.2.2

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem total_inSum₁ (s : OutStage E n) :
    (inSum₁ (E := E) Q).total s = claimValue P D Q 0 s.2.1.μ s.2.1.r s.2.1.w :=
  total_in₁ P D Q s.2.1

omit [Fintype E] [DecidableEq E] [SampleableType E] in
theorem total_inSum₂ (s : OutStage E n × (Fin 4 → E)) :
    (inSum₂ (E := E) Q).total s = (inSum₁ (E := E) Q).f s.1 s.2 :=
  total_in₂ Q _ _ _ _ _

theorem inOpen_sound :
    (inOpen Q).Sound (fun st => ¬ OutGood P D Q x st) (Fooled P D Q x) (20 / Fintype.card E) := by
  have i1 : (Phase.compute fun (st : Option (OutStage E n)) => st.map fun s => (s, s.2.1.c)).Sound
      (fun st => ¬ OutGood P D Q x st) ((inSum₁ (E := E) Q).True' (InPx P D Q x)) 0 := by
    refine Phase.compute_sound fun st hst h => ?_
    rcases st with _ | s
    · exact h
    · obtain ⟨⟨hst', hcol⟩, hc⟩ := h
      exact hst ⟨hst', hc.trans (total_inSum₁ P D Q s), hcol⟩
  have i2 : ((sumcheck 4 (inSum₁ (E := E) Q)).map fun st =>
      st.map fun c => ((c.1, c.2.1), c.2.2)).Sound
        (fun st => ¬ (inSum₁ (E := E) Q).True' (InPx P D Q x) st)
        ((inSum₂ (E := E) Q).True' fun c => InPx P D Q x c.1) ((4 : ℕ) * (2 : ℕ) / Fintype.card E) := by
    refine Phase.Sound.map ((sumcheck_sound 4 (inSum₁ (E := E) Q) (InPx P D Q x)).mono
      (fun _ h => h) (fun st h => ?_) le_rfl)
    rcases st with _ | ⟨s, fl, v⟩
    · exact h
    · obtain ⟨hPx, hv⟩ := h
      exact ⟨hPx, hv.trans (total_inSum₂ Q (s, fl))⟩
  have i3 := sumcheck_sound 6 (inSum₂ (E := E) Q) fun c => InPx P D Q x c.1
  have i4 : (Phase.receive (Slice → E) checkIn fun st =>
      match st with
      | some s => fun z => sliceEval Q z s.1.2 (Fin.init s.1.1.2.1.r) s.2.1
      | none => 0).Sound (fun st => ¬ (inSum₂ (E := E) Q).Good (fun c => InPx P D Q x c.1) st)
        (Fooled P D Q x) 0 := by
    refine Phase.receive_sound fun st hst sl h => hst ?_
    rcases st with _ | ⟨sf, fo, v⟩
    · exact h
    · simp only [checkIn, Option.bind_some] at h
      split_ifs at h with hc
      · obtain ⟨hout, hin, hst'⟩ := h
        refine ⟨⟨hst', hout⟩, ?_⟩
        simp only at hc ⊢
        rw [hc]
        simp only [InEval] at hin
        simp only [inSum₂, inSummand₂, hin]
      · exact h.elim
  refine (i1.comp (i2.comp (i3.comp i4))).mono (fun _ h => h) (fun _ h => h) (le_of_eq ?_)
  simp only [ENNReal.div_eq_inv_mul, zero_add, add_zero]
  push_cast
  ring

/-! ## The protocol -/

/-- **Soundness.** For any committed column and any prover strategy (arbitrary private memory,
randomness and effects), the verifier ends holding true claims on the column, though the
statement is false, with probability at most `(n + 42 + D (3n + 84)) / |E|`. -/
theorem protocol_sound (hx : WordBasis x) :
    (protocol P D Q x).Sound (fun _ => True) (Fooled P D Q x)
      ((n + 42 + D * (3 * n + 84)) / Fintype.card E) := by
  refine ((start_sound P D Q x hx).comp ((layers_sound P D Q (FalsePx P D Q x) D).comp
    ((outOpen_sound P D Q x).comp (inOpen_sound P D Q x)))).mono (fun _ h => h) (fun _ h => h)
    (le_of_eq ?_)
  simp only [ENNReal.div_eq_inv_mul]
  ring

end KeccakGkr
