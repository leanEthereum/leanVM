import VCVio.ProgramLogic.Relational.Basic

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

section GeneralFiberCoupling

variable {α β γ : Type} [DecidableEq γ]

noncomputable def generalFiberMass
    (p : PMF α) (f : α → γ) (value : γ) : ENNReal :=
  ∑' candidate, if f candidate = value then p candidate else 0

theorem generalFiberMass_eq_map_apply
    (p : PMF α) (f : α → γ) (value : γ) :
    generalFiberMass p f value = p.map f value := by
  rw [generalFiberMass, PMF.map_apply]
  apply tsum_congr
  intro candidate
  by_cases heq : f candidate = value
  · simp [heq]
  · simp [heq, Ne.symm heq]

noncomputable def generalFiberCouplingWeight
    (p : PMF α) (q : PMF β)
    (f : α → γ) (g : β → γ) (pair : α × β) : ENNReal :=
  if f pair.1 = g pair.2 then
    p pair.1 * q pair.2 * (generalFiberMass p f (f pair.1))⁻¹
  else
    0

theorem generalFiberMass_ne_zero_of_apply_ne_zero
    (p : PMF α) (f : α → γ) (value : α) (hvalue : p value ≠ 0) :
    generalFiberMass p f (f value) ≠ 0 := by
  unfold generalFiberMass
  intro hzero
  rw [ENNReal.tsum_eq_zero] at hzero
  exact hvalue (by simpa using hzero value)

theorem generalFiberMass_ne_top
    (p : PMF α) (f : α → γ) (value : γ) :
    generalFiberMass p f value ≠ ∞ := by
  apply ne_top_of_le_ne_top one_ne_top
  rw [generalFiberMass_eq_map_apply]
  exact PMF.coe_le_one (p.map f) value

set_option maxHeartbeats 1600000 in
theorem generalFiberCouplingWeight_sum_right
    (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (hmap : p.map f = q.map g) (left : α) :
    ∑' right, generalFiberCouplingWeight p q f g (left, right) =
      p left := by
  simp only [generalFiberCouplingWeight]
  calc
    (∑' right,
        if f left = g right then
          p left * q right * (generalFiberMass p f (f left))⁻¹
        else 0) =
      p left * ((∑' right,
          if g right = f left then q right else 0) *
        (generalFiberMass p f (f left))⁻¹) := by
          calc
            (∑' right,
                if f left = g right then
                  p left * q right * (generalFiberMass p f (f left))⁻¹
                else 0) =
              ∑' right, p left *
                ((if g right = f left then q right else 0) *
                  (generalFiberMass p f (f left))⁻¹) := by
                    apply tsum_congr
                    intro right
                    by_cases heq : f left = g right
                    · rw [if_pos heq, if_pos heq.symm]
                      ac_rfl
                    · rw [if_neg heq, if_neg (Ne.symm heq)]
                      simp
            _ = p left * ∑' right,
                (if g right = f left then q right else 0) *
                  (generalFiberMass p f (f left))⁻¹ :=
              ENNReal.tsum_mul_left
            _ = p left * ((∑' right,
                if g right = f left then q right else 0) *
                  (generalFiberMass p f (f left))⁻¹) := by
              rw [ENNReal.tsum_mul_right]
    _ = p left * (generalFiberMass p f (f left) *
        (generalFiberMass p f (f left))⁻¹) := by
      congr 2
      calc
        (∑' right, if g right = f left then q right else 0) =
            generalFiberMass q g (f left) := rfl
        _ = q.map g (f left) := generalFiberMass_eq_map_apply q g (f left)
        _ = p.map f (f left) := by rw [hmap]
        _ = generalFiberMass p f (f left) :=
          (generalFiberMass_eq_map_apply p f (f left)).symm
    _ = p left := by
      by_cases hleft : p left = 0
      · simp [hleft]
      · rw [ENNReal.mul_inv_cancel
          (generalFiberMass_ne_zero_of_apply_ne_zero p f left hleft)
          (generalFiberMass_ne_top p f (f left)), mul_one]

set_option maxHeartbeats 1600000 in
theorem generalFiberCouplingWeight_sum_left
    (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (hmap : p.map f = q.map g) (right : β) :
    ∑' left, generalFiberCouplingWeight p q f g (left, right) =
      q right := by
  simp only [generalFiberCouplingWeight]
  calc
    (∑' left,
        if f left = g right then
          p left * q right * (generalFiberMass p f (f left))⁻¹
        else 0) =
      q right * ((∑' left,
          if f left = g right then p left else 0) *
        (generalFiberMass p f (g right))⁻¹) := by
          calc
            (∑' left,
                if f left = g right then
                  p left * q right * (generalFiberMass p f (f left))⁻¹
                else 0) =
              ∑' left, q right *
                ((if f left = g right then p left else 0) *
                  (generalFiberMass p f (g right))⁻¹) := by
                    apply tsum_congr
                    intro left
                    by_cases heq : f left = g right
                    · rw [if_pos heq, if_pos heq, heq]
                      ac_rfl
                    · simp [heq]
            _ = q right * ∑' left,
                (if f left = g right then p left else 0) *
                  (generalFiberMass p f (g right))⁻¹ :=
              ENNReal.tsum_mul_left
            _ = q right * ((∑' left,
                if f left = g right then p left else 0) *
                  (generalFiberMass p f (g right))⁻¹) := by
              rw [ENNReal.tsum_mul_right]
    _ = q right * (generalFiberMass q g (g right) *
        (generalFiberMass q g (g right))⁻¹) := by
      have hmass : generalFiberMass p f (g right) =
          generalFiberMass q g (g right) :=
        (generalFiberMass_eq_map_apply p f (g right)).trans
          ((by rw [hmap]) : p.map f (g right) = q.map g (g right)) |>.trans
            (generalFiberMass_eq_map_apply q g (g right)).symm
      rw [show (∑' left, if f left = g right then p left else 0) =
          generalFiberMass p f (g right) from rfl, hmass]
    _ = q right := by
      by_cases hright : q right = 0
      · simp [hright]
      · rw [ENNReal.mul_inv_cancel
          (generalFiberMass_ne_zero_of_apply_ne_zero q g right hright)
          (generalFiberMass_ne_top q g (g right)), mul_one]

set_option maxHeartbeats 1600000 in
theorem generalFiberCouplingWeight_sum_eq_one
    (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (hmap : p.map f = q.map g) :
    ∑' pair, generalFiberCouplingWeight p q f g pair = 1 := by
  calc
    (∑' pair : α × β, generalFiberCouplingWeight p q f g pair) =
        ∑' left, ∑' right,
          generalFiberCouplingWeight p q f g (left, right) :=
      by
        rw [← ENNReal.tsum_prod]
    _ = ∑' left, p left := by
      simp_rw [generalFiberCouplingWeight_sum_right p q f g hmap]
    _ = 1 := p.tsum_coe

noncomputable def generalFiberCoupling
    (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (hmap : p.map f = q.map g) : PMF (α × β) :=
  PMF.normalize (generalFiberCouplingWeight p q f g)
    (by rw [generalFiberCouplingWeight_sum_eq_one p q f g hmap]; exact one_ne_zero)
    (by rw [generalFiberCouplingWeight_sum_eq_one p q f g hmap]; exact one_ne_top)

@[simp]
theorem generalFiberCoupling_apply
    (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (hmap : p.map f = q.map g) (pair : α × β) :
    generalFiberCoupling p q f g hmap pair =
      generalFiberCouplingWeight p q f g pair := by
  unfold generalFiberCoupling
  rw [PMF.normalize_apply,
    generalFiberCouplingWeight_sum_eq_one p q f g hmap]
  simp

theorem generalFiberCoupling_isCoupling
    (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (hmap : p.map f = q.map g) :
    PMF.IsCoupling (generalFiberCoupling p q f g hmap) p q := by
  classical
  constructor
  · ext left
    rw [PMF.map_apply]
    change (∑' pair : α × β,
      (fun candidate right => if left = candidate then
        generalFiberCoupling p q f g hmap (candidate, right) else 0)
          pair.1 pair.2) = p left
    calc
      (∑' pair : α × β,
          (fun candidate right => if left = candidate then
            generalFiberCoupling p q f g hmap (candidate, right) else 0)
              pair.1 pair.2) =
        ∑' candidate, ∑' right,
          if left = candidate then
            generalFiberCoupling p q f g hmap (candidate, right) else 0 := by
          rw [← ENNReal.tsum_prod]
      _ = (∑' candidate, ∑' right,
          if left = candidate then
            generalFiberCouplingWeight p q f g (candidate, right) else 0) := by
          simp only [generalFiberCoupling_apply]
      _ =
        ∑' right, generalFiberCouplingWeight p q f g (left, right) := by
          calc
            (∑' candidate, ∑' right,
                if left = candidate then
                  generalFiberCouplingWeight p q f g (candidate, right) else 0) =
              ∑' candidate, if candidate = left then
                (∑' right,
                  generalFiberCouplingWeight p q f g (candidate, right)) else 0 := by
                    apply tsum_congr
                    intro candidate
                    by_cases heq : candidate = left
                    · subst candidate
                      simp
                    · simp [heq, Ne.symm heq]
            _ = ∑' right,
                generalFiberCouplingWeight p q f g (left, right) :=
              tsum_ite_eq left _
      _ = p left := generalFiberCouplingWeight_sum_right p q f g hmap left
  · ext right
    rw [PMF.map_apply]
    change (∑' pair : α × β,
      (fun left candidate => if right = candidate then
        generalFiberCoupling p q f g hmap (left, candidate) else 0)
          pair.1 pair.2) = q right
    calc
      (∑' pair : α × β,
          (fun left candidate => if right = candidate then
            generalFiberCoupling p q f g hmap (left, candidate) else 0)
              pair.1 pair.2) =
        ∑' left, ∑' candidate,
          if right = candidate then
            generalFiberCoupling p q f g hmap (left, candidate) else 0 := by
          rw [← ENNReal.tsum_prod]
      _ = (∑' left, ∑' candidate,
          if right = candidate then
            generalFiberCouplingWeight p q f g (left, candidate) else 0) := by
          simp only [generalFiberCoupling_apply]
      _ =
        ∑' left, generalFiberCouplingWeight p q f g (left, right) := by
          apply tsum_congr
          intro left
          convert tsum_ite_eq right
            (fun candidate => generalFiberCouplingWeight p q f g (left, candidate))
            using 1
          apply tsum_congr
          intro candidate
          by_cases heq : candidate = right
          · simp [heq]
          · simp [heq, Ne.symm heq]
      _ = q right := generalFiberCouplingWeight_sum_left p q f g hmap right

end GeneralFiberCoupling

section GeneralRelTriple

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  [IsUniformSpec spec₁] [IsUniformSpec spec₂]
  {α β γ : Type} [DecidableEq γ]

noncomputable def generalSuccessPMF
    (p : SPMF α) (hfail : p.toPMF none = 0) : PMF α :=
  PMF.normalize p
    (by
      have hmass := p.tsum_run_some_eq_one_sub
      rw [hfail, tsub_zero] at hmass
      have hmass' : (∑' value, p value) = 1 := by
        simpa only [SPMF.apply_eq_toPMF_some] using hmass
      rw [hmass']
      exact one_ne_zero)
    (by
      have hmass := p.tsum_run_some_eq_one_sub
      rw [hfail, tsub_zero] at hmass
      have hmass' : (∑' value, p value) = 1 := by
        simpa only [SPMF.apply_eq_toPMF_some] using hmass
      rw [hmass']
      exact one_ne_top)

@[simp]
theorem generalSuccessPMF_apply
    (p : SPMF α) (hfail : p.toPMF none = 0) (value : α) :
    generalSuccessPMF p hfail value = p value := by
  have hmass := p.tsum_run_some_eq_one_sub
  rw [hfail, tsub_zero] at hmass
  have hmass' : (∑' candidate, p candidate) = 1 := by
    simpa only [SPMF.apply_eq_toPMF_some] using hmass
  rw [generalSuccessPMF, PMF.normalize_apply, hmass']
  simp

theorem liftM_generalSuccessPMF_eq
    (p : SPMF α) (hfail : p.toPMF none = 0) :
    (liftM (generalSuccessPMF p hfail) : SPMF α) = p := by
  apply SPMF.ext
  intro value
  simp

theorem generalSuccessPMF_map_eq_of_spmf_map_eq
    (left : SPMF α) (right : SPMF β)
    (f : α → γ) (g : β → γ)
    (hleft : left.toPMF none = 0) (hright : right.toPMF none = 0)
    (hmap : f <$> left = g <$> right) :
    (generalSuccessPMF left hleft).map f =
      (generalSuccessPMF right hright).map g := by
  have hlift :
      (liftM ((generalSuccessPMF left hleft).map f) : SPMF γ) =
        f <$> left := by
    calc
      (liftM ((generalSuccessPMF left hleft).map f) : SPMF γ) =
          f <$> (liftM (generalSuccessPMF left hleft) : SPMF α) :=
        liftM_map f (generalSuccessPMF left hleft)
      _ = f <$> left := by rw [liftM_generalSuccessPMF_eq]
  have hrightLift :
      (liftM ((generalSuccessPMF right hright).map g) : SPMF γ) =
        g <$> right := by
    calc
      (liftM ((generalSuccessPMF right hright).map g) : SPMF γ) =
          g <$> (liftM (generalSuccessPMF right hright) : SPMF β) :=
        liftM_map g (generalSuccessPMF right hright)
      _ = g <$> right := by rw [liftM_generalSuccessPMF_eq]
  have hspmf :
      (liftM ((generalSuccessPMF left hleft).map f) : SPMF γ) =
        liftM ((generalSuccessPMF right hright).map g) :=
    hlift.trans (hmap.trans hrightLift.symm)
  apply PMF.ext
  intro value
  have hpoint :
      (liftM ((generalSuccessPMF left hleft).map f) : SPMF γ) value =
        (liftM ((generalSuccessPMF right hright).map g) : SPMF γ) value := by
    rw [hspmf]
  simpa using hpoint

noncomputable def generalMarginalCoupling
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (f : α → γ) (g : β → γ)
    (hmap : 𝒟[f <$> oa] = 𝒟[g <$> ob]) : SPMF (α × β) :=
  let left := 𝒟[oa]
  let right := 𝒟[ob]
  let hleft : left.toPMF none = 0 := probFailure_eq_zero (mx := oa)
  let hright : right.toPMF none = 0 := probFailure_eq_zero (mx := ob)
  let hPMFMap : (generalSuccessPMF left hleft).map f =
      (generalSuccessPMF right hright).map g :=
    generalSuccessPMF_map_eq_of_spmf_map_eq left right f g hleft hright (by
      simpa [evalDist_map] using hmap)
  liftM (generalFiberCoupling
    (generalSuccessPMF left hleft) (generalSuccessPMF right hright)
    f g hPMFMap)

theorem generalMarginalCoupling_isCoupling
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (f : α → γ) (g : β → γ)
    (hmap : 𝒟[f <$> oa] = 𝒟[g <$> ob]) :
    SPMF.IsCoupling (generalMarginalCoupling oa ob f g hmap) 𝒟[oa] 𝒟[ob] := by
  let left := 𝒟[oa]
  let right := 𝒟[ob]
  let hleft : left.toPMF none = 0 := probFailure_eq_zero (mx := oa)
  let hright : right.toPMF none = 0 := probFailure_eq_zero (mx := ob)
  let hPMFMap : (generalSuccessPMF left hleft).map f =
      (generalSuccessPMF right hright).map g :=
    generalSuccessPMF_map_eq_of_spmf_map_eq left right f g hleft hright (by
      simpa [evalDist_map] using hmap)
  have hcoupling := generalFiberCoupling_isCoupling
    (generalSuccessPMF left hleft) (generalSuccessPMF right hright) f g hPMFMap
  constructor
  · change Prod.fst <$> (liftM (generalFiberCoupling
        (generalSuccessPMF left hleft) (generalSuccessPMF right hright)
        f g hPMFMap) : SPMF (α × β)) = left
    rw [← liftM_map]
    have hfst : Prod.fst <$> (generalFiberCoupling
        (generalSuccessPMF left hleft) (generalSuccessPMF right hright)
        f g hPMFMap) = generalSuccessPMF left hleft := hcoupling.map_fst
    rw [hfst, liftM_generalSuccessPMF_eq]
  · change Prod.snd <$> (liftM (generalFiberCoupling
        (generalSuccessPMF left hleft) (generalSuccessPMF right hright)
        f g hPMFMap) : SPMF (α × β)) = right
    rw [← liftM_map]
    have hsnd : Prod.snd <$> (generalFiberCoupling
        (generalSuccessPMF left hleft) (generalSuccessPMF right hright)
        f g hPMFMap) = generalSuccessPMF right hright := hcoupling.map_snd
    rw [hsnd, liftM_generalSuccessPMF_eq]

theorem generalMarginalCoupling_support_eq
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (f : α → γ) (g : β → γ)
    (hmap : 𝒟[f <$> oa] = 𝒟[g <$> ob])
    (pair : α × β)
    (hpair : pair ∈ support (generalMarginalCoupling oa ob f g hmap)) :
    f pair.1 = g pair.2 := by
  let left := 𝒟[oa]
  let right := 𝒟[ob]
  let hleft : left.toPMF none = 0 := probFailure_eq_zero (mx := oa)
  let hright : right.toPMF none = 0 := probFailure_eq_zero (mx := ob)
  let hPMFMap : (generalSuccessPMF left hleft).map f =
      (generalSuccessPMF right hright).map g :=
    generalSuccessPMF_map_eq_of_spmf_map_eq left right f g hleft hright (by
      simpa [evalDist_map] using hmap)
  change pair ∈ support (liftM (generalFiberCoupling
    (generalSuccessPMF left hleft) (generalSuccessPMF right hright)
    f g hPMFMap)) at hpair
  have hpair' : (generalFiberCoupling
      (generalSuccessPMF left hleft) (generalSuccessPMF right hright)
      f g hPMFMap) pair ≠ 0 := by
    have hne : (liftM (generalFiberCoupling
        (generalSuccessPMF left hleft) (generalSuccessPMF right hright)
        f g hPMFMap) : SPMF (α × β)) pair ≠ 0 :=
      (SPMF.mem_support_iff _ _).mp hpair
    simpa using hne
  rw [generalFiberCoupling_apply] at hpair'
  unfold generalFiberCouplingWeight at hpair'
  split at hpair'
  · assumption
  · exact (hpair' rfl).elim

theorem generalMarginalCoupling_support_marginals
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (f : α → γ) (g : β → γ)
    (hmap : 𝒟[f <$> oa] = 𝒟[g <$> ob])
    (pair : α × β)
    (hpair : pair ∈ support (generalMarginalCoupling oa ob f g hmap)) :
    pair.1 ∈ support oa ∧ pair.2 ∈ support ob := by
  have hcoupling := generalMarginalCoupling_isCoupling oa ob f g hmap
  constructor
  · have hmapped : pair.1 ∈ support
        (Prod.fst <$> generalMarginalCoupling oa ob f g hmap) := by
      rw [support_map]
      exact ⟨pair, hpair, rfl⟩
    rw [hcoupling.map_fst] at hmapped
    rw [mem_support_iff_evalDist_apply_ne_zero]
    exact (SPMF.mem_support_iff _ _).mp hmapped
  · have hmapped : pair.2 ∈ support
        (Prod.snd <$> generalMarginalCoupling oa ob f g hmap) := by
      rw [support_map]
      exact ⟨pair, hpair, rfl⟩
    rw [hcoupling.map_snd] at hmapped
    rw [mem_support_iff_evalDist_apply_ne_zero]
    exact (SPMF.mem_support_iff _ _).mp hmapped

theorem relTriple_of_evalDist_map_eq_general
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (f : α → γ) (g : β → γ)
    (hmap : 𝒟[f <$> oa] = 𝒟[g <$> ob]) :
    RelTriple oa ob (fun left right => f left = g right) := by
  rw [relTriple_iff_relWP]
  refine ⟨⟨generalMarginalCoupling oa ob f g hmap,
    generalMarginalCoupling_isCoupling oa ob f g hmap⟩, ?_⟩
  intro pair hpair
  exact generalMarginalCoupling_support_eq oa ob f g hmap pair hpair

theorem relTriple_of_evalDist_map_eq_with_support_general
    (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (f : α → γ) (g : β → γ)
    (hmap : 𝒟[f <$> oa] = 𝒟[g <$> ob]) :
    RelTriple oa ob (fun left right =>
      f left = g right ∧ left ∈ support oa ∧ right ∈ support ob) := by
  rw [relTriple_iff_relWP]
  refine ⟨⟨generalMarginalCoupling oa ob f g hmap,
    generalMarginalCoupling_isCoupling oa ob f g hmap⟩, ?_⟩
  intro pair hpair
  exact ⟨generalMarginalCoupling_support_eq oa ob f g hmap pair hpair,
    generalMarginalCoupling_support_marginals oa ob f g hmap pair hpair⟩

theorem relTriple_trans_exists
    {ι₃ : Type} {spec₃ : OracleSpec ι₃} [IsUniformSpec spec₃]
    {δ : Type} {oc : OracleComp spec₃ δ}
    {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : α → β → Prop} {S : β → δ → Prop}
    (hab : RelTriple oa ob R) (hbc : RelTriple ob oc S) :
    RelTriple oa oc (fun a c => ∃ b, R a b ∧ S b c) := by
  classical
  letI : DecidableEq β := Classical.decEq β
  rw [relTriple_iff_relWP] at hab hbc ⊢
  obtain ⟨cab, hR⟩ := hab
  obtain ⟨cbc, hS⟩ := hbc
  have hcabFail : cab.1.toPMF none = 0 := by
    have hmap := cab.2.map_fst
    rw [SPMF.fmap_eq_map] at hmap
    change PMF.map (Option.map Prod.fst) cab.1.toPMF =
      (evalDist oa).toPMF at hmap
    have h := congrArg (fun p : PMF (Option α) => p none) hmap
    rw [PMF.map_apply] at h
    simpa using h.trans (probFailure_eq_zero (mx := oa))
  have hcbcFail : cbc.1.toPMF none = 0 := by
    have hmap := cbc.2.map_fst
    rw [SPMF.fmap_eq_map] at hmap
    change PMF.map (Option.map Prod.fst) cbc.1.toPMF =
      (evalDist ob).toPMF at hmap
    have h := congrArg (fun p : PMF (Option β) => p none) hmap
    rw [PMF.map_apply] at h
    simpa using h.trans (probFailure_eq_zero (mx := ob))
  let p := generalSuccessPMF cab.1 hcabFail
  let q := generalSuccessPMF cbc.1 hcbcFail
  have hmiddle : p.map Prod.snd = q.map Prod.fst := by
    apply generalSuccessPMF_map_eq_of_spmf_map_eq
    exact cab.2.map_snd.trans cbc.2.map_fst.symm
  let d := generalFiberCoupling p q Prod.snd Prod.fst hmiddle
  let project : (α × β) × (β × δ) → α × δ :=
    fun pair => (pair.1.1, pair.2.2)
  let c : SPMF (α × δ) := liftM (d.map project)
  have hd : PMF.IsCoupling d p q := by
    simpa [d] using generalFiberCoupling_isCoupling p q Prod.snd Prod.fst hmiddle
  refine ⟨⟨c, ?_, ?_⟩, ?_⟩
  · dsimp only [c]
    rw [← liftM_map]
    change liftM ((d.map project).map Prod.fst) = _
    rw [PMF.map_comp]
    change liftM (d.map (Prod.fst ∘ Prod.fst)) = _
    rw [← PMF.map_comp, hd.map_fst]
    change liftM ((generalSuccessPMF cab.1 hcabFail).map Prod.fst) = _
    calc
      liftM ((generalSuccessPMF cab.1 hcabFail).map Prod.fst) =
          Prod.fst <$> (liftM (generalSuccessPMF cab.1 hcabFail) : SPMF (α × β)) :=
        liftM_map Prod.fst (generalSuccessPMF cab.1 hcabFail)
      _ = Prod.fst <$> cab.1 := by rw [liftM_generalSuccessPMF_eq]
      _ = evalDist oa := cab.2.map_fst
  · dsimp only [c]
    rw [← liftM_map]
    change liftM ((d.map project).map Prod.snd) = _
    rw [PMF.map_comp]
    change liftM (d.map (Prod.snd ∘ Prod.snd)) = _
    rw [← PMF.map_comp, hd.map_snd]
    change liftM ((generalSuccessPMF cbc.1 hcbcFail).map Prod.snd) = _
    calc
      liftM ((generalSuccessPMF cbc.1 hcbcFail).map Prod.snd) =
          Prod.snd <$> (liftM (generalSuccessPMF cbc.1 hcbcFail) : SPMF (β × δ)) :=
        liftM_map Prod.snd (generalSuccessPMF cbc.1 hcbcFail)
      _ = Prod.snd <$> cbc.1 := by rw [liftM_generalSuccessPMF_eq]
      _ = evalDist oc := cbc.2.map_snd
  · intro pair hpair
    change pair ∈ support (liftM (d.map project) : SPMF (α × δ)) at hpair
    change pair ∈ (liftM (d.map project) : SPMF (α × δ)).support at hpair
    rw [SPMF.support_liftM, PMF.mem_support_map_iff] at hpair
    obtain ⟨z, hz, hproject⟩ := hpair
    have hweight : generalFiberCouplingWeight p q Prod.snd Prod.fst z ≠ 0 := by
      simpa [d, generalFiberCoupling_apply] using
        (PMF.mem_support_iff d z).1 hz
    have heq : z.1.2 = z.2.1 := by
      unfold generalFiberCouplingWeight at hweight
      split at hweight
      · assumption
      · exact (hweight rfl).elim
    have hp : p z.1 ≠ 0 := by
      intro hpzero
      apply hweight
      simp [generalFiberCouplingWeight, heq, hpzero]
    have hq : q z.2 ≠ 0 := by
      intro hqzero
      apply hweight
      simp [generalFiberCouplingWeight, heq, hqzero]
    have hzLeft : z.1 ∈ support cab.1 := by
      change z.1 ∈ SPMF.support cab.1
      apply (SPMF.mem_support_iff cab.1 z.1).2
      simpa [p] using hp
    have hzRight : z.2 ∈ support cbc.1 := by
      change z.2 ∈ SPMF.support cbc.1
      apply (SPMF.mem_support_iff cbc.1 z.2).2
      simpa [q] using hq
    have hleft := hR z.1 hzLeft
    have hright := hS z.2 hzRight
    obtain ⟨rfl, rfl⟩ := hproject
    exact ⟨z.1.2, hleft, heq ▸ hright⟩

end GeneralRelTriple


end XmssSecurity
