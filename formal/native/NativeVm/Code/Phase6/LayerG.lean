module

public import NativeVm.Code.Phase6.LayerF

/-!
# A layer's second part: `s`, the instance weights, both sumchecks, `t`

`L2C`: the grind, the challenge `s` (`eS`), its powers, the instance weights
`keccakInstanceWeights s` (`eMu`, count `16`), `κ` (`eKappa`), the claim `polyEval product s`,
the sumcheck over the claim's point (its challenges over the point at `ePt`), the plain sumcheck
over the `keccakLocalBits` bit positions (`eLp`, its claim at `eSC`), the three values `t` (`eT`)
(`l2_refines`, against `l2M`).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm NativeVm.Model NativeVm.Code LeanVM.Parameters Finset
open NativeVm.Transcript (wd wdisp Env)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-- The layer's second part. -/
def l2M (c : KeccakClaimW) (product : Array EW) :
    VM (EW × (Array EW × EW) × (Array EW × EW) × Array EW) :=
  Model.grind 3 >>= fun _ ↦ Model.sampleChallenge >>= fun x ↦
    Model.sumcheck (polyEval product x) 3 (c.point.map some) >>= fun r1 ↦
      Model.sumcheckPlain r1.2 4 11 >>= fun r2 ↦ Model.readScalars 3 >>= fun tv ↦
        pure (x, r1, r2, tv)

/-- Its code. -/
def L2C : List Stmt := [grind3, smpEl eS, blk (powEl ePow 24 eS), blk muC,
  blk (sumMuC :: stEl eKappa), blk (pevC :: stEl eSC), scE 3 ePt, scP 4 eLp 11, rdN eT 3]

/-- What the second part leaves: the claim's bit weights kept, the instance weights at `s` and
their sum, the challenges of both sumchecks, the claim left, `t`. -/
structure L2Post (g : Nat → EW) (c : KeccakClaimW)
    (r : EW × (Array EW × EW) × (Array EW × EW) × Array EW) : Prop where
  w : ∀ i < 1600, g (eW + i) = c.weights.getD i 0
  mu : ∀ i < 16, g (eMu + i) = (keccakInstanceWeights r.1).getD i 0
  muN : g eMuN = EW.ofK (16 : Nat).toUInt64
  kappa : (g eKappa).toE = ∑ i ∈ range 16, ((keccakInstanceWeights r.1).getD i 0).toE
  ptSize : r.2.1.1.size = c.point.size
  pt : ∀ i < c.point.size, g (ePt + i) = r.2.1.1.getD i 0
  ptN : g ePtN = EW.ofK c.point.size.toUInt64
  lpSize : r.2.2.1.1.size = 11
  lp : ∀ i < 11, g (eLp + i) = r.2.2.1.1.getD i 0
  sc : g eSC = r.2.2.1.2
  tSize : r.2.2.2.size = 3
  tv : ∀ i < 3, g (eT + i) = r.2.2.2.getD i 0

/-- A precondition that holds some scratch with a fact. -/
theorem Refines.exSt {α : Type} {P : (Nat → EW) → Prop} {c : Stmt} {m : VM α}
    {Q : α → TState → QState → Prop} {E : QState → Prop}
    (h : ∀ g, P g → Refines (St env s0 g) c m Q E) :
    Refines (fun t s ↦ ∃ g, St env s0 g t s ∧ P g) c m Q E :=
  fun t s ⟨g, hs, hp⟩ ↦ h g hp t s hs

variable (env inp s0)

/-- **The layer's second part.** -/
theorem l2_refines (hin : Inputs env inp s0.mem) {c : KeccakClaimW} {product : Array EW}
    (g0 g : Nat → EW) (hcn : Cn g0) (hfr : LFr g g0) (hcl : ClaimIn g c)
    (hps : product.size = 47) (hp : ∀ i < 47, g (eProd + i) = product.getD i 0) :
    Refines (St env s0 g) (blk L2C) (l2M c product)
      (fun r t s ↦ ∃ g', St env s0 g' t s ∧ LFr g' g0 ∧ L2Post g' c r) (Kept env rs6 s0) := by
  have hpts := hcl.ptSize
  unfold L2C l2M
  refine Refines.blk_cons (grind3_refines env inp s0 hin g) fun _ ↦ ?_
  refine Refines.blk_cons (smpEl_refines env inp s0 hin (o := eS) (by p6_omega) g) fun x ↦ ?_
  set g2 := Function.update g eS x with hg2
  have k2 : ∀ i, i ≠ eS → g2 i = g i := fun i hi ↦ Function.update_of_ne hi _ _
  set g3 := ovr g2 ePow 24 fun b ↦ EW.ofE ((g2 eS).toE ^ b) with hg3
  have k3 : ∀ i, ¬ (ePow ≤ i ∧ i < ePow + 24) → g3 i = g2 i := fun i hi ↦ ovr_out (by omega)
  have cn3 : Cn g3 := (hfr.cn hcn).congr fun i h1 h2 ↦
    (k3 i (by p6_omega)).trans (k2 i (by p6_omega))
  have hpow : ∀ b < 24, (g3 (ePow + b)).toE = x.toE ^ b := fun b hb ↦ by
    rw [hg3, ovr_in (by omega) (by omega), Nat.add_sub_cancel_left, NativeVm.Equiv.EW.toE_ofE, hg2,
      Function.update_self]
  set g4 := Function.update (ovr g3 eMu 16 fun e ↦ (keccakInstanceWeights x).getD e 0) eMuN
    (EW.ofK (16 : Nat).toUInt64) with hg4
  have k4 : ∀ i, i ≠ eMuN → ¬ (eMu ≤ i ∧ i < eMu + 16) → g4 i = g3 i := fun i h1 h2 ↦ by
    rw [hg4, Function.update_of_ne h1, ovr_out (by omega)]
  have hmu4 : ∀ i < 16, g4 (eMu + i) = (keccakInstanceWeights x).getD i 0 := fun i hi ↦ by
    rw [hg4, Function.update_of_ne (by p6_omega), ovr_in (by omega) (by omega),
      Nat.add_sub_cancel_left]
  have hmuN4 : g4 eMuN = EW.ofK (16 : Nat).toUInt64 := by rw [hg4, Function.update_self]
  set g5 := Function.update g4 eKappa (EW.ofE (∑ i ∈ range 16, (g4 (eMu + i)).toE)) with hg5
  have k5 : ∀ i, i ≠ eKappa → g5 i = g4 i := fun i hi ↦ Function.update_of_ne hi _ _
  set g6 := Function.update g5 eSC (EW.ofE (LeanVM.Protocol.Verifier.polyEval (vals g5 eProd 47)
    (g5 eS).toE)) with hg6
  have k6 : ∀ i, i ≠ eSC → g6 i = g5 i := fun i hi ↦ Function.update_of_ne hi _ _
  -- from `g` to `g6`
  have k06 : ∀ i, ¬ (i = eS ∨ (ePow ≤ i ∧ i < ePow + 24) ∨ i = eMuN ∨ (eMu ≤ i ∧ i < eMu + 16) ∨
      i = eKappa ∨ i = eSC) → g6 i = g i := fun i hi ↦ by
    simp only [not_or] at hi
    rw [k6 i hi.2.2.2.2.2, k5 i hi.2.2.2.2.1, k4 i hi.2.2.1 hi.2.2.2.1, k3 i hi.2.1, k2 i hi.1]
  have hS5 : g5 eS = x := by
    rw [k5 _ (by p6_ne), k4 _ (by p6_ne) (by p6_omega), k3 _ (by p6_omega), hg2,
      Function.update_self]
  have hsc6 : g6 eSC = polyEval product x := by
    rw [hg6, Function.update_self, hS5]
    apply NativeVm.Equiv.EW.toE_injective
    rw [NativeVm.Equiv.EW.toE_ofE, NativeVm.Equiv.toE_polyEval, ← hps]
    congr 1
    exact vals_eq product fun i hi ↦ by
      rw [k5 _ (by p6_omega), k4 _ (by p6_omega) (by p6_omega), k3 _ (by p6_omega),
        k2 _ (by p6_omega), hp i (by omega)]
  have hptN6 : g6 ePtN = EW.ofK c.point.size.toUInt64 := (k06 _ (by p6_omega)).trans hcl.ptN
  have hpt6 : ∀ i < c.point.size, g6 (ePt + i) = c.point.getD i 0 := fun i hi ↦
    (k06 _ (by p6_omega)).trans (hcl.pt i hi)
  have hkap6 : (g6 eKappa).toE = ∑ i ∈ range 16, ((keccakInstanceWeights x).getD i 0).toE := by
    rw [k6 _ (by p6_ne), hg5, Function.update_self, NativeVm.Equiv.EW.toE_ofE]
    exact sum_congr rfl fun i hi ↦ by rw [hmu4 i (mem_range.1 hi)]
  refine Pure6.then (pure_pow hin (o := ePow) (n := 24) (base := eS) (by p6_omega) (by p6_omega))
    (Pure6.then (pure_mu hin cn3 hpow) (Pure6.then (pure_sumMu hin (g := g4) (o := eKappa) hmuN4
    (by omega) (by p6_omega)) (Pure6.then (pure_pev hin (g := g5)) ?_)))
  rw [← hsc6]
  refine Refines.blk_cons (scE_refines env inp s0 hin (c := 3) (by omega) (g6 eSC) c.point
    (by omega) g6 rfl hptN6 hpt6) fun r1 ↦ Refines.intro fun hr1 ↦ Refines.exSt fun g7 ⟨k7, hsc7⟩ ↦ ?_
  have k7' : ∀ i, ¬ Tmp i → ¬ (ePt ≤ i ∧ i < ePt + c.point.size) → g7 i = g6 i := fun i h1 h2 ↦
    (k7 i h1).trans (wrA_out (by rw [hr1]; omega))
  refine Refines.blk_cons (scP_refines env inp s0 hin (c := 4) (co := eLp) (n := 11)
    (np := c.point.size) (by omega) (by p6_omega) (by p6_omega) r1.2 g7 hsc7
    ((k7' _ (by unfold Tmp; p6_ne) (by p6_omega)).trans hptN6))
    fun r2 ↦ Refines.intro fun hr2 ↦ Refines.exSt fun g8 ⟨k8, hsc8⟩ ↦ ?_
  have k8' : ∀ i, ¬ Tmp i → ¬ (eLp ≤ i ∧ i < eLp + 11) → g8 i = g7 i := fun i h1 h2 ↦
    (k8 i h1).trans (wrA_out (by rw [hr2]; omega))
  refine Refines.blk_cons (rdN_refines env inp s0 hin (o := eT) (n := 3) (by p6_omega)
    (by norm_num) g8) fun tv ↦ Refines.intro fun htv ↦ Refines.skip fun t s h ↦ ?_
  have k9 : ∀ i, ¬ (eT ≤ i ∧ i < eT + 3) → wrA g8 eT tv i = g8 i := fun i hi ↦
    wrA_out (by rw [htv]; omega)
  -- the whole frame
  have kall : ∀ i, ¬ Tmp i → ¬ (eT ≤ i ∧ i < eT + 3) → ¬ (eLp ≤ i ∧ i < eLp + 11) →
      ¬ (ePt ≤ i ∧ i < ePt + c.point.size) → wrA g8 eT tv i = g6 i := fun i h1 h2 h3 h4 ↦
    (k9 i h2).trans ((k8' i h1 h3).trans (k7' i h1 h4))
  refine ⟨_, h, fun i hi ↦ ?_, ⟨fun i hi ↦ ?_, fun i hi ↦ ?_, ?_, ?_, hr1, fun i hi ↦ ?_, ?_, hr2,
    fun i hi ↦ ?_, ?_, htv, fun i hi ↦ wrA_in (by omega)⟩⟩
  · unfold LW at hi
    rw [kall i (by unfold Tmp; p6_omega) (by p6_omega) (by p6_omega) (by p6_omega),
      k06 i (by p6_omega), hfr i (by unfold LW; p6_omega)]
  · rw [kall _ (by unfold Tmp; p6_omega) (by p6_omega) (by p6_omega) (by p6_omega),
      k06 _ (by p6_omega), hcl.w i hi]
  · rw [kall _ (by unfold Tmp; p6_omega) (by p6_omega) (by p6_omega) (by p6_omega), k6 _ (by p6_omega),
      k5 _ (by p6_omega), hmu4 i hi]
  · rw [kall _ (by unfold Tmp; p6_ne) (by p6_omega) (by p6_omega) (by p6_omega), k6 _ (by p6_ne),
      k5 _ (by p6_ne), hmuN4]
  · rw [kall _ (by unfold Tmp; p6_ne) (by p6_omega) (by p6_omega) (by p6_omega), hkap6]
  · rw [k9 _ (by p6_omega), k8' _ (by unfold Tmp; p6_omega) (by p6_omega), k7 _ (by unfold Tmp; p6_omega),
      wrA_in (by omega)]
  · rw [kall _ (by unfold Tmp; p6_ne) (by p6_omega) (by p6_omega) (by p6_omega), hptN6]
  · rw [k9 _ (by p6_omega), k8 _ (by unfold Tmp; p6_omega), wrA_in (by omega)]
  · rw [k9 _ (by p6_ne), hsc8]

end NativeVm.Code.P6
