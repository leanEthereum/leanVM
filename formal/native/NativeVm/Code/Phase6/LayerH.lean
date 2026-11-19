module

public import NativeVm.Code.Phase6.LayerG
public import NativeVm.Code.Phase6.LayerE

/-!
# A layer's third part: the second check, `β`, the next claim

`L3C`: the bit-position equality weights, their `dot` with the claim's weights, the second check,
`β` (`eBeta`), the next weights before the linear map, `linear_transpose`, the next value
(`l3_refines`, against `l3M`): the scratch then holds the next claim (`ClaimIn`).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm NativeVm.Model NativeVm.Code LeanVM.Parameters Finset
open NativeVm.Transcript (wd wdisp Env)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-- The value the second check compares with the sumcheck's claim. -/
def y2 (c : KeccakClaimW) (x : EW) (lp tv : Array EW) : EW :=
  dot ((eqKernel lp).extract 0 LeanVM.Protocol.Verifier.keccakBits) c.weights *
    (sumE (keccakInstanceWeights x) * tv.getD 0 0 +
      (sumE (keccakInstanceWeights x) + tv.getD 1 0) * tv.getD 2 0)

/-- The next claim. -/
def nextClaim (x : EW) (pt lp tv : Array EW) (beta : EW) : KeccakClaimW :=
  ⟨tv.getD 0 0 + beta * (tv.getD 1 0 + beta * tv.getD 2 0), keccakInstanceWeights x, pt,
    keccakLinearTranspose (w2Arr (eqKernel lp) beta)⟩

/-- The layer's third part. -/
def l3M (c : KeccakClaimW) (x : EW) (pt : Array EW) (r2 : Array EW × EW) (tv : Array EW) :
    VM KeccakClaimW :=
  Model.require (y2 c x r2.1 tv == r2.2) >>= fun _ ↦ Model.sampleChallenge >>= fun beta ↦
    pure (nextClaim x pt r2.1 tv beta)

/-- Its code. -/
def L3C : List Stmt := [blk eqC, blk (dotC :: stEl eVal), blk (blk kt0C :: stEl eMsg), blk chk2C,
  smpEl eBeta, blk [I (.movi .r14 0), tab eW2 (.imm (Int64.ofNat 1600)) w2Val], blk lintC,
  blk newVC]

theorem y2_toE {c : KeccakClaimW} {x : EW} {lp tv : Array EW} (hw : c.weights.size = 1600)
    (hlp : lp.size = 11) :
    (y2 c x lp tv).toE = (∑ i ∈ range 1600, ((eqKernel lp).getD i 0).toE * (c.weights.getD i 0).toE) *
      ((∑ i ∈ range 16, ((keccakInstanceWeights x).getD i 0).toE) * (tv.getD 0 0).toE +
        ((∑ i ∈ range 16, ((keccakInstanceWeights x).getD i 0).toE) + (tv.getD 1 0).toE) *
          (tv.getD 2 0).toE) := by
  have hs : ((eqKernel lp).extract 0 LeanVM.Protocol.Verifier.keccakBits).size = 1600 := by
    rw [Array.size_extract, eqKernel_size, hlp]; rfl
  rw [y2, NativeVm.Equiv.EW.toE_mul, toE_dot_range, hs, hw, Nat.min_self]
  simp only [NativeVm.Equiv.EW.toE_add, NativeVm.Equiv.EW.toE_mul]
  rw [toE_sumE_range, instanceWeights_size]
  have he : ∀ i ∈ range 1600,
      (((eqKernel lp).extract 0 LeanVM.Protocol.Verifier.keccakBits).getD i 0).toE *
        (c.weights.getD i 0).toE = ((eqKernel lp).getD i 0).toE * (c.weights.getD i 0).toE :=
    fun i hi ↦ by
      have hi := mem_range.1 hi
      have hk : i < (eqKernel lp).size := by rw [eqKernel_size, hlp]; omega
      have e : ((eqKernel lp).extract 0 LeanVM.Protocol.Verifier.keccakBits).getD i 0 =
          (eqKernel lp).getD i 0 := by
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract, Nat.zero_add]
        split
        · rfl
        · simp [LeanVM.Protocol.Verifier.keccakBits] at *; omega
      rw [e]
  rw [sum_congr rfl he]

variable (env inp s0)

/-- **The layer's third part.** -/
theorem l3_refines (hin : Inputs env inp s0.mem) {c : KeccakClaimW}
    {r : EW × (Array EW × EW) × (Array EW × EW) × Array EW} (g0 g : Nat → EW) (hcn : Cn g0)
    (hfr : LFr g g0) (hpts : c.point.size < 32) (hws : c.weights.size = 1600)
    (hp : L2Post g c r) :
    Refines (St env s0 g) (blk L3C) (l3M c r.1 r.2.1.1 r.2.2.1 r.2.2.2)
      (fun c' t s ↦ ∃ g', St env s0 g' t s ∧ LFr g' g0 ∧ ClaimIn g' c' ∧
        c'.point.size = c.point.size ∧ c'.mu.size = 16) (Kept env rs6 s0) := by
  obtain ⟨x, ⟨pt, v1⟩, ⟨lp, v2⟩, tv⟩ := r
  have hlps := hp.lpSize
  simp only at hlps
  unfold L3C l3M
  set g1 := ovr (Function.update (Function.update g eKn (EW.ofK (11 : Nat).toUInt64)) eKd
    (EW.ofK (0 : Nat).toUInt64)) eEq 2048 fun m ↦ (eqKernel lp).getD m 0 with hg1
  have k1 : ∀ i, i ≠ eKn → i ≠ eKd → ¬ (eEq ≤ i ∧ i < eEq + 2048) → g1 i = g i := fun i h1 h2 h3 ↦ by
    rw [hg1, ovr_out (by omega), Function.update_of_ne h2, Function.update_of_ne h1]
  have heq1 : ∀ i < 2048, g1 (eEq + i) = (eqKernel lp).getD i 0 := fun i hi ↦ by
    rw [hg1, ovr_in (by omega) (by omega), Nat.add_sub_cancel_left]
  set g2 := Function.update g1 eVal
    (EW.ofE (∑ i ∈ range 1600, (g1 (eEq + i)).toE * (g1 (eW + i)).toE)) with hg2
  set g3 := Function.update g2 eMsg (EW.ofE ((g2 eKappa).toE * (g2 eT).toE)) with hg3
  have k3 : ∀ i, i ≠ eKn → i ≠ eKd → ¬ (eEq ≤ i ∧ i < eEq + 2048) → i ≠ eVal → i ≠ eMsg →
      g3 i = g i := fun i h1 h2 h3 h4 h5 ↦ by
    rw [hg3, Function.update_of_ne h5, hg2, Function.update_of_ne h4, k1 i h1 h2 h3]
  have hy : (y2 c x lp tv).toE = (g3 eVal).toE * ((g3 eMsg).toE + ((g3 eKappa).toE +
      (g3 (eT + 1)).toE) * (g3 (eT + 2)).toE) := by
    have eV : (g3 eVal).toE = ∑ i ∈ range 1600, ((eqKernel lp).getD i 0).toE *
        (c.weights.getD i 0).toE := by
      rw [hg3, Function.update_of_ne (by p6_ne), hg2, Function.update_self,
        NativeVm.Equiv.EW.toE_ofE]
      refine sum_congr rfl fun i hi ↦ ?_
      have hi := mem_range.1 hi
      rw [heq1 i (by omega), k1 (eW + i) (by p6_ne) (by p6_ne) (by p6_omega), hp.w i hi]
    have eK : g3 eKappa = g eKappa := k3 _ (by p6_ne) (by p6_ne) (by p6_omega) (by p6_ne) (by p6_ne)
    have eT0 : g3 eT = tv.getD 0 0 :=
      (k3 _ (by p6_ne) (by p6_ne) (by p6_omega) (by p6_ne) (by p6_ne)).trans (hp.tv 0 (by omega))
    have eT1 : g3 (eT + 1) = tv.getD 1 0 :=
      (k3 _ (by p6_ne) (by p6_ne) (by p6_omega) (by p6_ne) (by p6_ne)).trans (hp.tv 1 (by omega))
    have eT2 : g3 (eT + 2) = tv.getD 2 0 :=
      (k3 _ (by p6_ne) (by p6_ne) (by p6_omega) (by p6_ne) (by p6_ne)).trans (hp.tv 2 (by omega))
    have eM : (g3 eMsg).toE = (g eKappa).toE * (tv.getD 0 0).toE := by
      have e2K : g2 eKappa = g eKappa := by
        rw [hg2, Function.update_of_ne (by p6_ne), k1 _ (by p6_ne) (by p6_ne) (by p6_omega)]
      have e2T : g2 eT = tv.getD 0 0 := by
        rw [hg2, Function.update_of_ne (by p6_ne), k1 _ (by p6_ne) (by p6_ne) (by p6_omega)]
        exact hp.tv 0 (by omega)
      rw [hg3, Function.update_self, NativeVm.Equiv.EW.toE_ofE, e2K, e2T]
    rw [y2_toE hws hlps, eV, eM, eK, eT1, eT2, hp.kappa]
  have hsc3 : g3 eSC = v2 := by
    rw [k3 _ (by p6_ne) (by p6_ne) (by p6_omega) (by p6_ne) (by p6_ne)]; exact hp.sc
  refine Pure6.then (pure_eq hin (lp := lp) hlps hp.lp) (Pure6.then (pure_dot hin)
    (Pure6.then (pure_kt0 hin) ?_))
  rw [← hsc3]
  refine Refines.blk_cons (chk2_refines hin hy) fun _ ↦ ?_
  refine Refines.blk_cons (smpEl_refines env inp s0 hin (o := eBeta) (by p6_omega) g3) fun beta ↦ ?_
  set g4 := Function.update g3 eBeta beta with hg4
  have k4 : ∀ i, i ≠ eBeta → g4 i = g3 i := fun i hi ↦ Function.update_of_ne hi _ _
  have cn4 : Cn g4 := (hfr.cn hcn).congr fun i h1 h2 ↦
    (k4 i (by p6_omega)).trans (k3 i (by p6_omega) (by p6_omega) (by p6_omega) (by p6_omega)
      (by p6_omega))
  have hb4 : g4 eBeta = beta := Function.update_self ..
  set g5 := ovr g4 eW2 1600 fun m ↦ (w2Arr (eqKernel lp) (g4 eBeta)).getD m 0 with hg5
  have k5 : ∀ i, ¬ (eW2 ≤ i ∧ i < eW2 + 1600) → g5 i = g4 i := fun i hi ↦ ovr_out (by omega)
  have cn5 : Cn g5 := cn4.congr fun i h1 h2 ↦ k5 i (by p6_omega)
  have hW5 : ∀ i < 1600, g5 (eW2 + i) = (w2Arr (eqKernel lp) beta).getD i 0 := fun i hi ↦ by
    rw [hg5, ovr_in (by omega) (by omega), Nat.add_sub_cancel_left, hb4]
  obtain ⟨g6, p6, k6, hw6⟩ := pure_lt hin cn5 hW5
  have p5 := pure_w2 hin cn4 (eq := eqKernel lp) fun i hi ↦ by
    rw [k4 _ (by p6_omega), hg3, Function.update_of_ne (by p6_omega), hg2,
      Function.update_of_ne (by p6_omega), heq1 i hi]
  set g7 := Function.update g6 eCV (g6 eT + g6 eBeta * (g6 (eT + 1) + g6 eBeta * g6 (eT + 2)))
    with hg7
  have k6' : ∀ i, ¬ (eG ≤ i ∧ i < eCol + 320) → ¬ (eW ≤ i ∧ i < eW + 1600) →
      ¬ (eW2 ≤ i ∧ i < eW2 + 1600) → i ≠ eBeta → g6 i = g3 i := fun i h1 h2 h3 h4 ↦
    (k6 i h1 h2).trans ((k5 i h3).trans (k4 i h4))
  have k63 : ∀ i, i < 32 ∨ (48 ≤ i ∧ i < 200) → i ≠ eBeta → g6 i = g3 i := fun i h h4 ↦
    k6' i (by p6_omega) (by p6_omega) (by p6_omega) h4
  have hb6 : g6 eBeta = beta := (k6 _ (by p6_omega) (by p6_omega)).trans
    ((k5 _ (by p6_omega)).trans hb4)
  have hT : ∀ i < 3, g6 (eT + i) = tv.getD i 0 := fun i hi ↦ by
    rw [k63 _ (by p6_omega) (by p6_omega), k3 _ (by p6_ne) (by p6_ne) (by p6_omega) (by p6_omega)
      (by p6_omega)]
    exact hp.tv i hi
  have hv7 : g7 eCV = tv.getD 0 0 + beta * (tv.getD 1 0 + beta * tv.getD 2 0) := by
    rw [hg7, Function.update_self, hb6, show eT = eT + 0 from rfl, hT 0 (by omega), hT 1 (by omega),
      hT 2 (by omega)]
  have k7 : ∀ i, i ≠ eCV → g7 i = g6 i := fun i hi ↦ Function.update_of_ne hi _ _
  have hiw := instanceWeights_size x
  have hpt := hp.ptSize
  simp only at hpt
  have hci : ClaimIn g7 (nextClaim x pt lp tv beta) := by
    refine ⟨hv7, by simp only [nextClaim]; rw [hiw], ?_, fun i hi ↦ ?_,
      by simp only [nextClaim]; rw [hpt]; exact hpts, ?_, fun i hi ↦ ?_, linearTranspose_size _,
      fun i hi ↦ ?_⟩ <;> (try simp only [nextClaim] at hi) <;> simp only [nextClaim]
    · rw [hiw, k7 _ (by p6_ne), k63 _ (by p6_omega) (by p6_ne),
        k3 _ (by p6_ne) (by p6_ne) (by p6_omega) (by p6_ne) (by p6_ne)]
      exact hp.muN
    · rw [hiw] at hi
      rw [k7 _ (by p6_omega), k63 _ (by p6_omega) (by p6_omega),
        k3 _ (by p6_omega) (by p6_omega) (by p6_omega) (by p6_omega) (by p6_omega)]
      exact hp.mu i hi
    · rw [hpt, k7 _ (by p6_ne), k63 _ (by p6_omega) (by p6_ne),
        k3 _ (by p6_ne) (by p6_ne) (by p6_omega) (by p6_ne) (by p6_ne)]
      exact hp.ptN
    · rw [hpt] at hi
      rw [k7 _ (by p6_omega), k63 _ (by p6_omega) (by p6_omega),
        k3 _ (by p6_omega) (by p6_omega) (by p6_omega) (by p6_omega) (by p6_omega)]
      exact hp.pt i hi
    · rw [k7 _ (by p6_omega), hw6 i hi]
  have hfr7 : LFr g7 g0 := fun i hi ↦ by
    unfold LW at hi
    rw [k7 i (by p6_omega), k6' i (by p6_omega) (by p6_omega) (by p6_omega) (by p6_omega),
      k3 i (by p6_omega) (by p6_omega) (by p6_omega) (by p6_omega) (by p6_omega),
      hfr i (by unfold LW; p6_omega)]
  exact Pure6.then p5 (Pure6.then p6 (Pure6.then (pure_newV hin (g := g6)) (Refines.skip
    fun t s h ↦ ⟨g7, h, hfr7, hci, hpt, hiw⟩)))

end NativeVm.Code.P6
