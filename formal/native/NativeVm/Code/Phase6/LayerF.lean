module

public import NativeVm.Code.Phase6.Claim
public import NativeVm.Code.Phase6.LayerC

/-!
# A layer's first part: the product, the first check

`L1C`: the product's `productBits` coefficients read to `eProd`, then `projected`, the segment
weights, `iota` and the instance weights' sum, and the check of `projected + iota · Σ mu` against
the claim's value (`l1_refines`, against `l1M`). A layer writes only `LW`'s elements (`LFr`).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol.Verifier Finset
open NativeVm.Transcript (wd wdisp Env)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-- What a layer starts from: the claim `c`, the tables, `packBits` and the step. -/
structure LPre (g : Nat → EW) (c : KeccakClaimW) (pb step : Nat) : Prop where
  claim : ClaimIn g c
  cn : Cn g
  pbW : g ePB = EW.ofK pb.toUInt64
  pbLe : pb ≤ 26
  segN : g eSegN = EW.ofK (c.point.size - pb).toUInt64
  stepW : g eStep = EW.ofK step.toUInt64
  stepLt : step < 12

/-- `g` agrees with `g0` outside the layer's elements. -/
def LFr (g g0 : Nat → EW) : Prop := ∀ i, ¬ LW i → g i = g0 i

theorem LFr.refl (g : Nat → EW) : LFr g g := fun _ _ ↦ rfl

theorem LFr.trans {g₁ g₂ g₃ : Nat → EW} (h₁ : LFr g₂ g₁) (h₂ : LFr g₃ g₂) : LFr g₃ g₁ :=
  fun i hi ↦ (h₂ i hi).trans (h₁ i hi)

/-- The tables survive a layer. -/
theorem LFr.cn {g g0 : Nat → EW} (h : LFr g g0) (hc : Cn g0) : Cn g :=
  hc.congr fun i h1 h2 ↦ h i (by unfold LW; p6_omega)

/-- The value the first check compares with the claim's. -/
def y1 (c : KeccakClaimW) (product : Array EW) (pb step : Nat) : EW :=
  sumE ((Array.range productBits).map fun cc ↦
      sumE ((c.mu.zip rmfeProjectW).filterMap fun (m, mask) ↦
        if testBitW mask cc then some m else none) * product.getD cc 0) +
    sumE ((Array.range keccakSegments).map fun segment ↦
      (eqKernel (c.point.extract pb c.point.size)).getD segment 0 *
        sumE ((Array.range 64).filterMap fun z ↦
          if testBitW (keccakRCW.getD (keccakDepth * (segment + 1) - step - 1) 0) z then
            some (c.weights.getD z 0) else none)) * sumE c.mu

/-- The layer's first part. -/
def l1M (c : KeccakClaimW) (pb step : Nat) : VM (Array EW) :=
  readScalars 47 >>= fun product ↦
    Model.require (y1 c product pb step == c.value) >>= fun _ ↦ pure product

/-- Its code. -/
def L1C : List Stmt := [rdN eProd 47, blk (projC :: stEl eProj), blk segC, blk iotaC,
  blk (sumMuC :: stEl eSumMu), blk chk1C]

/-- The segment weights are `eqKernel`'s entries. -/
theorem segV_eq {pt : Array EW} {pb : Nat} (hpt : ∀ i < pt.size, g (ePt + i) = pt.getD i 0)
    (k : Nat) : segV g pb (pt.size - pb) k = ((eqKernel (pt.extract pb pt.size)).getD k 0).toE := by
  have hs : (pt.extract pb pt.size).size = pt.size - pb := by simp
  unfold segV
  split
  · rename_i hk
    rw [eqKernel_getD _ (by rwa [hs]), hs]
    refine prod_congr rfl fun j hj ↦ ?_
    have hj := mem_range.1 hj
    have e : (pt.extract pb pt.size).getD j 0 = pt.getD (pb + j) 0 := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
      split <;> [rfl; omega]
    rw [kfac, e, Nat.add_assoc, hpt (pb + j) (by omega)]
  · rw [eqKernel_getD_out _ (by rw [hs]; omega), NativeVm.Equiv.EW.toE_zero]

/-- `y1`'s value from the scratch's pieces. -/
theorem y1_toE {c : KeccakClaimW} {product : Array EW} {pb step : Nat} (hmu : c.mu.size ≤ 16) :
    (y1 c product pb step).toE =
      (∑ i ∈ range c.mu.size, (c.mu.getD i 0).toE *
        ∑ cc ∈ range 47, if testBitW (NativeVm.Equiv.rmfeProjectWLit.getD i 0) cc then
          (product.getD cc 0).toE else 0) +
      (∑ seg ∈ range 2, ((eqKernel (c.point.extract pb c.point.size)).getD seg 0).toE *
        ∑ z ∈ range 64, if testBitW (keccakRCLit.getD (12 * (seg + 1) - step - 1) 0) z then
          (c.weights.getD z 0).toE else 0) *
      ∑ i ∈ range c.mu.size, (c.mu.getD i 0).toE := by
  have h1 := projected_sum c.mu product
  have h2 := iota_sum step (eqKernel (c.point.extract pb c.point.size)) c.weights
  rw [Nat.min_eq_left hmu] at h1
  rw [y1, NativeVm.Equiv.EW.toE_add, NativeVm.Equiv.EW.toE_mul, h1, h2, toE_sumE_range]

/-- The claim's elements. -/
def CW (i : Nat) : Prop :=
  i = eCV ∨ i = eMuN ∨ i = ePtN ∨ (eMu ≤ i ∧ i < eMu + 16) ∨ (ePt ≤ i ∧ i < ePt + 32) ∨
    (eW ≤ i ∧ i < eW + 1600)

theorem ClaimIn.congr {g' : Nat → EW} {c : KeccakClaimW} (h : ClaimIn g c)
    (he : ∀ i, CW i → g' i = g i) : ClaimIn g' c where
  value := (he eCV (Or.inl rfl)).trans h.value
  muSize := h.muSize
  muN := (he eMuN (Or.inr (Or.inl rfl))).trans h.muN
  mu i hi := (he (eMu + i) (by have := h.muSize; unfold CW; p6_omega)).trans (h.mu i hi)
  ptSize := h.ptSize
  ptN := (he ePtN (Or.inr (Or.inr (Or.inl rfl)))).trans h.ptN
  pt i hi := (he (ePt + i) (by have := h.ptSize; unfold CW; p6_omega)).trans (h.pt i hi)
  wSize := h.wSize
  w i hi := (he (eW + i) (by unfold CW; p6_omega)).trans (h.w i hi)

/-- The project table's words. -/
theorem cn_project {g : Nat → EW} (hc : Cn g) {i : Nat} (hi : i < 16) :
    (g (eProject + i)).c0 = NativeVm.Equiv.rmfeProjectWLit.getD i 0 := by
  rw [hc.2.2.2.2.2.2.2.2 i (lt_of_lt_of_eq hi rfl)]
  exact tProject_spec i hi

variable (env inp s0)

/-- **The layer's first part.** -/
theorem l1_refines (hin : Inputs env inp s0.mem) {c : KeccakClaimW} {pb step : Nat}
    (g0 : Nat → EW) (hpre : LPre g0 c pb step) :
    Refines (St env s0 g0) (blk L1C) (l1M c pb step)
      (fun product t s ↦ ∃ g, St env s0 g t s ∧ LFr g g0 ∧ ClaimIn g c ∧ product.size = 47 ∧
        ∀ i < 47, g (eProd + i) = product.getD i 0) (Kept env rs6 s0) := by
  have hcl := hpre.claim
  have hmu := hcl.muSize
  have hpts := hcl.ptSize
  have hpb := hpre.pbLe
  unfold L1C l1M
  refine Refines.blk_cons (rdN_refines env inp s0 hin (o := eProd) (n := 47) (by p6_omega)
    (by norm_num) g0) fun xs ↦ Refines.intro fun hsz ↦ ?_
  set g1 := wrA g0 eProd xs with hg1
  have k1 : ∀ i, ¬ (eProd ≤ i ∧ i < eProd + 47) → g1 i = g0 i := fun i hi ↦
    wrA_out (by rw [hsz]; omega)
  have hP : ∀ i < 47, g1 (eProd + i) = xs.getD i 0 := fun i hi ↦ wrA_in (by omega)
  have c1 : ClaimIn g1 c := hcl.congr fun i hi ↦ k1 i (by unfold CW at hi; p6_omega)
  have cn1 : Cn g1 := hpre.cn.congr fun i h1 h2 ↦ k1 i (by p6_omega)
  set n := c.point.size - pb
  have hd1 : g1 ePB = EW.ofK pb.toUInt64 := (k1 _ (by p6_omega)).trans hpre.pbW
  have hn1 : g1 eSegN = EW.ofK n.toUInt64 := (k1 _ (by p6_omega)).trans hpre.segN
  set g2 := Function.update g1 eProj (EW.ofE (projV g1 c.mu.size)) with hg2
  have k2 : ∀ i, i ≠ eProj → g2 i = g1 i := fun i hi ↦ Function.update_of_ne hi _ _
  obtain ⟨g3, p3, k3, v3⟩ := pure_segW (env := env) (s0 := s0) (g := g2) hin (d := pb) (n := n)
    ((k2 _ (by p6_ne)).trans hd1) ((k2 _ (by p6_ne)).trans hn1) (by omega) (by omega)
  have cn3 : Cn g3 := cn1.congr fun i h1 h2 ↦ (k3 i (by p6_omega)).trans (k2 i (by p6_omega))
  obtain ⟨g4, p4, k4, v4⟩ := pure_iota (env := env) (s0 := s0) (g := g3) hin (step := step) cn3
    ((k3 _ (by p6_omega)).trans ((k2 _ (by p6_ne)).trans ((k1 _ (by p6_omega)).trans hpre.stepW)))
    hpre.stepLt
  have kk : ∀ i, ¬ (i = eProj ∨ i = eKd ∨ i = eKn ∨ i = eSegW ∨ i = eSegW + 1 ∨ i = eVal ∨
      i = eIota) → g4 i = g1 i := fun i hi ↦ by
    simp only [not_or] at hi
    rw [k4 i hi.2.2.2.2.2.1 hi.2.2.2.2.2.2, k3 i (by simp only [not_or]; exact
      ⟨hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1⟩), k2 i hi.1]
  set g5 := Function.update g4 eSumMu (EW.ofE (∑ i ∈ range c.mu.size, (g4 (eMu + i)).toE)) with hg5
  have k5 : ∀ i, ¬ (i = eProj ∨ i = eKd ∨ i = eKn ∨ i = eSegW ∨ i = eSegW + 1 ∨ i = eVal ∨
      i = eIota ∨ i = eSumMu) → g5 i = g1 i := fun i hi ↦ by
    simp only [not_or] at hi
    rw [hg5, Function.update_of_ne hi.2.2.2.2.2.2.2, kk i (by simp only [not_or]; exact
      ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2.1, hi.2.2.2.2.2.2.1⟩)]
  have c5 : ClaimIn g5 c := c1.congr fun i hi ↦ k5 i (by unfold CW at hi; p6_omega)
  -- the values
  have hProj : (g5 eProj).toE = ∑ i ∈ range c.mu.size, (c.mu.getD i 0).toE *
      ∑ cc ∈ range 47, if testBitW (NativeVm.Equiv.rmfeProjectWLit.getD i 0) cc then
        (xs.getD cc 0).toE else 0 := by
    rw [hg5, Function.update_of_ne (by p6_ne), k4 _ (by p6_ne) (by p6_ne), k3 eProj (by p6_omega), hg2,
      Function.update_self, NativeVm.Equiv.EW.toE_ofE, projV]
    refine sum_congr rfl fun i hi ↦ ?_
    have hi := mem_range.1 hi
    rw [c1.mu i hi, cn_project cn1 (by omega)]
    congr 1
    exact sum_congr rfl fun cc hc ↦ by rw [hP cc (mem_range.1 hc)]
  have hW3 : ∀ z < 64, g3 (eW + z) = c.weights.getD z 0 := fun z hz ↦ by
    rw [k3 _ (by p6_omega), k2 _ (by p6_ne), c1.w z (by omega)]
  have hPt2 : ∀ i < c.point.size, g2 (ePt + i) = c.point.getD i 0 := fun i hi ↦ by
    rw [k2 _ (by p6_omega), c1.pt i hi]
  have hIota : (g5 eIota).toE =
      ((eqKernel (c.point.extract pb c.point.size)).getD 1 0).toE *
        (∑ z ∈ range 64, if testBitW (keccakRCLit.getD (12 * (1 + 1) - step - 1) 0) z then
          (c.weights.getD z 0).toE else 0) +
      ((eqKernel (c.point.extract pb c.point.size)).getD 0 0).toE *
        (∑ z ∈ range 64, if testBitW (keccakRCLit.getD (12 * (0 + 1) - step - 1) 0) z then
          (c.weights.getD z 0).toE else 0) := by
    rw [hg5, Function.update_of_ne (by p6_ne), v4, iotaV, iotaV,
      show eSegW = eSegW + 0 from rfl, v3 1 (by omega), v3 0 (by omega), segV_eq hPt2,
      segV_eq hPt2]
    congr 2 <;> exact sum_congr rfl fun z hz ↦ by rw [hW3 z (mem_range.1 hz)]
  have hSum : (g5 eSumMu).toE = ∑ i ∈ range c.mu.size, (c.mu.getD i 0).toE := by
    rw [hg5, Function.update_self, NativeVm.Equiv.EW.toE_ofE]
    exact sum_congr rfl fun i hi ↦ by
      have hi := mem_range.1 hi
      rw [kk (eMu + i) (by p6_omega), c1.mu i hi]
  have hy : (y1 c xs pb step).toE = (g5 eProj).toE + (g5 eIota).toE * (g5 eSumMu).toE := by
    rw [y1_toE hmu, hProj, hIota, hSum]
    simp only [sum_range_succ, sum_range_zero, zero_add]
    ring
  have hv : g5 eCV = c.value := c5.value
  refine Pure6.then (pure_proj hin c1.muN hmu) (Pure6.then p3 (Pure6.then p4
    (Pure6.then (pure_sumMu hin (g := g4) (o := eSumMu) ((kk _ (by p6_ne)).trans c1.muN) hmu
      (by p6_omega)) ?_)))
  rw [← hv]
  refine Refines.blk_cons (chk1_refines hin hy) fun _ ↦ Refines.skip fun t s h ↦
    ⟨g5, h, fun i hi ↦ (k5 i (by unfold LW at hi; p6_omega)).trans (k1 i (by unfold LW at hi; p6_omega)),
      c5, hsz, fun i hi ↦ (k5 _ (by p6_omega)).trans (hP i hi)⟩

end NativeVm.Code.P6
