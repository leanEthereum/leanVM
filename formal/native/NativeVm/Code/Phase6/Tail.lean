module

public import NativeVm.Code.Phase6.Layers
public import NativeVm.Code.Phase6.Open

/-!
# `verifyKeccak` after the layers

`tailM`: the committed outputs' opening and its check, the sumcheck over the pack's instances, the
inputs' opening, the slices and the final check (`verifyKeccak` after `keccakLayers`, `verifyKeccak_eq`).
`tailC` refines it (`tail_refines`) from the scratch holding the last claim and what the first
left (`TPre`), to one holding what the results' writers read (`TPost`): the first opening's slot
point saved at `eSegPt` and its word at `eComm`, since the second opening reuses `eSlot` and `eVal`.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm NativeVm.Model NativeVm.Code LeanVM.Parameters
open NativeVm.Transcript (wd wdisp Env)
open NativeVm.Field (eOf emul emul_spec eRegs)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-! ## The model -/

/-- `verifyKeccak` after the layers. -/
def tailM (logSteps : Nat) (inst : Array EW) (first : KeccakClaimW) (committed : EW)
    (claim : KeccakClaimW) : VM (Array ColumnClaimW × Array EW × Array EW) :=
  keccakOpen logSteps first 1 1 committed >>= fun o1 ↦ Model.readScalar >>= fun word ↦
  Model.require (o1.2.1.getD 0 0 * word == o1.2.2) >>= fun _ ↦
  Model.sumcheckPlain claim.value 3 4 >>= fun r ↦
  keccakOpen logSteps claim 0 2 r.2 >>= fun o2 ↦ Model.readScalars 64 >>= fun slices ↦
  Model.require (multilinearEval claim.mu r.1 * dot o2.2.1 slices == o2.2.2) >>= fun _ ↦
  pure (#[⟨LeanVM.Protocol.Verifier.qkeccak, inst.extract 0 4 ++ inst.extract 4 inst.size ++ o1.1,
      word⟩], r.1 ++ claim.point.extract 0 (logSteps - 4) ++ o2.1, slices)

/-- `verifyKeccak` before the layers. -/
def headM (logSteps : Nat) (inst output : Array EW) : VM (Array ColumnClaimW × Array EW × Array EW) :=
  Model.sampleChallenges 1 >>= fun segment ↦ Model.sampleChallenges 5 >>= fun lanePoint ↦
  Model.readScalar >>= fun committed ↦
  keccakLayers logSteps (keccakFirstClaim inst segment lanePoint output committed) >>= fun claim ↦
  tailM logSteps inst (keccakFirstClaim inst segment lanePoint output committed) committed claim

theorem verifyKeccak_eq (logSteps : Nat) (inst output : Array EW) :
    verifyKeccak logSteps inst output = headM logSteps inst output := by
  have h0 : Model.grind (Model.grindingBits (LeanVM.Protocol.Verifier.keccakSegmentBits +
      LeanVM.Protocol.Verifier.keccakLaneBits)) = pure () := by
    rw [show Model.grindingBits (LeanVM.Protocol.Verifier.keccakSegmentBits +
      LeanVM.Protocol.Verifier.keccakLaneBits) = 0 by decide]; rfl
  have h1 : (1 < LeanVM.Protocol.Verifier.keccakSegments) = True := by decide
  simp only [verifyKeccak, headM, tailM, h0, pure_bind, h1, ite_true]
  rfl

/-! ## Copies -/

/-- The `n` elements from `src` copied to `dst`. -/
def cpN : Nat → Nat → Nat → List Stmt
  | _, _, 0 => []
  | src, dst, n + 1 => blk (cpEl src dst) :: cpN (src + 1) (dst + 1) n

theorem pure_cpN (hin : Inputs env inp s0.mem) :
    ∀ (n src dst : Nat) (g : Nat → EW), src + n ≤ scrN → dst + n ≤ scrN →
      (src + n ≤ dst ∨ dst + n ≤ src) →
      ∃ g', Pure6 env s0 (blk (cpN src dst n)) g g' ∧ (∀ i < n, g' (dst + i) = g (src + i)) ∧
        ∀ i, ¬ (dst ≤ i ∧ i < dst + n) → g' i = g i
  | 0, _, _, g, _, _, _ => ⟨g, Pure6.nil, fun _ h ↦ absurd h (by omega), fun _ _ ↦ rfl⟩
  | n + 1, src, dst, g, h1, h2, h3 => by
    obtain ⟨g', p, v, k⟩ := pure_cpN hin n (src + 1) (dst + 1) (Function.update g dst (g src))
      (by omega) (by omega) (by omega)
    refine ⟨g', Pure6.cons (pure_cp hin (by omega) (by omega)) p, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · rcases i with _ | i
      · rw [k _ (by omega), Nat.add_zero, Function.update_self, Nat.add_zero]
      · rw [show dst + (i + 1) = dst + 1 + i by omega, v i (by omega),
          Function.update_of_ne (by omega), show src + 1 + i = src + (i + 1) by omega]
    · rw [k _ (by omega), Function.update_of_ne (by omega)]

/-! ## The committed outputs' check -/

/-- `weights[0] · word` against the opening's claim. -/
def chk3C : List Stmt := ldA eOW ++ ldB eVal ++ [emul] ++ chkEl eSC

theorem chk3_refines (hin : Inputs env inp s0.mem) {y : EW}
    (hy : y.toE = (g eOW).toE * (g eVal).toE) :
    Refines (St env s0 g) (blk chk3C) (Model.require (y == g eSC)) (fun _ t s ↦ St env s0 g t s)
      (Kept env rs6 s0) := by
  intro t s h
  unfold chk3C
  simp only [List.append_assoc]
  refine ldA_spec h.2.2.1 h.2.2.2 (by p6_omega) ?_
  refine ldB_spec (by simpa using h.2.2.1) (h.2.2.2.congr fun _ _ ↦ rfl) (by p6_omega) ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun s1 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
  have h1 : St env s0 g t s1 :=
    (((h.setReg (r := .r9) (by decide) (by decide) _).setReg (r := .r10) (by decide) (by decide) _).setReg
      (r := .r11) (by decide) (by decide) _ |>.setReg (r := .r12) (by decide) (by decide) _).frame hin
      e2 e3
  refine chkEl_refines (by p6_omega) y t s1 ⟨h1, ?_⟩
  rw [e1, hy]
  simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, eOf_toE]

/-! ## The tail -/

/-- What the tail starts from: the last claim, `packBits`, the first claim's segment and bit
weights, the committed outputs' claim, `KECCAK`'s point. -/
structure TPre (g : Nat → EW) (pb : Nat) (inst : Array EW) (first claim : KeccakClaimW)
    (committed : EW) : Prop where
  cl : ClaimIn g claim
  muSize : claim.mu.size = 16
  pbW : g ePB = EW.ofK pb.toUInt64
  pbLe : pb ≤ 26
  segN : g eSegN = EW.ofK (claim.point.size - pb).toUInt64
  seg1 : ∀ k < 2, g (eSegW1 + k) = (eqKernel (first.point.extract pb first.point.size)).getD k 0
  wf : ∀ j < 1600, g (eWF + j) = first.weights.getD j 0
  comm : g eComm = committed
  instSize : inst.size ≤ 30
  instN : g eInstN = EW.ofK inst.size.toUInt64
  instG : ∀ i < inst.size, g (eInst + i) = inst.getD i 0

/-- What the results' writers read, the result's parts `low`, `slot1`, `slot2`, `word`. -/
structure TPostW (g : Nat → EW) (pb : Nat) (inst : Array EW) (claim : KeccakClaimW)
    (r : Array ColumnClaimW × Array EW × Array EW) (low slot1 slot2 : Array EW) (word : EW) :
    Prop where
  eq : r = (#[⟨LeanVM.Protocol.Verifier.qkeccak, inst.extract 0 4 ++ inst.extract 4 inst.size ++
    slot1, word⟩], low ++ claim.point.extract 0 pb ++ slot2, r.2.2)
  lowSize : low.size = 4
  lowG : ∀ i < 4, g (eLow + i) = low.getD i 0
  slot1Size : slot1.size = 6
  slot1G : ∀ i < 6, g (eSegPt + i) = slot1.getD i 0
  slot2Size : slot2.size = 6
  slot2G : ∀ i < 6, g (eSlot + i) = slot2.getD i 0
  wordG : g eComm = word
  slSize : r.2.2.size = 64
  slG : ∀ z < 64, g (eSl + z) = r.2.2.getD z 0
  ptSize : claim.point.size < 32
  ptN : g ePtN = EW.ofK claim.point.size.toUInt64
  pt : ∀ i < claim.point.size, g (ePt + i) = claim.point.getD i 0
  pbW : g ePB = EW.ofK pb.toUInt64
  pbLe : pb ≤ 26
  instSize : inst.size ≤ 30
  instN : g eInstN = EW.ofK inst.size.toUInt64
  instG : ∀ i < inst.size, g (eInst + i) = inst.getD i 0

/-- What the results' writers read. -/
def TPost (g : Nat → EW) (pb : Nat) (inst : Array EW) (claim : KeccakClaimW)
    (r : Array ColumnClaimW × Array EW × Array EW) : Prop :=
  ∃ low slot1 slot2 word, TPostW g pb inst claim r low slot1 slot2 word

/-- The tail's code. -/
def tailC : List Stmt := [blk (cpEl eComm eSC), blk (openC 1 eSegW1 eWF), rdEl eVal, blk chk3C,
  blk (cpEl eVal eComm), blk (cpN eSlot eSegPt 6), blk (cpEl eCV eSC), scP 3 eLow 4, blk segC,
  blk (openC 0 eSegW eW), rdN eSl 64, blk finC]

/-- A refinement from a sumcheck's result. -/
theorem Refines.scPost {α : Type} {g0 : Nat → EW} {co n : Nat} {r : Array EW × EW} {c : Stmt}
    {m : VM α} {Q : α → TState → QState → Prop} {E : QState → Prop}
    (h : r.1.size = n → ∀ g, (∀ i, ¬ Tmp i → g i = wrA g0 co r.1 i) → g eSC = r.2 →
      Refines (St env s0 g) c m Q E) :
    Refines (SCPost env s0 g0 co n r) c m Q E :=
  fun t s ⟨hn, g, hs, hk, hsc⟩ ↦ h hn g hk hsc t s hs

variable (env inp s0)

/-- **The tail** against `tailM`. -/
theorem tail_refines (hin : Inputs env inp s0.mem) {logSteps : Nat} {inst : Array EW}
    {first claim : KeccakClaimW} {committed : EW} (g0 : Nat → EW)
    (hpre : TPre g0 (logSteps - 4) inst first claim committed) :
    Refines (St env s0 g0) (blk tailC) (tailM logSteps inst first committed claim)
      (fun r t s ↦ ∃ g, St env s0 g t s ∧ TPost g (logSteps - 4) inst claim r)
      (Kept env rs6 s0) := by
  have hcl := hpre.cl
  have hpts := hcl.ptSize
  have hpb := hpre.pbLe
  unfold tailC tailM
  -- the first opening
  set g1 := Function.update g0 eSC (g0 eComm) with hg1
  have k1 : ∀ i, i ≠ eSC → g1 i = g0 i := fun i hi ↦ Function.update_of_ne hi _ _
  refine Pure6.then (pure_cp hin (src := eComm) (dst := eSC) (by p6_omega) (by p6_omega)) ?_
  refine Refines.blk_cons (open_refines hin (first := 1) (sw := eSegW1) (wb := eWF) (by omega)
    (by p6_omega) ⟨(by unfold OpenW Tmp; p6_omega), (by unfold OpenW Tmp; p6_omega)⟩
    (fun j hj ↦ (by unfold OpenW Tmp; p6_omega)) (by p6_omega) logSteps first committed g1
    (by rw [hg1, Function.update_self, hpre.comm])
    (fun k hk ↦ (k1 _ (by p6_omega)).trans (hpre.seg1 k hk))
    (fun j hj ↦ (k1 _ (by p6_omega)).trans (hpre.wf j hj))) fun o1 ↦
    Refines.exSt fun g2 ⟨o1s, o1G, o1ws, o1wG, o1v, k2⟩ ↦ ?_
  -- the word and the check
  refine Refines.blk_cons (rdEl_refines env inp s0 hin (o := eVal) (by p6_omega) g2) fun word ↦ ?_
  set g3 := Function.update g2 eVal word with hg3
  have k3 : ∀ i, i ≠ eVal → g3 i = g2 i := fun i hi ↦ Function.update_of_ne hi _ _
  have hsc3 : g3 eSC = o1.2.2 := (k3 _ (by p6_ne)).trans o1v
  rw [← hsc3]
  refine Refines.blk_cons (chk3_refines hin (y := o1.2.1.getD 0 0 * word) ?_) fun _ ↦ ?_
  · rw [k3 _ (by p6_ne), show eOW = eOW + 0 from rfl, o1wG 0 (by omega), hg3, Function.update_self,
      NativeVm.Equiv.EW.toE_mul]
  -- the copies
  set g4 := Function.update g3 eComm (g3 eVal) with hg4
  have k4 : ∀ i, i ≠ eComm → g4 i = g3 i := fun i hi ↦ Function.update_of_ne hi _ _
  have hw4 : g4 eComm = word := by rw [hg4, Function.update_self, hg3, Function.update_self]
  obtain ⟨g5, p5, v5, k5⟩ := pure_cpN (env := env) (s0 := s0) hin 6 eSlot eSegPt g4 (by p6_omega)
    (by p6_omega) (by p6_omega)
  set g6 := Function.update g5 eSC (g5 eCV) with hg6
  have k6 : ∀ i, i ≠ eSC → g6 i = g5 i := fun i hi ↦ Function.update_of_ne hi _ _
  -- from `g0` to `g6`, away from the opening's elements
  have k06 : ∀ i, ¬ OpenW i → i ≠ eVal → i ≠ eComm → ¬ (eSegPt ≤ i ∧ i < eSegPt + 6) →
      g6 i = g0 i := fun i h1 h2 h3 h4 ↦ by
    rw [k6 i (by unfold OpenW Tmp at h1; omega), k5 i h4, k4 i h3, k3 i h2, k2 i h1,
      k1 i (by unfold OpenW Tmp at h1; omega)]
  have hcv6 : g6 eSC = claim.value := by
    rw [hg6, Function.update_self, k5 _ (by p6_omega), k4 _ (by p6_ne), k3 _ (by p6_ne),
      k2 _ ((by unfold OpenW Tmp; p6_omega)), k1 _ (by p6_ne), hcl.value]
  have hptN6 : g6 ePtN = EW.ofK claim.point.size.toUInt64 :=
    (k06 _ ((by unfold OpenW Tmp; p6_omega)) (by p6_ne) (by p6_ne) (by p6_omega)).trans hcl.ptN
  refine Pure6.then (pure_cp hin (src := eVal) (dst := eComm) (by p6_omega) (by p6_omega))
    (Pure6.then p5 (Pure6.then (pure_cp hin (src := eCV) (dst := eSC) (by p6_omega)
      (by p6_omega)) ?_))
  rw [← hcv6]
  -- the sumcheck over the instances
  refine Refines.blk_cons (scP_refines env inp s0 hin (c := 3) (co := eLow) (n := 4)
    (np := claim.point.size) (by omega) (by p6_omega) (by p6_omega) (g6 eSC) g6 rfl hptN6) fun r ↦
    Refines.scPost fun hrs g7 k7 hsc7 ↦ ?_
  have k7' : ∀ i, ¬ Tmp i → ¬ (eLow ≤ i ∧ i < eLow + 4) → g7 i = g6 i := fun i h1 h2 ↦
    (k7 i h1).trans (wrA_out (by rw [hrs]; omega))
  have hlow7 : ∀ i < 4, g7 (eLow + i) = r.1.getD i 0 := fun i hi ↦
    (k7 _ (by unfold Tmp; p6_omega)).trans (wrA_in (by omega))
  have k07 : ∀ i, ¬ OpenW i → i ≠ eVal → i ≠ eComm → ¬ (eSegPt ≤ i ∧ i < eSegPt + 6) →
      ¬ (eLow ≤ i ∧ i < eLow + 4) → g7 i = g0 i := fun i h1 h2 h3 h4 h5 ↦
    (k7' i (fun h ↦ h1 (Or.inl h)) h5).trans (k06 i h1 h2 h3 h4)
  have hpt7 : ∀ i < claim.point.size, g7 (ePt + i) = claim.point.getD i 0 := fun i hi ↦
    (k07 _ ((by unfold OpenW Tmp; p6_omega)) (by p6_omega) (by p6_omega) (by p6_omega) (by p6_omega)).trans
      (hcl.pt i hi)
  -- the last claim's segment weights
  obtain ⟨g8, p8, k8, v8⟩ := pure_segW (env := env) (s0 := s0) (g := g7) hin (d := logSteps - 4)
    (n := claim.point.size - (logSteps - 4))
    ((k07 _ ((by unfold OpenW Tmp; p6_omega)) (by p6_ne) (by p6_ne) (by p6_omega) (by p6_omega)).trans
      hpre.pbW)
    ((k07 _ ((by unfold OpenW Tmp; p6_omega)) (by p6_ne) (by p6_ne) (by p6_omega) (by p6_omega)).trans
      hpre.segN) (by omega) (by omega)
  have hseg8 : ∀ k < 2, g8 (eSegW + k) =
      (eqKernel (claim.point.extract (logSteps - 4) claim.point.size)).getD k 0 := fun k hk ↦
    NativeVm.Equiv.EW.toE_injective ((v8 k hk).trans (segV_eq hpt7 k))
  have k8' : ∀ i, ¬ OpenW i → i ≠ eSegW → i ≠ eSegW + 1 → g8 i = g7 i := fun i h1 h2 h3 ↦
    k8 i (by unfold OpenW at h1; simp only [not_or] at h1 ⊢; exact ⟨h1.2.2.1, h1.2.1, h2, h3⟩)
  have hsc8 : g8 eSC = r.2 := (k8 _ (by p6_omega)).trans hsc7
  refine Pure6.then p8 ?_
  rw [← hsc8]
  -- the inputs' opening
  refine Refines.blk_cons (open_refines hin (first := 0) (sw := eSegW) (wb := eW) (by omega)
    (by p6_omega) ⟨(by unfold OpenW Tmp; p6_omega), (by unfold OpenW Tmp; p6_omega)⟩
    (fun j hj ↦ (by unfold OpenW Tmp; p6_omega)) (by p6_omega) logSteps claim (g8 eSC) g8 rfl hseg8
    (fun j hj ↦ (k8' _ ((by unfold OpenW Tmp; p6_omega)) (by p6_omega) (by p6_omega)).trans
      ((k07 _ ((by unfold OpenW Tmp; p6_omega)) (by p6_omega) (by p6_omega) (by p6_omega)
        (by p6_omega)).trans (hcl.w j hj)))) fun o2 ↦
    Refines.exSt fun g9 ⟨o2s, o2G, o2ws, o2wG, o2v, k9⟩ ↦ ?_
  -- the slices and the final check
  refine Refines.blk_cons (rdN_refines env inp s0 hin (o := eSl) (n := 64) (by p6_omega)
    (by norm_num) g9) fun slices ↦ Refines.intro fun hsl ↦ ?_
  set g10 := wrA g9 eSl slices with hg10
  have k10 : ∀ i, ¬ (eSl ≤ i ∧ i < eSl + 64) → g10 i = g9 i := fun i hi ↦
    wrA_out (by rw [hsl]; omega)
  have k0_10 : ∀ i, ¬ OpenW i → i ≠ eVal → i ≠ eComm → ¬ (eSegPt ≤ i ∧ i < eSegPt + 6) →
      ¬ (eLow ≤ i ∧ i < eLow + 4) → i ≠ eSegW → i ≠ eSegW + 1 → ¬ (eSl ≤ i ∧ i < eSl + 64) →
      g10 i = g0 i := fun i h1 h2 h3 h4 h5 h6 h7 h8 ↦
    (k10 i h8).trans ((k9 i h1).trans ((k8' i h1 h6 h7).trans (k07 i h1 h2 h3 h4 h5)))
  have hlow10 : ∀ i < 4, g10 (eLow + i) = r.1.getD i 0 := fun i hi ↦ by
    rw [k10 _ (by p6_omega), k9 _ ((by unfold OpenW Tmp; p6_omega)), k8' _ ((by unfold OpenW Tmp; p6_omega))
      (by p6_omega) (by p6_omega), hlow7 i hi]
  refine Refines.blk_cons (fin_refines hin (mu := claim.mu) (low := r.1) (wts := o2.2.1)
    (slices := slices) g10 hpre.muSize
    (fun i hi ↦ (k0_10 _ ((by unfold OpenW Tmp; p6_omega)) (by p6_omega) (by p6_omega) (by p6_omega)
      (by p6_omega) (by p6_omega) (by p6_omega) (by p6_omega)).trans (hcl.mu i (by rw [hpre.muSize]; exact hi)))
    hrs hlow10 o2ws (fun z hz ↦ (k10 _ (by p6_omega)).trans (o2wG z hz)) hsl
    (fun z hz ↦ wrA_in (by omega)) ((k10 _ (by p6_omega)).trans o2v)) fun _ ↦
    Refines.exSt fun g11 k11 ↦ Refines.skip fun t s h ↦ ⟨g11, h, ?_⟩
  have k11' : ∀ i, ¬ OpenW i → g11 i = g10 i := fun i hi ↦ k11 i (Or.inl hi)
  -- the results' inputs, from `g0`
  have kf : ∀ i, ¬ OpenW i → i ≠ eVal → i ≠ eComm → ¬ (eSegPt ≤ i ∧ i < eSegPt + 6) →
      ¬ (eLow ≤ i ∧ i < eLow + 4) → i ≠ eSegW → i ≠ eSegW + 1 → ¬ (eSl ≤ i ∧ i < eSl + 64) →
      g11 i = g0 i := fun i h1 h2 h3 h4 h5 h6 h7 h8 ↦
    (k11' i h1).trans (k0_10 i h1 h2 h3 h4 h5 h6 h7 h8)
  refine ⟨r.1, o1.1, o2.1, word, {
    eq := rfl
    lowSize := hrs
    lowG := fun i hi ↦ (k11' _ ((by unfold OpenW Tmp; p6_omega))).trans (hlow10 i hi)
    slot1Size := o1s
    slot1G := fun i hi ↦ by
      rw [k11' _ ((by unfold OpenW Tmp; p6_omega)), k10 _ (by p6_omega), k9 _ ((by unfold OpenW Tmp; p6_omega)),
        k8' _ ((by unfold OpenW Tmp; p6_omega)) (by p6_omega) (by p6_omega),
        k7' _ (by unfold Tmp; p6_omega) (by p6_omega), k6 _ (by p6_omega), v5 i hi,
        k4 _ (by p6_omega), k3 _ (by p6_omega), o1G i hi]
    slot2Size := o2s
    slot2G := fun i hi ↦ (k11 _ (Or.inr (by omega))).trans
      ((k10 _ (by p6_omega)).trans (o2G i hi))
    wordG := by
      rw [k11' _ ((by unfold OpenW Tmp; p6_omega)), k10 _ (by p6_omega), k9 _ ((by unfold OpenW Tmp; p6_omega)),
        k8' _ ((by unfold OpenW Tmp; p6_omega)) (by p6_ne) (by p6_ne),
        k7' _ (by unfold Tmp; p6_ne) (by p6_omega), k6 _ (by p6_ne), k5 _ (by p6_omega), hw4]
    slSize := hsl
    slG := fun z hz ↦ (k11' _ ((by unfold OpenW Tmp; p6_omega))).trans (wrA_in (by omega))
    ptSize := hpts
    ptN := (kf _ ((by unfold OpenW Tmp; p6_omega)) (by p6_ne) (by p6_ne) (by p6_omega) (by p6_omega)
      (by p6_ne) (by p6_ne) (by p6_omega)).trans hcl.ptN
    pt := fun i hi ↦ (kf _ ((by unfold OpenW Tmp; p6_omega)) (by p6_omega) (by p6_omega) (by p6_omega)
      (by p6_omega) (by p6_omega) (by p6_omega) (by p6_omega)).trans (hcl.pt i hi)
    pbW := (kf _ ((by unfold OpenW Tmp; p6_omega)) (by p6_ne) (by p6_ne) (by p6_omega) (by p6_omega)
      (by p6_ne) (by p6_ne) (by p6_omega)).trans hpre.pbW
    pbLe := hpb
    instSize := hpre.instSize
    instN := (kf _ ((by unfold OpenW Tmp; p6_omega)) (by p6_ne) (by p6_ne) (by p6_omega) (by p6_omega)
      (by p6_ne) (by p6_ne) (by p6_omega)).trans hpre.instN
    instG := fun i hi ↦ (kf _ ((by have := hpre.instSize; unfold OpenW Tmp; p6_omega)) (by p6_omega)
      (by p6_omega) (by p6_omega) (by p6_omega) (by p6_omega) (by p6_omega)
      (by have := hpre.instSize; p6_omega)).trans (hpre.instG i hi) }⟩

end NativeVm.Code.P6
