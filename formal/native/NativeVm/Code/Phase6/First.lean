module

public import NativeVm.Code.Phase6.FirstB

/-!
# Phase 6's start: the scratch, `KECCAK`'s evaluations, the first claim

`setupC` points `rbp` at the scratch and writes the constant tables (`setup_spec`); `copyC` copies
`KECCAK`'s point and its `25` output lanes' evaluations from `evalsR`, and `packBits` from the
layout, into the scratch (`pure_copy`); `firstC` builds `keccakFirstClaim` there (`pure_first`),
with a copy of its bit weights at `eWF` and its two segment weights at `eSegW1`, which the
committed outputs' opening reads after the layers.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeVm.Transcript (wd wdisp Env)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-! ## The scratch and the tables -/

/-- `rbp` at the scratch, then the tables. -/
def setupC : List Stmt := ldSb ++ initAll

theorem setup_spec (hin : Inputs env inp s0.mem) (hc : CodeRel env t s0) :
    WP (blk setupC) s0 (fun s ↦ ∃ g, St env s0 g t s ∧ Cn g) (fun _ ↦ False) := by
  obtain ⟨g', hp, hcn, -⟩ := pure_initAll hin (scrOf s0.mem (sb env))
  exact setup_st hc (WP.mono (hp t _ (setup_st' hin hc)) (fun _ h ↦ ⟨g', h, hcn⟩) (fun _ h ↦ h))

/-! ## `KECCAK`'s evaluations -/

/-- The elements `copyC` writes. -/
def CopyW (i : Nat) : Prop :=
  i = eInstN ∨ i = ePB ∨ i = eKn ∨ i = eKd ∨ (eInst ≤ i ∧ i < eInst + 32) ∨
    (eOut ≤ i ∧ i < eOut + 25)

/-- **What `copyC` leaves**: `KECCAK`'s point, its output lanes' evaluations (`0` past the
evaluations' end) and `packBits`. -/
def CopyIn (g : Nat → EW) (layout : LayoutW) (ev : Array (Array EW × Array EW)) : Prop :=
  (ev.getD opKeccak (#[], #[])).1.size ≤ 30 ∧
    g eInstN = EW.ofK (ev.getD opKeccak (#[], #[])).1.size.toUInt64 ∧
    (∀ i < (ev.getD opKeccak (#[], #[])).1.size,
      g (eInst + i) = (ev.getD opKeccak (#[], #[])).1.getD i 0) ∧
    (∀ l < 25, g (eOut + l) = (ev.getD opKeccak (#[], #[])).2.getD (keccakOut + l) 0) ∧
    layout.tableLogHeights.getD opKeccak 0 ≤ 30 ∧
    g ePB = EW.ofK (layout.tableLogHeights.getD opKeccak 0 - 4).toUInt64

/-- The point, the output lanes and `packBits` into the scratch. -/
def copyC : List Stmt := cpyC

theorem pure_copy (hin : Inputs env inp s0.mem) {layout : LayoutW} {rate : Nat}
    {ev : Array (Array EW × Array EW)}
    (hlay : LayoutAt s0.mem (layoutR.at env.work) inp.bytecode layout rate)
    (hev : EvalsAt s0.mem (evalsR.at env.work) ev) (g : Nat → EW) :
    ∃ g', Pure6 env s0 (blk copyC) g g' ∧ (∀ i, ¬ CopyW i → g' i = g i) ∧ CopyIn g' layout ev := by
  obtain ⟨g', hp, hk, h1, h2, h3, h4⟩ := pure_cpy hin hlay hev g
  have hsz : (ev.getD opKeccak (#[], #[])).1.size ≤ 30 := ((hev.2 5 (by decide)).1).1
  refine ⟨g', hp, fun i hi ↦ hk i fun h ↦ hi ?_, hsz, h1, fun i hi ↦ h2 i (by omega), h3,
    hlay.heightsBound 5 (by decide), h4⟩
  unfold CopyW
  tauto

/-! ## The first claim -/

/-- The elements `firstC` writes. -/
def FirstW (i : Nat) : Prop :=
  LW i ∨ i = eSegN ∨ i = eSegW1 ∨ i = eSegW1 + 1 ∨ (eLanes ≤ i ∧ i < eLanes + 32) ∨
    (eWF ≤ i ∧ i < eWF + 1600)

/-- `keccakFirstClaim` into the scratch. -/
def firstC : List Stmt := [blk firstAC, blk firstBC, blk segC, blk (cpEl eSegW eSegW1),
  blk (cpEl (eSegW + 1) (eSegW1 + 1))]

theorem pure_first (hin : Inputs env inp s0.mem) (_hc : Cn g) {inst output segment lanePoint : Array EW}
    {committed : EW} {pb : Nat} (hinst : inst.size ≤ 30)
    (hinstN : g eInstN = EW.ofK inst.size.toUInt64)
    (hinstG : ∀ i < inst.size, g (eInst + i) = inst.getD i 0)
    (hout : output.size = 25) (houtG : ∀ l < 25, g (eOut + l) = output.getD l 0)
    (hseg : segment.size = 1) (hsegG : g eSegPt = segment.getD 0 0)
    (hlp : lanePoint.size = 5) (hlpG : ∀ i < 5, g (eLanePt + i) = lanePoint.getD i 0)
    (hcomm : g eComm = committed) (hpb : g ePB = EW.ofK pb.toUInt64) (hpb26 : pb ≤ 26) :
    ∃ g', Pure6 env s0 (blk firstC) g g' ∧
      ClaimIn g' (keccakFirstClaim inst segment lanePoint output committed) ∧
      (∀ j < 1600, g' (eWF + j) =
        (keccakFirstClaim inst segment lanePoint output committed).weights.getD j 0) ∧
      g' eSegN = EW.ofK
        ((keccakFirstClaim inst segment lanePoint output committed).point.size - pb).toUInt64 ∧
      (∀ k < 2, g' (eSegW1 + k) =
        (eqKernel ((keccakFirstClaim inst segment lanePoint output committed).point.extract pb
          (keccakFirstClaim inst segment lanePoint output committed).point.size)).getD k 0) ∧
      ∀ i, ¬ FirstW i → g' i = g i := by
  set c := keccakFirstClaim inst segment lanePoint output committed with hc_def
  have hN := scrN_lt
  obtain ⟨gA, pA, kA, wA, wfA, cvA⟩ := pure_firstA hin (inst := inst) hout houtG hseg hsegG hlp hlpG
    hcomm
  have rA : ∀ i, ¬ AW i → gA i = g i := kA
  obtain ⟨gB, pB, kB, muS, muN, muG, ptS, ptN, ptG, segN⟩ := pure_firstB hin
    (lanePoint := lanePoint) (output := output) (committed := committed) (g := gA) hinst
    (by rw [rA _ (by simp only [AW]; p6_omega), hinstN])
    (fun i hi ↦ by rw [rA _ (by simp only [AW]; p6_omega), hinstG i hi]) hseg
    (by rw [rA _ (by simp only [AW]; p6_omega), hsegG])
    (by rw [rA _ (by simp only [AW]; p6_omega), hpb]) hpb26
  have rB : ∀ i, ¬ BW i → gB i = gA i := kB
  rw [← hc_def] at muS muN muG ptS ptN ptG segN
  set P := c.point.size with hP
  obtain ⟨gC, pC, kC, vC⟩ := pure_segW hin (g := gB) (d := pb) (n := P - pb)
    (by rw [rB _ (by simp only [BW]; p6_omega), rA _ (by simp only [AW]; p6_omega), hpb]) segN
    (by omega) (by omega)
  set gD := Function.update gC eSegW1 (gC eSegW)
  set gE := Function.update gD (eSegW1 + 1) (gD (eSegW + 1))
  have pD : Pure6 env s0 (blk (cpEl eSegW eSegW1)) gC gD := pure_cp hin (by p6_omega) (by p6_omega)
  have pE : Pure6 env s0 (blk (cpEl (eSegW + 1) (eSegW1 + 1))) gD gE :=
    pure_cp hin (by p6_omega) (by p6_omega)
  have rE : ∀ i, ¬ (i = eKd ∨ i = eKn ∨ i = eSegW ∨ i = eSegW + 1) → i ≠ eSegW1 →
      i ≠ eSegW1 + 1 → gE i = gB i := fun i h1 h2 h3 ↦ by
    simp only [gE, gD]
    rw [Function.update_of_ne h3, Function.update_of_ne h2, kC i h1]
  have rEA : ∀ i, ¬ BW i → ¬ (i = eKd ∨ i = eKn ∨ i = eSegW ∨ i = eSegW + 1) → i ≠ eSegW1 →
      i ≠ eSegW1 + 1 → gE i = gA i := fun i h0 h1 h2 h3 ↦ by rw [rE i h1 h2 h3, rB i h0]
  refine ⟨gE, Pure6.cons pA (Pure6.cons pB (Pure6.cons pC (Pure6.cons pD (Pure6.single pE)))),
    ⟨?_, muS, ?_, fun i hi ↦ ?_, ptS, ?_, fun i hi ↦ ?_, ?_, fun i hi ↦ ?_⟩, fun j hj ↦ ?_, ?_,
    fun k hk ↦ ?_, fun i hi ↦ ?_⟩
  · rw [rEA _ (by simp only [BW]; p6_omega) (by p6_omega) (by p6_omega) (by p6_omega), cvA]
  · rw [rE _ (by p6_omega) (by p6_omega) (by p6_omega), muN]
  · rw [rE _ (by p6_omega) (by p6_omega) (by p6_omega), muG i hi]
  · rw [rE _ (by p6_omega) (by p6_omega) (by p6_omega), ptN]
  · rw [rE _ (by p6_omega) (by p6_omega) (by p6_omega), ptG i hi]
  · rw [kfc_weights, Array.size_map, Array.size_range]; rfl
  · rw [rEA _ (by simp only [BW]; p6_omega) (by p6_omega) (by p6_omega) (by p6_omega), wA i hi]
  · rw [rEA _ (by simp only [BW]; p6_omega) (by p6_omega) (by p6_omega) (by p6_omega), wfA j hj]
  · rw [rE _ (by p6_omega) (by p6_omega) (by p6_omega), segN]
  · have hv : gE (eSegW1 + k) = gC (eSegW + k) := by
      rcases k with _ | _ | k
      · simp only [gE, gD]
        rw [Function.update_of_ne (by p6_ne), Nat.add_zero, Function.update_self, Nat.add_zero]
      · simp only [gE, gD]
        rw [Function.update_self, Function.update_of_ne (by p6_ne)]
      · omega
    rw [hv]
    apply NativeVm.Equiv.EW.toE_injective
    rw [vC k hk, segV]
    have hes : (c.point.extract pb P).size = P - pb := by
      rw [Array.size_extract, hP, Nat.min_self]
    by_cases h2 : k < 2 ^ (P - pb)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), eqKernel_getD _ (by rw [hes]; exact h2), hes]
      refine Finset.prod_congr rfl fun j hj ↦ ?_
      have hj' := Finset.mem_range.1 hj
      rw [kfac, extract_getD' _ (by omega) (by omega), ← ptG (pb + j) (by omega), Nat.add_assoc]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2),
        eqKernel_getD_out _ (by rw [hes]; omega), NativeVm.Equiv.EW.toE_zero]
  · simp only [FirstW, LW, not_or, not_and, Nat.not_lt] at hi
    rw [rEA i (by simp only [BW]; p6_omega) (by p6_omega) (by p6_omega) (by p6_omega),
      rA i (by simp only [AW]; p6_omega)]

end NativeVm.Code.P6
