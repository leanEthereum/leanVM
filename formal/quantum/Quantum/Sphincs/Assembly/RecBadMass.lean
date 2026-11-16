module

public import Quantum.Sphincs.Assembly.CostRefined
public import Quantum.Sphincs.Assembly.KeyMsg
public import Quantum.Xmss.Assembly.RecBadMass

@[expose] public section

/-!
# The `RecBad` mass of the counter trials

CostRefined's `recBadPre` sums, along the challenge prefix `prefixR pol A p v`, the weight of the
`RecBad` states at the trials' `h`-reads: the read cell `z` recorded (not hardwired), the state in
`BadR`, the state with the cell emptied not. As leanXMSS's `Quantum.Xmss.Assembly.RecBadMass`, this
file splits it and moves the re-grind part to the decompressed basis; unlike leanXMSS there is no
part off the re-grinds (`RecHitB`): each WOTS key signs one fixed value (KeyMsg).

* **What one recorded `h` value can do** (`recBad_cases`): leanXMSS's `tgt_eq_of_emptied` for both
  parts of the event. If the trial's own one-block tail reaches `z` in the union with a rate of the
  trial's digest (`TrialOn`), the recorded value hits the target of the trial's tail (`RecHit`); the
  coverage part needs an `H_msg` call-0 tail, and the trial's tail is at an encoding slot
  (`slotOf_encBlk`). Otherwise the trial's path is missing from the union (`RecOff`).
* **Always a re-grind** (`RegrindSel`, `RecHitA`, `recBad_of_kInv`): a hit needs the trial's key
  selected (`sel_of_recHit`); on KeyMsg's invariant the selection and the trial are blocks of the
  same search (`sameGrind_of_kInv`). So `recBadPre ≤ recHitAPre + recOffPre` (`recBadPre_le`,
  KeyMsg's `forallQueries_selKey`).
* **The conversion** (`recHitAW_le`, `recHitAPre_le`): leanXMSS's `re_trace_recH_wm_le` with the
  content predicate `hitG` (one target digest, `cellFrac_hitG_le`: `2^-128`):
  `recHitAPre ≤ 2 decHitAPre + recConv`, `recConv = 2^-127 clsCap ≤ 2^-59` (`recConv_le`).
* **The prefix and the average** (`recBadPre_le_parts`, `RecBadAvg`, `recBadAvg_of_parts`):
  `recBadPre ≤ 2 decHitAPre + recConv + recOffPre`, averaged over any finite family of template
  data from the averaged bounds `DecHitAvg` of `decHitAPre` and `RecOffAvg` of `recOffPre`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest)
open Quantum.Xmss (X Z blocks trunc128 trunc128_eq bitsEquiv two_pow_div_card_X)
open Quantum.Xmss.Hybrid (uavg uavg_mono uavg_add uavg_const_mul totalWeight_le_totalWeight
  totalWeight_add_weight totalWeight_const_mul_weight)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR extWeight card_fiber_trunc128_add
  card_filter_le_of_imp totalWeight_le_of_forallQueries querySupportedOn_traceRight uavg_const_le
  NoBot NoBotDb)

namespace Quantum.Sphincs.Assembly

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default
size. -/
set_option synthInstance.maxSize 2000

/-! ## The split of a `RecBad` state at a trial read -/

section split

variable (p : Pub) (v : (s : HPos) → XD s)

/-- Adding a value keeps the agreement of two rates' digests. -/
private theorem rbs_trunc128_add_congr {a b : X} (h : trunc128 a = trunc128 b) (y : X) :
    trunc128 (a + y) = trunc128 (b + y) := by
  rw [trunc128_eq, trunc128_eq] at h
  rw [trunc128_eq, trunc128_eq]
  have h' := (bitsEquiv 128).symm.injective h
  refine congrArg (bitsEquiv 128).symm (funext fun j ↦ ?_)
  rw [Pi.add_apply, Pi.add_apply, congrFun h' j]

/-- **A trial block's one-block tail is at its key's encoding slot.** -/
theorem slotOf_encBlk (K : Key) (m : Digest) (n : EncodingCounter) :
    slotOf (evData p v).pk [encBlk p K m n] = some (.enc K.1 K.2.1 K.2.2) := by
  have hb : blocks (encIn p K m n) = [encBlk p K m n] := blocks_encIn p K m n
  have hlen : (encIn p K m n).length < 136 := by
    rw [length_encIn]
    norm_num
  rw [← hb, ← Quantum.Xmss.absorbTail_blocks_of_lt (Equiv.refl _) hlen]
  exact slotOf_encoding _ _ K.1 K.2.1 K.2.2 m n

/-- The trial's own one-block tail `[t.x]` reaches the read cell `z` in the union of the hardwired
and the database cells, with a rate of the trial's digest (`trialOf` names a trial only up to its
rate's untruncated bits). -/
def TrialOn (z : Z) (t : TrialPt) (s : HwReg X Z (Mem HPos)) : Prop :=
  ∃ xi, trunc128 xi = trunc128 t.xi ∧ IsHeadTail p.perm (union s.2.1 s.1) [t.x] z xi

/-- **A recorded value hitting the target of the trial's tail**: the cell `z` not hardwired,
recorded with a value that makes the trial's tail `[t.x]` reach its Struct or Enc target. -/
def RecHit (z : Z) (t : TrialPt) (s : HwReg X Z (Mem HPos)) : Prop :=
  s.2.1.1 z = none ∧ ∃ y, s.1.1 z = some y ∧
    (evData p v).sphTgtHw s.2.1 s.2.2 [t.x] = some (trunc128 (t.xi + y))

/-- **A recorded cell off the trial's path**: the cell `z` recorded, not hardwired, and the trial's
own tail does not reach it in the union. -/
def RecOff (z : Z) (t : TrialPt) (s : HwReg X Z (Mem HPos)) : Prop :=
  s.2.1.1 z = none ∧ s.1.1 z ≠ none ∧ ¬ TrialOn p z t s

/-- **A `RecBad` state at a trial of an encoding slot hits the target of the trial's tail, or is
off its path** (`tgt_eq_of_emptied` for Struct and Enc; the coverage part needs an `H_msg` call-0
tail). -/
theorem recBad_cases {z : Z} {t : TrialPt} {s : HwReg X Z (Mem HPos)}
    (hslot : slotOf (evData p v).pk [t.x] = some (.enc t.K.1 t.K.2.1 t.K.2.2))
    (h : RecBad p v z s) : RecHit p v z t s ∨ RecOff p z t s := by
  obtain ⟨hW, hD, hb, hnb⟩ := h
  by_cases hon : TrialOn p z t s
  · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hD
    obtain ⟨xi, hxi, hht⟩ := hon
    have hnT : ((Function.update s.1.1 z none, s.1.2.1, s.1.2.2), s.2.1, s.2.2) ∉
        TgtBad (evData p v) progCap := fun h' ↦ hnb (Or.inl h')
    have hnC : ((Function.update s.1.1 z none, s.1.2.1, s.1.2.2), s.2.1, s.2.2) ∉
        CovBadOf (evData p v) progCap := fun h' ↦ hnb (Or.inr h')
    rcases (show (s.1, s.2.1, s.2.2) ∈ TgtBad (evData p v) progCap ∨
        (s.1, s.2.1, s.2.2) ∈ CovBadOf (evData p v) progCap from hb) with hb' | hb'
    · refine .inl ⟨hW, y, hy, ?_⟩
      rw [tgt_eq_of_emptied (D := s.1) (W := s.2.1) (m := s.2.2) hW hy hb' hnT hht,
        rbs_trunc128_add_congr hxi y]
    · exfalso
      have hc := tgt_eq_of_emptied (D := s.1) (W := s.2.1) (m := s.2.2) hW hy hb' hnC hht
      obtain ⟨-, R, M, hs, -⟩ := covTgt_eq_some_iff.1 hc
      rw [hslot] at hs
      cases hs
  · exact .inr ⟨hW, hD, hon⟩

/-- **A re-grind**: the trial's key is selected, by a block of the same search as the trial's. -/
def RegrindSel (t : TrialPt) (m : Selections) : Prop :=
  ∃ sel, m t.K = some sel ∧ SameGrind p t.K t.x sel.1

/-- `RecHit` at a re-grind of a selected key. -/
def RecHitA (z : Z) (t : TrialPt) (s : HwReg X Z (Mem HPos)) : Prop :=
  RecHit p v z t s ∧ RegrindSel p t s.2.2.2

/-- **A hit needs the trial's key selected**: the target of a tail at an encoding slot is the
selected digest. -/
theorem sel_of_recHit {z : Z} {t : TrialPt} {s : HwReg X Z (Mem HPos)}
    (hslot : slotOf (evData p v).pk [t.x] = some (.enc t.K.1 t.K.2.1 t.K.2.2))
    (h : RecHit p v z t s) : ∃ sel, s.2.2.2 t.K = some sel := by
  obtain ⟨-, y, -, ht⟩ := h
  obtain ⟨s', hs', hst | hst⟩ := sphTgt_eq_some_iff.1 ht
  · obtain rfl := Option.some.inj (hslot.symm.trans hs')
    exact (structTgt_eq_some_iff.1 hst).1.1.elim
  · obtain ⟨l, τ, e, x, rfl, hc, -⟩ := encTgt_eq_some_iff.1 hst
    obtain ⟨h1, h2, h3⟩ := Slot.enc.inj (Option.some.inj (hslot.symm.trans hs'))
    refine ⟨(x, trunc128 (t.xi + y)), ?_⟩
    rw [show t.K = (l, τ, e) from Prod.ext h1 (Prod.ext h2 h3)]
    exact hc

/-- **On KeyMsg's invariant a `RecBad` state at an allowed trial read is a re-grind hit or off the
trial's path**: no part off the re-grinds. -/
theorem recBad_of_kInv {τ : KMode} {c : HwRead X Z (Mem HPos)} (hc : KeyRd p τ c)
    (ht : IsTrial trialUpd c) {s : HwReg X Z (Mem HPos)} (hs : s ∈ KInv p v τ)
    (h : RecBad p v (trialOf trialUpd c).1 s) :
    RecHitA p v (trialOf trialUpd c).1 (trialOf trialUpd c).2 s ∨
      RecOff p (trialOf trialUpd c).1 (trialOf trialUpd c).2 s := by
  obtain ⟨n, hn⟩ := trial_of_kInv p v hc ht hs
  have hslot : slotOf (evData p v).pk [(trialOf trialUpd c).2.x] =
      some (.enc (trialOf trialUpd c).2.K.1 (trialOf trialUpd c).2.K.2.1
        (trialOf trialUpd c).2.K.2.2) := by
    rw [hn]
    exact slotOf_encBlk p v _ _ n
  rcases recBad_cases p v hslot h with h' | h'
  · obtain ⟨sel, hsel⟩ := sel_of_recHit p v hslot h'
    exact .inl ⟨h', sel, hsel, sameGrind_of_kInv p v hc ht hs hsel⟩
  · exact .inr h'

/-- **The content predicate of `RecHitA`**, on the hardwired cells and the memory `w` and the cell
content `o`. -/
def hitG (z : Z) (t : TrialPt) (w : Hw X Z × Mem HPos) (o : Option X) : Prop :=
  w.1.1 z = none ∧ RegrindSel p t w.2.2 ∧ ∃ y, o = some y ∧
    (evData p v).sphTgtHw w.1 w.2 [t.x] = some (trunc128 (t.xi + y))

theorem recHitA_iff (z : Z) (t : TrialPt) (s : HwReg X Z (Mem HPos)) :
    RecHitA p v z t s ↔ hitG p v z t s.2 (s.1.1 z) :=
  ⟨fun ⟨⟨h1, y, h2, h3⟩, h4⟩ ↦ ⟨h1, h4, y, h2, h3⟩, fun ⟨h1, h4, y, h2, h3⟩ ↦ ⟨⟨h1, y, h2, h3⟩, h4⟩⟩

theorem hitG_none (z : Z) (t : TrialPt) (w : Hw X Z × Mem HPos) : ¬ hitG p v z t w none :=
  fun ⟨_, _, _, h, _⟩ ↦ Option.some_ne_none _ h.symm

/-- A value with `hitG` makes the trial's tail reach its target. -/
theorem hitG_some_tgt {z : Z} {t : TrialPt} {w : Hw X Z × Mem HPos} {y : X}
    (h : hitG p v z t w (some y)) :
    (evData p v).sphTgtHw w.1 w.2 [t.x] = some (trunc128 (t.xi + y)) := by
  obtain ⟨-, -, y', hy, hd⟩ := h
  rw [Option.some_injective _ hy]
  exact hd

/-- At most `2^960` values satisfy `hitG` (one target digest). -/
theorem card_hitG_le (z : Z) (t : TrialPt) (w : Hw X Z × Mem HPos)
    [DecidablePred fun y : X ↦ hitG p v z t w (some y)] :
    (Finset.univ.filter fun y : X ↦ hitG p v z t w (some y)).card ≤ 2 ^ 960 := by
  rcases hT : (evData p v).sphTgtHw w.1 w.2 [t.x] with _ | d
  · have h0 : (Finset.univ.filter fun y : X ↦ hitG p v z t w (some y)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun y _ h ↦ by
        have h' := hitG_some_tgt p v h
        rw [hT] at h'
        exact Option.some_ne_none _ h'.symm
    rw [h0, Finset.card_empty]
    exact Nat.zero_le _
  · exact card_filter_le_of_imp (card_fiber_trunc128_add t.xi d) fun y hy ↦ by
      have h' := hitG_some_tgt p v hy
      rw [hT] at h'
      exact (Option.some_injective _ h').symm

open scoped Classical in
/-- **The value fraction of `hitG`**: at most `2^-128` (one target digest). -/
theorem cellFrac_hitG_le (z : Z) (t : TrialPt) (w : Hw X Z × Mem HPos) :
    cellFrac (hitG p v z t w) ≤ (2 ^ 128 : ℝ)⁻¹ := by
  unfold cellFrac
  rw [← two_pow_div_card_X]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_hitG_le p v z t w) (Nat.cast_nonneg _)

end split

/-! ## The weights and their sums along the prefix -/

section weights

variable (p : Pub) (v : (s : HPos) → XD s)

open scoped Classical in
/-- The `RecHitA` mass of a trial read port (`0` at the other read ports). -/
noncomputable def recHitAW (c : HwRead X Z (Mem HPos))
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal (∑ q, if RecHitA p v (trialOf trialUpd c).1
    (trialOf trialUpd c).2 q.2 then (σ q q).re else 0) else 0

open scoped Classical in
/-- The `RecOff` mass of a trial read port. -/
noncomputable def recOffW (c : HwRead X Z (Mem HPos))
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal (∑ q, if RecOff p (trialOf trialUpd c).1
    (trialOf trialUpd c).2 q.2 then (σ q q).re else 0) else 0

open scoped Classical in
/-- **The decompressed `RecHitA` weight of a trial read port**: the weight of the decompressed
event "the cell's content satisfies `hitG`". -/
noncomputable def decHitAW (c : HwRead X Z (Mem HPos))
    (σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal ((((1 : Matrix Unit Unit ℂ) ⊗ₖ
    hwDecProj {s : HwReg X Z (Mem HPos) | hitG p v (trialOf trialUpd c).1 (trialOf trialUpd c).2
      s.2 (s.1.1 (trialOf trialUpd c).1)}) * σ).trace.re) else 0

/-- `recHitAW` summed along the prefix. -/
noncomputable def recHitAPre (pol : DigestPolicy) (A : SAdversary) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (recHitAW p v) fun _ _ ↦ 0))
    (prefixR pol A p v) initR

/-- `recOffW` summed along the prefix. -/
noncomputable def recOffPre (pol : DigestPolicy) (A : SAdversary) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (recOffW p) fun _ _ ↦ 0))
    (prefixR pol A p v) initR

/-- **The decompressed re-grind hit weight**, summed along the prefix. -/
noncomputable def decHitAPre (pol : DigestPolicy) (A : SAdversary) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (decHitAW p v) fun _ _ ↦ 0))
    (prefixR pol A p v) initR

/-- A real sum over the two parts of `RecBad`, on the support. -/
theorem sum_ite_le_two_of {n : Type} [Fintype n] (P Q R : n → Prop) [DecidablePred P]
    [DecidablePred Q] [DecidablePred R] (f : n → ℝ) (hf : ∀ a, 0 ≤ f a)
    (h : ∀ a, f a ≠ 0 → P a → Q a ∨ R a) :
    ∑ a, (if P a then f a else 0) ≤
      ∑ a, (if Q a then f a else 0) + ∑ a, (if R a then f a else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  have := hf a
  by_cases h0 : f a = 0
  · rw [h0]
    split_ifs <;> simp
  by_cases hP : P a
  · rcases h a h0 hP with hQ | hR
    · rw [ite_eq_left hP, ite_eq_left hQ]
      split_ifs <;> linarith
    · rw [ite_eq_left hP, ite_eq_left hR]
      split_ifs <;> linarith
  · rw [ite_eq_right hP]
    split_ifs <;> linarith

/-- **On KeyMsg's invariant the `RecBad` mass of an allowed read port splits** into the re-grind
hits and the cells off the trial's path. -/
theorem recBadW_le_of_kInv {τ : KMode} {c : HwRead X Z (Mem HPos)} (hc : KeyRd p τ c)
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef)
    (hs : QuerySupportedOn (fun m : Unit × HwReg X Z (Mem HPos) ↦ m.2) (KInv p v τ) σ) :
    recBadW p v c σ ≤ recHitAW p v c σ + recOffW p c σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  unfold recBadW recHitAW recOffW
  split_ifs with ht
  · refine (ENNReal.ofReal_le_ofReal (sum_ite_le_two_of _ _ _ _ hre fun q h0 h ↦
      recBad_of_kInv p v hc ht (hs q q fun h' ↦ h0 (by rw [h', Complex.zero_re])).1 h)).trans
        ENNReal.ofReal_add_le
  · simp

/-- **`recBadPre` splits** into the re-grind hits and the cells off the trial's path (KeyMsg's
`forallQueries_selKey`): no part off the re-grinds. -/
theorem recBadPre_le (pol : DigestPolicy) (A : SAdversary) :
    recBadPre pol A p v ≤ recHitAPre p v pol A + recOffPre p v pol A := by
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments
    (fun i σ ↦ ∃ τ, kOkZ p τ i ∧
      QuerySupportedOn (fun m : (recHwSpec X Z HPos Selections).In i × HwReg X Z (Mem HPos) ↦ m.2)
        (KInv p v τ) σ)
    (fun _ _ _ ⟨τ, hok, hσ⟩ ↦ ⟨τ, hok, querySupportedOn_traceRight hσ⟩)
    (w' := fun i σ ↦ extWeight (hwCost (recHitAW p v) fun _ _ ↦ 0) i σ +
      extWeight (hwCost (recOffW p) fun _ _ ↦ 0) i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR pol A p v) initR_posSemidef
    (forallQueries_selKey p v pol A)).trans_eq
      (totalWeight_add_weight (runtimeR m0R) .instruments _ _ (prefixR pol A p v) initR)
  rcases i with ((q | c) | c) | T
  · exact zero_le
  · obtain ⟨τ, hok, hs⟩ := hI
    exact recBadW_le_of_kInv p v hok hσ hs
  · exact zero_le
  · exact zero_le

end weights

/-! ## The conversion of the re-grind part -/

section convert

variable (p : Pub) (v : (s : HPos) → XD s)

/-- **The conversion term** of the re-grind part: `2 · 2^-128` per unit of trial-read trace, at
most `clsCap` of it. -/
noncomputable def recConv : ℝ≥0∞ :=
  ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹) * clsCap

/-- `recConv ≤ 2^-59` (`clsCap ≤ 2^68`). -/
theorem recConv_le : recConv ≤ ENNReal.ofReal (1 / 2 ^ 59) := by
  have hc : (clsCap : ℝ) ≤ 2 ^ 68 := by
    have := progCap_add_le (q := 0) (Nat.zero_le _)
    exact_mod_cast (by omega : clsCap ≤ 2 ^ 68)
  unfold recConv
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hc (by positivity)).trans ?_)
  norm_num

open scoped Classical in
/-- **A trial read port's `RecHitA` mass against its decompressed weight**: on a port input with
no decompressed `⊥`, `recHitAW ≤ 2 decHitAW + 2 · 2^-128 tr σ` (leanXMSS's `re_trace_recH_wm_le`
with `hitG`, `cellFrac_hitG_le`). -/
theorem recHitAW_le (c : HwRead X Z (Mem HPos))
    {σ : Matrix (Unit × HwReg X Z (Mem HPos)) (Unit × HwReg X Z (Mem HPos)) ℂ}
    (hσ : σ.PosSemidef)
    (hnb : QuerySupportedOn (fun m : Unit × HwReg X Z (Mem HPos) ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Mem HPos)) σ)) :
    recHitAW p v c σ ≤ 2 * decHitAW p v c σ +
      ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹) * ENNReal.ofReal σ.trace.re := by
  unfold recHitAW decHitAW
  split_ifs with ht
  · generalize trialOf trialUpd c = zt
    obtain ⟨z, t⟩ := zt
    have hnb' : QuerySupportedOn (fun m : Unit × HwReg X Z (Mem HPos) ↦ m.2)
        {s | (s.1.1 z).isSome}
        (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Mem HPos)) σ) :=
      fun a b h ↦ ⟨(show NoBotDb a.2.1 from (hnb a b h).1).1 z,
        (show NoBotDb b.2.1 from (hnb a b h).2).1 z⟩
    have h := re_trace_recH_wm_le z (hitG p v z t) (hitG_none p v z t) (cellFrac_hitG_le p v z t)
      hσ hnb'
    have hl : (((1 : Matrix Unit Unit ℂ) ⊗ₖ diagonal fun s : HwReg X Z (Mem HPos) ↦
        if hitG p v z t s.2 (s.1.1 z) then 1 else 0) * σ).trace.re =
          ∑ q, if RecHitA p v z t q.2 then (σ q q).re else 0 := by
      rw [rb_one_kron_diagonal, rb_trace_diagonal_mul, Complex.re_sum]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      by_cases hq : RecHitA p v z t q.2
      · rw [ite_eq_left hq, ite_eq_left ((recHitA_iff p v z t q.2).1 hq), one_mul]
      · rw [ite_eq_right hq, ite_eq_right fun h ↦ hq ((recHitA_iff p v z t q.2).2 h), zero_mul,
          Complex.zero_re]
    rw [hl] at h
    calc ENNReal.ofReal (∑ q, if RecHitA p v z t q.2 then (σ q q).re else 0)
        ≤ ENNReal.ofReal (2 * (((1 : Matrix Unit Unit ℂ) ⊗ₖ hwDecProj
            {s : HwReg X Z (Mem HPos) | hitG p v z t s.2 (s.1.1 z)}) * σ).trace.re +
              2 * (2 ^ 128 : ℝ)⁻¹ * σ.trace.re) :=
          ENNReal.ofReal_le_ofReal h
      _ ≤ ENNReal.ofReal (2 * (((1 : Matrix Unit Unit ℂ) ⊗ₖ hwDecProj
            {s : HwReg X Z (Mem HPos) | hitG p v z t s.2 (s.1.1 z)}) * σ).trace.re) +
            ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹ * σ.trace.re) := ENNReal.ofReal_add_le
      _ = _ := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_ofNat]
  · exact zero_le

/-- **The averaged `RecBad` bound** (leanXMSS's `RecBadAvg`): over a finite family of template
data `(P θ, V θ)` and a good set, the average of `recBadPre` is at most `τ`. -/
def RecBadAvg (pol : DigestPolicy) (A : SAdversary) {Θ : Type} [Fintype Θ] (P : Θ → Pub)
    (V : Θ → (s : HPos) → XD s) (good : Θ → Prop) [DecidablePred good] (τ : ℝ≥0∞) : Prop :=
  uavg (fun θ ↦ if good θ then recBadPre pol A (P θ) (V θ) else 0) ≤ τ

/-- **The remaining bound of the re-grind part**: the average of the decompressed re-grind hit
weight `decHitAPre` is at most `τ` (expected `0` up to static terms: in the decompressed basis a
re-grind reads the values its first grind measured). -/
def DecHitAvg (pol : DigestPolicy) (A : SAdversary) {Θ : Type} [Fintype Θ] (P : Θ → Pub)
    (V : Θ → (s : HPos) → XD s) (good : Θ → Prop) [DecidablePred good] (τ : ℝ≥0∞) : Prop :=
  uavg (fun θ ↦ if good θ then decHitAPre (P θ) (V θ) pol A else 0) ≤ τ

/-- **The remaining bound off the trial's path**: the average of `recOffPre` is at most `τ`
(about `4 / |Z|` per trial read). -/
def RecOffAvg (pol : DigestPolicy) (A : SAdversary) {Θ : Type} [Fintype Θ] (P : Θ → Pub)
    (V : Θ → (s : HPos) → XD s) (good : Θ → Prop) [DecidablePred good] (τ : ℝ≥0∞) : Prop :=
  uavg (fun θ ↦ if good θ then recOffPre (P θ) (V θ) pol A else 0) ≤ τ

variable {q : ℕ} {A : SAdversary}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **The re-grind part against its decompressed weight**: `recHitAPre ≤ 2 decHitAPre + recConv`
(CostRefined's `forallQueries_preInv` gives the inputs no decompressed `⊥`; the trial reads'
traces add up to at most `clsCap`), for every digest policy. -/
theorem recHitAPre_le (pol : DigestPolicy) :
    recHitAPre p v pol A ≤ 2 * decHitAPre p v pol A + recConv := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign pol p v
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (PreInv q) hP
    (w := extWeight (hwCost (recHitAW p v) fun _ _ ↦ 0))
    (w' := fun i σ ↦ 2 * extWeight (hwCost (decHitAW p v) fun _ _ ↦ 0) i σ +
      ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹) * extWeight (hwCost
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR pol A p v) initR_posSemidef hx).trans ?_
  · rcases i with ((p' | c) | c) | T
    · exact zero_le
    · exact recHitAW_le p v c hσ hI.2.2
    · exact zero_le
    · exact zero_le
  · refine (le_of_eq (totalWeight_add_weight (runtimeR m0R) .instruments
      (fun i σ ↦ 2 * extWeight (hwCost (decHitAW p v) fun _ _ ↦ 0) i σ)
      (fun i σ ↦ ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹) * extWeight (hwCost
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ)
      (prefixR pol A p v) initR)).trans (add_le_add (le_of_eq (totalWeight_const_mul_weight
        (runtimeR m0R) .instruments 2 (extWeight (hwCost (decHitAW p v) fun _ _ ↦ 0))
        (prefixR pol A p v) initR)) ((le_of_eq (totalWeight_const_mul_weight (runtimeR m0R)
          .instruments (ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹)) (extWeight (hwCost
            (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re))
          (prefixR pol A p v) initR)).trans ?_))
    unfold recConv
    gcongr
    exact totalWeight_calls_le (prefixR pol A p v) (clsCalls_prefixR hperm hsign pol p v)

/-- **The `RecBad` mass of the prefix**: `recBadPre ≤ 2 decHitAPre + recConv + recOffPre`, for
every digest policy and template data (no part off the re-grinds). -/
theorem recBadPre_le_parts (pol : DigestPolicy) :
    recBadPre pol A p v ≤ 2 * decHitAPre p v pol A + recConv + recOffPre p v pol A :=
  (recBadPre_le p v pol A).trans (add_le_add (recHitAPre_le p v hperm hsign pol) le_rfl)

/-- **`RecBadAvg` from the two remaining bounds** (no part off the re-grinds):
`RecBadAvg (2 τA + recConv + τO)` from `DecHitAvg τA` and `RecOffAvg τO`, `recConv ≤ 2^-59`. -/
theorem recBadAvg_of_parts (pol : DigestPolicy) {Θ : Type} [Fintype Θ] (P : Θ → Pub)
    (V : Θ → (s : HPos) → XD s) (good : Θ → Prop) [DecidablePred good] {τA τO : ℝ≥0∞}
    (hA : DecHitAvg pol A P V good τA) (hO : RecOffAvg pol A P V good τO) :
    RecBadAvg pol A P V good (2 * τA + recConv + τO) := by
  unfold RecBadAvg
  calc uavg (fun θ ↦ if good θ then recBadPre pol A (P θ) (V θ) else 0)
      ≤ uavg (fun θ ↦ 2 * (if good θ then decHitAPre (P θ) (V θ) pol A else 0) + recConv +
          (if good θ then recOffPre (P θ) (V θ) pol A else 0)) :=
        uavg_mono fun θ ↦ by
          by_cases hθ : good θ
          · simp only [hθ, ↓reduceIte]
            exact recBadPre_le_parts (P θ) (V θ) hperm hsign pol
          · simp only [hθ, ↓reduceIte, mul_zero, zero_add, add_zero]
            exact zero_le
    _ = 2 * uavg (fun θ ↦ if good θ then decHitAPre (P θ) (V θ) pol A else 0) +
          uavg (fun _ : Θ ↦ recConv) +
          uavg (fun θ ↦ if good θ then recOffPre (P θ) (V θ) pol A else 0) := by
        rw [uavg_add, uavg_add, uavg_const_mul]
    _ ≤ 2 * τA + recConv + τO :=
        add_le_add (add_le_add (by gcongr; exact hA) (uavg_const_le _)) hO

end convert

end Quantum.Sphincs.Assembly

end
