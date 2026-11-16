module

public import Quantum.Xmss.Assembly.RecBadMass

@[expose] public section

/-!
# The `RecHitB` mass of the randomizer trials

RecBadMass's `RecHitB` part of the `RecBad` mass: a trial's `h`-read whose recorded value makes the
trial's one-block tail hit its target, the selected digest of the trial's key, selected by a block
of another search (`¬ RegrindSel`). Its bound is moved to the decompressed basis, as RecBadMass
does for `RecHitA`.

* **Why not CwRec's moded potentials**: a search started by a reveal is charged four times each of
  its trials whose block is recorded or hardwired while a memory condition `U` on the key holds;
  here `U` would be "selected by a block outside the search". `signT` answers reused leaves, so a
  bottom key can sign a second message `m₂` after `m₁`; at a repeated reveal of the label of `m₂`
  every trial block is recorded by its first run and `U` holds, a charge of `4 · 2^32`. The
  register state at a trial read does not tell a first run from a repeated one (the memory only
  holds the revealed set and the selections), so the split must be made where the values persist:
  in the decompressed basis.
* **The conversion** (`recHitBW_le`, `recHitBPre_le`): RecBadMass's `re_trace_recH_wm_le` with the
  content predicate `hitGB` (one target digest, value fraction `2^-128`, `cellFrac_hitGB_le`):
  `recHitBPre ≤ 2 decHitBPre + recConv`.
* **The average** (`recHitBAvg_of_dec`): `RecHitBAvg A good (2 τ + recConv)` from the decompressed
  bound `DecHitBAvg A good τ`, the remaining lemma. Its route: in the decompressed basis a search's
  trial cells keep the values its first run measured (Persistence; the trial cells are
  message-domain, off the programmed cells); before its stopping trial the first run measured
  non-codeword digests, which differ from the codeword `d` selected for the key; so every run of
  the label hits `d` only at its stopping trial and only if the first run's stopping digest is
  `d`, a collision of two labels' codeword digests, `≈ 1 / |codeword digests|` per pair of labels
  of one key by the uniform first-run values (DecUniform) and the undisclosed bases.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## The content predicate of `RecHitB` -/

section content

/-- **The content predicate of `RecHitB`**, on the hardwired cells and the memory `w` and the cell
content `o`. -/
def hitGB (L : HonestTable) (z : Z) (t : TrialPt) (w : Hw X Z × Mem) (o : Option X) : Prop :=
  w.1.1 z = none ∧ ¬ RegrindSel L t w.2.2 ∧ ∃ v, o = some v ∧
    xmssTgtHw L w.1 w.2.2 [t.x] = some (trunc128 (t.xi + v))

theorem recHitB_iff (L : HonestTable) (z : Z) (t : TrialPt) (s : HwReg X Z Mem) :
    RecHitB L z t s ↔ hitGB L z t s.2 (s.1.1 z) :=
  ⟨fun ⟨⟨h1, v, h2, h3⟩, h4⟩ ↦ ⟨h1, h4, v, h2, h3⟩, fun ⟨h1, h4, v, h2, h3⟩ ↦ ⟨⟨h1, v, h2, h3⟩, h4⟩⟩

theorem hitGB_none (L : HonestTable) (z : Z) (t : TrialPt) (w : Hw X Z × Mem) :
    ¬ hitGB L z t w none := fun ⟨_, _, _, h, _⟩ ↦ Option.some_ne_none _ h.symm

/-- A value with `hitGB` makes the trial's tail reach its target. -/
theorem hitGB_some_tgt {L : HonestTable} {z : Z} {t : TrialPt} {w : Hw X Z × Mem} {y : X}
    (h : hitGB L z t w (some y)) : xmssTgtHw L w.1 w.2.2 [t.x] = some (trunc128 (t.xi + y)) := by
  obtain ⟨-, -, v, hv, hd⟩ := h
  rw [Option.some_injective _ hv]
  exact hd

/-- At most `2^960` values satisfy `hitGB` (one target digest). -/
theorem card_hitGB_le (L : HonestTable) (z : Z) (t : TrialPt) (w : Hw X Z × Mem)
    [DecidablePred fun y : X ↦ hitGB L z t w (some y)] :
    (Finset.univ.filter fun y : X ↦ hitGB L z t w (some y)).card ≤ 2 ^ 960 := by
  rcases hT : xmssTgtHw L w.1 w.2.2 [t.x] with _ | d
  · have h0 : (Finset.univ.filter fun y : X ↦ hitGB L z t w (some y)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun y _ h ↦ by
        have h' := hitGB_some_tgt h
        rw [hT] at h'
        exact Option.some_ne_none _ h'.symm
    rw [h0, Finset.card_empty]
    exact Nat.zero_le _
  · exact card_filter_le_of_imp (card_fiber_trunc128_add t.xi d) fun y hy ↦ by
      have h' := hitGB_some_tgt hy
      rw [hT] at h'
      exact (Option.some_injective _ h').symm

open scoped Classical in
/-- **The value fraction of `hitGB`**: at most `2^-128` (one target digest). -/
theorem cellFrac_hitGB_le (L : HonestTable) (z : Z) (t : TrialPt) (w : Hw X Z × Mem) :
    cellFrac (hitGB L z t w) ≤ (2 ^ 128 : ℝ)⁻¹ := by
  unfold cellFrac
  rw [← two_pow_div_card_X]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_hitGB_le L z t w) (Nat.cast_nonneg _)

end content

/-! ## The conversion to the decompressed basis -/

section convert

open scoped Classical in
/-- **The decompressed `RecHitB` weight of a trial read port**: the weight of the decompressed
event "the cell's content satisfies `hitGB`". -/
noncomputable def decHitBW (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal ((((1 : Matrix Unit Unit ℂ) ⊗ₖ
    hwDecProj {s : HwReg X Z Mem | hitGB L (trialOf trialUpd c).1 (trialOf trialUpd c).2 s.2
      (s.1.1 (trialOf trialUpd c).1)}) * σ).trace.re) else 0

/-- **The decompressed `RecHitB` weight**, summed along the prefix. -/
noncomputable def decHitBPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (decHitBW L) fun _ _ ↦ 0))
    (prefixR A L) initR

open scoped Classical in
/-- **A trial read port's `RecHitB` mass against its decompressed weight**: on a port input with
no decompressed `⊥`, `recHitBW ≤ 2 decHitBW + 2 · 2^-128 tr σ` (`re_trace_recH_wm_le` with
`hitGB`, `cellFrac_hitGB_le`). -/
theorem recHitBW_le (L : HonestTable) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hnb : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z Mem) σ)) :
    recHitBW L c σ ≤ 2 * decHitBW L c σ +
      ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹) * ENNReal.ofReal σ.trace.re := by
  unfold recHitBW decHitBW
  split_ifs with ht
  · generalize trialOf trialUpd c = zt
    obtain ⟨z, t⟩ := zt
    have hnb' : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) {s | (s.1.1 z).isSome}
        (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z Mem) σ) :=
      fun a b h ↦ ⟨(show NoBotDb a.2.1 from (hnb a b h).1).1 z,
        (show NoBotDb b.2.1 from (hnb a b h).2).1 z⟩
    have h := re_trace_recH_wm_le z (hitGB L z t) (hitGB_none L z t) (cellFrac_hitGB_le L z t) hσ
      hnb'
    have hl : (((1 : Matrix Unit Unit ℂ) ⊗ₖ diagonal fun s : HwReg X Z Mem ↦
        if hitGB L z t s.2 (s.1.1 z) then 1 else 0) * σ).trace.re =
          ∑ q, if RecHitB L z t q.2 then (σ q q).re else 0 := by
      rw [rb_one_kron_diagonal, rb_trace_diagonal_mul, Complex.re_sum]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      by_cases hq : RecHitB L z t q.2
      · rw [ite_eq_left hq, ite_eq_left ((recHitB_iff L z t q.2).1 hq), one_mul]
      · rw [ite_eq_right hq, ite_eq_right fun h ↦ hq ((recHitB_iff L z t q.2).2 h), zero_mul,
          Complex.zero_re]
    rw [hl] at h
    calc ENNReal.ofReal (∑ q, if RecHitB L z t q.2 then (σ q q).re else 0)
        ≤ ENNReal.ofReal (2 * (((1 : Matrix Unit Unit ℂ) ⊗ₖ hwDecProj {s : HwReg X Z Mem |
            hitGB L z t s.2 (s.1.1 z)}) * σ).trace.re + 2 * (2 ^ 128 : ℝ)⁻¹ * σ.trace.re) :=
          ENNReal.ofReal_le_ofReal h
      _ ≤ ENNReal.ofReal (2 * (((1 : Matrix Unit Unit ℂ) ⊗ₖ hwDecProj {s : HwReg X Z Mem |
            hitGB L z t s.2 (s.1.1 z)}) * σ).trace.re) +
            ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹ * σ.trace.re) := ENNReal.ofReal_add_le
      _ = _ := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_ofNat]
  · exact zero_le

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The `RecHitB` part against its decompressed weight**:
`recHitBPre ≤ 2 decHitBPre + recConv` (EncPorts' `forallQueries_preInv` gives the inputs no
decompressed `⊥`; the trial reads' traces add up to at most `clsCap`). -/
theorem recHitBPre_le (L : HonestTable) : recHitBPre A L ≤ 2 * decHitBPre A L + recConv := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (PreInv q) hP
    (w' := fun i σ ↦ 2 * extWeight (hwCost (decHitBW L) fun _ _ ↦ 0) i σ +
      ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹) * extWeight (hwCost
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef hx).trans ?_
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · exact recHitBW_le L c hσ hI.2.2
    · exact zero_le
    · exact zero_le
  · refine (le_of_eq (totalWeight_add_weight (runtimeR m0R) .instruments
      (fun i σ ↦ 2 * extWeight (hwCost (decHitBW L) fun _ _ ↦ 0) i σ)
      (fun i σ ↦ ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹) * extWeight (hwCost
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ)
      (prefixR A L) initR)).trans (add_le_add (le_of_eq (totalWeight_const_mul_weight
        (runtimeR m0R) .instruments 2 (extWeight (hwCost (decHitBW L) fun _ _ ↦ 0))
        (prefixR A L) initR)) ((le_of_eq (totalWeight_const_mul_weight (runtimeR m0R)
          .instruments (ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹)) (extWeight (hwCost
            (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re))
          (prefixR A L) initR)).trans ?_))
    unfold recConv
    gcongr
    exact totalWeight_calls_le (prefixR A L) (clsCalls_prefixR hperm hsign L)

end convert

/-! ## The average -/

section avg

/-- **The remaining bound of the other labels' hits**: over a good set, the average of the
decompressed `RecHitB` weight `decHitBPre` is at most `τ` (every run of a label hits the selected
digest only at its first run's stopping trial, and only on a collision of two labels' codeword
digests). -/
def DecHitBAvg (A : Adversary (X × Z)) (good : HonestTable → Prop) [DecidablePred good]
    (τ : ℝ≥0∞) : Prop :=
  uavg (fun L ↦ if good L then decHitBPre A L else 0) ≤ τ

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **`RecHitBAvg` from the decompressed bound**: `RecHitBAvg A good (2 τ + recConv)`,
`recConv ≤ 2^-60`. -/
theorem recHitBAvg_of_dec (good : HonestTable → Prop) [DecidablePred good] {τ : ℝ≥0∞}
    (h : DecHitBAvg A good τ) : RecHitBAvg A good (2 * τ + recConv) := by
  unfold RecHitBAvg
  calc uavg (fun L ↦ if good L then recHitBPre A L else 0)
      ≤ uavg (fun L ↦ 2 * (if good L then decHitBPre A L else 0) + recConv) :=
        uavg_mono fun L ↦ by
          by_cases hL : good L
          · simp only [hL, ↓reduceIte]
            exact recHitBPre_le hperm hsign L
          · simp only [hL, ↓reduceIte, mul_zero, zero_add]
            exact zero_le
    _ = 2 * uavg (fun L ↦ if good L then decHitBPre A L else 0) + uavg (fun _ ↦ recConv) := by
        rw [uavg_add, uavg_const_mul]
    _ ≤ 2 * τ + recConv := add_le_add (by gcongr; exact h) (uavg_const_le _)

end avg

end Quantum.Xmss.Assembly

end
