/-
  LeanVM.Protocol.EndToEnd.Front.RingSwitch

  The verifier program's ring switching specified in the doom calculus: from the Keccak
  reduction's 64 bit-slice claims on `q_keccak` to the switched claim on the stack.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.RingFidelity

/-!
# Ring switching as a specification

`ringSwitch point s` (`crates/verifier/src/ring_switch.rs:36-54` at leanVM `40f877dc`;
`crates/pcs/src/ring_switch.rs`) draws the six
coefficients `f_0, …, f_5` of the staged map `Φ` (shifts `32, 16, 8, 4, 2, 1`) and returns the
target `Σ_i x^i Φ(s_i)` and the weight `W(u) = Σ_k c_k eq(point^(2^k), u)`; the program claims
`⟨eqAbove · W, q⟩ = target` on the stack (`ringSwitchClaim`, `crates/verifier/src/lib.rs:303-311`).

The Keccak reduction leaves 64 claims `s_i = ẑ_i(point)` on the bit slices of `q_keccak`
(`KeccakGkr.slicesTrue`). With the errors `δ_i = s_i - ẑ_i(point)` and
`π_k(b) = Σ_i x^i · b_i^(2^k)` (`frobPair`), a candidate is alive after `j` coefficients
(`RingAlive`) when it satisfies the column claims and every `π_k`, `k < 2^(6 - j)`, of the errors
under the first `j` stages vanishes:

| step | alive | escape per candidate |
| --- | --- | --- |
| start | the slice claims hold (`ring_start`: `ringSwitch_injective`, all 64 `π_k`) | — |
| coefficient `j < 6` | `π_k`, `k < 2^(5 - j)`, under `j + 1` stages | `1/|E|` (`card_stage_zero_le_one`) |
| end | `π_0` under the six stages: the ring claim (`ringClaim_holds_iff`) | — |

One stage with shift `M` sends `π_k` to `π_k + f^(2^k) π_{M + k}`, so a family with some
`π_k ≠ 0`, `k < 2M`, keeps some `π_k ≠ 0`, `k < M`, for every coefficient but one. The lead is
`6 · L₀/|E|`, the six coefficients and the opening's challenges being one group.

`RingPost` is the opening's starting point (`Sound/Glue.lean`): no candidate satisfies the
column claims and the ring claim.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Ring LeanVM.Protocol.KeccakGkr
open scoped ENNReal NNReal

@[expose] public section

section Ring

variable (layout : LeanVM.Protocol.Verifier.Layout) (C : List Ev → Set (Column layout.stackLog))
  (claims : List LeanVM.Protocol.Verifier.ColumnClaim)

/-- **The ring-switching phase's postcondition**: no candidate satisfies the program's claims and
the ring claim. -/
def RingPost (r : E × (List E → E)) (h : List Ev) : Prop :=
  Doomed C (fun q ↦ ColumnClaimsHold layout claims q ∧
    StackClaim.Holds layout.stackLog (LeanVM.Protocol.Verifier.ringSwitchClaim layout r.1 r.2) q)
    h

/-- **The ring-switching phase's precondition**: no candidate satisfies the program's claims and
the 64 slice claims on its `q_keccak` (the Keccak reduction's postcondition, `KeccakPost`). -/
def RingPre (h₅ : ℕ) (pt sv : List E) (h : List Ev) : Prop :=
  Doomed C (fun q ↦ ColumnClaimsHold layout claims q ∧ slicesTrue h₅ (qkOf layout q) pt sv) h

/-- Alive after the coefficients `acc`: the column claims, and every `π_k`,
`k < 2^(6 - |acc|)`, of the slices' errors under the stages of `acc` is zero. -/
def RingAlive (h₅ : ℕ) (pt sv acc : List E) (q : Column layout.stackLog) : Prop :=
  ColumnClaimsHold layout claims q ∧ ∀ k < 2 ^ (6 - acc.length),
    frobPair Finset.univ ringW
      (fun i ↦ frobMap (stagesOf acc) (ringErr h₅ (qkOf layout q) pt sv i)) k = 0

/-- The unit `1/|E|` of the calculus is the average's weight. -/
theorem overE_one_coe : ((overE 1 : ℝ≥0) : ℝ≥0∞) = (Fintype.card E : ℝ≥0∞)⁻¹ := by
  have hc : (Fintype.card E : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [overE, Nat.cast_one, ENNReal.coe_div hc, ENNReal.coe_one, ENNReal.coe_natCast, one_div]

/-- **A coefficient's escape**: a candidate not alive becomes alive for one coefficient at
most. -/
theorem ring_escape (h₅ : ℕ) (pt sv acc : List E) (q : Column layout.stackLog)
    (hq : ¬ RingAlive layout claims h₅ pt sv acc q) :
    avgE (fun c ↦ indE (RingAlive layout claims h₅ pt sv (acc ++ [c]) q)) ≤
      ((overE 1 : ℝ≥0) : ℝ≥0∞) := by
  classical
  have hzero : avgE (fun _ : E ↦ indE False) ≤ ((overE 1 : ℝ≥0) : ℝ≥0∞) :=
    (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le
  by_cases hG : ColumnClaimsHold layout claims q
  swap
  · exact (avgE_mono fun c ↦ indE_mono (q := False) fun hc ↦ hG hc.1).trans hzero
  let b : Fin 64 → E := fun i ↦ frobMap (stagesOf acc) (ringErr h₅ (qkOf layout q) pt sv i)
  rcases Nat.lt_or_ge acc.length 6 with hlen | hlen
  · let M := 2 ^ (5 - acc.length)
    have h2M : 2 * M = 2 ^ (6 - acc.length) := by
      simp only [M, ← pow_succ']
      congr 1
      omega
    have hex : ∃ k < 2 * M, frobPair Finset.univ ringW b k ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      exact hq ⟨hG, fun k hk ↦ hall k (by rw [h2M]; exact hk)⟩
    have hcard := card_stage_zero_le_one Finset.univ ringW b M hex
    calc avgE (fun c ↦ indE (RingAlive layout claims h₅ pt sv (acc ++ [c]) q))
        ≤ avgE (fun c ↦ indE (∀ k < M,
            frobPair Finset.univ ringW (fun i ↦ b i + c * b i ^ 2 ^ M) k = 0)) :=
          avgE_mono fun c ↦ indE_mono fun hc k hk ↦ by
            have h := hc.2 k (by
              rw [List.length_append, List.length_singleton]
              simp only [M] at hk
              rwa [show 6 - (acc.length + 1) = 5 - acc.length by omega])
            rw [stagesOf_snoc acc c hlen] at h
            simp only [frobMap_append] at h
            exact h
      _ = (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun c : E ↦ ∀ k < M,
            frobPair Finset.univ ringW (fun i ↦ b i + c * b i ^ 2 ^ M) k = 0).card : ℝ≥0∞) :=
          (card_filter_eq_avgE _).symm
      _ ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * 1 := by
          gcongr
          exact_mod_cast hcard
      _ = ((overE 1 : ℝ≥0) : ℝ≥0∞) := by rw [mul_one, overE_one_coe]
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun hc ↦ hq ⟨hG, fun k hk ↦ ?_⟩).trans hzero
    have h := hc.2 k (by
      rw [List.length_append, List.length_singleton]
      rwa [show 6 - (acc.length + 1) = 6 - acc.length by omega])
    rwa [stagesOf_snoc_of_le acc c hlen] at h

/-- **The start**: a candidate whose slice claims fail is not alive before the coefficients,
ring switching being injective (`ringSwitch_injective`). -/
theorem ring_start (h₅ : ℕ) (pt sv : List E) (hl : pt.length = h₅ + 6 ∧ sv.length = 64)
    (q : Column layout.stackLog)
    (hq : ¬ (ColumnClaimsHold layout claims q ∧ slicesTrue h₅ (qkOf layout q) pt sv)) :
    ¬ RingAlive layout claims h₅ pt sv ([] : List E) q := by
  rintro ⟨hG, hπ⟩
  refine hq ⟨hG, hl.1, hl.2, fun i hi ↦ ?_⟩
  have hδ := ringSwitch_injective (fun i ↦ ringErr h₅ (qkOf layout q) pt sv i)
    (fun k hk ↦ hπ k (by simpa using hk)) ⟨i, hi⟩
  exact sub_eq_zero.mp hδ

/-- **The end**: after the six coefficients, the ring claim makes a candidate alive. -/
theorem ring_end {h₅ off : ℕ} (hlay : RingLayoutHyp layout h₅ off) (pt sv ch : List E)
    (hl : pt.length = h₅ + 6 ∧ sv.length = 64) (hch : ch.length = 6) (q : Column layout.stackLog)
    (hG : ColumnClaimsHold layout claims q)
    (hclaim : StackClaim.Holds layout.stackLog
      (LeanVM.Protocol.Verifier.ringSwitchClaim layout
        (LeanVM.Protocol.Verifier.polyEval (sv.map (LeanVM.Protocol.Verifier.phiMap · ch))
          LeanVM.Protocol.Verifier.gen)
        fun rPrime ↦ LeanVM.Protocol.Verifier.ringWeight pt rPrime
          (LeanVM.Protocol.Verifier.ringCoefficients ch)) q) :
    RingAlive layout claims h₅ pt sv ch q := by
  refine ⟨hG, fun k hk ↦ ?_⟩
  rw [hch, Nat.sub_self, pow_zero, Nat.lt_one_iff] at hk
  subst hk
  have h := (ringClaim_holds_iff hlay.placement hlay.aligned hlay.fits q hl.1 hl.2 hch).mp hclaim
  rw [qkOf_eq_qkAt, hlay.placement]
  simpa only [frobPair, pow_zero, pow_one, phiMap_eq_frobMap] using h

/-- Ring switching draws the six coefficients and returns the target and the weight. -/
theorem ringSwitch_eq (point sv : List E) :
    LeanVM.Protocol.Verifier.ringSwitch point sv = VerifierProgram.sampleChallenges 6 >>= fun ch ↦
      VerifierProgram.ret (LeanVM.Protocol.Verifier.polyEval
          (sv.map (LeanVM.Protocol.Verifier.phiMap · ch)) LeanVM.Protocol.Verifier.gen,
        fun rPrime ↦ LeanVM.Protocol.Verifier.ringWeight point rPrime
          (LeanVM.Protocol.Verifier.ringCoefficients ch)) := rfl

/-- **Ring switching's specification** at a point and slices of the right lengths, from the
Keccak reduction's postcondition to `RingPost`: lead `6 · L₀/|E|` plus the follower's `T`. -/
noncomputable def ringSpecOf {h₅ off : ℕ} (hlay : RingLayoutHyp layout h₅ off) (hst : Stable C)
    {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀) {εmax T : ℝ≥0∞} (pt sv : List E)
    (hl : pt.length = h₅ + 6 ∧ sv.length = 64) :
    Spec (LeanVM.Protocol.Verifier.ringSwitch pt sv) (RingPre layout C claims h₅ pt sv)
      (RingPost layout C claims) εmax
      ((∑ _i ∈ Finset.range 6, (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) + T) T :=
  Spec.congr (ringSwitch_eq pt sv).symm <|
    ((doomSampleN hst hcard (fun acc q ↦ RingAlive layout claims h₅ pt sv acc q)
        (fun _ ↦ ((overE 1 : ℝ≥0) : ℝ≥0∞))
        (fun acc q hq ↦ ring_escape layout claims h₅ pt sv acc q hq) 6 []).mono
        (fun _ h q hq hr ↦ ring_start layout claims h₅ pt sv hl q (h q hq) hr)
        (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun ch ↦
      (Spec.ret _).mono (fun _ hd ↦ by
          intro q hq ⟨hG, hclaim⟩
          refine hd.2 q hq ?_
          have h6 : ch.length = 6 := by simpa using hd.1
          simpa only [List.nil_append] using
            ring_end layout claims hlay pt sv ch hl h6 q hG hclaim)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

open Classical in
/-- **Ring switching's specification**, the lengths of the point and slices in the
precondition. -/
noncomputable def ringSpec {h₅ off : ℕ} (hlay : RingLayoutHyp layout h₅ off) (hst : Stable C)
    {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀) {εmax T : ℝ≥0∞} (pt sv : List E) :
    Spec (LeanVM.Protocol.Verifier.ringSwitch pt sv)
      (fun h ↦ (pt.length = h₅ + 6 ∧ sv.length = 64) ∧ RingPre layout C claims h₅ pt sv h)
      (RingPost layout C claims) εmax
      ((∑ _i ∈ Finset.range 6, (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) + T) T :=
  if hl : pt.length = h₅ + 6 ∧ sv.length = 64 then
    (ringSpecOf layout C claims hlay hst hcard pt sv hl).mono (fun _ h ↦ h.2) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ h ↦ hl h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Ring

end
end LeanVM.Protocol.EndToEnd.Front
