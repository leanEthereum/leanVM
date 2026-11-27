module

public import LeanDa.Straight
public import LeanDa.WithHash

@[expose] public section

/-!
# The straight-line verdict's bound

The simulated world with a verdict after the challenges of the adversary's root (`idealT`: `H`
and the draws random oracles, the adversary's permutation calls simulated) is bounded for the
straight-line verdict (`tailH`, `LeanDa.Straight`): a true verdict is a bad cache of the world
with a random oracle of the draws per root and label (`not_good_of_tail`), whose probability is
bounded phase by phase (`prob_world_not_good_le`): the adversary's at most `2 Q + 1` queries, `Q`
of them of draws, by the bad-event budget; the verifier's reading of its root's draws, one fresh
try; the verdict's hashes, by the budget again (`prT_idealT_tailH_le`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA; the
straight-line argument is built on his notions (his arguments of knowledge and their extractors,
the form of his code-binding game).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex PqDas
open Common.Duplex (GSpec hP gaP)
open scoped ENNReal

namespace LeanDa

/-! ## The simulated world with a verdict -/

section Ideal

variable (r : ℕ) {Crs Proof : Type} {rel : Unit × Common.DigestBytes × MembershipChallenge → (Fin (r * 128) → Cell) → Bool}
  (ps : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Crs
      Proof rel)
  (ext : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell)
      Crs Proof)

/-- **The simulated world with a verdict `T`** after the challenges of the adversary's root. -/
noncomputable def idealT (A : CodeBindingAdvB r Crs Proof) (crs : Crs)
    (T : CbOut r Proof → MembershipChallenge → OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) Bool) :
    ProbComp Bool :=
  (simulateQ (GSpec (List UInt8) DigestBytes Common.DigestBytes Draw nLabels).romImpl
    (advSim r A crs >>= fun out ↦ readVec (Msg := List UInt8) (Dg := DigestBytes) out.1.1 >>= fun l ↦
      simulateQ embG (T out l))).run' ∅

/-! ## The verdict in the straight-line world -/

/-- **The verdict is at most a bad cache**, the draws read at all labels. -/
theorem prT_tailL_le (hr : r ≤ maxRows) (A : CodeBindingAdvB r Crs Proof) (crs : Crs) (L : List (Fin nLabels))
    (hlen : L.length = nLabels) (hidx : ∀ i (hi : i < L.length), (L[i]).val = i) :
    Pr{let b ← (simulateQ GW.romImpl (advSim r A crs >>= tailL r ps ext L crs)).run' ∅}[b = true] ≤
      Pr{let z ← (simulateQ GW.romImpl (advSim r A crs >>= tailL r ps ext L crs)).run ∅}[
        ¬ Good r z.2] := by
  rw [StateT.run'_eq, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun z hz hz1 ↦ ?_
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨w, -, hz⟩ := hz
  exact not_good_of_tail r ps ext hr L hlen hidx crs w.1 w.2 hz hz1

/-! ## The world's queries -/

/-- `H` among coins and `H`, one each. -/
def tCount : (unifSpec + roSpec (List UInt8) DigestBytes).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem isWeightBound_walkM {ι : Type} {spec : OracleSpec.{0, 0} ι}
    (H : List UInt8 → OracleComp spec Common.DigestBytes) (w : ι → ℕ) (hH : ∀ a, QueryCostAtMost (H a) w 1)
    (path : List Common.DigestBytes) : ∀ (idx : ℕ) (node : Common.DigestBytes),
      QueryCostAtMost (walkMWithHash H idx node path) w path.length := by
  induction path with
  | nil => intro idx node; exact isWeightBound_pure _ _ _
  | cons s rest ih =>
    intro idx node
    exact ((hH _).bind fun _ ↦ ih _ _).mono (by simp only [List.length_cons]; omega)

theorem isWeightBound_verifyCellM {ι : Type} {spec : OracleSpec.{0, 0} ι}
    (H : List UInt8 → OracleComp spec Common.DigestBytes) (w : ι → ℕ) (hH : ∀ a, QueryCostAtMost (H a) w 1)
    (com : Common.DigestBytes) (p : Fin (r * 128)) (x : Cell) (τ : ByteOpening) :
    QueryCostAtMost (verifyCellMWithHash H r com p x τ) w (τ.path.length + 2) :=
  ((hH _).bind fun _ ↦ (isWeightBound_walkM H w hH _ _ _).bind fun _ ↦
    isWeightBound_pure _ _ 0).mono (by simp only [List.length_append, List.length_singleton]; omega)

theorem isWeightBound_tailH (crs : Crs) (out : CbOut r Proof) (l : MembershipChallenge) :
    QueryCostAtMost (tailH r ps ext crs out l) tCount (commitCalls r + (9 + logMaxRows)) := by
  classical
  have h1 : ∀ a, QueryCostAtMost (LeanDa.hH a) tCount 1 := fun a ↦
    isWeightBound_query (spec := unifSpec + roSpec (List UInt8) DigestBytes) tCount (.inr a)
  have hc := isWeightBound_commitCellsM LeanDa.hH tCount 1 1 (fun a b ↦ h1 _) (fun x ↦ h1 _)
    (ext crs ((), out.1.1, l) out.1.2)
  have hc' : QueryCostAtMost (commitCellsMWithHash LeanDa.hH (ext crs ((), out.1.1, l) out.1.2)) tCount
      (commitCalls r) := hc.mono (le_of_eq (by ring))
  unfold tailH
  refine hc'.bind fun root ↦ ?_
  split_ifs
  · split
    · split_ifs with hlen
      · exact (isWeightBound_verifyCellM r LeanDa.hH tCount h1 _ _ _ _).mono (by omega)
      · exact isWeightBound_pure _ _ _
    · exact isWeightBound_pure _ _ _
  · exact isWeightBound_pure _ _ _
  · exact isWeightBound_pure _ _ _

theorem isWeightBound_embG_h {α : Type} {Y : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α}
    {N : ℕ} (h : QueryCostAtMost Y tCount N) :
    QueryCostAtMost (simulateQ (embG (Root := Common.DigestBytes) (Z := Draw) (n := nLabels)) Y) hgCalls N :=
  isWeightBound_simulateQ _ tCount hgCalls (fun t ↦ by
    rcases t with k | a
    · exact isWeightBound_query hgCalls (.inl k)
    · exact isWeightBound_query hgCalls (.inr (.inl a))) h

theorem isWeightBound_embG_g {α : Type} (Y : OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) α) :
    QueryCostAtMost (simulateQ (embG (Root := Common.DigestBytes) (Z := Draw) (n := nLabels)) Y)
      gwCalls 0 :=
  isWeightBound_simulateQ _ (fun _ ↦ 0) _ (fun t ↦ by
    rcases t with k | a
    · exact isWeightBound_query gwCalls (.inl k)
    · exact isWeightBound_query gwCalls (.inr (.inl a))) (QueryCostAtMost.zero_weight Y)

theorem hgCalls_eq : (fun t ↦ hCallsG t + gCalls (Msg := List UInt8) (Dg := DigestBytes)
    (Root := Common.DigestBytes) (Z := Draw) (n := nLabels) t) = hgCalls := by
  funext t
  rcases t with k | m | x <;> rfl

/-- **The simulated adversary makes at most `2 Q + 1` queries of `H` or the challenges, `Q` of
them of the challenges.** -/
theorem isWeightBound_advSim (A : CodeBindingAdvB r Crs Proof) (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r ps A) permCalls2 Q) (crs : Crs)
    (hcrs : crs ∈ support ps.setup) :
    QueryCostAtMost (advSim r A crs) hgCalls (2 * Q + 1) ∧
      QueryCostAtMost (advSim r A crs)
        (gCalls (Msg := List UInt8) (Dg := DigestBytes) (Root := Common.DigestBytes) (Z := Draw) (n := nLabels)) Q := by
  have hBh := isWeightBound_advS2_h r ps A Q hQ crs hcrs
  have hPh : QueryCostAtMost (Common.SeedDuplex.hQ (St := KState) daDuplex.label >>= fun _ ↦
      advS2 keccakPadding KState.zero (A ((), crs))) hCalls (1 + Q) :=
    (isWeightBound_query hCalls (.inr (.inl daDuplex.label))).bind fun _ ↦ hBh
  have hSh := isWeightBound_run_simulateQ _ _ _ isWeightBound_simImpl_h hPh SimSt.init
  have hBf := isWeightBound_advS2 r ps A Q hQ crs hcrs
  have hPf : QueryCostAtMost (Common.SeedDuplex.hQ (St := KState) daDuplex.label >>= fun _ ↦
      advS2 keccakPadding KState.zero (A ((), crs)))
      (fCalls (Msg := List UInt8) (Dg := DigestBytes) (St := KState)) Q := by
    simpa using (isWeightBound_hQ (Dg := DigestBytes) (St := KState) daDuplex.label).bind fun _ ↦ hBf
  have hSf := isWeightBound_run_simulateQ _ _ _ (isWeightBound_simImpl (D := daDuplex)) hPf
    SimSt.init
  have h1 : QueryCostAtMost (advSim r A crs) hCallsG (1 + Q) := by
    rw [advSim, StateT.run'_eq]; exact isWeightBound_map _ hSh
  have h2 : QueryCostAtMost (advSim r A crs)
      (gCalls (Msg := List UInt8) (Dg := DigestBytes) (Root := Common.DigestBytes) (Z := Draw) (n := nLabels)) Q := by
    rw [advSim, StateT.run'_eq]; exact isWeightBound_map _ hSf
  refine ⟨?_, h2⟩
  have := h1.add_weight h2
  rw [hgCalls_eq] at this
  exact this.mono (by omega)

/-- **A bad cache after the adversary, the reading of its root's draws and the verdict**: the
adversary's queries (at most `Q₁` of `H` or the draws, `Q₂` of the draws), then one fresh try
for the reading, then the verdict's queries of `H`. -/
theorem prob_world_not_good_le (hr : r ≤ maxRows) (A : CodeBindingAdvB r Crs Proof) (crs : Crs)
    (L : List (Fin nLabels))
    (hread : ∀ d c, Good r c → Pr{let z ← (simulateQ GW.romImpl (readL L d)).run c}[¬ Good r z.2] ≤
      (2 ^ 13 - 1) / 2 ^ 128)
    (N Q₁ Q₂ Q₃ : ℕ) (ha : QueryCostAtMost (advSim r A crs) hgCalls Q₁)
    (hg : QueryCostAtMost (advSim r A crs) gwCalls Q₂)
    (ht : ∀ out l, QueryCostAtMost (simulateQ (embG (Root := Common.DigestBytes) (Z := Draw)
      (n := nLabels)) (tailH r ps ext crs out l)) hgCalls Q₃) (hN : Q₁ + 1 + Q₃ ≤ N) :
    Pr{let z ← (simulateQ GW.romImpl (advSim r A crs >>= tailL r ps ext L crs)).run ∅}[
        ¬ Good r z.2] ≤
      Q₁ * (65 * N / 2 ^ 256) + Q₂ * ((2 ^ 13 - 1) / 2 ^ 138) +
        ((2 ^ 13 - 1) / 2 ^ 128 + Q₃ * (65 * N / 2 ^ 256)) := by
  have hf0 : GFin ∅ := ⟨by simp [domH], by simp [domG]⟩
  have hs0 : gSize ∅ = 0 := by simp [gSize, domH, domG]
  rw [simulateQ_bind, StateT.run_bind]
  have hadv := prob_run_not_good_le r hr _ ∅ (good_empty r) hf0 N Q₁ Q₂ ha hg (by omega)
  refine (prEvent_bind_le_of_good _ _ (fun p ↦ ¬ Good r p.2) _ _ fun p hp hgp ↦ ?_).trans
    (add_le_add hadv le_rfl)
  simp only [not_not] at hgp
  obtain ⟨hfp, hsp⟩ := run_gFin_gSize _ Q₁ ha ∅ hf0 p hp
  rw [tailL, simulateQ_bind, StateT.run_bind]
  refine (prEvent_bind_le_of_good _ _ (fun q ↦ ¬ Good r q.2) _ _ fun q hq hgq ↦ ?_).trans
    (add_le_add (hread _ _ hgp) le_rfl)
  simp only [not_not] at hgq
  obtain ⟨hfq, hsq⟩ := readL_gFin_gSize L _ p.2 hfp hq
  have htail := prob_run_not_good_le r hr _ q.2 hgq hfq N Q₃ 0 (ht p.1 q.1)
    (isWeightBound_embG_g _) (by omega)
  refine htail.trans (le_of_eq ?_)
  simp

theorem finRange_getElem_val (n : ℕ) : ∀ i (hi : i < (List.finRange n).length),
    ((List.finRange n)[i]).val = i := fun i hi ↦ by simp

/-- **The straight-line verdict's probability**, for an adversary of `Q` permutation calls and
`r ≤ maxRows` rows: at most `N · 65 N / 2^256 + Q · 2^-10 · (2^13 - 1) / 2^128 + (2^13 - 1) / 2^128`
for `N = 2 Q + 2^20`: the hash's bad events, a fresh draw the adversary's call makes selected and
accepting, and the one fresh try of the verifier's nonce search. -/
theorem prT_idealT_tailH_le (A : CodeBindingAdvB r Crs Proof) (Q : ℕ) (hr : r ≤ maxRows)
    (crs : Crs) (ha : QueryCostAtMost (advSim r A crs) hgCalls (2 * Q + 1))
    (hg : QueryCostAtMost (advSim r A crs) gwCalls Q) :
    prT (idealT r A crs (tailH r ps ext crs)) ≤
      ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) * (65 * ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        (Q * ((2 ^ 13 - 1) / 2 ^ 138) + (2 ^ 13 - 1) / 2 ^ 128) := by
  have hL : logMaxRows = 5 := rfl
  have hN : maxRows = 32 := rfl
  have hread : ∀ d c, Good r c →
      Pr{let z ← (simulateQ GW.romImpl (readL (List.finRange nLabels) d)).run c}[¬ Good r z.2] ≤
        (2 ^ 13 - 1) / 2 ^ 128 := fun d c hc ↦ by
    rw [← readVec_eq_readL]; exact prob_readVec_not_good_le r hr d c hc
  have hT : idealT r A crs (tailH r ps ext crs) =
      (simulateQ GW.romImpl (advSim r A crs >>=
        tailL r ps ext (List.finRange nLabels) crs)).run' ∅ := by
    unfold idealT tailL
    simp only [readVec_eq_readL]
  have h1 := prT_tailL_le r ps ext hr A crs (List.finRange nLabels) (List.length_finRange)
    (finRange_getElem_val nLabels)
  have h2 := prob_world_not_good_le r ps ext hr A crs (List.finRange nLabels) hread
    (2 * Q + 2 ^ 20) (2 * Q + 1) Q (commitCalls r + (9 + logMaxRows)) ha hg
    (fun out l ↦ isWeightBound_embG_h (isWeightBound_tailH r ps ext crs out l))
    (by unfold commitCalls; omega)
  rw [prT, hT]
  refine h1.trans (h2.trans ?_)
  set x : ℝ≥0∞ := 65 * ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 256
  have hQ : ((2 * Q + 1 : ℕ) : ℝ≥0∞) + ((commitCalls r + (9 + logMaxRows) : ℕ) : ℝ≥0∞) ≤
      ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_add]; exact_mod_cast (by unfold commitCalls; omega)
  calc ((2 * Q + 1 : ℕ) : ℝ≥0∞) * x + (Q : ℝ≥0∞) * ((2 ^ 13 - 1) / 2 ^ 138) +
        ((2 ^ 13 - 1) / 2 ^ 128 + ((commitCalls r + (9 + logMaxRows) : ℕ) : ℝ≥0∞) * x)
      = (((2 * Q + 1 : ℕ) : ℝ≥0∞) + ((commitCalls r + (9 + logMaxRows) : ℕ) : ℝ≥0∞)) * x +
          ((Q : ℝ≥0∞) * ((2 ^ 13 - 1) / 2 ^ 138) + (2 ^ 13 - 1) / 2 ^ 128) := by ring
    _ ≤ _ := by gcongr

end Ideal

/-! ## The arithmetic of the bound -/

/-- The duplex lemma's term for `Q` calls of `F`. -/
noncomputable abbrev dupTerm (Q : ℕ) : ℝ≥0∞ :=
  ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) * (2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) * (2 ^ 576 : ℝ≥0∞)⁻¹)

end LeanDa
