module

public import LeanDa.Straight
public import LeanDa.WithHash

@[expose] public section

/-!
# The straight-line code-binding bound

The simulated world of code binding with any verdict after the challenges of the adversary's
root (`idealT`) is, for each table `h` of `H`, Wagner's world with the verdict's pure form
(`idealT_evalDistEq`, the chain of `cbIdealG_evalDistEq`). So a code-binding win, a
knowledge-soundness break and a true straight-line verdict are three events of one experiment,
and the first is at most the other two (`prT_cbIdealG_le`, by `postP_imp`). The straight-line
verdict is a bad cache of the world with a random oracle of the draws per root and label
(`not_good_of_tail`), whose probability is bounded phase by phase (`prob_world_not_good_le`): the
adversary's at most `2 Q + 1` queries, `Q` of them of draws, by the bad-event budget; the
verifier's reading of its root's draws, one fresh try; the verdict's hashes, by the budget again
(`prT_idealT_tailH_le`, `codeBindingExpG_le`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA; the
straight-line argument replaces his forking step and is built on his framework and games.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex PqDas
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal

namespace LeanDa

/-! ## Averages -/

theorem prEvent_bind_le_add_of_support {α β : Type} (mx : ProbComp α) (f g k : α → ProbComp β)
    (P : β → Prop)
    (hp : ∀ x ∈ support mx, Pr{let y ← f x}[P y] ≤ Pr{let y ← g x}[P y] + Pr{let y ← k x}[P y]) :
    Pr{let y ← mx >>= f}[P y] ≤ Pr{let y ← mx >>= g}[P y] + Pr{let y ← mx >>= k}[P y] := by
  simp only [OracleComp.prEvent_bind_eq_tsum]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  by_cases hx : x ∈ support mx
  · rw [← mul_add]; gcongr; exact hp x hx
  · simp [prEvent_eq_zero_of_not_mem_support mx hx]

theorem prEvent_bind_le_of_support {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (P : β → Prop) (a : ℝ≥0∞) (hp : ∀ x ∈ support mx, Pr{let y ← f x}[P y] ≤ a) :
    Pr{let y ← mx >>= f}[P y] ≤ a := by
  simp only [OracleComp.prEvent_bind_eq_tsum]
  calc ∑' x, Pr{let z ← mx}[z = x] * Pr{let y ← f x}[P y]
      ≤ ∑' x, Pr{let z ← mx}[z = x] * a := ENNReal.tsum_le_tsum fun x ↦ by
        by_cases hx : x ∈ support mx
        · gcongr; exact hp x hx
        · simp [prEvent_eq_zero_of_not_mem_support mx hx]
    _ = (∑' x, Pr{let z ← mx}[z = x]) * a := ENNReal.tsum_mul_right
    _ ≤ a := mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one mx)

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

theorem cbIdealG_eq (A : CodeBindingAdvB r Crs Proof) (crs : Crs) :
    cbIdealG r ps A crs = idealT r A crs (postV r ps crs) := rfl

theorem ksIdealG_eq (A : CodeBindingAdvB r Crs Proof) (crs : Crs) :
    ksIdealG r ps ext A crs = idealT r A crs (ksPostH r ps ext crs) := rfl

/-- **The simulated world with a verdict is, for each table of `H`, Wagner's world with the
verdict's pure form.** -/
theorem idealT_evalDistEq (A : CodeBindingAdvB r Crs Proof) {crs : Crs}
    (hcrs : crs ∈ support ps.setup)
    (T : CbOut r Proof → MembershipChallenge → OracleComp (unifSpec + roSpec (List UInt8)
        DigestBytes) Bool)
    (TP : HTab → CbOut r Proof → MembershipChallenge → Bool)
    (hT : ∀ h out l s, (simulateQ (phiG h) (simulateQ embG (T out l))).run s = pure (TP h out l, s)) :
    idealT r A crs T =ᵈ ($ᵗ HTab >>= fun h ↦
      (simulateQ (Common.DigestBytes →ₒ MembershipChallenge).romImpl (advH r ps A h ((), crs) >>=
          fun out ↦
        TP h out <$> readVecW out.1.1)).run' ∅) := by
  rw [idealT]
  refine (run'_romImpl_evalDistEq_vec _).trans ?_
  refine (run'_romImpl_evalDistEq_swap _ _).trans ?_
  rw [swapCache_empty]
  refine (run'_romImpl_evalDistEq_eager shortP _ ∅).trans ?_
  refine EvalDistEq.bind_right _ fun h ↦ (run'_eagerImpl_tImpl h _).trans ?_
  rw [simulateQ_phiG]
  have e : (simulateQ (phiG h) (advSim r A crs >>= fun out ↦
      readVec (Msg := List UInt8) (Dg := DigestBytes) out.1.1 >>= fun l ↦
        simulateQ embG (T out l))).run' ∅ =
        advH r ps A h ((), crs) >>= fun out ↦ TP h out <$> readVecW out.1.1 := by
    rw [advH, fixCrs_of_mem r ps hcrs, simulateQ_bind, StateT.run'_eq,
      StateT.run_bind, StateT.run'_eq, map_bind, bind_map_left]
    refine bind_congr fun z ↦ ?_
    rw [simulateQ_bind, StateT.run_bind, run_readVec_phiG, bind_map_left]
    simp only [hT, map_pure, map_bind]
    rw [map_eq_bind_pure_comp]
    rfl
  rw [e]

/-- Wagner's world with a pure verdict, as the verdict of one run. -/
theorem run'_verdict_eq (A : CodeBindingAdvB r Crs Proof) (h : HTab) (crs : Crs)
    (F : CbOut r Proof → MembershipChallenge → Bool) :
    (simulateQ (Common.DigestBytes →ₒ MembershipChallenge).romImpl (advH r ps A h ((), crs) >>=
        fun out ↦
        F out <$> readVecW out.1.1)).run' ∅ =
      (fun p ↦ F p.1 p.2) <$> (simulateQ (Common.DigestBytes →ₒ MembershipChallenge).romImpl
        (advH r ps A h ((), crs) >>= fun out ↦ (out, ·) <$> readVecW out.1.1)).run' ∅ := by
  have e : (advH r ps A h ((), crs) >>= fun out ↦ F out <$> readVecW out.1.1) =
      (fun p ↦ F p.1 p.2) <$> (advH r ps A h ((), crs) >>= fun out ↦
        (out, ·) <$> readVecW out.1.1) := by
    simp only [map_bind, Functor.map_map]
  rw [e, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
    Functor.map_map]

/-- **A code-binding win in the simulated world is at most a knowledge-soundness break plus a
true straight-line verdict.** -/
theorem prT_cbIdealG_le (A : CodeBindingAdvB r Crs Proof) {crs : Crs}
    (hcrs : crs ∈ support ps.setup) :
    prT (cbIdealG r ps A crs) ≤
      prT (ksIdealG r ps ext A crs) + prT (idealT r A crs (tailH r ps ext crs)) := by
  rw [cbIdealG_eq, ksIdealG_eq, prT, prT, prT,
    (idealT_evalDistEq r ps A hcrs _ (fun h ↦ postP r ps h crs)
      (fun h out l s ↦ run_postV_phiG r ps h crs out l s)).prEvent_eq,
    (idealT_evalDistEq r ps A hcrs _ (fun h ↦ ksP r ps ext h crs)
      (fun h out l s ↦ run_ksPostH_phiG r ps ext h crs out l s)).prEvent_eq,
    (idealT_evalDistEq r ps A hcrs _ (fun h ↦ tailP r ps ext h crs)
      (fun h out l s ↦ run_tailH_phiG r ps ext h crs out l s)).prEvent_eq]
  refine prEvent_bind_le_add_of_support _ _ _ _ _ fun h _ ↦ ?_
  rw [run'_verdict_eq, run'_verdict_eq, run'_verdict_eq, prEvent_map, prEvent_map, prEvent_map]
  exact (prEvent_mono _ _ _ fun p hp ↦ postP_imp r ps ext h crs p.1 p.2 hp).trans
    (prEvent_or_le _ _ _)

/-- **The simulated code-binding experiment is at most the knowledge-soundness one plus the
straight-line verdict.** -/
theorem prT_codeBindingExpG_le (A : CodeBindingAdvB r Crs Proof) :
    prT (codeBindingExpG r ps A) ≤ prT (ps.setup >>= ksIdealG r ps ext A) +
      prT (ps.setup >>= fun crs ↦ idealT r A crs (tailH r ps ext crs)) :=
  prEvent_bind_le_add_of_support _ _ _ _ _ fun _ hcrs ↦ prT_cbIdealG_le r ps ext A hcrs

/-! ## The verdict in the straight-line world -/

/-- **The verdict is at most a bad cache**, the draws read at all labels. -/
theorem prT_tailL_le (A : CodeBindingAdvB r Crs Proof) (crs : Crs) (L : List (Fin nLabels))
    (hlen : L.length = nLabels) (hidx : ∀ i (hi : i < L.length), (L[i]).val = i) :
    Pr{let b ← (simulateQ GW.romImpl (advSim r A crs >>= tailL r ps ext L crs)).run' ∅}[b = true] ≤
      Pr{let z ← (simulateQ GW.romImpl (advSim r A crs >>= tailL r ps ext L crs)).run ∅}[
        ¬ Good r z.2] := by
  rw [StateT.run'_eq, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun z hz hz1 ↦ ?_
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨w, -, hz⟩ := hz
  exact not_good_of_tail r ps ext L hlen hidx crs w.1 w.2 hz hz1

/-! ## The world's queries -/

/-- `H` among coins and `H`, one each. -/
def tCount : (unifSpec + roSpec (List UInt8) DigestBytes).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem isWeightBound_zero {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (X : OracleComp spec α) : QueryCostAtMost X (fun _ ↦ 0) 0 := by
  induction X using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih => exact (isWeightBound_query_bind_iff _ _ _ _).mpr ⟨le_rfl, fun u ↦ ih u⟩

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
    (com : Common.DigestBytes) (p : Fin (r * 128)) (x : Cell) (τ : CellOpening) :
    QueryCostAtMost (verifyCellMWithHash H r com p x τ) w (τ.path.length + 2) :=
  ((hH _).bind fun _ ↦ (isWeightBound_walkM H w hH _ _ _).bind fun _ ↦
    isWeightBound_pure _ _ 0).mono (by omega)

set_option maxRecDepth 4000 in
theorem isWeightBound_tailH (crs : Crs) (out : CbOut r Proof) (l : MembershipChallenge) :
    QueryCostAtMost (tailH r ps ext crs out l) tCount (commitCalls r + (9 + logPaddedRowCount r)) := by
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
    · exact isWeightBound_query gwCalls (.inr (.inl a))) (isWeightBound_zero Y)

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
  have := h1.add h2
  rw [hgCalls_eq] at this
  exact this.mono (by omega)

/-- **A bad cache after the adversary, the reading of its root's draws and the verdict**: the
adversary's queries (at most `Q₁` of `H` or the draws, `Q₂` of the draws), then one fresh try
for the reading, then the verdict's queries of `H`. -/
theorem prob_world_not_good_le (A : CodeBindingAdvB r Crs Proof) (crs : Crs)
    (L : List (Fin nLabels))
    (hread : ∀ d c, Good r c → Pr{let z ← (simulateQ GW.romImpl (readL L d)).run c}[¬ Good r z.2] ≤
      (2 ^ 14 - 1) / 2 ^ 128)
    (N Q₁ Q₂ Q₃ : ℕ) (ha : QueryCostAtMost (advSim r A crs) hgCalls Q₁)
    (hg : QueryCostAtMost (advSim r A crs) gwCalls Q₂)
    (ht : ∀ out l, QueryCostAtMost (simulateQ (embG (Root := Common.DigestBytes) (Z := Draw)
      (n := nLabels)) (tailH r ps ext crs out l)) hgCalls Q₃) (hN : Q₁ + 1 + Q₃ ≤ N) :
    Pr{let z ← (simulateQ GW.romImpl (advSim r A crs >>= tailL r ps ext L crs)).run ∅}[
        ¬ Good r z.2] ≤
      Q₁ * (65 * N / 2 ^ 256) + Q₂ * ((2 ^ 14 - 1) / 2 ^ 139) +
        ((2 ^ 14 - 1) / 2 ^ 128 + Q₃ * (65 * N / 2 ^ 256)) := by
  have hf0 : GFin ∅ := ⟨by simp [domH], by simp [domG]⟩
  have hs0 : gSize ∅ = 0 := by simp [gSize, domH, domG]
  rw [simulateQ_bind, StateT.run_bind]
  refine (prEvent_bind_le_of_good _ _ (fun p ↦ ¬ Good r p.2) _ _ fun p hp hgp ↦ ?_).trans
    (add_le_add (prob_run_not_good_le r _ ∅ (good_empty r) hf0 N Q₁ Q₂ ha hg (by omega)) le_rfl)
  simp only [not_not] at hgp
  obtain ⟨hfp, hsp⟩ := run_gFin_gSize _ Q₁ ha ∅ hf0 p hp
  rw [tailL, simulateQ_bind, StateT.run_bind]
  refine (prEvent_bind_le_of_good _ _ (fun q ↦ ¬ Good r q.2) _ _ fun q hq hgq ↦ ?_).trans
    (add_le_add (hread _ _ hgp) le_rfl)
  simp only [not_not] at hgq
  obtain ⟨hfq, hsq⟩ := readL_gFin_gSize L _ p.2 hfp hq
  refine (prob_run_not_good_le r _ q.2 hgq hfq N Q₃ 0 (ht p.1 q.1)
    (isWeightBound_embG_g _) (by omega)).trans (le_of_eq ?_)
  simp

theorem finRange_getElem_val (n : ℕ) : ∀ i (hi : i < (List.finRange n).length),
    ((List.finRange n)[i]).val = i := fun i hi ↦ by simp

/-- **The straight-line verdict's probability**, for an adversary of `Q` permutation calls and
`r ≤ 1024` rows: at most `N · 65 N / 2^256 + Q · 2^-11 · (2^14 - 1) / 2^128 + (2^14 - 1) / 2^128`
for `N = 2 Q + 2^20`: the hash's bad events, a fresh draw the adversary's call makes selected and
accepting, and the one fresh try of the verifier's nonce search. -/
theorem prT_idealT_tailH_le (A : CodeBindingAdvB r Crs Proof) (Q : ℕ) (hr : r ≤ maxRows)
    (crs : Crs) (ha : QueryCostAtMost (advSim r A crs) hgCalls (2 * Q + 1))
    (hg : QueryCostAtMost (advSim r A crs) gwCalls Q) :
    prT (idealT r A crs (tailH r ps ext crs)) ≤
      ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) * (65 * ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        (Q * ((2 ^ 14 - 1) / 2 ^ 139) + (2 ^ 14 - 1) / 2 ^ 128) := by
  have hL : logPaddedRowCount r ≤ 10 := by
    unfold logPaddedRowCount
    exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr (by simpa [maxRows] using hr)
  have hN : paddedRowCount r ≤ 1024 := by
    unfold paddedRowCount
    calc 2 ^ logPaddedRowCount r ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hL
      _ = 1024 := by norm_num
  have hread : ∀ d c, Good r c →
      Pr{let z ← (simulateQ GW.romImpl (readL (List.finRange nLabels) d)).run c}[¬ Good r z.2] ≤
        (2 ^ 14 - 1) / 2 ^ 128 := fun d c hc ↦ by
    rw [← readVec_eq_readL]; exact prob_readVec_not_good_le r d c hc
  have hT : idealT r A crs (tailH r ps ext crs) =
      (simulateQ GW.romImpl (advSim r A crs >>=
        tailL r ps ext (List.finRange nLabels) crs)).run' ∅ := by
    unfold idealT tailL
    simp only [readVec_eq_readL]
  have h1 := prT_tailL_le r ps ext A crs (List.finRange nLabels) (List.length_finRange)
    (finRange_getElem_val nLabels)
  have h2 := prob_world_not_good_le r ps ext A crs (List.finRange nLabels) hread
    (2 * Q + 2 ^ 20) (2 * Q + 1) Q (commitCalls r + (9 + logPaddedRowCount r)) ha hg
    (fun out l ↦ isWeightBound_embG_h (isWeightBound_tailH r ps ext crs out l))
    (by unfold commitCalls; omega)
  rw [prT, hT]
  refine h1.trans (h2.trans ?_)
  set x : ℝ≥0∞ := 65 * ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 256
  have hQ : ((2 * Q + 1 : ℕ) : ℝ≥0∞) + ((commitCalls r + (9 + logPaddedRowCount r) : ℕ) : ℝ≥0∞) ≤
      ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_add]; exact_mod_cast (by unfold commitCalls; omega)
  calc ((2 * Q + 1 : ℕ) : ℝ≥0∞) * x + (Q : ℝ≥0∞) * ((2 ^ 14 - 1) / 2 ^ 139) +
        ((2 ^ 14 - 1) / 2 ^ 128 + ((commitCalls r + (9 + logPaddedRowCount r) : ℕ) : ℝ≥0∞) * x)
      = (((2 * Q + 1 : ℕ) : ℝ≥0∞) + ((commitCalls r + (9 + logPaddedRowCount r) : ℕ) : ℝ≥0∞)) * x +
          ((Q : ℝ≥0∞) * ((2 ^ 14 - 1) / 2 ^ 139) + (2 ^ 14 - 1) / 2 ^ 128) := by ring
    _ ≤ _ := by gcongr

/-- **The simulated code-binding experiment**: the knowledge-soundness one plus the straight-line
verdict's bound, for a simulated adversary of at most `2 Q + 1` queries of `H` or the draws, `Q`
of them of the draws (`isWeightBound_advSim`). -/
theorem codeBindingExpG_le (A : CodeBindingAdvB r Crs Proof) (Q : ℕ) (hr : r ≤ maxRows)
    (hA : ∀ crs ∈ support ps.setup, QueryCostAtMost (advSim r A crs) hgCalls (2 * Q + 1) ∧
      QueryCostAtMost (advSim r A crs) gwCalls Q) :
    prT (codeBindingExpG r ps A) ≤ prT (ps.setup >>= ksIdealG r ps ext A) +
      (((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) * (65 * ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        (Q * ((2 ^ 14 - 1) / 2 ^ 139) + (2 ^ 14 - 1) / 2 ^ 128)) :=
  (prT_codeBindingExpG_le r ps ext A).trans (add_le_add le_rfl
    (prEvent_bind_le_of_support _ _ _ _ fun crs hcrs ↦
      prT_idealT_tailH_le r ps ext A Q hr crs (hA crs hcrs).1 (hA crs hcrs).2))

end Ideal
end LeanDa

/-! ## The arithmetic of the bound -/

namespace LeanDa

/-- The duplex lemma's term for `Q` calls of `F`. -/
noncomputable abbrev dupTerm (Q : ℕ) : ℝ≥0∞ :=
  ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) * (2 * ((Q + nLabels + 1 : ℕ) : ℝ≥0∞) * (2 ^ 576 : ℝ≥0∞)⁻¹)

/-- **The terms besides the argument's knowledge soundness**: the two transfers, the two duplex
lemmas and the straight-line verdict, at most `(Q + 2^11) · 2^-125 + (Q + 2^22)² · 2^-247` for
`K ≤ Q + 2^65` calls of the knowledge-soundness game. -/
theorem straight_rest_le (Q K : ℕ) (hK : K ≤ Q + 2 ^ 65) :
    (K : ℝ≥0∞) ^ 2 / 2 ^ 508 + dupTerm Q +
        (((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) * (65 * ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
          ((Q : ℝ≥0∞) * ((2 ^ 14 - 1) / 2 ^ 139) + (2 ^ 14 - 1) / 2 ^ 128)) +
        ((Q : ℝ≥0∞) ^ 2 / 2 ^ 508 + dupTerm Q) ≤
      ((Q : ℝ≥0∞) + 2 ^ 11) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 247 := by
  calc _ ≤ (K : ℝ≥0∞) ^ 2 / 2 ^ 508 + dupTerm Q +
        (((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) * (65 * ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
          ((Q : ℝ≥0∞) * (2 ^ 14 / 2 ^ 139) + 2 ^ 14 / 2 ^ 128)) +
        ((Q : ℝ≥0∞) ^ 2 / 2 ^ 508 + dupTerm Q) := by
        gcongr <;> exact tsub_le_self
    _ ≤ _ := ?_
  unfold dupTerm
  simp only [nLabels, nonceCount]
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_add, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ne_eq, ENNReal.div_eq_top,
    ENNReal.natCast_ne_top, ENNReal.pow_eq_top_iff, ENNReal.ofNat_ne_top, false_and, and_false,
    or_self, not_false_eq_true, ENNReal.mul_eq_top, pow_eq_zero_iff, OfNat.ofNat_ne_zero,
    ENNReal.add_eq_top, ENNReal.inv_eq_top, ENNReal.inv_eq_zero]
  push_cast
  have t5 : (Q : ℝ) * (2 ^ 14 / 2 ^ 139) = Q * (2 : ℝ)⁻¹ ^ 125 := by norm_num
  have t6 : (2 : ℝ) ^ 14 / 2 ^ 128 = 2 ^ 11 * (2 : ℝ)⁻¹ ^ 125 := by norm_num
  have hA : (2 : ℝ) ^ 86 * 2 ^ 256 ≤ 2 ^ 508 := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hB : (2 : ℝ) ^ 88 * 2 ^ 256 ≤ 2 ^ 576 := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hc : (264 : ℝ) / 2 ^ 256 ≤ (2 : ℝ)⁻¹ ^ 247 := by norm_num
  have hC0 : (0 : ℝ) < 2 ^ 256 := by positivity
  generalize (2 : ℝ) ^ 508 = A at hA ⊢
  generalize (2 : ℝ) ^ 576 = B at hB ⊢
  generalize (2 : ℝ) ^ 256 = C at hA hB hc hC0 ⊢
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  set y : ℝ := (Q : ℝ) + 2 ^ 22 with hy
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hy0 : (0 : ℝ) ≤ y := by positivity
  have hy2 : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  have hK' : (K : ℝ) ≤ 2 ^ 43 * y := by
    have : (K : ℝ) ≤ Q + 2 ^ 65 := by exact_mod_cast hK
    rw [hy]; nlinarith
  have hD : (Q : ℝ) + 2 ^ 64 + 1 + 1 ≤ 2 ^ 43 * y := by rw [hy]; nlinarith
  have hD0 : (0 : ℝ) ≤ (Q : ℝ) + 2 ^ 64 + 1 + 1 := by positivity
  -- the terms over `A`, `B`, `C`
  have hAC : (2 : ℝ) ^ 86 / A ≤ 1 / C := by rw [div_le_div_iff₀ hA0 hC0]; linarith
  have hAC' : (1 : ℝ) / A ≤ 1 / C := by rw [div_le_div_iff₀ hA0 hC0]; nlinarith
  have hBC : (2 : ℝ) ^ 87 / B ≤ 1 / (2 * C) := by
    rw [div_le_div_iff₀ hB0 (by positivity)]; linarith
  have t1 : (K : ℝ) ^ 2 / A ≤ y ^ 2 * (1 / C) := by
    have : (K : ℝ) ^ 2 ≤ (2 ^ 43 * y) ^ 2 := pow_le_pow_left₀ hK0 hK' 2
    calc (K : ℝ) ^ 2 / A ≤ (2 ^ 43 * y) ^ 2 / A := by gcongr
      _ = y ^ 2 * (2 ^ 86 / A) := by ring
      _ ≤ y ^ 2 * (1 / C) := mul_le_mul_of_nonneg_left hAC hy2
  have t2 : (Q : ℝ) ^ 2 / A ≤ y ^ 2 * (1 / C) := by
    have : (Q : ℝ) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hQ0 (by rw [hy]; linarith) 2
    calc (Q : ℝ) ^ 2 / A ≤ y ^ 2 / A := by gcongr
      _ = y ^ 2 * (1 / A) := by ring
      _ ≤ y ^ 2 * (1 / C) := mul_le_mul_of_nonneg_left hAC' hy2
  have t3 : ((Q : ℝ) + 2 ^ 64 + 1 + 1) * (2 * ((Q : ℝ) + 2 ^ 64 + 1 + 1) * B⁻¹) ≤
      y ^ 2 * (1 / (2 * C)) := by
    calc ((Q : ℝ) + 2 ^ 64 + 1 + 1) * (2 * ((Q : ℝ) + 2 ^ 64 + 1 + 1) * B⁻¹)
        ≤ (2 ^ 43 * y) * (2 * (2 ^ 43 * y) * B⁻¹) := by gcongr
      _ = y ^ 2 * (2 ^ 87 / B) := by ring
      _ ≤ y ^ 2 * (1 / (2 * C)) := mul_le_mul_of_nonneg_left hBC hy2
  have t4 : (2 * (Q : ℝ) + 2 ^ 20) * (65 * (2 * (Q : ℝ) + 2 ^ 20) / C) ≤ y ^ 2 * (260 / C) := by
    calc (2 * (Q : ℝ) + 2 ^ 20) * (65 * (2 * (Q : ℝ) + 2 ^ 20) / C) ≤
          (2 * y) * (65 * (2 * y) / C) := by gcongr <;> (rw [hy]; linarith)
      _ = y ^ 2 * (260 / C) := by ring
  have e7 : y ^ 2 * (264 / C) ≤ y ^ 2 * (2 : ℝ)⁻¹ ^ 247 := mul_le_mul_of_nonneg_left hc hy2
  have hsplit : y ^ 2 * (1 / C) + y ^ 2 * (1 / (2 * C)) + y ^ 2 * (260 / C) +
      (y ^ 2 * (1 / C) + y ^ 2 * (1 / (2 * C))) = y ^ 2 * (263 / C) := by
    field_simp; ring
  have e8 : y ^ 2 * (263 / C) ≤ y ^ 2 * (264 / C) := by gcongr; norm_num
  linarith [t1, t2, t3, t4, t5, t6, e7, e8, hsplit]

/-- **The straight-line bound is below the forking route's** for every `Q`. -/
theorem straight_le_fork (Q c k : ℕ) :
    ((Q : ℝ≥0∞) + c + 2 ^ 65) * (2 : ℝ≥0∞)⁻¹ ^ k + ((Q : ℝ≥0∞) + 2 ^ 11) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 247 ≤
      ((Q : ℝ≥0∞) + c + 2 ^ 65) * (2 : ℝ≥0∞)⁻¹ ^ k + ((Q : ℝ≥0∞) + 2 ^ 20) * (2 : ℝ≥0∞)⁻¹ ^ 56 +
        ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 158 := by
  have hlin : ((Q : ℝ≥0∞) + 2 ^ 11) * (2 : ℝ≥0∞)⁻¹ ^ 125 ≤
      ((Q : ℝ≥0∞) + 2 ^ 20) * (2 : ℝ≥0∞)⁻¹ ^ 56 :=
    mul_le_mul' (add_le_add le_rfl (show (2 : ℝ≥0∞) ^ 11 ≤ 2 ^ 20 from
      pow_le_pow_right₀ (by norm_num) (by norm_num)))
      (pow_le_pow_of_le_one zero_le (by norm_num) (by norm_num))
  have hquad : ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 247 ≤
      ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 158 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one zero_le (by norm_num) (by norm_num)) zero_le
  gcongr

end LeanDa
