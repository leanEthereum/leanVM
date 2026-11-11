module

public import Qrom.Verify
public import Qrom.OvSearch

@[expose] public section

/-!
# Assembling the bounds of a game with a classical verifier

The search bound for a game whose adversary is followed by a classical verifier: the probability
that a value the verifier reads, in the side state the game ends in, is good
(`Qrom.OvGame.search_withVerifier_le`). The verifier's calls count toward the budget.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum

namespace OvGame

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]

section bound

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{0, 0}} {α β : Type}

/-- Call budgets add under sequencing of fixed-register programs. -/
theorem isTotalQueryBound_bind₂ {A B C : QReg} (x : QuantumComp₂ L spec A B α)
    {k : α → QuantumComp₂ L spec B C β} {n m : ℕ} (hx : x.IsTotalQueryBound n)
    (hk : ∀ a, (k a).IsTotalQueryBound m) : (x.bind k).IsTotalQueryBound (n + m) := by
  induction x using QuantumComp₂.inductionOn generalizing n with
  | pure A a =>
    rw [QuantumComp₂.pure_bind]
    exact (hk a).mono (Nat.le_add_left m n)
  | primBind A B o k' ih =>
    rw [QuantumComp₂.primBind_bind]
    exact (QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun b ↦
      ih b ((QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mp hx b) hk
  | queryBind A B i E ℓ k' ih =>
    rw [QuantumComp₂.queryBind_bind]
    obtain ⟨hn, hr⟩ := (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mp hx
    refine (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr ⟨by omega, fun r ↦ ?_⟩
    exact (ih r (hr r) hk).mono (by omega)

theorem isTotalQueryBound_act {A B : QReg} (p : SubInstrument A B α) :
    (QComp.act (spec := spec) p).IsTotalQueryBound 0 :=
  (QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦
    QuantumComp.isTotalQueryBound_pure _ _

end bound

/-- A classical hash query makes one call. -/
theorem isTotalQueryBound_hashQuery (t : X) :
    (hashQuery (S := S) (P := P) (Res := Res) (Y := Y) t).IsTotalQueryBound 1 := by
  unfold hashQuery QComp.callBasis
  have hq : (QuantumComp₂.query (L := LocalSig.instruments) (spec := ovSpec X Y S P Res)
      (A := QReg.of (((ovSpec X Y S P Res).In (Sum.inl ())).carrier × (QReg.of Unit).carrier))
      (Sum.inl ()) (QReg.of Unit) (Equiv.refl _)).IsTotalQueryBound 1 :=
    (QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr ⟨Nat.one_pos, fun _ ↦
      QuantumComp.isTotalQueryBound_pure _ _⟩
  exact (isTotalQueryBound_bind₂ (n := 0) (m := 1) _ (isTotalQueryBound_act _) fun _ ↦
    isTotalQueryBound_bind₂ (n := 1) (m := 0) _ hq fun _ ↦ isTotalQueryBound_act _)

/-- A classical algorithm making at most `m` queries runs to a program making at most `m` calls. -/
theorem isTotalQueryBound_classicalProg {β : Type} {oa : OracleComp (X →ₒ Y) β} {m : ℕ}
    (h : OracleComp.IsTotalQueryBound oa m) :
    (classicalProg (S := S) (P := P) (Res := Res) oa).IsTotalQueryBound m := by
  induction oa using OracleComp.inductionOn generalizing m with
  | pure a => exact QuantumComp.isTotalQueryBound_pure _ _
  | query_bind t k ih =>
    rw [OracleComp.isTotalQueryBound_query_bind_iff] at h
    rw [classicalProg, OracleComp.toQuantumAt_query_bind]
    exact (isTotalQueryBound_bind₂ _ (isTotalQueryBound_hashQuery t) fun y ↦ ih y (h.2 y)).mono
      (by omega)

/-- The calls of the program and of the verifier add. -/
theorem isTotalQueryBound_withVerifier {A : QReg} {α β : Type}
    {adv : QComp (ovSpec X Y S P Res) A (QReg.of Unit) α} {ver : α → OracleComp (X →ₒ Y) β}
    {n m : ℕ} (hadv : adv.IsTotalQueryBound n) (hver : ∀ a, OracleComp.IsTotalQueryBound (ver a) m) :
    (withVerifier adv ver).IsTotalQueryBound (n + m) := by
  refine isTotalQueryBound_bind₂ _ hadv fun a ↦ ?_
  rw [QuantumComp₂.map_eq_bind_pure]
  exact (isTotalQueryBound_bind₂ _ (isTotalQueryBound_classicalProg (hver a)) fun _ ↦
    QuantumComp.isTotalQueryBound_pure _ 0).mono (by omega)


/-- **The search bound with a classical verifier.** A program making at most `n` calls, followed by
a verifier making at most `m` queries and reading at most `k` inputs, reads a good value in the side
state it ends in with probability at most `λ (√(2 + 4 λ) (n + m) + 2 k)²`, where every input has a fraction
at most `λ` of good values. -/
theorem search_withVerifier_le (g : OvGame X Y S P Res) [Nonempty Y] (good : X → Y → Prop)
    [∀ z, DecidablePred (good z)] (sb : ℕ) (hs : ∀ z, (Finset.univ.filter (good z)).card ≤ sb)
    {A : QReg} {α β : Type} [DecidableEq α] [DecidableEq β]
    (adv : QComp (ovSpec X Y S P Res) A (QReg.of Unit) α) (ver : α → OracleComp (X →ₒ Y) β)
    (out : β → Finset X) (k : ℕ) (hout : ∀ b, (out b).card ≤ k) (n m : ℕ)
    (hadv : adv.IsTotalQueryBound n) (hver : ∀ a, OracleComp.IsTotalQueryBound (ver a) m)
    (ρ : SubState A) :
    ∑ G : X → Y, (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * sideW g G .instruments adv ρ (fun p s ↦
        decide (∃ z ∈ out (evalWithAnswerFn (QueryImpl.ofFn (g.answer s G)) (ver p.2.2)),
          good z (G z))) ≤
      ENNReal.ofReal (((sb : ℝ) / Fintype.card Y) *
        (√(2 + 4 * ((sb : ℝ) / Fintype.card Y)) * (n + m : ℕ) + 2 * k) ^ 2) *
        ENNReal.ofReal ρ.matrix.trace.re := by
  have h := ov_search_le g good .instruments sb hs (n + m) k (withVerifier adv ver)
    (isTotalQueryBound_withVerifier hadv hver) ρ (fun p ↦ out p.2.2.2) fun p ↦ hout _
  erw [sampledEvalDistMap_apply _ _ _ _ _ (measurableSet_singleton true)] at h
  refine le_of_eq_of_le (Finset.sum_congr rfl fun G _ ↦ ?_) h
  congr 1
  exact (sideW_withVerifier g G adv ver ρ fun ab _ ↦
    decide (∃ z ∈ out ab.2, good z (G z))).symm.trans
    (sideW_const g G .instruments (withVerifier adv ver) ρ fun p ↦
      decide (∃ z ∈ out p.2.2.2, good z (G z)))

section events

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

theorem sideW_mono (g : OvGame X Y S P Res) (G : X → Y) (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) {ev ev' : (Σ u, W u) → S → Bool}
    (h : ∀ p s, ev p s = true → ev' p s = true) :
    sideW g G I x ρ ev ≤ sideW g G I x ρ ev' := by
  rw [sideW_eq_sum, sideW_eq_sum]
  refine ENNReal.tsum_le_tsum fun p ↦ Finset.sum_le_sum fun s _ ↦ ?_
  by_cases he : ev p s = true
  · rw [ite_eq_left he, ite_eq_left (h p s he)]
  · rw [ite_eq_right he]
    exact zero_le

theorem sideW_or_le (g : OvGame X Y S P Res) (G : X → Y) (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) (ev ev' : (Σ u, W u) → S → Bool) :
    sideW g G I x ρ (fun p s ↦ ev p s || ev' p s) ≤ sideW g G I x ρ ev + sideW g G I x ρ ev' := by
  rw [sideW_eq_sum, sideW_eq_sum, sideW_eq_sum, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun p ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  cases ev p s <;> cases ev' p s <;> simp

/-- The total weight of the leaves and side states is at most the trace of the input. -/
theorem sideW_true_le (g : OvGame X Y S P Res) (G : X → Y) (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) :
    sideW g G I x ρ (fun _ _ ↦ true) ≤ ENNReal.ofReal ρ.matrix.trace.re := by
  rw [sideW_const]
  refine (MeasureTheory.measure_mono (Set.subset_univ _)).trans ?_
  rw [QuantumRuntime.evalDistMap_apply_univ]
  set p := (g.sampled G).run I x
  rw [p.isCPTNIFamily.familyTrace_apply, p.isCPTNIFamily.re_tsum_trace_apply]
  refine ENNReal.ofReal_le_ofReal ((p.tsum_trace_re_le (ρ.prod _).posSemidef).trans (le_of_eq ?_))
  simp [SubState.prod, Matrix.trace_kronecker, SubState.matrix_basis]

end events

/-- Two games with the same answers, transitions and initial side state run alike. -/
theorem sampled_congr {g g' : OvGame X Y S P Res} {G G' : X → Y}
    (hans : ∀ s x, g.answer s G x = g'.answer s G' x) (htr : g.trans = g'.trans)
    (hinit : g.init = g'.init) : g.sampled G = g'.sampled G' := by
  have ha : (fun t : S × Unit ↦ g.answer t.1 G) = fun t ↦ g'.answer t.1 G' :=
    funext fun t ↦ funext fun x ↦ hans t.1 x
  have hs : ∀ j, g.sideStep Unit j = g'.sideStep Unit j := by
    intro j
    have hk : g.sideKraus Unit j = g'.sideKraus Unit j := by
      funext rs
      simp only [sideKraus, htr]
    unfold sideStep
    congr 1
  simp only [sampled, tabRuntime, hinit]
  congr 1
  funext i
  rcases i with ⟨⟩ | j
  · simp only [ha]
    rfl
  · exact hs j

/-- Two games with the same answers, transitions and initial side state give every event the same
weight. -/
theorem sideW_congr {g g' : OvGame X Y S P Res} {G G' : X → Y}
    (hans : ∀ s x, g.answer s G x = g'.answer s G' x) (htr : g.trans = g'.trans)
    (hinit : g.init = g'.init) {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg} (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) (ev : (Σ u, W u) → S → Bool) :
    sideW g G I x ρ ev = sideW g' G' I x ρ ev := by
  have ha : (fun t : S × Unit ↦ g.answer t.1 G) = fun t ↦ g'.answer t.1 G' :=
    funext fun t ↦ funext fun x ↦ hans t.1 x
  have hs : g.sideStep Unit = g'.sideStep Unit := by
    funext j
    have hk : g.sideKraus Unit j = g'.sideKraus Unit j := by
      funext rs
      simp only [sideKraus, htr]
    unfold sideStep
    congr 1
  unfold sideW sampled tabRuntime
  rw [ha, hs, hinit]

/-- A side state no run reaches carries no weight: a set of side states that no transition
leaves into from outside and that the initial side state avoids. -/
theorem blockW_unreachable (g : OvGame X Y S P Res) (G : X → Y) (V : Set S) [DecidablePred (· ∈ V)]
    (hclosed : ∀ j s, (g.trans j s).2 ∈ V → s ∈ V) (hinit : g.init ∉ V) {L : LocalSig.{u, v}}
    {W : QReg → Type w} {A : QReg} (I : L.Interp) (x : QuantumComp L (ovSpec X Y S P Res) W A)
    (ρ : SubState A) (p : Σ u, W u) (s : S) (hs : s ∈ V) :
    blockW s ((g.sampled G).jointPost I x ρ p).matrix = 0 := by
  let z : SubState (QReg.of (S × Unit)) := ⟨0, PosSemidef.zero, by simp⟩
  have hz : MatrixMap.conj (sideProj V) (g.sampled G).init.matrix = MatrixMap.conj (sideProj V) z.matrix := by
    have hm : (g.sampled G).init.matrix = Matrix.single (g.init, ()) (g.init, ()) 1 := by
      simp [sampled, tabRuntime, SubState.prod, SubState.matrix_basis, Matrix.single_kronecker_single]
    rw [hm, MatrixMap.conj_apply, MatrixMap.conj_apply, sideProj, diagonal_mul_single']
    simp [hinit, z]
  have hj := conj_jointPost_eq_of_proj (s₀ := (g.sampled G).step) (s₁ := (g.sampled G).step)
    (σ₀ := (g.sampled G).init) (σ₁ := z) I (g.sampled_branch G) (g.sampled_branch G)
    (sideProj_conjTranspose V) (sideProj_mul_self V) (sampKraus_leak g hclosed G)
    (sampKraus_leak g hclosed G) (fun _ _ ↦ rfl) hz x ρ p
  rw [← blockW_proj V s hs]
  change blockW s ((MatrixMap.conj (sideProj V)).amplifyLeft p.1
    ((QuantumRuntime.mk (QReg.of (S × Unit)) (g.sampled G).init (g.sampled G).step).jointPost I x ρ p).matrix) = 0
  rw [hj, QuantumRuntime.matrix_jointPost]
  simp [blockW, z]

/-- An event may be restricted to the side states a run reaches. -/
theorem sideW_restrict (g : OvGame X Y S P Res) (G : X → Y) (V : Set S) [DecidablePred (· ∈ V)]
    (hclosed : ∀ j s, (g.trans j s).2 ∈ V → s ∈ V) (hinit : g.init ∉ V) {L : LocalSig.{u, v}}
    {W : QReg → Type w} {A : QReg} (I : L.Interp) (x : QuantumComp L (ovSpec X Y S P Res) W A)
    (ρ : SubState A) (ev : (Σ u, W u) → S → Bool) :
    sideW g G I x ρ ev = sideW g G I x ρ (fun p s ↦ ev p s && decide (s ∉ V)) := by
  rw [sideW_eq_sum, sideW_eq_sum]
  refine tsum_congr fun p ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases hs : s ∈ V
  · rw [blockW_unreachable g G V hclosed hinit I x ρ p s hs]
    simp
  · simp [hs]

end OvGame

end Qrom
