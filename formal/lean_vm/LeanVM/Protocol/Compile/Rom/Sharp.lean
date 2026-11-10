/-
  LeanVM.Protocol.Compile.Rom.Sharp

  Completeness against the random oracles, union only over the answers the transcript uses: the
  compiled verifier of a program refining the honest prover's rejects the honest proof with
  probability at most the program's ideal failure probability, plus the proofs of work's misses,
  plus a capacity collision.
-/

module

public import LeanVM.Protocol.Compile.Rom.Ideal
public import LeanVM.Protocol.Compile.Rom.Complete

/-!
# Completeness, union only over the transcript's answers

`romCompleteSharp`. The honest prover of `P` runs against the logged random oracles, then the
compiled verifier of `P'`, a program refining `P` (`Limits.Refines`: `P` with failures inserted).
The verifier rejects only where the honest transcript fails a check of `P'` (`traceOk`,
`runProof_prove_trace`). Along the prover's run, each challenge of the transcript comes from a
fresh permutation answer, unless some answer's capacity is that of an earlier permutation input
(`Collided`); the proof of work's nonces are tried in order, and the passing nonce's answer has a
challenge uniform and independent of its proof-of-work lane. So, by induction along the program
(`trace_le`), the probability that the transcript fails `P'` with no collision is at most the
ideal failure probability `S.failFrom P' [] none` (every challenge uniform and independent), plus
`(1 - 2^-bits)^fuel` per quarter of `P`'s cost; the collisions are at most `Q · Q · 2^-256` over
the run's `Q` queries (`collided_le`).
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol
open LeanVM.Protocol.Rom OracleComp OracleSpec
open LeanVM.Prover (Tree buildTreeWithHash searchM findNonceM)
open scoped ENNReal

@[expose] public section

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## One query against the logged oracles -/

section Query

variable {β : Type}

/-- A run against the logged oracles from the log `ℓ`. -/
abbrev runL (oa : OracleComp KeccakCalls β) (ℓ : Log) : ProbComp (β × Log) :=
  (simulateQ loggedRO oa).run ℓ

theorem run_loggedRO_queryF_bind (s : KeccakState) (mx : KeccakState → OracleComp KeccakCalls β)
    (ℓ : Log) :
    runL (callKeccakF1600 s >>= mx) ℓ =
      (loggedRO (Sum.inr s : Bytes ⊕ KeccakState)).run ℓ >>= fun p ↦ runL (mx p.1) p.2 := by
  simp only [runL, callKeccakF1600]
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

/-- **A fresh permutation query**: its answer uniform, recorded at the end of the log. -/
theorem pr_queryF_fresh {s : KeccakState} {ℓ : Log} (hs : lookF ℓ s = none)
    (mx : KeccakState → OracleComp KeccakCalls β) (ev : β × Log → Prop) :
    Pr{let z ← runL (callKeccakF1600 s >>= mx) ℓ}[ev z] =
      (∑ u, Pr{let z ← runL (mx u) (ℓ ++ [Sum.inr (s, u)])}[ev z]) /
        Fintype.card KeccakState := by
  rw [run_loggedRO_queryF_bind, loggedRO_isLazySampler (Sum.inr s : Bytes ⊕ KeccakState) ℓ]
  have hs' : logLookup ℓ (Sum.inr s : Bytes ⊕ KeccakState) = none := hs
  simp only [hs']
  simp only [bind_assoc, pure_bind]
  let _ : MeasurableSpace ((Spec₂ Bytes Digest KeccakState KeccakState).Range (Sum.inr s)) := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, SampleableType.evalDist_uniformSample,
    ProbabilityTheory.lintegral_uniformOn_univ]
  rfl

/-- **A permutation query the log answers.** -/
theorem pr_queryF_cached {s u : KeccakState} {ℓ : Log} (hs : lookF ℓ s = some u)
    (mx : KeccakState → OracleComp KeccakCalls β) (ev : β × Log → Prop) :
    Pr{let z ← runL (callKeccakF1600 s >>= mx) ℓ}[ev z] =
      Pr{let z ← runL (mx u) ℓ}[ev z] := by
  rw [run_loggedRO_queryF_bind, loggedRO_isLazySampler (Sum.inr s : Bytes ⊕ KeccakState) ℓ]
  have hs' : logLookup ℓ (Sum.inr s : Bytes ⊕ KeccakState) = some u := hs
  simp only [hs', pure_bind]

/-- **A fresh first query is the average over its answer logged in advance.** -/
theorem pr_queryF_fresh_relog {s : KeccakState} {ℓ : Log} (hs : lookF ℓ s = none)
    (mx : KeccakState → OracleComp KeccakCalls β) (ev : β × Log → Prop) :
    Pr{let z ← runL (callKeccakF1600 s >>= mx) ℓ}[ev z] =
      (∑ u, Pr{let z ← runL (callKeccakF1600 s >>= mx) (ℓ ++ [Sum.inr (s, u)])}[ev z]) /
        Fintype.card KeccakState := by
  rw [pr_queryF_fresh hs]
  congr 1
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [pr_queryF_cached (lookF_append_inr_self hs u)]

end Query

/-! ## Answers of a log as functions, and capacity collisions -/

/-- The hash answers of a log, `default` where it has none. -/
def hOf (ℓ : Log) : Bytes → Digest := fun x ↦ (lookH ℓ x).getD default

/-- The permutation answers of a log, `default` where it has none. -/
def fOf (ℓ : Log) : KeccakState → KeccakState := fun s ↦ (lookF ℓ s).getD default

theorem hOf_eq {ℓ : Log} {x : Bytes} {u : Digest} (h : lookH ℓ x = some u) : hOf ℓ x = u := by
  simp [hOf, h]

theorem fOf_eq {ℓ : Log} {s u : KeccakState} (h : lookF ℓ s = some u) : fOf ℓ s = u := by
  simp [fOf, h]

/-- A fresh permutation answer whose capacity is its input's or an earlier input's. -/
def CapHit (ℓ : Log) (s u : KeccakState) : Prop := ∃ y ∈ s :: fIns ℓ, capOf y = capOf u

/-- Some permutation answer of the log hit the capacity of its input or of an earlier input. -/
def Collided (ℓ : Log) : Prop :=
  ∃ (i : ℕ) (hi : i < ℓ.length) (s u : KeccakState), ℓ[i] = .inr (s, u) ∧ CapHit (ℓ.take i) s u

theorem collided_of_prefix {ℓ ℓ' : Log} (hp : ℓ <+: ℓ') (h : Collided ℓ) : Collided ℓ' := by
  obtain ⟨i, hi, s, u, he, hc⟩ := h
  obtain ⟨t, rfl⟩ := hp
  refine ⟨i, by simp; omega, s, u, ?_, ?_⟩
  · rw [List.getElem_append_left hi]; exact he
  · rw [List.take_append_of_le_length hi.le]; exact hc

theorem collided_append_inr {ℓ : Log} {s u : KeccakState} (h : CapHit ℓ s u) :
    Collided (ℓ ++ [.inr (s, u)]) :=
  ⟨ℓ.length, by simp, s, u, by simp, by simpa using h⟩

theorem collided_append_inr_iff (ℓ : Log) (s u : KeccakState) :
    Collided (ℓ ++ [.inr (s, u)]) ↔ Collided ℓ ∨ CapHit ℓ s u := by
  constructor
  · rintro ⟨i, hi, s', u', he, hc⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by simpa using hi) with hi' | rfl
    · refine Or.inl ⟨i, hi', s', u', ?_, ?_⟩
      · rw [List.getElem_append_left hi'] at he; exact he
      · rw [List.take_append_of_le_length hi'.le] at hc; exact hc
    · simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero,
        Sum.inr.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inr (by simpa using hc)
  · rintro (h | h)
    · exact collided_of_prefix (List.prefix_append _ _) h
    · exact collided_append_inr h

theorem collided_append_inl_iff (ℓ : Log) (p : Bytes × Digest) :
    Collided (ℓ ++ [.inl p]) ↔ Collided ℓ := by
  constructor
  · rintro ⟨i, hi, s', u', he, hc⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by simpa using hi) with hi' | rfl
    · refine ⟨i, hi', s', u', ?_, ?_⟩
      · rw [List.getElem_append_left hi'] at he; exact he
      · rw [List.take_append_of_le_length hi'.le] at hc; exact hc
    · simp at he
  · exact collided_of_prefix (List.prefix_append _ _)

/-- A capacity hit has probability at most `(|ℓ| + 1) · 2^-256`. -/
theorem sum_capHit_div_le (ℓ : Log) (s : KeccakState) :
    (∑ u, ind (CapHit ℓ s u)) / Fintype.card KeccakState ≤
      ((ℓ.length + 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 256 := by
  set C : List (Fin 9 → UInt64) := (s :: fIns ℓ).map capOf
  have hpt : ∀ u, ind (CapHit ℓ s u) ≤ (C.map fun c ↦ ind (capOf u = c)).sum := by
    intro u
    refine le_trans (ind_mono fun h ↦ ?_) (ind_exists_le C _)
    obtain ⟨y, hy, h⟩ := h
    exact ⟨capOf y, List.mem_map_of_mem hy, h.symm⟩
  have hC : C.length ≤ ℓ.length + 1 := by
    have := length_leftOf_add_rightOf ℓ
    simp [C, fIns]
    omega
  calc (∑ u, ind (CapHit ℓ s u)) / Fintype.card KeccakState
      ≤ (∑ u, (C.map fun c ↦ ind (capOf u = c)).sum) / Fintype.card KeccakState := by
        gcongr with u; exact hpt u
    _ = (C.map fun c ↦ (∑ u, ind (capOf u = c)) / Fintype.card KeccakState).sum := by
        rw [sum_list_sum_comm, div_eq_mul_inv, ← List.sum_map_mul_right]
        simp only [div_eq_mul_inv]
    _ ≤ C.length * 2⁻¹ ^ 256 := list_sum_le _ _ _ fun c _ ↦ sum_capOf_div_le c
    _ ≤ _ := by gcongr

open Classical in
/-- The collision potential: `1` once the log collided. -/
noncomputable def collPot (ℓ : Log) : ℝ≥0∞ := if Collided ℓ then 1 else 0

/-- **Capacity collisions are rare**: over a run of at most `Q` queries from the empty log, the
final log collided with probability at most `Q · Q · 2^-256`. -/
theorem collided_le {β : Type} (oa : OracleComp KeccakCalls β) (Q : ℕ)
    (hQ : IsTotalQueryBound oa Q) :
    Pr{let z ← runL oa []}[Collided z.2] ≤
      Q * (((Q : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 256) := by
  classical
  have hstep : LogStepBelow Q collPot (((Q : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 256) := by
    refine ⟨fun ℓ x _ _ ↦ ?_, fun ℓ s hℓ _ ↦ ?_⟩
    · simp only [collPot, collided_append_inl_iff]
      exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
    · calc (∑ u, collPot (ℓ ++ [.inr (s, u)])) / Fintype.card KeccakState
          ≤ (∑ u, (collPot ℓ + ind (CapHit ℓ s u))) / Fintype.card KeccakState := by
            gcongr with u
            simp only [collPot, collided_append_inr_iff, ind]
            split_ifs <;> simp_all
        _ = collPot ℓ + (∑ u, ind (CapHit ℓ s u)) / Fintype.card KeccakState := by
            rw [show (∑ u, (collPot ℓ + ind (CapHit ℓ s u))) = ∑ u, (ind (CapHit ℓ s u) + collPot ℓ)
              from Finset.sum_congr rfl fun _ _ ↦ add_comm _ _, avg_add_const, add_comm]
        _ ≤ collPot ℓ + ((ℓ.length + 1 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ 256 := by
            gcongr; exact sum_capHit_div_le ℓ s
        _ ≤ _ := by gcongr; exact_mod_cast hℓ
  have h := prEvent_run_loggedRO_le_of_freshStepBelow Q hstep oa Q hQ [] (by simp)
    (fun _ ℓ ↦ Collided ℓ) (fun z _ hz ↦ by simp [collPot, hz])
  simpa [collPot, Collided] using h

/-! ## The prover's sponge steps, one query at a time -/

section Steps

variable {β : Type}

theorem absorb_bind_full {sp : Sponge} (hfull : sp.pending.length = rateScalars) (x : E)
    (tag : ℕ) (f : Sponge → OracleComp KeccakCalls β) :
    Compile.absorb callKeccakF1600 sp x tag >>= f =
      callKeccakF1600 (duplexInput sp) >>= fun v ↦ f ⟨v, [(x, tag)], sp.ground⟩ := by
  simp [Compile.absorb, duplex, hfull]

theorem absorb_bind_short {sp : Sponge} (hshort : sp.pending.length ≠ rateScalars) (x : E)
    (tag : ℕ) (f : Sponge → OracleComp KeccakCalls β) :
    Compile.absorb callKeccakF1600 sp x tag >>= f =
      f { sp with pending := sp.pending ++ [(x, tag)] } := by
  simp [Compile.absorb, hshort]

theorem absorbI_full (F : KeccakState → KeccakState) {sp : Sponge}
    (hfull : sp.pending.length = rateScalars) (x : E) (tag : ℕ) :
    absorbI F sp x tag = ⟨F (duplexInput sp), [(x, tag)], sp.ground⟩ := by
  simp [absorbI, Compile.absorb, duplex, hfull]
  rfl

theorem absorbI_short (F : KeccakState → KeccakState) {sp : Sponge}
    (hshort : sp.pending.length ≠ rateScalars) (x : E) (tag : ℕ) :
    absorbI F sp x tag = { sp with pending := sp.pending ++ [(x, tag)] } := by
  simp [absorbI, Compile.absorb, hshort]

theorem squeeze_bind_none {sp : Sponge} (hg : sp.ground = none)
    (f : E × Sponge → OracleComp KeccakCalls β) :
    squeeze callKeccakF1600 sp >>= f =
      callKeccakF1600 (duplexInput sp) >>= fun u ↦ f (challengeOf u, ⟨u, [], none⟩) := by
  simp [squeeze, duplex, hg]

theorem squeeze_bind_some {sp : Sponge} {c : E} (hg : sp.ground = some c)
    (f : E × Sponge → OracleComp KeccakCalls β) :
    squeeze callKeccakF1600 sp >>= f = f (c, { sp with ground := none }) := by
  simp [squeeze, hg]

theorem squeezeI_none (F : KeccakState → KeccakState) {sp : Sponge} (hg : sp.ground = none) :
    squeezeI F sp = (challengeOf (F (duplexInput sp)), ⟨F (duplexInput sp), [], none⟩) := by
  simp [squeezeI, squeeze, duplex, hg]
  exact ⟨rfl, rfl⟩

theorem squeezeI_some (F : KeccakState → KeccakState) {sp : Sponge} {c : E}
    (hg : sp.ground = some c) : squeezeI F sp = (c, { sp with ground := none }) := by
  simp [squeezeI, squeeze, hg]

/-- The capacity of a permutation's input is the sponge's. -/
theorem capOf_duplexInput (sp : Sponge) : capOf (duplexInput sp) = capOf sp.state := by
  rw [duplexInput_eq, capOf_duplexOf]

theorem lookF_none_of_cap {ℓ : Log} {s : KeccakState} (h : ∀ y ∈ fIns ℓ, capOf y ≠ capOf s) :
    lookF ℓ s = none :=
  (lookR_eq_none_iff ℓ s).mpr fun hs ↦ h s hs rfl

/-- After a fresh answer with no capacity hit, the sponge it starts is fresh. -/
theorem fresh_of_not_capHit {ℓ : Log} {s u : KeccakState} (h : ¬ CapHit ℓ s u) :
    Fresh (ℓ ++ [.inr (s, u)]) u := by
  intro y hy hc
  rw [fIns_append_inr, List.mem_append, List.mem_singleton] at hy
  exact h ⟨y, by rcases hy with hy | rfl <;> simp [*], hc⟩

/-- The event is impossible on outcomes of a run from a collided log. -/
theorem pr_eq_zero_of_collided {oa : OracleComp KeccakCalls β} {ℓ : Log} (hc : Collided ℓ)
    (ev : Log → Prop) (hev : ∀ ℓf, ev ℓf → ¬ Collided ℓf) :
    Pr{let z ← runL oa ℓ}[ev z.2] = 0 :=
  prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h ↦
    hev z.2 h (collided_of_prefix (simulateQ_look_of_mem_support oa ℓ z hz).1 hc)

/-- An event read through the answers of the final log, on outcomes of a run from `ℓ'`, where a
function of those answers is constant. -/
theorem pr_congr_final {oa : OracleComp KeccakCalls β} {ℓ' : Log} {γ : Type} (g : Log → γ)
    (c : γ) (hg : ∀ ℓf, ℓ' <+: ℓf → g ℓf = c) (ev : γ → Log → Prop) :
    Pr{let z ← runL oa ℓ'}[ev (g z.2) z.2] = Pr{let z ← runL oa ℓ'}[ev c z.2] :=
  prEvent_congr_of_support _ _ _ fun z hz ↦ by
    rw [hg z.2 (simulateQ_look_of_mem_support oa ℓ' z hz).1]

/-- **An absorption.** -/
theorem pr_absorb_le {sp : Sponge} {ℓ : Log} (hF : Fresh ℓ sp.state) (x : E) (tag : ℕ)
    (f : Sponge → OracleComp KeccakCalls β) (ev : Sponge → Log → Prop)
    (hev : ∀ sp' ℓf, ev sp' ℓf → ¬ Collided ℓf) (c : ℝ≥0∞)
    (hk : ∀ (F' : KeccakState → KeccakState) (ℓ' : Log), ℓ <+: ℓ' →
      Fresh ℓ' (absorbI F' sp x tag).state →
      (∀ ℓf, ℓ' <+: ℓf → absorbI (fOf ℓf) sp x tag = absorbI F' sp x tag) →
      Pr{let z ← runL (f (absorbI F' sp x tag)) ℓ'}[ev (absorbI F' sp x tag) z.2] ≤ c) :
    Pr{let z ← runL (Compile.absorb callKeccakF1600 sp x tag >>= f) ℓ}[
      ev (absorbI (fOf z.2) sp x tag) z.2] ≤ c := by
  by_cases hfull : sp.pending.length = rateScalars
  · rw [absorb_bind_full hfull]
    have hs : lookF ℓ (duplexInput sp) = none :=
      lookF_none_of_cap fun y hy ↦ by rw [capOf_duplexInput]; exact hF y hy
    rw [pr_queryF_fresh hs]
    refine avg_le_of_le fun v ↦ ?_
    let F' : KeccakState → KeccakState := fun _ ↦ v
    have hsp : absorbI F' sp x tag = ⟨v, [(x, tag)], sp.ground⟩ := absorbI_full F' hfull x tag
    have hfin : ∀ ℓf, ℓ ++ [.inr (duplexInput sp, v)] <+: ℓf →
        absorbI (fOf ℓf) sp x tag = absorbI F' sp x tag := fun ℓf hp ↦ by
      rw [absorbI_full _ hfull, absorbI_full _ hfull,
        fOf_eq (lookF_of_prefix hp (lookF_append_inr_self hs v))]
    rw [pr_congr_final (fun ℓf ↦ absorbI (fOf ℓf) sp x tag) _ hfin]
    by_cases hc : CapHit ℓ (duplexInput sp) v
    · rw [pr_eq_zero_of_collided (collided_append_inr hc) _ fun ℓf h ↦ hev _ ℓf h]
      exact bot_le
    · rw [← hsp]
      exact hk F' _ (List.prefix_append _ _) (by rw [hsp]; exact fresh_of_not_capHit hc) hfin
  · rw [absorb_bind_short hfull]
    have hsp : ∀ F', absorbI F' sp x tag = { sp with pending := sp.pending ++ [(x, tag)] } :=
      fun F' ↦ absorbI_short F' hfull x tag
    have hfin : ∀ ℓf, ℓ <+: ℓf → absorbI (fOf ℓf) sp x tag = absorbI id sp x tag :=
      fun ℓf _ ↦ by rw [hsp, hsp]
    rw [pr_congr_final (fun ℓf ↦ absorbI (fOf ℓf) sp x tag) _ hfin]
    have := hk id ℓ (List.prefix_refl _) (by rw [hsp id]; exact hF) hfin
    rw [hsp id] at this ⊢
    exact this

/-- **A squeeze.** -/
theorem pr_squeeze_le {sp : Sponge} {ℓ : Log} (hF : Fresh ℓ sp.state)
    (f : E × Sponge → OracleComp KeccakCalls β) (ev : E × Sponge → Log → Prop)
    (hev : ∀ r ℓf, ev r ℓf → ¬ Collided ℓf) (A : E → ℝ≥0∞)
    (hk : ∀ (F' : KeccakState → KeccakState) (ℓ' : Log), ℓ <+: ℓ' →
      Fresh ℓ' (squeezeI F' sp).2.state →
      (∀ ℓf, ℓ' <+: ℓf → squeezeI (fOf ℓf) sp = squeezeI F' sp) →
      Pr{let z ← runL (f (squeezeI F' sp)) ℓ'}[ev (squeezeI F' sp) z.2] ≤
        A (squeezeI F' sp).1) :
    Pr{let z ← runL (squeeze callKeccakF1600 sp >>= f) ℓ}[ev (squeezeI (fOf z.2) sp) z.2] ≤
      match sp.ground with
      | some c => A c
      | none => (∑ u : KeccakState, A (challengeOf u)) / Fintype.card KeccakState := by
  rcases hg : sp.ground with _ | c
  · rw [squeeze_bind_none hg]
    have hs : lookF ℓ (duplexInput sp) = none :=
      lookF_none_of_cap fun y hy ↦ by rw [capOf_duplexInput]; exact hF y hy
    show _ ≤ (∑ u : KeccakState, A (challengeOf u)) / (Fintype.card KeccakState : ℝ≥0∞)
    rw [pr_queryF_fresh hs]
    gcongr with u
    let F' : KeccakState → KeccakState := fun _ ↦ u
    have hsp : squeezeI F' sp = (challengeOf u, ⟨u, [], none⟩) := squeezeI_none F' hg
    have hfin : ∀ ℓf, ℓ ++ [.inr (duplexInput sp, u)] <+: ℓf →
        squeezeI (fOf ℓf) sp = squeezeI F' sp := fun ℓf hp ↦ by
      rw [squeezeI_none _ hg, squeezeI_none _ hg,
        fOf_eq (lookF_of_prefix hp (lookF_append_inr_self hs u))]
    rw [pr_congr_final (fun ℓf ↦ squeezeI (fOf ℓf) sp) _ hfin]
    by_cases hc : CapHit ℓ (duplexInput sp) u
    · rw [pr_eq_zero_of_collided (collided_append_inr hc) _ fun ℓf h ↦ hev _ ℓf h]
      exact bot_le
    · have := hk F' _ (List.prefix_append _ _) (by rw [hsp]; exact fresh_of_not_capHit hc)
        hfin
      rw [hsp] at this ⊢
      exact this
  · rw [squeeze_bind_some hg]
    have hsp : ∀ F', squeezeI F' sp = (c, { sp with ground := none }) :=
      fun F' ↦ squeezeI_some F' hg
    have hfin : ∀ ℓf, ℓ <+: ℓf → squeezeI (fOf ℓf) sp = squeezeI id sp :=
      fun ℓf _ ↦ by rw [hsp, hsp]
    rw [pr_congr_final (fun ℓf ↦ squeezeI (fOf ℓf) sp) _ hfin]
    have := hk id ℓ (List.prefix_refl _) (by rw [hsp id]; exact hF) hfin
    rw [hsp id] at this ⊢
    exact this

end Steps

/-! ## The commitment's tree: hash queries only -/

section Tree

variable {α β : Type}

/-- A computation whose runs leave the log's permutation inputs as they were. -/
def HOnly (oa : OracleComp KeccakCalls β) : Prop :=
  ∀ ℓ z, z ∈ support (runL oa ℓ) → fIns z.2 = fIns ℓ

theorem hOnly_pure (x : β) : HOnly (pure x : OracleComp KeccakCalls β) := by
  intro ℓ z hz
  simp [runL] at hz
  rw [hz]

theorem hOnly_bind {oa : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    (h1 : HOnly oa) (h2 : ∀ a, HOnly (f a)) : HOnly (oa >>= f) := by
  intro ℓ z hz
  rw [runL, LeanVM.Protocol.Rom.run_simulateQ_bind, mem_support_bind_iff] at hz
  obtain ⟨p, hp, hz⟩ := hz
  rw [h2 p.1 p.2 z hz, h1 ℓ p hp]

theorem hOnly_callH (x : Bytes) : HOnly (callKeccak256 x) := by
  intro ℓ z hz
  have hz' : z ∈ support ((loggedRO (Sum.inl x : Bytes ⊕ KeccakState)).run ℓ) := by
    simpa [runL, callKeccak256] using hz
  rw [loggedRO_isLazySampler (Sum.inl x : Bytes ⊕ KeccakState) ℓ] at hz'
  rcases hl : logLookup ℓ (Sum.inl x : Bytes ⊕ KeccakState) with _ | u
  · rw [hl] at hz'
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz'
    obtain ⟨u, -, rfl⟩ := hz'
    exact fIns_append_inl ℓ (x, u)
  · rw [hl] at hz'
    simp only [support_pure, Set.mem_singleton_iff] at hz'
    rw [hz']

theorem hOnly_listMapM (g : α → OracleComp KeccakCalls β) (hg : ∀ a, HOnly (g a)) :
    ∀ l : List α, HOnly (l.mapM g)
  | [] => by simpa using hOnly_pure ([] : List β)
  | a :: l => by
    simp only [List.mapM_cons]
    exact hOnly_bind (hg a) fun b ↦ hOnly_bind (hOnly_listMapM g hg l) fun bs ↦ hOnly_pure _

theorem hOnly_arrayMapM (g : α → OracleComp KeccakCalls β) (hg : ∀ a, HOnly (g a))
    (xs : Array α) : HOnly (xs.mapM g) := by
  rw [Array.mapM_eq_mapM_toList, map_eq_bind_pure_comp]
  exact hOnly_bind (hOnly_listMapM g hg _) fun _ ↦ hOnly_pure _

theorem hOnly_levels : ∀ (k : ℕ) (level : Array Digest),
    HOnly (LeanVM.Prover.levelsWithHash callKeccak256 k level)
  | 0, _ => hOnly_pure _
  | k + 1, _ => hOnly_bind (hOnly_arrayMapM _ (fun _ ↦ hOnly_callH _) _) fun up ↦
      hOnly_bind (hOnly_levels k up) fun _ ↦ hOnly_pure _

theorem hOnly_buildTree (ht : ℕ) (w : Word) : HOnly (buildTreeWithHash callKeccak256 ht w) :=
  hOnly_bind (hOnly_arrayMapM _ (fun _ ↦ hOnly_callH _) _) fun leaves ↦
    hOnly_bind (hOnly_levels ht leaves) fun _ ↦ hOnly_pure _

/-- **A computation's outcome is its value at the answers of any log extending the final one.** -/
theorem eq_id_of_mem_support {oa : OracleComp KeccakCalls β} {ℓ : Log} {z : β × Log}
    (hz : z ∈ support (runL oa ℓ)) {ℓf : Log} (hp : z.2 <+: ℓf) :
    simulateQ (totalImpl (hOf ℓf) (fOf ℓf)) oa = z.1 :=
  simulateQ_id_of_look ℓf (hOf ℓf) (fOf ℓf) (fun _ _ h ↦ hOf_eq h) (fun _ _ h ↦ fOf_eq h) oa z.1
    ((simulateQ_look_of_mem_support oa ℓ z hz).2 ℓf hp)

/-- The tree built against the logged oracles is the one built with the final log's answers. -/
theorem tree_of_mem_support {ht : ℕ} {w : Word} {ℓ : Log} {z : Tree × Log}
    (hz : z ∈ support (runL (buildTreeWithHash callKeccak256 ht w) ℓ)) {ℓf : Log}
    (hp : z.2 <+: ℓf) : z.1 = buildTreeWithHash (m := Id) (hOf ℓf) ht w := by
  have := eq_id_of_mem_support hz hp
  rw [simulateQ_buildTreeM, implH_totalImpl] at this
  exact this.symm

end Tree

/-! ## The proof-of-work search -/

section Search

variable {β : Type}

/-- The nonce position of a search from `sp` in the log `ℓ`: the sponge's capacity and waiting
scalars, or, with four waiting, the capacity of the permutation that empties them, which `ℓ`
answers. -/
def NonceAt (ℓ : Log) (sp : Sponge) (κ : PowKey) : Prop :=
  (sp.pending.length ≠ rateScalars ∧ κ = (capOf sp.state, sp.pending)) ∨
    (sp.pending.length = rateScalars ∧ ∃ v, lookF ℓ (duplexInput sp) = some v ∧ κ = (capOf v, []))

theorem nonceAt_of_prefix {ℓ ℓ' : Log} (hp : ℓ <+: ℓ') {sp : Sponge} {κ : PowKey}
    (h : NonceAt ℓ sp κ) : NonceAt ℓ' sp κ := by
  rcases h with h | ⟨h4, v, hv, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨h4, v, lookF_of_prefix hp hv, rfl⟩

theorem absorbNonce_bind_short {sp : Sponge} (hshort : sp.pending.length ≠ rateScalars) (n : E)
    (g : UInt64 × Sponge → OracleComp KeccakCalls β) :
    absorbNonce callKeccakF1600 sp n >>= g =
      callKeccakF1600 (duplexOf (capOf sp.state) (sp.pending ++ [(n, dsPowNonce)])) >>= fun u ↦
        g (Keccak.lane u 2, ⟨u, [], some (challengeOf u)⟩) := by
  simp only [absorbNonce, bind_assoc]
  rw [absorb_bind_short hshort]
  simp [duplex, duplexInput_eq]

theorem absorbNonce_bind_full {sp : Sponge} (hfull : sp.pending.length = rateScalars) (n : E)
    (g : UInt64 × Sponge → OracleComp KeccakCalls β) :
    absorbNonce callKeccakF1600 sp n >>= g =
      callKeccakF1600 (duplexInput sp) >>= fun v ↦
        callKeccakF1600 (duplexOf (capOf v) [(n, dsPowNonce)]) >>= fun u ↦
          g (Keccak.lane u 2, ⟨u, [], some (challengeOf u)⟩) := by
  simp only [absorbNonce, bind_assoc]
  rw [absorb_bind_full hfull]
  simp [duplex, duplexInput_eq]

/-- **A nonce's permutation, at its position.** -/
theorem pr_absorbNonce {ℓ : Log} {sp : Sponge} {κ : PowKey} (h : NonceAt ℓ sp κ) (m : ℕ)
    (g : UInt64 × Sponge → OracleComp KeccakCalls β) (ev : Log → Prop) :
    Pr{let z ← runL (absorbNonce callKeccakF1600 sp (nonceOf m) >>= g) ℓ}[ev z.2] =
      Pr{let z ← runL (callKeccakF1600 (nonceInput κ.1 κ.2 m) >>= fun u ↦
        g (Keccak.lane u 2, ⟨u, [], some (challengeOf u)⟩)) ℓ}[ev z.2] := by
  rcases h with ⟨hs, rfl⟩ | ⟨h4, v, hv, rfl⟩
  · rw [absorbNonce_bind_short hs]
    rfl
  · rw [absorbNonce_bind_full h4, pr_queryF_cached hv]
    rfl

/-- The pure nonce step at a position the log answers. -/
theorem powStep_of_nonceAt {ℓ : Log} {sp : Sponge} {κ : PowKey} (h : NonceAt ℓ sp κ) (m : ℕ) :
    powStep (fOf ℓ) sp (nonceOf m) =
      (Keccak.lane (fOf ℓ (nonceInput κ.1 κ.2 m)) 2,
        ⟨fOf ℓ (nonceInput κ.1 κ.2 m), [], some (challengeOf (fOf ℓ (nonceInput κ.1 κ.2 m)))⟩) := by
  rcases h with ⟨hs, rfl⟩ | ⟨h4, v, hv, rfl⟩
  · simp [powStep, absorbNonce, Compile.absorb, hs, duplex, duplexInput_eq, nonceInput]
    exact ⟨rfl, rfl, rfl⟩
  · simp [powStep, absorbNonce, Compile.absorb, h4, duplex, duplexInput_eq, nonceInput]
    rw [← duplexInput_eq, fOf_eq hv]
    exact ⟨rfl, rfl, rfl⟩

/-- The pure search finds the first passing nonce the log answers. -/
theorem findNonce_of_log {ℓ : Log} {sp : Sponge} {κ : PowKey} (h : NonceAt ℓ sp κ) {b fuel m : ℕ}
    (hm : m < fuel) {u : KeccakState} (hu : lookF ℓ (nonceInput κ.1 κ.2 m) = some u)
    (hpass : powOk b (Keccak.lane u 2) = true)
    (hfail : ∀ m' < m, ∃ u', lookF ℓ (nonceInput κ.1 κ.2 m') = some u' ∧
      powOk b (Keccak.lane u' 2) = false) :
    findNonce (fOf ℓ) b sp fuel = some (nonceOf m) := by
  unfold findNonce
  have e : (List.range fuel).find? (fun n ↦ powOk b (powStep (fOf ℓ) sp (nonceOf n)).1) =
      some m := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by rw [powStep_of_nonceAt h, fOf_eq hu]; exact hpass, m, by simpa using hm, by simp,
      fun j hj ↦ ?_⟩
    simp only [List.getElem_range]
    obtain ⟨u', hu', hf⟩ := hfail j hj
    rw [powStep_of_nonceAt h, fOf_eq hu']
    simp [hf]
  rw [e]
  rfl

/-- The capacities of the nonce inputs below `n`, and no other input, are the position's. -/
def SearchInv (ℓ : Log) (κ : PowKey) (n : ℕ) : Prop :=
  ∀ y ∈ fIns ℓ, capOf y = κ.1 → ∃ m < n, y = nonceInput κ.1 κ.2 m

/-- **The proof-of-work search**: the first passing nonce's answer has a challenge uniform and
independent of its proof of work; the search misses all its nonces with probability
`(1 - 2^-b)^count`. -/
theorem pr_search_le {sp : Sponge} {κ : PowKey} (hκ : KeyOk κ) {b fuel : ℕ} (hb : b ≤ 64)
    (hfuel : fuel ≤ 2 ^ 64) (G : Option E → OracleComp KeccakCalls β) (ev : Log → Prop)
    (hev : ∀ ℓf, ev ℓf → ¬ Collided ℓf) (A : E → ℝ≥0∞) (R : ℝ≥0∞)
    (hG : ∀ (m : ℕ) (ℓ' : Log) (u : KeccakState), m < fuel → NonceAt ℓ' sp κ →
      lookF ℓ' (nonceInput κ.1 κ.2 m) = some u → powOk b (Keccak.lane u 2) = true →
      (∀ m' < m, ∃ u', lookF ℓ' (nonceInput κ.1 κ.2 m') = some u' ∧
        powOk b (Keccak.lane u' 2) = false) →
      Fresh ℓ' u →
      Pr{let z ← runL (G (some (nonceOf m))) ℓ'}[ev z.2] ≤ A (challengeOf u) + R) :
    ∀ (count n : ℕ) (ℓ : Log), n + count = fuel → NonceAt ℓ sp κ → SearchInv ℓ κ n →
      (∀ m < n, ∃ u', lookF ℓ (nonceInput κ.1 κ.2 m) = some u' ∧
        powOk b (Keccak.lane u' 2) = false) →
      Pr{let z ← runL (searchM callKeccakF1600 b sp n count >>= G) ℓ}[ev z.2] ≤
        missProb b ^ count +
          (∑ u : KeccakState, A (challengeOf u)) / Fintype.card KeccakState + R
  | 0, n, ℓ, _, _, _, _ => by
    simp only [searchM, pure_bind, pow_zero]
    exact (prEvent_le_one _).trans (le_trans le_self_add le_self_add)
  | count + 1, n, ℓ, hc, hat, hinv, hfails => by
    have hn : n < fuel := by omega
    simp only [searchM, bind_assoc, prover_nonceOf]
    rw [pr_absorbNonce hat n]
    set x := nonceInput κ.1 κ.2 n
    have hx : lookF ℓ x = none := by
      refine (lookR_eq_none_iff ℓ x).mpr fun hmem ↦ ?_
      obtain ⟨m, hm, he⟩ := hinv x hmem (by simp [x, nonceInput])
      have := (nonceInput_inj hκ hκ (by omega) (by omega) he).2
      omega
    rw [pr_queryF_fresh hx]
    set avgA := (∑ u : KeccakState, A (challengeOf u)) / Fintype.card KeccakState
    calc _ ≤ (∑ u, (ind (powOk b (Keccak.lane u 2) = true) * A (challengeOf u) +
            ind (powOk b (Keccak.lane u 2) = false) * (missProb b ^ count + avgA) + R)) /
            Fintype.card KeccakState := by
          gcongr with u
          have hlook : lookF (ℓ ++ [.inr (x, u)]) x = some u := lookF_append_inr_self hx u
          have hat' := nonceAt_of_prefix (List.prefix_append ℓ [.inr (x, u)]) hat
          have hfails' : ∀ m < n, ∃ u', lookF (ℓ ++ [.inr (x, u)]) (nonceInput κ.1 κ.2 m) =
              some u' ∧ powOk b (Keccak.lane u' 2) = false := fun m hm ↦ by
            obtain ⟨u', hu', hf⟩ := hfails m hm
            exact ⟨u', lookF_of_prefix (List.prefix_append _ _) hu', hf⟩
          by_cases hp : powOk b (Keccak.lane u 2) = true
          · simp only [hp, ↓reduceIte, pure_bind, ind, one_mul, Bool.true_eq_false, zero_mul,
              add_zero]
            by_cases hcap : CapHit ℓ x u
            · rw [pr_eq_zero_of_collided (collided_append_inr hcap) _ hev]
              exact bot_le
            · exact hG n _ u hn hat' hlook hp hfails' (fresh_of_not_capHit hcap)
          · have hp' : powOk b (Keccak.lane u 2) = false := by simpa using hp
            simp only [hp', Bool.false_eq_true, ↓reduceIte, ind, zero_mul, zero_add, one_mul]
            refine pr_search_le hκ hb hfuel G ev hev A R hG count (n + 1) _ (by omega) hat' ?_ ?_
            · intro y hy hcy
              rw [fIns_append_inr, List.mem_append, List.mem_singleton] at hy
              rcases hy with hy | rfl
              · obtain ⟨m, hm, rfl⟩ := hinv y hy hcy
                exact ⟨m, by omega, rfl⟩
              · exact ⟨n, by omega, rfl⟩
            · intro m hm
              rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
              · exact hfails' m hm
              · exact ⟨u, hlook, hp'⟩
      _ = (∑ u, ind (powOk b (Keccak.lane u 2) = true) * A (challengeOf u)) /
            Fintype.card KeccakState +
          (∑ u, ind (powOk b (Keccak.lane u 2) = false)) / Fintype.card KeccakState *
            (missProb b ^ count + avgA) + R := by
          rw [avg_add_const, Finset.sum_add_distrib, ENNReal.add_div, ← Finset.sum_mul,
            ENNReal.mul_div_right_comm]
      _ = 2⁻¹ ^ b * avgA + missProb b * (missProb b ^ count + avgA) + R := by
          rw [avg_miss_eq hb, sum_powOk_mul_challengeOf_div, sum_powOk_lane_div_eq hb,
            ← sum_challengeOf_div]
      _ = missProb b ^ (count + 1) + avgA + R := by
          have h1 : 2⁻¹ ^ b + missProb b = (1 : ℝ≥0∞) := by
            rw [missProb]
            exact add_tsub_cancel_of_le (pow_le_one₀ bot_le (by norm_num))
          rw [mul_add, pow_succ]
          calc 2⁻¹ ^ b * avgA + (missProb b * missProb b ^ count + missProb b * avgA) + R
              = missProb b ^ count * missProb b + (2⁻¹ ^ b + missProb b) * avgA + R := by ring
            _ = _ := by rw [h1, one_mul]

end Search

end
end LeanVM.Protocol.Compile.Rom
