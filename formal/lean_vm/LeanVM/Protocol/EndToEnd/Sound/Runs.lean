/-
  LeanVM.Protocol.EndToEnd.Sound.Runs

  Facts about runs of the compiled verifier the knowledge statement reads: the random-oracle
  theorem for any bad event that implies doom on accepted proofs, the extracted history of an
  accepted run as a return of the program with well-shaped commitments, and the shape of the
  first phases' runs.
-/

module

public import LeanVM.Protocol.Compile.Rom.Sound
public import LeanVM.Protocol.EndToEnd.Sound.Frame

/-!
# Runs of the compiled verifier

* `romSound_of_imp`: `romSound` (`LeanVM.Protocol.Compile.Rom.Sound`) for any bad event that,
  on a proof the seeded verifier accepts with every hash answered by the final cache, implies
  that a boundary prefix of the extracted history is doomed. The knowledge statement's event
  ("accepted, and the extractor finds no witness") is one.
* `xrun_after`: the extracted history of a compiled run that returns `a` is a history of the
  program that returns `a`, and every commitment in it holds a well-shaped word;
  `after_extractedHistory`: hence for an accepted proof.
* `commitStack_after_ret`, `readSizes_ne_ret`, `verifyExecution_ne_ret`,
  `verifyBusBalance_ne_ret`: the shapes of the first phases' runs.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-! ## The random-oracle theorem for an event that implies doom -/

/-- Some boundary prefix of the extracted history of the seeded verifier's run of `P` on `π`,
under the answers of the cache `c`, is doomed. -/
def DoomedRun {P : Prog Bool} (C : Cert P) (σ : Seed) (π : Proof) (c : HashSpec.QueryCache) :
    Prop :=
  ∃ h₀, h₀ <+: extractedHistory (fun x ↦ c x) σ P π ∧ Boundary h₀ ∧ C.D h₀

/-- **The random-oracle theorem for any event that implies doom on accepted proofs.** If, on
every statement and proof the statement's seeded verifier accepts with the hashes answered by the
cache, the event `bad` implies that a boundary prefix of the extracted history is doomed, then
the probability that the verifier accepts the adversary's statement and proof while `bad` holds
is at most romSound's bound. -/
theorem romSound_of_imp {X : Type} (P : Prog Bool) (C : Cert P) (σ : Seeds X)
    (hroot : ∀ x, RootOk P (σ.root x)) (εmax : ℝ≥0∞)
    (hε : ∀ h, (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax)
    (A : OracleComp HashSpec (X × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA)
    (QV : ℕ) (hV : ∀ z, IsTotalQueryBound (verifierFam σ P z) QV)
    (bad : X × Proof → HashSpec.QueryCache → Prop)
    (hbad : ∀ z c, Rom.verify (fun x ↦ c x) (σ.seed z.1) (nodeAt P (σ.root z.1)) z.2 =
      some true → bad z c → Doomed C σ z c) :
    Pr{let z ← romExperiment A (verifierFam σ P)}[z.1.2 = true ∧ bad z.1.1 z.2] ≤
      (QA + QV : ℕ) * (εmax + failBound σ (QA + QV)) := by
  refine prEvent_romExperiment_le_of_logFreshStepBelow (QA + QV) ?_ (pot_nil C.D σ P) A
    (verifierFam σ P) QA QV hA hV le_rfl bad ?_
  · intro ℓ t hℓ ht
    refine (step_ineq C hε ℓ t ht).trans (add_le_add le_rfl (add_le_add le_rfl ?_))
    rw [failBound, card_digest, Nat.cast_pow, Nat.cast_ofNat]
    refine ENNReal.div_le_div_right ?_ _
    exact_mod_cast Nat.mul_le_mul_left _ hℓ
  · intro z hz hacc hb
    by_cases hf : Fail σ z.2
    · simp only [pot, hf, ↓reduceIte, le_refl]
    · have hv := verifyFam_of_mem_support_logExperiment A hz hacc
      exact final_ineq C hf (hroot _) hv (hbad z.1.1 (cacheOf z.2) hv hb)

/-! ## The extracted history of an accepted run -/

section XRun

variable (H : Bytes → Option Digest)

/-- **The extracted history of a compiled run is a run of the program**: it extends the
starting history by a history along which the program returns the run's value, and every
commitment in it holds a well-shaped word. -/
theorem xrun_after {α : Type} :
    ∀ (p : Prog α) (s : St) (h : List Ev) {a : α} {s' : St} {hist : List Ev},
      xrun H p s h = some (a, s', hist) →
        ∃ l, hist = h ++ l ∧ p.after l = some (.ret a) ∧
          ∀ ht w W, Ev.commit ht w W ∈ l → WellShaped w W
  | .ret a, s, h, _, _, _, hr => by
    simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -, rfl⟩ := hr
    exact ⟨[], by simp, rfl, by simp⟩
  | .fail, s, h, _, _, _, hr => by simp [xrun] at hr
  | .read k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, hr⟩ := hr
      obtain ⟨l, rfl, hl, hw⟩ := xrun_after _ _ _ hr
      refine ⟨_ :: l, List.append_assoc _ _ _, by simpa [Prog.after] using hl, ?_⟩
      intro ht w W hm
      simp only [List.mem_cons, reduceCtorEq, false_or] at hm
      exact hw _ _ _ hm
  | .sample k, s, h, _, _, _, hr => by
    simp only [xrun, Option.bind_eq_some_iff] at hr
    obtain ⟨_, _, hr⟩ := hr
    obtain ⟨l, rfl, hl, hw⟩ := xrun_after _ _ _ hr
    refine ⟨_ :: l, List.append_assoc _ _ _, by simpa [Prog.after] using hl, ?_⟩
    intro ht w W hm
    simp only [List.mem_cons, reduceCtorEq, false_or] at hm
    exact hw _ _ _ hm
  | .grind bits k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, _, _, _, _, hr⟩ := hr
      split at hr
      · obtain ⟨l, rfl, hl, hw⟩ := xrun_after _ _ _ hr
        refine ⟨_ :: l, List.append_assoc _ _ _, by simpa [Prog.after] using hl, ?_⟩
        intro ht w W hm
        simp only [List.mem_cons, reduceCtorEq, false_or] at hm
        exact hw _ _ _ hm
      · simp at hr
  | .commit height width k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨_, _, _, _, hr⟩ := hr
      split at hr
      · obtain ⟨l, rfl, hl, hw⟩ := xrun_after _ _ _ hr
        refine ⟨_ :: l, List.append_assoc _ _ _, by simpa [Prog.after] using hl, ?_⟩
        intro ht w W hm
        rcases List.mem_cons.1 hm with he | hm
        · simp only [Ev.commit.injEq] at he
          obtain ⟨-, rfl, rfl⟩ := he
          exact wellShaped_extract _ _ _ _
        · exact hw _ _ _ hm
      · simp at hr
    · simp at hr
  | .query i ps k, s, h, _, _, _, hr => by
    simp only [xrun] at hr
    split at hr
    · simp at hr
    · split at hr
      · obtain ⟨l, rfl, hl, hw⟩ := xrun_after _ _ _ hr
        refine ⟨_ :: l, List.append_assoc _ _ _, by simpa [Prog.after] using hl, ?_⟩
        intro ht w W hm
        simp only [List.mem_cons, reduceCtorEq, false_or] at hm
        exact hw _ _ _ hm
      · simp at hr

/-- **An accepted proof's extracted history is an accepting history of the program**, whose
commitments hold well-shaped words. -/
theorem after_extractedHistory {σ : Seed} {P : Prog Bool} {π : Proof}
    (hv : Rom.verify H σ P π = some true) :
    P.after (extractedHistory H σ P π) = some (.ret true) ∧
      ∀ ht w W, Ev.commit ht w W ∈ extractedHistory H σ P π → WellShaped w W := by
  obtain ⟨seed, s, -, hx⟩ := xrun_of_verify hv
  obtain ⟨l, hl, ha, hw⟩ := xrun_after H P _ [] hx
  simp only [List.nil_append] at hl
  rw [hl]
  exact ⟨ha, hw⟩

end XRun

/-! ## The first phases' runs -/

/-- The announced sizes are read: `readSizes` does not return without an event. -/
theorem readSizes_ne_ret (bytecode : List K) (a : Layout × ℕ) : readSizes bytecode ≠ .ret a := by
  intro h
  obtain ⟨x, hx, -⟩ := bind_eq_ret_iff h
  rw [show 2 + tables.length = 7 + 1 from rfl] at hx
  simp [Prog.readN, Prog.readE, Prog.bind] at hx

/-- `verify_execution` does not return without an event. -/
theorem verifyExecution_ne_ret (bytecode : List K) (publicInput : Digest) (u : Unit) :
    verifyExecution .computed bytecode publicInput ≠ .ret u := by
  intro h
  obtain ⟨a, ha, -⟩ := bind_eq_ret_iff h
  exact readSizes_ne_ret bytecode a ha

/-- The bus phase starts with its fingerprint challenges. -/
theorem verifyBusBalance_ne_ret (layout : Layout) (b : BusResult) :
    verifyBusBalance .computed layout ≠ .ret b := by
  intro h
  obtain ⟨x, hx, -⟩ := bind_eq_ret_iff h
  simp [busBits, Prog.sampleN, Prog.sampleE, Prog.bind] at hx

/-- **The stack's root returns after exactly one commitment**, of the shape of the ladder's first
level. -/
theorem commitStack_after_ret {logN logInvRate : ℕ} {m : List Ev}
    (h : (commitStack logN logInvRate).after m = some (.ret ())) :
    ∃ level rest W, deriveConfig logN logInvRate = some (level :: rest) ∧
      m = [Ev.commit (levelShape logN level (2 ^ level.fold)).1
        (levelShape logN level (2 ^ level.fold)).2 W] := by
  obtain ⟨cfg, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret h
  rcases hc : deriveConfig logN logInvRate with _ | c
  · rw [hc] at h1
    cases l₁ with
    | nil => simp [Verifier.liftOption, Prog.after] at h1
    | cons e es => cases e <;> simp [Verifier.liftOption, Prog.after] at h1
  · rw [hc] at h1
    obtain rfl : l₁ = [] := by
      cases l₁ with
      | nil => rfl
      | cons e es => cases e <;> simp [Verifier.liftOption, Prog.after] at h1
    simp only [Verifier.liftOption, Prog.after, Option.some.injEq, Prog.ret.injEq] at h1
    subst h1
    rcases c with _ | ⟨level, rest⟩
    · cases l₂ with
      | nil => simp [Prog.after] at h2
      | cons e es => cases e <;> simp [Prog.after] at h2
    · refine ⟨level, rest, ?_⟩
      cases l₂ with
      | nil => simp [Prog.after, Prog.commitP] at h2
      | cons e es =>
        cases e with
        | commit ht w W =>
          simp only [Prog.commitP, Prog.after] at h2
          split_ifs at h2 with hs
          · cases es with
            | nil => exact ⟨W, rfl, by simp [hs.1, hs.2]⟩
            | cons e' es' => cases e' <;> simp [Prog.after] at h2
        | _ => simp [Prog.after, Prog.commitP] at h2

end
end LeanVM.Protocol.EndToEnd.Sound
