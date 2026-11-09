/-
  LeanVM.Guest.Child.NZRom

  Completeness of the verifier refusing a zero challenge in the random-oracle model: the honest
  prover's proof is rejected only when a proof of work runs out of nonces or a permutation answer
  has a zero challenge, with probability at most `Q · ((1 - 2^-bits)^fuel + 2^-192)`.
-/

module

public import LeanVM.Guest.Child.NZRun
public import LeanVM.Protocol.Compile.Rom.Complete
public import LeanVM.Protocol.Verifier.Cost
public import LeanVM.Protocol.WithHash

/-!
# Refusing a zero challenge, against the random oracles

The potential of `romComplete` (`powPot`) gains a term (`zeroPot`): `1` once some permutation
answer of the log has a zero challenge (`challengeOf u = 0`), `0` before. A fresh permutation
query raises it by at most `2^-192` in expectation (`zeroPot_stepF`: the challenge of a uniform
state is uniform in `E`, `|E| = 2^192`), and a hash query not at all. On an outcome where the
verifier refusing a zero challenge rejects the honest proof (`one_le_pot`): either the prover
failed, and `powPot ≥ 1` as in `romComplete`, or some answer of the log has a zero challenge, or
else the runs read from the log are those at a permutation with no zero challenge, where the
refusing verifier runs as the verifier (`runProof_nz`), which accepts (`runProof_prove`).

`romCompleteNZ`: rejection with probability at most
`(QA + QV) · ((1 - 2^-bits)^fuel + 2^-192)`.
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## The zero-challenge potential -/

open Classical in
/-- `1` once a permutation answer of the log has a zero challenge. -/
noncomputable def zeroPot (ℓ : Log) : ℝ≥0∞ := if ∃ u ∈ fOuts ℓ, challengeOf u = 0 then 1 else 0

theorem zeroPot_nil : zeroPot [] = 0 := by simp [zeroPot, fOuts]

theorem fOuts_append_inr (ℓ : Log) (s u : KeccakState) : fOuts (ℓ ++ [.inr (s, u)]) = fOuts ℓ ++ [u] := by
  simp [fOuts]

theorem fOuts_append_inl (ℓ : Log) (p : Bytes × Digest) : fOuts (ℓ ++ [.inl p]) = fOuts ℓ := by
  simp [fOuts]

theorem zeroPot_append_inl (ℓ : Log) (p : Bytes × Digest) : zeroPot (ℓ ++ [.inl p]) = zeroPot ℓ := by
  simp [zeroPot, fOuts_append_inl]

/-- The challenge of a uniform state is zero with probability `2^-192`. -/
theorem sum_challengeOf_zero :
    (∑ u : KeccakState, ind (challengeOf u = 0)) / Fintype.card KeccakState = (2 : ℝ≥0∞)⁻¹ ^ 192 := by
  rw [sum_challengeOf_div (fun c ↦ ind (c = 0)), card_E,
    Finset.sum_eq_single (0 : E) (fun b _ hb ↦ by simp [ind, hb]) (by simp)]
  simp only [ind, ↓reduceIte]
  rw [Nat.cast_pow, Nat.cast_ofNat, one_div, ENNReal.inv_pow]

/-- **The zero-challenge potential's step**: a fresh permutation query raises it by at most
`2^-192` in expectation. -/
theorem zeroPot_stepF (ℓ : Log) (s : KeccakState) :
    (∑ u, zeroPot (ℓ ++ [.inr (s, u)])) / Fintype.card KeccakState ≤
      zeroPot ℓ + (2 : ℝ≥0∞)⁻¹ ^ 192 := by
  classical
  by_cases hz : ∃ u ∈ fOuts ℓ, challengeOf u = 0
  · have h1 : zeroPot ℓ = 1 := by simp [zeroPot, hz]
    rw [h1]
    refine (avg_le_of_le fun u ↦ ?_).trans le_self_add
    unfold zeroPot
    split <;> simp
  · have h0 : zeroPot ℓ = 0 := by simp [zeroPot, hz]
    have hu : ∀ u, zeroPot (ℓ ++ [.inr (s, u)]) = ind (challengeOf u = 0) := by
      intro u
      unfold zeroPot
      rw [fOuts_append_inr]
      by_cases hc : challengeOf u = 0
      · simp [hc, ind]
      · simp only [List.mem_append, List.mem_singleton]
        have : ¬ ∃ v, (v ∈ fOuts ℓ ∨ v = u) ∧ challengeOf v = 0 := by
          rintro ⟨v, hv | rfl, hv0⟩
          · exact hz ⟨v, hv, hv0⟩
          · exact hc hv0
        simp [this, hc, ind]
    simp only [hu, h0, zero_add]
    exact le_of_eq sum_challengeOf_zero

/-- The two potentials together. -/
noncomputable def nzPot (bits fuel : ℕ) (ℓ : Log) : ℝ≥0∞ := powPot bits fuel ℓ + zeroPot ℓ

/-! ## A state whose challenge is not zero -/

/-- A state whose challenge is `1`. -/
noncomputable def nzState : KeccakState := challengeEquiv.symm (1, fun _ ↦ 0)

theorem challengeOf_nzState : challengeOf nzState ≠ 0 := by
  have h := challengeEquiv_fst nzState
  simp only [nzState, Equiv.apply_symm_apply] at h
  show challengeOf (challengeEquiv.symm (1, fun _ ↦ 0)) ≠ 0
  rw [← h]
  exact one_ne_zero

/-! ## The final inequality -/

/-- **On every outcome where the verifier refusing a zero challenge rejects the honest proof**,
the potential is at least `1`. -/
theorem one_le_nzPot {σ : Seed} {P P' : VerifierProgram Bool} (hNZ : NZ P' P) {S : Strategy} {bits
    fuel : ℕ}
    (hfuel : fuel ≤ 2 ^ 64) (hfuel0 : fuel ≠ 0)
    (hc : ∀ chal, runI P S chal = some true) (hs : ∀ chal, shapedI P S chal)
    (hg : ∀ h b k, P.after h = some (.grind b k) → b = bits)
    {z : (Proof × Bool) × Log} (hz : z ∈ support (logExperiment (honestComp σ P S fuel)
      (verifierComp σ P'))) (hrej : z.1.2 = false) :
    1 ≤ nzPot bits fuel z.2 := by
  set ℓ := z.2
  have h := (simulateQ_look_of_mem_support _ [] z hz).2 ℓ (List.prefix_refl _)
  rw [simulateQ_bind] at h
  obtain ⟨π, hA, h⟩ := Option.bind_eq_some_iff.mp h
  rw [simulateQ_map] at h
  obtain ⟨b, hb, hπb⟩ := Option.map_eq_some_iff.mp h
  have hzb : b = false := by rw [← hrej, ← hπb]
  subst hzb
  -- The prover's run against the log.
  simp only [honestComp, simulateQ_bind, simulateQ_seedRun, simulateQ_proveM,
    simulateQ_pure] at hA
  change (σ.run (lookH ℓ) (lookF ℓ)).bind (fun seed ↦ (proveM (lookH ℓ) (lookF ℓ) P S seed
    fuel).bind fun r ↦ some (r.getD ⟨[], []⟩)) = some π at hA
  obtain ⟨seed, hseed, hA⟩ := Option.bind_eq_some_iff.mp hA
  obtain ⟨r, hr, hA⟩ := Option.bind_eq_some_iff.mp hA
  cases r with
  | some π' =>
    -- The prover succeeded: a zero challenge in the log, or the verifier accepts.
    cases hA
    classical
    by_cases hzero : ∃ u ∈ fOuts ℓ, challengeOf u = 0
    · have : zeroPot ℓ = 1 := by simp [zeroPot, hzero]
      rw [nzPot, this]
      exact le_add_self
    exfalso
    let Ht : Bytes → Digest := fun x ↦ (lookH ℓ x).getD default
    let Ft : KeccakState → KeccakState := fun s ↦ (lookF ℓ s).getD nzState
    have hH : ∀ x u, lookH ℓ x = some u → Ht x = u := fun x u hx ↦ by simp [Ht, hx]
    have hF : ∀ s u, lookF ℓ s = some u → Ft s = u := fun s u hs ↦ by simp [Ft, hs]
    have hFnz : ∀ s, challengeOf (Id.run (Ft s)) ≠ 0 := by
      intro s
      show challengeOf (Ft s) ≠ 0
      cases hl : lookF ℓ s with
      | none => simp only [Ft, hl, Option.getD_none]; exact challengeOf_nzState
      | some u =>
        simp only [Ft, hl, Option.getD_some]
        intro h0
        obtain ⟨i, hi, hei, -⟩ := (lookF_eq_some_iff ℓ s u).mp hl
        exact hzero ⟨u, mem_fOuts_of_getElem hi hei, h0⟩
    have hseed' : σ.run (m := Id) Ht Ft = seed := by
      have := simulateQ_id_of_look ℓ Ht Ft hH hF (σ.run callKeccak256 callKeccakF1600) seed
        (by rw [simulateQ_seedRun]; exact hseed)
      rwa [simulateQ_seedRun] at this
    have hπ : prove Ht Ft P S seed fuel = some π' := by
      have := simulateQ_id_of_look ℓ Ht Ft hH hF (proveM callKeccak256 callKeccakF1600 P S seed fuel) (some π')
        (by rw [simulateQ_proveM]; exact hr)
      rw [simulateQ_proveM] at this
      rw [← proveM_id]
      exact this
    have hb' : simulateQ (lookImpl ℓ) (verifierComp σ P' π') = some false := hb
    have hv := simulateQ_id_of_look ℓ Ht Ft hH hF (verifierComp σ P' π') false hb'
    rw [simulateQ_verify] at hv
    have hacc := runProof_prove Ht Ft P S seed fuel hc hs hπ
    have hv' : runProofWithHash (m := Id) Ht Ft P' (σ.run (m := Id) Ht Ft) π' = false := hv
    rw [hseed', runProof_nz Ht Ft hFnz hNZ, hacc] at hv'
    cases hv'
  | none =>
    -- The prover failed: some proof-of-work search failed.
    have hr' : proveFromM (lookH ℓ) (lookF ℓ) S fuel P ⟨seed, []⟩ [] [] = some none := by
      change (proveFromM (lookH ℓ) (lookF ℓ) S fuel P ⟨seed, []⟩ [] []).bind _ = _ at hr
      obtain ⟨t, ht, hr⟩ := Option.bind_eq_some_iff.mp hr
      cases t with
      | none => exact ht
      | some _ => cases hr
    obtain ⟨h', b', k, sp, ha, hsp, hf⟩ :=
      proveFromM_eq_some_none S fuel P ⟨seed, []⟩ [] [] (VerifierProgram.after.eq_1 P)
          ⟨by simp, by simp⟩ hr'
    rw [hg h' b' k ha] at hf
    obtain ⟨-, hall⟩ := findNonceM_eq_some_none hf
    -- The position of the search, the same for every nonce.
    obtain ⟨κ, hκ, hnon⟩ : ∃ κ : PowKey, KeyOk κ ∧ ∀ n < fuel, ∃ u,
        lookF ℓ (nonceInput κ.1 κ.2 n) = some u ∧ powOk bits (nonceOf n) (challengeOf u) = false := by
      by_cases h4 : sp.pending.length = 4
      · obtain ⟨r0, hr0, -⟩ := hall 0 (Nat.pos_of_ne_zero hfuel0)
        obtain ⟨c0, ps0, u0, -, -, hif⟩ := powStepM_option hr0
        simp only [h4, ↓reduceIte] at hif
        obtain ⟨-, v, hv, -⟩ := hif
        refine ⟨(capOf v, []), ⟨by simp, by simp⟩, fun n hn ↦ ?_⟩
        obtain ⟨r, hr, hp⟩ := hall n hn
        obtain ⟨c, ps, u, hu, hru, hif⟩ := powStepM_option hr
        simp only [h4, ↓reduceIte] at hif
        obtain ⟨rfl, v', hv', rfl⟩ := hif
        rw [hv] at hv'
        cases hv'
        exact ⟨u, hu, by rw [← hru]; exact hp⟩
      · refine ⟨(capOf sp.state, sp.pending), ⟨by dsimp only; have := hsp.1; omega, hsp.2⟩,
          fun n hn ↦ ?_⟩
        obtain ⟨r, hr, hp⟩ := hall n hn
        obtain ⟨c, ps, u, hu, hru, hif⟩ := powStepM_option hr
        simp only [h4, ↓reduceIte] at hif
        obtain ⟨rfl, rfl⟩ := hif
        exact ⟨u, hu, by rw [← hru]; exact hp⟩
    -- Its term is `1`.
    have hS : ¬ Solved bits fuel ℓ κ := by
      rintro ⟨n, hn, d, hd, hp⟩
      obtain ⟨d', hd', hp'⟩ := hnon n hn
      rw [hd'] at hd
      cases hd
      rw [hp'] at hp
      cases hp
    have hT : (tried fuel ℓ κ).card = fuel := by
      have : tried fuel ℓ κ = Finset.range fuel := by
        refine Finset.filter_true_of_mem fun n hn ↦ ?_
        obtain ⟨d, hd, -⟩ := hnon n (Finset.mem_range.mp hn)
        simp [hd]
      rw [this, Finset.card_range]
    have hterm : powTerm bits fuel ℓ κ = 1 := by
      simp [powTerm, hS, hT]
    have hmem : κ ∈ keys fuel ℓ := by
      obtain ⟨u, hu, -⟩ := hnon 0 (Nat.pos_of_ne_zero hfuel0)
      obtain ⟨i, hi, hei, -⟩ := (lookF_eq_some_iff ℓ _ u).mp hu
      exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨_, mem_fIns_of_getElem hi hei,
        keyOf_nonceInput hfuel hκ (Nat.pos_of_ne_zero hfuel0)⟩)
    rw [← hterm]
    exact (Finset.single_le_sum (fun _ _ ↦ bot_le) hmem).trans le_self_add

/-! ## The bound -/

/-- **Completeness of the verifier refusing a zero challenge in the random-oracle model.** For a
verifier program `P` whose proofs of work all ask for `bits ∈ [1, 64]` bits, a strategy `S`
that wins every interactive run of `P` with well-shaped words, `P'` refusing zero challenges of
`P` (`NZ P' P`), both of cost `n`, the seeding `σ`, and a fuel of at most `2^64` nonces: the
verifier `P'` rejects the honest prover's proof with probability at most
`Q · ((1 - 2^-bits)^fuel + 2^-192)`, `Q` the queries of the prover and the verifier together. -/
theorem romCompleteNZ (P P' : VerifierProgram Bool) (hNZ : NZ P' P) (S : Strategy) (σ : Seed)
    {bits fuel height n : ℕ} (hb0 : bits ≠ 0) (hb : bits ≤ 64) (hfuel : fuel ≤ 2 ^ 64)
    (hg : ∀ h b k, P.after h = some (.grind b k) → b = bits)
    (hc : ∀ chal, runI P S chal = some true) (hs : ∀ chal, shapedI P S chal)
    (hP : P.CostLE height n) (hP' : P'.CostLE height n) :
    Pr{let z ← romExperiment (honestComp σ P S fuel) (verifierComp σ P')}[z.1.2 = false] ≤
      ((σ.hs.length + 1 + n * proverFactor height fuel + (σ.hs.length + 1 + n / 4) : ℕ) :
        ℝ≥0∞) * (missProb bits ^ fuel + (2 : ℝ≥0∞)⁻¹ ^ 192) := by
  set QA := σ.hs.length + 1 + n * proverFactor height fuel
  set QV := σ.hs.length + 1 + n / 4
  by_cases hfuel0 : fuel = 0
  · subst hfuel0
    refine (prEvent_le_one _).trans ?_
    rw [pow_zero]
    calc (1 : ℝ≥0∞) ≤ ((QA + QV : ℕ) : ℝ≥0∞) := by exact_mod_cast (show 1 ≤ QA + QV by omega)
      _ = ((QA + QV : ℕ) : ℝ≥0∞) * 1 := (mul_one _).symm
      _ ≤ _ := by gcongr; exact le_self_add
  have hA := isTotalQueryBound_honestComp (σ := σ) hP S fuel
  have hV : ∀ π, IsTotalQueryBound (verifierComp σ P' π) QV :=
    isTotalQueryBound_verifierComp hP' σ
  rw [prEvent_romExperiment_eq_logExperiment _ _ fun r _ ↦ r.2 = false]
  have hstep : LogFreshStepBound (nzPot bits fuel) (missProb bits ^ fuel + (2 : ℝ≥0∞)⁻¹ ^ 192) := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ x _ ↦ ?_, fun ℓ s hs' ↦ ?_⟩
    · simp only [nzPot, powPot_append_inl, zeroPot_append_inl]
      exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
    · have h1 := powPot_stepF hb0 hb hfuel ((lookR_eq_none_iff ℓ s).mpr hs')
        (bits := bits) (fuel := fuel)
      have h2 := zeroPot_stepF ℓ s
      simp only [nzPot]
      rw [Finset.sum_add_distrib, ENNReal.add_div]
      calc _ ≤ (powPot bits fuel ℓ + missProb bits ^ fuel) + (zeroPot ℓ + (2 : ℝ≥0∞)⁻¹ ^ 192) :=
            add_le_add h1 h2
        _ = _ := by ring
  have h := prEvent_run_loggedRO_le_of_freshStepBound hstep _ (QA + QV)
    (isTotalQueryBound_bind hA fun a ↦ (isQueryBound_map_iff (verifierComp σ P' a) _ QV _ _).mpr
      (hV a)) [] (fun r _ ↦ r.2 = false)
    (fun z hz hrej ↦ one_le_nzPot hNZ hfuel hfuel0 hc hs hg hz hrej)
  rw [nzPot, powPot_nil, zeroPot_nil, zero_add, zero_add] at h
  exact h

/-! ## The program refusing zero challenges -/

/-- The verifier program refusing a zero fold, tail or level batching challenge. -/
def nzProgram (bytecode : List K) (publicInput : Digest) : VerifierProgram Bool :=
  (execWith computedBytecodeValue Limits.verifyStackedOpeningNZ bytecode publicInput).bind fun _ ↦ VerifierProgram.ret true

theorem leanVmProgram_execWith (bytecode : List K) (publicInput : Digest) :
    leanVmVerifierProgram bytecode publicInput =
      (execWith computedBytecodeValue verifyStackedOpening bytecode publicInput).bind fun _ ↦ VerifierProgram.ret true := by
  rw [Verifier.leanVmProgram_eq]
  rfl

/-- A refining program costs at most what the refined one costs. -/
theorem costs_of_refines {α : Type} {height : ℕ} {P' P : VerifierProgram α} (h : Limits.Refines
    P' P) :
    ∀ {n : ℕ} {Q : α → Prop}, VerifierProgram.Costs height P n Q → VerifierProgram.Costs height P' n
        Q := by
  induction h with
  | fail P => intro n Q _; trivial
  | ret a => intro n Q hc; exact hc
  | read _ ih => intro n Q hc; exact ⟨hc.1, fun x ↦ ih x (hc.2 x)⟩
  | sample _ ih => intro n Q hc; exact ⟨hc.1, fun x ↦ ih x (hc.2 x)⟩
  | grind _ ih => intro n Q hc; exact ⟨hc.1, ih hc.2⟩
  | commit _ ih => intro n Q hc; exact ⟨hc.1, hc.2.1, ih hc.2.2⟩
  | query _ ih => intro n Q hc; exact ⟨hc.1, fun r ↦ ih r (hc.2 r)⟩

end
end LeanVM.Guest.Child
