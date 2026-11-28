/-
  LeanVM.Protocol.Relation.Avail

  Without failure, an accepted proof's seed and cut verifier are answered by the adversary's part
  of the log, or the final query's proof of work hits on a fresh answer of the verifier.
-/

module

public import LeanVM.Protocol.Relation.Cut
public import LeanVM.Protocol.Compile.Rom.Chain
public import LeanVM.Protocol.Extraction.Merkle

/-!
# What the extractor can read

From tag `formal-bus-archive`, `EndToEnd/Sound/Avail.lean`.

The agreement-set extractor reads the seed and replays the cut verifier on the answers of the
adversary's part of the log, its first `k` entries. Without failure, the seed's hash precedes its
permutation (`lt_of_laneDigest`), and the cut verifier's permutations follow it in order
(`replay_chain`), as does the final query's proof of work after the cut (`absorb_chain`,
`duplex_chain`). So either the first `k` entries answer the seed and every permutation of the cut
(`Avail`), or the final proof of work's permutation is first answered at an entry `j ≥ k`, a fresh
answer of the verifier, which hits it (`FinalHit`, read off the log before it: the replay on its
answers is the same). `avail_or_hit` says so for every accepted proof.

Also the keys the extractor is given: any list covering the hash answers gives the same words
(`extractAS_keys_congr`), the log's hash inputs cover its answers (`keysCover_lookH`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom

@[expose] public section

/-! ## The keys -/

/-- **The computed leaves do not depend on the covering keys.** -/
theorem committedWordC_keys_congr {answers : Bytes → Option Digest} {keys keys' : List Bytes}
    (hc : Extraction.MerkleProofs.KeysCover answers keys)
    (hc' : Extraction.MerkleProofs.KeysCover answers keys') :
    Extraction.committedWordC answers keys = Extraction.committedWordC answers keys' := by
  funext root height width
  simp only [Extraction.committedWordC, Extraction.committedLeaves,
    Extraction.MerkleProofs.subtreeLeaves_congr (Extraction.MerkleProofs.preimage_keys_congr hc hc')]

/-- A covering key list makes the answers' support finite. -/
theorem finite_of_keysCover {answers : Bytes → Option Digest} {keys : List Bytes}
    (hc : Extraction.MerkleProofs.KeysCover answers keys) : {x | answers x ≠ none}.Finite := by
  refine (List.finite_toSet keys).subset fun x hx ↦ ?_
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hx
  exact hc x d hd

/-- **The keys of a finite support cover it.** -/
theorem keysCover_supportKeys {answers : Bytes → Option Digest}
    (h : {x | answers x ≠ none}.Finite) :
    Extraction.MerkleProofs.KeysCover answers (Extraction.supportKeys answers) := by
  intro x d hx
  simp only [Extraction.supportKeys, h, ↓reduceDIte, Finset.mem_toList, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq, hx]
  exact Option.some_ne_none d

/-- The paths' byte strings cover their evaluations. -/
theorem keysCover_hashesOf (P : List (Bytes × Digest)) :
    Extraction.MerkleProofs.KeysCover (lookupEvaluation P) (P.map (·.1)) := by
  intro x d h
  simp only [lookupEvaluation, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, -⟩ := h
  have hpx := List.find?_some hp
  simp only [decide_eq_true_eq] at hpx
  exact List.mem_map.mpr ⟨p, List.mem_of_find?_eq_some hp, hpx⟩

/-- **The hash inputs of a log cover its hash answers.** -/
theorem keysCover_lookH (ℓ : Log) : Extraction.MerkleProofs.KeysCover (lookH ℓ) (hIns ℓ) := by
  intro x d h
  obtain ⟨i, hi, hei, -⟩ := (lookH_eq_some_iff ℓ x d).mp h
  have hmem : (.inl (x, d) : Entry) ∈ ℓ := by
    rw [← hei]
    exact List.getElem_mem hi
  exact List.mem_map.mpr ⟨(x, d), mem_leftOf.mpr hmem, rfl⟩

/-- **The extraction does not depend on which covering keys it is given.** -/
theorem extractAS_keys_congr (program : LeanIsaProgram) (input : PublicInput)
    {H : Bytes → Option Digest} {keys keys' : List Bytes}
    (hc : Extraction.MerkleProofs.KeysCover H keys)
    (hc' : Extraction.MerkleProofs.KeysCover H keys')
    (F : KeccakState → Option KeccakState) (π : Proof) :
    extractAS program input H keys F π = extractAS program input H keys' F π := by
  unfold extractAS finishAS
  rw [committedWordC_keys_congr hc hc']

/-! ## The seed -/

/-- The seed of `seedWithHash` with answers in `Option`: the bytecode's hash, then the
permutation of the initial state. -/
theorem leanVmSeed_run_option (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)
    (bc : List K) (pd : Digest) :
    (leanVmSeed bc pd).run H F =
      (H (versionTag ++ bc.flatMap K.toBytes)).bind fun d ↦ F (seedInput d pd) := by
  rcases hH : H (versionTag ++ bc.flatMap K.toBytes) with _ | d <;>
    simp [Seed.run, Seed.hsRun, leanVmSeed, hH, bind, pure]

/-- **The extractor is monotone in its permutation answers**: answers that extend the ones it
returned an execution on give the same execution. -/
theorem extractAS_mono {program : LeanIsaProgram} {input : PublicInput}
    {H : Bytes → Option Digest} {keys : List Bytes} {F F' : KeccakState → Option KeccakState}
    {π : Proof} {t : Execution program} (h : extractAS program input H keys F π = some t)
    (hF : ∀ x y, F x = some y → F' x = some y) :
    extractAS program input H keys F' π = some t := by
  unfold extractAS at h ⊢
  obtain ⟨seed, hseed, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  have hseed' : (leanVmSeed (bytecodeWords program) (publicInputDigest input)).run H F' =
      some seed := by
    rw [leanVmSeed_run_option] at hseed ⊢
    obtain ⟨d, hd, ht⟩ := Option.bind_eq_some_iff.mp hseed
    rw [hd, Option.bind_some]
    exact hF _ _ ht
  rw [hseed', Option.bind_some, replayU_mono hr hF, Option.bind_some]
  exact h

variable {X : Type} {σs : Seeds X} {ℓ : Log}

/-- **The seed's chain**: without failure, the seed is the answer of a permutation entry `i₀`,
and a prefix of the log that does not give the seed ends at or before it. -/
theorem seed_chain (hf : ¬ Fail σs ℓ) {bc : List K} {pd : Digest} {seed : KeccakState}
    (h : (leanVmSeed bc pd).run (lookH ℓ) (lookF ℓ) = some seed) :
    ∃ i₀, OutAt ℓ i₀ seed ∧
      ∀ m, (leanVmSeed bc pd).run (lookH (ℓ.take m)) (lookF (ℓ.take m)) ≠ some seed → m ≤ i₀ := by
  rw [leanVmSeed_run_option] at h
  obtain ⟨d, hd, ht⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e, he, hee, hen⟩ := (lookH_eq_some_iff ℓ _ d).mp hd
  obtain ⟨i₀, hi₀, hei, hin⟩ := (lookF_eq_some_iff ℓ _ seed).mp ht
  have hlt : e < i₀ := lt_of_laneDigest hf he hi₀ hee hei (laneDigest_seedInput d pd)
  refine ⟨i₀, ⟨hi₀, _, hei⟩, fun m hm ↦ ?_⟩
  by_contra hmi
  apply hm
  rw [leanVmSeed_run_option, lookH_take_of_first he hee hen (by omega), Option.bind_some]
  exact (FirstAt.lookF_take ⟨hi₀, seed, hei, hin⟩ (by omega)).trans ht

/-! ## Availability -/

/-- **The first `k` entries answer the extractor's queries**: the seed, and every permutation
input of the cut verifier's replay. -/
def Avail (bc : List K) (input : PublicInput) (π : Proof) (ℓ : Log) (k : ℕ) (seed : KeccakState) :
    Prop :=
  (leanVmSeed bc (publicInputDigest input)).run (lookH (ℓ.take k)) (lookF (ℓ.take k)) = some seed ∧
    ∀ x ∈ replayIn (lookF ℓ) (leanVmProgramCut bc input) (startState π seed),
      lookF (ℓ.take k) x = lookF ℓ x

/-- **The final proof of work after the log `ℓ'`**: on `ℓ'`'s answers, the seed, the cut
verifier's replay and the nonce's absorption return; the permutation input that follows, the final
level's query depth, the positions its first sample names and the phase they open. -/
def grindData (bc : List K) (input : PublicInput) (π : Proof) (ℓ' : Log) :
    Option (KeccakState × ℕ × ℕ × List Opening) :=
  ((leanVmSeed bc (publicInputDigest input)).run (lookH ℓ') (lookF ℓ')).bind fun seed ↦
  (replayU (lookF ℓ') (leanVmProgramCut bc input) (startState π seed)).bind fun r ↦
  (Whir.ladder r.1.2.1.1.stackLog r.1.2.1.2).bind fun config ↦
  match r.2.openings, r.2.stream, r.2.sponge.ground with
  | phase :: _, n :: _, none =>
    (absorb (m := Option) (lookF ℓ') r.2.sponge n dsPowNonce).map fun sp1 ↦
      (duplexInput sp1, finalDepth r.1.2.1.1.stackLog 0 config,
        min (128 / finalDepth r.1.2.1.1.stackLog 0 config) (finalCount config), phase)
  | _, _, _ => none

/-- **The answer `u` at the input `t` hits the final proof of work after the log `ℓ'`**: `t` is
the final proof of work's permutation input after `ℓ'`, and `u` hits it. -/
def FinalHit (bc : List K) (input : PublicInput) (π : Proof) (ℓ' : Log) (t u : KeccakState) :
    Prop :=
  ∃ d n phase, grindData bc input π ℓ' = some (t, d, n, phase) ∧
    GrindHit Whir.queryGrindingBits d n phase u

/-- **Available, or a fresh hit**: without failure, on an accepted proof, the first `k` entries
answer the extractor's queries, or a permutation entry `j ≥ k` answers a hit of the final proof
of work after the log before it. -/
theorem avail_or_hit (hf : ¬ Fail σs ℓ) {bc : List K} {input : PublicInput} {π : Proof}
    (hv : Rom.verify (lookH ℓ) (lookF ℓ) (leanVmSeed bc (publicInputDigest input))
      (leanVmVerifierProgram bc (publicInputDigest input)) π = some true) (k : ℕ) :
    ∃ seed, (leanVmSeed bc (publicInputDigest input)).run (lookH ℓ) (lookF ℓ) = some seed ∧
      (Avail bc input π ℓ k seed ∨
        ∃ j, k ≤ j ∧ ∃ (hj : j < ℓ.length) (t u : KeccakState), ℓ[j] = .inr (t, u) ∧
          FinalHit bc input π (ℓ.take j) t u) := by
  obtain ⟨seed, s, hseed, hx⟩ := xrun_of_verify hv
  obtain ⟨d, hxg⟩ := xrun_leanVmProgramG hx
  obtain ⟨s₁, h₁, -, hrep, -, hend⟩ :=
    replayU_cut (F' := lookF ℓ) hxg (by rfl) fun _ _ ↦ rfl
  refine ⟨seed, hseed, ?_⟩
  obtain ⟨i₀, hout₀, hseedk⟩ := seed_chain hf hseed
  obtain ⟨i', hi', hout', hchain⟩ := replay_chain hf _ (startState π seed) hrep hout₀
  obtain ⟨config, hconfig, n, xs, sp1, sp2, phase, rest, hst, hg, hsp1, hsp2, hop, hhit⟩ := hend
  obtain ⟨i₁, hi₁, hout₁, habs⟩ := absorb_chain hf hout' hsp1
  obtain ⟨j, hj, hfirst, hout⟩ := duplex_chain hf hout₁ hsp2
  by_cases hav : Avail bc input π ℓ k seed
  · exact Or.inl hav
  right
  have hkj : k ≤ j := by
    by_contra hkj
    refine hav ⟨?_, fun x hx ↦ ?_⟩
    · by_contra hne
      have := hseedk k hne
      omega
    · obtain ⟨jx, h1, h2, hfx⟩ := hchain x hx
      exact hfx.lookF_take (by omega)
  have hseedj : (leanVmSeed bc (publicInputDigest input)).run (lookH (ℓ.take j))
      (lookF (ℓ.take j)) = some seed := by
    by_contra hne
    have := hseedk j hne
    omega
  have hrepj : replayU (lookF (ℓ.take j)) (leanVmProgramCut bc input) (startState π seed) =
      some ((true, d), s₁) := by
    rw [replayU_congr _ _ fun x hx ↦ ?_]
    · exact hrep
    · obtain ⟨jx, h1, h2, hfx⟩ := hchain x hx
      exact hfx.lookF_take (by omega)
  have habsj : absorb (m := Option) (lookF (ℓ.take j)) s₁.sponge n dsPowNonce = some sp1 := by
    rw [absorb_congr n dsPowNonce fun y hy ↦ ?_]
    · exact hsp1
    · obtain ⟨jy, h1, h2, hfy⟩ := habs y hy
      exact hfy.lookF_take (by omega)
  obtain ⟨hjl, v, hej, -⟩ := hfirst
  obtain ⟨hjl', x, hej'⟩ := hout
  have hv' : v = sp2.state := by
    have := hej.symm.trans hej'
    simp only [Sum.inr.injEq, Prod.mk.injEq] at this
    exact this.2
  rw [hv'] at hej
  refine ⟨j, hkj, hjl, duplexInput sp1, sp2.state, hej, _, _, phase, ?_, hhit⟩
  simp only [grindData, hseedj, Option.bind_some, hrepj, hconfig, hop, hst, hg, habsj,
    Option.map_some]

/-- The seed on a log's answers is the seed on any longer log's. -/
theorem seed_run_append {bc : List K} {pd : Digest} {ℓ' : Log} {seed : KeccakState}
    (h : (leanVmSeed bc pd).run (lookH ℓ') (lookF ℓ') = some seed) (ℓ'' : Log) :
    (leanVmSeed bc pd).run (lookH (ℓ' ++ ℓ'')) (lookF (ℓ' ++ ℓ'')) = some seed := by
  rw [leanVmSeed_run_option] at h ⊢
  obtain ⟨d, hd, ht⟩ := Option.bind_eq_some_iff.mp h
  rw [lookH_append_of_some hd, Option.bind_some, lookF_append_of_some ht]

/-- **The final proof of work's data persists on a longer log.** -/
theorem grindData_append {bc : List K} {input : PublicInput} {π : Proof} {ℓ' : Log}
    {D : KeccakState × ℕ × ℕ × List Opening} (h : grindData bc input π ℓ' = some D) (ℓ'' : Log) :
    grindData bc input π (ℓ' ++ ℓ'') = some D := by
  unfold grindData at h ⊢
  obtain ⟨seed, hseed, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨config, hconfig, h⟩ := Option.bind_eq_some_iff.mp h
  have hF : ∀ x v, lookF ℓ' x = some v → lookF (ℓ' ++ ℓ'') x = some v :=
    fun x v hx ↦ lookF_append_of_some hx ℓ''
  rw [seed_run_append hseed ℓ'', Option.bind_some, replayU_mono hr hF, Option.bind_some, hconfig,
    Option.bind_some]
  revert h
  split
  · intro h
    obtain ⟨sp1, hsp1, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [absorb_mono hsp1 hF, Option.map_some]
  · intro h
    simp at h

end
end LeanVM.Protocol.Relation
