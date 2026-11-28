/-
  LeanVM.Prover.Complete.CostRun

  The queries of the compiled verifier's run and of the honest prover's run of a program, from
  its stream and openings (`Wired`) and its other events (`SampLE`).
-/

module

public import LeanVM.Prover.Complete.CostCalc
public import LeanVM.Prover.Complete.Rom
public import LeanVM.Protocol.Compile.Cost

/-!
# The runs' queries

Each node of a run makes a bounded number of queries: a read's absorption at most one permutation,
a challenge at most one, a packed message of `m` at most `m + 1`, a packed draw of `m` at most `m`,
a proof of work two (the verifier) or `2 · fuel + 2` (the prover's search, then its absorption), a
commitment two absorptions (and the prover's tree, `2^(h + 1)` hashes), an opening of `k` positions
of a tree of height `h` at most `k · (1 + h)` hashes (the verifier).

* `qb_run`: the verifier's run of a program `Wired` with `c` stream elements and `nO` openings and of
  `s` other events makes at most `c + s + nO · wireMaxQueries · (1 + wireMaxHeight)` queries.
* `qb_runFrom`: the prover's run of it at most `(c + s) · proverK commitMaxHeight fuel`, its commitments of
  height at most `H`.
-/

@[expose] public section

namespace LeanVM.Prover.Complete.Cost

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier
open LeanVM.Prover LeanVM.Wire
open OracleComp OracleSpec

variable {α β : Type}

/-! ## The sponge's steps -/

theorem qb_duplex (sp : Sponge) : IsTotalQueryBound (duplex callKeccakF1600 sp) 1 :=
  isTotalQueryBound_queryF_bind (n := 0) _ fun _ ↦ isTotalQueryBound_pure' _ 0

theorem qb_absorb (sp : Sponge) (x : E) (tag : ℕ) :
    IsTotalQueryBound (Compile.absorb callKeccakF1600 sp x tag) 1 := by
  unfold Compile.absorb
  split
  · exact isTotalQueryBound_bind (n₂ := 0) (qb_duplex sp) fun _ ↦ isTotalQueryBound_pure' _ 0
  · exact (isTotalQueryBound_pure' _ 0).mono (Nat.zero_le _)

theorem qb_squeeze (sp : Sponge) : IsTotalQueryBound (squeeze callKeccakF1600 sp) 1 := by
  unfold squeeze
  split
  · exact (isTotalQueryBound_pure' _ 0).mono (Nat.zero_le _)
  · exact isTotalQueryBound_bind (n₂ := 0) (qb_duplex sp) fun _ ↦ isTotalQueryBound_pure' _ 0

theorem qb_absorbNonce (sp : Sponge) (n : E) :
    IsTotalQueryBound (absorbNonce callKeccakF1600 sp n) 2 := by
  unfold absorbNonce
  exact isTotalQueryBound_bind (n₁ := 1) (n₂ := 1) (qb_absorb _ _ _) fun _ ↦
    isTotalQueryBound_bind (n₂ := 0) (qb_duplex _) fun _ ↦ isTotalQueryBound_pure' _ 0

theorem qb_absorbPackedChunks : ∀ (fuel : ℕ) (state : KeccakState) (values : List E),
    IsTotalQueryBound (absorbPackedChunks callKeccakF1600 fuel state values) fuel
  | 0, _, _ => trivial
  | _ + 1, _, [] => (isTotalQueryBound_pure' _ 0).mono (Nat.zero_le _)
  | fuel + 1, state, v :: vs => by
    simp only [absorbPackedChunks]
    exact isTotalQueryBound_queryF_bind _ fun st ↦ qb_absorbPackedChunks fuel st _

theorem qb_observePacked (sp : Sponge) (values : List E) :
    IsTotalQueryBound (observePacked callKeccakF1600 sp values) (values.length + 1) := by
  unfold observePacked
  dsimp only
  split
  · exact (isTotalQueryBound_bind (qb_absorbPackedChunks _ _ _) fun _ ↦
      isTotalQueryBound_pure' _ 0).mono (by omega)
  · exact (isTotalQueryBound_bind (qb_duplex sp) fun _ ↦ isTotalQueryBound_bind
      (qb_absorbPackedChunks _ _ _) fun _ ↦ isTotalQueryBound_pure' _ 0).mono (by omega)

theorem qb_squeezePackedChunks : ∀ (fuel : ℕ) (sp : Sponge) (missing : ℕ),
    IsTotalQueryBound (squeezePackedChunks callKeccakF1600 fuel sp missing) fuel
  | 0, _, _ => trivial
  | _ + 1, _, 0 => (isTotalQueryBound_pure' _ 0).mono (Nat.zero_le _)
  | fuel + 1, sp, missing + 1 => by
    simp only [squeezePackedChunks]
    rw [show fuel + 1 = 1 + (fuel + 0) by omega]
    exact isTotalQueryBound_bind (qb_duplex sp) fun sp' ↦ isTotalQueryBound_bind
      (qb_squeezePackedChunks fuel _ _) fun _ ↦ isTotalQueryBound_pure' _ 0

theorem qb_samplesPacked (sp : Sponge) (count : ℕ) :
    IsTotalQueryBound (samplesPacked callKeccakF1600 sp count) count := by
  unfold samplesPacked
  refine (isTotalQueryBound_bind (qb_squeezePackedChunks _ _ _) fun _ ↦
    isTotalQueryBound_pure' _ 0).mono ?_
  omega

/-! ## The verifier's run -/

/-- An opening's queries, at most. -/
def openBound : ℕ := wireMaxQueries * (1 + wireMaxHeight)

/-- **The verifier's run's queries.** -/
theorem qb_run : ∀ (p : VerifierProgram α) (st : VerifierProgramState) (hs : List ℕ)
    (nO c s : ℕ) (Q : α → List ℕ → ℕ → Prop), Wired p hs nO c Q → SampLE p s →
      st.roots.map (·.2.1) = hs →
      IsTotalQueryBound (runWithHash callKeccak256 callKeccakF1600 p st) (c + s + nO * openBound)
  | .ret _, _, _, _, _, _, _, _, _, _ => trivial
  | .fail, _, _, _, _, _, _, _, _, _ => trivial
  | .read k, st, hs, nO, c, s, Q, hw, hsm, hr => by
    simp only [runWithHash]
    split
    · rename_i x xs _ _
      have h1 := hw.1
      exact (isTotalQueryBound_bind (qb_absorb _ _ _) fun sp ↦
        qb_run (k x) { st with sponge := sp, stream := xs } hs nO (c - 1) s Q (hw.2 x) (hsm.2 x)
          hr).mono
        (by omega : 1 + (c - 1 + s + nO * openBound) ≤ c + s + nO * openBound)
    · trivial
  | .sample k, st, hs, nO, c, s, Q, hw, hsm, hr => by
    simp only [runWithHash]
    have h1 := hsm.1
    exact (isTotalQueryBound_bind (qb_squeeze _) fun r ↦ by
      obtain ⟨ch, sp⟩ := r
      exact qb_run (k ch) { st with sponge := sp } hs nO c (s - 1) Q (hw ch) (hsm.2 ch) hr).mono
      (by omega : 1 + (c + (s - 1) + nO * openBound) ≤ c + s + nO * openBound)
  | .readPacked m k, st, hs, nO, c, s, Q, hw, hsm, hr => by
    simp only [runWithHash]
    split
    · have h1 := hw.1
      have h2 := hsm.1
      refine (isTotalQueryBound_bind (qb_observePacked _ _) fun sp ↦
        qb_run (k (st.stream.take m)) { st with sponge := sp, stream := st.stream.drop m } hs nO
          (c - m) (s - 1) Q (hw.2 _) (hsm.2 _) hr).mono ?_
      simp only [List.length_take]
      have : min m st.stream.length ≤ m := Nat.min_le_left _ _
      omega
    · trivial
  | .samplePacked m k, st, hs, nO, c, s, Q, hw, hsm, hr => by
    simp only [runWithHash]
    have h1 := hsm.1
    exact (isTotalQueryBound_bind (qb_samplesPacked _ _) fun r ↦ by
      obtain ⟨chs, sp⟩ := r
      exact qb_run (k chs) { st with sponge := sp } hs nO c (s - m) Q (hw chs) (hsm.2 chs)
        hr).mono
      (by omega : m + (c + (s - m) + nO * openBound) ≤ c + s + nO * openBound)
  | .grind bits k, st, hs, nO, c, s, Q, hw, hsm, hr => by
    simp only [runWithHash]
    split
    · refine (isTotalQueryBound_bind (qb_absorbNonce _ _) fun r ↦ ?_).mono
        (show 2 + ((c - 1) + (s - 1) + nO * openBound) ≤ _ by have := hw.1; have := hsm.1; omega)
      split
      · exact qb_run k _ hs nO (c - 1) (s - 1) Q hw.2 hsm.2 hr
      · trivial
    · trivial
  | .commit ht w k, st, hs, nO, c, s, Q, hw, hsm, hr => by
    simp only [runWithHash]
    split
    · refine (isTotalQueryBound_bind (qb_absorb _ _ _) fun sp0 ↦ isTotalQueryBound_bind
        (qb_absorb _ _ _) fun sp1 ↦ qb_run k _ (hs ++ [ht]) nO (c - 2) (s - 1) Q hw.2 hsm.2.2.2
          (by simp [hr])).mono
        (by have := hw.1; have := hsm.2.2.1; omega :
          1 + (1 + (c - 2 + (s - 1) + nO * openBound)) ≤ c + s + nO * openBound)
    · trivial
  | .query i ps k, st, hs, nO, c, s, Q, hw, hsm, hr => by
    simp only [runWithHash]
    split
    · next root ht w phase rest hroot hopen =>
      obtain ⟨hn, ⟨-, hlen, hh, -⟩, hk⟩ := hw
      have hht : hs.getD i 0 = ht := by
        rw [← hr, List.getD_eq_getElem?_getD, List.getElem?_map, hroot]
        rfl
      rw [hht] at hh
      refine (isTotalQueryBound_bind (isTotalQueryBound_openPhase root ht w ps phase) fun o ↦ ?_).mono
        (show ps.length * (1 + ht) + (c + s + (nO - 1) * openBound) ≤ _ from ?_)
      · split
        · exact qb_run _ _ hs (nO - 1) c s Q (hk _) (hsm.2 _) hr
        · trivial
      · have h1 : ps.length * (1 + ht) ≤ openBound :=
          Nat.mul_le_mul hlen (by unfold wireMaxHeight at hh ⊢; omega)
        have h2 : (nO - 1) * openBound + openBound = nO * openBound := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
        omega
    · trivial

/-- **The compiled verifier's queries**, from a seed: the seed's, then the run's. -/
theorem qb_verifierComp {P : VerifierProgram Bool} {nO c s : ℕ}
    {Q : Bool → List ℕ → ℕ → Prop} (hw : Wired P [] nO c Q) (hsm : SampLE P s) (σ : Seed)
    (π : Proof) :
    IsTotalQueryBound (verifierComp σ P π) (σ.hs.length + 1 + (c + s + nO * openBound)) := by
  refine isTotalQueryBound_bind (isTotalQueryBound_seedRun σ) fun seed ↦ ?_
  unfold runProofWithHash
  rw [← Nat.add_zero (c + s + nO * openBound)]
  refine isTotalQueryBound_bind (qb_run P _ [] nO c s Q hw hsm rfl) fun o ↦ ?_
  split <;> trivial

/-! ## The prover's run -/

theorem qb_mapM {γ δ : Type} (f : γ → OracleComp KeccakCalls δ) (k : ℕ)
    (hf : ∀ a, IsTotalQueryBound (f a) k) :
    ∀ l : List γ, IsTotalQueryBound (l.mapM f) (l.length * k)
  | [] => trivial
  | a :: l => by
    simp only [List.mapM_cons, List.length_cons]
    rw [show (l.length + 1) * k = k + (l.length * k + 0) by ring]
    exact isTotalQueryBound_bind (hf a) fun _ ↦ isTotalQueryBound_bind
      (qb_mapM f k hf l) fun _ ↦ isTotalQueryBound_pure' _ 0

theorem qb_arrayMapM {γ δ : Type} (f : γ → OracleComp KeccakCalls δ) (k : ℕ)
    (hf : ∀ a, IsTotalQueryBound (f a) k) (xs : Array γ) :
    IsTotalQueryBound (xs.mapM f) (xs.size * k) := by
  rw [Array.mapM_eq_mapM_toList, map_eq_bind_pure_comp, ← Array.length_toList,
    ← Nat.add_zero (xs.toList.length * k)]
  exact isTotalQueryBound_bind (qb_mapM f k hf xs.toList) fun _ ↦ isTotalQueryBound_pure' _ 0

theorem qb_callH (x : Bytes) : IsTotalQueryBound (callKeccak256 x) 1 :=
  (isTotalQueryBound_queryH_bind (f := pure) x fun _ ↦ isTotalQueryBound_pure' _ 0).mono
    (by simp)

theorem qb_parents (level : Array Digest) (n : ℕ) :
    IsTotalQueryBound (parentsWithHash callKeccak256 level n) n := by
  have := qb_arrayMapM (δ := Digest) (fun j : ℕ ↦ callKeccak256 (digestBytes
    (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default))) 1
    (fun _ ↦ qb_callH _) (Array.range n)
  simpa [parentsWithHash] using this

theorem qb_levels : ∀ (k : ℕ) (level : Array Digest),
    IsTotalQueryBound (levelsWithHash callKeccak256 k level) (2 ^ k)
  | 0, _ => trivial
  | k + 1, level => by
    simp only [levelsWithHash]
    rw [show 2 ^ (k + 1) = 2 ^ k + (2 ^ k + 0) by ring]
    exact isTotalQueryBound_bind (qb_parents level _) fun up ↦
      isTotalQueryBound_bind (qb_levels k up) fun _ ↦ isTotalQueryBound_pure' _ 0

theorem qb_leafDigests (height : ℕ) (word : Word) :
    IsTotalQueryBound (leafDigestsWithHash callKeccak256 height word) (2 ^ height) := by
  have := qb_arrayMapM (δ := Digest) (fun i : ℕ ↦ callKeccak256 ((word i).flatMap K.toBytes)) 1
    (fun _ ↦ qb_callH _) (Array.range (2 ^ height))
  simpa [leafDigestsWithHash] using this

/-- A commitment's tree is built with at most `2^(height + 1)` queries. -/
theorem qb_buildTree (height : ℕ) (word : Word) :
    IsTotalQueryBound (buildTreeWithHash callKeccak256 height word) (2 ^ (height + 1)) := by
  unfold buildTreeWithHash
  rw [show 2 ^ (height + 1) = 2 ^ height + (2 ^ height + 0) by ring]
  exact isTotalQueryBound_bind (qb_leafDigests height word) fun l ↦
    isTotalQueryBound_bind (qb_levels height l) fun _ ↦ isTotalQueryBound_pure' _ 0

theorem qb_searchM (bits : ℕ) (o : Bool) (sp : Sponge) :
    ∀ (count n : ℕ), IsTotalQueryBound (searchM callKeccakF1600 bits o sp n count) (2 * count)
  | 0, _ => trivial
  | count + 1, n => by
    simp only [searchM]
    rw [show 2 * (count + 1) = 2 + 2 * count by ring]
    refine isTotalQueryBound_bind (qb_absorbNonce _ _) fun r ↦ ?_
    split
    · exact (isTotalQueryBound_pure' _ 0).mono (Nat.zero_le _)
    · exact qb_searchM bits o sp count (n + 1)

theorem qb_findNonce (bits : ℕ) (o : Bool) (sp : Sponge) (fuel : ℕ) :
    IsTotalQueryBound (findNonceM callKeccakF1600 bits o sp fuel) (2 * fuel) :=
  qb_searchM bits o sp fuel 0

/-- The prover's queries per event: a tree of height at most `H`, or a proof-of-work search of
`fuel` nonces and its absorption. -/
def proverK (H fuel : ℕ) : ℕ := 2 ^ (H + 1) + 2 * fuel + 2

theorem one_le_proverK (H fuel : ℕ) : 1 ≤ proverK H fuel := by
  unfold proverK; generalize 2 ^ (H + 1) = A; omega

theorem fuel_le_proverK (H fuel : ℕ) : 2 * fuel + 2 ≤ proverK H fuel := by
  unfold proverK; generalize 2 ^ (H + 1) = A; omega

theorem pow_le_proverK (H fuel : ℕ) : 2 ^ (H + 1) + 2 ≤ proverK H fuel := by
  unfold proverK; generalize 2 ^ (H + 1) = A; omega

theorem step_le {c s c' s' u e K : ℕ} (hc : c' + s' + u ≤ c + s) (he : e ≤ u * K) :
    e + (c' + s') * K ≤ (c + s) * K := by
  have := Nat.mul_le_mul_right K hc
  rw [Nat.add_mul] at this
  omega

/-- **The prover's run's queries.** -/
theorem qb_runFrom (fuel : ℕ) : ∀ (p : VerifierProgram α) (S : Option (Script β))
    (sp : Sponge) (cs : List Tree) (hs : List ℕ) (nO c s : ℕ) (Q : α → List ℕ → ℕ → Prop),
    Wired p hs nO c Q → SampLE p s →
      IsTotalQueryBound (runFromWithHash callKeccak256 callKeccakF1600 fuel p S sp cs)
        ((c + s) * proverK commitMaxHeight fuel)
  | .ret _, _, _, _, _, _, _, _, _, _, _ => trivial
  | .fail, _, _, _, _, _, _, _, _, _, _ => trivial
  | .read k, S, sp, cs, hs, nO, c, s, Q, hw, hsm => by
    simp only [runFromWithHash]
    have h1 := hw.1
    refine (isTotalQueryBound_bind (qb_absorb _ _ _) fun sp' ↦ isTotalQueryBound_bind
      (qb_runFrom fuel _ _ sp' cs hs nO (c - 1) s Q (hw.2 _) (hsm.2 _)) fun _ ↦
        isTotalQueryBound_pure' _ 0).mono ?_
    rw [Nat.add_zero]
    exact step_le (c' := c - 1) (s' := s) (u := 1) (K := proverK commitMaxHeight fuel) (by omega)
      (by rw [one_mul]; exact one_le_proverK commitMaxHeight fuel)
  | .sample k, S, sp, cs, hs, nO, c, s, Q, hw, hsm => by
    simp only [runFromWithHash]
    have h1 := hsm.1
    refine (isTotalQueryBound_bind (qb_squeeze _) fun r ↦
      qb_runFrom fuel _ _ r.2 cs hs nO c (s - 1) Q (hw _) (hsm.2 _)).mono ?_
    exact step_le (c' := c) (s' := s - 1) (u := 1) (K := proverK commitMaxHeight fuel) (by omega)
      (by rw [one_mul]; exact one_le_proverK commitMaxHeight fuel)
  | .readPacked m k, S, sp, cs, hs, nO, c, s, Q, hw, hsm => by
    simp only [runFromWithHash]
    have h1 := hw.1
    have h2 := hsm.1
    refine (isTotalQueryBound_bind (qb_observePacked _ _) fun sp' ↦ isTotalQueryBound_bind
      (qb_runFrom fuel _ _ sp' cs hs nO (c - m) (s - 1) Q (hw.2 _) (hsm.2 _)) fun _ ↦
        isTotalQueryBound_pure' _ 0).mono ?_
    rw [Nat.add_zero, length_packedOf]
    exact step_le (c' := c - m) (s' := s - 1) (u := m + 1) (by omega)
      (Nat.le_mul_of_pos_right _ (by unfold proverK; positivity))
  | .samplePacked m k, S, sp, cs, hs, nO, c, s, Q, hw, hsm => by
    simp only [runFromWithHash]
    have h1 := hsm.1
    refine (isTotalQueryBound_bind (qb_samplesPacked _ _) fun r ↦
      qb_runFrom fuel _ _ r.2 cs hs nO c (s - m) Q (hw _) (hsm.2 _)).mono ?_
    exact step_le (c' := c) (s' := s - m) (u := m) (by omega)
      (Nat.le_mul_of_pos_right _ (by unfold proverK; positivity))
  | .grind bits k, S, sp, cs, hs, nO, c, s, Q, hw, hsm => by
    simp only [runFromWithHash]
    have h1 := hw.1
    have h2 := hsm.1
    refine (isTotalQueryBound_bind (qb_findNonce _ _ _ _) fun o ↦ ?_).mono
      (show 2 * fuel + (2 + ((c - 1 + (s - 1)) * proverK commitMaxHeight fuel + 0)) ≤ _ from ?_)
    · split
      · exact (isTotalQueryBound_pure' _ 0).mono (Nat.zero_le _)
      · exact isTotalQueryBound_bind (qb_absorbNonce _ _) fun r ↦ isTotalQueryBound_bind
          (qb_runFrom fuel _ _ r.2 cs hs nO (c - 1) (s - 1) Q hw.2 hsm.2) fun _ ↦
            isTotalQueryBound_pure' _ 0
    · rw [Nat.add_zero, ← Nat.add_assoc]
      exact step_le (c' := c - 1) (s' := s - 1) (u := 2) (K := proverK commitMaxHeight fuel) (by omega)
        (le_trans (fuel_le_proverK commitMaxHeight fuel) (by omega))
  | .commit ht w k, S, sp, cs, hs, nO, c, s, Q, hw, hsm => by
    simp only [runFromWithHash]
    have h1 := hw.1
    have h2 := hsm.2.2.1
    have hpow : 2 ^ (ht + 1) ≤ 2 ^ (commitMaxHeight + 1) := Nat.pow_le_pow_right (by norm_num) (by
      have := hsm.1; omega)
    refine (isTotalQueryBound_bind (qb_buildTree ht _) fun tree ↦ isTotalQueryBound_bind
      (qb_absorb _ _ _) fun sp0 ↦ isTotalQueryBound_bind (qb_absorb _ _ _) fun sp1 ↦
        isTotalQueryBound_bind (qb_runFrom fuel k _ sp1 _ (hs ++ [ht]) nO (c - 2) (s - 1) Q hw.2
          hsm.2.2.2) fun _ ↦ isTotalQueryBound_pure' _ 0).mono
      (show 2 ^ (ht + 1) + (1 + (1 + ((c - 2 + (s - 1)) * proverK commitMaxHeight fuel + 0))) ≤ _ from ?_)
    have := step_le (c := c) (s := s) (c' := c - 2) (s' := s - 1) (u := 3)
      (e := 2 ^ (ht + 1) + 2) (K := proverK commitMaxHeight fuel) (by omega)
      (le_trans (le_trans (by omega) (pow_le_proverK commitMaxHeight fuel)) (by omega))
    omega
  | .query i ps k, S, sp, cs, hs, nO, c, s, Q, hw, hsm => by
    simp only [runFromWithHash]
    split
    · exact (isTotalQueryBound_pure' _ 0).mono (Nat.zero_le _)
    · exact (isTotalQueryBound_bind (qb_runFrom fuel _ _ sp cs hs (nO - 1) c s Q (hw.2.2 _)
        (hsm.2 _)) fun _ ↦ isTotalQueryBound_pure' _ 0).mono (by rw [Nat.add_zero])

/-- **The honest prover's queries**, from a seed: the seed's, then the run's. -/
theorem qb_honestComp {P : VerifierProgram Bool} {nO c s : ℕ}
    {Q : Bool → List ℕ → ℕ → Prop} (hw : Wired P [] nO c Q) (hsm : SampLE P s) (σ : Seed)
    (S : Script β) (fuel : ℕ) :
    IsTotalQueryBound (honestComp σ P S fuel) (σ.hs.length + 1 + (c + s) * proverK commitMaxHeight fuel) := by
  unfold honestComp
  refine isTotalQueryBound_bind (isTotalQueryBound_seedRun σ) fun seed ↦ ?_
  rw [← Nat.add_zero ((c + s) * proverK commitMaxHeight fuel)]
  refine isTotalQueryBound_bind ?_ fun _ ↦ isTotalQueryBound_pure' _ 0
  unfold runScriptWithHash
  rw [← Nat.add_zero ((c + s) * proverK commitMaxHeight fuel)]
  exact isTotalQueryBound_bind (qb_runFrom fuel P _ _ [] [] nO c s Q hw hsm) fun _ ↦
    isTotalQueryBound_pure' _ 0

end LeanVM.Prover.Complete.Cost

end
