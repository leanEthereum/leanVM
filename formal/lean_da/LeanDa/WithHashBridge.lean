module

public import LeanDa.WithHash
public import Common.Lanes

/-!
# The statement's LeanDA is the hash-parameter form, the hash over the permutation

The statement's LeanDA hashes with Keccak-256 over the permutation it is given
(`keccakDigestBytes`); Benedikt Wagner's framework and its proofs take the hash as a parameter of
its own (`LeanDa.WithHash`). Each statement definition is the hash-parameter one with the hash
Keccak-256 over the permutation (`hashOver π`, `keccakDigestBytes P`), by unfolding, and by
induction for the recursive ones (`merkleRootWith_id`, `walkM_eq_withHash`,
`merkleRootM_eq_withHash`); the statement's membership challenge, drawn with the leanVM verifier's
sponge, is the proofs' duplex's (`membershipChallengeM_eq_withHash`). So the statement's games
are the hash-parameter ones (`positionBindingGame_eq_withHash`, …), and its end statements follow from those
(`positionBindingRpm_of_withHash`, …).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal Common

namespace LeanDa

open LeanVM.Semantics (KeccakState)

/-! ## The commitment over a pure permutation -/

section Pure

variable (π : KeccakState → KeccakState)

/-- `π` as a permutation in `Id`. -/
abbrev pureIn (x : KeccakState) : Id KeccakState := pure (π x)

theorem merkleRootWith_id : ∀ (d : ℕ) (f : ℕ → DigestBytes),
    Id.run (merkleRootWith (pureIn π) d fun i ↦ pure (f i)) = merkleRootWithHash (hashOver π) d f
  | 0, _ => rfl
  | d + 1, f => merkleRootWith_id d (upWithHash (hashOver π) f)

theorem merklePathWith_id : ∀ (d : ℕ) (f : ℕ → DigestBytes) (index : ℕ),
    Id.run (merklePathWith (pureIn π) d (fun i ↦ pure (f i)) index) =
      merklePathWithHash (hashOver π) d f index
  | 0, _, _ => rfl
  | d + 1, f, index => by
    show f (sibling index) ::
        Id.run (merklePathWith (pureIn π) d (fun i ↦ pure (upWithHash (hashOver π) f i))
          (index / 2)) = _
    rw [merklePathWith_id d]
    rfl

theorem blobRoot_id {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) :
    Id.run (blobRootWith (pureIn π) c i) = blobRootWithHash (hashOver π) c i :=
  merkleRootWith_id π 7 _

theorem blobRootWith_pureIn {r : ℕ} (c : Fin (r * 128) → Cell) :
    blobRootWith (pureIn π) c = fun i ↦ pure (blobRootWithHash (hashOver π) c i) :=
  funext fun i ↦ blobRoot_id π c i

theorem commitCells_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) :
    commitCells π c = commitCellsWithHash (hashOver π) c := by
  show Id.run (merkleRootWith (pureIn π) logMaxRows (blobRootWith (pureIn π) c)) = _
  rw [blobRootWith_pureIn, merkleRootWith_id]
  rfl

theorem openCell_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) :
    openCell π c p = openCellWithHash (hashOver π) c p := by
  show (⟨Id.run (merklePathWith (pureIn π) 7
      (fun j ↦ pure (cellLeavesWithHash (hashOver π) c (positionRow p) j)) (positionCell p)) ++
    Id.run (merklePathWith (pureIn π) logMaxRows (blobRootWith (pureIn π) c)
      (positionRow p))⟩ : CellOpening) = _
  rw [blobRootWith_pureIn, merklePathWith_id, merklePathWith_id]
  rfl

theorem commitCodewords_eq_withHash (rows : List (List E)) :
    commitCodewords π rows = commitCodewordsWithHash (hashOver π) rows := rfl

end Pure

/-! ## The challenge's sponge

The statement's sponge (`Field.lean`, tags in `ℕ`) runs as the proofs' (`Sponge`, tags in `K`):
`toCompile` maps the one to the other, and every step commutes with it. -/

open LeanVM.Protocol.Compile (pendingLanes challengeOf seedInput)

/-- The statement's sponge of a proofs' sponge: the tags as the numbers of their lanes, no ground
challenge. -/
def Sponge.toCompile (s : Sponge) : LeanVM.Protocol.Compile.Sponge :=
  ⟨s.state, s.pending.map fun x ↦ (x.1, x.2.lane.toNat), none⟩

theorem pendingLanes_toCompile (pending : List (E × K)) :
    pendingLanes (pending.map fun x ↦ (x.1, x.2.lane.toNat)) = (rateWords pending).map K.lane := by
  induction pending with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, pendingLanes, List.flatMap_cons, rateWords, List.map_append] at ih ⊢
    rw [ih]
    simp only [List.map_nil, limb, UInt64.ofNat_toNat, Nat.toUInt64_eq]
    rfl

theorem duplexInput_toCompile (s : Sponge) :
    LeanVM.Protocol.Compile.duplexInput s.toCompile = duplexInput s := by
  apply Vector.ext
  intro i hi
  simp only [LeanVM.Protocol.Compile.duplexInput, duplexInput, Vector.getElem_ofFn]
  by_cases h : i < 16
  · simp only [h, ↓reduceIte, show i < rateLanes from h, Sponge.toCompile, pendingLanes_toCompile]
    rw [show (0 : UInt64) = K.lane 0 from rfl, List.getD_map]
  · simp only [h, ↓reduceIte, show ¬ i < rateLanes from h, Sponge.toCompile]
    simp [LeanVM.Semantics.Keccak.lane, hi]

theorem challengeOf_eq (state : KeccakState) : challengeOf state = chalOfState state := by
  simp [challengeOf, chalOfState, LeanVM.Semantics.Keccak.lane]
  rfl

/-- The state a nonce is permuted from, in the statement's sponge. -/
theorem duplexInput_nonce (y : KeccakState) (nonce : ℕ) :
    LeanVM.Protocol.Compile.duplexInput
        ⟨y, [(LeanVM.Protocol.Verifier.eOfNat nonce, LeanVM.Protocol.Compile.dsPowNonce)], none⟩ =
      nonceInput y nonce := by
  rw [nonceInput, ← duplexInput_toCompile]
  rfl

section Monadic

variable {m : Type → Type} [Monad m] (P : KeccakState → m KeccakState)

/-- **The statement's nonce search is the proofs'.** -/
theorem grindWith_eq [LawfulMonad m] (y : KeccakState) : ∀ (fuel nonce : ℕ),
    grindWith P ⟨y, [], none⟩ nonce fuel = grindMWithHash P y nonce fuel
  | 0, _ => rfl
  | fuel + 1, nonce => by
    simp only [grindWith, grindMWithHash, LeanVM.Protocol.Compile.absorbNonce,
      LeanVM.Protocol.Compile.absorb, LeanVM.Protocol.Compile.duplex,
      LeanVM.Protocol.Compile.squeeze, LeanVM.Protocol.Compile.rateScalars, List.length_nil,
      show (0 = 4) = False from by decide, ite_false, pure_bind, bind_assoc, List.nil_append,
      duplexInput_nonce]
    refine bind_congr fun o ↦ ?_
    have h2 : LeanVM.Semantics.Keccak.lane o 2 = o[2] := by
      simp [LeanVM.Semantics.Keccak.lane]
    simp only [h2, challengeOf_eq, grindWith_eq y fuel (nonce + 1)]

/-- The IV's words are the words of its bytes, the root's those of `digestOfBytes`. -/
theorem freshSpongeInput_toBytes (iv : LeanVM.Protocol.Digest) (root : DigestBytes) :
    freshSpongeInput iv.toBytes root = seedInput iv (digestOfBytes root) := by
  apply Vector.ext
  intro i hi
  have hiv : iv.toBytes.toList = LeanVM.Rpm.lanesBytes iv.toList := by
    simp [LeanVM.Protocol.Digest.toBytes, LeanVM.Protocol.KeccakHash.digestBytes,
      LeanVM.Rpm.lanesBytes, Vector.toList]
  simp only [freshSpongeInput, seedInput, Vector.getElem_ofFn, digestWord, digestOfBytes]
  split_ifs with h1 h2 <;> try rfl
  rw [hiv, LeanVM.Rpm.leLane_lanesBytes _ _ (by simpa using h1), Vector.getElem_toList]
  rfl

/-- **The statement's challenge is the proofs' duplex's.** -/
theorem membershipChallengeM_eq_withHash [LawfulMonad m] (root : DigestBytes) :
    membershipChallengeWith P root =
      membershipChallengeMWithHash (keccakDigestBytes P) P root := by
  simp only [membershipChallengeWith, membershipChallengeMWithHash, keccakDigestBytes,
    Sponge.newWith, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  refine bind_congr fun iv ↦ ?_
  rw [freshSpongeInput_toBytes]
  refine bind_congr fun state ↦ ?_
  exact grindWith_eq P state _ _

theorem walkM_eq_withHash : ∀ (idx : ℕ) (node : DigestBytes) (path : List DigestBytes),
    climbWith P idx node path = walkMWithHash (keccakDigestBytes P) idx node path
  | _, _, [] => rfl
  | idx, node, s :: rest => by
    simp only [climbWith, walkMWithHash, walkM_eq_withHash]

theorem verifyCellM_eq_withHash (r : ℕ) (com : DigestBytes) (p : Fin (r * 128)) (x : Cell)
    (τ : CellOpening) :
    verifyCellWith P r com p x τ = verifyCellMWithHash (keccakDigestBytes P) r com p x τ := by
  simp only [verifyCellWith, verifyCellMWithHash, walkM_eq_withHash]

theorem merkleRootM_eq_withHash : ∀ (d : ℕ) (f : ℕ → m DigestBytes),
    merkleRootWith P d f = merkleRootMWithHash (keccakDigestBytes P) d f
  | 0, _ => rfl
  | d + 1, f => by rw [merkleRootWith, merkleRootMWithHash, merkleRootM_eq_withHash d]; rfl

theorem blobRootM_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) :
    blobRootWith P c i = blobRootMWithHash (keccakDigestBytes P) c i := by
  rw [blobRootWith, blobRootMWithHash, merkleRootM_eq_withHash]
  rfl

theorem commitCellsM_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) :
    commitCellsWith P c = commitCellsMWithHash (keccakDigestBytes P) c := by
  rw [commitCellsWith, commitCellsMWithHash, merkleRootM_eq_withHash,
    funext (blobRootM_eq_withHash P c)]

theorem relationM_eq_withHash [LawfulMonad m] {r : ℕ} (root : DigestBytes) (c : Fin (r * 128) → Cell) :
    relationWith P root c = relationMWithHash (keccakDigestBytes P) P root c := by
  simp only
    [relationWith, relationMWithHash, membershipChallengeM_eq_withHash, commitCellsM_eq_withHash]

end Monadic

/-! ## The games and the end statements -/

/-- Keccak-256 over the model's `π` is `keccak256OverPermutation`. -/
theorem keccakDigestBytes_queryPermutation :
    keccakDigestBytes queryPermutation = keccak256OverPermutation := rfl

theorem relationForPermutation_eq_withHash (r : ℕ) :
    relationForPermutation r = relationForPermutationWithHash r := by
  funext π root c
  simp only [relationForPermutation, relationForPermutationWithHash, relationM_eq_withHash]; rfl

variable (r : ℕ) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof)
  (ext : StraightLineExtractor DigestBytes (Fin (r * 128) → Cell) Crs Proof)

theorem positionBindingGame_eq_withHash (A : PositionBindingAdversary r Crs Proof) :
    positionBindingGame r ps A = positionBindingGameWithHash r ps A := by
  simp only [positionBindingGame, positionBindingGameWithHash, verifyCellM_eq_withHash,
    keccakDigestBytes_queryPermutation]

theorem codeBindingGame_eq_withHash (A : CodeBindingAdversary r Crs Proof) :
    codeBindingGame r ps A = codeBindingGameWithHash r ps A := by
  simp only [codeBindingGame, codeBindingGameWithHash, verifyCellM_eq_withHash,
    keccakDigestBytes_queryPermutation]

theorem knowledgeSoundnessGame_eq_withHash (B : KnowledgeSoundnessAdversary Crs Proof) :
    knowledgeSoundnessGame r ps ext B = knowledgeSoundnessGameWithHash r ps ext B := by
  simp only [knowledgeSoundnessGame, knowledgeSoundnessGameWithHash, relationM_eq_withHash,
    keccakDigestBytes_queryPermutation]

theorem completenessExperiment_eq_withHash (π : Equiv.Perm KeccakState) (msg : Fin r → Payload)
    (p : Fin (r * 128)) :
    completenessExperiment r π ps msg p = completenessExperimentWithHash r π ps msg p := by
  simp only [completenessExperiment, completenessExperimentWithHash, commitCells_eq_withHash,
    openCell_eq_withHash, verifyCellM_eq_withHash]; rfl

/-- **Perfect completeness, from the hash-parameter form.** -/
theorem perfectlyCompleteRpm_of_withHash (h : PerfectlyCompleteRpmWithHash) :
    LeanDaPerfectlyComplete := by
  intro r π Crs Proof ps hr hps msg p
  rw [completenessExperiment_eq_withHash]
  exact h r π ps hr (relationForPermutation_eq_withHash r ▸ hps) msg p

/-- **Position binding, from the hash-parameter form.** -/
theorem positionBindingRpm_of_withHash (h : PositionBindingRpmWithHash) :
    LeanDaPositionBinding := by
  intro r Crs Proof ps A Q hQ
  rw [positionBindingGame_eq_withHash] at hQ ⊢
  exact h r ps A Q hQ

/-- **Code binding, from the hash-parameter form.** -/
theorem codeBindingRpm_of_withHash (h : CodeBindingRpmWithHash) : LeanDaCodeBinding := by
  intro r Crs Proof ps ext c k hks hr hrmax A Q hQ
  rw [codeBindingGame_eq_withHash] at hQ ⊢
  refine h r ps ext c k (fun B q hq hq' ↦ ?_) hr hrmax A Q hQ
  rw [← knowledgeSoundnessGame_eq_withHash] at hq ⊢
  exact hks B q hq hq'

end LeanDa

end
