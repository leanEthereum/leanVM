module

public import LeanDa.WithHash
public import Common.Lanes

/-!
# The statement's LeanDA is the hash-parameter form, the hash over the permutation

The statement's LeanDA hashes with Keccak-256 over the permutation it is given (`keccak256With`)
to leanVM's digests; Benedikt Wagner's framework and its proofs take the hash as a parameter of its
own (`LeanDa.WithHash`), answering `32` bytes. Each statement definition, its digests read as
bytes (`Digest.toBytes`, injective), is the hash-parameter one with the hash Keccak-256 over the
permutation (`hashOver π`, `keccakDigestBytes P`), by unfolding, and by induction for the
recursive ones (`merkleRootWith_id`, `walkM_eq_withHash`, `merkleRootM_eq_withHash`); the
statement's membership challenge, drawn with the leanVM verifier's sponge, is the proofs' duplex's
(`membershipChallengeM_eq_withHash`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal Common

namespace LeanDa

open LeanVM.Semantics (KeccakState)

/-! ## Digests and their bytes

The statement's digests are four words (`Digest`), the framework's `32` bytes: `Digest.toBytes`,
injective (`digestOfBytes_toBytes`), carries every statement definition to the framework's. -/

open LeanVM.Protocol (Digest)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)
open LeanVM.Protocol.Compile (climb)

theorem toBytes_toList (d : Digest) : d.toBytes.toList = digestBytes d := by
  simp [LeanVM.Protocol.Digest.toBytes, Vector.toList]

theorem pairBytes_toBytes (a b : Digest) :
    pairBytes a.toBytes b.toBytes = digestBytes a ++ digestBytes b := by
  simp [pairBytes, toBytes_toList]

theorem digestOfBytes_toBytes (d : Digest) : digestOfBytes d.toBytes = d := by
  apply Vector.ext
  intro i hi
  have hd : d.toBytes.toList = LeanVM.Rpm.lanesBytes d.toList := by
    simp [LeanVM.Protocol.Digest.toBytes, digestBytes, LeanVM.Rpm.lanesBytes, Vector.toList]
  simp only [digestOfBytes, Vector.getElem_ofFn]
  rw [hd, LeanVM.Rpm.leLane_lanesBytes _ _ (by simpa using hi), Vector.getElem_toList]

theorem toBytes_injective : Function.Injective LeanVM.Protocol.Digest.toBytes := fun a b h ↦ by
  rw [← digestOfBytes_toBytes a, h, digestOfBytes_toBytes]

/-! ## The commitment over a pure permutation -/

section Pure

variable (π : KeccakState → KeccakState)

/-- `π` as a permutation in `Id`. -/
abbrev pureIn (x : KeccakState) : Id KeccakState := pure (π x)

theorem hashOver_eq (bytes : List UInt8) :
    hashOver π bytes = (Id.run (keccak256With (pureIn π) bytes)).toBytes := rfl

theorem merkleRootWith_id : ∀ (d : ℕ) (f : ℕ → Digest),
    (Id.run (merkleRootWith (pureIn π) d fun i ↦ pure (f i))).toBytes =
      merkleRootWithHash (hashOver π) d fun i ↦ (f i).toBytes
  | 0, _ => rfl
  | d + 1, f => by
    have h := merkleRootWith_id d fun i ↦
      Id.run (keccak256With (pureIn π) (digestBytes (f (2 * i)) ++ digestBytes (f (2 * i + 1))))
    refine h.trans ?_
    simp only [merkleRootWithHash]
    congr 1

theorem merklePathWith_id : ∀ (d : ℕ) (f : ℕ → Digest) (index : ℕ),
    (Id.run (merklePathWith (pureIn π) d (fun i ↦ pure (f i)) index)).map Digest.toBytes =
      merklePathWithHash (hashOver π) d (fun i ↦ (f i).toBytes) index
  | 0, _, _ => rfl
  | d + 1, f, index => by
    have h := merklePathWith_id d (fun i ↦
      Id.run (keccak256With (pureIn π) (digestBytes (f (2 * i)) ++ digestBytes (f (2 * i + 1)))))
      (index / 2)
    show (f (sibling index)).toBytes :: (Id.run (merklePathWith (pureIn π) d (fun i ↦
      pure (Id.run (keccak256With (pureIn π) (digestBytes (f (2 * i)) ++
        digestBytes (f (2 * i + 1)))))) (index / 2))).map Digest.toBytes = _
    rw [h]
    simp only [merklePathWithHash, List.cons.injEq, true_and]
    congr 1

theorem blobRoot_id {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) :
    (Id.run (blobRootWith (pureIn π) c i)).toBytes = blobRootWithHash (hashOver π) c i :=
  merkleRootWith_id π 7 _

theorem commitCells_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) :
    (commitCells π c).toBytes = commitCellsWithHash (hashOver π) c := by
  have h := merkleRootWith_id π logMaxRows fun i ↦ Id.run (blobRootWith (pureIn π) c i)
  rw [funext (blobRoot_id π c)] at h
  simp only [commitCellsWithHash, ← h, countBytes, pairBytes_toBytes, hashOver_eq]
  rfl

theorem openCell_eq_withHash {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) :
    (openCell π c p).toBytes = openCellWithHash (hashOver π) c p := by
  have h1 := merklePathWith_id π 7 (fun j ↦
    Id.run (keccak256With (pureIn π) (cellBytes (paddedCell c (positionRow p) j)))) (positionCell p)
  have h2 := merklePathWith_id π logMaxRows (fun i ↦ Id.run (blobRootWith (pureIn π) c i))
    (positionRow p)
  rw [funext (blobRoot_id π c)] at h2
  show (⟨(Id.run (merklePathWith (pureIn π) 7 (fun j ↦ pure (Id.run (keccak256With (pureIn π)
      (cellBytes (paddedCell c (positionRow p) j))))) (positionCell p)) ++
    Id.run (merklePathWith (pureIn π) logMaxRows (fun i ↦ pure (Id.run (blobRootWith (pureIn π) c i)))
      (positionRow p))).map Digest.toBytes⟩ : ByteOpening) = _
  rw [List.map_append, h1, h2]
  rfl

end Pure

/-! ## The challenge's sponge

The statement's sponge (`Verifier/Transcript.lean`, tags in `ℕ`) runs as the proofs' (`Sponge`, tags in `K`):
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
theorem membershipChallengeM_eq_withHash [LawfulMonad m] (root : Digest) :
    membershipChallengeWith P root =
      membershipChallengeMWithHash (keccakDigestBytes P) P root.toBytes := by
  simp only [membershipChallengeWith, membershipChallengeMWithHash, keccakDigestBytes,
    Sponge.newWith, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  refine bind_congr fun iv ↦ ?_
  rw [freshSpongeInput_toBytes, digestOfBytes_toBytes]
  refine bind_congr fun state ↦ ?_
  exact grindWith_eq P state _ _

theorem walkM_eq_withHash [LawfulMonad m] : ∀ (idx : ℕ) (node : Digest) (path : List Digest),
    Digest.toBytes <$> climb P node idx path =
      walkMWithHash (keccakDigestBytes P) idx node.toBytes (path.map Digest.toBytes)
  | _, _, [] => by simp [climb, walkMWithHash]
  | idx, node, s :: rest => by
    have ih := fun parent ↦ walkM_eq_withHash (idx / 2) parent rest
    by_cases h : idx % 2 = 0 <;>
      simp [climb, walkMWithHash, h, keccakDigestBytes, pairBytes_toBytes, ih]

theorem verifyCellM_eq_withHash [LawfulMonad m] (r : ℕ) (com : Digest) (p : Fin (r * 128))
    (x : Cell) (τ : CellOpening) :
    verifyCellWith P r com p x τ =
      verifyCellMWithHash (keccakDigestBytes P) r com.toBytes p x τ.toBytes := by
  have hpath : τ.toBytes.path ++ [countBytes r] = (τ.path ++ [countDigest r]).map Digest.toBytes := by
    simp [CellOpening.toBytes, countBytes]
  simp only [verifyCellWith, verifyCellMWithHash, keccakDigestBytes, bind_map_left, hpath,
    ← walkM_eq_withHash]
  refine bind_congr fun d ↦ ?_
  simp [CellOpening.toBytes, toBytes_injective.eq_iff]

theorem merkleRootM_eq_withHash [LawfulMonad m] : ∀ (d : ℕ) (f : ℕ → m Digest),
    Digest.toBytes <$> merkleRootWith P d f =
      merkleRootMWithHash (keccakDigestBytes P) d fun i ↦ Digest.toBytes <$> f i
  | 0, _ => rfl
  | d + 1, f => by
    rw [merkleRootWith, merkleRootMWithHash, merkleRootM_eq_withHash d]
    congr 1
    funext i
    simp [merkleLevelUpWith, upMWithHash, keccakDigestBytes, pairBytes_toBytes]

theorem blobRootM_eq_withHash [LawfulMonad m] {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) :
    Digest.toBytes <$> blobRootWith P c i = blobRootMWithHash (keccakDigestBytes P) c i := by
  rw [blobRootWith, blobRootMWithHash, merkleRootM_eq_withHash]
  rfl

theorem commitCellsM_eq_withHash [LawfulMonad m] {r : ℕ} (c : Fin (r * 128) → Cell) :
    Digest.toBytes <$> commitCellsWith P c = commitCellsMWithHash (keccakDigestBytes P) c := by
  rw [commitCellsMWithHash, ← funext (blobRootM_eq_withHash P c), ← merkleRootM_eq_withHash,
    commitCellsWith, map_bind, bind_map_left]
  simp [keccakDigestBytes, countBytes, pairBytes_toBytes]

theorem relationM_eq_withHash [LawfulMonad m] {r : ℕ} (root : Digest) (c : Fin (r * 128) → Cell) :
    relationWith P root c = relationMWithHash (keccakDigestBytes P) P root.toBytes c := by
  simp only [relationWith, relationMWithHash, membershipChallengeM_eq_withHash,
    ← commitCellsM_eq_withHash, bind_map_left, toBytes_injective.eq_iff]

end Monadic

/-! ## The model's hash -/

/-- Keccak-256 over the model's `π` is `keccak256OverPermutation`. -/
theorem keccakDigestBytes_queryPermutation :
    keccakDigestBytes queryPermutation = keccak256OverPermutation := rfl

end LeanDa

end
