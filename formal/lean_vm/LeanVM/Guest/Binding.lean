/-
  LeanVM.Guest.Binding

  The statement's digest binds the seed and the statement, unless one of three named pairs of
  byte strings is a Keccak-256 collision.
-/

module

public import Statement.LeanVmGuest
public import LeanXmss.Scheme
public import Statement.LeanSphincs
public import Statement.Fast.Schemes
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords
public import LeanVM.Facts.Verifier
public import LeanVM.Protocol.KeccakHash
public import LeanVM.Facts.ClaimBytes

/-!
# The statement's digest binds

`statementDigest seed s` hashes the seed, the two claim lists' digests, the DA digest and the
deferred claim's cells, an odd count paired with a zero cell (`statement_digest`,
`crates/rec_aggregation/src/aggregation.rs:316-345` at leanVM `542b035`). Every encoding on the
way is injective at a fixed width (`digestBytes`, 32 bytes; `claimBytesOf`, 64; `eBytes`, 16). So
two statements with the same digest are equal, or one of the three Keccak-256
hashes on the way was given two different inputs with the same output: the pairs
`collisionCandidates` lists (`statementDigest_binds`, and `digest_binds : StatementDigestBinds`).

The deferred claim's cells carry no lengths: `[x] ++ [y]` and `[x, y] ++ []` are the same cells.
The binding needs the two deferred claims' points to have the same length, which
`DeferredClaim.HasBytecodeShape` gives at one bytecode (`statementDigest_binds_of_length` takes the length
itself). Nothing else is assumed of the statements.

A consumer compares the public input's digest with that of its own statement under the deployed
seed, while the guest's execution decodes a seed and a statement of that digest
(`decoded_binds`; the decoded statement's shape is `NodeRelation.hasBytecodeShape`'s).
-/

namespace LeanVM.Guest.Binding

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Node

@[expose] public section

/-! ## The bytes each digest hashes (`Statement/LeanVmGuest.lean`) -/


/-! ## Fixed-width encodings are injective -/

/-- A concatenation of encodings of one positive width is injective. -/
theorem flatMap_inj {α β : Type} {f : α → List β} {n : ℕ} (hn : 0 < n)
    (hlen : ∀ a, (f a).length = n) (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l l' : List α}, l.flatMap f = l'.flatMap f → l = l'
  | [], [], _ => rfl
  | [], b :: l', h => by
    have := congrArg List.length h
    rw [List.flatMap_nil, List.flatMap_cons, List.length_append, hlen] at this
    simp at this
    omega
  | a :: l, [], h => by
    have := congrArg List.length h
    rw [List.flatMap_nil, List.flatMap_cons, List.length_append, hlen] at this
    simp at this
    omega
  | a :: l, b :: l', h => by
    rw [List.flatMap_cons, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hlen, hlen])
    rw [hf a b h1, flatMap_inj hn hlen hf h2]

theorem kBytes_inj {a b : K} (h : K.toBytes a = K.toBytes b) : a = b :=
  K.lane_injective (wordBytes_injective h)

theorem length_eBytes (x : E) : (E.toBytes x).length = 16 := rfl

theorem eBytes_inj {x y : E} (h : E.toBytes x = E.toBytes y) : x = y := by
  obtain ⟨h1, h2⟩ := List.append_inj h rfl
  apply CompPoly.Extension.Ext.ext
  rintro ⟨i, hi⟩
  match i, hi with
  | 0, _ => exact kBytes_inj h1
  | 1, _ => exact kBytes_inj h2
  | n + 2, hi => exact absurd hi (show ¬ (n + 2 < 2) by omega)

theorem length_bytesLE (n : ℕ) (v : BitVec (8 * n)) : (HashSig.littleEndianBytes n v).length = n :=
  List.length_ofFn

theorem bytesLE_inj {n : ℕ} {v v' : BitVec (8 * n)}
    (h : HashSig.littleEndianBytes n v = HashSig.littleEndianBytes n v') : v = v' := by
  have hf := List.ofFn_injective h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have e := congrArg (fun f ↦ (f ⟨j / 8, by omega⟩ : UInt8).toBitVec.getLsbD (j % 8)) hf
  have hj' : 8 * (j / 8) + j % 8 = j := by omega
  simpa [BitVec.getLsbD_extractLsb', hj', Nat.mod_lt] using e

theorem claimBytes_inj {r p r' p' : BitVec 128} {m m' : BitVec 256}
    (h : claimBytesOf r p m = claimBytesOf r' p' m') : r = r' ∧ p = p' ∧ m = m' := by
  obtain ⟨h12, h3⟩ := List.append_inj h (by simp [length_bytesLE])
  obtain ⟨h1, h2⟩ := List.append_inj h12 (by simp [length_bytesLE])
  exact ⟨bytesLE_inj (n := 16) h1, bytesLE_inj (n := 16) h2, bytesLE_inj (n := 32) h3⟩

theorem length_claimBytes (r p : BitVec 128) (m : BitVec 256) :
    (claimBytesOf r p m).length = 64 := by
  simp [claimBytesOf, length_bytesLE]

theorem xmssPreimage_inj {l l' : List LeanXmssClaim}
    (h : claimListPreimage xmssPublicKeyBytes l = claimListPreimage xmssPublicKeyBytes l') :
    l = l' := by
  rw [claimListPreimage_xmss, claimListPreimage_xmss] at h
  exact flatMap_inj (n := 64) (by decide) (fun _ ↦ length_claimBytes _ _ _)
    (fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h ↦ by
      obtain ⟨rfl, rfl, rfl⟩ := claimBytes_inj h
      rfl) h

theorem sphincsPreimage_inj {l l' : List LeanSphincsClaim}
    (h : claimListPreimage Sphincs.PublicKey.toBytes l =
      claimListPreimage Sphincs.PublicKey.toBytes l') : l = l' := by
  rw [claimListPreimage_sphincs, claimListPreimage_sphincs] at h
  exact flatMap_inj (n := 64) (by decide) (fun _ ↦ length_claimBytes _ _ _)
    (fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h ↦ by
      obtain ⟨rfl, rfl, rfl⟩ := claimBytes_inj h
      rfl) h

/-- Two deferred claims with the same cells and points of the same length are equal. -/
theorem cells_inj {c c' : DeferredClaim}
    (hb : c.bytecodePoint.length = c'.bytecodePoint.length) (h : c.cells = c'.cells) : c = c' := by
  obtain ⟨b, v⟩ := c
  obtain ⟨b', v'⟩ := c'
  simp only [DeferredClaim.cells] at h hb
  obtain ⟨h1, h2⟩ := List.append_inj h hb
  simp only [List.cons.injEq, and_true] at h2
  subst h1 h2
  rfl

/-- The outer preimage determines the seed, the two claim lists' digests, the DA digest and, at a
fixed point length, the deferred claim. -/
theorem statementPreimage_inj {seed seed' : Digest} {s s' : NodeStatement}
    (hb : s.deferredClaim.bytecodePoint.length = s'.deferredClaim.bytecodePoint.length)
    (h : statementPreimage seed s = statementPreimage seed' s') :
    seed = seed' ∧
      claimListDigest xmssPublicKeyBytes s.claims.xmss =
        claimListDigest xmssPublicKeyBytes s'.claims.xmss ∧
      claimListDigest Sphincs.PublicKey.toBytes s.claims.sphincs =
        claimListDigest Sphincs.PublicKey.toBytes s'.claims.sphincs ∧
      s.claims.daDigest = s'.claims.daDigest ∧ s.deferredClaim = s'.deferredClaim := by
  have hc : s.deferredClaim.cells.length = s'.deferredClaim.cells.length := by
    simp [DeferredClaim.cells, hb]
  unfold statementPreimage at h
  obtain ⟨h1234, h5⟩ := List.append_inj h (by simp [digestBytes_length])
  obtain ⟨h123, h4⟩ := List.append_inj h1234 (by simp [digestBytes_length])
  obtain ⟨h12, h3⟩ := List.append_inj h123 (by simp [digestBytes_length])
  obtain ⟨h1, h2⟩ := List.append_inj h12 (by simp [digestBytes_length])
  have hp := flatMap_inj (n := 16) (by decide) length_eBytes (fun _ _ ↦ eBytes_inj) h5
  unfold paddedDeferredClaimCells at hp
  obtain ⟨hcells, -⟩ := List.append_inj hp hc
  exact ⟨digestBytes_injective h1, digestBytes_injective h2, digestBytes_injective h3,
    digestBytes_injective h4, cells_inj hb hcells⟩

/-! ## The binding -/

/-- **The statement's digest binds**, at point lengths equal on both sides: the seeds and the
statements are equal, or a candidate pair is a Keccak-256 collision. -/
theorem statementDigest_binds_of_length {seed seed' : Digest} {s s' : NodeStatement}
    (hb : s.deferredClaim.bytecodePoint.length = s'.deferredClaim.bytecodePoint.length)
    (h : statementDigest seed s = statementDigest seed' s') :
    (seed = seed' ∧ s = s') ∨ HasCollision (collisionCandidates seed s seed' s') := by
  by_cases h0 : statementPreimage seed s = statementPreimage seed' s'
  swap
  · exact Or.inr ⟨(statementPreimage seed s, statementPreimage seed' s'),
      by simp [collisionCandidates], h0, h⟩
  obtain ⟨hseed, hx, hp, hda, hdef⟩ := statementPreimage_inj hb h0
  by_cases h2 : claimListPreimage xmssPublicKeyBytes s.claims.xmss =
      claimListPreimage xmssPublicKeyBytes s'.claims.xmss
  swap
  · exact Or.inr ⟨(claimListPreimage xmssPublicKeyBytes s.claims.xmss,
      claimListPreimage xmssPublicKeyBytes s'.claims.xmss), by simp [collisionCandidates], h2, hx⟩
  by_cases h3 : claimListPreimage Sphincs.PublicKey.toBytes s.claims.sphincs =
      claimListPreimage Sphincs.PublicKey.toBytes s'.claims.sphincs
  swap
  · exact Or.inr ⟨(claimListPreimage Sphincs.PublicKey.toBytes s.claims.sphincs,
      claimListPreimage Sphincs.PublicKey.toBytes s'.claims.sphincs),
      by simp [collisionCandidates], h3, hp⟩
  left
  refine ⟨hseed, ?_⟩
  have e1 := xmssPreimage_inj h2
  have e2 := sphincsPreimage_inj h3
  obtain ⟨⟨x, p, d⟩, c⟩ := s
  obtain ⟨⟨x', p', d'⟩, c'⟩ := s'
  dsimp only at e1 e2 hda hdef
  subst e1 e2 hda hdef
  rfl

/-- **The statement's digest binds the seed and the statement**, for two statements whose
deferred claims have the shape of one bytecode: the seeds and the statements are equal, or one
of the candidate pairs is a Keccak-256 collision. The shape fixes the length of the deferred
claim's point, which its cells do not record. -/
theorem statementDigest_binds {b : List K} {seed seed' : Digest} {s s' : NodeStatement}
    (hs : s.deferredClaim.HasBytecodeShape b) (hs' : s'.deferredClaim.HasBytecodeShape b)
    (h : statementDigest seed s = statementDigest seed' s') :
    (seed = seed' ∧ s = s') ∨ HasCollision (collisionCandidates seed s seed' s') :=
  statementDigest_binds_of_length (hs.trans hs'.symm) h

/-- **`StatementDigestBinds`** (`Statement/LeanVmGuest.lean`): `statementDigest_binds`. -/
theorem digest_binds : StatementDigestBinds :=
  fun _ _ _ _ _ hs hs' h ↦ statementDigest_binds hs hs' h

/-! ## What a consumer learns -/

/-- **A consumer learns the decoded statement**: it checks that the public input's digest is its
statement `s₀`'s under the deployed seed `iv`; an execution decodes a seed and a statement `s` of
the same digest. Then the decoded seed is `iv` and `s` is `s₀`, or a candidate pair is a
Keccak-256 collision. -/
theorem decoded_binds {b : List K} {iv seed : Digest} {s₀ s : NodeStatement}
    {input : PublicInput} (hs₀ : s₀.deferredClaim.HasBytecodeShape b) (hs : s.deferredClaim.HasBytecodeShape b)
    (hpub : publicInputDigest input = statementDigest iv s₀)
    (hdec : statementDigest seed s = publicInputDigest input) :
    (seed = iv ∧ s = s₀) ∨ HasCollision (collisionCandidates seed s iv s₀) :=
  statementDigest_binds hs hs₀ (hdec.trans hpub)

end
end LeanVM.Guest.Binding
