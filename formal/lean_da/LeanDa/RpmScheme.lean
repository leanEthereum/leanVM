module

public import LeanDa.Merkle
public import Common.Keccak
public import Common.Lemmas
public import LeanDa.Defs
public import LeanDa.WithHash

@[expose] public section

/-!
# LeanDA's hashing and challenges over a permutation oracle

The random-permutation model (`Common`) instantiates LeanDA's hash `H` with Keccak-256, the
sponge over a permutation `π` of the 200-byte Keccak-f[1600] state, and the challenges' duplex
sponge `P` with `π` itself. The definitions of `LeanDa.Scheme` take `H` and `P` as functions; here
they are transcribed for oracles, in any monad (`Sponge.newWith`, `grindMWithHash`,
`membershipChallengeMWithHash`, `walkMWithHash`, `verifyCellMWithHash`), and are the scheme's own
for pure ones (`membershipChallengeM_id`, `verifyCellM_id`).

**Lanes and bytes.** The sponge's state is the statement's `KState`, `25` lanes of `u64`, read
on the permutation's `200` bytes: lane `i` is bytes `8 i … 8 i + 7`, little endian
(`LeanVM.KState.toRpm`), as in Keccak-f[1600] (`Common.keccakF`, `lanesOfBytes`); a lane read as
an element of `K` has the bytes `laneBytes` gives it (`laneBytes_toList`). `lanesToState` and
`stateToLanes` convert, and a duplexing writes the rate lanes `0 … 15` and keeps lanes `16 … 24`, that is bytes
`128 … 199`: the capacity and the last rate byte `135`, whose top bit no padded block has clear
(`Common.keccakNF`). So every permutation call of the challenges' sponge absorbs a non-final
block into the zero state or into an earlier answer (`duplexP_membershipChallengeR`,
`duplexP_membershipChallengeVecR`): the duplex
discipline of the two-oracle transfer (`Common.keccak256_transfer2`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common

namespace LeanDa

/-! ## Lanes and bytes -/

/-- A lane's bytes are the crate's (`kBytes`, `as_bytes`). -/
theorem laneBytes_toList (a : K) : (laneBytes a).toList = LeanVM.Parameters.K.toBytes a := by
  apply List.ext_getElem
  · simp [toBytes_eq_shift]
  intro t h1 h2
  simp only [Vector.getElem_toList, toBytes_eq_shift, List.getElem_map, List.getElem_range]
  apply UInt8.toNat_inj.mp
  simp only [laneBytes, Equiv.trans_apply, arrayVectorEquivFin, Equiv.coe_fn_symm_mk,
    Vector.getElem_ofFn, Equiv.arrowCongr_apply, Function.comp_apply]
  change ((finFunctionFinEquiv (m := 256) (n := 8)).symm _ ⟨t, _⟩ : ℕ) = _
  rw [finFunctionFinEquiv_symm_apply_val]
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

/-- **The kept lanes keep the capacity and byte `135`**: a state whose lanes `16 … 24` are those of
`y` has `y`'s capacity and byte `135`. -/
theorem lanesToState_keep {L : Lanes} {y : KState}
    (h : ∀ i : Fin 25, 16 ≤ (i : ℕ) → L[i] = (stateToLanes y)[i]) :
    (lanesToState L).2 = y.2 ∧ (lanesToState L).1.2[103] = y.1.2[103] := by
  obtain ⟨h1, h2⟩ := LeanVM.Rpm.toRpm_keep L (stateToLanes y) h
  rw [← lanesToState_stateToLanes y]
  exact ⟨h1, h2⟩

/-! ## The challenges and the openings' verification, over oracles -/

section Pure

variable (H : List UInt8 → Common.DigestBytes) (P : Lanes → Lanes)

/-- **Over pure functions, the challenge is the crate's.** -/
theorem membershipChallengeM_id (root : Common.DigestBytes) :
    membershipChallengeMWithHash (m := Id) (fun a ↦ pure (H a)) (fun L ↦ pure (P L)) root =
      membershipChallenge H P root := rfl

theorem walkM_id (idx : ℕ) (node : Common.DigestBytes) (path : List Common.DigestBytes) :
    walkMWithHash (m := Id) (fun a ↦ pure (H a)) idx node path = walk H idx node path := by
  induction path generalizing idx node with
  | nil => rfl
  | cons s rest ih =>
    simp only [walkMWithHash, walk, apply_ite H]
    exact ih _ _

/-- **Over a pure function, the verification is `verifyCell`.** -/
theorem verifyCellM_id (r : ℕ) (com : Common.DigestBytes) (p : Fin (r * 128)) (x : Cell) (τ : CellOpening) :
    verifyCellMWithHash (m := Id) (fun a ↦ pure (H a)) r com p x τ = verifyCell H r com p x τ := by
  simp only [verifyCellMWithHash, verifyCell, walkM_id, cellDigestWithHash]
  rfl

end Pure

/-! ## The duplex discipline -/

/-- **The duplex discipline with a postcondition**: along every run, every direct call is
admissible after the earlier answers (`Duplex`), and every result satisfies `post` with the
answers so far. -/
def DuplexP {α : Type} (post : α → List KState → Prop) :
    OracleComp Rom2 α → List KState → Prop
  | .pure a, hist => post a hist
  | .liftBind (.inr (.inr x)) k, hist =>
      Admissible KState.zero keccakNF hist x ∧ ∀ y, DuplexP post (k y) (y :: hist)
  | .liftBind _ k, hist => ∀ u, DuplexP post (k u) hist

theorem duplexP_pure {α : Type} {post : α → List KState → Prop} {a : α} {hist : List KState}
    (h : post a hist) : DuplexP post (pure a : OracleComp Rom2 α) hist := h

theorem duplexP_query_bind_F {α : Type} {post : α → List KState → Prop} (x : KState)
    (k : KState → OracleComp Rom2 α) (hist : List KState) :
    DuplexP post (liftM (Rom2.query (.inr (.inr x))) >>= k) hist ↔
      Admissible KState.zero keccakNF hist x ∧ ∀ y, DuplexP post (k y) (y :: hist) := Iff.rfl

theorem duplexP_query_bind_other {α : Type} {post : α → List KState → Prop}
    (t : Rom2.Domain) (ht : ∀ x, t ≠ .inr (.inr x)) (k : Rom2.Range t → OracleComp Rom2 α)
    (hist : List KState) :
    DuplexP post (liftM (Rom2.query t) >>= k) hist ↔ ∀ u, DuplexP post (k u) hist := by
  rcases t with n | a | x
  · exact Iff.rfl
  · exact Iff.rfl
  · exact absurd rfl (ht x)

/-- **Sequencing**: a computation with postcondition `Q`, then one with postcondition `R` from
every result and history satisfying `Q`. -/
theorem duplexP_bind {α β : Type} {Q : α → List KState → Prop} {R : β → List KState → Prop}
    {X : OracleComp Rom2 α} {f : α → OracleComp Rom2 β} {hist : List KState}
    (hX : DuplexP Q X hist) (hf : ∀ a hist', Q a hist' → DuplexP R (f a) hist') :
    DuplexP R (X >>= f) hist := by
  induction X using OracleComp.inductionOn generalizing hist with
  | pure a => simpa using hf a hist hX
  | query_bind t k ih =>
    rw [bind_assoc]
    rcases t with n | a | x
    · exact (duplexP_query_bind_other (.inl n) (by simp) _ hist).mpr fun u ↦
        ih u ((duplexP_query_bind_other (.inl n) (by simp) _ hist).mp hX u)
    · exact (duplexP_query_bind_other (.inr (.inl a)) (by simp) _ hist).mpr fun u ↦
        ih u ((duplexP_query_bind_other (.inr (.inl a)) (by simp) _ hist).mp hX u)
    · obtain ⟨hadm, hk⟩ := (duplexP_query_bind_F x k hist).mp hX
      exact (duplexP_query_bind_F x _ hist).mpr ⟨hadm, fun y ↦ ih y (hk y)⟩

theorem duplexP_mono {α : Type} {Q R : α → List KState → Prop} {X : OracleComp Rom2 α}
    {hist : List KState} (hX : DuplexP Q X hist) (h : ∀ a hist', Q a hist' → R a hist') :
    DuplexP R X hist := by
  simpa using duplexP_bind (f := pure) hX fun a hist' hq ↦ duplexP_pure (h a hist' hq)

/-- The duplex discipline is the discipline with the trivial postcondition. -/
theorem duplex_of_duplexP {α : Type} {X : OracleComp Rom2 α} {hist : List KState}
    {Q : α → List KState → Prop} (hX : DuplexP Q X hist) :
    Duplex KState.zero keccakNF X hist := by
  induction X using OracleComp.inductionOn generalizing hist with
  | pure a => trivial
  | query_bind t k ih =>
    rcases t with n | a | x
    · exact fun u ↦ ih u ((duplexP_query_bind_other (.inl n) (by simp) _ hist).mp hX u)
    · exact fun u ↦ ih u ((duplexP_query_bind_other (.inr (.inl a)) (by simp) _ hist).mp hX u)
    · obtain ⟨hadm, hk⟩ := (duplexP_query_bind_F x k hist).mp hX
      exact ⟨hadm, fun y ↦ ih y (hk y)⟩

theorem duplexP_hR_bind {α : Type} {post : α → List KState → Prop} (a : List UInt8)
    (k : Common.DigestBytes → OracleComp Rom2 α) (hist : List KState) (hk : ∀ d, DuplexP post (k d) hist) :
    DuplexP post (hR a >>= k) hist :=
  (duplexP_query_bind_other (.inr (.inl a)) (by simp) k hist).mpr hk

theorem duplexP_fQuery_bind {α : Type} {post : α → List KState → Prop} (x : KState)
    (k : KState → OracleComp Rom2 α) (hist : List KState)
    (hadm : Admissible KState.zero keccakNF hist x) (hk : ∀ y, DuplexP post (k y) (y :: hist)) :
    DuplexP post (fQuery (Msg := List UInt8) (Dg := DigestBytes) x >>= k) hist :=
  (duplexP_query_bind_F x k hist).mpr ⟨hadm, hk⟩

theorem admissible_mono {hist hist' : List KState} {x : KState} (h : hist ⊆ hist')
    (hx : Admissible KState.zero keccakNF hist x) : Admissible KState.zero keccakNF hist' x := by
  rcases hx with hx | ⟨y, hy, hxy⟩
  · exact Or.inl hx
  · exact Or.inr ⟨y, h hy, hxy⟩

theorem stateToLanes_zero : stateToLanes KState.zero = Vector.replicate 25 0 :=
  LeanVM.Rpm.ofRpm_zero

/-- A sponge whose state is the lanes of an earlier answer. -/
def SpongeOK (hist : List KState) (s : Sponge) : Prop := ∃ y ∈ hist, s.state = stateToLanes y

/-- A duplexing permutes an admissible state. -/
theorem admissible_duplexInput {hist : List KState} {s : Sponge} (hs : SpongeOK hist s) :
    Admissible KState.zero keccakNF hist (lanesToState (duplexInput s)) := by
  obtain ⟨y, hy, hsy⟩ := hs
  have hk := lanesToState_keep (L := duplexInput s) (y := y) fun i hi ↦ by
    simp only [duplexInput, Vector.getElem_ofFn, rateLanes, Fin.getElem_fin,
      show ¬ (i : ℕ) < 16 by omega, ↓reduceIte, hsy]
  exact Or.inr ⟨y, hy, hk.1, keccakNF_blockTo y _ hk.2⟩

/-- A fresh sponge permutes an admissible state. -/
theorem admissible_newInput (hist : List KState) (iv publicInput : Common.DigestBytes) :
    Admissible KState.zero keccakNF hist (lanesToState (freshSpongeInput iv publicInput)) := by
  have hk := lanesToState_keep (L := freshSpongeInput iv publicInput) (y := KState.zero) fun i
      hi ↦ by
    simp only [freshSpongeInput, Vector.getElem_ofFn, stateToLanes_zero, Vector.getElem_replicate,
      Fin.getElem_fin, show ¬ (i : ℕ) < 4 by omega, show ¬ (i : ℕ) < 8 by omega, ↓reduceIte]
  exact Or.inl ⟨hk.1, keccakNF_blockTo KState.zero _ hk.2⟩

/-- The postcondition of the sponge's steps: a good sponge, and the earlier answers kept. -/
def SpongePost (hist : List KState) (s : Sponge) (hist' : List KState) : Prop :=
  SpongeOK hist' s ∧ hist ⊆ hist'

theorem duplexP_pR {hist : List KState} {L : Lanes}
    (hadm : Admissible KState.zero keccakNF hist (lanesToState L)) :
    DuplexP (fun L' hist' ↦ (∃ y ∈ hist', L' = stateToLanes y) ∧ hist ⊆ hist') (pR L) hist := by
  rw [pR, lanePerm, map_eq_bind_pure_comp]
  exact duplexP_fQuery_bind _ _ hist hadm fun y ↦
    duplexP_pure ⟨⟨y, List.mem_cons_self, rfl⟩, List.subset_cons_self _ _⟩

theorem duplexP_newM (hist : List KState) (iv publicInput : Common.DigestBytes) :
    DuplexP (SpongePost hist) (Sponge.newWith pR iv publicInput) hist := by
  refine duplexP_bind (duplexP_pR (admissible_newInput hist iv publicInput)) fun L hist' h ↦ ?_
  obtain ⟨⟨y, hy, rfl⟩, hsub⟩ := h
  exact duplexP_pure ⟨⟨y, hy, rfl⟩, hsub⟩

theorem SpongePost.trans {h₀ h₁ h₂ : List KState} {s : Sponge} (h01 : h₀ ⊆ h₁)
    (h : SpongePost h₁ s h₂) : SpongePost h₀ s h₂ := ⟨h.1, fun _ ha ↦ h.2 (h01 ha)⟩

/-- A nonce's state is permuted from an earlier answer's lanes. -/
theorem duplexP_nonceR {hist : List KState} {y : Lanes} (hy : ∃ y' ∈ hist, y = stateToLanes y')
    (nonce : ℕ) :
    DuplexP (fun L' hist' ↦ (∃ y ∈ hist', L' = stateToLanes y) ∧ hist ⊆ hist')
      (pR (nonceInput y nonce)) hist :=
  duplexP_pR (admissible_duplexInput (s := ⟨y, _⟩) hy)

/-- **The nonce search follows the duplex discipline**: each nonce's call permutes the seeded
answer's lanes with the nonce over the rate. -/
theorem duplexP_grindR (y : Lanes) : ∀ (fuel nonce : ℕ) (hist₀ hist : List KState),
    hist₀ ⊆ hist → (∃ y' ∈ hist, y = stateToLanes y') →
      DuplexP (fun _ hist' ↦ hist₀ ⊆ hist') (grindMWithHash pR y nonce fuel) hist
  | 0, _, _, _, h0, _ => duplexP_pure h0
  | fuel + 1, nonce, hist₀, hist, h0, hy => by
    unfold grindMWithHash
    refine duplexP_bind (duplexP_nonceR hy nonce) fun o h₁ ho ↦ ?_
    split
    · exact duplexP_pure fun _ ha ↦ ho.2 (h0 ha)
    · obtain ⟨y', hy', rfl⟩ := hy
      exact duplexP_grindR _ fuel (nonce + 1) hist₀ h₁ (fun _ ha ↦ ho.2 (h0 ha))
        ⟨y', ho.2 hy', rfl⟩

/-- The duplex discipline of the nonces' draws. -/
theorem duplexP_branchDrawsR (y : Lanes) : ∀ (js : List (Fin nLabels)) (hist₀ hist : List KState),
    hist₀ ⊆ hist → (∃ y' ∈ hist, y = stateToLanes y') →
      DuplexP (fun _ hist' ↦ hist₀ ⊆ hist') (branchDrawsM pR y js) hist
  | [], _, _, h0, _ => duplexP_pure h0
  | j :: js, hist₀, hist, h0, hy => by
    unfold branchDrawsM
    refine duplexP_bind (duplexP_nonceR hy (j.val - 1)) fun o h₁ ho ↦ ?_
    obtain ⟨y', hy', rfl⟩ := hy
    exact duplexP_bind (duplexP_branchDrawsR _ js hist₀ h₁ (fun _ ha ↦ ho.2 (h0 ha))
      ⟨y', ho.2 hy', rfl⟩) fun _ h₂ hs₂ ↦ duplexP_pure hs₂

/-- **The challenge's sponge follows the duplex discipline**: its first call permutes a fresh
sponge, a non-final block into the zero state, and each nonce's call an earlier answer's lanes. -/
theorem duplexP_membershipChallengeR (root : Common.DigestBytes) (hist : List KState) :
    DuplexP (fun _ hist' ↦ hist ⊆ hist') (membershipChallengeMWithHash hR pR root) hist := by
  unfold membershipChallengeMWithHash
  refine duplexP_hR_bind _ _ hist fun iv ↦ ?_
  refine duplexP_bind (duplexP_newM hist iv _) fun s₁ h₁ hs₁ ↦ ?_
  exact duplexP_grindR _ _ _ hist h₁ hs₁.2 hs₁.1

/-- The duplex discipline of the draws (`membershipChallengeVecM`). -/
theorem duplexP_membershipChallengeVecR (root : Common.DigestBytes) (hist : List KState) :
    DuplexP (fun _ hist' ↦ hist ⊆ hist') (membershipChallengeVecM hR pR root) hist := by
  unfold membershipChallengeVecM
  generalize Common.SeedDuplex.branchIdx nLabels = js
  refine duplexP_hR_bind _ _ hist fun iv ↦ ?_
  refine duplexP_bind (duplexP_newM hist iv _) fun s₁ h₁ hs₁ ↦ ?_
  exact duplexP_bind (duplexP_branchDrawsR s₁.state js hist h₁ hs₁.2 hs₁.1) fun _ h₂ hs₂ ↦
    duplexP_pure hs₂

end LeanDa
