module

public import LeanDa.PositionBinding
public import LeanDa.StraightBound
public import Common.PiOnly
public import LeanDa.WithHashBridge

@[expose] public section

/-!
# LeanDA's end theorems: completeness, position binding, the membership test's soundness

The end statements of `Statement/LeanDa.lean` name no argument system.

* **Completeness** (`leanDa_complete`), for every function `π` on the Keccak state: an honest
  opening verifies (`verifyCell_openCell`, for any hash), and a matrix of codewords commits to its
  root and passes the membership test on every challenge (`membershipCheckOpt_of_mem_code`).
* **Position binding** (`leanDa_positionBinding_rpm`): the game is the game with the hash oracle
  (`posBindingGameH`, `LeanDa.HashOracle`), each hash call expanded into its permutation calls
  (`positionBindingGame_eq_expand`), so the bound is `leanDa_positionBinding_rpmH`'s
  (`LeanDa.PositionBinding`): a win is a collision of `H`.
* **The membership test's soundness** (`leanDa_membershipSound_rpm`). The adversary, its root and
  matrix, is a code-binding adversary that opens no cell (`memAdv`), its proof the matrix, for the
  oracle-free argument that accepts everything (`acceptAll`) and the extractor that returns the
  proof (`proofMatrix`). For them the straight-line verdict (`tailH`, `LeanDa.Straight`) is the
  game's event: the matrix commits to the root, passes the membership check at the selected
  challenge, and is not a matrix of codewords (`tailH_noOpening`). The game moves to the two-oracle
  model (`relabel_memGameH`, `Common.keccak256_transfer2`), the relation's nonce search is the
  selection over the root's draws (`run'_memPost_eq`, by `run'_drawsL_select`), and the duplex
  lemma gives the simulated world (`membershipGame_le_G`), where the verdict is a bad cache
  (`prT_idealT_tailH_le`, `LeanDa.StraightBound`). Only the adversary's calls are charged: the
  relation's check, whose nonce search makes `2^64 + 2` calls on its worst path, enters the
  transfer's squared term alone.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA: position
binding is his vector commitment's, and the membership test's soundness his committed soundness,
by the straight-line argument built on his framework and games.
-/

open OracleComp OracleSpec Common Common.SeedDuplex PqDas
open Common.Duplex (GSpec hP gaP)
open scoped ENNReal

namespace LeanDa

/-! ## Completeness -/

/-- **LeanDA is complete, for every function `π`** (`LeanDaComplete`): the honest opening verifies
for any hash, and a matrix of codewords satisfies the relation at its commitment, whatever the
root's challenge. -/
theorem leanDa_complete : LeanDaComplete := by
  intro r π hr
  refine ⟨fun cells position ↦ ?_, fun message ↦ ?_⟩
  · rw [verifyCellM_eq_withHash, commitCells_eq_withHash, openCell_eq_withHash]
    exact (congrArg Id.run (verifyCellM_id (hashOver π) r _ _ _ _)).trans
      (verifyCell_openCell (hashOver π) hr cells position)
  · have hcode : encodeMatrix message ∈ (leanDaErasureCode r).code := ⟨message, rfl⟩
    have hcomm : commitCellsMWithHash (m := Id) (keccakDigestBytes (fun x ↦ pure (π x)))
        (encodeMatrix message) = pure (commitCellsWithHash (hashOver π) (encodeMatrix message)) :=
      commitCellsM_eval (fun x ↦ x) (fun _ ↦ rfl) (fun _ _ ↦ rfl) _ _ (fun _ ↦ rfl) _
    rw [relationM_eq_withHash, commitCells_eq_withHash]
    unfold relationMWithHash
    rw [hcomm]
    simp only [Id.run_bind, Id.run_pure, decide_true, Bool.true_and]
    exact membershipCheckOpt_of_mem_code hcode _

/-! ## The oracle programs, expanded

The statement's games query coins, `π` and `π⁻¹` and hash with Keccak-256 over `π`
(`Common.keccak256OverPermutation`); the proofs hold them with a Keccak-256 oracle
(`LeanDa.HashOracle`), each hash call expanded into its permutation calls (`Common.expand`), with
the same distribution (`Common.runK_expand`) and the same number of permutation calls
(`Common.isWeightBound_expand_iff`). -/

theorem expand_hK (a : List UInt8) : simulateQ expand (hK a) = keccak256OverPermutation a := by
  simp [hK, expand]

theorem expand_pK (x : LeanVM.Semantics.KeccakState) :
    simulateQ expand (pK x) = queryPermutation x := by
  simp [pK, expand, queryPermutation]

theorem expand_verifyCellM (r : ℕ) (com : Common.DigestBytes) (p : Fin (r * 128)) (x : Cell)
    (τ : ByteOpening) :
    simulateQ expand (verifyCellMWithHash hK r com p x τ) =
      verifyCellMWithHash keccak256OverPermutation r com p x τ := by
  rw [verifyCellM_map (fun x ↦ simulateQ expand x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [expand_hK]

theorem expand_relationM {r : ℕ} (root : Common.DigestBytes) (c : Fin (r * 128) → Cell) :
    simulateQ expand (relationMWithHash hK pK root c) =
      relationMWithHash keccak256OverPermutation queryPermutation root c := by
  simp only [relationMWithHash, simulateQ_bind, simulateQ_pure]
  rw [membershipChallengeM_map (fun x ↦ simulateQ expand x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _), commitCellsM_map (fun x ↦ simulateQ expand x)
    (fun _ ↦ simulateQ_pure _ _) (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [expand_hK, expand_pK]

/-! ## Position binding -/

/-- The hash-oracle argument that accepts everything. -/
def trivialArgument (r : ℕ) : ArgumentRpmH r Unit Unit where
  setup := pure ()
  prove _ _ _ := pure ()
  verify _ _ _ := pure true

/-- A position-binding adversary's output with its digests as bytes, the commitment's proof empty. -/
def positionBindingOutBytes {r : ℕ}
    (out : LeanVM.Protocol.Digest × Fin (r * 128) × Cell × CellOpening × Cell × CellOpening) :
    (Common.DigestBytes × Unit) × Fin (r * 128) × Cell × ByteOpening × Cell × ByteOpening :=
  ((out.1.toBytes, ()), out.2.1, out.2.2.1, out.2.2.2.1.toBytes, out.2.2.2.2.1,
    out.2.2.2.2.2.toBytes)

/-- **The position-binding game is the game with the hash oracle, expanded**, for the argument
that accepts everything, the adversary's digests read as bytes. -/
theorem positionBindingGame_eq_expand (r : ℕ) (adversary : PositionBindingAdversary r) :
    positionBindingGame r adversary =
      simulateQ expand (posBindingGameH r (trivialArgument r)
        (fun _ ↦ positionBindingOutBytes <$> simulateQ embed adversary)) := by
  unfold positionBindingGame posBindingGameH
  have h0 : (liftM (trivialArgument r).setup : OracleComp KSpecH Unit) = pure () := rfl
  rw [h0, pure_bind, bind_map_left, simulateQ_bind, simulateQ_expand_embed]
  refine bind_congr fun out ↦ ?_
  obtain ⟨commitment, position, cell, opening, cell', opening'⟩ := out
  by_cases h : cell = cell' <;> simp [trivialArgument, expand_verifyCellM, verifyCellM_eq_withHash,
    keccakDigestBytes_queryPermutation, positionBindingOutBytes, h]

/-- **LeanDA is position binding in the random-permutation model** (`LeanDaPositionBinding`): the
game is the game with the hash oracle, expanded, with the same distribution and the same
permutation calls. -/
theorem leanDa_positionBinding_rpm : LeanDaPositionBinding := by
  intro r adversary Q hQ
  rw [positionBindingGame_eq_expand, isWeightBound_expand_iff] at hQ
  rw [positionBindingGame_eq_expand, runK_expand]
  exact leanDa_positionBinding_rpmH r (trivialArgument r) _ Q hQ

/-! ## The membership test's soundness -/

section Membership

variable (r : ℕ)

/-- The oracle-free argument that accepts everything, its proof a matrix. -/
def acceptAll : Nark (Unit × Common.DigestBytes × MembershipChallenge) (Fin (r * 128) → Cell) Unit
    (Fin (r * 128) → Cell) (fun _ _ ↦ true) where
  setup := pure ()
  prove _ _ w := w
  verify _ _ _ := true

/-- The extractor that returns the proof, a matrix. -/
def proofMatrix : Nark.Extractor (Unit × Common.DigestBytes × MembershipChallenge)
    (Fin (r * 128) → Cell) Unit (Fin (r * 128) → Cell) :=
  fun _ _ w ↦ w

/-- A root and a matrix as a code-binding adversary's output that opens no cell. -/
def withNoOpening (out : Common.DigestBytes × (Fin (r * 128) → Cell)) :
    CbOut r (Fin (r * 128) → Cell) := (out, [])

/-- The membership adversary with its root as bytes. -/
def byteAdversary (adversary : MembershipAdversary r) :
    OracleComp RandomPermutationOracles (Common.DigestBytes × (Fin (r * 128) → Cell)) :=
  (fun out ↦ (out.1.toBytes, out.2)) <$> adversary

/-- **The membership adversary as a code-binding adversary on byte states** that opens no cell:
its root, and its matrix as the proof. -/
def memAdv (adversary : MembershipAdversary r) : CodeBindingAdvB r Unit (Fin (r * 128) → Cell) :=
  fun _ ↦ withNoOpening r <$> simulateQ relabel (simulateQ embed (byteAdversary r adversary))

open Classical in
/-- Whether a matrix is not a matrix of codewords. -/
noncomputable def notCodeword (cells : Fin (r * 128) → Cell) : Bool :=
  !decide (cells ∈ (leanDaErasureCode r).code)

theorem notCodeword_eq_true_iff (cells : Fin (r * 128) → Cell) :
    notCodeword r cells = true ↔ ¬ IsCodewordMatrix cells := by
  classical
  have h : IsCodewordMatrix cells ↔ cells ∈ (leanDaErasureCode r).code :=
    ⟨fun ⟨m, hm⟩ ↦ ⟨m, hm.symm⟩, fun ⟨m, hm⟩ ↦ ⟨m, hm.symm⟩⟩
  simp [notCodeword, h]

/-! ### The game, with its event as a verdict -/

/-- **The membership game with its event as a verdict**: the relation holds and the matrix is not
a matrix of codewords. -/
noncomputable def memGame (adversary : MembershipAdversary r) :
    OracleComp RandomPermutationOracles Bool := do
  let out ← adversary
  let ok ← relationWith queryPermutation out.1 out.2
  pure (ok && notCodeword r out.2)

/-- The same with the hash oracle. -/
noncomputable def memGameH (adversary : MembershipAdversary r) : OracleComp KSpecH Bool := do
  let out ← simulateQ embed (byteAdversary r adversary)
  let ok ← relationMWithHash hK pK out.1 out.2
  pure (ok && notCodeword r out.2)

theorem runWithRandomPermutation_map {α β : Type} (f : α → β)
    (G : OracleComp RandomPermutationOracles α) :
    runWithRandomPermutation (f <$> G) = f <$> runWithRandomPermutation G := by
  rw [runWithRandomPermutation, runWithRandomPermutation, simulateQ_map, StateT.run'_eq,
    StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]

/-- **The game's event is the verdict.** -/
theorem prEvent_membershipGame (adversary : MembershipAdversary r) :
    Pr{let out ← runWithRandomPermutation (membershipGame r adversary)}[
        out.1 = true ∧ ¬ IsCodewordMatrix out.2] =
      Pr{let b ← runWithRandomPermutation (memGame r adversary)}[b = true] := by
  have e : memGame r adversary =
      (fun out : Bool × (Fin (r * 128) → Cell) ↦ out.1 && notCodeword r out.2) <$>
        membershipGame r adversary := by
    simp only [memGame, membershipGame, map_bind, map_pure]
  rw [e, runWithRandomPermutation_map, prEvent_map]
  refine prEvent_congr_of_support _ _ _ fun z _ ↦ ?_
  rw [Bool.and_eq_true, notCodeword_eq_true_iff]

/-- **The game is the game with the hash oracle, expanded.** -/
theorem memGame_eq_expand (adversary : MembershipAdversary r) :
    memGame r adversary = simulateQ expand (memGameH r adversary) := by
  simp only [memGame, memGameH, simulateQ_bind, simulateQ_pure, simulateQ_expand_embed,
    expand_relationM, relationM_eq_withHash, keccakDigestBytes_queryPermutation, byteAdversary,
    bind_map_left]

/-! ### The verifier's part: the nonce search, then the verdict -/

/-- The verdict on the challenge `z`, with `H` among coins and `H`: the matrix commits to the
root, passes the check on `z`, and is not a matrix of codewords. -/
noncomputable def memPostH (out : CbOut r (Fin (r * 128) → Cell)) (z : Option E) :
    OracleComp (unifSpec + roSpec (List UInt8) DigestBytes) Bool := do
  let root ← commitCellsMWithHash hH out.1.2
  pure (decide (root = out.1.1) && membershipCheckOpt z out.1.2 && notCodeword r out.1.2)

/-- The same over the verifier's oracles. -/
noncomputable def memPostR (out : CbOut r (Fin (r * 128) → Cell)) (z : Option E) :
    OracleComp Rom2 Bool := do
  let root ← commitCellsMWithHash hR out.1.2
  pure (decide (root = out.1.1) && membershipCheckOpt z out.1.2 && notCodeword r out.1.2)

theorem memPostR_embH (out : CbOut r (Fin (r * 128) → Cell)) (z : Option E) :
    memPostR r out z = simulateQ embH (memPostH r out z) := by
  rw [memPostH, simulateQ_bind, commitCellsM_map (fun x ↦ simulateQ embH x) (fun _ ↦ rfl)
    (fun x f ↦ simulateQ_bind _ x f)]
  simp only [simulateQ_embH_hH, simulateQ_pure, memPostR]

/-- **The verifier's part of the membership game**: the nonce search over its direct calls, then
the verdict on the challenge. -/
noncomputable def memPost (_ : Unit) (out : CbOut r (Fin (r * 128) → Cell)) :
    OracleComp Rom2 Bool :=
  membershipChallengeMWithHash hR pR out.1.1 >>= memPostR r out

theorem isWeightBound_memPostR (out : CbOut r (Fin (r * 128) → Cell)) (z : Option E) :
    QueryCostAtMost (memPostR r out z) rCalls (relCalls r) := by
  unfold memPostR
  have h := isWeightBound_commitCellsM hR rCalls 1 16
    (fun a b ↦ (isWeightBound_query rCalls (.inr (.inl (pairBytes a b)))).mono
      (by simp [rCalls, length_pairBytes]))
    (fun x ↦ (isWeightBound_query rCalls (.inr (.inl (cellBytes x)))).mono
      (by simp [rCalls, length_cellBytes])) out.1.2
  exact (h.bind fun _ ↦ isWeightBound_pure _ _ 0).mono (le_of_eq (by ring))

theorem isWeightBound_memPost (crs : Unit) (out : CbOut r (Fin (r * 128) → Cell)) :
    QueryCostAtMost (memPost r crs out) rCalls (nLabels + 1 + relCalls r) :=
  (isWeightBound_membershipChallengeM rCalls hR pR
    ((isWeightBound_query rCalls (.inr (.inl membershipLabel))).mono
        (by simp [rCalls, label_calls]))
    (fun L ↦ isWeightBound_map _ (isWeightBound_query rCalls (.inr (.inr _)))) _).bind fun z ↦
      isWeightBound_memPostR r out z

theorem duplex_memPost (crs : Unit) (out : CbOut r (Fin (r * 128) → Cell)) :
    Duplex KState.zero keccakNF (memPost r crs out) [] :=
  duplex_of_duplexP (Q := fun _ _ ↦ True) <|
    duplexP_bind (duplexP_membershipChallengeR _ []) fun z _ _ ↦ by
      rw [memPostR_embH]; exact duplexP_embH _ _

/-! ### The game in the two-oracle form -/

/-- **The membership game is its two-oracle form**, the relation's check the verifier's part. -/
theorem relabel_memGameH (adversary : MembershipAdversary r) :
    simulateQ relabel (memGameH r adversary) =
      simulateQ (toOne (E := KRest) (C := KCap)) (rpmGame2 (liftM (acceptAll r).setup)
        (fun crs ↦ memAdv r adversary ((), crs)) (memPost r)) := by
  rw [toOne_rpmGame2]
  have h0 : (liftM (acceptAll r).setup : OracleComp KSpecB Unit) = pure () := rfl
  rw [h0, pure_bind]
  simp only [memGameH, memAdv, simulateQ_bind, bind_map_left, simulateQ_pure]
  refine bind_congr fun out ↦ ?_
  simp only [relationMWithHash, simulateQ_bind, relabel_membershipChallengeM, memPost,
    toK_membershipChallengeM, bind_assoc]
  refine bind_congr fun z ↦ ?_
  simp only [memPostR, simulateQ_bind, toK_commitCellsM, relabel_commitCellsM, simulateQ_pure,
    pure_bind, withNoOpening]
  rfl

/-- **The adversary's calls are the calls of its code-binding game**, which opens no cell. -/
theorem isWeightBound_memAdv (adversary : MembershipAdversary r) (Q : ℕ)
    (hQ : QueryCostAtMost adversary permutationCallCost Q) :
    QueryCostAtMost (codeBindingGame2 r (acceptAll r) (memAdv r adversary)) permCalls2 Q := by
  have hQ' : QueryCostAtMost (byteAdversary r adversary) permutationCallCost Q :=
    isWeightBound_map _ hQ
  have hE : QueryCostAtMost (simulateQ embed (byteAdversary r adversary)) permCallsH Q :=
    (isWeightBound_expand_iff _ _).mp (by rw [simulateQ_expand_embed]; exact hQ')
  have hB : QueryCostAtMost (simulateQ relabel (simulateQ embed (byteAdversary r adversary)))
      permCallsB Q :=
    isWeightBound_relabel hE
  have h0 : QueryCostAtMost (rpmGame2 (liftM (acceptAll r).setup)
      (fun _ : Unit ↦ simulateQ relabel (simulateQ embed (byteAdversary r adversary)))
      (fun _ _ ↦ (pure () : OracleComp Rom2 Unit))) permCalls2 Q :=
    ((isWeightBound_hEmbed2_setup (acceptAll r).setup).bind fun _ ↦
      (isWeightBound_advEmbed hB).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (by omega)
  rw [codeBindingGame2]
  refine isWeightBound_rpmGame2_map (acceptAll r).setup _ _ (withNoOpening r) _ Q h0 fun x a ↦ ?_
  simp only [codeBindingPost, withNoOpening, List.map_nil, List.mapM_nil, pure_bind,
    simulateQ_pure]
  exact isWeightBound_pure _ _ _

/-- The calls of the two-oracle game: the adversary's and the relation's check. -/
theorem isWeightBound_memGame2 (adversary : MembershipAdversary r) (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r (acceptAll r) (memAdv r adversary)) permCalls2 Q) :
    QueryCostAtMost (rpmGame2 (liftM (acceptAll r).setup)
      (fun crs ↦ memAdv r adversary ((), crs)) (memPost r)) permCalls2 (ksCalls r Q) :=
  (IsWeightBound.bind_of_mem_support (isWeightBound_hEmbed2_setup (acceptAll r).setup) fun x hx ↦
    (isWeightBound_advEmbed_A r (acceptAll r) (memAdv r adversary) Q hQ x hx).bind fun _ ↦
      isWeightBound_hfEmbed (isWeightBound_memPost r x _)).mono (by unfold ksCalls; omega)

/-! ### The straight-line verdict of an adversary that opens no cell -/

/-- **The straight-line verdict is the game's event** for the argument that accepts everything,
the extractor that returns the proof, and no opened cell. -/
theorem tailH_noOpening (crs : Unit) (out : CbOut r (Fin (r * 128) → Cell)) (hout : out.2 = [])
    (l : MembershipChallenge) :
    tailH r (acceptAll r) (proofMatrix r) crs out l = memPostH r out (selectChal l) := by
  classical
  unfold tailH memPostH
  simp only [proofMatrix]
  refine bind_congr fun root ↦ ?_
  by_cases h1 : root = out.1.1 <;>
    by_cases h2 : membershipCheckOpt (selectChal l) out.1.2 = true <;>
    by_cases h3 : out.1.2 ∈ (leanDaErasureCode r).code <;>
    simp [acceptAll, notCodeword, firstBad, hout, h1, h2, h3]

/-- **The nonce search, then the verdict, is the root's draws, then the straight-line verdict**,
over the random function `F`: the search's calls are the draws' first ones. -/
theorem run'_memPost_eq (crs : Unit) (out : CbOut r (Fin (r * 128) → Cell)) (hout : out.2 = [])
    (c : Cache2) :
    (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl (memPost r crs out)).run' c =ᵈ
      (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
        (chalR out.1.1 >>= fun zs ↦ simulateQ embH
          (tailH r (acceptAll r) (proofMatrix r) crs out (toVec zs)))).run' c := by
  have hT : ∀ l, simulateQ embH (tailH r (acceptAll r) (proofMatrix r) crs out l) =
      memPostR r out (selectChal l) := fun l ↦ by
    rw [tailH_noOpening r crs out hout, ← memPostR_embH]
  have e1 : (chalR out.1.1 >>= fun zs ↦ simulateQ embH
        (tailH r (acceptAll r) (proofMatrix r) crs out (toVec zs))) =
      hR membershipLabel >>= fun iv ↦ Sponge.newWith pR iv out.1.1 >>= fun s ↦
        drawsL pR s.state (List.range' 0 nonceCount) >>= fun zs ↦
          memPostR r out (selectList zs) := by
    have e0 : (chalR out.1.1 >>= fun zs ↦ simulateQ embH
          (tailH r (acceptAll r) (proofMatrix r) crs out (toVec zs))) =
        membershipChallengeVecM hR pR out.1.1 >>= fun l ↦ memPostR r out (selectChal l) := by
      rw [membershipChallengeVecM_eq_chalP, bind_map_left]
      exact bind_congr fun zs ↦ hT _
    rw [e0, membershipChallengeVecM_eq_drawsL]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun iv ↦ bind_congr fun s ↦ ?_
    rw [drawsL]
    exact mapM_bind_congr _ _ _ _ fun zs hzs ↦ by
      rw [selectChal_drawsVec _ zs (by simpa using hzs)]
  have e2 : memPost r crs out = hR membershipLabel >>= fun iv ↦
      Sponge.newWith pR iv out.1.1 >>= fun s ↦
        grindL pR s.state (List.range' 0 nonceCount) >>= memPostR r out := by
    rw [memPost, membershipChallengeM_eq_grindL]
    simp only [bind_assoc]
  rw [e1, e2]
  exact (run'_bind_congr (hR membershipLabel) _ _ c fun iv c₁ ↦
    run'_bind_congr (Sponge.newWith pR iv out.1.1) _ _ c₁ fun s c₂ ↦
      run'_drawsL_select s.state _ _ c₂).symm

/-! ### From the random-permutation model to the simulated world -/

/-- **From the random-permutation model to the simulated world**: the two-oracle transfer, of the
adversary's calls and the relation's check, the nonce search read as the selection over the root's
draws, and the duplex lemma, of the adversary's calls. -/
theorem membershipGame_le_G (adversary : MembershipAdversary r) (Q : ℕ)
    (hQ : QueryCostAtMost (codeBindingGame2 r (acceptAll r) (memAdv r adversary)) permCalls2 Q) :
    Pr{let out ← runWithRandomPermutation (membershipGame r adversary)}[
        out.1 = true ∧ ¬ IsCodewordMatrix out.2] ≤
      prT ((acceptAll r).setup >>= fun crs ↦ idealT r (memAdv r adversary) crs
        (tailH r (acceptAll r) (proofMatrix r) crs)) +
        ((ksCalls r Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 + dupTerm Q := by
  rw [prEvent_membershipGame, memGame_eq_expand, runK_expand, (runK_relabel _).prEvent_eq,
    relabel_memGameH]
  change Pr{let b ← realGame2 keccakPadding KState.zero _}[b = true] ≤ _
  have hq := isWeightBound_memGame2 r adversary Q hQ
  rw [permCalls2_eq] at hq
  obtain ⟨h1, -⟩ := keccak256_transfer2 (liftM (acceptAll r).setup)
    (fun crs ↦ memAdv r adversary ((), crs)) (memPost r) (fun x a ↦ duplex_memPost r x a)
    (ksCalls r Q) hq (· = true)
  refine h1.trans ?_
  rw [add_right_comm]
  refine add_le_add ?_ le_rfl
  have hsplit : Pr{let b ← romRun2 (simulateQ (hInF (E := KRest) (C := KCap))
        (liftM (acceptAll r).setup) >>= fun x ↦
          advS2 keccakPadding KState.zero (memAdv r adversary ((), x)) >>= fun a ↦
            memPost r x a)}[b = true] =
      Pr{let b ← (acceptAll r).setup >>= fun crs ↦ romRun2 (advS2 keccakPadding KState.zero
        (memAdv r adversary ((), crs)) >>= fun out ↦ memPost r crs out)}[b = true] := by
    rw [romRun2, simulateQ_liftM_of_coins _ (fun _ ↦ rfl), simulateQ_bind,
      StateT.run'_eq, StateT.run_bind, simulateQ_romImpl_liftM_run, bind_map_left, map_bind]
    rfl
  rw [hsplit]
  refine prEvent_bind_le_add_const_of_support _ _ _ _ _ _ fun crs hcrs ↦ ?_
  have hB := isWeightBound_advS2 r (acceptAll r) (memAdv r adversary) Q hQ crs hcrs
  have h2 : Pr{let b ← romRun2 (advS2 keccakPadding KState.zero
        (memAdv r adversary ((), crs)) >>= fun out ↦ memPost r crs out)}[b = true] =
      Pr{let b ← (simulateQ (hfSpec (List UInt8) DigestBytes KState).romImpl
        (advS2 keccakPadding KState.zero (memAdv r adversary ((), crs)) >>= fun out ↦
          chalR out.1.1 >>= fun zs ↦ simulateQ embH
            (tailH r (acceptAll r) (proofMatrix r) crs out (toVec zs)))).run' ∅}[b = true] := by
    rw [romRun2]
    simp only [memAdv, advS2_map, bind_map_left]
    exact (run'_bind_congr _ _ _ ∅ fun b c ↦
      run'_memPost_eq r crs (withNoOpening r b) rfl c).prEvent_eq _
  rw [h2]
  exact duplex_le (D := daDuplex) daDuplex_cap _ Q hB (fun out ↦ out.1.1)
    (fun out l ↦ tailH r (acceptAll r) (proofMatrix r) crs out l)

end Membership

/-- **The terms besides the straight-line verdict's selected draws**: the transfer of `K ≤ Q + 2^65`
calls (the relation's check among them), the duplex lemma and the hash's bad events among
`2 Q + 2^20` hash queries are at most `(Q + 2^19)² · 2^-247`, and the membership test's two terms
at most `(Q + 2^10) · 2^-125`. -/
theorem membership_rest_le (Q K : ℕ) (hK : K ≤ Q + 2 ^ 65) :
    (K : ℝ≥0∞) ^ 2 / 2 ^ 508 + dupTerm Q +
        (((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) * (65 * ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
          ((Q : ℝ≥0∞) * ((2 ^ 13 - 1) / 2 ^ 138) + (2 ^ 13 - 1) / 2 ^ 128)) ≤
      ((Q : ℝ≥0∞) + 2 ^ 10) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        ((Q : ℝ≥0∞) + 2 ^ 19) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 247 := by
  calc _ ≤ (K : ℝ≥0∞) ^ 2 / 2 ^ 508 + dupTerm Q +
        (((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) * (65 * ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
          ((Q : ℝ≥0∞) * (2 ^ 13 / 2 ^ 138) + 2 ^ 13 / 2 ^ 128)) := by
        gcongr <;> exact tsub_le_self
    _ ≤ _ := ?_
  unfold dupTerm
  simp only [nLabels, nonceCount]
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_add, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ne_eq, ENNReal.div_eq_top,
    ENNReal.natCast_ne_top, ENNReal.pow_eq_top_iff, ENNReal.ofNat_ne_top, false_and, and_false,
    or_self, not_false_eq_true, ENNReal.mul_eq_top, pow_eq_zero_iff, OfNat.ofNat_ne_zero,
    ENNReal.add_eq_top, ENNReal.inv_eq_top, ENNReal.inv_eq_zero]
  push_cast
  have t5 : (Q : ℝ) * (2 ^ 13 / 2 ^ 138) = Q * (2 : ℝ)⁻¹ ^ 125 := by norm_num
  have t6 : (2 : ℝ) ^ 13 / 2 ^ 128 = 2 ^ 10 * (2 : ℝ)⁻¹ ^ 125 := by norm_num
  have hA : (2 : ℝ) ^ 92 * 2 ^ 256 ≤ 2 ^ 508 := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hB : (2 : ℝ) ^ 94 * 2 ^ 256 ≤ 2 ^ 576 := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hc : (264 : ℝ) / 2 ^ 256 ≤ (2 : ℝ)⁻¹ ^ 247 := by norm_num
  have hC0 : (0 : ℝ) < 2 ^ 256 := by positivity
  generalize (2 : ℝ) ^ 508 = A at hA ⊢
  generalize (2 : ℝ) ^ 576 = B at hB ⊢
  generalize (2 : ℝ) ^ 256 = C at hA hB hc hC0 ⊢
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  set y : ℝ := (Q : ℝ) + 2 ^ 19 with hy
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hy0 : (0 : ℝ) ≤ y := by positivity
  have hy2 : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  have hK' : (K : ℝ) ≤ 2 ^ 46 * y := by
    have : (K : ℝ) ≤ Q + 2 ^ 65 := by exact_mod_cast hK
    rw [hy]; nlinarith
  have hD : (Q : ℝ) + 2 ^ 64 + 1 + 1 ≤ 2 ^ 46 * y := by rw [hy]; nlinarith
  have hD0 : (0 : ℝ) ≤ (Q : ℝ) + 2 ^ 64 + 1 + 1 := by positivity
  have hAC : (2 : ℝ) ^ 92 / A ≤ 1 / C := by rw [div_le_div_iff₀ hA0 hC0]; linarith
  have hBC : (2 : ℝ) ^ 93 / B ≤ 1 / (2 * C) := by
    rw [div_le_div_iff₀ hB0 (by positivity)]; linarith
  have t1 : (K : ℝ) ^ 2 / A ≤ y ^ 2 * (1 / C) := by
    have : (K : ℝ) ^ 2 ≤ (2 ^ 46 * y) ^ 2 := pow_le_pow_left₀ hK0 hK' 2
    calc (K : ℝ) ^ 2 / A ≤ (2 ^ 46 * y) ^ 2 / A := by gcongr
      _ = y ^ 2 * (2 ^ 92 / A) := by ring
      _ ≤ y ^ 2 * (1 / C) := mul_le_mul_of_nonneg_left hAC hy2
  have t3 : ((Q : ℝ) + 2 ^ 64 + 1 + 1) * (2 * ((Q : ℝ) + 2 ^ 64 + 1 + 1) * B⁻¹) ≤
      y ^ 2 * (1 / (2 * C)) := by
    calc ((Q : ℝ) + 2 ^ 64 + 1 + 1) * (2 * ((Q : ℝ) + 2 ^ 64 + 1 + 1) * B⁻¹)
        ≤ (2 ^ 46 * y) * (2 * (2 ^ 46 * y) * B⁻¹) := by gcongr
      _ = y ^ 2 * (2 ^ 93 / B) := by ring
      _ ≤ y ^ 2 * (1 / (2 * C)) := mul_le_mul_of_nonneg_left hBC hy2
  have t4 : (2 * (Q : ℝ) + 2 ^ 20) * (65 * (2 * (Q : ℝ) + 2 ^ 20) / C) ≤ y ^ 2 * (260 / C) := by
    calc (2 * (Q : ℝ) + 2 ^ 20) * (65 * (2 * (Q : ℝ) + 2 ^ 20) / C) ≤
          (2 * y) * (65 * (2 * y) / C) := by gcongr <;> (rw [hy]; linarith)
      _ = y ^ 2 * (260 / C) := by ring
  have e7 : y ^ 2 * (264 / C) ≤ y ^ 2 * (2 : ℝ)⁻¹ ^ 247 := mul_le_mul_of_nonneg_left hc hy2
  have hsplit : y ^ 2 * (1 / C) + y ^ 2 * (1 / (2 * C)) + y ^ 2 * (260 / C) =
      y ^ 2 * (523 / (2 * C)) := by
    field_simp; ring
  have e8 : y ^ 2 * (523 / (2 * C)) ≤ y ^ 2 * (264 / C) := by
    refine mul_le_mul_of_nonneg_left ?_ hy2
    rw [div_le_div_iff₀ (by positivity) hC0]; linarith
  linarith [t1, t3, t4, t5, t6, e7, e8, hsplit]

/-- **LeanDA's membership test is sound in the random-permutation model**
(`LeanDaMembershipSound`), by the straight-line argument built on Benedikt Wagner's framework and
games (`LeanDa.StraightBound`), for the argument that accepts everything: the transfer to the
two-oracle model and the duplex lemma (`membershipGame_le_G`), then the event, the straight-line
verdict of an adversary that opens no cell, is a bad cache of the world with `H` and the draws
lazily sampled (`prT_idealT_tailH_le`: the hash's bad events, a selected accepting draw among the
adversary's, and the check's one fresh try). -/
theorem leanDa_membershipSound_rpm : LeanDaMembershipSound := by
  intro r hrM adversary Q hQ
  have hQ2 := isWeightBound_memAdv r adversary Q hQ
  have hN : maxRows = 32 := rfl
  have hK : ksCalls r Q ≤ Q + 2 ^ 65 := by
    unfold ksCalls relCalls nLabels nonceCount; omega
  have hG := membershipGame_le_G r adversary Q hQ2
  have hS : prT ((acceptAll r).setup >>= fun crs ↦ idealT r (memAdv r adversary) crs
      (tailH r (acceptAll r) (proofMatrix r) crs)) ≤
      ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) * (65 * ((2 * Q + 2 ^ 20 : ℕ) : ℝ≥0∞) / 2 ^ 256) +
        ((Q : ℝ≥0∞) * ((2 ^ 13 - 1) / 2 ^ 138) + (2 ^ 13 - 1) / 2 ^ 128) :=
    prEvent_bind_le_of_forall_le_of_support _ _ _ fun crs hcrs ↦ by
      obtain ⟨ha, hg⟩ := isWeightBound_advSim r (acceptAll r) (memAdv r adversary) Q hQ2 crs hcrs
      exact prT_idealT_tailH_le r (acceptAll r) (proofMatrix r) (memAdv r adversary) Q hrM crs
        ha hg
  have hR := membership_rest_le Q (ksCalls r Q) hK
  refine hG.trans (le_trans ?_ hR)
  refine (add_le_add (add_le_add hS le_rfl) le_rfl).trans (le_of_eq ?_)
  ring

end LeanDa
