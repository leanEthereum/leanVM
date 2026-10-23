/-
  LeanVM.Protocol.Compile.Rom.Prover

  The honest prover of a compiled verifier program with the hash in any monad: the prover of
  `LeanVM.Protocol.Compile.Prover` written so that it runs against the random oracle, with its
  `Id` instance the pure prover, its commutation with simulation, and its query bound.
-/

module

public import LeanVM.Protocol.Compile.Prover
public import LeanVM.Protocol.Compile.Cost

/-!
# The honest prover against the random oracle

`proveM H P S seed fuel` is the honest prover `prove` (`LeanVM.Protocol.Compile.Prover`) with
the hash `H : Bytes → m Digest` in any monad `m`, as the verifier `run` is. Its `Id` instance is
`prove` (`proveM_id`); at `H = queryH` it is an oracle computation, the honest prover of the
random-oracle model.

* The Merkle tree is built level by level as lists (`parentsM`, `rootOfLevelM`, `pathOfLevelM`);
  an opening rebuilds the tree it opens, as `openingAt` does.
* The proof-of-work search hashes the base `H(cv ‖ (0, 3))` once, then the nonces `0, 1, …` in
  order (`searchM`).
* `simulateQ_proveM`: interpreting the queries of `proveM queryH` by any implementation is
  running `proveM` with that implementation as the hash.
* `simulateQ_id_of_look`: a computation whose run against a log's answers returns `r` returns
  `r` against every hash function that agrees with the log.
* `isTotalQueryBound_proveM`: a program of cost `n` at height `h` (`Prog.CostLE`) makes the
  prover query the oracle at most `n · (2^(h + 1) + fuel + 1)` times, after the seed.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleComp OracleSpec

@[expose] public section

/-! ## The prover with the hash in any monad -/

section ProverM

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- The first `n` parents of a level: parent `j` hashes nodes `2j` and `2j + 1`. -/
def parentsM (level : List Digest) (n : ℕ) : m (List Digest) :=
  (List.range n).mapM fun j ↦
    H (digestBytes (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default))

/-- The root of a level of `2^k` nodes. -/
def rootOfLevelM : ℕ → List Digest → m Digest
  | 0, level => pure (level.getD 0 default)
  | k + 1, level => do rootOfLevelM k (← parentsM H level (2 ^ k))

/-- The authentication path of node `i` of a level of `2^k` nodes. -/
def pathOfLevelM : ℕ → List Digest → ℕ → m (List Digest)
  | 0, _, _ => pure []
  | k + 1, level, i => do
    let up ← parentsM H level (2 ^ k)
    let rest ← pathOfLevelM k up (i / 2)
    pure (level.getD (MerkleTree.sibling i) default :: rest)

/-- The leaf hashes of the `2^height` rows of a word. -/
def leafHashesM (height : ℕ) (word : Word) : m (List Digest) :=
  (List.range (2 ^ height)).mapM fun i ↦ H ((word i).flatMap kBytes)

/-- The Merkle root of the `2^height` rows of a word. -/
def treeRootM (height : ℕ) (word : Word) : m Digest := do
  rootOfLevelM H height (← leafHashesM H height word)

/-- The opening of a word's tree at position `q`. -/
def openingAtM (height : ℕ) (word : Word) (q : ℕ) : m Opening := do
  let path ← pathOfLevelM H height (← leafHashesM H height word) (q % 2 ^ height)
  pure ⟨word (q % 2 ^ height), path⟩

/-- The nonce search from the base `base`: the first nonce of `ns` whose digest passes. -/
def searchM (bits : ℕ) (base : Digest) : List ℕ → m (Option E)
  | [] => pure none
  | n :: ns => do
    let d ← H (digestBytes base ++ blockOf (nonceOf n) 4)
    if powOk bits (nonceOf n) d then pure (some (nonceOf n)) else searchM bits base ns

/-- The proof-of-work search: at `bits = 0` the nonce `0`; otherwise the base, then the first
nonce below `fuel` that passes. -/
def findNonceM (bits : ℕ) (cv : Digest) (fuel : ℕ) : m (Option E) :=
  if bits = 0 then pure (some (nonceOf 0)) else do
    searchM H bits (← H (digestBytes cv ++ blockOf 0 3)) (List.range fuel)

/-- The honest prover from a history `h` at chain state `cv` (`proveFrom`). -/
def proveFromM (S : Strategy) (fuel : ℕ) {α : Type} :
    Prog α → Digest → List Ev → m (Option (List E × List Opening))
  | .ret _, _, _ => pure (some ([], []))
  | .fail, _, _ => pure (some ([], []))
  | .read k, cv, h => do
    let cv' ← H (digestBytes cv ++ blockOf (S.msg h) 1)
    let r ← proveFromM S fuel (k (S.msg h)) cv' (h ++ [Ev.read (S.msg h)])
    pure (r.map fun t ↦ (S.msg h :: t.1, t.2))
  | .sample k, cv, h => do
    let cv' ← H (digestBytes cv ++ blockOf 0 2)
    proveFromM S fuel (k (challengeOf cv')) cv' (h ++ [Ev.sample (challengeOf cv')])
  | .grind bits k, cv, h => do
    match ← findNonceM H bits cv fuel with
    | none => pure none
    | some n => do
      let cv' ← H (digestBytes cv ++ blockOf n 4)
      let r ← proveFromM S fuel k cv' (h ++ [Ev.grind bits])
      pure (r.map fun t ↦ (n :: t.1, t.2))
  | .commit ht w k, cv, h => do
    let root ← treeRootM H ht (S.word h)
    let cv0 ← H (digestBytes cv ++ blockOf (digestScalars root).1 1)
    let cv1 ← H (digestBytes cv0 ++ blockOf (digestScalars root).2 1)
    let r ← proveFromM S fuel k cv1 (h ++ [Ev.commit ht w (S.word h)])
    pure (r.map fun t ↦ ((digestScalars root).1 :: (digestScalars root).2 :: t.1, t.2))
  | .query i ps k, cv, h => match (commits h)[i]? with
    | none => pure (some ([], []))
    | some (ht, _, word) => do
      let os ← ps.mapM (openingAtM H ht word)
      let r ← proveFromM S fuel (k (ps.map fun q ↦ word (q % 2 ^ ht))) cv
        (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))])
      pure (r.map fun t ↦ (t.1, os ++ t.2))

/-- **The honest prover**, with the hash in any monad (`prove`). -/
def proveM (P : Prog Bool) (S : Strategy) (seed : Digest) (fuel : ℕ) : m (Option Proof) := do
  let r ← proveFromM H S fuel P seed []
  pure (r.map fun t ↦ ⟨t.1, t.2⟩)

end ProverM

/-! ## The `Id` instance is the pure prover -/

section Pure

variable (H : Bytes → Digest)

theorem parentsM_id (level : List Digest) (n : ℕ) :
    parentsM (m := Id) H level n = (List.range n).map fun j ↦
      H (digestBytes (level.getD (2 * j) default) ++
        digestBytes (level.getD (2 * j + 1) default)) := by
  simp only [parentsM]
  exact List.idRun_mapM

/-- The parents of a level, as lists. -/
theorem parentsM_id_toList {k : ℕ} (level : Vector Digest (2 ^ (k + 1))) :
    parentsM (m := Id) H level.toList (2 ^ k) =
      (MerkleTree.parents (nodeHash H) level).toList := by
  rw [parentsM_id]
  refine List.ext_getElem (by simp) fun j h1 h2 ↦ ?_
  simp only [List.length_map, List.length_range] at h1
  have hj1 : 2 * j < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  have hj2 : 2 * j + 1 < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  simp only [List.getElem_map, List.getElem_range, Vector.getElem_toList,
    MerkleTree.getElem_parents _ _ _ h1, nodeHash]
  rw [List.getD_eq_getElem _ _ (by simpa using hj1), List.getD_eq_getElem _ _ (by simpa using hj2)]
  simp

theorem rootOfLevelM_id :
    ∀ (k : ℕ) (level : Vector Digest (2 ^ k)),
      rootOfLevelM (m := Id) H k level.toList = MerkleTree.rootOfLevel (nodeHash H) k level
  | 0, level => by
    simp only [rootOfLevelM, MerkleTree.rootOfLevel]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp only [Vector.getElem_toList]
    rfl
  | k + 1, level => by
    simp only [rootOfLevelM, MerkleTree.rootOfLevel]
    show rootOfLevelM (m := Id) H k (parentsM (m := Id) H level.toList (2 ^ k)) = _
    rw [parentsM_id_toList, rootOfLevelM_id k]

theorem pathOfLevelM_id :
    ∀ (k : ℕ) (level : Vector Digest (2 ^ k)) (i : Fin (2 ^ k)),
      pathOfLevelM (m := Id) H k level.toList i =
        MerkleTree.pathOfLevel (nodeHash H) k level i
  | 0, _, _ => rfl
  | k + 1, level, i => by
    simp only [pathOfLevelM, MerkleTree.pathOfLevel]
    show (level.toList.getD (MerkleTree.sibling i) default ::
      pathOfLevelM (m := Id) H k (parentsM (m := Id) H level.toList (2 ^ k)) (i / 2)) = _
    rw [parentsM_id_toList, ← pathOfLevelM_id k _ ⟨i.val / 2, MerkleTree.div_two_lt i.isLt⟩,
      List.getD_eq_getElem _ _ (by simpa using MerkleTree.sibling_lt i.isLt)]
    simp

theorem leafHashesM_id (height : ℕ) (word : Word) :
    leafHashesM (m := Id) H height word = ((leavesOf height word).map (leafHash H)).toList := by
  simp only [leafHashesM]
  change Id.run (List.mapM _ _) = _
  rw [List.idRun_mapM]
  refine List.ext_getElem (by simp) fun j h1 h2 ↦ ?_
  simp [leavesOf, leafHash]
  rfl

theorem treeRootM_id (height : ℕ) (word : Word) :
    treeRootM (m := Id) H height word = treeRoot H height word := by
  show rootOfLevelM (m := Id) H height (leafHashesM (m := Id) H height word) = _
  rw [leafHashesM_id, rootOfLevelM_id]
  rfl

theorem openingAtM_id (height : ℕ) (word : Word) (q : ℕ) :
    openingAtM (m := Id) H height word q = openingAt H height word q := by
  show (⟨word (q % 2 ^ height), pathOfLevelM (m := Id) H height
    (leafHashesM (m := Id) H height word) (q % 2 ^ height)⟩ : Opening) = _
  rw [leafHashesM_id]
  have := pathOfLevelM_id H height ((leavesOf height word).map (leafHash H))
    ⟨q % 2 ^ height, Nat.mod_lt _ (Nat.two_pow_pos height)⟩
  simp only at this
  rw [this]
  rfl

theorem searchM_id (bits : ℕ) (cv : Digest) :
    ∀ ns : List ℕ, searchM (m := Id) H bits (H (digestBytes cv ++ blockOf 0 3)) ns =
      (ns.find? fun n ↦ powOk bits (nonceOf n) (powDigest H cv (nonceOf n))).map nonceOf
  | [] => rfl
  | n :: ns => by
    simp only [searchM, List.find?_cons]
    show (if powOk bits (nonceOf n) (powDigest H cv (nonceOf n)) then _ else _) = _
    split <;> rename_i hp
    · simp only [hp, Option.map_some]; rfl
    · simp only [hp]; exact searchM_id bits cv ns

theorem findNonceM_id (bits : ℕ) (cv : Digest) (fuel : ℕ) :
    findNonceM (m := Id) H bits cv fuel = findNonce H bits cv fuel := by
  unfold findNonceM findNonce
  split
  · rfl
  · exact searchM_id H bits cv _

theorem proveFromM_id (S : Strategy) (fuel : ℕ) {α : Type} :
    ∀ (p : Prog α) (cv : Digest) (h : List Ev),
      proveFromM (m := Id) H S fuel p cv h = proveFrom H S fuel p cv h
  | .ret _, _, _ => rfl
  | .fail, _, _ => rfl
  | .read k, cv, h => by
    simp only [proveFromM, proveFrom]
    rw [← proveFromM_id S fuel]
    rfl
  | .sample k, cv, h => by
    simp only [proveFromM, proveFrom]
    rw [← proveFromM_id S fuel]
    rfl
  | .grind bits k, cv, h => by
    simp only [proveFromM, proveFrom]
    show (match findNonceM (m := Id) H bits cv fuel with
      | none => _ | some n => _) = _
    rw [findNonceM_id]
    cases findNonce H bits cv fuel
    · rfl
    · show Option.map _ (proveFromM (m := Id) H S fuel k _ _) =
        Option.map _ (proveFrom H S fuel k _ _)
      rw [proveFromM_id S fuel]
  | .commit ht w k, cv, h => by
    simp only [proveFromM, proveFrom]
    show (proveFromM (m := Id) H S fuel k _ _).map _ = _
    rw [treeRootM_id, proveFromM_id S fuel]
  | .query i ps k, cv, h => by
    simp only [proveFromM, proveFrom]
    rcases (commits h)[i]? with _ | ⟨ht, w, word⟩
    · rfl
    · show (proveFromM (m := Id) H S fuel _ cv _).map
        (fun t ↦ (t.1, Id.run (ps.mapM (openingAtM (m := Id) H ht word)) ++ t.2)) = _
      rw [List.idRun_mapM, proveFromM_id S fuel]
      simp only [Id.run, openingAtM_id]

/-- **The `Id` instance is the honest prover.** -/
theorem proveM_id (P : Prog Bool) (S : Strategy) (seed : Digest) (fuel : ℕ) :
    proveM (m := Id) H P S seed fuel = prove H P S seed fuel := by
  show (proveFromM (m := Id) H S fuel P seed []).map _ = _
  rw [proveFromM_id]
  rfl

end Pure

/-! ## Simulation commutes with the prover -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl HashSpec r)

theorem simulateQ_mapM {α β : Type} (f : α → OracleComp HashSpec β) :
    ∀ l : List α, simulateQ impl (l.mapM f) = l.mapM fun a ↦ simulateQ impl (f a)
  | [] => by simp
  | a :: l => by
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure]
    congr 1; funext b; rw [simulateQ_mapM f l]

theorem simulateQ_parentsM (level : List Digest) (n : ℕ) :
    simulateQ impl (parentsM queryH level n) = parentsM (fun x ↦ impl x) level n := by
  simp only [parentsM, simulateQ_mapM, simulateQ_queryH]

theorem simulateQ_rootOfLevelM :
    ∀ (k : ℕ) (level : List Digest),
      simulateQ impl (rootOfLevelM queryH k level) = rootOfLevelM (fun x ↦ impl x) k level
  | 0, _ => by simp [rootOfLevelM]
  | k + 1, level => by
    simp only [rootOfLevelM, simulateQ_bind, simulateQ_parentsM]
    congr 1; funext up; exact simulateQ_rootOfLevelM k up

theorem simulateQ_pathOfLevelM :
    ∀ (k : ℕ) (level : List Digest) (i : ℕ),
      simulateQ impl (pathOfLevelM queryH k level i) = pathOfLevelM (fun x ↦ impl x) k level i
  | 0, _, _ => by simp [pathOfLevelM]
  | k + 1, level, i => by
    simp only [pathOfLevelM, simulateQ_bind, simulateQ_parentsM, simulateQ_pure]
    congr 1; funext up; rw [simulateQ_pathOfLevelM k up]

theorem simulateQ_leafHashesM (height : ℕ) (word : Word) :
    simulateQ impl (leafHashesM queryH height word) = leafHashesM (fun x ↦ impl x) height word := by
  simp only [leafHashesM, simulateQ_mapM, simulateQ_queryH]

theorem simulateQ_treeRootM (height : ℕ) (word : Word) :
    simulateQ impl (treeRootM queryH height word) = treeRootM (fun x ↦ impl x) height word := by
  simp only [treeRootM, simulateQ_bind, simulateQ_leafHashesM, simulateQ_rootOfLevelM]

theorem simulateQ_openingAtM (height : ℕ) (word : Word) (q : ℕ) :
    simulateQ impl (openingAtM queryH height word q) =
      openingAtM (fun x ↦ impl x) height word q := by
  simp only [openingAtM, simulateQ_bind, simulateQ_leafHashesM, simulateQ_pathOfLevelM,
    simulateQ_pure]

theorem simulateQ_searchM (bits : ℕ) (base : Digest) :
    ∀ ns : List ℕ, simulateQ impl (searchM queryH bits base ns) =
      searchM (fun x ↦ impl x) bits base ns
  | [] => by simp [searchM]
  | n :: ns => by
    simp only [searchM, simulateQ_bind, simulateQ_queryH]
    congr 1; funext d
    split
    · simp
    · exact simulateQ_searchM bits base ns

theorem simulateQ_findNonceM (bits : ℕ) (cv : Digest) (fuel : ℕ) :
    simulateQ impl (findNonceM queryH bits cv fuel) = findNonceM (fun x ↦ impl x) bits cv fuel := by
  unfold findNonceM
  split
  · simp
  · simp only [simulateQ_bind, simulateQ_queryH, simulateQ_searchM]

theorem simulateQ_proveFromM (S : Strategy) (fuel : ℕ) {α : Type} :
    ∀ (p : Prog α) (cv : Digest) (h : List Ev),
      simulateQ impl (proveFromM queryH S fuel p cv h) =
        proveFromM (fun x ↦ impl x) S fuel p cv h
  | .ret _, _, _ => by simp [proveFromM]
  | .fail, _, _ => by simp [proveFromM]
  | .read k, cv, h => by
    simp only [proveFromM, simulateQ_bind, simulateQ_queryH, simulateQ_pure]
    congr 1; funext cv'; rw [simulateQ_proveFromM S fuel]
  | .sample k, cv, h => by
    simp only [proveFromM, simulateQ_bind, simulateQ_queryH]
    congr 1; funext cv'; exact simulateQ_proveFromM S fuel _ _ _
  | .grind bits k, cv, h => by
    simp only [proveFromM, simulateQ_bind, simulateQ_findNonceM]
    congr 1; funext o
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_queryH, simulateQ_pure]
      congr 1; funext cv'; rw [simulateQ_proveFromM S fuel]
  | .commit ht w k, cv, h => by
    simp only [proveFromM, simulateQ_bind, simulateQ_treeRootM, simulateQ_queryH,
      simulateQ_pure]
    congr 1; funext root; congr 1; funext cv0; congr 1; funext cv1
    rw [simulateQ_proveFromM S fuel]
  | .query i ps k, cv, h => by
    simp only [proveFromM]
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_mapM, simulateQ_openingAtM, simulateQ_pure]
      congr 1; funext os; rw [simulateQ_proveFromM S fuel]

/-- **The prover commutes with simulation.** -/
theorem simulateQ_proveM (P : Prog Bool) (S : Strategy) (seed : Digest) (fuel : ℕ) :
    simulateQ impl (proveM queryH P S seed fuel) = proveM (fun x ↦ impl x) P S seed fuel := by
  simp only [proveM, simulateQ_bind, simulateQ_proveFromM, simulateQ_pure]

end Commute

/-! ## From a log's answers to a hash function -/

/-- **From the log to a hash function.** A computation that returns `r` when every query is
answered by the log `ℓ` returns `r` when every query is answered by a hash function that agrees
with the log. -/
theorem simulateQ_id_of_look {β : Type} (ℓ : Log) (H : Bytes → Digest)
    (hH : ∀ x u, look ℓ x = some u → H x = u) (oa : OracleComp HashSpec β) :
    ∀ r : β, simulateQ (lookImpl ℓ) oa = some r →
      simulateQ (fun x ↦ (pure (H x) : Id Digest)) oa = r := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro r h
    simp only [simulateQ_pure] at h ⊢
    exact Option.some.inj h
  | query_bind t mx ih =>
    intro r h
    rw [simulateQ_query_bind] at h ⊢
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id] at h ⊢
    change (look ℓ t).bind (fun u ↦ simulateQ (lookImpl ℓ) (mx u)) = some r at h
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    change simulateQ (fun x ↦ (pure (H x) : Id Digest)) (mx (H t)) = r
    rw [hH t u hu]
    exact ih u r h

/-! ## The prover's queries -/

section Queries

theorem isTotalQueryBound_mapM {α β : Type} (f : α → OracleComp HashSpec β) (c : ℕ)
    (hf : ∀ a, IsTotalQueryBound (f a) c) :
    ∀ l : List α, IsTotalQueryBound (l.mapM f) (l.length * c)
  | [] => trivial
  | a :: l => by
    simp only [List.mapM_cons, List.length_cons]
    rw [show (l.length + 1) * c = c + (l.length * c + 0) by ring]
    exact isTotalQueryBound_bind (hf a) fun _ ↦ isTotalQueryBound_bind
      (isTotalQueryBound_mapM f c hf l) fun _ ↦ isTotalQueryBound_pure' _ 0

theorem isTotalQueryBound_parentsM (level : List Digest) (n : ℕ) :
    IsTotalQueryBound (parentsM queryH level n) n := by
  have := isTotalQueryBound_mapM (β := Digest) (fun j : ℕ ↦ queryH (digestBytes
    (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default))) 1
    (fun _ ↦ isTotalQueryBound_queryH_bind (f := pure) _ fun _ ↦ isTotalQueryBound_pure' _ 0
      |>.mono (by simp)) (List.range n)
  simpa [parentsM, queryH] using this

theorem isTotalQueryBound_rootOfLevelM :
    ∀ (k : ℕ) (level : List Digest), IsTotalQueryBound (rootOfLevelM queryH k level) (2 ^ k)
  | 0, _ => trivial
  | k + 1, level => by
    simp only [rootOfLevelM]
    rw [show 2 ^ (k + 1) = 2 ^ k + 2 ^ k by ring]
    exact isTotalQueryBound_bind (isTotalQueryBound_parentsM level _) fun up ↦
      isTotalQueryBound_rootOfLevelM k up

theorem isTotalQueryBound_pathOfLevelM :
    ∀ (k : ℕ) (level : List Digest) (i : ℕ),
      IsTotalQueryBound (pathOfLevelM queryH k level i) (2 ^ k)
  | 0, _, _ => trivial
  | k + 1, level, i => by
    simp only [pathOfLevelM]
    rw [show 2 ^ (k + 1) = 2 ^ k + (2 ^ k + 0) by ring]
    exact isTotalQueryBound_bind (isTotalQueryBound_parentsM level _) fun up ↦
      isTotalQueryBound_bind (isTotalQueryBound_pathOfLevelM k up _) fun _ ↦
        isTotalQueryBound_pure' _ 0

theorem isTotalQueryBound_leafHashesM (height : ℕ) (word : Word) :
    IsTotalQueryBound (leafHashesM queryH height word) (2 ^ height) := by
  have := isTotalQueryBound_mapM (β := Digest) (fun i : ℕ ↦ queryH ((word i).flatMap kBytes)) 1
    (fun _ ↦ isTotalQueryBound_queryH_bind (f := pure) _ fun _ ↦ isTotalQueryBound_pure' _ 0
      |>.mono (by simp)) (List.range (2 ^ height))
  simpa [leafHashesM, queryH] using this

theorem isTotalQueryBound_treeRootM (height : ℕ) (word : Word) :
    IsTotalQueryBound (treeRootM queryH height word) (2 ^ (height + 1)) := by
  unfold treeRootM
  rw [show 2 ^ (height + 1) = 2 ^ height + 2 ^ height by ring]
  exact isTotalQueryBound_bind (isTotalQueryBound_leafHashesM height word) fun l ↦
    isTotalQueryBound_rootOfLevelM height l

theorem isTotalQueryBound_openingAtM (height : ℕ) (word : Word) (q : ℕ) :
    IsTotalQueryBound (openingAtM queryH height word q) (2 ^ (height + 1)) := by
  unfold openingAtM
  rw [show 2 ^ (height + 1) = 2 ^ height + (2 ^ height + 0) by ring]
  exact isTotalQueryBound_bind (isTotalQueryBound_leafHashesM height word) fun l ↦
    isTotalQueryBound_bind (isTotalQueryBound_pathOfLevelM height l _) fun _ ↦
      isTotalQueryBound_pure' _ 0

theorem isTotalQueryBound_searchM (bits : ℕ) (base : Digest) :
    ∀ ns : List ℕ, IsTotalQueryBound (searchM queryH bits base ns) ns.length
  | [] => trivial
  | n :: ns => by
    simp only [searchM, List.length_cons]
    refine isTotalQueryBound_queryH_bind _ fun d ↦ ?_
    split
    · trivial
    · exact isTotalQueryBound_searchM bits base ns

theorem isTotalQueryBound_findNonceM (bits : ℕ) (cv : Digest) (fuel : ℕ) :
    IsTotalQueryBound (findNonceM queryH bits cv fuel) (fuel + 1) := by
  unfold findNonceM
  split
  · trivial
  · exact isTotalQueryBound_queryH_bind _ fun base ↦ by
      simpa using isTotalQueryBound_searchM bits base (List.range fuel)

/-- The query cost of one unit of a program's cost: an opening or a commitment rebuilds a tree
of height at most `height`, a proof of work searches `fuel` nonces. -/
def proverFactor (height fuel : ℕ) : ℕ := 2 ^ (height + 1) + fuel + 1

theorem one_le_proverFactor (height fuel : ℕ) : 1 ≤ proverFactor height fuel :=
  Nat.le_add_left 1 _

theorem fuel_lt_proverFactor (height fuel : ℕ) : fuel + 1 ≤ proverFactor height fuel := by
  unfold proverFactor; exact Nat.add_le_add_right (Nat.le_add_left _ _) 1

theorem pow_lt_proverFactor (height fuel : ℕ) : 2 ^ (height + 1) + 1 ≤ proverFactor height fuel := by
  unfold proverFactor; exact Nat.add_le_add_right (Nat.le_add_right _ _) 1

/-- **The prover's queries.** From a history whose commitments have height at most `height`, the
prover runs a program of cost `n` (`Prog.Costs`) with at most `n · proverFactor height fuel`
queries. -/
theorem isTotalQueryBound_proveFromM (S : Strategy) (fuel height : ℕ) {α : Type} :
    ∀ (p : Prog α) (cv : Digest) (h : List Ev) (n : ℕ) (Q : α → Prop), p.Costs height n Q →
      (∀ c ∈ commits h, c.1 ≤ height) →
      IsTotalQueryBound (proveFromM queryH S fuel p cv h) (n * proverFactor height fuel)
  | .ret _, _, _, _, _, _, _ => trivial
  | .fail, _, _, _, _, _, _ => trivial
  | .read k, cv, h, n, Q, hp, hs => by
    simp only [proveFromM]
    have hs' : ∀ c ∈ commits (h ++ [Ev.read (S.msg h)]), c.1 ≤ height := by
      simpa [commits_append, commits] using hs
    refine (isTotalQueryBound_queryH_bind (n := (n - 1) * proverFactor height fuel + 0) _
      fun cv' ↦ isTotalQueryBound_bind (isTotalQueryBound_proveFromM S fuel height _ cv'
        (h ++ [Ev.read (S.msg h)]) (n - 1) Q (hp.2 _) hs') fun _ ↦
          isTotalQueryBound_pure' _ 0).mono ?_
    have h1 := hp.1
    have hF := one_le_proverFactor height fuel
    generalize proverFactor height fuel = F at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul, one_mul]
    omega
  | .sample k, cv, h, n, Q, hp, hs => by
    simp only [proveFromM]
    refine (isTotalQueryBound_queryH_bind (n := (n - 1) * proverFactor height fuel) _
      fun cv' ↦ isTotalQueryBound_proveFromM S fuel height _ cv'
        (h ++ [Ev.sample (challengeOf cv')]) (n - 1) Q (hp.2 _)
          (by simpa [commits_append, commits] using hs)).mono ?_
    have h1 := hp.1
    have hF := one_le_proverFactor height fuel
    generalize proverFactor height fuel = F at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul, one_mul]
    omega
  | .grind bits k, cv, h, n, Q, hp, hs => by
    simp only [proveFromM]
    have hs' : ∀ c ∈ commits (h ++ [Ev.grind bits]), c.1 ≤ height := by
      simpa [commits_append, commits] using hs
    refine (isTotalQueryBound_bind (isTotalQueryBound_findNonceM bits cv fuel)
      (n₂ := (n - 3) * proverFactor height fuel + 0 + 1) fun o ↦ ?_).mono ?_
    · split
      · trivial
      · exact isTotalQueryBound_queryH_bind (n := (n - 3) * proverFactor height fuel + 0) _
          fun cv' ↦ isTotalQueryBound_bind
          (isTotalQueryBound_proveFromM S fuel height k cv' (h ++ [Ev.grind bits]) (n - 3) Q
            hp.2 hs') fun _ ↦ isTotalQueryBound_pure' _ 0
    · have h1 := hp.1
      have hF := fuel_lt_proverFactor height fuel
      generalize proverFactor height fuel = F at *
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 3 := ⟨n - 3, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_mul]
      omega
  | .commit ht w k, cv, h, n, Q, hp, hs => by
    simp only [proveFromM]
    have hs' : ∀ c ∈ commits (h ++ [Ev.commit ht w (S.word h)]), c.1 ≤ height := by
      simp only [commits_append, commits, List.mem_append, List.mem_singleton]
      rintro c (hc | rfl)
      · exact hs c hc
      · exact hp.1
    refine (isTotalQueryBound_bind (isTotalQueryBound_treeRootM ht (S.word h))
      (n₂ := (n - 2) * proverFactor height fuel + 0 + 1 + 1) fun root ↦
        isTotalQueryBound_queryH_bind (n := (n - 2) * proverFactor height fuel + 0 + 1) _
          fun cv0 ↦ isTotalQueryBound_queryH_bind (n := (n - 2) * proverFactor height fuel + 0) _
            fun cv1 ↦
          isTotalQueryBound_bind (isTotalQueryBound_proveFromM S fuel height k cv1
            (h ++ [Ev.commit ht w (S.word h)]) (n - 2) Q hp.2.2 hs') fun _ ↦
              isTotalQueryBound_pure' _ 0).mono ?_
    have h1 := hp.2.1
    have h2 : 2 ^ (ht + 1) ≤ 2 ^ (height + 1) := Nat.pow_le_pow_right (by norm_num) (by
      have := hp.1; omega)
    have hF := pow_lt_proverFactor height fuel
    generalize proverFactor height fuel = F at *
    generalize 2 ^ (height + 1) = A at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul]
    omega
  | .query i ps k, cv, h, n, Q, hp, hs => by
    simp only [proveFromM]
    split
    · trivial
    · rename_i ht w word hc
      have hht : ht ≤ height := hs _ (List.mem_of_getElem? hc)
      have hs' : ∀ c ∈ commits (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))]),
          c.1 ≤ height := by
        simpa [commits_append, commits] using hs
      refine (isTotalQueryBound_bind (isTotalQueryBound_mapM _ _
        (isTotalQueryBound_openingAtM ht word) ps)
        (n₂ := (n - ps.length * (1 + height)) * proverFactor height fuel + 0) fun os ↦
          isTotalQueryBound_bind (isTotalQueryBound_proveFromM S fuel height _ cv _ _ Q (hp.2 _)
            hs') fun _ ↦ isTotalQueryBound_pure' _ 0).mono ?_
      have h1 := hp.1
      have h2 : 2 ^ (ht + 1) ≤ proverFactor height fuel :=
        (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
          ((Nat.le_succ _).trans (pow_lt_proverFactor height fuel))
      have h3 : ps.length * 2 ^ (ht + 1) ≤ ps.length * (1 + height) * proverFactor height fuel :=
        calc ps.length * 2 ^ (ht + 1) ≤ ps.length * proverFactor height fuel :=
              Nat.mul_le_mul_left _ h2
          _ ≤ ps.length * (1 + height) * proverFactor height fuel := by
              rw [mul_assoc]
              exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
      generalize proverFactor height fuel = F at *
      obtain ⟨d, hd⟩ : ∃ d, n = ps.length * (1 + height) + d :=
        ⟨n - ps.length * (1 + height), by omega⟩
      rw [hd, Nat.add_sub_cancel_left, Nat.add_mul]
      omega

/-- **The honest prover's queries**: at most `n · proverFactor height fuel` for a program of
cost `n` at `height`. -/
theorem isTotalQueryBound_proveM {P : Prog Bool} {height n : ℕ} (hP : P.CostLE height n)
    (S : Strategy) (seed : Digest) (fuel : ℕ) :
    IsTotalQueryBound (proveM queryH P S seed fuel) (n * proverFactor height fuel) := by
  unfold proveM
  rw [← Nat.add_zero (n * _)]
  exact isTotalQueryBound_bind (isTotalQueryBound_proveFromM S fuel height P seed [] n _ hP
    (by simp [commits])) fun _ ↦ isTotalQueryBound_pure' _ 0

end Queries

end
end LeanVM.Protocol.Compile
