/-
  LeanVM.Protocol.Compile.Rom.Prover

  The honest prover of a compiled verifier program with the hash in any monad: the prover of
  `LeanVM.Protocol.Compile.Prover` written so that it runs against the random oracle, with its
  `Id` instance the pure prover, its commutation with simulation, and its query bound.
-/

module

public import LeanVM.Protocol.Compile.Prover
public import LeanVM.Protocol.Compile.Cost
public import Statement.Prover.Run
public import LeanVM.Protocol.WithHash

/-!
# The honest prover against the random oracles

`proveM H F P S seed fuel` is the honest prover `prove` (`LeanVM.Protocol.Compile.Prover`) with
the hash `H : Bytes → m Digest` and the permutation `F : KState → m KState` in any monad `m`, as
the verifier `run` is. Its `Id` instance is `prove` (`proveM_id`); at `H = callKeccak256` and
`F = callKeccakF1600` it is an oracle computation, the honest prover of the random-oracle model.

It is written with the statement's pieces (`Statement/Prover/Run.lean`), so that it makes the
moves of the statement's runner `LeanVM.Prover.runFrom` (`LeanVM/Prover/Refine.lean`):

* a commitment builds its Merkle tree once, every level stored (`LeanVM.Prover.buildTreeM`), and
  the trees committed so far are carried along; an opening reads the stored tree
  (`LeanVM.Prover.Tree.opening`) and queries nothing;
* the proof-of-work search tries the nonces `0, 1, …, fuel - 1` in order, each absorbed into the
  sponge with tag `4` and a challenge squeezed (`LeanVM.Prover.powStepM`,
  `LeanVM.Prover.searchM`).

* `simulateQ_proveM`: interpreting the queries of `proveM callKeccak256 callKeccakF1600` by any implementation is
  running `proveM` with that implementation as the hash and the permutation.
* `simulateQ_id_of_look`: a computation whose run against a log's answers returns `r` returns
  `r` against every hash function and permutation that agree with the log.
* `isTotalQueryBound_proveM`: a program of cost `n` at height `h` (`VerifierProgram.CostLE`, in
  quarters) makes the prover query the oracles at most `n · (2^(h + 1) + 2 · fuel + 2)` times, after
  the seed.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open LeanVM.Prover (Tree buildTreeWithHash leafDigestsWithHash parentsWithHash levelsWithHash powStepM searchM findNonceM)
open OracleComp OracleSpec

@[expose] public section

/-! ## The prover with the hash in any monad -/

section ProverM

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- The honest prover from a history `h` at sponge `sp`, the trees of the commitments so far `cs`
(`proveFrom`): each commitment's tree built once, the openings read from it. -/
def proveFromM (S : Strategy) (fuel : ℕ) {α : Type} :
    VerifierProgram α → Sponge → List Ev → List Tree →
      m (Option (List E × List (List Opening)))
  | .ret _, _, _, _ => pure (some ([], []))
  | .fail, _, _, _ => pure (some ([], []))
  | .read k, sp, h, cs => do
    let sp' ← Compile.absorb F sp (S.msg h) dsObserve
    let r ← proveFromM S fuel (k (S.msg h)) sp' (h ++ [Ev.read (S.msg h)]) cs
    pure (r.map fun t ↦ (S.msg h :: t.1, t.2))
  | .sample k, sp, h, cs => do
    let r ← squeeze F sp
    proveFromM S fuel (k r.1) r.2 (h ++ [Ev.sample r.1]) cs
  | .grind bits k, sp, h, cs => do
    match ← findNonceM F bits sp fuel with
    | none => pure none
    | some n => do
      let r ← powStepM F sp n
      let t ← proveFromM S fuel k r.2 (h ++ [Ev.grind bits]) cs
      pure (t.map fun t ↦ (n :: t.1, t.2))
  | .commit ht w k, sp, h, cs => do
    let tree ← buildTreeWithHash H ht (S.word h)
    let sp0 ← Compile.absorb F sp (digestHalves tree.root).1 dsObserve
    let sp1 ← Compile.absorb F sp0 (digestHalves tree.root).2 dsObserve
    let r ← proveFromM S fuel k sp1 (h ++ [Ev.commit ht w (S.word h)]) (cs ++ [tree])
    pure (r.map fun t ↦ ((digestHalves tree.root).1 :: (digestHalves tree.root).2 :: t.1, t.2))
  | .query i ps k, sp, h, cs => match cs[i]? with
    | none => pure (some ([], []))
    | some tree => do
      let rows := ps.map fun q ↦ tree.word (q % 2 ^ tree.height)
      let r ← proveFromM S fuel (k rows) sp (h ++ [Ev.query rows]) cs
      pure (r.map fun t ↦ (t.1, ps.map tree.opening :: t.2))

/-- **The honest prover**, with the hash and the permutation in any monad (`prove`). -/
def proveM (P : VerifierProgram Bool) (S : Strategy) (seed : KeccakState) (fuel : ℕ) : m (Option
    Proof) := do
  let r ← proveFromM H F S fuel P ⟨seed, []⟩ [] []
  pure (r.map fun t ↦ ⟨t.1, t.2⟩)

end ProverM

/-- The statement's nonce is the prover's. -/
theorem prover_nonceOf (n : ℕ) : LeanVM.Prover.nonceOf n = nonceOf n := rfl

/-- The trees of a list of commitments, as `buildTreeM` builds them in `Id`. -/
def treesOf (H : Bytes → Digest) (cs : List (ℕ × ℕ × Word)) : List Tree :=
  cs.map fun c ↦ buildTreeWithHash (m := Id) H c.1 c.2.2

/-! ## The `Id` instance is the pure prover -/

section Pure

variable (H : Bytes → Digest) (F : KeccakState → KeccakState)

theorem toArray_getD {α : Type} (l : List α) (i : ℕ) (d : α) : l.toArray.getD i d = l.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem parentsM_id (level : Array Digest) (n : ℕ) :
    parentsWithHash (m := Id) H level n = (Array.range n).map fun j ↦
      H (digestBytes (level.getD (2 * j) default) ++
        digestBytes (level.getD (2 * j + 1) default)) :=
  Array.idRun_mapM

/-- The parents of a level, as arrays. -/
theorem parentsM_id_toArray {k : ℕ} (level : Vector Digest (2 ^ (k + 1))) :
    parentsWithHash (m := Id) H level.toArray (2 ^ k) =
      (MerkleTree.parents (nodeHash H) level).toArray := by
  rw [parentsM_id]
  refine Array.ext (by simp) fun j h1 h2 ↦ ?_
  simp only [Array.size_map, Array.size_range] at h1
  have hj1 : 2 * j < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  have hj2 : 2 * j + 1 < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  simp only [Array.getElem_map, Array.getElem_range, Vector.getElem_toArray,
    MerkleTree.getElem_parents _ _ _ h1, nodeHash]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by simpa using hj1), Array.getElem?_eq_getElem (by simpa using hj2)]
  simp

theorem levelsM_id_succ (k : ℕ) (level : Array Digest) :
    levelsWithHash (m := Id) H (k + 1) level =
      level :: levelsWithHash (m := Id) H k (parentsWithHash (m := Id) H level (2 ^ k)) := rfl

/-- The last level is the root. -/
theorem levelsM_id_root : ∀ (k : ℕ) (level : Vector Digest (2 ^ k)),
    ((levelsWithHash (m := Id) H k level.toArray).getD k #[]).getD 0 default =
      MerkleTree.rootOfLevel (nodeHash H) k level
  | 0, level => by
    show level.toArray.getD 0 default = level[0]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simp)]
    simp
  | k + 1, level => by
    rw [levelsM_id_succ, List.getD_cons_succ, parentsM_id_toArray, levelsM_id_root k]
    rfl

/-- The siblings read off the levels are the authentication path. -/
theorem levelsM_id_path : ∀ (k : ℕ) (level : Vector Digest (2 ^ k)) (i : Fin (2 ^ k)),
    (List.range k).map (fun l ↦ ((levelsWithHash (m := Id) H k level.toArray).getD l #[]).getD
      (LeanVM.Prover.sibling (i.val / 2 ^ l)) default) =
      MerkleTree.pathOfLevel (nodeHash H) k level i
  | 0, _, _ => rfl
  | k + 1, level, i => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, levelsM_id_succ,
      parentsM_id_toArray, MerkleTree.pathOfLevel]
    congr 1
    · rw [List.getD_cons_zero, pow_zero, Nat.div_one, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (by rw [Vector.size_toArray]; exact MerkleTree.sibling_lt i.isLt)]
      rfl
    · rw [← levelsM_id_path k _ ⟨i.val / 2, MerkleTree.div_two_lt i.isLt⟩]
      refine List.map_congr_left fun l _ ↦ ?_
      simp only [Function.comp, List.getD_cons_succ]
      rw [show (i : ℕ) / 2 ^ (l + 1) = (i : ℕ) / 2 / 2 ^ l by
        rw [Nat.div_div_eq_div_mul, ← pow_succ']]

theorem leafDigestsM_id (height : ℕ) (word : Word) :
    leafDigestsWithHash (m := Id) H height word = ((leavesOf height word).map (leafHash H)).toArray := by
  refine (Array.idRun_mapM).trans (Array.ext (by simp) fun j h1 h2 ↦ ?_)
  simp [leavesOf, leafHash]
  rfl

/-- **The root of the tree built once** is `treeRoot`. -/
theorem root_buildTreeM_id (height : ℕ) (word : Word) :
    (buildTreeWithHash (m := Id) H height word).root = treeRoot H height word := by
  show ((levelsWithHash (m := Id) H height (leafDigestsWithHash (m := Id) H height word)).toArray.getD height
    #[]).getD 0 default = _
  simp only [toArray_getD, leafDigestsM_id]
  rw [levelsM_id_root]
  rfl

/-- **An opening read off the tree built once** is `openingAt`. -/
theorem opening_buildTreeM_id (height : ℕ) (word : Word) (q : ℕ) :
    (buildTreeWithHash (m := Id) H height word).opening q = openingAt H height word q := by
  have e := levelsM_id_path H height ((leavesOf height word).map (leafHash H))
    ⟨q % 2 ^ height, Nat.mod_lt _ (Nat.two_pow_pos height)⟩
  show (⟨q, word (q % 2 ^ height), (List.range height).map fun l ↦
    ((levelsWithHash (m := Id) H height (leafDigestsWithHash (m := Id) H height word)).toArray.getD l #[]).getD
      (LeanVM.Prover.sibling (q % 2 ^ height / 2 ^ l)) default⟩ : Opening) =
    ⟨q, word (q % 2 ^ height), _⟩
  simp only [toArray_getD, leafDigestsM_id]
  exact congrArg _ e

theorem searchM_id (bits : ℕ) (sp : Sponge) :
    ∀ (count n : ℕ), searchM (m := Id) F bits sp n count =
      ((List.range' n count).find? fun j ↦ powOk bits (powStep F sp (nonceOf j)).1).map
        nonceOf
  | 0, _ => rfl
  | count + 1, n => by
    rw [List.range'_succ, List.find?_cons]
    show (if powOk bits (powStep F sp (nonceOf n)).1 then _ else _) = _
    split <;> rename_i hp
    · simp only [hp, Option.map_some]; rfl
    · simp only [hp]; exact searchM_id bits sp count (n + 1)

theorem findNonceM_id (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    findNonceM (m := Id) F bits sp fuel = findNonce F bits sp fuel := by
  unfold findNonceM findNonce
  rw [searchM_id, List.range_eq_range']

theorem treesOf_append (h : List Ev) (ht w : ℕ) (W : Word) :
    treesOf H (commits (h ++ [Ev.commit ht w W])) = treesOf H (commits h) ++
      ([buildTreeWithHash (m := Id) H ht W] : List Tree) := by
  simp [treesOf, commits_append, commits]

theorem treesOf_append_nil (h : List Ev) (e : Ev) (he : commits [e] = []) :
    treesOf H (commits (h ++ [e])) = treesOf H (commits h) := by
  simp [treesOf, commits_append, he]

/-- The `Id` instance from the trees of a history's commitments is `proveFrom`. -/
theorem proveFromM_id (S : Strategy) (fuel : ℕ) {α : Type} :
    ∀ (p : VerifierProgram α) (sp : Sponge) (h : List Ev),
      proveFromM (m := Id) H F S fuel p sp h (treesOf H (commits h)) = proveFrom H F S fuel p sp h
  | .ret _, _, _ => rfl
  | .fail, _, _ => rfl
  | .read k, sp, h => by
    simp only [proveFromM, proveFrom]
    rw [← proveFromM_id S fuel, treesOf_append_nil H h (Ev.read (S.msg h)) rfl]
    rfl
  | .sample k, sp, h => by
    simp only [proveFromM, proveFrom]
    rw [← proveFromM_id S fuel, treesOf_append_nil H h (Ev.sample (squeezeI F sp).1) rfl]
    rfl
  | .grind bits k, sp, h => by
    simp only [proveFromM, proveFrom]
    show (match findNonceM (m := Id) F bits sp fuel with
      | none => _ | some n => _) = _
    rw [findNonceM_id]
    cases findNonce F bits sp fuel
    · rfl
    · show Option.map _ (proveFromM (m := Id) H F S fuel k _ _ _) =
        Option.map _ (proveFrom H F S fuel k _ _)
      rw [← proveFromM_id S fuel, treesOf_append_nil H h (Ev.grind bits) rfl]
      rfl
  | .commit ht w k, sp, h => by
    simp only [proveFromM, proveFrom]
    show (proveFromM (m := Id) H F S fuel k _ _ _).map _ = _
    rw [root_buildTreeM_id, ← treesOf_append, proveFromM_id S fuel]
    rfl
  | .query i ps k, sp, h => by
    simp only [proveFromM, proveFrom]
    have hc : (treesOf H (commits h))[i]? =
        ((commits h)[i]?).map fun c ↦ buildTreeWithHash (m := Id) H c.1 c.2.2 := by
      simp [treesOf]
    rw [hc]
    rcases (commits h)[i]? with _ | ⟨ht, w, word⟩
    · rfl
    · have ho : (buildTreeWithHash (m := Id) H ht word).opening = openingAt H ht word :=
        funext (opening_buildTreeM_id H ht word)
      show (proveFromM (m := Id) H F S fuel (k (ps.map fun q ↦ word (q % 2 ^ ht))) sp
          (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))]) (treesOf H (commits h))).map
          (fun t ↦ (t.1, ps.map (buildTreeWithHash (m := Id) H ht word).opening :: t.2)) = _
      rw [ho, ← treesOf_append_nil H h (Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))) rfl,
        proveFromM_id S fuel]

/-- **The `Id` instance is the honest prover.** -/
theorem proveM_id (P : VerifierProgram Bool) (S : Strategy) (seed : KeccakState) (fuel : ℕ) :
    proveM (m := Id) H F P S seed fuel = prove H F P S seed fuel := by
  show (proveFromM (m := Id) H F S fuel P ⟨seed, []⟩ [] (treesOf H (commits []))).map _ = _
  rw [proveFromM_id]
  rfl

end Pure

/-! ## Simulation commutes with the prover -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

theorem simulateQ_mapM {α β : Type} (f : α → OracleComp KeccakCalls β) :
    ∀ l : List α, simulateQ impl (l.mapM f) = l.mapM fun a ↦ simulateQ impl (f a)
  | [] => by simp
  | a :: l => by
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure]
    congr 1; funext b; rw [simulateQ_mapM f l]

theorem simulateQ_arrayMapM {α β : Type} (f : α → OracleComp KeccakCalls β) (xs : Array α) :
    simulateQ impl (xs.mapM f) = xs.mapM fun a ↦ simulateQ impl (f a) := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList, simulateQ_map, simulateQ_mapM]

theorem simulateQ_parentsM (level : Array Digest) (n : ℕ) :
    simulateQ impl (parentsWithHash callKeccak256 level n) = parentsWithHash (implH impl) level n := by
  simp only [parentsWithHash, simulateQ_arrayMapM, simulateQ_queryH]

theorem simulateQ_levelsM :
    ∀ (k : ℕ) (level : Array Digest),
      simulateQ impl (levelsWithHash callKeccak256 k level) = levelsWithHash (implH impl) k level
  | 0, _ => by simp [levelsWithHash]
  | k + 1, level => by
    simp only [levelsWithHash, simulateQ_bind, simulateQ_parentsM, simulateQ_pure]
    congr 1; funext up; rw [simulateQ_levelsM k up]

theorem simulateQ_leafDigestsM (height : ℕ) (word : Word) :
    simulateQ impl (leafDigestsWithHash callKeccak256 height word) = leafDigestsWithHash (implH impl) height word := by
  simp only [leafDigestsWithHash, simulateQ_arrayMapM, simulateQ_queryH]

theorem simulateQ_buildTreeM (height : ℕ) (word : Word) :
    simulateQ impl (buildTreeWithHash callKeccak256 height word) = buildTreeWithHash (implH impl) height word := by
  simp only [buildTreeWithHash, simulateQ_bind, simulateQ_leafDigestsM, simulateQ_levelsM,
    simulateQ_pure]

theorem simulateQ_powStepM (sp : Sponge) (n : E) :
    simulateQ impl (powStepM callKeccakF1600 sp n) = powStepM (implF impl) sp n := by
  simp only [powStepM, simulateQ_bind, simulateQ_absorb, simulateQ_squeeze]

theorem simulateQ_searchM (bits : ℕ) (sp : Sponge) :
    ∀ (count n : ℕ), simulateQ impl (searchM callKeccakF1600 bits sp n count) =
      searchM (implF impl) bits sp n count
  | 0, _ => by simp [searchM]
  | count + 1, n => by
    simp only [searchM, simulateQ_bind, simulateQ_powStepM]
    congr 1; funext r
    split
    · simp
    · exact simulateQ_searchM bits sp count (n + 1)

theorem simulateQ_findNonceM (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    simulateQ impl (findNonceM callKeccakF1600 bits sp fuel) = findNonceM (implF impl) bits sp fuel := by
  unfold findNonceM
  exact simulateQ_searchM impl bits sp _ _

theorem simulateQ_proveFromM (S : Strategy) (fuel : ℕ) {α : Type} :
    ∀ (p : VerifierProgram α) (sp : Sponge) (h : List Ev) (cs : List Tree),
      simulateQ impl (proveFromM callKeccak256 callKeccakF1600 S fuel p sp h cs) =
        proveFromM (implH impl) (implF impl) S fuel p sp h cs
  | .ret _, _, _, _ => by simp [proveFromM]
  | .fail, _, _, _ => by simp [proveFromM]
  | .read k, sp, h, cs => by
    simp only [proveFromM, simulateQ_bind, simulateQ_absorb, simulateQ_pure]
    congr 1; funext sp'; rw [simulateQ_proveFromM S fuel]
  | .sample k, sp, h, cs => by
    simp only [proveFromM, simulateQ_bind, simulateQ_squeeze]
    congr 1; funext r; exact simulateQ_proveFromM S fuel _ _ _ _
  | .grind bits k, sp, h, cs => by
    simp only [proveFromM, simulateQ_bind, simulateQ_findNonceM]
    congr 1; funext o
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_powStepM, simulateQ_pure]
      congr 1; funext r; rw [simulateQ_proveFromM S fuel]
  | .commit ht w k, sp, h, cs => by
    simp only [proveFromM, simulateQ_bind, simulateQ_buildTreeM, simulateQ_absorb,
      simulateQ_pure]
    congr 1; funext tree; congr 1; funext sp0; congr 1; funext sp1
    rw [simulateQ_proveFromM S fuel]
  | .query i ps k, sp, h, cs => by
    simp only [proveFromM]
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_pure]
      rw [simulateQ_proveFromM S fuel]

/-- **The prover commutes with simulation.** -/
theorem simulateQ_proveM (P : VerifierProgram Bool) (S : Strategy) (seed : KeccakState) (fuel : ℕ) :
    simulateQ impl (proveM callKeccak256 callKeccakF1600 P S seed fuel) =
      proveM (implH impl) (implF impl) P S seed fuel := by
  simp only [proveM, simulateQ_bind, simulateQ_proveFromM, simulateQ_pure]

end Commute

/-! ## From a log's answers to a hash function and a permutation -/

/-- A hash function and a permutation, as an implementation of the oracles in `Id`. -/
def totalImpl (H : Bytes → Digest) (F : KeccakState → KeccakState) : QueryImpl KeccakCalls Id
  | .inl x => H x
  | .inr s => F s

theorem implH_totalImpl (H : Bytes → Digest) (F : KeccakState → KeccakState) :
    implH (totalImpl H F) = H := rfl

theorem implF_totalImpl (H : Bytes → Digest) (F : KeccakState → KeccakState) :
    implF (totalImpl H F) = F := rfl

/-- **From the log to a hash function and a permutation.** A computation that returns `r` when
every query is answered by the log `ℓ` returns `r` when every query is answered by a hash
function and a permutation that agree with the log. -/
theorem simulateQ_id_of_look {β : Type} (ℓ : Log) (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (hH : ∀ x u, lookH ℓ x = some u → H x = u) (hF : ∀ s u, lookF ℓ s = some u → F s = u)
    (oa : OracleComp KeccakCalls β) :
    ∀ r : β, simulateQ (lookImpl ℓ) oa = some r → simulateQ (totalImpl H F) oa = r := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro r h
    simp only [simulateQ_pure] at h ⊢
    exact Option.some.inj h
  | query_bind t mx ih =>
    intro r h
    rw [simulateQ_query_bind] at h ⊢
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id] at h ⊢
    change (logLookup ℓ t).bind (fun u ↦ simulateQ (lookImpl ℓ) (mx u)) = some r at h
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    change simulateQ (totalImpl H F) (mx (totalImpl H F t)) = r
    have ht : totalImpl H F t = u := by
      rcases t with x | s
      · exact hH x u hu
      · exact hF s u hu
    rw [ht]
    exact ih u r h

/-! ## The prover's queries -/

section Queries

theorem isTotalQueryBound_mapM {α β : Type} (f : α → OracleComp KeccakCalls β) (c : ℕ)
    (hf : ∀ a, IsTotalQueryBound (f a) c) :
    ∀ l : List α, IsTotalQueryBound (l.mapM f) (l.length * c)
  | [] => trivial
  | a :: l => by
    simp only [List.mapM_cons, List.length_cons]
    rw [show (l.length + 1) * c = c + (l.length * c + 0) by ring]
    exact isTotalQueryBound_bind (hf a) fun _ ↦ isTotalQueryBound_bind
      (isTotalQueryBound_mapM f c hf l) fun _ ↦ isTotalQueryBound_pure' _ 0


theorem isTotalQueryBound_arrayMapM {α β : Type} (f : α → OracleComp KeccakCalls β) (c : ℕ)
    (hf : ∀ a, IsTotalQueryBound (f a) c) (xs : Array α) :
    IsTotalQueryBound (xs.mapM f) (xs.size * c) := by
  rw [Array.mapM_eq_mapM_toList, map_eq_bind_pure_comp, ← Array.length_toList,
    ← Nat.add_zero (xs.toList.length * c)]
  exact isTotalQueryBound_bind (isTotalQueryBound_mapM f c hf xs.toList) fun _ ↦
    isTotalQueryBound_pure' _ 0

theorem isTotalQueryBound_parentsM (level : Array Digest) (n : ℕ) :
    IsTotalQueryBound (parentsWithHash callKeccak256 level n) n := by
  have := isTotalQueryBound_arrayMapM (β := Digest) (fun j : ℕ ↦ callKeccak256 (digestBytes
    (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default))) 1
    (fun _ ↦ isTotalQueryBound_queryH_bind (f := pure) _ fun _ ↦ isTotalQueryBound_pure' _ 0
      |>.mono (by simp)) (Array.range n)
  simpa [parentsWithHash, callKeccak256] using this

theorem isTotalQueryBound_levelsM :
    ∀ (k : ℕ) (level : Array Digest), IsTotalQueryBound (levelsWithHash callKeccak256 k level) (2 ^ k)
  | 0, _ => trivial
  | k + 1, level => by
    simp only [levelsWithHash]
    rw [show 2 ^ (k + 1) = 2 ^ k + (2 ^ k + 0) by ring]
    exact isTotalQueryBound_bind (isTotalQueryBound_parentsM level _) fun up ↦
      isTotalQueryBound_bind (isTotalQueryBound_levelsM k up) fun _ ↦ isTotalQueryBound_pure' _ 0

theorem isTotalQueryBound_leafDigestsM (height : ℕ) (word : Word) :
    IsTotalQueryBound (leafDigestsWithHash callKeccak256 height word) (2 ^ height) := by
  have := isTotalQueryBound_arrayMapM (β := Digest) (fun i : ℕ ↦ callKeccak256 ((word i).flatMap K.toBytes))
    1 (fun _ ↦ isTotalQueryBound_queryH_bind (f := pure) _ fun _ ↦ isTotalQueryBound_pure' _ 0
      |>.mono (by simp)) (Array.range (2 ^ height))
  simpa [leafDigestsWithHash, callKeccak256] using this

/-- **A commitment's tree is built with at most `2^(height + 1)` queries.** -/
theorem isTotalQueryBound_buildTreeM (height : ℕ) (word : Word) :
    IsTotalQueryBound (buildTreeWithHash callKeccak256 height word) (2 ^ (height + 1)) := by
  unfold buildTreeWithHash
  rw [show 2 ^ (height + 1) = 2 ^ height + (2 ^ height + 0) by ring]
  exact isTotalQueryBound_bind (isTotalQueryBound_leafDigestsM height word) fun l ↦
    isTotalQueryBound_bind (isTotalQueryBound_levelsM height l) fun _ ↦
      isTotalQueryBound_pure' _ 0

/-- An absorption queries at most once. -/
theorem isTotalQueryBound_absorb_le {β : Type} (sp : Sponge) (x : E) (tag : ℕ)
    {g : Sponge → OracleComp KeccakCalls β} {n : ℕ} (hg : ∀ sp', IsTotalQueryBound (g sp') n) :
    IsTotalQueryBound (Compile.absorb callKeccakF1600 sp x tag >>= g) (n + 1) := by
  rw [absorb_bind]
  split
  · exact isTotalQueryBound_queryF_bind _ fun st ↦ hg _
  · exact (hg _).mono (Nat.le_succ n)

/-- A squeeze queries once. -/
theorem isTotalQueryBound_squeeze_le {β : Type} (sp : Sponge)
    {g : E × Sponge → OracleComp KeccakCalls β} {n : ℕ} (hg : ∀ r, IsTotalQueryBound (g r) n) :
    IsTotalQueryBound (squeeze callKeccakF1600 sp >>= g) (n + 1) := by
  rw [squeeze_bind]
  exact isTotalQueryBound_queryF_bind _ fun st ↦ hg _

/-- A proof-of-work step queries at most twice. -/
theorem isTotalQueryBound_powStepM_le {β : Type} (sp : Sponge) (n : E)
    {g : E × Sponge → OracleComp KeccakCalls β} {c : ℕ} (hg : ∀ r, IsTotalQueryBound (g r) c) :
    IsTotalQueryBound (powStepM callKeccakF1600 sp n >>= g) (c + 2) := by
  simp only [powStepM, bind_assoc]
  exact isTotalQueryBound_absorb_le _ _ _ fun sp' ↦ isTotalQueryBound_squeeze_le _ hg

theorem isTotalQueryBound_searchM (bits : ℕ) (sp : Sponge) :
    ∀ (count n : ℕ), IsTotalQueryBound (searchM callKeccakF1600 bits sp n count) (2 * count)
  | 0, _ => trivial
  | count + 1, n => by
    simp only [searchM]
    rw [show 2 * (count + 1) = 2 * count + 2 by ring]
    refine isTotalQueryBound_powStepM_le _ _ fun r ↦ ?_
    split
    · trivial
    · exact isTotalQueryBound_searchM bits sp count (n + 1)

theorem isTotalQueryBound_findNonceM (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    IsTotalQueryBound (findNonceM callKeccakF1600 bits sp fuel) (2 * fuel) := by
  unfold findNonceM
  exact isTotalQueryBound_searchM bits sp fuel 0

/-- The query cost of one quarter of a program's cost: a commitment builds a
tree of height at most `height`, a proof of work searches `fuel` nonces at two queries each. -/
def proverFactor (height fuel : ℕ) : ℕ := 2 ^ (height + 1) + 2 * fuel + 2

theorem one_le_proverFactor (height fuel : ℕ) : 1 ≤ proverFactor height fuel := by
  unfold proverFactor; exact Nat.succ_le_of_lt (by positivity)

theorem fuel_le_proverFactor (height fuel : ℕ) :
    2 * fuel + 2 ≤ proverFactor height fuel := by
  unfold proverFactor; rw [Nat.add_assoc]; exact Nat.le_add_left _ _

theorem pow_le_proverFactor (height fuel : ℕ) :
    2 ^ (height + 1) + 2 ≤ proverFactor height fuel := by
  unfold proverFactor; exact Nat.add_le_add_right (Nat.le_add_right _ _) 2

/-- **The prover's queries.** The prover runs a program of cost `n` (`VerifierProgram.Costs`, in
quarters) at height `height` with at most `n · proverFactor height fuel` queries. -/
theorem isTotalQueryBound_proveFromM (S : Strategy) (fuel height : ℕ) {α : Type} :
    ∀ (p : VerifierProgram α) (sp : Sponge) (h : List Ev) (cs : List Tree) (n : ℕ) (Q : α → Prop),
      p.Costs height n Q →
      IsTotalQueryBound (proveFromM callKeccak256 callKeccakF1600 S fuel p sp h cs) (n * proverFactor height fuel)
  | .ret _, _, _, _, _, _, _ => trivial
  | .fail, _, _, _, _, _, _ => trivial
  | .read k, sp, h, cs, n, Q, hp => by
    simp only [proveFromM]
    refine (isTotalQueryBound_absorb_le (n := (n - 1) * proverFactor height fuel + 0) _ _ _
      fun sp' ↦ isTotalQueryBound_bind (isTotalQueryBound_proveFromM S fuel height _ sp'
        (h ++ [Ev.read (S.msg h)]) cs (n - 1) Q (hp.2 _)) fun _ ↦
          isTotalQueryBound_pure' _ 0).mono ?_
    have h1 := hp.1
    have hF := one_le_proverFactor height fuel
    generalize proverFactor height fuel = F at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul, one_mul]
    omega
  | .sample k, sp, h, cs, n, Q, hp => by
    simp only [proveFromM]
    refine (isTotalQueryBound_squeeze_le (n := (n - 4) * proverFactor height fuel) _
      fun r ↦ isTotalQueryBound_proveFromM S fuel height _ r.2
        (h ++ [Ev.sample r.1]) cs (n - 4) Q (hp.2 _)).mono ?_
    have h1 := hp.1
    have hF := one_le_proverFactor height fuel
    generalize proverFactor height fuel = F at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 4 := ⟨n - 4, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul]
    nlinarith
  | .grind bits k, sp, h, cs, n, Q, hp => by
    simp only [proveFromM]
    refine (isTotalQueryBound_bind (isTotalQueryBound_findNonceM bits sp fuel)
      (n₂ := (n - 5) * proverFactor height fuel + 0 + 2) fun o ↦ ?_).mono ?_
    · split
      · trivial
      · exact isTotalQueryBound_powStepM_le (c := (n - 5) * proverFactor height fuel + 0) _ _
          fun r ↦ isTotalQueryBound_bind
          (isTotalQueryBound_proveFromM S fuel height k r.2 (h ++ [Ev.grind bits]) cs (n - 5) Q
            hp.2) fun _ ↦ isTotalQueryBound_pure' _ 0
    · have h1 := hp.1
      have hF := fuel_le_proverFactor height fuel
      generalize proverFactor height fuel = F at *
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 5 := ⟨n - 5, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_mul]
      nlinarith
  | .commit ht w k, sp, h, cs, n, Q, hp => by
    simp only [proveFromM]
    refine (isTotalQueryBound_bind (isTotalQueryBound_buildTreeM ht (S.word h))
      (n₂ := (n - 2) * proverFactor height fuel + 0 + 1 + 1) fun tree ↦
        isTotalQueryBound_absorb_le _ _ _ fun sp0 ↦ isTotalQueryBound_absorb_le _ _ _ fun sp1 ↦
          isTotalQueryBound_bind (isTotalQueryBound_proveFromM S fuel height k sp1
            (h ++ [Ev.commit ht w (S.word h)]) (cs ++ [tree]) (n - 2) Q hp.2.2) fun _ ↦
              isTotalQueryBound_pure' _ 0).mono ?_
    have h1 := hp.2.1
    have h2 : 2 ^ (ht + 1) ≤ 2 ^ (height + 1) := Nat.pow_le_pow_right (by norm_num) (by
      have := hp.1; omega)
    have hF := pow_le_proverFactor height fuel
    generalize proverFactor height fuel = F at *
    generalize 2 ^ (height + 1) = A at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul]
    omega
  | .query i ps k, sp, h, cs, n, Q, hp => by
    simp only [proveFromM]
    split
    · trivial
    · refine (isTotalQueryBound_bind (isTotalQueryBound_proveFromM S fuel height _ sp _ cs
        (n - VerifierProgram.openCost height ps.length) Q (hp.2 _)) fun _ ↦
          isTotalQueryBound_pure' _ 0).mono ?_
      rw [Nat.add_zero]
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

/-- **The honest prover's queries**: at most `n · proverFactor height fuel` for a program of
cost `n` at `height`. -/
theorem isTotalQueryBound_proveM {P : VerifierProgram Bool} {height n : ℕ} (hP : P.CostLE height n)
    (S : Strategy) (seed : KeccakState) (fuel : ℕ) :
    IsTotalQueryBound (proveM callKeccak256 callKeccakF1600 P S seed fuel) (n * proverFactor height fuel) := by
  unfold proveM
  rw [← Nat.add_zero (n * _)]
  exact isTotalQueryBound_bind (isTotalQueryBound_proveFromM S fuel height P ⟨seed, []⟩ [] [] n _
    hP) fun _ ↦ isTotalQueryBound_pure' _ 0

end Queries

end
end LeanVM.Protocol.Compile
