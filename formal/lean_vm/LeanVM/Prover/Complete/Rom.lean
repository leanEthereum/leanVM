/-
  LeanVM.Prover.Complete.Rom

  Completeness in the random-oracle model, for a winning script: the honest run against the
  random oracles makes a proof the verifier rejects only if a proof-of-work search runs out of
  fuel.
-/

module

public import LeanVM.Prover.Complete.Replay
public import LeanVM.Prover.Complete.Pow

/-!
# A winning script in the random-oracle model

The honest prover of the random-oracle model (`honestComp σ P S fuel`) seeds the sponge by `σ` and
runs the script `S` against the program `P` (`runScriptWithHash`) with Keccak-256 and
Keccak-f[1600] two oracle calls, the empty proof where a proof-of-work search fails. In the
experiment `romExperiment` the honest prover and then the verifier run against the same lazily
sampled random oracles.

* `simulateQ_runScript`: interpreting the run's calls by an implementation is running it with
  that implementation (the bus era's `simulateQ_proveM`, for scripts).
* `simulateQ_id_of_look`: a computation that returns `r` against a log's answers returns `r`
  against every hash function and permutation agreeing with the log (restored).
* `runFrom_eq_some_none`: a run of a winning script fails only at a proof-of-work search of at most
  `B` bits, at a sponge whose waiting scalars are the prover's (`ProverSp`).
* `romComplete`: if the script wins `P` with `true` (`Wins B`, `B ≤ 64`), the verifier rejects the
  honest proof with probability at most `(QA + QV) · missK B ^ fuel`, `QA` and `QV` the prover's and
  the verifier's queries. On an outcome where the prover made a proof, both runs read their answers
  from the final log, so they are the pure runs at functions agreeing with it, and the verifier
  accepts (`runProof_of_wins`); where it made none, a search failed, and the proof-of-work
  potential (`LeanVM.Prover.Complete.Pow`) is at least `1`.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

variable {α β : Type}

/-! ## The run commutes with simulation -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

theorem simulateQ_mapM {γ δ : Type} (f : γ → OracleComp KeccakCalls δ) :
    ∀ l : List γ, simulateQ impl (l.mapM f) = l.mapM fun a ↦ simulateQ impl (f a)
  | [] => by simp
  | a :: l => by
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure]
    congr 1; funext b; rw [simulateQ_mapM f l]

theorem simulateQ_arrayMapM {γ δ : Type} (f : γ → OracleComp KeccakCalls δ) (xs : Array γ) :
    simulateQ impl (xs.mapM f) = xs.mapM fun a ↦ simulateQ impl (f a) := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList, simulateQ_map, simulateQ_mapM]

theorem simulateQ_parents (level : Array Digest) (n : ℕ) :
    simulateQ impl (parentsWithHash callKeccak256 level n) =
      parentsWithHash (implH impl) level n := by
  simp only [parentsWithHash, simulateQ_arrayMapM, simulateQ_queryH]

theorem simulateQ_levels :
    ∀ (k : ℕ) (level : Array Digest),
      simulateQ impl (levelsWithHash callKeccak256 k level) = levelsWithHash (implH impl) k level
  | 0, _ => by simp [levelsWithHash]
  | k + 1, level => by
    simp only [levelsWithHash, simulateQ_bind, simulateQ_parents, simulateQ_pure]
    congr 1; funext up; rw [simulateQ_levels k up]

theorem simulateQ_leafDigests (height : ℕ) (word : Word) :
    simulateQ impl (leafDigestsWithHash callKeccak256 height word) =
      leafDigestsWithHash (implH impl) height word := by
  simp only [leafDigestsWithHash, simulateQ_arrayMapM, simulateQ_queryH]

theorem simulateQ_buildTree (height : ℕ) (word : Word) :
    simulateQ impl (buildTreeWithHash callKeccak256 height word) =
      buildTreeWithHash (implH impl) height word := by
  simp only [buildTreeWithHash, simulateQ_bind, simulateQ_leafDigests, simulateQ_levels,
    simulateQ_pure]

theorem simulateQ_searchM (bits : ℕ) (o : Bool) (sp : Sponge) :
    ∀ (count n : ℕ), simulateQ impl (searchM callKeccakF1600 bits o sp n count) =
      searchM (implF impl) bits o sp n count
  | 0, _ => by simp [searchM]
  | count + 1, n => by
    simp only [searchM, simulateQ_bind, simulateQ_absorbNonce]
    congr 1; funext r
    split
    · simp
    · exact simulateQ_searchM bits o sp count (n + 1)

theorem simulateQ_findNonceM (bits : ℕ) (o : Bool) (sp : Sponge) (fuel : ℕ) :
    simulateQ impl (findNonceM callKeccakF1600 bits o sp fuel) =
      findNonceM (implF impl) bits o sp fuel := by
  unfold findNonceM
  exact simulateQ_searchM impl bits o sp _ _

theorem simulateQ_runFrom (fuel : ℕ) :
    ∀ (p : VerifierProgram α) (S : Option (Script β)) (sp : Sponge) (cs : List Tree),
      simulateQ impl (runFromWithHash callKeccak256 callKeccakF1600 fuel p S sp cs) =
        runFromWithHash (implH impl) (implF impl) fuel p S sp cs
  | .ret _, _, _, _ => by simp [runFromWithHash]
  | .fail, _, _, _ => by simp [runFromWithHash]
  | .read k, S, sp, cs => by
    simp only [runFromWithHash, simulateQ_bind, simulateQ_absorb, simulateQ_pure]
    congr 1; funext sp'; rw [simulateQ_runFrom fuel]
  | .sample k, S, sp, cs => by
    simp only [runFromWithHash, simulateQ_bind, simulateQ_squeeze]
    congr 1; funext r; exact simulateQ_runFrom fuel _ _ _ _
  | .readPacked n k, S, sp, cs => by
    simp only [runFromWithHash, simulateQ_bind, simulateQ_observePacked, simulateQ_pure]
    congr 1; funext sp'; rw [simulateQ_runFrom fuel]
  | .samplePacked n k, S, sp, cs => by
    simp only [runFromWithHash, simulateQ_bind, simulateQ_samplesPacked]
    congr 1; funext r; exact simulateQ_runFrom fuel _ _ _ _
  | .grind bits k, S, sp, cs => by
    simp only [runFromWithHash, simulateQ_bind, simulateQ_findNonceM]
    congr 1; funext o
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_absorbNonce, simulateQ_pure]
      congr 1; funext r; rw [simulateQ_runFrom fuel]
  | .commit ht w k, S, sp, cs => by
    simp only [runFromWithHash, simulateQ_bind, simulateQ_buildTree, simulateQ_absorb,
      simulateQ_pure]
    congr 1; funext tree; congr 1; funext sp0; congr 1; funext sp1
    rw [simulateQ_runFrom fuel]
  | .query i ps k, S, sp, cs => by
    simp only [runFromWithHash]
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_pure]
      rw [simulateQ_runFrom fuel]

/-- **The run of a script commutes with simulation.** -/
theorem simulateQ_runScript (P : VerifierProgram Bool) (S : Script β) (seed : KeccakState)
    (fuel : ℕ) :
    simulateQ impl (runScriptWithHash callKeccak256 callKeccakF1600 P S seed fuel) =
      runScriptWithHash (implH impl) (implF impl) P S seed fuel := by
  simp only [runScriptWithHash, simulateQ_bind, simulateQ_runFrom, simulateQ_pure]

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
theorem simulateQ_id_of_look {γ : Type} (ℓ : Log) (H : Bytes → Digest)
    (F : KeccakState → KeccakState)
    (hH : ∀ x u, lookH ℓ x = some u → H x = u) (hF : ∀ s u, lookF ℓ s = some u → F s = u)
    (oa : OracleComp KeccakCalls γ) :
    ∀ r : γ, simulateQ (lookImpl ℓ) oa = some r → simulateQ (totalImpl H F) oa = r := by
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

/-! ## Failure of the honest run -/

section Failure

variable {F : KeccakState → Option KeccakState}

/-- A proof-of-work step's third lane, in `Option`, is the answer's at the position's nonce
input. -/
theorem absorbNonce_option' {sp : Sponge} {n : ℕ} {r : UInt64 × Sponge}
    (h : absorbNonce F sp (nonceOf n) = some r) :
    ∃ c ps u, F (nonceInput c ps n) = some u ∧ r.1 = Keccak.lane u 2 ∧ r.2.state = u ∧
      r.2.pending = [] ∧
      (if sp.pending.length = 4 then ps = [] ∧ ∃ v, F (duplexInput sp) = some v ∧ c = capOf v
        else ps = sp.pending ∧ c = capOf sp.state) := by
  obtain ⟨sp', ha, u, hu, rfl⟩ := (absorbNonce_option _ _ _ _).mp h
  rw [absorb_option] at ha
  split at ha
  · rename_i h4
    obtain ⟨v, hv, rfl⟩ := ha
    refine ⟨capOf v, [], u, ?_, rfl, rfl, rfl, by simp [h4, hv]⟩
    rw [duplexInput_eq] at hu
    exact hu
  · rename_i h4
    subst ha
    refine ⟨capOf sp.state, sp.pending, u, ?_, rfl, rfl, rfl, by simp [h4]⟩
    rw [duplexInput_eq] at hu
    exact hu

theorem searchM_eq_some_none {bits : ℕ} {o : Bool} {sp : Sponge} :
    ∀ (count n : ℕ), searchM F bits o sp n count = some none →
      ∀ j, n ≤ j → j < n + count →
        ∃ r, absorbNonce F sp (nonceOf j) = some r ∧
          (powOk bits r.1 && nonceUsable o (challengeOf r.2.state)) = false
  | 0, _, _ => fun _ h1 h2 ↦ by omega
  | count + 1, n, h => by
    change (absorbNonce F sp (nonceOf n)).bind _ = _ at h
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · rename_i hp
      intro j hj1 hj2
      rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
      · exact ⟨r, hr, Bool.eq_false_iff.mpr hp⟩
      · exact searchM_eq_some_none count (n + 1) h j hlt (by omega)

theorem findNonceM_eq_some_none {bits : ℕ} {o : Bool} {sp : Sponge} {fuel : ℕ}
    (h : findNonceM F bits o sp fuel = some none) :
    ∀ n < fuel, ∃ r, absorbNonce F sp (nonceOf n) = some r ∧
      (powOk bits r.1 && nonceUsable o (challengeOf r.2.state)) = false := by
  unfold findNonceM at h
  exact fun n hn ↦ searchM_eq_some_none fuel 0 h n (Nat.zero_le n) (by omega)

/-- The honest run's sponge between its moves: at most four scalars waiting, each of tag `1`. -/
def ProverSp (sp : Sponge) : Prop := sp.pending.length ≤ 4 ∧ ∀ e ∈ sp.pending, e.2 = 1

theorem proverSp_of_pending {sp sp' : Sponge} (hsp : ProverSp sp)
    (h : sp'.pending = [] ∨ sp'.pending = sp.pending) : ProverSp sp' := by
  rcases h with h | h
  · exact ⟨by simp [h], by simp [h]⟩
  · exact ⟨h ▸ hsp.1, h ▸ hsp.2⟩

theorem proverSp_squeeze {sp : Sponge} (hsp : ProverSp sp) {r : E × Sponge}
    (hr : squeeze F sp = some r) : ProverSp r.2 := by
  rcases hg : sp.ground with _ | c
  · obtain ⟨u, -, rfl⟩ := (squeeze_option _ hg _).mp hr
    exact ⟨by simp, by simp⟩
  · rw [squeeze_ground _ hg] at hr
    cases hr
    exact hsp

theorem proverSp_absorb {sp sp' : Sponge} (hsp : ProverSp sp) {x : E}
    (ha : Compile.absorb (m := Option) F sp x dsObserve = some sp') : ProverSp sp' := by
  rw [absorb_option] at ha
  split at ha
  · obtain ⟨v, -, rfl⟩ := ha
    exact ⟨by simp, by simp [dsObserve]⟩
  · rename_i h4
    subst ha
    refine ⟨by simp; have := hsp.1; omega, fun e he ↦ ?_⟩
    rcases List.mem_append.mp he with he | he
    · exact hsp.2 e he
    · rw [List.mem_singleton] at he; subst he; rfl

theorem pending_observePacked {sp sp' : Sponge} {xs : List E}
    (h : observePacked (m := Option) F sp xs = some sp') :
    sp'.pending = [] ∨ sp'.pending = sp.pending := by
  unfold observePacked at h
  split at h
  · simp only [pure, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨st, rfl, a, -, rfl⟩ := h
    exact Or.inr rfl
  · simp only [duplex, pure, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨sp1, ⟨u, -, rfl⟩, st, -, rfl⟩ := h
    exact Or.inl rfl

theorem pending_squeezePackedChunks :
    ∀ (fuel : ℕ) (sp : Sponge) (missing : ℕ) {r : List E × Sponge},
      squeezePackedChunks (m := Option) F fuel sp missing = some r →
        r.2.pending = [] ∨ r.2.pending = sp.pending
  | 0, sp, _, r, h => by
    simp only [squeezePackedChunks, pure, Option.some.injEq] at h
    subst h; exact Or.inr rfl
  | _ + 1, sp, 0, r, h => by
    simp only [squeezePackedChunks, pure, Option.some.injEq] at h
    subst h; exact Or.inr rfl
  | fuel + 1, sp, missing + 1, r, h => by
    simp only [squeezePackedChunks, duplex, pure, bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨sp1, ⟨u, -, rfl⟩, ⟨rest, sp2⟩, h2, rfl⟩ := h
    rcases pending_squeezePackedChunks fuel _ _ h2 with h' | h'
    · exact Or.inl h'
    · exact Or.inl h'

theorem pending_samplesPacked {sp : Sponge} {n : ℕ} {r : List E × Sponge}
    (h : samplesPacked (m := Option) F sp n = some r) :
    r.2.pending = [] ∨ r.2.pending = sp.pending := by
  unfold samplesPacked at h
  simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨⟨rest, sp2⟩, h2, rfl⟩ := h
  have := pending_squeezePackedChunks _ _ _ h2
  revert this
  split <;> exact id

theorem length_squeezePackedChunks :
    ∀ (fuel : ℕ) (sp : Sponge) (missing : ℕ) {r : List E × Sponge}, missing ≤ fuel →
      squeezePackedChunks (m := Option) F fuel sp missing = some r → r.1.length = missing
  | 0, sp, missing, r, hm, h => by
    simp only [squeezePackedChunks, pure, Option.some.injEq] at h
    subst h; simp; omega
  | _ + 1, sp, 0, r, _, h => by
    simp only [squeezePackedChunks, pure, Option.some.injEq] at h
    subst h; rfl
  | fuel + 1, sp, missing + 1, r, hm, h => by
    simp only [squeezePackedChunks, duplex, pure, bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨sp1, ⟨u, -, rfl⟩, ⟨rest, sp2⟩, h2, rfl⟩ := h
    have := length_squeezePackedChunks fuel _ _ (by omega) h2
    simp only [List.length_append, List.length_map, List.length_range]
    simp only at this
    omega

theorem length_samplesPacked {sp : Sponge} {n : ℕ} {r : List E × Sponge}
    (h : samplesPacked (m := Option) F sp n = some r) : r.1.length = n := by
  unfold samplesPacked at h
  rcases n with _ | c
  · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨rest, sp2⟩, h2, rfl⟩ := h
    exact length_squeezePackedChunks _ _ _ le_rfl h2
  · rcases hg : sp.ground with _ | gr
    · simp only [hg, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨rest, sp2⟩, h2, rfl⟩ := h
      have := length_squeezePackedChunks _ _ _ le_rfl h2
      simp only [List.length_nil, Nat.sub_zero] at this
      simpa using this
    · simp only [hg, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨rest, sp2⟩, h2, rfl⟩ := h
      have := length_squeezePackedChunks _ _ _ le_rfl h2
      simp only [List.length_cons, List.length_map, List.length_take, List.length_range] at this ⊢
      simp only [List.length_append, List.length_cons, List.length_map, List.length_take,
        List.length_range, this]
      omega

/-- The trees of the honest run hold the committed matrices' heights and words. -/
def TreesMatch (trees : List Tree) (cs : List Committed) : Prop :=
  List.Forall₂ (fun t c ↦ t.height = c.height ∧ t.word = c.word) trees cs

theorem buildTree_option {H : Bytes → Option Digest} {ht : ℕ} {word : Word} {tree : Tree}
    (h : buildTreeWithHash H ht word = some tree) : tree.height = ht ∧ tree.word = word := by
  simp only [buildTreeWithHash, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨_, -, _, -, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem TreesMatch.getElem? {trees : List Tree} {cs : List Committed} (h : TreesMatch trees cs)
    {i : ℕ} {c : Committed} (hc : cs[i]? = some c) :
    ∃ t, trees[i]? = some t ∧ t.height = c.height ∧ t.word = c.word := by
  induction h generalizing i with
  | nil => simp at hc
  | cons hab _ ih =>
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hc ⊢
      subst hc
      exact ⟨_, rfl, hab⟩
    · simp only [List.getElem?_cons_succ] at hc ⊢
      exact ih hc

/-- **A winning script's run fails only at a proof of work**: if the run, its queries answered in
`Option`, fails, some proof-of-work search of at most `B` bits failed, at a sponge of the honest
run. -/
theorem runFrom_eq_some_none {H : Bytes → Option Digest} {fuel B : ℕ}
    {Q : α → β → Bool → List Committed → Prop} :
    ∀ (p : VerifierProgram α) (s : Script β) (g : Bool) (cs : List Committed) (sp : Sponge)
      (trees : List Tree),
      Wins B Q p s g cs → TreesMatch trees cs → ProverSp sp →
      runFromWithHash H F fuel p (some s) sp trees = some none →
      ∃ bits o sp', bits ≤ B ∧ ProverSp sp' ∧ findNonceM F bits o sp' fuel = some none
  | .ret _, .ret _, _, _, _, _, _, _, _, hp => by cases hp
  | .read k, .send x s, _, cs, sp, trees, hw, ht, hsp, hp => by
    change (Compile.absorb F sp x dsObserve).bind _ = _ at hp
    obtain ⟨sp', hsp', hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases r with _ | _
    · exact runFrom_eq_some_none (k x) s false cs sp' trees hw.2 ht (proverSp_absorb hsp hsp') hr
    · cases hp
  | .sample k, .sample s, _, cs, sp, trees, hw, ht, hsp, hp => by
    change (squeeze F sp).bind _ = _ at hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    exact runFrom_eq_some_none _ _ false cs _ trees (hw r.1) ht (proverSp_squeeze hsp hr) hp
  | .readPacked n k, .sendPacked xs s, _, cs, sp, trees, hw, ht, hsp, hp => by
    obtain ⟨-, hlen, hw⟩ := hw
    have hpk : Script.packedOf n (some (Script.sendPacked xs s)) = xs := by
      simp only [Script.packedOf]
      subst hlen
      exact List.ext_getElem (by simp) fun i h1 h2 ↦ by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    change (observePacked F sp (Script.packedOf n (some (Script.sendPacked xs s)))).bind _ = _ at hp
    rw [hpk] at hp
    obtain ⟨sp', hsp', hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases r with _ | _
    · exact runFrom_eq_some_none (k xs) s false cs sp' trees hw ht
        (proverSp_of_pending hsp (pending_observePacked hsp')) hr
    · cases hp
  | .samplePacked n k, .samplePacked _ s, g, cs, sp, trees, hw, ht, hsp, hp => by
    change (samplesPacked F sp n).bind _ = _ at hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    exact runFrom_eq_some_none _ _ _ cs _ trees (hw r.1 (length_samplesPacked hr)) ht
      (proverSp_of_pending hsp (pending_samplesPacked hr)) hp
  | .grind bits k, .grind o s, _, cs, sp, trees, hw, ht, hsp, hp => by
    change (findNonceM F bits o sp fuel).bind _ = _ at hp
    obtain ⟨on, hon, hp⟩ := Option.bind_eq_some_iff.mp hp
    rcases on with _ | n
    · exact ⟨bits, o, sp, hw.2.1, hsp, hon⟩
    · change (absorbNonce F sp n).bind _ = _ at hp
      obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
      obtain ⟨t, htt, hp⟩ := Option.bind_eq_some_iff.mp hp
      have hsp' : ProverSp r.2 := by
        obtain ⟨sp', -, u, -, rfl⟩ := (absorbNonce_option _ _ _ _).mp hr
        exact ⟨by simp, by simp⟩
      rcases t with _ | _
      · exact runFrom_eq_some_none k s true cs _ trees hw.2.2 ht hsp' htt
      · cases hp
  | .commit hgt w k, .commit word s, _, cs, sp, trees, hw, ht, hsp, hp => by
    change (buildTreeWithHash H hgt word).bind _ = _ at hp
    obtain ⟨tree, htree, hp⟩ := Option.bind_eq_some_iff.mp hp
    change (Compile.absorb F sp _ _).bind _ = _ at hp
    obtain ⟨sp0, h0, hp⟩ := Option.bind_eq_some_iff.mp hp
    change (Compile.absorb F sp0 _ _).bind _ = _ at hp
    obtain ⟨sp1, h1, hp⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    have ht' : TreesMatch (trees ++ [tree]) (cs ++ [⟨hgt, w, word⟩]) :=
      List.rel_append ht (List.Forall₂.cons (buildTree_option htree) List.Forall₂.nil)
    rcases r with _ | _
    · exact runFrom_eq_some_none k s false _ sp1 _ hw.2.2 ht'
        (proverSp_absorb (proverSp_absorb hsp h0) h1) hr
    · cases hp
  | .query i ps k, .query s, g, cs, sp, trees, hw, ht, hsp, hp => by
    obtain ⟨c, hc, hw⟩ := hw
    obtain ⟨tree, htree, hh, hwd⟩ := ht.getElem? hc
    have hrows : (ps.map fun q ↦ tree.word (q % 2 ^ tree.height)) = c.rows ps := by
      rw [hh, hwd]; rfl
    simp only [runFromWithHash, htree] at hp
    change (runFromWithHash H F fuel _ _ sp trees).bind _ = _ at hp
    obtain ⟨r, hr, hp⟩ := Option.bind_eq_some_iff.mp hp
    rw [hrows] at hr
    rcases r with _ | _
    · exact runFrom_eq_some_none _ _ g cs sp trees hw ht hsp hr
    · cases hp
  | .ret _, .send _ _, _, _, _, _, hw, _, _, _ | .ret _, .sample _, _, _, _, _, hw, _, _, _
  | .ret _, .sendPacked _ _, _, _, _, _, hw, _, _, _
  | .ret _, .samplePacked _ _, _, _, _, _, hw, _, _, _
  | .ret _, .grind _ _, _, _, _, _, hw, _, _, _ | .ret _, .commit _ _, _, _, _, _, hw, _, _, _
  | .ret _, .query _, _, _, _, _, hw, _, _, _ => hw.elim
  | .fail, _, _, _, _, _, hw, _, _, _ => hw.elim
  | .read _, .ret _, _, _, _, _, hw, _, _, _ | .read _, .sample _, _, _, _, _, hw, _, _, _
  | .read _, .sendPacked _ _, _, _, _, _, hw, _, _, _
  | .read _, .samplePacked _ _, _, _, _, _, hw, _, _, _
  | .read _, .grind _ _, _, _, _, _, hw, _, _, _ | .read _, .commit _ _, _, _, _, _, hw, _, _, _
  | .read _, .query _, _, _, _, _, hw, _, _, _ => hw.elim
  | .sample _, .ret _, _, _, _, _, hw, _, _, _ | .sample _, .send _ _, _, _, _, _, hw, _, _, _
  | .sample _, .sendPacked _ _, _, _, _, _, hw, _, _, _
  | .sample _, .samplePacked _ _, _, _, _, _, hw, _, _, _
  | .sample _, .grind _ _, _, _, _, _, hw, _, _, _
  | .sample _, .commit _ _, _, _, _, _, hw, _, _, _
  | .sample _, .query _, _, _, _, _, hw, _, _, _ => hw.elim
  | .readPacked _ _, .ret _, _, _, _, _, hw, _, _, _
  | .readPacked _ _, .send _ _, _, _, _, _, hw, _, _, _
  | .readPacked _ _, .sample _, _, _, _, _, hw, _, _, _
  | .readPacked _ _, .samplePacked _ _, _, _, _, _, hw, _, _, _
  | .readPacked _ _, .grind _ _, _, _, _, _, hw, _, _, _
  | .readPacked _ _, .commit _ _, _, _, _, _, hw, _, _, _
  | .readPacked _ _, .query _, _, _, _, _, hw, _, _, _ => hw.elim
  | .samplePacked _ _, .ret _, _, _, _, _, hw, _, _, _
  | .samplePacked _ _, .send _ _, _, _, _, _, hw, _, _, _
  | .samplePacked _ _, .sample _, _, _, _, _, hw, _, _, _
  | .samplePacked _ _, .sendPacked _ _, _, _, _, _, hw, _, _, _
  | .samplePacked _ _, .grind _ _, _, _, _, _, hw, _, _, _
  | .samplePacked _ _, .commit _ _, _, _, _, _, hw, _, _, _
  | .samplePacked _ _, .query _, _, _, _, _, hw, _, _, _ => hw.elim
  | .grind _ _, .ret _, _, _, _, _, hw, _, _, _ | .grind _ _, .send _ _, _, _, _, _, hw, _, _, _
  | .grind _ _, .sample _, _, _, _, _, hw, _, _, _
  | .grind _ _, .sendPacked _ _, _, _, _, _, hw, _, _, _
  | .grind _ _, .samplePacked _ _, _, _, _, _, hw, _, _, _
  | .grind _ _, .commit _ _, _, _, _, _, hw, _, _, _
  | .grind _ _, .query _, _, _, _, _, hw, _, _, _ => hw.elim
  | .commit _ _ _, .ret _, _, _, _, _, hw, _, _, _
  | .commit _ _ _, .send _ _, _, _, _, _, hw, _, _, _
  | .commit _ _ _, .sample _, _, _, _, _, hw, _, _, _
  | .commit _ _ _, .sendPacked _ _, _, _, _, _, hw, _, _, _
  | .commit _ _ _, .samplePacked _ _, _, _, _, _, hw, _, _, _
  | .commit _ _ _, .grind _ _, _, _, _, _, hw, _, _, _
  | .commit _ _ _, .query _, _, _, _, _, hw, _, _, _ => hw.elim
  | .query _ _ _, .ret _, _, _, _, _, hw, _, _, _
  | .query _ _ _, .send _ _, _, _, _, _, hw, _, _, _
  | .query _ _ _, .sample _, _, _, _, _, hw, _, _, _
  | .query _ _ _, .sendPacked _ _, _, _, _, _, hw, _, _, _
  | .query _ _ _, .samplePacked _ _, _, _, _, _, hw, _, _, _
  | .query _ _ _, .grind _ _, _, _, _, _, hw, _, _, _
  | .query _ _ _, .commit _ _, _, _, _, _, hw, _, _, _ => hw.elim

end Failure

/-! ## The honest prover against the random oracles -/

/-- **The honest prover of the random-oracle model**: seed the sponge by `σ`, then run the script
with every hash and permutation a query; the empty proof if a proof-of-work search fails. -/
def honestComp (σ : Seed) (P : VerifierProgram Bool) (S : Script β) (fuel : ℕ) :
    OracleComp KeccakCalls Proof := do
  let seed ← σ.run callKeccak256 callKeccakF1600
  let r ← runScriptWithHash callKeccak256 callKeccakF1600 P S seed fuel
  pure (r.getD ⟨[], []⟩)

/-- **The final inequality.** On every reachable outcome of the logged experiment in which the
verifier rejects a winning script's proof, the proof-of-work potential of the final log is at least
`1`. -/
theorem one_le_powPot {σ : Seed} {P : VerifierProgram Bool} {S : Script β} {B fuel : ℕ}
    (hfuel : fuel ≤ 2 ^ 64) (hfuel0 : fuel ≠ 0)
    (hw : Wins B (fun a _ _ _ ↦ a = true) P S false [])
    {z : (Proof × Bool) × Log}
    (hz : z ∈ support (logExperiment (honestComp σ P S fuel) (verifierComp σ P)))
    (hrej : z.1.2 = false) :
    1 ≤ powPot B fuel z.2 := by
  set ℓ := z.2
  have h := (simulateQ_look_of_mem_support _ [] z hz).2 ℓ (List.prefix_refl _)
  rw [simulateQ_bind] at h
  obtain ⟨π, hA, h⟩ := Option.bind_eq_some_iff.mp h
  rw [simulateQ_map] at h
  obtain ⟨b, hb, hπb⟩ := Option.map_eq_some_iff.mp h
  have hzb : b = false := by rw [← hrej, ← hπb]
  subst hzb
  simp only [honestComp, simulateQ_bind, simulateQ_seedRun, simulateQ_runScript,
    simulateQ_pure] at hA
  change (σ.run (lookH ℓ) (lookF ℓ)).bind (fun seed ↦ (runScriptWithHash (lookH ℓ) (lookF ℓ) P S
    seed fuel).bind fun r ↦ some (r.getD ⟨[], []⟩)) = some π at hA
  obtain ⟨seed, hseed, hA⟩ := Option.bind_eq_some_iff.mp hA
  obtain ⟨r, hr, hA⟩ := Option.bind_eq_some_iff.mp hA
  cases r with
  | some π' =>
    -- The prover made a proof: the verifier accepts it, a contradiction.
    exfalso
    cases hA
    let Ht : Bytes → Digest := fun x ↦ (lookH ℓ x).getD default
    let Ft : KeccakState → KeccakState := fun s ↦ (lookF ℓ s).getD default
    have hH : ∀ x u, lookH ℓ x = some u → Ht x = u := fun x u hx ↦ by simp [Ht, hx]
    have hF : ∀ s u, lookF ℓ s = some u → Ft s = u := fun s u hs ↦ by simp [Ft, hs]
    have hseed' : σ.run (m := Id) Ht Ft = seed := by
      have := simulateQ_id_of_look ℓ Ht Ft hH hF (σ.run callKeccak256 callKeccakF1600) seed
        (by rw [simulateQ_seedRun]; exact hseed)
      rwa [simulateQ_seedRun] at this
    have hπ : Id.run (runScriptWithHash (m := Id) Ht Ft P S seed fuel) = some π' := by
      have := simulateQ_id_of_look ℓ Ht Ft hH hF
        (runScriptWithHash callKeccak256 callKeccakF1600 P S seed fuel) (some π')
        (by rw [simulateQ_runScript]; exact hr)
      rw [simulateQ_runScript] at this
      exact this
    have hb' : simulateQ (lookImpl ℓ) (verifierComp σ P π') = some false := hb
    have hv := simulateQ_id_of_look ℓ Ht Ft hH hF (verifierComp σ P π') false hb'
    rw [simulateQ_verify] at hv
    have hacc := runProof_of_wins Ht Ft fuel hw hπ
    have hv' : runProofWithHash (m := Id) Ht Ft P (σ.run (m := Id) Ht Ft) π' = false := hv
    rw [hseed'] at hv'
    rw [hv'] at hacc
    cases hacc
  | none =>
    -- The prover made none: some proof-of-work search failed.
    have hr' : runFromWithHash (lookH ℓ) (lookF ℓ) fuel P (some S) ⟨seed, [], none⟩ [] =
        some none := by
      change (runFromWithHash (lookH ℓ) (lookF ℓ) fuel P (some S) ⟨seed, [], none⟩ []).bind
        _ = _ at hr
      obtain ⟨t, ht, hr⟩ := Option.bind_eq_some_iff.mp hr
      cases t with
      | none => exact ht
      | some _ => cases hr
    obtain ⟨b', o, sp, hbB, hsp, hf⟩ := runFrom_eq_some_none P S false [] ⟨seed, [], none⟩ [] hw
      List.Forall₂.nil ⟨by simp, by simp⟩ hr'
    have hall' := findNonceM_eq_some_none hf
    have hall : ∀ n < fuel, ∃ r, absorbNonce (lookF ℓ) sp (nonceOf n) = some r ∧
        passK B r.2.state = false ∧ r.1 = Keccak.lane r.2.state 2 := fun n hn ↦ by
      obtain ⟨r, hr, hp⟩ := hall' n hn
      obtain ⟨-, -, u, -, hru, hsu, -⟩ := absorbNonce_option' hr
      refine ⟨r, hr, ?_, by rw [hru, hsu]⟩
      by_contra hB
      have := nonceOk_of_passK hbB o (by simpa using hB)
      rw [hru, hsu] at hp
      rw [hsu, hp] at this
      cases this
    obtain ⟨κ, hκ, hnon⟩ : ∃ κ : PowKey, KeyOk κ ∧ ∀ n < fuel, ∃ u,
        lookF ℓ (nonceInput κ.1 κ.2 n) = some u ∧ passK B u = false := by
      by_cases h4 : sp.pending.length = 4
      · obtain ⟨r0, hr0, -⟩ := hall 0 (Nat.pos_of_ne_zero hfuel0)
        obtain ⟨c0, ps0, u0, -, -, -, -, hif⟩ := absorbNonce_option' hr0
        simp only [h4, ↓reduceIte] at hif
        obtain ⟨-, v, hv, -⟩ := hif
        refine ⟨(capOf v, []), ⟨by simp, by simp⟩, fun n hn ↦ ?_⟩
        obtain ⟨r, hr, hp, -⟩ := hall n hn
        obtain ⟨c, ps, u, hu, -, hsu, -, hif⟩ := absorbNonce_option' hr
        simp only [h4, ↓reduceIte] at hif
        obtain ⟨rfl, v', hv', rfl⟩ := hif
        rw [hv] at hv'
        cases hv'
        exact ⟨u, hu, by rw [← hsu]; exact hp⟩
      · refine ⟨(capOf sp.state, sp.pending), ⟨by dsimp only; have := hsp.1; omega, hsp.2⟩,
          fun n hn ↦ ?_⟩
        obtain ⟨r, hr, hp, -⟩ := hall n hn
        obtain ⟨c, ps, u, hu, -, hsu, -, hif⟩ := absorbNonce_option' hr
        simp only [h4, ↓reduceIte] at hif
        obtain ⟨rfl, rfl⟩ := hif
        exact ⟨u, hu, by rw [← hsu]; exact hp⟩
    have hS : ¬ Solved B fuel ℓ κ := by
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
    have hterm : powTerm B fuel ℓ κ = 1 := by
      simp [powTerm, hS, hT]
    have hmem : κ ∈ keys fuel ℓ := by
      obtain ⟨u, hu, -⟩ := hnon 0 (Nat.pos_of_ne_zero hfuel0)
      obtain ⟨i, hi, hei, -⟩ := (lookF_eq_some_iff ℓ _ u).mp hu
      exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨_, mem_fIns_of_getElem hi hei,
        keyOf_nonceInput hfuel hκ (Nat.pos_of_ne_zero hfuel0)⟩)
    rw [← hterm]
    exact Finset.single_le_sum (fun _ _ ↦ bot_le) hmem

/-- **Completeness in the random-oracle model, for a winning script.** For a script that wins the
program `P` with `true` with proofs of work of at most `B ≤ 64` bits, the seeding `σ`, and a fuel
of `1` to `2^64` nonces: with `QA` and `QV` the queries of the honest prover and of the verifier,
the verifier rejects the honest proof with probability at most
`(QA + QV) · (1 - 2^-B (1 - 2^-64))^fuel`. -/
theorem romComplete (P : VerifierProgram Bool) (S : Script β) (σ : Seed) {B fuel QA QV : ℕ}
    (hb : B ≤ 64) (hfuel : fuel ≤ 2 ^ 64) (hfuel0 : fuel ≠ 0)
    (hw : Wins B (fun a _ _ _ ↦ a = true) P S false [])
    (hA : IsTotalQueryBound (honestComp σ P S fuel) QA)
    (hV : ∀ π, IsTotalQueryBound (verifierComp σ P π) QV) :
    Pr{let z ← romExperiment (honestComp σ P S fuel) (verifierComp σ P)}[z.1.2 = false] ≤
      ((QA + QV : ℕ) : ℝ≥0∞) * missK B ^ fuel := by
  rw [prEvent_romExperiment_eq_logExperiment _ _ fun r _ ↦ r.2 = false]
  have hstep : LogFreshStepBound (powPot B fuel) (missK B ^ fuel) := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ x _ ↦ ?_, fun ℓ s hs' ↦ ?_⟩
    · simp only [powPot_append_inl]
      exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
    · exact powPot_stepF hb hfuel ((lookR_eq_none_iff ℓ s).mpr hs')
  have h := prEvent_run_loggedRO_le_of_freshStepBound hstep _ (QA + QV)
    (isTotalQueryBound_bind hA fun a ↦ (isQueryBound_map_iff (verifierComp σ P a) _ QV _ _).mpr
      (hV a)) [] (fun r _ ↦ r.2 = false)
    (fun z hz hrej ↦ one_le_powPot hfuel hfuel0 hw hz hrej)
  rw [powPot_nil, zero_add] at h
  exact h

end LeanVM.Prover

end
