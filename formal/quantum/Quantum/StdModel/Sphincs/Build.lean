module

public import Quantum.StdModel.Sphincs.Table

@[expose] public section

/-!
# leanSPHINCS at a fixed hash: the key's structure built position by position

The reductions see the hash only through their challengers, so they compute the honest structure
of a key one position at a time, each value from the values of lower rank.

* `KeyPart`: the positions of the key's structure (all but the key expansion, the randomizers and
  the digest cells, which belong to the messages); `keyOrder` lists those in use by rank
  (`mem_keyOrder`, `pairwise_keyOrder`).
* `buildDig ask`: the digests of the key's positions, asked in `keyOrder`, each `ask p t` given
  the digests `t` found so far. `buildDig_eq_pure`: if `ask` returns a target `T` at the
  positions of `Pub` whenever `t` agrees with `T` at the lower positions of `Pub`, and some pure
  value elsewhere, the build returns a table agreeing with `T` on `Pub`
  (`buildDig_eq_pure_full` for `Pub = True`); `simulateQ_buildDig`.
* `keySlot p`, `keyPayload p t`: the slot of a key position and its payload read from the digests
  `t` (`keyPayload_congr`: only the digests of lower rank). An honest table's digest at a public
  key position is `Th` at its slot and payload (`dig_eq_thSlot`, `dig_digTable_eq_thSlot`), so a
  build asking `Th` there and the secrets at the secrets returns the digests of `digTable`
  (`buildDig_digTable`).
-/

open OracleComp OracleSpec
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Qrom.Sphincs

namespace Quantum.StdModel.Sphincs

/-! ## The key's positions and their order -/

/-- The positions of a key's structure: all but the key expansion, the randomizers and the
digest cells. -/
def KeyPart : RawPos → Prop
  | .prfKey | .publicSeed | .prfMsg _ | .hmsg _ => False
  | _ => True

instance instDecidablePredKeyPart : DecidablePred KeyPart := fun p ↦ by
  cases p <;> unfold KeyPart <;> infer_instance

/-- **The key's positions in use, by nondecreasing rank.** -/
noncomputable def keyOrder : List Pos :=
  ((Finset.univ.filter fun p : Pos ↦ KeyPart p.1).toList).mergeSort
    fun p q ↦ decide (p.1.rank ≤ q.1.rank)

theorem mem_keyOrder (p : Pos) : p ∈ keyOrder ↔ KeyPart p.1 := by
  unfold keyOrder
  simp

theorem pairwise_keyOrder : keyOrder.Pairwise fun p q ↦ p.1.rank ≤ q.1.rank := by
  unfold keyOrder
  refine (List.pairwise_mergeSort (fun a b c hab hbc ↦ ?_) (fun a b ↦ ?_) _).imp
    fun h ↦ of_decide_eq_true h
  · exact decide_eq_true (le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
  · rcases le_total a.1.rank b.1.rank with h | h
    · simp [h]
    · simp [h]

attribute [irreducible] keyOrder

/-! ## The build -/

/-- One step of the build: ask the position's digest and record it. -/
def buildStep {m : Type → Type} [Monad m] (ask : RawPos → (RawPos → Digest) → m Digest)
    (t : RawPos → Digest) (p : Pos) : m (RawPos → Digest) := do
  let d ← ask p.1 t
  pure (Function.update t p.1 d)

/-- **The build**: the key's digests asked in `keyOrder`, from the zero table. -/
noncomputable def buildDig {m : Type → Type} [Monad m]
    (ask : RawPos → (RawPos → Digest) → m Digest) : m (RawPos → Digest) :=
  keyOrder.foldlM (buildStep ask) fun _ ↦ 0

theorem simulateQ_foldlM_buildStep {ι : Type} {O : OracleSpec.{0, 0} ι} {n : Type → Type}
    [Monad n] [LawfulMonad n] (impl : QueryImpl O n)
    (ask : RawPos → (RawPos → Digest) → OracleComp O Digest) :
    ∀ (L : List Pos) (t : RawPos → Digest),
      simulateQ impl (L.foldlM (buildStep ask) t) =
        L.foldlM (buildStep fun p t ↦ simulateQ impl (ask p t)) t
  | [], t => simulateQ_pure impl t
  | p :: L, t => by
    simp only [List.foldlM_cons, buildStep, simulateQ_bind, bind_assoc, pure_bind,
      simulateQ_foldlM_buildStep impl ask L]

/-- **The build**, its oracles answered by `impl`, is the build of the answered asks. -/
theorem simulateQ_buildDig {ι : Type} {O : OracleSpec.{0, 0} ι} {n : Type → Type} [Monad n]
    [LawfulMonad n] (impl : QueryImpl O n)
    (ask : RawPos → (RawPos → Digest) → OracleComp O Digest) :
    simulateQ impl (buildDig ask) = buildDig fun p t ↦ simulateQ impl (ask p t) :=
  simulateQ_foldlM_buildStep impl ask keyOrder _

section Semantics

variable {m : Type → Type} [Monad m] [LawfulMonad m]
  (ask : RawPos → (RawPos → Digest) → m Digest) (T : RawPos → Digest) (Pub : RawPos → Prop)
  (junk : RawPos → (RawPos → Digest) → Digest)

theorem foldlM_buildStep_eq_pure
    (hPub : ∀ p : Pos, KeyPart p.1 → Pub p.1 → ∀ t : RawPos → Digest,
      (∀ q : Pos, KeyPart q.1 → Pub q.1 → q.1.rank < p.1.rank → t q.1 = T q.1) →
        ask p.1 t = pure (T p.1))
    (hjunk : ∀ p : Pos, KeyPart p.1 → ¬Pub p.1 → ∀ t, ask p.1 t = pure (junk p.1 t)) :
    ∀ L : List Pos, L.Pairwise (fun a b : Pos ↦ a.1.rank ≤ b.1.rank) →
      (∀ p ∈ L, KeyPart p.1) → ∀ t : RawPos → Digest,
        (∀ q : Pos, KeyPart q.1 → Pub q.1 → q ∉ L → t q.1 = T q.1) →
          ∃ tf, L.foldlM (buildStep ask) t = pure tf ∧
            ∀ q : Pos, KeyPart q.1 → Pub q.1 → tf q.1 = T q.1
  | [], _, _, t, hinv => ⟨t, rfl, fun q hk hq ↦ hinv q hk hq fun h ↦ by cases h⟩
  | p :: L, hL, hK, t, hinv => by
    rw [List.pairwise_cons] at hL
    have hkp := hK p List.mem_cons_self
    have hstep : ∃ d, ask p.1 t = pure d ∧ (Pub p.1 → d = T p.1) := by
      by_cases hp : Pub p.1
      · refine ⟨T p.1, hPub p hkp hp t fun q hk hq hr ↦ hinv q hk hq ?_, fun _ ↦ rfl⟩
        intro hmem
        rcases List.mem_cons.1 hmem with rfl | hmem
        · exact lt_irrefl _ hr
        · exact absurd (hL.1 q hmem) (Nat.not_le.2 hr)
      · exact ⟨junk p.1 t, hjunk p hkp hp t, fun h ↦ (hp h).elim⟩
    obtain ⟨d, hd, hdT⟩ := hstep
    obtain ⟨tf, h1, h2⟩ := foldlM_buildStep_eq_pure hPub hjunk L hL.2
      (fun q hq ↦ hK q (List.mem_cons_of_mem p hq)) (Function.update t p.1 d)
      fun q hk hq hnot ↦ by
        by_cases hqp : q = p
        · subst hqp
          rw [Function.update_self]
          exact hdT hq
        · rw [Function.update_of_ne fun e ↦ hqp (Subtype.ext e)]
          exact hinv q hk hq fun hmem ↦ (List.mem_cons.1 hmem).elim hqp hnot
    refine ⟨tf, ?_, h2⟩
    rw [List.foldlM_cons, buildStep, hd, pure_bind, pure_bind]
    exact h1

/-- **The build returns the target on the public positions**: `ask` returns the target at a
position of `Pub` given the target at the lower positions of `Pub`, and a pure value elsewhere. -/
theorem buildDig_eq_pure
    (hPub : ∀ p : Pos, KeyPart p.1 → Pub p.1 → ∀ t : RawPos → Digest,
      (∀ q : Pos, KeyPart q.1 → Pub q.1 → q.1.rank < p.1.rank → t q.1 = T q.1) →
        ask p.1 t = pure (T p.1))
    (hjunk : ∀ p : Pos, KeyPart p.1 → ¬Pub p.1 → ∀ t, ask p.1 t = pure (junk p.1 t)) :
    ∃ tf, buildDig ask = pure tf ∧ ∀ p : Pos, KeyPart p.1 → Pub p.1 → tf p.1 = T p.1 :=
  foldlM_buildStep_eq_pure ask T Pub junk hPub hjunk keyOrder pairwise_keyOrder
    (fun p hp ↦ (mem_keyOrder p).1 hp) _ fun q hk _ hq ↦ (hq ((mem_keyOrder q).2 hk)).elim

/-- **The build returns the target** when `ask` returns it at every key position given the target
at the lower ones. -/
theorem buildDig_eq_pure_full
    (hall : ∀ p : Pos, KeyPart p.1 → ∀ t : RawPos → Digest,
      (∀ q : Pos, KeyPart q.1 → q.1.rank < p.1.rank → t q.1 = T q.1) →
        ask p.1 t = pure (T p.1)) :
    ∃ tf, buildDig ask = pure tf ∧ ∀ p : Pos, KeyPart p.1 → tf p.1 = T p.1 := by
  obtain ⟨tf, h1, h2⟩ := buildDig_eq_pure ask T (fun _ ↦ True) (fun _ _ ↦ 0)
    (fun p hk _ t ht ↦ hall p hk t fun q hq hr ↦ ht q hq trivial hr)
    (fun _ _ hp ↦ (hp trivial).elim)
  exact ⟨tf, h1, fun p hk ↦ h2 p hk trivial⟩

end Semantics

/-! ## Slots and payloads of the key's positions -/

/-- The slot of a position (a digest cell's at randomizer `0`). -/
def keySlot : RawPos → Quantum.Sphincs.Slot
  | .prfKey => .expand 1
  | .publicSeed => .expand 0
  | .chainStart l τ e i => .prf (.oneTimeChain l τ e i)
  | .chain l τ e i step => .chain l τ e i step
  | .leaf l τ e => .leaf l τ e
  | .node l τ level index => .node l τ (level.val + 1) index.val
  | .forsSecret idx κ s => .prf (.forsSecret idx κ s)
  | .forsLeaf idx κ s => .forsLeaf idx κ s
  | .forsNode idx κ level node => .forsNode idx κ (level.val + 1) node.val
  | .forsRoots idx => .forsRoots idx
  | .prfMsg message => .prfMsg message
  | .hmsg message => .hmsg 0 message 0

theorem posSlot_eq_keySlot (v : QTable) {p : RawPos} (hp : ∀ M, p ≠ .hmsg M) :
    posSlot v p = keySlot p := by
  cases p <;> first | rfl | exact (hp _ rfl).elim

theorem slotInRange_keySlot (p : Pos) (hp : ∀ M, p.1 ≠ .hmsg M) : SlotInRange (keySlot p.1) :=
  posSlot_eq_keySlot (fun _ ↦ 0) hp ▸ slotInRange_posSlot (fun _ ↦ 0) p

/-- The table holding the digests `t` at the key's positions, `0` elsewhere. -/
def ofDig (t : RawPos → Digest) : QTable :=
  fun p ↦ if KeyPart p.1 then (embedDigest (t p.1), 0) else 0

theorem dig_ofDig_congr {t t' : RawPos → Digest} {q : RawPos}
    (h : q.InRange → KeyPart q → t q = t' q) : (ofDig t).dig q = (ofDig t').dig q :=
  dig_congr_trunc fun hp ↦ by
    by_cases hk : KeyPart q
    · simp only [ofDig, hk, ↓reduceIte, h hp hk]
    · simp only [ofDig, hk, ↓reduceIte]

theorem dig_ofDig (t : RawPos → Digest) (q : Pos) (hk : KeyPart q.1) :
    (ofDig t).dig q.1 = t q.1 := by
  refine (congrArg truncateHash ((ofDig t).out_of_inRange q.2)).trans ?_
  simp only [ofDig, hk, ↓reduceIte, truncateHash_embedDigest]

theorem dig_ofDig_dig (v : QTable) {q : RawPos} (hk : KeyPart q) :
    (ofDig v.dig).dig q = v.dig q :=
  dig_congr_trunc fun hp ↦ by
    simp only [ofDig, hk, ↓reduceIte, truncateHash_embedDigest]
    exact congrArg truncateHash (v.out_of_inRange hp)

/-- The payload of a position's slot, its values read from the digests `t`. -/
def keyPayload : (p : RawPos) → (RawPos → Digest) → SlotPayload (keySlot p)
  | .prfKey, _ => ()
  | .publicSeed, _ => ()
  | .chainStart .., _ => ()
  | .chain l τ e i step, t => (ofDig t).chainValue l τ e i step.val
  | .leaf l τ e, t => (ofDig t).endpoints l τ e
  | .node l τ level index, t =>
      ((ofDig t).treeValue l τ level.val (2 * index.val),
        (ofDig t).treeValue l τ level.val (2 * index.val + 1))
  | .forsSecret .., _ => ()
  | .forsLeaf idx κ s, t => (ofDig t).forsSecret idx κ s
  | .forsNode idx κ level node, t =>
      ((ofDig t).forsValue idx κ level.val (2 * node.val),
        (ofDig t).forsValue idx κ level.val (2 * node.val + 1))
  | .forsRoots idx, t => (ofDig t).forsRoot idx
  | .prfMsg _, _ => ()
  | .hmsg _, _ => ()

section KeyCongr

variable {v v' : QTable}

theorem chainValue_congr_key {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {i : ChainIndex}
    {j : ℕ} (hd : ∀ q : RawPos, KeyPart q → q.rank < 2 + j → v.dig q = v'.dig q) :
    v.chainValue l τ e i j = v'.chainValue l τ e i j := by
  cases j with
  | zero => exact hd (.chainStart l τ e i) trivial (by simp [RawPos.rank])
  | succ j =>
    simp only [QTable.chainValue]
    split_ifs with hj
    · exact hd (.chain l τ e i ⟨j, hj⟩) trivial (by simp [RawPos.rank])
    · rfl

theorem treeValue_congr_key {l : Layer} {τ : TreeIndex} {level index : ℕ}
    (hd : ∀ q : RawPos, KeyPart q → q.rank < 2 + chainLength + level → v.dig q = v'.dig q) :
    v.treeValue l τ level index = v'.treeValue l τ level index := by
  cases level with
  | zero => exact hd (.leaf l τ (leafOfNat index)) trivial (by simp [RawPos.rank])
  | succ level =>
    simp only [QTable.treeValue]
    split_ifs with hl
    · exact hd (.node l τ ⟨level, hl.1⟩ ⟨index, hl.2⟩) trivial (by simp [RawPos.rank])
    · rfl

theorem forsValue_congr_key {idx : Index} {κ : ForsTreeIndex} {height node : ℕ}
    (hd : ∀ q : RawPos, KeyPart q → q.rank < 3 + height → v.dig q = v'.dig q) :
    v.forsValue idx κ height node = v'.forsValue idx κ height node := by
  cases height with
  | zero => exact hd (.forsLeaf idx κ (forsLeafOfNat node)) trivial (by simp [RawPos.rank])
  | succ height =>
    simp only [QTable.forsValue]
    split_ifs with hh
    · exact hd (.forsNode idx κ ⟨height, hh.1⟩ ⟨node, hh.2⟩) trivial (by simp [RawPos.rank])
    · rfl

end KeyCongr

/-- **A payload reads only the digests of lower rank.** -/
theorem keyPayload_congr (p : RawPos) {t t' : RawPos → Digest}
    (ht : ∀ q : Pos, KeyPart q.1 → q.1.rank < p.rank → t q.1 = t' q.1) :
    keyPayload p t = keyPayload p t' := by
  have hd : ∀ q : RawPos, KeyPart q → q.rank < p.rank → (ofDig t).dig q = (ofDig t').dig q :=
    fun q hk hr ↦ dig_ofDig_congr fun hq _ ↦ ht ⟨q, hq⟩ hk hr
  have hc := two_le_chainLength
  cases p with
  | chain l τ e i step =>
    show (ofDig t).chainValue l τ e i step.val = (ofDig t').chainValue l τ e i step.val
    exact chainValue_congr_key hd
  | leaf l τ e =>
    show (ofDig t).endpoints l τ e = (ofDig t').endpoints l τ e
    exact funext fun _ ↦ chainValue_congr_key (j := chainLength - 1) fun q hk hr ↦
      hd q hk (lt_of_lt_of_le hr (by show 2 + (chainLength - 1) ≤ 1 + chainLength; omega))
  | node l τ level index =>
    show ((ofDig t).treeValue l τ level.val (2 * index.val),
        (ofDig t).treeValue l τ level.val (2 * index.val + 1)) =
      ((ofDig t').treeValue l τ level.val (2 * index.val),
        (ofDig t').treeValue l τ level.val (2 * index.val + 1))
    exact Prod.ext (treeValue_congr_key hd) (treeValue_congr_key hd)
  | forsLeaf idx κ s =>
    show (ofDig t).forsSecret idx κ s = (ofDig t').forsSecret idx κ s
    exact hd (.forsSecret idx κ s) trivial (by show 1 < 2; omega)
  | forsNode idx κ level node =>
    show ((ofDig t).forsValue idx κ level.val (2 * node.val),
        (ofDig t).forsValue idx κ level.val (2 * node.val + 1)) =
      ((ofDig t').forsValue idx κ level.val (2 * node.val),
        (ofDig t').forsValue idx κ level.val (2 * node.val + 1))
    exact Prod.ext (forsValue_congr_key hd) (forsValue_congr_key hd)
  | forsRoots idx =>
    show (ofDig t).forsRoot idx = (ofDig t').forsRoot idx
    exact funext fun _ ↦ forsValue_congr_key hd
  | _ => rfl

/-- A public key position's input is its slot's input at its payload read from the digests. -/
theorem posInput_eq_keyInput (S0 : MasterSeed) (v : QTable) {p : RawPos} (hk : KeyPart p)
    (hs : ¬IsSecret p) :
    posInput S0 v p = slotInput (pubKey v.publicSeed) 0 (keySlot p) (keyPayload p v.dig) := by
  have hd : ∀ q : RawPos, KeyPart q → v.dig q = (ofDig v.dig).dig q :=
    fun q hq ↦ (dig_ofDig_dig v hq).symm
  have hcv : v.chainValue = (ofDig v.dig).chainValue := by
    funext l τ e i j
    exact chainValue_congr_key fun q hq _ ↦ hd q hq
  have htv : v.treeValue = (ofDig v.dig).treeValue := by
    funext l τ level index
    exact treeValue_congr_key fun q hq _ ↦ hd q hq
  have hfv : v.forsValue = (ofDig v.dig).forsValue := by
    funext idx κ height node
    exact forsValue_congr_key fun q hq _ ↦ hd q hq
  cases p with
  | chain l τ e i step =>
    show slotInput (pubKey v.publicSeed) 0 (.chain l τ e i step) (v.chainValue l τ e i step.val) =
      slotInput (pubKey v.publicSeed) 0 (.chain l τ e i step)
        ((ofDig v.dig).chainValue l τ e i step.val)
    rw [hcv]
  | leaf l τ e =>
    have hep : v.endpoints l τ e = (ofDig v.dig).endpoints l τ e := funext fun i ↦
      congrFun (congrFun (congrFun (congrFun (congrFun hcv l) τ) e) i) (chainLength - 1)
    show slotInput (pubKey v.publicSeed) 0 (.leaf l τ e) (v.endpoints l τ e) =
      slotInput (pubKey v.publicSeed) 0 (.leaf l τ e) ((ofDig v.dig).endpoints l τ e)
    rw [hep]
  | node l τ level index =>
    show slotInput (pubKey v.publicSeed) 0 (.node l τ (level.val + 1) index.val)
        (v.treeValue l τ level.val (2 * index.val),
          v.treeValue l τ level.val (2 * index.val + 1)) =
      slotInput (pubKey v.publicSeed) 0 (.node l τ (level.val + 1) index.val)
        ((ofDig v.dig).treeValue l τ level.val (2 * index.val),
          (ofDig v.dig).treeValue l τ level.val (2 * index.val + 1))
    rw [htv]
  | forsLeaf idx κ s =>
    have hfs : v.forsSecret idx κ s = (ofDig v.dig).forsSecret idx κ s :=
      hd (.forsSecret idx κ s) trivial
    show slotInput (pubKey v.publicSeed) 0 (.forsLeaf idx κ s) (v.forsSecret idx κ s) =
      slotInput (pubKey v.publicSeed) 0 (.forsLeaf idx κ s) ((ofDig v.dig).forsSecret idx κ s)
    rw [hfs]
  | forsNode idx κ level node =>
    show slotInput (pubKey v.publicSeed) 0 (.forsNode idx κ (level.val + 1) node.val)
        (v.forsValue idx κ level.val (2 * node.val),
          v.forsValue idx κ level.val (2 * node.val + 1)) =
      slotInput (pubKey v.publicSeed) 0 (.forsNode idx κ (level.val + 1) node.val)
        ((ofDig v.dig).forsValue idx κ level.val (2 * node.val),
          (ofDig v.dig).forsValue idx κ level.val (2 * node.val + 1))
    rw [hfv]
  | forsRoots idx =>
    have hr : v.forsRoot idx = (ofDig v.dig).forsRoot idx := funext fun κ ↦
      congrFun (congrFun (congrFun (congrFun hfv idx) κ) forsTreeHeight) 0
    show slotInput (pubKey v.publicSeed) 0 (.forsRoots idx) (v.forsRoot idx) =
      slotInput (pubKey v.publicSeed) 0 (.forsRoots idx) ((ofDig v.dig).forsRoot idx)
    rw [hr]
  | _ => first | exact (hk : False).elim | exact (hs trivial).elim

/-- **An honest table's digest at a public key position** is `Th` at its slot and payload. -/
theorem dig_eq_thSlot {h : HashInput → HashOutput} {v : QTable} (hv : Honest h v) (p : Pos)
    (hk : KeyPart p.1) (hs : ¬IsSecret p.1) :
    v.dig p.1 = thSlot h v.publicSeed (keySlot p.1) (keyPayload p.1 v.dig) :=
  (congrArg truncateHash ((v.out_of_inRange p.2).trans (hv.out p hs))).trans
    (congrArg (fun x ↦ truncateHash (h x)) (posInput_eq_keyInput 0 v hk hs))

theorem dig_digTable_eq_thSlot (h : HashInput → HashOutput) (P : PublicParameter)
    (sec : KeygenDomain → Digest) (r : Message → Digest) (p : Pos) (hk : KeyPart p.1)
    (hs : ¬IsSecret p.1) :
    (digTable h P sec r).dig p.1 =
      thSlot h P (keySlot p.1) (keyPayload p.1 (digTable h P sec r).dig) :=
  (dig_eq_thSlot (honest_digTable h P sec r) p hk hs).trans
    (congrArg (fun P' ↦ thSlot h P' (keySlot p.1) (keyPayload p.1 (digTable h P sec r).dig))
      (publicSeed_digTable h P sec r))

/-- **The build of the digest table**: asking `Th` at the public key positions and the table's
secrets at the secrets returns the digests of `digTable h P sec r` at the key's positions. -/
theorem buildDig_digTable {m : Type → Type} [Monad m] [LawfulMonad m]
    (h : HashInput → HashOutput) (P : PublicParameter) (sec : KeygenDomain → Digest)
    (r : Message → Digest) (ask : RawPos → (RawPos → Digest) → m Digest)
    (hsec : ∀ p : Pos, KeyPart p.1 → IsSecret p.1 → ∀ t,
      ask p.1 t = pure ((digTable h P sec r).dig p.1))
    (hth : ∀ p : Pos, KeyPart p.1 → ¬IsSecret p.1 → ∀ t,
      ask p.1 t = pure (thSlot h P (keySlot p.1) (keyPayload p.1 t))) :
    ∃ tf, buildDig ask = pure tf ∧
      ∀ p : Pos, KeyPart p.1 → tf p.1 = (digTable h P sec r).dig p.1 :=
  buildDig_eq_pure_full ask _ fun p hk t ht ↦ by
    by_cases hs : IsSecret p.1
    · exact hsec p hk hs t
    · rw [hth p hk hs t, keyPayload_congr p.1 ht, ← dig_digTable_eq_thSlot h P sec r p hk hs]

end Quantum.StdModel.Sphincs

end
