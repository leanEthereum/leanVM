module

public import Quantum.Qrom.Xmss.Events
public import Quantum.Qrom.Xmss.HonestTable

@[expose] public section

/-!
# leanXMSS in the random-oracle model: a win is in the event

A state `s` of the hardwired register answers the verifier's hash calls through its union view
`unionH s` (the hardwired cells over the adversary's database): `viewH (unionH s)`, `0` off its
cells.

`win_imp_badQ`: a forgery that verifies with every hashed cell recorded or hardwired, against a
valid transcript of honest signatures (`v.signature H`) and not returned by the signer, puts the
state in `BadQ (QTable.honCell S0 v)`, when every hardwired honest chain cell has a known input
(`HwKnown`, implied by its slot being `Public`) and the memory records the signer's selections
(`Records`).

The proof is the last-divergence argument of `Quantum.Xmss.Classify`, with cells for sponge
paths. Along each walk the verifier makes (Merkle path, leaf, chains), the forged walk ends at the
honest value, so either some input differs from the honest cell while its output truncates to the
honest digest (Struct, a target of that input), or the walk starts at the honest value. A chain
entered at the honest value at position `x_i` is a Struct hit unless the honest cell of that step
is hardwired, hence known, hence opened by a signature of the same key at a position `≤ x_i`; the
forged word is then the signed word (incomparability of codewords), and the forged
message-digest cell is the selected one or its digest is the selected digest (Enc). Hardwired
values play no role: a cell has one input.
-/

open OracleComp OracleSpec
open HashSig HashSig.OverPermutation LeanXmss
open Quantum.Xmss (Slot leafKey leafKey_val layerDisclosed Known known_chain sibling
  last_divergence evalWithAnswerFn_sequenceFin queriesSatisfy_bind_iff eq_topLayer
  signature_eq_layers)
open Quantum.SufCma (QueriesSatisfy queries trace_query_bind trace_eq_flatMap)

namespace Quantum.Qrom.Xmss

local notation "ev" H => evalWithAnswerFn (romAnswers H)

/-! ## The view of a union -/

/-- **The hash of a union view**: its value at a recorded or hardwired cell, `0` elsewhere. -/
def viewH (U : HashDomain → Option HashOutput) (x : HashDomain) : HashOutput :=
  (U x).getD 0

/-- A query answered by the union view: a hash of a recorded or hardwired cell (coins pass). -/
def ReadBy (U : HashDomain → Option HashOutput) : RomOracles.Domain → Prop
  | .inl _ => True
  | .inr x => (U x).isSome

/-- The hashed cells of an honest evaluation are its hash queries. -/
theorem readBy_of_honestEval {U : HashDomain → Option HashOutput} {α : Type}
    {x : OracleComp RomOracles α} (h : ∀ c ∈ (honestEval (viewH U) x).2, (U c).isSome) :
    QueriesSatisfy (romAnswers (viewH U)) (ReadBy U) x := by
  intro t ht
  rcases t with n | c
  · trivial
  · refine h c ?_
    change c ∈ Quantum.SufCma.trace (romAnswers (viewH U)) hashRead x
    rw [trace_eq_flatMap]
    exact List.mem_flatMap.2 ⟨_, ht, List.mem_singleton_self c⟩

/-- A cell determines its payload. -/
theorem cell_payload_inj {P : PublicParameter} {s : Slot} (hs : Addressable s)
    {d d' : Payload s} (h : cell P s d = cell P s d') : d = d' :=
  eq_of_heq (Sigma.mk.inj (cell_injective P hs hs h)).2

/-! ## The verifier's walks as cell reads -/

section Walks

variable {H : HashDomain → HashOutput} {Pr : RomOracles.Domain → Prop}

/-- A tweakable hash at a slot's input queries its cell. -/
theorem queriesSatisfy_th_cell {P : PublicParameter} {fields : TweakFields} {p : HashInput}
    {Q : PublicParameter} {s : Slot} {d : Payload s} (h : thInput P fields p = slotInput Q s d)
    (hq : QueriesSatisfy (romAnswers H) Pr (Over.th hashQ P fields p)) :
    Pr (.inr (cell Q s d)) := by
  rw [Over.th, h, hashQ_slotInput] at hq
  refine hq _ ?_
  rw [queries, trace_query_bind]
  exact List.mem_append_left _ (List.mem_singleton_self _)

/-- The cell of the chain step leaving position `j` of chain `i` at value `w` (`0` past the
chain). -/
def chainCell (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex) (j : ℕ)
    (w : Digest) : HashDomain :=
  if h : j < chainLength - 1 then cell P (.chain l e ⟨j, h⟩ i) w else 0

theorem chainCell_of_lt {P : PublicParameter} {l : Layer} {e : KeyIndex} {i : ChainIndex}
    {j : ℕ} (h : j < chainLength - 1) (w : Digest) :
    chainCell P l e i j w = cell P (.chain l e ⟨j, h⟩ i) w :=
  dite_eq_left h

theorem chainCell_inj {P : PublicParameter} {l : Layer} {e : KeyIndex} {i : ChainIndex} {j : ℕ}
    (h : j < chainLength - 1) {w w' : Digest}
    (hc : chainCell P l e i j w = chainCell P l e i j w') : w = w' := by
  rw [chainCell_of_lt h, chainCell_of_lt h] at hc
  exact cell_payload_inj (by trivial) hc

variable (H) in
theorem ev_chainWalk_succ (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex)
    (a k : ℕ) (w : Digest) (h : a + k < chainLength - 1) :
    (ev H) (Over.chainWalk hashQ P l e i a (k + 1) w) =
      truncateHash (H (chainCell P l e i (a + k)
        ((ev H) (Over.chainWalk hashQ P l e i a k w)))) := by
  rw [chainCell_of_lt h, Over.chainWalk, walkChain, evalWithAnswerFn_bind]
  simp only [h, ↓reduceDIte]
  exact eval_th rfl

theorem readBy_chainWalk {P : PublicParameter} {l : Layer} {e : KeyIndex} {i : ChainIndex}
    {a : ℕ} {w : Digest} : ∀ {n : ℕ},
      QueriesSatisfy (romAnswers H) Pr (Over.chainWalk hashQ P l e i a n w) →
      ∀ k < n, a + k < chainLength - 1 →
        Pr (.inr (chainCell P l e i (a + k) ((ev H) (Over.chainWalk hashQ P l e i a k w))))
  | 0, _, k, hk, _ => absurd hk (Nat.not_lt_zero k)
  | n + 1, hQ, k, hk, h => by
    rw [Over.chainWalk, walkChain] at hQ
    obtain ⟨h1, h2⟩ := queriesSatisfy_bind_iff.1 hQ
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact readBy_chainWalk h1 k hk h
    · simp only [h, ↓reduceDIte] at h2
      rw [chainCell_of_lt h]
      exact queriesSatisfy_th_cell rfl h2

/-- The children of the node above level `k` on the path of key `e`: the value `cur` and the
sibling, ordered by bit `k` of `e`. -/
def nodeChildren (e : KeyIndex) (sib : ℕ → Digest) (k : ℕ) (cur : Digest) : Digest × Digest :=
  if e.val.testBit k then (sib k, cur) else (cur, sib k)

/-- The cell of the node above level `k` on the path of key `e` of layer `l`. -/
def nodeCell (P : PublicParameter) (l : Layer) (e : KeyIndex) (sib : ℕ → Digest) (k : ℕ)
    (cur : Digest) : HashDomain :=
  cell P (.node l (k + 1) (e.val / 2 ^ (k + 1))) (nodeChildren e sib k cur)

theorem thInput_node (P : PublicParameter) (l : Layer) (e : KeyIndex) (sib : ℕ → Digest)
    (k : ℕ) (cur : Digest) :
    thInput P (hashDomainFields (.node l (k + 1) (e.val / 2 ^ (k + 1))))
      (if e.val.testBit k then nodePayload (sib k) cur else nodePayload cur (sib k)) =
      slotInput P (.node l (k + 1) (e.val / 2 ^ (k + 1))) (nodeChildren e sib k cur) := by
  unfold nodeChildren
  split <;> rfl

theorem addressable_node_path (l : Layer) (e : KeyIndex) {k : ℕ} (hk : k < layerHeight) :
    Addressable (.node l (k + 1) (e.val / 2 ^ (k + 1))) := by
  have he : e.val < 2 ^ 32 := e.isLt
  have hL : layerHeight = 16 := rfl
  exact ⟨by omega, lt_of_le_of_lt (Nat.div_le_self _ _) he⟩

theorem nodeCell_inj {P : PublicParameter} {l : Layer} {e : KeyIndex} {sib sib' : ℕ → Digest}
    {k : ℕ} (hk : k < layerHeight) {cur cur' : Digest}
    (h : nodeCell P l e sib k cur = nodeCell P l e sib' k cur') : cur = cur' ∧ sib k = sib' k := by
  have h' := cell_payload_inj (addressable_node_path l e hk) h
  unfold nodeChildren at h'
  split at h'
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact ⟨h2, h1⟩
  · obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact ⟨h1, h2⟩

variable (H) in
theorem ev_treeFold_succ (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (path : Fin layerHeight → Digest) (k : ℕ) (cur : Digest) :
    (ev H) (Over.treeFold hashQ P l e path (k + 1) cur) =
      truncateHash (H (nodeCell P l e (sibling path) k
        ((ev H) (Over.treeFold hashQ P l e path k cur)))) := by
  rw [Over.treeFold, foldPath, evalWithAnswerFn_bind]
  exact eval_th (thInput_node P l e (sibling path) k _)

theorem readBy_treeFold {P : PublicParameter} {l : Layer} {e : KeyIndex}
    {path : Fin layerHeight → Digest} {cur : Digest} : ∀ {n : ℕ},
      QueriesSatisfy (romAnswers H) Pr (Over.treeFold hashQ P l e path n cur) →
      ∀ k < n, Pr (.inr (nodeCell P l e (sibling path) k
        ((ev H) (Over.treeFold hashQ P l e path k cur))))
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, hQ, k, hk => by
    rw [Over.treeFold, foldPath] at hQ
    obtain ⟨h1, h2⟩ := queriesSatisfy_bind_iff.1 hQ
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact readBy_treeFold h1 k hk
    · exact queriesSatisfy_th_cell (thInput_node P l e (sibling path) k _) h2

variable (H) in
theorem ev_leafHash (P : PublicParameter) (l : Layer) (e : KeyIndex) (E : ChainIndex → Digest) :
    (ev H) (Over.leafHash hashQ P l e E) = truncateHash (H (cell P (.leaf l e) E)) :=
  eval_th rfl

variable (H) in
theorem ev_messageDigest (P : PublicParameter) (l : Layer) (e : KeyIndex) (msg : MsgBytes)
    (ρ : Randomizer) :
    (ev H) (Over.messageDigest hashQ P l e msg.1 ρ) =
      truncateHash (H (cell P (.msg l e) (msg, ρ))) :=
  eval_th rfl

/-- **What an accepted layer computes**: the message digest decodes to a word `x`, the chains are
walked from the signature's values at `x` to their ends `E`, the leaf of `E` is folded along the
path to the root; with every query satisfying `Pr` when the layer's queries do. -/
theorem layerRoot_spec {P : PublicParameter} {l : Layer} {e : KeyIndex} {msg : MsgBytes}
    {part : LayerSignature} {root : Digest}
    (hQ : QueriesSatisfy (romAnswers H) Pr (Over.layerRoot hashQ P l e msg.1 part))
    (hr : (ev H) (Over.layerRoot hashQ P l e msg.1 part) = some root) :
    ∃ x E, Codeword.decode (truncateHash (H (cell P (.msg l e) (msg, part.randomizer)))) = some x ∧
      Pr (.inr (cell P (.msg l e) (msg, part.randomizer))) ∧
      (∀ i, QueriesSatisfy (romAnswers H) Pr
        (Over.recoverChain hashQ P l e i (x i) (part.chainValues i))) ∧
      (∀ i, E i = (ev H) (Over.recoverChain hashQ P l e i (x i) (part.chainValues i))) ∧
      Pr (.inr (cell P (.leaf l e) E)) ∧
      QueriesSatisfy (romAnswers H) Pr (Over.treeFold hashQ P l e part.authenticationPath
        layerHeight (truncateHash (H (cell P (.leaf l e) E)))) ∧
      (ev H) (Over.treeFold hashQ P l e part.authenticationPath layerHeight
        (truncateHash (H (cell P (.leaf l e) E)))) = root := by
  rw [Over.layerRoot, evalWithAnswerFn_bind] at hr
  rw [Over.layerRoot] at hQ
  obtain ⟨hQ1, hQ2⟩ := queriesSatisfy_bind_iff.1 hQ
  rw [Over.otsLeaf] at hQ1
  obtain ⟨hQm, hQ1⟩ := queriesSatisfy_bind_iff.1 hQ1
  have hd := ev_messageDigest H P l e msg part.randomizer
  rw [hd] at hQ1
  generalize hleaf : (ev H) (Over.otsLeaf hashQ P l e msg.1 part.randomizer part.chainValues) =
    leaf at hr hQ2
  rw [Over.otsLeaf, evalWithAnswerFn_bind, hd] at hleaf
  cases hx : Codeword.decode (truncateHash (H (cell P (.msg l e) (msg, part.randomizer)))) with
  | none =>
    simp only [hx] at hleaf
    subst hleaf
    simp at hr
  | some x =>
    simp only [hx] at hleaf hQ1
    obtain ⟨hQc, hQ1⟩ := queriesSatisfy_bind_iff.1 hQ1
    obtain ⟨hQl, -⟩ := queriesSatisfy_bind_iff.1 hQ1
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, evalWithAnswerFn_sequenceFin,
      ev_leafHash] at hleaf
    subst hleaf
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at hr
    simp only [evalWithAnswerFn_sequenceFin] at hQl
    simp only [queriesSatisfy_bind_iff] at hQ2
    exact ⟨x, _, rfl, queriesSatisfy_th_cell rfl hQm,
      Quantum.Xmss.QueriesSatisfy.of_sequenceFin hQc, fun _ ↦ rfl,
      queriesSatisfy_th_cell rfl hQl, hQ2.1, hr⟩

end Walks

/-! ## Target hits -/

section Hits

variable {hon : HonestCells} {s : RomReg HashDomain HashOutput SelMem}

/-- **A Struct hit**: a recorded or hardwired cell at a Struct slot whose value truncates to the
slot's honest digest, other than the hardwired honest cell. -/
theorem mem_badQ_of_struct {x c : HashDomain} {sl : Slot} {d : Digest}
    (hx : (unionH s x).isSome) (hsl : slotOf x = some sl) (hmsg : ∀ l e, sl ≠ .msg l e)
    (hc : hon sl = some (c, d)) (hd : truncateHash (viewH (unionH s) x) = d)
    (hne : ¬(c = x ∧ (s.2.1.1 x).isSome)) : s ∈ BadQ hon := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hx
  refine mem_badQ_iff.2 ⟨x, y, hy, ?_⟩
  rw [tgtDigest, hsl, Option.bind_some, slotDigest_of_ne_msg _ _ _ hmsg, structDigest, hc,
    Option.bind_some, ite_eq_right hne, ← hd, viewH, hy]
  rfl

/-- **An Enc hit**: a recorded or hardwired cell at the message slot of a selected key, other than
the selected cell, whose value truncates to the selected digest. -/
theorem mem_badQ_of_enc {x c : HashDomain} {l : Layer} {e : KeyIndex} {d : Digest}
    (hx : (unionH s x).isSome) (hsl : slotOf x = some (.msg l e)) (hm : s.2.2 l e = some (c, d))
    (hne : c ≠ x) (hd : truncateHash (viewH (unionH s) x) = d) : s ∈ BadQ hon := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hx
  refine mem_badQ_iff.2 ⟨x, y, hy, ?_⟩
  rw [tgtDigest, hsl, Option.bind_some, slotDigest_msg, hm, Option.bind_some, ite_eq_right hne,
    ← hd, viewH, hy]
  rfl

end Hits

/-! ## Walks meeting the honest table -/

section Meet

variable {S0 : MasterSeed} {v : QTable} {s : RomReg HashDomain HashOutput SelMem}

theorem chainCell_honest (S0 : MasterSeed) (v : QTable) (l : Layer) (e : KeyIndex)
    (i : ChainIndex) {j : ℕ} (h : j < chainLength - 1) :
    chainCell v.param l e i j (v.chainValue l e i j) = cellOf S0 (.chain l e i ⟨j, h⟩) v := by
  rw [chainCell_of_lt h]
  rfl

theorem truncateHash_chain (v : QTable) (l : Layer) (e : KeyIndex) (i : ChainIndex) {j : ℕ}
    (h : j < chainLength - 1) :
    truncateHash (v (.chain l e i ⟨j, h⟩)) = v.chainValue l e i (j + 1) := by
  rw [QTable.chainValue, dite_eq_left h]

/-- **A chain walk ending at the honest chain** (no hit): it starts at the honest value, and the
honest cell of its first step is hardwired. -/
theorem chain_meet (hnb : s ∉ BadQ (QTable.honCell S0 v)) {l : Layer} {e : KeyIndex}
    {i : ChainIndex} {a n : ℕ} (hn : 0 < n) (han : a + n ≤ chainLength - 1) {w : Digest}
    (hQ : QueriesSatisfy (romAnswers (viewH (unionH s))) (ReadBy (unionH s))
      (Over.chainWalk hashQ v.param l e i a n w))
    (hend : (ev (viewH (unionH s))) (Over.chainWalk hashQ v.param l e i a n w) =
      v.chainValue l e i (a + n)) :
    w = v.chainValue l e i a ∧
      ∀ h : a < chainLength - 1, (s.2.1.1 (cellOf S0 (.chain l e i ⟨a, h⟩) v)).isSome := by
  let H := viewH (unionH s)
  let f : ℕ → Digest := fun k ↦ (ev H) (Over.chainWalk hashQ v.param l e i a k w)
  let g : ℕ → Digest := fun k ↦ v.chainValue l e i (a + k)
  let u : ℕ → HashDomain := fun k ↦ chainCell v.param l e i (a + k) (f k)
  let u' : ℕ → HashDomain := fun k ↦ chainCell v.param l e i (a + k) (g k)
  have hit : ∀ k (hk : k < n), f (k + 1) = g (k + 1) →
      ¬(u' k = u k ∧ (s.2.1.1 (u k)).isSome) → False := by
    intro k hk hfg hne
    have hb : a + k < chainLength - 1 := by omega
    apply hnb
    refine mem_badQ_of_struct (x := u k) (sl := .chain l e ⟨a + k, hb⟩ i)
      (readBy_chainWalk hQ k hk hb) ?_ (fun _ _ h ↦ by cases h) rfl ?_ ?_
    · show slotOf (chainCell v.param l e i (a + k) (f k)) = _
      rw [chainCell_of_lt hb]
      exact slotOf_cell _ (by trivial) _
    · exact (ev_chainWalk_succ H _ _ _ _ a k w hb).symm.trans
        (hfg.trans (truncateHash_chain v l e i hb).symm)
    · rintro ⟨h1, h2⟩
      exact hne ⟨(chainCell_honest S0 v l e i hb).trans h1, h2⟩
  have hstep : ∀ k, k + 1 < n → u (k + 1) = u' (k + 1) → f (k + 1) = g (k + 1) :=
    fun k hk h ↦ chainCell_inj (by omega) h
  rcases last_divergence u u' f g n hend hstep with ⟨k, hk, hne, hfg⟩ | hall
  · exact (hit k hk hfg fun h ↦ hne h.1.symm).elim
  · have h0 : f 0 = g 0 := chainCell_inj (by omega) (hall 0 hn)
    refine ⟨h0, fun ha ↦ ?_⟩
    by_contra hEx
    have h1 : f 1 = g 1 := by
      rcases Nat.lt_or_ge 1 n with h | h
      · exact chainCell_inj (by omega) (hall 1 h)
      · obtain rfl : n = 1 := by omega
        exact hend
    exact hit 0 hn h1 fun h ↦ hEx (by
      rw [← chainCell_honest S0 v l e i ha]
      exact (congrArg (fun x ↦ (s.2.1.1 x).isSome) h.1).trans h.2)

/-- The honest cell of the node above level `k` on the path of key `e`. -/
theorem honCell_node_path (S0 : MasterSeed) (v : QTable) (l : Layer) (e : KeyIndex) {k : ℕ}
    (hk : k < layerHeight) (hx : e.val / 2 ^ (k + 1) < 2 ^ (31 - k)) :
    QTable.honCell S0 v (.node l (k + 1) (e.val / 2 ^ (k + 1))) =
      some (cellOf S0 (.node l ⟨k, hk⟩ ⟨e.val / 2 ^ (k + 1), hx⟩) v,
        truncateHash (v (.node l ⟨k, hk⟩ ⟨e.val / 2 ^ (k + 1), hx⟩))) :=
  dite_eq_left ⟨hk, hx⟩

theorem index_node_path (e : KeyIndex) {k : ℕ} (hk : k < layerHeight) :
    e.val / 2 ^ (k + 1) < 2 ^ (31 - k) := by
  have he : e.val < 2 ^ 32 := e.isLt
  have hL : layerHeight = 16 := rfl
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 31 - k + (k + 1) = 32 by omega]
  exact he

/-- The honest cell of the node above level `k` on the path of key `e` is the node cell of the
honest value and sibling at level `k`. -/
theorem nodeCell_honest (S0 : MasterSeed) (v : QTable) (l : Layer) (e : KeyIndex) {k : ℕ}
    (hk : k < layerHeight) :
    nodeCell v.param l e (fun k ↦ v.treeValue l k (e.val / 2 ^ k ^^^ 1)) k
        (v.treeValue l k (e.val / 2 ^ k)) =
      cellOf S0 (.node l ⟨k, hk⟩ ⟨e.val / 2 ^ (k + 1), index_node_path e hk⟩) v := by
  unfold nodeCell
  change _ = cell v.param (.node l (k + 1) (e.val / 2 ^ (k + 1)))
    (v.treeValue l k (2 * (e.val / 2 ^ (k + 1))), v.treeValue l k (2 * (e.val / 2 ^ (k + 1)) + 1))
  congr 1
  have hj : e.val / 2 ^ (k + 1) = e.val / 2 ^ k / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  unfold nodeChildren
  rw [hj, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (e.val / 2 ^ k) with h | h
  · have hx : e.val / 2 ^ k ^^^ 1 = e.val / 2 ^ k + 1 := Nat.xor_one_of_even (Nat.even_iff.2 h)
    simp only [h, hx, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte]
    congr 2 <;> omega
  · have hx : e.val / 2 ^ k ^^^ 1 = e.val / 2 ^ k - 1 := Nat.xor_one_of_odd (Nat.odd_iff.2 h)
    simp only [h, hx, decide_true, ↓reduceIte]
    congr 2 <;> omega

theorem truncateHash_node (v : QTable) (l : Layer) {k : ℕ} (hk : k < layerHeight) {x : ℕ}
    (hx : x < 2 ^ (31 - k)) :
    truncateHash (v (.node l ⟨k, hk⟩ ⟨x, hx⟩)) = v.treeValue l (k + 1) x := by
  rw [QTable.treeValue, dite_eq_left (show k < layerHeight ∧ x < 2 ^ (31 - k) from ⟨hk, hx⟩)]

/-- **A Merkle path ending at the honest root** (no hit): it starts at the honest leaf value and
its siblings are the honest authentication path. -/
theorem path_meet (hnb : s ∉ BadQ (QTable.honCell S0 v)) {l : Layer} {e : KeyIndex}
    {path : Fin layerHeight → Digest} {cur : Digest}
    (hQ : QueriesSatisfy (romAnswers (viewH (unionH s))) (ReadBy (unionH s))
      (Over.treeFold hashQ v.param l e path layerHeight cur))
    (hroot : (ev (viewH (unionH s))) (Over.treeFold hashQ v.param l e path layerHeight cur) =
      v.treeValue l layerHeight (e.val / 2 ^ layerHeight)) :
    cur = v.treeValue l 0 e.val ∧ path = v.authPath l e := by
  let H := viewH (unionH s)
  let f : ℕ → Digest := fun k ↦ (ev H) (Over.treeFold hashQ v.param l e path k cur)
  let g : ℕ → Digest := fun k ↦ v.treeValue l k (e.val / 2 ^ k)
  let hs : ℕ → Digest := fun k ↦ v.treeValue l k (e.val / 2 ^ k ^^^ 1)
  let u : ℕ → HashDomain := fun k ↦ nodeCell v.param l e (sibling path) k (f k)
  let u' : ℕ → HashDomain := fun k ↦ nodeCell v.param l e hs k (g k)
  have hstep : ∀ k, k + 1 < layerHeight → u (k + 1) = u' (k + 1) → f (k + 1) = g (k + 1) :=
    fun _ hk h ↦ (nodeCell_inj hk h).1
  rcases last_divergence u u' f g layerHeight hroot hstep with ⟨k, hk, hne, hfg⟩ | hall
  · exfalso
    apply hnb
    refine mem_badQ_of_struct (x := u k) (readBy_treeFold hQ k hk)
      (slotOf_cell _ (addressable_node_path l e hk) _) (fun _ _ h ↦ by cases h)
      (honCell_node_path S0 v l e hk (index_node_path e hk)) ?_ ?_
    · exact (ev_treeFold_succ H _ _ _ _ k cur).symm.trans
        (hfg.trans (truncateHash_node v l hk (index_node_path e hk)).symm)
    · rintro ⟨h1, -⟩
      exact hne (h1.symm.trans (nodeCell_honest S0 v l e hk).symm)
  · have h0 := (nodeCell_inj (by decide) (hall 0 (by decide))).1
    change cur = v.treeValue l 0 (e.val / 2 ^ 0) at h0
    rw [pow_zero, Nat.div_one] at h0
    refine ⟨h0, funext fun k ↦ ?_⟩
    have hk := (nodeCell_inj k.isLt (hall k.val k.isLt)).2
    simp only [sibling, k.isLt, ↓reduceDIte] at hk
    exact hk

theorem truncateHash_leaf (v : QTable) (l : Layer) (e : KeyIndex) :
    truncateHash (v (.leaf l e)) = v.treeValue l 0 e.val := by
  change _ = truncateHash (v (.leaf l (leafKey e.val)))
  rw [leafKey_val]

end Meet

/-! ## Signed keys and the opened chain positions -/

section Signed

/-- The message a request's signature signs on layer `l`: the message at the bottom, the root of
the bottom tree at the top. -/
def layerMsg (v : QTable) (req : SigningRequest) (l : Layer) : MsgBytes :=
  if l = bottomLayer then messageBytes req.message else rootBytes (v.bottomRoot req.leafIndex)

/-- The randomizer base of a request's key on layer `l`. -/
def layerBase (v : QTable) (req : SigningRequest) (l : Layer) : Randomizer :=
  if l = bottomLayer then v.bottomBase req else v.topBase req

theorem layerMsg_bottom (v : QTable) (req : SigningRequest) :
    layerMsg v req bottomLayer = messageBytes req.message :=
  ite_eq_left rfl

theorem layerMsg_top (v : QTable) (req : SigningRequest) :
    layerMsg v req topLayer = rootBytes (v.bottomRoot req.leafIndex) :=
  ite_eq_right (by decide)

theorem layerBase_bottom (v : QTable) (req : SigningRequest) :
    layerBase v req bottomLayer = v.bottomBase req :=
  ite_eq_left rfl

theorem layerBase_top (v : QTable) (req : SigningRequest) :
    layerBase v req topLayer = v.topBase req :=
  ite_eq_right (by decide)

/-- **The memory records the signer's selections of `req`**: for each layer, the cell of the
selected message-digest input and the selected digest. -/
def Records (v : QTable) (H : HashDomain → HashOutput) (m : SelMem) (req : SigningRequest) :
    Prop :=
  ∀ l sel, v.select H l (keyIndexOnLayer req.leafIndex l) (layerMsg v req l)
      (layerBase v req l) = some sel →
    m l (keyIndexOnLayer req.leafIndex l) =
      some (cell v.param (.msg l (keyIndexOnLayer req.leafIndex l)) (layerMsg v req l, sel.1),
        v.messageDigest H l (keyIndexOnLayer req.leafIndex l) (layerMsg v req l) sel.1)

/-- **Every hardwired honest chain cell has a known input**: its input position is computable
from the disclosures (`Known`), as for every `Public` slot. -/
def HwKnown (S0 : MasterSeed) (v : QTable) (H : HashDomain → HashOutput)
    (s : RomReg HashDomain HashOutput SelMem) (reqs : List SigningRequest) : Prop :=
  ∀ l e i (step : ChainStep), (s.2.1.1 (cellOf S0 (.chain l e i step) v)).isSome →
    Known (v.disclosures H reqs) (.chain l e i step.val)

/-- The selection decodes its digest to its word. -/
theorem decode_of_selectFrom (v : QTable) (H : HashDomain → HashOutput) {l : Layer}
    {e : KeyIndex} {msg : MsgBytes} {base : Randomizer} :
    ∀ attempts trial {sel : Randomizer × Encoding},
      v.selectFrom H l e msg base attempts trial = some sel →
        Codeword.decode (v.messageDigest H l e msg sel.1) = some sel.2
  | 0, _, _, h => by simp [QTable.selectFrom] at h
  | n + 1, trial, sel, h => by
    rw [QTable.selectFrom] at h
    split at h
    · next x hx =>
      obtain rfl := Option.some.inj h
      exact hx
    · exact decode_of_selectFrom v H n (trial + 1) h

theorem decode_of_select {v : QTable} {H : HashDomain → HashOutput} {l : Layer} {e : KeyIndex}
    {msg : MsgBytes} {base : Randomizer} {sel : Randomizer × Encoding}
    (h : v.select H l e msg base = some sel) :
    Codeword.decode (v.messageDigest H l e msg sel.1) = some sel.2 :=
  decode_of_selectFrom v H _ _ h

/-- **An opened chain position comes from a signature by its key**: the key's selection for the
request's message opens the chain at or below it. -/
theorem exists_signed_of_known {v : QTable} {H : HashDomain → HashOutput}
    {reqs : List SigningRequest} {l : Layer} {e : KeyIndex} {i : ChainIndex} {j : ℕ}
    (h : Known (v.disclosures H reqs) (.chain l e i j)) :
    ∃ req ∈ reqs, keyIndexOnLayer req.leafIndex l = e ∧
      ∃ sel, v.select H l e (layerMsg v req l) (layerBase v req l) = some sel ∧
        (sel.2 i).val ≤ j := by
  obtain ⟨j', hj', hm⟩ := known_chain h l e i j rfl
  rcases hm with hm | hm
  · simp at hm
  simp only [Set.mem_iUnion] at hm
  obtain ⟨req, hreq, hd⟩ := hm
  refine ⟨req, hreq, ?_⟩
  unfold QTable.disclosedBy at hd
  rcases hb : v.select H bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (messageBytes req.message) (v.bottomBase req) with _ | b <;>
    rcases ht : v.select H topLayer (keyIndexOnLayer req.leafIndex topLayer)
      (rootBytes (v.bottomRoot req.leafIndex)) (v.topBase req) with _ | tp <;>
    simp only [hb, ht, Set.mem_empty_iff_false] at hd
  rcases hd with (⟨i', hi'⟩ | ⟨lv, hlv⟩) | (⟨i', hi'⟩ | ⟨lv, hlv⟩)
  · simp only [Quantum.Xmss.Pos.chain.injEq] at hi'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi'
    exact ⟨rfl, b, by rw [layerMsg_bottom, layerBase_bottom]; exact hb, hj'⟩
  · cases hlv
  · simp only [Quantum.Xmss.Pos.chain.injEq] at hi'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi'
    exact ⟨rfl, tp, by rw [layerMsg_top, layerBase_top]; exact ht, hj'⟩
  · cases hlv

/-- **One selection per key**: in a valid transcript, two requests signing with the same key of a
layer sign the same message on it from the same randomizer base. -/
theorem layer_eq_of_key {v : QTable} {log : QueryLog SigningOracleSpec}
    (hvalid : SigningTranscript.NoLeafIndexReused log)
    {r r' : (_ : SigningRequest) × Option Signature} (hr : r ∈ log) (hr' : r' ∈ log) {l : Layer}
    (hk : keyIndexOnLayer r.1.leafIndex l = keyIndexOnLayer r'.1.leafIndex l) :
    layerMsg v r.1 l = layerMsg v r'.1 l ∧ layerBase v r.1 l = layerBase v r'.1 l := by
  by_cases hl : l = bottomLayer
  · subst hl
    have hidx : r.1.leafIndex = r'.1.leafIndex := Fin.ext (by
      have := congrArg Fin.val hk
      simpa [keyIndexOnLayer, bottomLayer] using this)
    rw [List.inj_on_of_nodup_map hvalid hr hr' hidx]
    exact ⟨rfl, rfl⟩
  · obtain rfl := eq_topLayer hl
    rw [layerMsg_top, layerMsg_top, layerBase_top, layerBase_top]
    unfold QTable.topBase QTable.bottomRoot
    rw [hk]
    exact ⟨rfl, rfl⟩

end Signed

/-! ## Both layers -/

section Layers

variable {S0 : MasterSeed} {v : QTable} {H : HashDomain → HashOutput}
  {s : RomReg HashDomain HashOutput SelMem} {log : QueryLog SigningOracleSpec}

/-- **A layer reaching the honest root of its tree** (no hit) is the signature of that layer by a
signed request with the same key, on the same message. -/
theorem layer_meet (hM : ∀ r ∈ log, Records v H s.2.2 r.1)
    (hEx : HwKnown S0 v H s (log.map Sigma.fst))
    (hvalid : SigningTranscript.NoLeafIndexReused log) (hnb : s ∉ BadQ (QTable.honCell S0 v))
    {l : Layer} {e : KeyIndex} {msg : MsgBytes} {part : LayerSignature}
    (hQ : QueriesSatisfy (romAnswers (viewH (unionH s))) (ReadBy (unionH s))
      (Over.layerRoot hashQ v.param l e msg.1 part))
    (hr : (ev (viewH (unionH s))) (Over.layerRoot hashQ v.param l e msg.1 part) =
      some (v.treeValue l layerHeight (e.val / 2 ^ layerHeight))) :
    ∃ r ∈ log, keyIndexOnLayer r.1.leafIndex l = e ∧ msg = layerMsg v r.1 l ∧
      v.layerSignature H l e msg (layerBase v r.1 l) = some part := by
  obtain ⟨x, E, hx, hQm, hQc, hEeq, hQl, hQt, hroot⟩ := layerRoot_spec hQ hr
  obtain ⟨hleaf, hpath⟩ := path_meet hnb hQt hroot
  -- The leaf: the forged chain ends are the honest ones.
  have hE : E = v.endpoints l e := by
    by_contra hne
    apply hnb
    refine mem_badQ_of_struct hQl (slotOf_cell _ (by trivial) _) (fun _ _ h ↦ by cases h)
      (rfl : QTable.honCell S0 v (.leaf l e) =
        some (cellOf S0 (.leaf l e) v, truncateHash (v (.leaf l e))))
      (hleaf.trans (truncateHash_leaf v l e).symm) ?_
    rintro ⟨hc, -⟩
    exact hne (cell_payload_inj (by trivial) hc).symm
  -- The chains: the forged values are honest, and the honest cells leaving them hardwired.
  have hchain : ∀ i, part.chainValues i = v.chainValue l e i (x i).val ∧
      ∀ h : (x i).val < chainLength - 1,
        (s.2.1.1 (cellOf S0 (.chain l e i ⟨(x i).val, h⟩) v)).isSome := by
    intro i
    have hEi : E i = v.chainValue l e i (chainLength - 1) := congrFun hE i
    rw [hEeq i] at hEi
    by_cases h3 : (x i).val < chainLength - 1
    · have hsum : (x i).val + (chainLength - 1 - (x i).val) = chainLength - 1 := by omega
      exact chain_meet hnb (a := (x i).val) (n := chainLength - 1 - (x i).val) (by omega)
        (by omega) (hQc i) (hEi.trans (congrArg (v.chainValue l e i) hsum.symm))
    · have h3' : (x i).val = chainLength - 1 := by have := (x i).isLt; omega
      refine ⟨?_, fun h ↦ absurd h h3⟩
      have hv : (ev (viewH (unionH s))) (Over.recoverChain hashQ v.param l e i (x i)
          (part.chainValues i)) = part.chainValues i := by
        show (ev (viewH (unionH s))) (Over.chainWalk hashQ v.param l e i (x i).val
          (chainLength - 1 - (x i).val) (part.chainValues i)) = _
        rw [h3', Nat.sub_self]
        rfl
      exact hv.symm.trans (hEi.trans (congrArg (v.chainValue l e i) h3'.symm))
  -- A hardwired step is known: a signature by the same key opened its chain at or below it.
  have hknown : ∀ i (h : (x i).val < chainLength - 1),
      Known (v.disclosures H (log.map Sigma.fst)) (.chain l e i (x i).val) :=
    fun i h ↦ hEx l e i ⟨(x i).val, h⟩ ((hchain i).2 h)
  have hvx := Quantum.Xmss.Codeword.sum_eq_of_decode hx
  obtain ⟨i0, hi0⟩ := Quantum.Xmss.Codeword.exists_lt_of_sum hvx
  obtain ⟨req, hreq, hkey, sel, hsel, -⟩ := exists_signed_of_known (hknown i0 hi0)
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hreq
  have hle : ∀ i, sel.2 i ≤ x i := by
    intro i
    by_cases h : (x i).val < chainLength - 1
    · obtain ⟨req', hreq', hkey', sel', hsel', hj⟩ := exists_signed_of_known (hknown i h)
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hreq'
      obtain ⟨hm1, hm2⟩ := layer_eq_of_key (v := v) hvalid hr hr' (hkey.trans hkey'.symm)
      rw [hm1, hm2, hsel'] at hsel
      obtain rfl := Option.some.inj hsel
      exact hj
    · show (sel.2 i).val ≤ (x i).val
      have := (sel.2 i).isLt
      omega
  -- Incomparability: the forged word is the selected one.
  have hvs := decode_of_select hsel
  have hxs : sel.2 = x :=
    Quantum.Xmss.Codeword.eq_of_le (Quantum.Xmss.Codeword.sum_eq_of_decode hvs) hvx hle
  -- The message-digest cell is the selected one, or an Enc hit.
  have hmeq : cell v.param (.msg l e) (msg, part.randomizer) =
      cell v.param (.msg l e) (layerMsg v r.1 l, sel.1) := by
    by_contra hne
    apply hnb
    have hMr := hM r hr l sel (by rw [hkey]; exact hsel)
    rw [hkey] at hMr
    exact mem_badQ_of_enc hQm (slotOf_cell _ (by trivial) _) hMr (Ne.symm hne)
      (Quantum.Xmss.Codeword.eq_of_decode hx (hxs ▸ hvs))
  obtain ⟨hmsgEq, hρ⟩ := Prod.mk.inj (cell_payload_inj (by trivial) hmeq)
  refine ⟨r, hr, hkey, hmsgEq, ?_⟩
  have hcv : (fun i ↦ v.chainValue l e i (sel.2 i).val) = part.chainValues :=
    funext fun i ↦ by rw [hxs]; exact (hchain i).1.symm
  rw [hmsgEq, QTable.layerSignature, hsel, Option.map_some, hcv, ← hρ, ← hpath]

/-- **A win is in the event**: a forgery that verifies with every hashed cell recorded or
hardwired, against a valid transcript of honest signatures and not returned by the signer, puts
the state in `BadQ`, when every hardwired honest chain cell has a known input and the memory
records the signer's selections. -/
theorem win_imp_badQ (S0 : MasterSeed) (v : QTable) (H : HashDomain → HashOutput)
    (s : RomReg HashDomain HashOutput SelMem) (log : QueryLog SigningOracleSpec)
    (forgery : Forgery) (hlog : ∀ r ∈ log, r.2 = v.signature H r.1)
    (hM : ∀ r ∈ log, Records v H s.2.2 r.1) (hEx : HwKnown S0 v H s (log.map Sigma.fst))
    (hwin : SigningTranscript.NoLeafIndexReused log ∧
      ¬Common.SufCma.SignerReturnedForgery SigningRequest.message log forgery.message
        forgery.signature)
    (hverify : (honestEval (viewH (unionH s)) (xmssRom.verify v.publicKey forgery)).1 = true)
    (hreads : ∀ c ∈ (honestEval (viewH (unionH s)) (xmssRom.verify v.publicKey forgery)).2,
      (unionH s c).isSome) :
    s ∈ BadQ (QTable.honCell S0 v) := by
  by_contra hnb
  have hv : (ev (viewH (unionH s)))
      (Over.verify hashQ v.publicKey forgery.message forgery.signature) = true := hverify
  have hq : QueriesSatisfy (romAnswers (viewH (unionH s))) (ReadBy (unionH s))
      (Over.verify hashQ v.publicKey forgery.message forgery.signature) :=
    readBy_of_honestEval hreads
  set idx := forgery.signature.leafIndex
  simp only [Over.verify, evalWithAnswerFn_bind] at hv
  simp only [Over.verify] at hq
  obtain ⟨hqb, hq⟩ := queriesSatisfy_bind_iff.1 hq
  split at hv
  · next R hb =>
    rw [hb] at hq
    dsimp only at hq hv
    rw [evalWithAnswerFn_bind] at hv
    obtain ⟨hqt, -⟩ := queriesSatisfy_bind_iff.1 hq
    split at hv
    · next R' ht =>
      simp only [evalWithAnswerFn_pure, decide_eq_true_eq] at hv
      -- The top layer: a signed top key's layer, on the honest bottom root.
      have hlt : (keyIndexOnLayer idx topLayer).val < 2 ^ layerHeight :=
        QTable.keyIndexOnLayer_top_lt idx
      have hdiv1 : (keyIndexOnLayer idx topLayer).val / 2 ^ layerHeight = 0 :=
        Nat.div_eq_of_lt hlt
      have hrt : (ev (viewH (unionH s))) (Over.layerRoot hashQ v.param topLayer
          (keyIndexOnLayer idx topLayer) (rootBytes R).1 (forgery.signature.layers topLayer)) =
          some (v.treeValue topLayer layerHeight
            ((keyIndexOnLayer idx topLayer).val / 2 ^ layerHeight)) := by
        rw [hdiv1]
        exact ht.trans (congrArg some hv)
      obtain ⟨r1, hr1, hkey1, hmsg1, hsig1⟩ :=
        layer_meet (msg := rootBytes R) hM hEx hwin.1 hnb hqt hrt
      rw [layerMsg_top] at hmsg1
      have hR : R = v.bottomRoot idx := by
        have h1 : R = v.bottomRoot r1.1.leafIndex :=
          littleEndianBytes_inj (n := 16) (congrArg Subtype.val hmsg1)
        rw [h1, QTable.bottomRoot, QTable.bottomRoot, hkey1]
      -- The bottom layer: a signed request's layer, on the forged message.
      have hdiv0 : (keyIndexOnLayer idx bottomLayer).val / 2 ^ layerHeight =
          (keyIndexOnLayer idx topLayer).val := by
        simp [keyIndexOnLayer, bottomLayer, topLayer, layerHeight]
      have hrb : (ev (viewH (unionH s))) (Over.layerRoot hashQ v.param bottomLayer
          (keyIndexOnLayer idx bottomLayer) (messageBytes forgery.message).1
          (forgery.signature.layers bottomLayer)) =
          some (v.treeValue bottomLayer layerHeight
            ((keyIndexOnLayer idx bottomLayer).val / 2 ^ layerHeight)) := by
        rw [hdiv0]
        exact hb.trans (congrArg some hR)
      obtain ⟨r0, hr0, hkey0, hmsg0, hsig0⟩ :=
        layer_meet (msg := messageBytes forgery.message) hM hEx hwin.1 hnb hqb hrb
      rw [layerMsg_bottom] at hmsg0
      have hidx : r0.1.leafIndex = idx := Fin.ext (by
        have := congrArg Fin.val hkey0
        simpa [keyIndexOnLayer, bottomLayer] using this)
      have hm : r0.1.message = forgery.message :=
        (littleEndianBytes_inj (n := 32) (congrArg Subtype.val hmsg0)).symm
      -- The forgery is the signature of that request.
      have hb0 : v.bottomSignature H r0.1 = some (forgery.signature.layers bottomLayer) := by
        rw [QTable.bottomSignature, hkey0, ← hmsg0, ← layerBase_bottom]
        exact hsig0
      have hk01 : keyIndexOnLayer r0.1.leafIndex topLayer =
          keyIndexOnLayer r1.1.leafIndex topLayer := by
        rw [hidx, hkey1]
      have hbase := (layer_eq_of_key (v := v) hwin.1 hr0 hr1 hk01).2
      rw [layerBase_top, layerBase_top] at hbase
      have ht0 : v.topSignature H r0.1 = some (forgery.signature.layers topLayer) := by
        rw [QTable.topSignature, hbase, hidx, ← hR, ← layerBase_top]
        exact hsig1
      have hsig : v.signature H r0.1 = some forgery.signature := by
        simp only [QTable.signature, hb0, ht0, Option.bind_some, Option.map_some]
        rw [hidx, signature_eq_layers]
      exact hwin.2 ⟨r0, hr0, hm, (hlog r0 hr0).trans hsig⟩
    · simp at hv
  · simp at hv

end Layers

end Quantum.Qrom.Xmss

end
