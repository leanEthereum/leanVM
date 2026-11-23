module

public import Quantum.Qrom.Xmss.Template
public import Quantum.Xmss.Assembly.GameTCalls
public import Common.CostCombinators

@[expose] public section

/-!
# The calls of the realized runtime-2 template game in the QROM

The QROM analog of QRPM's `Quantum.Xmss.Assembly.GameTCalls`, for `realizeT θ (gameT M upd A)`.

* **Sources** (`srcSlot`, `srcOf`): the coordinate of the hidden values a cell's input carries in
  full (the master seed's low half for the scheme seed, the scheme seed's low half for its
  derivations, the input value of a chain step, the end of chain `0` for a leaf, the left child
  for a node). `vcoord_inj`: inside the tables, distinct values have distinct coordinates.
  `mem_layerPos_of_srcOf_mem`: a layer signature reveals the source of a position's cell only if
  it programs that position; the other reveals (public key, randomizer bases, bottom root) reveal
  no source.
* **The source invariant** (`SrcInv θ`): every position whose source is revealed has its cell
  hardwired. `PendInv θ C` with pending cells `C`, `HPend` (templates keeping it: reveals add the
  cells whose source they reveal, program ports remove theirs, sponge and read calls with nothing
  pending), `hPend_gameT`; `forallQueries_gameQ`, `forallQueries_prefixQ`: Masses' `hinv` for any
  ports `Q` other than the program ports, from states with an empty memory label.
* **Charges by kind** (`tChargeQ`, `rChargeQ`: `a` per sponge call, `b` per read at a cell other
  than a message digest, `b'` per read at a message digest, `c` per program call, `d` per reveal
  or record): `chg_readsProgram` (one read per hash call), `verify_cost` (`verifyCalls = 384`),
  `chg_grindT`, `chg_signT` (`reqCallsQ`), `chg_challengeT`, composed in `chg_realizeT_gameT`
  (`gameCallsQ`). The counts: `advCalls_gameQ` (`q` sponge calls), `clsCalls_gameQ` (`clsCapQ`),
  `progCalls_gameQ` (`progCapQ`), `readQCalls_gameQ` (`verifyCalls` reads at non-digest cells),
  and `advCalls_prefixQ`, `clsCalls_prefixQ`, `progCalls_prefixQ`.
* `keepsLab_gameQ`, `keepsLab_prefixQ`: the reads keep the memory label (Mismatch's `KeepsLab`).
-/

open Matrix IPFunctor OracleComp OracleSpec
open scoped ENNReal Kronecker

universe u v w w₁

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open LeanXmss HashSig
open Quantum.Xmss (Slot leafKey leafKey_val)
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec runtimeR realizeT revealThen progThen
  readLift readLiftQ RevealVals)

/-! ## The source coordinates of the cells -/

section sources

/-- Chain `0` of a key. -/
def chain0 : ChainIndex :=
  ⟨0, by decide⟩

/-- **The source coordinate of a slot's cell**: a coordinate whose value the cell's input carries
in full. -/
def srcSlot : Slot → HPos
  | .seed => (none, false)
  | .chain l e step i => vcoord (.chain l e i step.val)
  | .leaf l e => vcoord (.chain l e chain0 (chainLength - 1))
  | .node l level index => vcoord (.tree l (level - 1) (2 * index))
  | _ => loC .seed

/-- The source coordinate of a position's cell. -/
def srcOf (p : Pos) : HPos :=
  srcSlot p.slot

/-- The symbolic position whose value carries a structural position's source. -/
def srcQ : Pos → Quantum.Xmss.Pos
  | .chain l e i step => .chain l e i step.val
  | .leaf l e => .chain l e chain0 (chainLength - 1)
  | .node l k x => .tree l k.val (2 * x.val)
  | _ => .chain bottomLayer ⟨0, by decide⟩ chain0 0

/-- The symbolic positions inside the tables: chain positions up to the end, tree values with an
index below `2^32` at level `0` and inside the tree above. -/
def VRange : Quantum.Xmss.Pos → Prop
  | .chain _ _ _ j => j < chainLength
  | .tree _ level index => level ≤ layerHeight ∧ index < 2 ^ (32 - level)

theorem vcoord_chain_zero (l : Layer) (e : KeyIndex) (i : ChainIndex) :
    vcoord (.chain l e i 0) = (some (.prf l e (chainPair i)), decide (i.val % 2 ≠ 0)) :=
  rfl

theorem vcoord_chain_succ (l : Layer) (e : KeyIndex) (i : ChainIndex) {j : ℕ}
    (h : j < chainLength - 1) : vcoord (.chain l e i (j + 1)) = loC (.chain l e i ⟨j, h⟩) :=
  dite_eq_left h

theorem vcoord_tree_zero (l : Layer) (index : ℕ) :
    vcoord (.tree l 0 index) = loC (.leaf l (leafKey index)) :=
  rfl

theorem vcoord_chain_succ_out (l : Layer) (e : KeyIndex) (i : ChainIndex) {j : ℕ}
    (h : ¬j < chainLength - 1) : vcoord (.chain l e i (j + 1)) = paramC :=
  dite_eq_right h

theorem vcoord_tree_succ_out (l : Layer) {level index : ℕ}
    (h : ¬(level < layerHeight ∧ index < 2 ^ (31 - level))) :
    vcoord (.tree l (level + 1) index) = paramC :=
  dite_eq_right h

theorem chainLength_eq : chainLength = 4 :=
  rfl

theorem layerHeight_eq : layerHeight = 16 :=
  rfl

theorem lifetime_eq : lifetime = 2 ^ 32 :=
  rfl

/-- In range, the tree's node index bound. -/
theorem tree_succ_cond {level index : ℕ} (h : level + 1 ≤ layerHeight)
    (hi : index < 2 ^ (32 - (level + 1))) : level < layerHeight ∧ index < 2 ^ (31 - level) := by
  rw [layerHeight_eq] at h
  exact ⟨by rw [layerHeight_eq]; omega, by rwa [show 31 - level = 32 - (level + 1) by omega]⟩

theorem leafKey_inj {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : leafKey a = leafKey b) :
    a = b := by
  have h' := congrArg Fin.val h
  simp only [leafKey, lifetime_eq] at h'
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

/-- **The coordinate map is injective inside the tables.** -/
theorem vcoord_inj {q q' : Quantum.Xmss.Pos} (hq : VRange q) (hq' : VRange q')
    (h : vcoord q = vcoord q') : q = q' := by
  rcases q with ⟨l, e, i, _ | j⟩ | ⟨l, _ | k, a⟩ <;>
    rcases q' with ⟨l', e', i', _ | j'⟩ | ⟨l', _ | k', a'⟩ <;>
    simp only [VRange, chainLength_eq] at hq hq'
  · rw [vcoord_chain_zero, vcoord_chain_zero] at h
    simp only [Prod.mk.injEq, Option.some.injEq, Pos.prf.injEq, chainPair, Fin.mk.injEq,
      decide_eq_decide] at h
    obtain ⟨⟨rfl, rfl, h1⟩, h2⟩ := h
    have : i = i' := Fin.ext (by omega)
    subst this
    rfl
  · rw [vcoord_chain_zero, vcoord_chain_succ l' e' i' (by rw [chainLength_eq]; omega)] at h
    simp [loC] at h
  · rw [vcoord_chain_zero, vcoord_tree_zero] at h
    simp [loC] at h
  · rw [vcoord_chain_zero, vcoord_tree_succ l' k' a' (tree_succ_cond hq'.1 hq'.2)] at h
    simp [loC] at h
  · rw [vcoord_chain_succ l e i (by rw [chainLength_eq]; omega), vcoord_chain_zero] at h
    simp [loC] at h
  · rw [vcoord_chain_succ l e i (by rw [chainLength_eq]; omega),
      vcoord_chain_succ l' e' i' (by rw [chainLength_eq]; omega)] at h
    simp only [loC, Prod.mk.injEq, Option.some.injEq, Pos.chain.injEq, Fin.mk.injEq,
      and_true] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl
  · rw [vcoord_chain_succ l e i (by rw [chainLength_eq]; omega), vcoord_tree_zero] at h
    simp [loC] at h
  · rw [vcoord_chain_succ l e i (by rw [chainLength_eq]; omega),
      vcoord_tree_succ l' k' a' (tree_succ_cond hq'.1 hq'.2)] at h
    simp [loC] at h
  · rw [vcoord_tree_zero, vcoord_chain_zero] at h
    simp [loC] at h
  · rw [vcoord_tree_zero, vcoord_chain_succ l' e' i' (by rw [chainLength_eq]; omega)] at h
    simp [loC] at h
  · rw [vcoord_tree_zero, vcoord_tree_zero] at h
    simp only [loC, Prod.mk.injEq, Option.some.injEq, Pos.leaf.injEq, and_true] at h
    obtain ⟨rfl, h⟩ := h
    rw [leafKey_inj (by simpa using hq.2) (by simpa using hq'.2) h]
  · rw [vcoord_tree_zero, vcoord_tree_succ l' k' a' (tree_succ_cond hq'.1 hq'.2)] at h
    simp [loC] at h
  · rw [vcoord_tree_succ l k a (tree_succ_cond hq.1 hq.2), vcoord_chain_zero] at h
    simp [loC] at h
  · rw [vcoord_tree_succ l k a (tree_succ_cond hq.1 hq.2),
      vcoord_chain_succ l' e' i' (by rw [chainLength_eq]; omega)] at h
    simp [loC] at h
  · rw [vcoord_tree_succ l k a (tree_succ_cond hq.1 hq.2), vcoord_tree_zero] at h
    simp [loC] at h
  · rw [vcoord_tree_succ l k a (tree_succ_cond hq.1 hq.2),
      vcoord_tree_succ l' k' a' (tree_succ_cond hq'.1 hq'.2)] at h
    simp only [loC, Prod.mk.injEq, Option.some.injEq, Pos.node.injEq, and_true] at h
    obtain ⟨rfl, hk, ha⟩ := h
    obtain rfl : k = k' := congrArg Fin.val hk
    obtain rfl : a = a' := congrArg Fin.val (eq_of_heq ha)
    rfl

/-- Inside the tables the coordinate is not the parameter's. -/
theorem vcoord_ne_paramC {q : Quantum.Xmss.Pos} (hq : VRange q) : vcoord q ≠ paramC := by
  rcases q with ⟨l, e, i, _ | j⟩ | ⟨l, _ | k, a⟩ <;> simp only [VRange, chainLength_eq] at hq
  · simp [vcoord_chain_zero, paramC, loC]
  · rw [vcoord_chain_succ l e i (by rw [chainLength_eq]; omega)]
    simp [paramC, loC]
  · simp [vcoord_tree_zero, paramC, loC]
  · rw [vcoord_tree_succ l k a (tree_succ_cond hq.1 hq.2)]
    simp [paramC, loC]

/-- A coordinate of a value is a value's half, never a master-seed half. -/
theorem vcoord_fst_ne_none (q : Quantum.Xmss.Pos) : (vcoord q).1 ≠ none := by
  rcases q with ⟨l, e, i, _ | j⟩ | ⟨l, _ | k, a⟩
  · simp [vcoord_chain_zero]
  · by_cases hj : j < chainLength - 1
    · simp [vcoord_chain_succ l e i hj, loC]
    · simp [vcoord_chain_succ_out l e i hj, paramC, loC]
  · simp [vcoord_tree_zero, loC]
  · by_cases hk : k < layerHeight ∧ a < 2 ^ (31 - k)
    · simp [vcoord_tree_succ l k a hk, loC]
    · simp [vcoord_tree_succ_out l hk, paramC, loC]

/-- The coordinates of values are halves of chain-start derivations, chain steps, leaves, nodes
or the parameter. -/
theorem vcoord_eq_loC {q : Quantum.Xmss.Pos} {r : Pos} (h : vcoord q = loC r) :
    r = .param ∨ (∃ l e t, r = .prf l e t) ∨ r.IsStruct := by
  rcases q with ⟨l, e, i, _ | j⟩ | ⟨l, _ | k, a⟩
  · rw [vcoord_chain_zero] at h
    simp only [loC, Prod.mk.injEq, Option.some.injEq] at h
    exact .inr (.inl ⟨l, e, _, h.1.symm⟩)
  · by_cases hj : j < chainLength - 1
    · rw [vcoord_chain_succ l e i hj] at h
      simp only [loC, Prod.mk.injEq, Option.some.injEq, and_true] at h
      exact .inr (.inr (h ▸ trivial))
    · rw [vcoord_chain_succ_out l e i hj] at h
      simp only [paramC, loC, Prod.mk.injEq, Option.some.injEq, and_true] at h
      exact .inl h.symm
  · rw [vcoord_tree_zero] at h
    simp only [loC, Prod.mk.injEq, Option.some.injEq, and_true] at h
    exact .inr (.inr (h ▸ trivial))
  · by_cases hk : k < layerHeight ∧ a < 2 ^ (31 - k)
    · rw [vcoord_tree_succ l k a hk] at h
      simp only [loC, Prod.mk.injEq, Option.some.injEq, and_true] at h
      exact .inr (.inr (h ▸ trivial))
    · rw [vcoord_tree_succ_out l hk] at h
      simp only [paramC, loC, Prod.mk.injEq, Option.some.injEq, and_true] at h
      exact .inl h.symm

/-- A high half is the coordinate of a value only for a chain-start derivation. -/
theorem vcoord_eq_hiC {q : Quantum.Xmss.Pos} {r : Pos} (h : vcoord q = hiC r) :
    ∃ l e t, r = .prf l e t := by
  rcases q with ⟨l, e, i, _ | j⟩ | ⟨l, _ | k, a⟩
  · rw [vcoord_chain_zero] at h
    simp only [hiC, Prod.mk.injEq, Option.some.injEq] at h
    exact ⟨l, e, _, h.1.symm⟩
  · by_cases hj : j < chainLength - 1
    · rw [vcoord_chain_succ l e i hj] at h
      simp [hiC, loC] at h
    · rw [vcoord_chain_succ_out l e i hj] at h
      simp [hiC, loC, paramC] at h
  · simp [vcoord_tree_zero, hiC, loC] at h
  · by_cases hk : k < layerHeight ∧ a < 2 ^ (31 - k)
    · rw [vcoord_tree_succ l k a hk] at h
      simp [hiC, loC] at h
    · rw [vcoord_tree_succ_out l hk] at h
      simp [hiC, loC, paramC] at h

theorem isStruct_chain (l : Layer) (e : KeyIndex) (i : ChainIndex) (step : ChainStep) :
    (Pos.chain l e i step).IsStruct :=
  trivial

theorem srcOf_struct {p : Pos} (hp : p.IsStruct) : srcOf p = vcoord (srcQ p) := by
  cases p with
  | chain => rfl
  | leaf => rfl
  | node l k x => simp only [srcOf, srcSlot, Pos.slot, srcQ, Nat.add_sub_cancel]
  | seed | param | prf | rndBottom | rndTop => exact absurd hp id

theorem vRange_srcQ {p : Pos} (hp : p.IsStruct) : VRange (srcQ p) := by
  cases p with
  | chain l e i step =>
    simp only [srcQ, VRange]
    exact step.isLt.trans (by decide)
  | leaf => simp only [srcQ, VRange]; decide
  | node l k x =>
    simp only [srcQ, VRange]
    have hk : k.val < 16 := k.isLt
    have hx := x.isLt
    refine ⟨k.isLt.le, ?_⟩
    rw [show 32 - k.val = 31 - k.val + 1 by omega, pow_succ]
    omega
  | seed | param | prf | rndBottom | rndTop => exact absurd hp id

/-- The non-structural positions' sources: the master seed's or the scheme seed's low half. -/
theorem srcOf_of_not_struct {p : Pos} (hp : ¬p.IsStruct) :
    srcOf p = (none, false) ∨ srcOf p = loC .seed := by
  cases p with
  | seed => exact .inl rfl
  | param | prf | rndBottom | rndTop => exact .inr rfl
  | chain | leaf | node => exact absurd trivial hp

/-- **A source that is a value's coordinate inside the tables names the position.** -/
theorem srcQ_eq_of_srcOf_eq {p : Pos} {w : Quantum.Xmss.Pos} (hw : VRange w)
    (h : srcOf p = vcoord w) : p.IsStruct ∧ srcQ p = w := by
  by_cases hp : p.IsStruct
  · exact ⟨hp, vcoord_inj (vRange_srcQ hp) hw ((srcOf_struct hp).symm.trans h)⟩
  · rcases srcOf_of_not_struct hp with h' | h' <;> rw [h'] at h
    · exact absurd (congrArg Prod.fst h).symm (vcoord_fst_ne_none w)
    · rcases vcoord_eq_loC h.symm with h1 | ⟨_, _, _, h1⟩ | h1
      · cases h1
      · cases h1
      · exact absurd h1 id

theorem srcOf_ne_paramC (p : Pos) : srcOf p ≠ paramC := by
  by_cases hp : p.IsStruct
  · rw [srcOf_struct hp]
    exact vcoord_ne_paramC (vRange_srcQ hp)
  · rcases srcOf_of_not_struct hp with h | h <;> rw [h] <;> simp [paramC, loC]

theorem srcQ_eq_chain {p : Pos} (hp : p.IsStruct) {l : Layer} {e : KeyIndex} {i : ChainIndex}
    {j : ℕ} (h : srcQ p = .chain l e i j) :
    (∃ s : ChainStep, s.val = j ∧ p = .chain l e i s) ∨
      (j = chainLength - 1 ∧ i = chain0 ∧ p = .leaf l e) := by
  cases p with
  | chain l' e' i' s =>
    simp only [srcQ, Quantum.Xmss.Pos.chain.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact .inl ⟨s, rfl, rfl⟩
  | leaf l' e' =>
    simp only [srcQ, Quantum.Xmss.Pos.chain.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact .inr ⟨rfl, rfl, rfl⟩
  | node => simp [srcQ] at h
  | seed | param | prf | rndBottom | rndTop => exact absurd hp id

theorem srcQ_eq_tree {p : Pos} (hp : p.IsStruct) {l : Layer} {k idx : ℕ}
    (h : srcQ p = .tree l k idx) :
    ∃ (k' : Fin layerHeight) (x' : Fin (2 ^ (31 - k'.val))), k'.val = k ∧ 2 * x'.val = idx ∧
      p = .node l k' x' := by
  cases p with
  | node l' k' x' =>
    simp only [srcQ, Quantum.Xmss.Pos.tree.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨k', x', rfl, rfl, rfl⟩
  | chain => simp [srcQ] at h
  | leaf => simp [srcQ] at h
  | seed | param | prf | rndBottom | rndTop => exact absurd hp id

theorem mem_layerPos_chain {l : Layer} {e : KeyIndex} {x : Encoding} {i : ChainIndex}
    {step : ChainStep} (h : (x i).val ≤ step.val) : Pos.chain l e i step ∈ layerPos l e x :=
  List.mem_append_left _ (List.mem_flatMap.2 ⟨i, List.mem_finRange _, List.mem_map.2
    ⟨step, List.mem_filter.2 ⟨List.mem_finRange _, by simpa using h⟩, rfl⟩⟩)

theorem mem_layerPos_leaf (l : Layer) (e : KeyIndex) (x : Encoding) :
    Pos.leaf l e ∈ layerPos l e x :=
  List.mem_append_right _ List.mem_cons_self

theorem mem_layerPos_pathNode (l : Layer) (e : KeyIndex) (x : Encoding) (lev : Fin layerHeight) :
    pathNode l e lev ∈ layerPos l e x :=
  List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨lev, List.mem_finRange _, rfl⟩))

theorem mem_layerPos_cases {l : Layer} {e : KeyIndex} {x : Encoding} {q : Pos}
    (h : q ∈ layerPos l e x) :
    (∃ (i : ChainIndex) (step : ChainStep), (x i).val ≤ step.val ∧ q = .chain l e i step) ∨
      q = .leaf l e ∨ ∃ lev, q = pathNode l e lev := by
  simp only [layerPos, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_cons, List.mem_finRange, true_and, decide_eq_true_eq] at h
  rcases h with ⟨i, step, hs, rfl⟩ | rfl | ⟨lev, rfl⟩
  · exact .inl ⟨i, step, hs, rfl⟩
  · exact .inr (.inl rfl)
  · exact .inr (.inr ⟨lev, rfl⟩)

theorem node_mem_layerPos {l : Layer} {e : KeyIndex} (x : Encoding) {k : Fin layerHeight}
    {y : Fin (2 ^ (31 - k.val))} (h : y.val = e.val / 2 ^ (k.val + 1)) :
    Pos.node l k y ∈ layerPos l e x := by
  have he : Pos.node l k y = pathNode l e k := by
    simp only [pathNode, Pos.node.injEq, heq_eq_eq, true_and]
    exact Fin.ext h
  rw [he]
  exact mem_layerPos_pathNode l e x k

theorem exists_of_mem_needUnion {c : HPos} :
    ∀ {ps : List Pos}, c ∈ needUnion ps → ∃ q ∈ ps, c ∈ progNeed q
  | [], h => absurd h (Finset.notMem_empty c)
  | q :: _, h => (Finset.mem_union.1 h).elim (fun h ↦ ⟨q, List.mem_cons_self, h⟩) fun h ↦
      let ⟨q', hq', h'⟩ := exists_of_mem_needUnion h
      ⟨q', List.mem_cons_of_mem _ hq', h'⟩

theorem pow_thirtyTwo_sub {lev : ℕ} (h : lev < 16) : 2 ^ (32 - lev) = 2 * 2 ^ (31 - lev) := by
  rw [show 32 - lev = 31 - lev + 1 by omega, pow_succ, mul_comm]

theorem div_pow_lt (e : KeyIndex) (lev : ℕ) (h : lev ≤ 32) : e.val / 2 ^ lev < 2 ^ (32 - lev) := by
  have he : e.val < 2 ^ 32 := e.isLt
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel h]
  exact he

/-- A position whose source the coordinate of a chain position `j` of key `e` (at most the
opened position `x i` onwards) carries is a layer signature's position. -/
theorem mem_layerPos_of_chain {l : Layer} {e : KeyIndex} {x : Encoding} {p : Pos} {i : ChainIndex}
    {j : ℕ} (hj : j < chainLength) (hxj : (x i).val ≤ j) (h : srcOf p = vcoord (.chain l e i j)) :
    p ∈ layerPos l e x := by
  obtain ⟨hp, hq⟩ := srcQ_eq_of_srcOf_eq (w := .chain l e i j) hj h
  rcases srcQ_eq_chain hp hq with ⟨s, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact mem_layerPos_chain hxj
  · exact mem_layerPos_leaf l e x

/-- **A layer signature reveals the source of a position's cell only if it programs that
position.** -/
theorem mem_layerPos_of_srcOf_mem {l : Layer} {e : KeyIndex} {x : Encoding} {p : Pos}
    (h : srcOf p ∈ layerReveal l e x) : p ∈ layerPos l e x := by
  have hC : chainLength = 4 := rfl
  have hH : layerHeight = 16 := rfl
  simp only [layerReveal, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
  rcases h with (hn | ⟨i, hi⟩) | ⟨lev, hl⟩
  · obtain ⟨q, hq, hc⟩ := exists_of_mem_needUnion hn
    simp only [progNeed, cellNeed, Finset.mem_union, Finset.mem_insert, Finset.mem_image,
      Finset.mem_singleton] at hc
    rcases hc with (hc | ⟨w, hw, hc⟩) | hc | hc
    · exact absurd hc (srcOf_ne_paramC p)
    · rcases mem_layerPos_cases hq with ⟨i, s, hs, rfl⟩ | rfl | ⟨lev, rfl⟩
      · simp only [cellDeps, Finset.mem_singleton] at hw
        subst hw
        exact mem_layerPos_of_chain (by have := s.isLt; omega) hs hc.symm
      · simp only [cellDeps, Finset.mem_image, Finset.mem_univ, true_and] at hw
        obtain ⟨i, rfl⟩ := hw
        obtain ⟨hp, hq⟩ := srcQ_eq_of_srcOf_eq (w := .chain l e i (chainLength - 1))
          (by show chainLength - 1 < chainLength; omega) hc.symm
        rcases srcQ_eq_chain hp hq with ⟨s, hs, rfl⟩ | ⟨-, -, rfl⟩
        · have := s.isLt
          omega
        · exact mem_layerPos_leaf l e x
      · have hlev : lev.val < 16 := lev.isLt
        have hb := nodeIndex_lt e lev
        have hp32 := pow_thirtyTwo_sub hlev
        simp only [pathNode, cellDeps, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · obtain ⟨hp, hq⟩ := srcQ_eq_of_srcOf_eq
            (w := .tree l lev.val (2 * (e.val / 2 ^ (lev.val + 1))))
            ⟨by omega, by omega⟩ hc.symm
          obtain ⟨k', y, hk, hy, rfl⟩ := srcQ_eq_tree hp hq
          obtain rfl : k' = lev := Fin.ext hk
          exact node_mem_layerPos x (by omega)
        · obtain ⟨hp, hq⟩ := srcQ_eq_of_srcOf_eq
            (w := .tree l lev.val (2 * (e.val / 2 ^ (lev.val + 1)) + 1))
            ⟨by omega, by omega⟩ hc.symm
          obtain ⟨k', y, hk, hy, rfl⟩ := srcQ_eq_tree hp hq
          omega
    · rcases mem_layerPos_cases hq with ⟨i, s, hs, rfl⟩ | rfl | ⟨lev, rfl⟩
      · rw [← vcoord_chain_succ l e i s.isLt] at hc
        exact mem_layerPos_of_chain (by have := s.isLt; omega) (by omega) hc
      · have he : e.val < 2 ^ 32 := e.isLt
        rw [show loC (Pos.leaf l e) = vcoord (.tree l 0 e.val) by
          rw [vcoord_tree_zero, leafKey_val]] at hc
        obtain ⟨hp, hq⟩ := srcQ_eq_of_srcOf_eq (w := .tree l 0 e.val) ⟨by omega, by simpa using he⟩
          hc
        obtain ⟨k', y, hk, hy, rfl⟩ := srcQ_eq_tree hp hq
        have h2 : e.val / 2 ^ (k'.val + 1) = e.val / 2 := by rw [hk]; rfl
        exact node_mem_layerPos x (by rw [h2]; omega)
      · have hlev : lev.val < 16 := lev.isLt
        have hb := nodeIndex_lt e lev
        rw [pathNode, ← vcoord_tree_succ l lev.val _ ⟨lev.isLt, hb⟩] at hc
        obtain ⟨hp, hq⟩ := srcQ_eq_of_srcOf_eq (w := .tree l (lev.val + 1) _)
          ⟨by omega, by rwa [show 32 - (lev.val + 1) = 31 - lev.val by omega]⟩ hc
        obtain ⟨k', y, hk, hy, rfl⟩ := srcQ_eq_tree hp hq
        have h2 : e.val / 2 ^ (k'.val + 1) = e.val / 2 ^ (lev.val + 1) / 2 := by
          rw [hk, pow_succ, ← Nat.div_div_eq_div_mul]
        exact node_mem_layerPos x (by rw [h2]; omega)
    · exfalso
      have hq' := isStruct_of_mem_layerPos hq
      by_cases hp : p.IsStruct
      · rw [srcOf_struct hp] at hc
        obtain ⟨_, _, _, rfl⟩ := vcoord_eq_hiC hc
        exact hq'
      · rcases srcOf_of_not_struct hp with h' | h' <;> rw [h'] at hc <;> simp [hiC, loC] at hc
  · exact mem_layerPos_of_chain (x i).isLt le_rfl hi.symm
  · have hlev : lev.val < 16 := lev.isLt
    have hn := div_pow_lt e lev.val (by omega)
    have hp32 := pow_thirtyTwo_sub hlev
    have hx := Quantum.Xmss.xor_one_div_two (e.val / 2 ^ lev.val)
    obtain ⟨hp, hq⟩ := srcQ_eq_of_srcOf_eq
      (w := .tree l lev.val (Nat.xor (e.val / 2 ^ lev.val) 1)) ⟨by omega, by omega⟩ hl.symm
    obtain ⟨k', y, hk, hy, rfl⟩ := srcQ_eq_tree hp hq
    obtain rfl : k' = lev := Fin.ext hk
    refine node_mem_layerPos x ?_
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    omega

/-- A tree value above the trees' top level is no source. -/
theorem srcOf_ne_vcoord_top (l : Layer) {idx : ℕ} (h : idx < 2 ^ (32 - layerHeight)) (p : Pos) :
    srcOf p ≠ vcoord (.tree l layerHeight idx) := by
  intro hp
  obtain ⟨hs, hq⟩ := srcQ_eq_of_srcOf_eq (w := .tree l layerHeight idx) ⟨le_rfl, h⟩ hp
  obtain ⟨k', y, hk, -, -⟩ := srcQ_eq_tree hs hq
  have := k'.isLt
  omega

theorem loC_rootPos : loC rootPos = vcoord (.tree topLayer layerHeight 0) :=
  (vcoord_tree_succ topLayer 15 0 (by decide)).symm

/-- The public key's coordinates are no source. -/
theorem srcOf_not_mem_pkReveal (p : Pos) : srcOf p ∉ pkReveal := by
  simp only [pkReveal, Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨srcOf_ne_paramC p, ?_⟩
  rw [loC_rootPos]
  exact srcOf_ne_vcoord_top topLayer (by decide) p

/-- The bottom root's coordinate is no source. -/
theorem srcOf_not_mem_rootReveal (r : SigningRequest) (p : Pos) : srcOf p ∉ rootReveal r := by
  simp only [rootReveal, Finset.mem_singleton]
  exact srcOf_ne_vcoord_top bottomLayer (QTable.keyIndexOnLayer_top_lt r.leafIndex) p

/-- The low half of a position other than the parameter, the seed, a chain-start derivation or a
structural position is no source. -/
theorem srcOf_ne_loC {r : Pos} (h1 : r ≠ .seed) (h2 : r ≠ .param)
    (h3 : ∀ l e t, r ≠ .prf l e t) (h4 : ¬r.IsStruct) (p : Pos) : srcOf p ≠ loC r := by
  intro hp
  by_cases hs : p.IsStruct
  · rw [srcOf_struct hs] at hp
    rcases vcoord_eq_loC hp with h | ⟨l, e, t, h⟩ | h
    · exact h2 h
    · exact h3 l e t h
    · exact h4 h
  · rcases srcOf_of_not_struct hs with h | h <;> rw [h] at hp
    · simp [loC] at hp
    · simp only [loC, Prod.mk.injEq, Option.some.injEq, and_true] at hp
      exact h1 hp.symm

theorem srcOf_ne_loC_rndBottom (e : KeyIndex) (m : Message) (p : Pos) :
    srcOf p ≠ loC (.rndBottom e m) :=
  srcOf_ne_loC (by simp) (by simp) (fun _ _ _ h ↦ Pos.noConfusion h) id p

theorem srcOf_ne_loC_rndTop (e : KeyIndex) (d : Digest) (p : Pos) :
    srcOf p ≠ loC (.rndTop e d) :=
  srcOf_ne_loC (by simp) (by simp) (fun _ _ _ h ↦ Pos.noConfusion h) id p

end sources

/-! ## The source invariant -/

section pending

variable {M : Type}

/-- **The source invariant** at the hidden values `θ`: every position whose source coordinate is
revealed has its cell hardwired. -/
def SrcInv (θ : HPos → Digest) (r : HwReg HashOutput HashDomain (Finset HPos × M)) : Prop :=
  ∀ p, srcOf p ∈ r.2.2.1 → r.2.1.1 (cellOf (seedOf θ) p (tabOf θ)) ≠ none

/-- **The source invariant with pending cells `C`**: a position whose source is revealed has its
cell hardwired or pending. -/
def PendInv (θ : HPos → Digest) (C : Set HashDomain)
    (r : HwReg HashOutput HashDomain (Finset HPos × M)) : Prop :=
  ∀ p, srcOf p ∈ r.2.2.1 →
    r.2.1.1 (cellOf (seedOf θ) p (tabOf θ)) ≠ none ∨ cellOf (seedOf θ) p (tabOf θ) ∈ C

/-- The cells whose source a reveal of `T` reveals. -/
def revealCells (θ : HPos → Digest) (T : Finset HPos) : Set HashDomain :=
  {z | ∃ p, srcOf p ∈ T ∧ cellOf (seedOf θ) p (tabOf θ) = z}

/-- The `h`-cell a program port hardwires. -/
def progCellH : HwProg HashOutput HashDomain → Set HashDomain
  | .programH z _ => {z}
  | _ => ∅

variable {θ : HPos → Digest}

theorem pendInv_mono {C C' : Set HashDomain} (h : C ⊆ C')
    {r : HwReg HashOutput HashDomain (Finset HPos × M)} (hr : PendInv θ C r) :
    PendInv θ C' r :=
  fun p hp ↦ (hr p hp).imp_right fun hc ↦ h hc

theorem pendInv_of_eq {C : Set HashDomain} {r r' : HwReg HashOutput HashDomain (Finset HPos × M)}
    (h1 : r'.2.1 = r.2.1) (h2 : r'.2.2.1 = r.2.2.1) (hr : PendInv θ C r) : PendInv θ C r' := by
  intro p hp
  rw [h1]
  exact hr p (h2 ▸ hp)

theorem pendInv_of_label_empty {C : Set HashDomain}
    {r : HwReg HashOutput HashDomain (Finset HPos × M)} (h : r.2.2.1 = ∅) : PendInv θ C r := by
  intro p hp
  rw [h] at hp
  exact absurd hp (Finset.notMem_empty _)

theorem progUpdate_ne_none (c : HwProg HashOutput HashDomain) (W : Hw HashOutput HashDomain)
    {z : HashDomain} (h : W.1 z ≠ none ∨ z ∈ progCellH c) : (progUpdate c W).1 z ≠ none := by
  cases c with
  | programH z' a =>
    rcases h with h | h
    · exact Quantum.Xmss.Assembly.update_some_ne_none_of z' a h
    · rw [Set.mem_singleton_iff.mp h]
      exact Quantum.Xmss.Assembly.update_some_ne_none W.1 z' a
  | programK => exact h.resolve_right (Set.notMem_empty _)
  | programK' => exact h.resolve_right (Set.notMem_empty _)

/-- A program port hardwires its cell and keeps the others: it leaves the pending set. -/
theorem pendInv_prog {C : Set HashDomain} (c : HwProg HashOutput HashDomain)
    {r r' : HwReg HashOutput HashDomain (Finset HPos × M)} (h : r'.2 = (progUpdate c r.2.1, r.2.2))
    (hr : PendInv θ C r) : PendInv θ (C \ progCellH c) r' := by
  intro p hp
  rw [h] at hp ⊢
  rcases hr p hp with hc | hc
  · exact .inl (progUpdate_ne_none c _ (.inl hc))
  · by_cases hz : cellOf (seedOf θ) p (tabOf θ) ∈ progCellH c
    · exact .inl (progUpdate_ne_none c _ (.inr hz))
    · exact .inr ⟨hc, hz⟩

/-- A reveal of `T` adds the cells whose source it reveals to the pending set. -/
theorem pendInv_reveal {C : Set HashDomain} (T : Finset HPos)
    {r r' : HwReg HashOutput HashDomain (Finset HPos × M)}
    (h : r'.2 = (r.2.1, (r.2.2.1 ∪ T, r.2.2.2))) (hr : PendInv θ C r) :
    PendInv θ (C ∪ revealCells θ T) r' := by
  intro p hp
  rw [h] at hp ⊢
  rcases Finset.mem_union.1 hp with hp | hp
  · exact (hr p hp).imp_right Or.inl
  · exact .inr (.inr ⟨p, hp, rfl⟩)

theorem srcInv_of_pendInv {r : HwReg HashOutput HashDomain (Finset HPos × M)}
    (h : PendInv θ ∅ r) : SrcInv θ r :=
  fun p hp ↦ (h p hp).resolve_right (Set.notMem_empty _)

variable (θ)

theorem revealCells_pkReveal : revealCells θ pkReveal ⊆ ∅ := by
  rintro z ⟨p, hp, -⟩
  exact srcOf_not_mem_pkReveal p hp

theorem revealCells_rootReveal (r : SigningRequest) : revealCells θ (rootReveal r) ⊆ ∅ := by
  rintro z ⟨p, hp, -⟩
  exact srcOf_not_mem_rootReveal r p hp

theorem revealCells_rndBottom (e : KeyIndex) (m : Message) :
    revealCells θ {loC (.rndBottom e m)} ⊆ ∅ := by
  rintro z ⟨p, hp, -⟩
  exact srcOf_ne_loC_rndBottom e m p (Finset.mem_singleton.mp hp)

theorem revealCells_rndTop (e : KeyIndex) (d : Digest) :
    revealCells θ {loC (.rndTop e d)} ⊆ ∅ := by
  rintro z ⟨p, hp, -⟩
  exact srcOf_ne_loC_rndTop e d p (Finset.mem_singleton.mp hp)

/-- The cells a layer signature's reveal makes pending are those it programs. -/
theorem revealCells_layerReveal (l : Layer) (e : KeyIndex) (x : Encoding) :
    revealCells θ (layerReveal l e x) ⊆
      {z | ∃ q ∈ layerPos l e x, z ∈ progCellH ((progT q).realize θ)} := by
  rintro z ⟨p, hp, rfl⟩
  have hq := mem_layerPos_of_srcOf_mem hp
  refine ⟨p, hq, ?_⟩
  rw [realize_progT (isStruct_of_mem_layerPos hq) (seedOf θ) θ]
  exact Set.mem_singleton _

end pending

/-! ## Templates that keep the source invariant

`HPend θ y C C'`: run from states on the pending invariant `C`, the template `y` calls the sponge,
read and reveal ports with nothing pending, its reads keep the label, a program port leaves the
pending set, a reveal of `T` adds the cells whose source it reveals; it ends on `C'`. -/

section hp

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- A read port whose memory update keeps the memory label. -/
def LabKeepQ : HwRead HashOutput HashDomain (Finset HPos × M) → Prop
  | .readH _ u => ∀ m o, (u m o).1 = m.1
  | .readK _ u => ∀ m o, (u m o).1 = m.1
  | .readK' _ u => ∀ m o, (u m o).1 = m.1

omit [Fintype M] [DecidableEq M] in
theorem labKeepQ_liftRead (c : HwRead HashOutput HashDomain M) :
    LabKeepQ (Quantum.Xmss.Assembly.liftRead (S := HPos) c) := by
  cases c <;> intro _ _ <;> rfl

/-- The condition of `HPend` on the pending set before a call. -/
def portPreQ : (XSpec M).Port → Set HashDomain → Prop
  | .inl (.inl (.inl _)), C => C = ∅
  | .inl (.inl (.inr c)), C => C = ∅ ∧ LabKeepQ c.1
  | .inl (.inr _), _ => True
  | .inr _, C => C = ∅

/-- The pending set after a call. -/
def portPostQ (θ : HPos → Digest) : (XSpec M).Port → Set HashDomain → Set HashDomain
  | .inl (.inl (.inl _)), C => C
  | .inl (.inl (.inr _)), C => C
  | .inl (.inr p), C => C \ progCellH (p.1.realize θ)
  | .inr T, C => C ∪ revealCells θ T

/-- The condition before a command. -/
def cmdPreQ {A : QReg} : QuantumComp.Cmd L (XSpec M) A → Set HashDomain → Prop
  | .prim _, _ => True
  | .query i _ _, C => portPreQ i C

/-- The pending set after a command. -/
def cmdPostQ (θ : HPos → Digest) {A : QReg} :
    QuantumComp.Cmd L (XSpec M) A → Set HashDomain → Set HashDomain
  | .prim _, C => C
  | .query i _ _, C => portPostQ θ i C

/-- **A template that keeps the source invariant**, from the pending set `C` to `C'`. -/
def HPend (θ : HPos → Digest) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (XSpec M)) Ω A → Set HashDomain →
      Set HashDomain → Prop
  | _, .pure _, C, C' => C ⊆ C'
  | _, .liftBind c next, C, C' => cmdPreQ c C ∧ ∀ b, HPend θ (next b) (cmdPostQ θ c C) C'

omit [Fintype M] [DecidableEq M] in
theorem cmdPreQ_anti {A : QReg} (c : QuantumComp.Cmd L (XSpec M) A) {C D : Set HashDomain}
    (hD : D ⊆ C) (h : cmdPreQ c C) : cmdPreQ c D := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · trivial
  · exact Set.subset_empty_iff.1 (h ▸ hD)
  · exact ⟨Set.subset_empty_iff.1 (h.1 ▸ hD), h.2⟩
  · trivial
  · exact Set.subset_empty_iff.1 (h ▸ hD)

omit [Fintype M] [DecidableEq M] in
theorem cmdPostQ_mono (θ : HPos → Digest) {A : QReg} (c : QuantumComp.Cmd L (XSpec M) A)
    {C D : Set HashDomain} (hD : D ⊆ C) : cmdPostQ θ c D ⊆ cmdPostQ θ c C := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · exact hD
  · exact hD
  · exact hD
  · exact Set.sdiff_subset_sdiff_left hD
  · exact Set.union_subset_union_left _ hD

variable (θ : HPos → Digest)

omit [Fintype M] [DecidableEq M] in
theorem hPend_mono {A : QReg} (y : IFreeM (QuantumComp.toIPFunctor L (XSpec M)) Ω A)
    {C C' D D' : Set HashDomain} (hy : HPend θ y C C') (hD : D ⊆ C) (hD' : C' ⊆ D') :
    HPend θ y D D' := by
  induction y using IFreeM.inductionOn generalizing C D with
  | pure _ _ => exact hD.trans (hy.trans hD')
  | liftBind _ c next ih =>
    exact ⟨cmdPreQ_anti c hD hy.1, fun b ↦ ih b (hy.2 b) (cmdPostQ_mono θ c hD)⟩

omit [Fintype M] [DecidableEq M] in
theorem hPend_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor L (XSpec M)) Ω A) (C C' : Set HashDomain) :
    HPend θ (e ▸ y) C C' ↔ HPend θ y C C' := by
  subst e
  rfl

omit [Fintype M] [DecidableEq M] in
theorem hPend_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor L (XSpec M)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor L (XSpec M)) Y u)
    {C D C' : Set HashDomain} (hx : HPend θ x C D) (hg : ∀ u a, HPend θ (g u a) D C') :
    HPend θ (x.bind g) C C' := by
  induction x using IFreeM.inductionOn generalizing C with
  | pure _ a => exact hPend_mono θ _ (hg _ a) hx subset_rfl
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

omit [Fintype M] [DecidableEq M] in
theorem hPend₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L (XSpec M) A B α) (g : α → QuantumComp₂ L (XSpec M) B B' β)
    {C D C' : Set HashDomain} (hx : HPend θ x C D) (hg : ∀ a, HPend θ (g a) D C') :
    HPend θ (x.bind g) C C' := by
  refine hPend_bind θ x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

omit [Fintype M] [DecidableEq M] in
/-- Substituting trees that keep the invariant with nothing pending. -/
theorem hPend_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor L spec)
      (QuantumComp.toIPFunctor L (XSpec M)))
    (hσ : ∀ A c, HPend θ (σ A c) ∅ ∅) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L spec) Ω A) : HPend θ (x.substitute σ) ∅ ∅ := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact hPend_bind θ _ _ (hσ s c) fun u ans ↦ (hPend_cast θ ans.2 _ _ _).mpr (ih ans.1)

omit [Fintype M] [DecidableEq M] in
/-- **Runtime 1's programs keep the invariant**: their sponge and read ports (the reads lifted,
keeping the label) leave nothing pending. -/
theorem hPend_readLift {A : QReg} (y : QuantumComp L (hwReadSpec HashOutput HashDomain M) Ω A) :
    HPend θ (readLift goodQ y) ∅ ∅ := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind _ c next ih =>
    show HPend θ (IFreeM.mapLens (Quantum.Xmss.Assembly.readLens goodQ)
      (IFreeM.liftBind c next)) ∅ ∅
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨rfl, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨⟨rfl, labKeepQ_liftRead c⟩, fun b ↦ ?_⟩
      dsimp only
      exact ih _

omit [Fintype M] [DecidableEq M] in
theorem hPend_act {A B : QReg} {α : Type} (p : SubInstrument A B α) (C : Set HashDomain) :
    HPend θ (QComp.act (spec := XSpec M) p) C C :=
  ⟨trivial, fun _ ↦ subset_rfl⟩

omit [Fintype M] [DecidableEq M] in
/-- A reveal with nothing pending makes the cells whose source it reveals pending. -/
theorem hPend_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals HD T × (Finset HPos × M) → QComp (XSpec M) B B' α) {C' : Set HashDomain}
    (hk : ∀ r, HPend θ (k r) (revealCells θ T) C') :
    HPend θ (revealThen goodQ T k) ∅ C' :=
  ⟨rfl, fun r ↦ hPend₂_bind θ _ _ (hPend_act θ _ _) fun _ ↦
    hPend_mono θ _ (hk r.down) (Set.empty_union _).le subset_rfl⟩

omit [Fintype M] [DecidableEq M] in
theorem hPend_progThen {B B' : QReg} {α : Type} (p : LazyProg HashOutput HashDomain HPos HD)
    (hp : goodQ p) (k : QComp (XSpec M) B B' α) {C C' : Set HashDomain}
    (hk : HPend θ k (C \ progCellH (p.realize θ)) C') : HPend θ (progThen p hp k) C C' :=
  ⟨trivial, fun _ ↦ hPend₂_bind θ _ _ (hPend_act θ _ _) fun _ ↦ hk⟩

omit [Fintype M] [DecidableEq M] in
theorem hPend_progPos (B : QReg) (ps : List Pos) (C : Set HashDomain) :
    HPend θ (progPos M B ps) C (C \ {z | ∃ q ∈ ps, z ∈ progCellH ((progT q).realize θ)}) := by
  induction ps generalizing C with
  | nil => exact fun z hz ↦ ⟨hz, fun ⟨_, hq, _⟩ ↦ absurd hq List.not_mem_nil⟩
  | cons q ps ih =>
    refine hPend_progThen θ (progT q) trivial _ (hPend_mono θ _ (ih _) subset_rfl ?_)
    rintro z ⟨⟨hz, hne⟩, hn⟩
    refine ⟨hz, ?_⟩
    rintro ⟨q', hq', hz'⟩
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact hne hz'
    · exact hn ⟨q', hq', hz'⟩

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
theorem hPend_selectT (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (rnd : Pos) (hrnd : revealCells θ {loC rnd} ⊆ ∅) :
    HPend θ (selectT M upd P B l e message rnd) ∅ ∅ :=
  hPend_revealThen θ _ _ fun _ ↦ hPend_mono θ _ (hPend_readLift θ _) hrnd subset_rfl

omit [Fintype M] [DecidableEq M] in
theorem hPend_publishT (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer) (x : Encoding) :
    HPend θ (publishT M B l e ρ x) ∅ ∅ :=
  hPend_revealThen θ _ _ fun _ ↦ hPend₂_bind θ _ _ (hPend_progPos θ B _ _) fun _ ↦ by
    rintro z ⟨hz, hn⟩
    exact hn (revealCells_layerReveal θ l e x hz)

omit [Fintype M] [DecidableEq M] in
theorem hPend_signT (P : PublicParameter) (B : QReg) (r : SigningRequest) :
    HPend θ (signT M upd P B r) ∅ ∅ := by
  refine hPend₂_bind θ _ _ (hPend_selectT θ upd P B _ _ _ _ (revealCells_rndBottom θ _ _))
    fun gb ↦ hPend_revealThen θ _ _ fun rr ↦ hPend_mono θ _ (hPend₂_bind θ _ _
      (hPend_selectT θ upd P B _ _ _ _ (revealCells_rndTop θ _ _)) fun gt ↦ ?_)
      (revealCells_rootReveal θ r) subset_rfl
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · exact subset_rfl
  · exact subset_rfl
  · exact subset_rfl
  · exact hPend₂_bind θ _ _ (hPend_publishT θ B _ _ _ _) fun _ ↦
      hPend₂_bind θ _ _ (hPend_publishT θ B _ _ _ _) fun _ ↦ subset_rfl

omit [Fintype M] [DecidableEq M] in
theorem hPend_challengeT (P : PublicParameter) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0}
      (SufCma.advSpec SigningRequest (Option Signature)) A) :
    HPend θ (challengeT M upd P A c) ∅ ∅ := by
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact hPend_readLift θ _
  · exact hPend_readLift θ _
  · exact hPend_bind θ _ _ (hPend₂_bind θ _ _ (hPend_act θ _ _) fun _ ↦
      hPend_signT θ upd P _ r) fun _ _ ↦ subset_rfl

attribute [local irreducible] xmssRom

omit [Fintype M] [DecidableEq M] in
theorem hPend_prefixT (A : Adversary) : HPend θ (prefixT M upd A) ∅ ∅ :=
  hPend_revealThen θ _ _ fun _ ↦ hPend_mono θ _
    (hPend₂_bind θ _ _ (hPend_substitute θ _ (hPend_challengeT θ upd _) _) fun _ ↦ subset_rfl)
    (revealCells_pkReveal θ) subset_rfl

omit [Fintype M] [DecidableEq M] in
theorem hPend_verifyT (x : PublicKey × (Forgery × SignLog)) : HPend θ (verifyT M x) ∅ ∅ := by
  unfold verifyT
  generalize (readsProgram M _ (xmssRom.verify x.1 x.2.1)).map Prod.fst = y
  exact hPend₂_bind θ _ _ (hPend_readLift θ _) fun _ ↦ subset_rfl

omit [Fintype M] [DecidableEq M] in
/-- **The game keeps the source invariant.** -/
theorem hPend_gameT (A : Adversary) : HPend θ (gameT M upd A) ∅ ∅ := by
  rw [gameT_eq_prefixT_bind]
  exact hPend₂_bind θ _ _ (hPend_prefixT θ upd A) fun x ↦ hPend_verifyT θ x

end hp

/-! ## The steps of `runtimeR` on the pending invariant -/

section steps

variable {M : Type} [Fintype M] [DecidableEq M] {θ : HPos → Digest}

omit [Fintype M] in
/-- A read port keeping the label keeps the hardwired cells and the label. -/
theorem hwReadKraus_ne_zero_keepQ {c : HwRead HashOutput HashDomain (Finset HPos × M)}
    (hc : LabKeepQ c) (r : c.Result) {u u' : Unit}
    {s s' : HwReg HashOutput HashDomain (Finset HPos × M)}
    (h : hwReadKraus c r (u', s') (u, s) ≠ 0) : s'.2.1 = s.2.1 ∧ s'.2.2.1 = s.2.2.1 := by
  cases c with
  | readH z upd =>
    simp only [hwReadKraus, readKrausH] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact ⟨rfl, (hc _ _).trans (congrArg Prod.fst hp).symm⟩
  | readK x upd =>
    simp only [hwReadKraus, readKrausK] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact ⟨rfl, (hc _ _).trans (congrArg Prod.fst hp).symm⟩
  | readK' x upd =>
    simp only [hwReadKraus, readKrausK'] at h
    obtain ⟨hp, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
    exact ⟨rfl, (hc _ _).trans (congrArg Prod.fst hp).symm⟩

variable (θ) in
/-- A step of `runtimeR` at port `i` carries support on the pending invariant `C` to support on
the pending invariant `C'`. -/
def StepPend (m₀ : Finset HPos × M) (i : (recHwSpec HashOutput HashDomain HPos M).Port)
    (C C' : Set HashDomain) : Prop :=
  ∀ r σ, QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain HPos M).In i ×
      (runtimeR m₀).D ↦ m.2) {s | PendInv θ C s} σ →
    QuerySupportedOn (fun m : (recHwSpec HashOutput HashDomain HPos M).Out i ×
      (runtimeR m₀).D ↦ m.2) {s | PendInv θ C' s} (((runtimeR m₀).step i).branch r σ)

theorem stepPend_sponge (m₀ : Finset HPos × M) (i : SpongePort) (C : Set HashDomain) :
    StepPend θ m₀ (.inl (.inl (.inl i))) C C := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r σ =
      MatrixMap.conj ((spongeHardwired HashOutput HashDomain
        (hwEmpty HashOutput HashDomain) m₀).U i) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty HashOutput HashDomain) m₀ i
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    have he := snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty HashOutput HashDomain) m₀ i q.1 q'.1
      q.2 q'.2 hK
    exact pendInv_of_eq (congrArg Prod.fst he) (congrArg (fun t ↦ t.2.1) he) hq

theorem stepPend_read (m₀ : Finset HPos × M)
    (c : {c : HwRead HashOutput HashDomain (Finset HPos × M) //
      ReadMono (Quantum.Xmss.Assembly.memLab HashOutput HashDomain HPos M) c})
    (hc : LabKeepQ c.1) (C : Set HashDomain) : StepPend θ m₀ (.inl (.inl (.inr c.1))) C C := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c.1)))).branch r σ =
      MatrixMap.conj (hwReadKraus c.1 r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain) m₀ c.1
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    obtain ⟨h1, h2⟩ := hwReadKraus_ne_zero_keepQ hc r (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK
    exact pendInv_of_eq h1 h2 hq

theorem stepPend_prog (m₀ : Finset HPos × M) (c : HwProg HashOutput HashDomain)
    (C : Set HashDomain) : StepPend θ m₀ (.inl (.inr c)) C (C \ progCellH c) := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty HashOutput HashDomain) m₀ c
      r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    pendInv_prog c (hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK) hq

theorem stepPend_rec (m₀ : Finset HPos × M) (T : Finset HPos) (C : Set HashDomain) :
    StepPend θ m₀ (.inr T) C (C ∪ revealCells θ T) := by
  intro r σ hσ
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    pendInv_reveal T (Quantum.Xmss.Assembly.recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK) hq

/-- An operator supported on the invariant presents, at a call, no diagonal mass outside it. -/
theorem relabel_diag_eq_zero_srcInv (m₀ : Finset HPos × M) {A : QReg}
    {i : (recHwSpec HashOutput HashDomain HPos M).Port} (E : QReg)
    (ℓ : A ≃ (recHwSpec HashOutput HashDomain HPos M).In i × E)
    {ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | PendInv θ ∅ s} ρ)
    (a : ((recHwSpec HashOutput HashDomain HPos M).In i × (runtimeR m₀).D) × E)
    (ha : ¬SrcInv θ a.1.2) :
    (SubInstrument.relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).branch () ρ a a =
      0 := by
  by_contra h
  have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).imp
    (q' := fun m : ((recHwSpec HashOutput HashDomain HPos M).In i × (runtimeR m₀).D) × E ↦ m.1.2)
    (S' := {s | PendInv θ ∅ s}) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  exact ha (srcInv_of_pendInv (h₁ a a h).1)

end steps

/-! ## The invariant at the calls (`hinv`) -/

section hinv

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- One call of a realized program on the pending invariant. -/
theorem forallQueries_queryBind_of_stepPend
    {Q : (recHwSpec HashOutput HashDomain HPos M).Port → Prop}
    (m₀ : Finset HPos × M) (I : L.Interp) (θ : HPos → Digest) {A : QReg}
    (i : (recHwSpec HashOutput HashDomain HPos M).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec HashOutput HashDomain HPos M).In i × E)
    (k' : (recHwSpec HashOutput HashDomain HPos M).Result i →
      QuantumComp L (recHwSpec HashOutput HashDomain HPos M) Ω
        (QReg.of ((recHwSpec HashOutput HashDomain HPos M).Out i × E)))
    {C C' : Set HashDomain} (hpre : Q i → C = ∅) (hstep : StepPend θ m₀ i C C')
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of ((recHwSpec HashOutput HashDomain HPos M).Out i
        × E) × (runtimeR m₀).D ↦ m.2) {s | PendInv θ C' s} ρ' →
      (runtimeR m₀).ForallQueries I (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInv θ))
        (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | PendInv θ C s} ρ) :
    (runtimeR m₀).ForallQueries I (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInv θ))
      (QuantumComp.queryBind i E ℓ k') ρ :=
  ⟨fun hq a ha ↦ relabel_diag_eq_zero_srcInv (i := i) m₀ E ℓ (hpre hq ▸ hρ) a ha, fun r ↦
    hk r _ (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) i r (hstep r) E ℓ hρ)⟩

/-- **The realized program of a template keeping the source invariant presents, at every call of
the ports `Q` (no program port), only states of the invariant.** -/
theorem forallQueries_of_hPend {Q : (recHwSpec HashOutput HashDomain HPos M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (m₀ : Finset HPos × M) (I : L.Interp) (θ : HPos → Digest)
    {A : QReg} (y : QuantumComp L (XSpec M) Ω A) :
    ∀ C C', HPend θ y C C' → ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | PendInv θ C s} ρ →
      (runtimeR m₀).ForallQueries I (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInv θ))
        (realizeT θ y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro C C' hy ρ hρ b
    exact ih b C C' (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro C C' hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_of_stepPend m₀ I θ (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT θ (k r)) (fun _ ↦ hy.1) (stepPend_sponge m₀ i C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepPend m₀ I θ (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT θ (k r)) (fun _ ↦ hy.1.1) (stepPend_read m₀ c hy.1.2 C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_stepPend m₀ I θ
          (.inl (.inr ((LazyProg.programH T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepPend_prog m₀ _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_stepPend m₀ I θ
          (.inl (.inr ((LazyProg.programK T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepPend_prog m₀ _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_stepPend m₀ I θ
          (.inl (.inr ((LazyProg.programK' T₀ c).realize θ))) E ℓ (fun r ↦ realizeT θ (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepPend_prog m₀ _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepPend m₀ I θ (.inr T) E ℓ
        (fun m ↦ realizeT θ (k (restrictTo T θ, m))) (fun _ ↦ hy.1) (stepPend_rec m₀ T C)
        (fun m ↦ ih (restrictTo T θ, m) _ C' (hy.2 (ULift.up (restrictTo T θ, m)))) ρ hρ

/-- An initial state whose memory label is empty. -/
theorem querySupportedOn_initQ (m₀ : Finset HPos × M) (hm₀ : m₀.1 = ∅) {A : QReg}
    (σ : Matrix A A ℂ) :
    QuerySupportedOn (fun a : A × QReg.of (HwReg HashOutput HashDomain (Finset HPos × M)) ↦
      a.2.2.2.1) {∅} (σ ⊗ₖ (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix) := by
  intro a b h
  change (σ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
    hwEmpty HashOutput HashDomain, m₀) : HwReg HashOutput HashDomain (Finset HPos × M))).matrix)
      a b ≠ 0 at h
  rw [SubState.matrix_basis, kroneckerMap_apply] at h
  have h' := right_ne_zero_of_mul h
  rw [Matrix.single_apply] at h'
  split_ifs at h' with he
  · show a.2.2.2.1 ∈ ({∅} : Set (Finset HPos)) ∧ b.2.2.2.1 ∈ ({∅} : Set (Finset HPos))
    rw [← he.1, ← he.2]
    exact ⟨hm₀, hm₀⟩
  · exact absurd rfl h'

variable (upd : TrialUpd M)

/-- **`hinv` for the realized template game**: from states with an empty memory label, every
call of ports `Q` that are not program ports sees the source invariant. -/
theorem forallQueries_gameQ {Q : (recHwSpec HashOutput HashDomain HPos M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (m₀ : Finset HPos × M) (A : Adversary) (θ : HPos → Digest)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset HPos × M))) ℂ)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit ×
      QReg.of (HwReg HashOutput HashDomain (Finset HPos × M)) ↦ a.2.2.2.1) {∅} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInv θ)) (realizeT θ (gameT M upd A))
        ρ :=
  forallQueries_of_hPend hQ m₀ _ θ _ ∅ ∅ (hPend_gameT θ upd A) ρ
    (hρ.imp fun _ ha ↦ pendInv_of_label_empty (Set.mem_singleton_iff.1 ha))

/-- The same for the challenge prefix. -/
theorem forallQueries_prefixQ {Q : (recHwSpec HashOutput HashDomain HPos M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (m₀ : Finset HPos × M) (A : Adversary) (θ : HPos → Digest)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg HashOutput HashDomain (Finset HPos × M))) ℂ)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit ×
      QReg.of (HwReg HashOutput HashDomain (Finset HPos × M)) ↦ a.2.2.2.1) {∅} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (Quantum.Xmss.Assembly.invSupp (runtimeR m₀) Q (SrcInv θ)) (realizeT θ (prefixT M upd A))
        ρ :=
  forallQueries_of_hPend hQ m₀ _ θ _ ∅ ∅ (hPend_prefixT θ upd A) ρ
    (hρ.imp fun _ ha ↦ pendInv_of_label_empty (Set.mem_singleton_iff.1 ha))

end hinv

/-! ## The verifier's hash calls -/

section verifyCost

open Common

attribute [local irreducible] HashSig.OverPermutation.sequenceFin HashSig.OverPermutation.walkChain
  HashSig.OverPermutation.foldPath

theorem hashQ_cost (l : HashInput) : QueryCostAtMost (hashQ l) hashCallCost 1 := by
  unfold hashQ
  split
  · exact isWeightBound_query hashCallCost _
  · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)

theorem th_cost (P : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    QueryCostAtMost (Over.th hashQ P fields payload) hashCallCost 1 := by
  unfold Over.th
  exact (hashQ_cost _).bind fun _ ↦ isWeightBound_pure _ _ 0

theorem recoverChain_cost (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex)
    (digit : WinternitzDigit) (v : Digest) :
    QueryCostAtMost (Over.recoverChain hashQ P l e i digit v) hashCallCost (chainLength - 1) :=
  (walkChain_cost _ 1 (fun _ _ ↦ th_cost _ _ _) _ _ v).mono (by omega)

/-- The hash calls of a one-time leaf's recovery. -/
def otsLeafCalls : ℕ :=
  1 + (chainCount * (chainLength - 1) + 1)

theorem otsLeaf_cost (P : PublicParameter) (l : Layer) (e : KeyIndex) (message : HashInput)
    (randomizer : Randomizer) (values : ChainIndex → Digest) :
    QueryCostAtMost (Over.otsLeaf hashQ P l e message randomizer values) hashCallCost
      otsLeafCalls := by
  unfold Over.otsLeaf
  refine (th_cost _ _ _).bind fun digest ↦ ?_
  split
  · exact ((sequenceFin_cost _ _ fun i ↦ recoverChain_cost _ _ _ _ _ _).bind fun _ ↦
      (th_cost _ _ _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono le_rfl
  · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)

/-- The hash calls of a layer's root. -/
def layerRootCalls : ℕ :=
  otsLeafCalls + layerHeight * 1

theorem layerRoot_cost (P : PublicParameter) (l : Layer) (e : KeyIndex) (message : HashInput)
    (sig : LayerSignature) :
    QueryCostAtMost (Over.layerRoot hashQ P l e message sig) hashCallCost layerRootCalls := by
  unfold Over.layerRoot
  refine (otsLeaf_cost _ _ _ _ _ _).bind fun leaf ↦ ?_
  cases leaf with
  | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  | some _ =>
    exact ((foldPath_cost _ 1 (fun _ _ _ _ ↦ th_cost _ _ _) _ _ _ _).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono le_rfl

/-- **The verifier's hash calls**: two layer roots. -/
def verifyCalls : ℕ :=
  2 * layerRootCalls

theorem verifyCalls_eq : verifyCalls = 384 := by
  simp [verifyCalls, layerRootCalls, otsLeafCalls, chainCount, chainLength, winternitzBits,
    layerHeight]

theorem verify_cost (pk : PublicKey) (forgery : Forgery) :
    QueryCostAtMost (xmssRom.verify pk forgery) hashCallCost verifyCalls := by
  change QueryCostAtMost (Over.verify hashQ pk forgery.message forgery.signature) _ _
  unfold Over.verify
  refine ((layerRoot_cost _ _ _ _ _).bind fun r ↦ ?_).mono
    (Q := layerRootCalls + layerRootCalls) (by rw [verifyCalls]; omega)
  cases r with
  | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  | some _ =>
    refine ((layerRoot_cost _ _ _ _ _).bind fun r' ↦ ?_).mono (Q := layerRootCalls + 0) (by simp)
    cases r' <;> exact isWeightBound_pure _ _ _

end verifyCost

/-! ## Charges of the calls by kind -/

section charges

/-- A message-digest cell: the trials' and the verifier's digests. -/
def isMsgCell (z : HashDomain) : Bool :=
  match slotOf z with
  | some (.msg _ _) => true
  | _ => false

theorem isMsgCell_cell (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (d : Payload (.msg l e)) : isMsgCell (cell P (.msg l e) d) = true := by
  rw [isMsgCell, slotOf_cell P (show Addressable (.msg l e) from trivial) d]

/-- A read at a message-digest cell. -/
def readMsg {M' : Type} : HwRead HashOutput HashDomain M' → Bool
  | .readH z _ => isMsgCell z
  | _ => false

theorem readMsg_liftRead {M : Type} (c : HwRead HashOutput HashDomain M) :
    readMsg (Quantum.Xmss.Assembly.liftRead (S := HPos) c) = readMsg c := by
  cases c <;> rfl

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

variable (M) in
/-- A charge on the template ports by kind: `a` per sponge call, `b` per read at a cell other than
a message digest, `b'` per read at a message digest, `c` per program call, `d` per reveal. -/
def tChargeQ (a b b' c d : ℕ) : (XSpec M).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr r)) => if readMsg r.1 then b' else b
  | .inl (.inr _) => c
  | .inr _ => d

variable (M) in
/-- The same charge on runtime 2 with record ports (a reveal realizes as a record call). -/
def rChargeQ (a b b' c d : ℕ) : (recHwSpec HashOutput HashDomain HPos M).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr r)) => if readMsg r then b' else b
  | .inl (.inr _) => c
  | .inr _ => d

variable (M) in
/-- The charge on runtime 1's ports. -/
def rdChargeQ (a b b' : ℕ) : (hwReadSpec HashOutput HashDomain M).Port → ℕ
  | .inl _ => a
  | .inr r => if readMsg r then b' else b

variable (M) in
/-- The reads at cells other than message digests: the ports of the read mass. -/
def readQ : (recHwSpec HashOutput HashDomain HPos M).Port → Bool
  | .inl (.inl (.inr r)) => !readMsg r
  | _ => false

variable (a b b' c d : ℕ)

omit [Fintype M] [DecidableEq M] in
/-- **Realizing keeps the charges by kind.** -/
theorem isChargeBound_realizeT (θ : HPos → Digest) {A : QReg}
    {y : QuantumComp L (XSpec M) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (tChargeQ M a b b' c d)) n) :
    IFreeM.IsChargeBound (realizeT θ y) (portCharge (rChargeQ M a b b' c d)) n := by
  refine IFreeM.IsChargeBound.mapLens (Quantum.Xmss.Assembly.tmplLens θ) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (rChargeQ M a b b' c d) s
      ((Quantum.Xmss.Assembly.tmplLens θ).toFunA s cmd)) =
      portCharge (tChargeQ M a b b' c d) := by
    funext s cmd
    rcases cmd with o | ⟨((i | r) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem isChargeBound_readLift {A : QReg}
    {y : QuantumComp L (hwReadSpec HashOutput HashDomain M) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (rdChargeQ M a b b')) n) :
    IFreeM.IsChargeBound (readLift goodQ y) (portCharge (tChargeQ M a b b' c d)) n := by
  refine IFreeM.IsChargeBound.mapLens (Quantum.Xmss.Assembly.readLens goodQ) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (tChargeQ M a b b' c d) s
      ((Quantum.Xmss.Assembly.readLens goodQ).toFunA s cmd)) = portCharge (rdChargeQ M a b b') := by
    funext s cmd
    rcases cmd with o | ⟨i | r, E, ℓ⟩
    · rfl
    · rfl
    · cases r <;> rfl
  rw [he]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem chg_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals HD T × (Finset HPos × M) → QComp (XSpec M) B B' α) {n : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (tChargeQ M a b b' c d)) n) :
    IFreeM.IsChargeBound (revealThen goodQ T k) (portCharge (tChargeQ M a b b' c d)) (d + n) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right d n, fun r ↦ ?_⟩
  simp only [tChargeQ, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0)
    (Quantum.Xmss.Assembly.chg_act _ _ 0) fun _ ↦ hk r) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
theorem chg_progThen {B B' : QReg} {α : Type} (p : LazyProg HashOutput HashDomain HPos HD)
    (hp : goodQ p) (k : QComp (XSpec M) B B' α) {n : ℕ}
    (hk : IFreeM.IsChargeBound k (portCharge (tChargeQ M a b b' c d)) n) :
    IFreeM.IsChargeBound (progThen p hp k) (portCharge (tChargeQ M a b b' c d)) (c + n) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right c n, fun r ↦ ?_⟩
  simp only [tChargeQ, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0)
    (Quantum.Xmss.Assembly.chg_act _ _ 0) fun _ ↦ hk) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
theorem chg_progPos (B : QReg) (ps : List Pos) :
    IFreeM.IsChargeBound (progPos M B ps) (portCharge (tChargeQ M a b b' c d)) (c * ps.length) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    refine IFreeM.IsChargeBound.mono (chg_progThen a b b' c d (progT p) trivial _ ih) (le_of_eq ?_)
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm]

omit [Fintype M] [DecidableEq M] in
theorem chg_readCall (r : HwRead HashOutput HashDomain M) (B : QReg) :
    IFreeM.IsChargeBound (readCall r B) (portCharge (rdChargeQ M a b b'))
      (if readMsg r then b' else b) := by
  unfold readCall
  exact FreeM₂.isChargeBound_bind (n₂ := 0)
    ((IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_rfl, fun _ ↦ trivial⟩) fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (Quantum.Xmss.Assembly.chg_act _ _ 0)
        fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem sChg_romReadImpl (B : QReg) (t : RomOracles.Domain) :
    Quantum.Xmss.Assembly.SChg (rdChargeQ M a b b') (romReadImpl M B t)
      (max b b' * hashCallCost t) := by
  rcases t with n | x
  · intro s
    show IFreeM.IsChargeBound ((StateT.lift (QComp.coinImpl (hwReadSpec HashOutput HashDomain M)
      B n) : StateT (List HashDomain) (QComp (hwReadSpec HashOutput HashDomain M) B B) _).run s)
      _ _
    rw [StateT.run_lift]
    refine IFreeM.IsChargeBound.mono ?_ (Nat.zero_le _)
    exact FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (Quantum.Xmss.Assembly.chg_act _ _ 0)
      fun a' ↦ Quantum.Xmss.Assembly.sChg_pure (σ := List HashDomain) (B := B)
        (rdChargeQ M a b b') a' 0 s
  · intro log
    show IFreeM.IsChargeBound ((readCall (.readH x keepMem) B).bind fun r ↦
      QuantumComp₂.pure (r.1.getD 0, log ++ [x])) _ _
    refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
      (chg_readCall a b b' _ B) fun _ ↦ trivial) ?_
    simp only [hashCallCost, Nat.mul_one, Nat.add_zero]
    split
    · exact le_max_right b b'
    · exact le_max_left b b'

omit [Fintype M] [DecidableEq M] in
theorem sChg_simulateQ_romReadImpl (B : QReg) {α : Type} (x : OracleComp RomOracles α) {n : ℕ}
    (h : Common.QueryCostAtMost x hashCallCost n) :
    Quantum.Xmss.Assembly.SChg (rdChargeQ M a b b') (simulateQ (romReadImpl M B) x)
      (max b b' * n) := by
  induction x using OracleComp.inductionOn generalizing n with
  | pure x => rw [simulateQ_pure]; exact Quantum.Xmss.Assembly.sChg_pure _ x _
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_spec_query]
    refine Quantum.Xmss.Assembly.sChg_mono _ (Quantum.Xmss.Assembly.sChg_bind _
      (sChg_romReadImpl a b b' B t) fun u ↦ ih u (h.2 u)) ?_
    rw [← Nat.mul_add, Nat.add_sub_cancel' h.1]

omit [Fintype M] [DecidableEq M] in
/-- **A computation through read ports**: one read per call of `H` of a path bound. -/
theorem chg_readsProgram (B : QReg) {α : Type} {x : OracleComp RomOracles α} {n : ℕ}
    (h : Common.QueryCostAtMost x hashCallCost n) :
    IFreeM.IsChargeBound (readsProgram M B x) (portCharge (rdChargeQ M a b b')) (max b b' * n) :=
  sChg_simulateQ_romReadImpl a b b' B x h []

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
/-- **The randomizer search**: one read of a message digest per trial. -/
theorem chg_grindT (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (base : Randomizer) :
    ∀ n trial, IFreeM.IsChargeBound (grindT M upd P B l e message base n trial)
      (portCharge (rdChargeQ M a b b')) (n * b')
  | 0, _ => trivial
  | n + 1, trial => by
    have hr := chg_readCall a b b' (.readH (trialCell P l e message base trial)
      (upd l e (trialCell P l e message base trial))) B
    rw [show readMsg (HwRead.readH (trialCell P l e message base trial)
      (upd l e (trialCell P l e message base trial))) = true from isMsgCell_cell _ _ _ _,
      ite_eq_left rfl] at hr
    rw [grindT]
    refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := n * b') hr fun r ↦ ?_)
      (le_of_eq (by ring))
    split
    · trivial
    · exact chg_grindT P B l e message base n (trial + 1)

theorem length_flatMap_le_mul {α β : Type} (l : List α) (f : α → List β) {k : ℕ}
    (h : ∀ x ∈ l, (f x).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h x List.mem_cons_self
    have h2 := ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)
    omega

/-- The positions a layer signature programs: at most `191`. -/
def layerProgCap : ℕ :=
  chainCount * (chainLength - 1) + 1 + layerHeight

theorem length_layerPos_le (l : Layer) (e : KeyIndex) (x : Encoding) :
    (layerPos l e x).length ≤ layerProgCap := by
  have key : ∀ F : List Pos, F.length ≤ chainCount * (chainLength - 1) →
      (F ++ Pos.leaf l e :: (List.finRange layerHeight).map (pathNode l e)).length ≤
        layerProgCap := by
    intro F hF
    rw [List.length_append, List.length_cons, List.length_map, List.length_finRange, layerProgCap]
    omega
  refine key _ ((length_flatMap_le_mul _ _ (k := chainLength - 1) fun i _ ↦ ?_).trans ?_)
  · rw [List.length_map]
    exact (List.length_filter_le _ _).trans List.length_finRange.le
  · rw [List.length_finRange]

omit [Fintype M] [DecidableEq M] in
theorem chg_selectT (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (rnd : Pos) :
    IFreeM.IsChargeBound (selectT M upd P B l e message rnd) (portCharge (tChargeQ M a b b' c d))
      (d + randomizerAttemptLimit * b') :=
  chg_revealThen a b b' c d _ _ fun _ ↦
    isChargeBound_readLift a b b' c d (chg_grindT a b b' upd P B l e message _ _ 0)

omit [Fintype M] [DecidableEq M] in
theorem chg_publishT (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer) (x : Encoding) :
    IFreeM.IsChargeBound (publishT M B l e ρ x) (portCharge (tChargeQ M a b b' c d))
      (d + c * layerProgCap) := by
  refine chg_revealThen a b b' c d _ _ fun _ ↦ IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₂ := 0) (chg_progPos a b b' c d B _) fun _ ↦ trivial) ?_
  rw [Nat.add_zero]
  exact Nat.mul_le_mul_left c (length_layerPos_le l e x)

/-- The calls of one signing request by kind: two searches, the root's reveal, two layer
publications. -/
def reqCallsQ (b' c d : ℕ) : ℕ :=
  5 * d + 2 * randomizerAttemptLimit * b' + 2 * c * layerProgCap

omit [Fintype M] [DecidableEq M] in
/-- **A signature's calls.** -/
theorem chg_signT (P : PublicParameter) (B : QReg) (r : SigningRequest) :
    IFreeM.IsChargeBound (signT M upd P B r) (portCharge (tChargeQ M a b b' c d))
      (reqCallsQ b' c d) := by
  unfold signT
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind
    (chg_selectT a b b' c d upd P B _ _ _ _) fun gb ↦ chg_revealThen a b b' c d _ _ fun rr ↦
      FreeM₂.isChargeBound_bind (chg_selectT a b b' c d upd P B _ _ _ _) fun gt ↦
        (?_ : IFreeM.IsChargeBound _ _ ((d + c * layerProgCap) + ((d + c * layerProgCap) + 0))))
    (le_of_eq (by unfold reqCallsQ; ring))
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · trivial
  · trivial
  · trivial
  · exact FreeM₂.isChargeBound_bind (chg_publishT a b b' c d B _ _ _ _) fun _ ↦
      FreeM₂.isChargeBound_bind (chg_publishT a b b' c d B _ _ _ _) fun _ ↦ trivial

/-- The source charge of the adversary's commands: `α` per hash call, `β` per signing request. -/
def advChargeQ (α β : ℕ) (A : QReg) (cmd : QuantumComp.Cmd LocalSig.instruments.{0}
    (SufCma.advSpec SigningRequest (Option Signature)) A) : ℕ :=
  α * SufCma.cmdCharge SufCma.hashCharge A cmd + β * SufCma.cmdCharge SufCma.signCharge A cmd

omit [Fintype M] [DecidableEq M] in
/-- **The challenger's calls** per command: a local operation none, a hash call one sponge call,
a signing request the signature's calls `S`. -/
theorem chg_challengeT (P : PublicParameter) {S : ℕ}
    (hS : ∀ B r, IFreeM.IsChargeBound (signT M upd P B r) (portCharge (tChargeQ M a b b' c d)) S)
    (A : QReg) (cmd : QuantumComp.Cmd LocalSig.instruments.{0}
      (SufCma.advSpec SigningRequest (Option Signature)) A) :
    IFreeM.IsChargeBound (challengeT M upd P A cmd) (portCharge (tChargeQ M a b b' c d))
      (advChargeQ a S A cmd) := by
  rcases cmd with o | ⟨_ | r, E, ℓ⟩
  · refine isChargeBound_readLift a b b' c d (isChargeBound_liftOrdinary _
      ((isChargeBound_liftH_iff _ _ _).mpr ?_))
    exact (isChargeBound_portCharge_primBind_iff _ _ _ _).mpr fun _ ↦ trivial
  · refine isChargeBound_readLift a b b' c d (isChargeBound_liftOrdinary _
      ((isChargeBound_liftH_iff _ _ _).mpr ?_))
    refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr
      ⟨by simp [advChargeQ, SufCma.cmdCharge, SufCma.hashCharge, SufCma.signCharge, rdChargeQ],
        fun _ ↦ trivial⟩
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind (FreeM₂.isChargeBound_bind
      (n₁ := 0) (Quantum.Xmss.Assembly.chg_act _ _ 0) fun _ ↦ hS _ r) fun _ _ ↦
        IFreeM.isChargeBound_pure _ 0) ?_
    simp only [advChargeQ, SufCma.cmdCharge, SufCma.hashCharge, SufCma.signCharge]
    omega

attribute [local irreducible] xmssRom

omit [Fintype M] [DecidableEq M] in
/-- **The challenge prefix's calls**: the public key's reveal, the challenged adversary. -/
theorem chg_prefixT (A : Adversary) {q n S : ℕ}
    (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) n)
    (hS : ∀ P B r, IFreeM.IsChargeBound (signT M upd P B r)
      (portCharge (tChargeQ M a b b' c d)) S) :
    IFreeM.IsChargeBound (prefixT M upd A) (portCharge (tChargeQ M a b b' c d))
      (d + ((a * q + S * n) + 0)) := by
  refine chg_revealThen a b b' c d _ _ fun r₀ ↦ ?_
  have hx := IFreeM.IsChargeBound.add
    ((SufCma.isChargeBound_withSignLog (hhash (pkT r₀.1))).mul a)
    ((SufCma.isChargeBound_withSignLog (hsign (pkT r₀.1))).mul S)
  have hc := IFreeM.IsChargeBound.substitute (challengeT M upd (pkT r₀.1).parameter)
    (chg_challengeT a b b' c d upd (pkT r₀.1).parameter (hS (pkT r₀.1).parameter)) hx
  exact FreeM₂.isChargeBound_bind hc fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The verification's calls**: one read per hash call of the verifier. -/
theorem chg_verifyT (x : PublicKey × (Forgery × SignLog)) :
    IFreeM.IsChargeBound (verifyT M x) (portCharge (tChargeQ M a b b' c d))
      (max b b' * verifyCalls + 0) := by
  unfold verifyT
  exact FreeM₂.isChargeBound_bind (isChargeBound_readLift a b b' c d
    (Quantum.Xmss.Assembly.chg_map _ Prod.fst (chg_readsProgram a b b' _ (verify_cost _ _))))
      fun _ ↦ trivial

/-- The calls of the game by kind: the public key's reveal, `a` per hash call, the requests'
calls, the verification's reads. -/
def gameCallsQ (a b b' c d q : ℕ) : ℕ :=
  d + (a * q + reqCallsQ b' c d * lifetime) + max b b' * verifyCalls

omit [Fintype M] [DecidableEq M] in
/-- **The realized game's calls by kind**, for an adversary making at most `q` hash calls and at
most `lifetime` signing requests on every path, at all hidden values. -/
theorem chg_realizeT_gameT (A : Adversary) {q : ℕ}
    (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) lifetime)
    (θ : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT θ (gameT M upd A)) (portCharge (rChargeQ M a b b' c d))
      (gameCallsQ a b b' c d q) := by
  refine isChargeBound_realizeT a b b' c d θ ?_
  rw [gameT_eq_prefixT_bind]
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind
    (chg_prefixT a b b' c d upd A hhash hsign fun P B r ↦ chg_signT a b b' c d upd P B r)
      fun x ↦ chg_verifyT a b b' c d x) (le_of_eq (by unfold gameCallsQ; ring))

omit [Fintype M] [DecidableEq M] in
/-- **The realized prefix's calls by kind.** -/
theorem chg_realizeT_prefixT (A : Adversary) {q : ℕ}
    (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) lifetime)
    (θ : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT θ (prefixT M upd A)) (portCharge (rChargeQ M a b b' c d))
      (gameCallsQ a b b' c d q) :=
  isChargeBound_realizeT a b b' c d θ (IFreeM.IsChargeBound.mono
    (chg_prefixT a b b' c d upd A hhash hsign fun P B r ↦ chg_signT a b b' c d upd P B r)
      (by unfold gameCallsQ; omega))

end charges

/-! ## The call counts -/

section counts

/-- The program calls of the game: two layer publications per request. -/
def progCapQ : ℕ :=
  2 * layerProgCap * lifetime

/-- The classical calls of the game: the public key's reveal, per request two searches of
`randomizerAttemptLimit` reads, three searches' and the root's reveals and the program calls, and
the verification's reads. -/
def clsCapQ : ℕ :=
  1 + (2 * randomizerAttemptLimit + 5) * lifetime + progCapQ + verifyCalls

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M) (A : Adversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) lifetime)
include hhash hsign

omit [Fintype M] [DecidableEq M] hhash hsign in
theorem advCharge_eq :
    (fun i ↦ if Quantum.Xmss.Assembly.extCls HashOutput HashDomain (Finset HPos × M)
      (recSpec HPos M) i then 0 else 1) = rChargeQ M 1 0 0 0 0 := by
  funext i
  rcases i with ((i | r) | p) | T
  · rfl
  · exact (ite_self 0).symm
  · rfl
  · rfl

omit [Fintype M] [DecidableEq M] hhash hsign in
theorem clsCharge_eq :
    (fun i ↦ if Quantum.Xmss.Assembly.extCls HashOutput HashDomain (Finset HPos × M)
      (recSpec HPos M) i then 1 else 0) = rChargeQ M 0 1 1 1 1 := by
  funext i
  rcases i with ((i | r) | p) | T
  · rfl
  · exact (ite_self 1).symm
  · rfl
  · rfl

omit [Fintype M] [DecidableEq M] hhash hsign in
theorem progCharge_eq :
    Quantum.Xmss.extProgCharge HashOutput HashDomain (Finset HPos × M) (recSpec HPos M) =
      rChargeQ M 0 0 0 1 0 := by
  funext i
  rcases i with ((i | r) | p) | T
  · rfl
  · exact (ite_self 0).symm
  · rfl
  · rfl

omit [Fintype M] [DecidableEq M] hhash hsign in
theorem readQCharge_eq :
    (fun i ↦ if readQ M i = true then 1 else 0) = rChargeQ M 0 1 0 0 0 := by
  funext i
  rcases i with ((i | r) | p) | T
  · rfl
  · simp only [readQ, rChargeQ]
    rcases Bool.eq_false_or_eq_true (readMsg r) with h | h <;> simp [h]
  · rfl
  · rfl

omit [Fintype M] [DecidableEq M] in
/-- **The game's sponge calls**: at most `q`. -/
theorem advCalls_gameQ (θ : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT θ (gameT M upd A))
      (portCharge fun i ↦ if Quantum.Xmss.Assembly.extCls HashOutput HashDomain
        (Finset HPos × M) (recSpec HPos M) i then 0 else 1) q := by
  rw [advCharge_eq]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_gameT 1 0 0 0 0 upd A hhash hsign θ)
    (le_of_eq (by simp [gameCallsQ, reqCallsQ]))

omit [Fintype M] [DecidableEq M] in
/-- **The game's classical calls** (reads, program and record calls): at most `clsCapQ`. -/
theorem clsCalls_gameQ (θ : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT θ (gameT M upd A))
      (portCharge fun i ↦ if Quantum.Xmss.Assembly.extCls HashOutput HashDomain
        (Finset HPos × M) (recSpec HPos M) i then 1 else 0) clsCapQ := by
  rw [clsCharge_eq]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_gameT 0 1 1 1 1 upd A hhash hsign θ)
    (le_of_eq (by simp only [gameCallsQ, reqCallsQ, clsCapQ, progCapQ, max_self]; ring))

omit [Fintype M] [DecidableEq M] in
/-- **The game's program calls**: at most `progCapQ`. -/
theorem progCalls_gameQ (θ : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT θ (gameT M upd A))
      (portCharge (Quantum.Xmss.extProgCharge HashOutput HashDomain (Finset HPos × M)
        (recSpec HPos M))) progCapQ := by
  rw [progCharge_eq]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_gameT 0 0 0 1 0 upd A hhash hsign θ)
    (le_of_eq (by simp only [gameCallsQ, reqCallsQ, progCapQ, max_self]; ring))

omit [Fintype M] [DecidableEq M] in
/-- **The game's reads at cells other than message digests**: the verification's, at most
`verifyCalls`. -/
theorem readQCalls_gameQ (θ : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT θ (gameT M upd A))
      (portCharge fun i ↦ if readQ M i = true then 1 else 0) verifyCalls := by
  rw [readQCharge_eq]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_gameT 0 1 0 0 0 upd A hhash hsign θ)
    (le_of_eq (by simp [gameCallsQ, reqCallsQ]))

omit [Fintype M] [DecidableEq M] in
theorem advCalls_prefixQ (θ : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT θ (prefixT M upd A))
      (portCharge fun i ↦ if Quantum.Xmss.Assembly.extCls HashOutput HashDomain
        (Finset HPos × M) (recSpec HPos M) i then 0 else 1) q := by
  rw [advCharge_eq]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixT 1 0 0 0 0 upd A hhash hsign θ)
    (le_of_eq (by simp [gameCallsQ, reqCallsQ]))

omit [Fintype M] [DecidableEq M] in
theorem clsCalls_prefixQ (θ : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT θ (prefixT M upd A))
      (portCharge fun i ↦ if Quantum.Xmss.Assembly.extCls HashOutput HashDomain
        (Finset HPos × M) (recSpec HPos M) i then 1 else 0) clsCapQ := by
  rw [clsCharge_eq]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixT 0 1 1 1 1 upd A hhash hsign θ)
    (le_of_eq (by simp only [gameCallsQ, reqCallsQ, clsCapQ, progCapQ, max_self]; ring))

omit [Fintype M] [DecidableEq M] in
theorem progCalls_prefixQ (θ : HPos → Digest) :
    IFreeM.IsChargeBound (realizeT θ (prefixT M upd A))
      (portCharge (Quantum.Xmss.extProgCharge HashOutput HashDomain (Finset HPos × M)
        (recSpec HPos M))) progCapQ := by
  rw [progCharge_eq]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixT 0 0 0 1 0 upd A hhash hsign θ)
    (le_of_eq (by simp only [gameCallsQ, reqCallsQ, progCapQ, max_self]; ring))

end counts

/-! ## The game's reads keep the label

Mismatch's `KeepsLab` for the realized template game and its prefix. -/

section keepsLab

variable {M : Type} (upd : TrialUpd M)

theorem keepsLab_progPosQ (B : QReg) (ps : List Pos) : KeepsLab (progPos M B ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact keepsLab_progThen _ trivial _ ih

theorem keepsLab_selectTQ (P : PublicParameter) (B : QReg) (l : Layer) (e : KeyIndex)
    (message : MsgBytes) (rnd : Pos) : KeepsLab (selectT M upd P B l e message rnd) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab_readLift _

theorem keepsLab_publishTQ (B : QReg) (l : Layer) (e : KeyIndex) (ρ : Randomizer)
    (x : Encoding) : KeepsLab (publishT M B l e ρ x) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _ (keepsLab_progPosQ B _) fun _ ↦ trivial

theorem keepsLab_signTQ (P : PublicParameter) (B : QReg) (r : SigningRequest) :
    KeepsLab (signT M upd P B r) := by
  refine keepsLab₂_bind _ _ (keepsLab_selectTQ upd P B _ _ _ _) fun gb ↦
    keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _ (keepsLab_selectTQ upd P B _ _ _ _)
      fun gt ↦ ?_
  rcases gb with _ | ⟨ρb, xb⟩ <;> rcases gt with _ | ⟨ρt, xt⟩
  · trivial
  · trivial
  · trivial
  · exact keepsLab₂_bind _ _ (keepsLab_publishTQ B _ _ _ _) fun _ ↦
      keepsLab₂_bind _ _ (keepsLab_publishTQ B _ _ _ _) fun _ ↦ trivial

theorem keepsLab_challengeTQ (P : PublicParameter) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0}
      (SufCma.advSpec SigningRequest (Option Signature)) A) :
    KeepsLab (challengeT M upd P A c) := by
  rcases c with o | ⟨_ | r, E, ℓ⟩
  · exact keepsLab_readLift _
  · exact keepsLab_readLift _
  · exact keepsLab_bind _ _ (keepsLab₂_bind _ _ (keepsLab_act _) fun _ ↦
      keepsLab_signTQ upd P _ r) fun _ _ ↦ trivial

attribute [local irreducible] xmssRom

/-- The challenge prefix's reads keep the label. -/
theorem keepsLab_prefixQ (A : Adversary) : KeepsLab (prefixT M upd A) :=
  keepsLab_revealThen _ _ fun _ ↦ keepsLab₂_bind _ _
    (keepsLab_substitute _ (keepsLab_challengeTQ upd _) _) fun _ ↦ trivial

theorem keepsLab_verifyQ (x : PublicKey × (Forgery × SignLog)) : KeepsLab (verifyT M x) := by
  unfold verifyT
  generalize (readsProgram M _ (xmssRom.verify x.1 x.2.1)).map Prod.fst = y
  exact keepsLab₂_bind _ _ (keepsLab_readLift _) fun _ ↦ trivial

/-- **The game's reads keep the label.** -/
theorem keepsLab_gameQ (A : Adversary) : KeepsLab (gameT M upd A) := by
  rw [gameT_eq_prefixT_bind]
  exact keepsLab₂_bind _ _ (keepsLab_prefixQ upd A) fun x ↦ keepsLab_verifyQ x

end keepsLab

end Quantum.Qrom.Xmss

end
