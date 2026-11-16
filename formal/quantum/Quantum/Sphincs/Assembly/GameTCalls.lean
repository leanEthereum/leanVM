module

public import Quantum.Sphincs.Assembly.GameTCalls.Charges
public import Quantum.Sphincs.Assembly.Template.Exempt
public import Quantum.Sphincs.Assembly.FullTable

@[expose] public section

/-!
# The calls of leanSPHINCS's realized template game

Masses' hypothesis `hinv` for `realizeT v (gameT M upd pol pub A)`
(`Quantum.Sphincs.Assembly.Template`), for every public datum `pub` and every digest policy `pol`
revealing no value position (`DigestPolicy.ValFree`: `msgPol`, `strPol`), and the run fact the
event's exemptions need (`RoundHeld` of the earlier rounds at a round's port). The charges and
`hN` are in `Quantum.Sphincs.Assembly.GameTCalls.Charges`.

* **The invariant** (`SlotInv`): at a call, every in-table slot with a disclosed input (`IsInput`,
  a payload position in the memory label) has the `k`, `k'`, `h` cells of every round of its
  honest path at `(pub, v)` hardwired (PathBad's `sCellK`, `sCellR`, `sCellZ` at `pub.xw`).
* **Combinatorics**: a slot with an input in `forsNeed idx lv` is one of `forsSlots idx lv`
  (`mem_forsSlots_of_isInput`), one with an input in `layerNeed l τ e x` one of
  `layerSlots l τ e x` (`mem_layerSlots_of_isInput`); `PK.root`, the roots of the trees and the
  FORS keys (the values the keys sign, `msgPos`) are no slot's input (`not_isInput_tpos_top`,
  `not_isInput_forsKey`, `not_isInput_msgPos`).
* **Pending ports** (`InvP`, `HP`): between a reveal and the end of its program calls the slots it
  discloses are pending. Per component `hp_readLift`, `hp_forsOpenT`, `hp_signLayerT`, `hp_signT`,
  `hp_challengeT`, composed in `hp_gameT`; `forallQueries_of_hp` gives `ForallQueries` of
  `invSupp` for the ports `Q` other than the program ports (`forallQueries_gameT`, `hinv_gameT`
  with `Inv p v := SlotInv M (pubP p) v`, from states with an empty memory label).
* **The read mass** (`readMass_eq_portMass`): the hidden mass at the read and record ports
  (`readRecPort`).
* **Batches** (`BatchOk`, `HB`): the ports of an absorption (a structural slot's `slotPorts`, an
  `H_msg` call's `hmsgPorts`) are called in order `k`, `k'`, `h` round by round. For any condition
  `ok` on program calls that holds at a round's ports once the earlier rounds are held with their
  programmed values (`RoundHeld`), and at the `k'`, `h` ports once the round's `k` (and `k'`) cell
  is, every program call of the realized game is presented only states satisfying `ok`
  (`forallQueries_progSupp_gameT`). Applied to the event: after a structural slot's final `h`
  program the slot is exempted (`mem_exS_progUpdate_final`, with Exempt's `FinalSep`); before an
  `H_msg` call's `h` program its `k`, `k'` cells are held (`isHeadTail_hmsg`'s hypotheses).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker

universe u v w w₁

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message Randomizer ChainStep chainLength winternitzBits)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (LazyProg restrictTo ReadMono querySupportedOn_queryStep progUpdate
  hwProgKraus_ne_zero_snd clsKraus_ne_zero_cls portMass readMass)
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec readLift readLens realizeT revealThen
  progThen RevealVals memLab liftRead CellHardwired cellHardwired_progUpdate
  cellHardwired_progUpdate_self invSupp recKraus_ne_zero extCls runtimeR)

namespace Quantum.Sphincs.Assembly

/- Membership in the concrete FORS opening's sets is otherwise decided by evaluating them. -/
attribute [local irreducible] forsNeed forsSlots

/-! ## The invariant -/

section inv

/-- `q` is a payload position of the structural slot `s` (its output position is not an input). -/
def IsInput (q : ValPos) : Slot → Prop
  | .chain l τ e i step => q = cpos l τ e i step.val
  | .leaf l τ e => ∃ i : ChainIndex, q = cpos l τ e i (chainLength - 1)
  | .node l τ height index =>
      q = tpos l τ (height - 1) (2 * index) ∨ q = tpos l τ (height - 1) (2 * index + 1)
  | .forsLeaf idx κ s => q = .forsSecret idx κ s
  | .forsNode idx κ height node =>
      q = fpos idx κ (height - 1) (2 * node) ∨ q = fpos idx κ (height - 1) (2 * node + 1)
  | .forsRoots idx => ∃ κ : ForsTreeIndex, q = fpos idx κ forsTreeHeight 0
  | _ => False

variable (M : Type) in
/-- **The invariant at the sponge, read and record calls**: an in-table slot with a disclosed input
has all its cells at `(pub, v)` hardwired. -/
def SlotInv (pub : Pub) (v : (s : HPos) → XD s) (r : HwReg X Z (Finset HPos × M)) : Prop :=
  ∀ s, InTable s → ∀ q, IsInput q s → HPos.val q ∈ r.2.2.1 → ∀ j < nBlk pub.seed s,
    r.2.1.2.1 (sCellK pub.xw pub.keys.1 s (valsOf v) j) ≠ none ∧
      r.2.1.2.2 (sCellR pub.xw pub.keys.1 s (valsOf v) j) ≠ none ∧
      r.2.1.1 (sCellZ pub.xw pub.keys.1 s (valsOf v) j) ≠ none

end inv

/-! ## The slots a signature discloses -/

section slots

theorem div_two_pow_succ (e lev : ℕ) : e / 2 ^ (lev + 1) = e / 2 ^ lev / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

theorem xor_one_div_two (n : ℕ) : (n ^^^ 1) / 2 = n / 2 := by
  rcases Nat.even_or_odd n with h | h
  · rw [Nat.xor_one_of_even h]
    have := Nat.even_iff.1 h
    omega
  · rw [Nat.xor_one_of_odd h]
    have := Nat.odd_iff.1 h
    omega

/-- The positions on the path of the leaf `e < 2^10` at level `lev`: the children of the node at
`lev + 1` and the node are in range, and halving a child gives the node. -/
theorem path_facts {e : ℕ} (he : e < 2 ^ 10) (lev : ℕ) :
    2 * (e / 2 ^ (lev + 1)) + 1 < 2 ^ 10 ∧ e / 2 ^ (lev + 1) < 2 ^ 10 ∧
      2 * (e / 2 ^ (lev + 1)) / 2 = e / 2 ^ (lev + 1) ∧
      (2 * (e / 2 ^ (lev + 1)) + 1) / 2 = e / 2 ^ (lev + 1) := by
  have h1 := Nat.div_le_self e (2 ^ lev)
  rw [div_two_pow_succ]
  omega

/-- The sibling of the path of the leaf `e < 2^10` at level `z` is in range, and halving it gives
the path's node at `z + 1`. -/
theorem sibling_facts {e : ℕ} (he : e < 2 ^ 10) (z : ℕ) :
    (e >>> z) ^^^ 1 < 2 ^ 10 ∧ ((e >>> z) ^^^ 1) / 2 = e / 2 ^ (z + 1) := by
  have hx := xor_one_div_two (e >>> z)
  have h1 := Nat.div_le_self e (2 ^ z)
  rw [Nat.shiftRight_eq_div_pow] at hx ⊢
  rw [div_two_pow_succ]
  omega

theorem chain_mem_layerSlots {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {x : Encoding}
    {i : ChainIndex} {step : ChainStep} (h : (x i).val ≤ step.val) :
    Slot.chain l τ e i step ∈ layerSlots l τ e x :=
  List.mem_append_left _ (List.mem_flatMap.2 ⟨i, List.mem_finRange _, List.mem_map.2
    ⟨step, List.mem_filter.2 ⟨List.mem_finRange _, by simpa using h⟩, rfl⟩⟩)

theorem leaf_mem_layerSlots (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (x : Encoding) :
    Slot.leaf l τ e ∈ layerSlots l τ e x :=
  List.mem_append_right _ List.mem_cons_self

theorem node_mem_layerSlots {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} (x : Encoding)
    {lev : ℕ} (h : lev < layerHeight l) :
    Slot.node l τ (lev + 1) (e.val / 2 ^ (lev + 1)) ∈ layerSlots l τ e x := by
  rw [← Nat.shiftRight_eq_div_pow]
  exact List.mem_append_right _ (List.mem_cons_of_mem _
    (List.mem_map.2 ⟨lev, List.mem_range.2 h, rfl⟩))

/-- The slots of a layer signature: the chain steps from the opened positions, the leaf, the
nodes on the path. -/
theorem mem_layerSlots_cases {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {x : Encoding}
    {s : Slot} (h : s ∈ layerSlots l τ e x) :
    (∃ (i : ChainIndex) (step : ChainStep), (x i).val ≤ step.val ∧ s = .chain l τ e i step) ∨
      s = .leaf l τ e ∨
      ∃ lev < layerHeight l, s = .node l τ (lev + 1) (e.val / 2 ^ (lev + 1)) := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨i, -, h⟩ := List.mem_flatMap.1 h
    obtain ⟨step, hs, rfl⟩ := List.mem_map.1 h
    exact Or.inl ⟨i, step, by simpa using (List.mem_filter.1 hs).2, rfl⟩
  · rcases List.mem_cons.1 h with rfl | h
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨lev, hl, rfl⟩ := List.mem_map.1 h
      exact Or.inr (Or.inr ⟨lev, List.mem_range.1 hl, by rw [Nat.shiftRight_eq_div_pow]⟩)

/-- **The positions a layer signature reveals**: chain positions of its key from the opened
positions on, and tree positions whose parent is on its key's path. -/
theorem mem_layerNeed {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {x : Encoding} {q : ValPos}
    (h : q ∈ layerNeed l τ e x) :
    (∃ (i : ChainIndex) (j : ℕ), j < chainLength ∧ (x i).val ≤ j ∧ q = cpos l τ e i j) ∨
      ∃ lev a, q = tpos l τ lev a ∧ lev ≤ layerHeight l ∧ a < 2 ^ 10 ∧
        (lev < layerHeight l → a / 2 = e.val / 2 ^ (lev + 1)) := by
  have he : e.val < 2 ^ 10 := e.isLt
  have hC : chainLength = 4 := rfl
  simp only [layerNeed, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
  rcases h with (h | ⟨i, rfl⟩) | ⟨z, rfl⟩
  · obtain ⟨s, hs, hq⟩ := mem_needUnion h
    rcases mem_layerSlots_cases hs with ⟨i, step, hle, rfl⟩ | rfl | ⟨lev, hlev, rfl⟩
    · have := step.isLt
      simp only [slotNeed, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Or.inl ⟨i, step.val, by omega, hle, rfl⟩
      · exact Or.inl ⟨i, step.val + 1, by omega, by omega, rfl⟩
    · simp only [slotNeed, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hq
      rcases hq with rfl | ⟨i, rfl⟩
      · exact Or.inr ⟨0, e.val, rfl, Nat.zero_le _, he, fun _ ↦ rfl⟩
      · exact Or.inl ⟨i, chainLength - 1, by omega, by have := (x i).isLt; omega, rfl⟩
    · obtain ⟨f1, f2, f3, f4⟩ := path_facts he lev
      simp only [slotNeed, Nat.add_sub_cancel, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact Or.inr ⟨lev, _, rfl, by omega, by omega, fun _ ↦ f3⟩
      · exact Or.inr ⟨lev, _, rfl, by omega, f1, fun _ ↦ f4⟩
      · exact Or.inr ⟨lev + 1, _, rfl, by omega, f2,
          fun _ ↦ (div_two_pow_succ e.val (lev + 1)).symm⟩
  · exact Or.inl ⟨i, (x i).val, (x i).isLt, le_rfl, rfl⟩
  · obtain ⟨f1, f2⟩ := sibling_facts he z.val
    exact Or.inr ⟨z.val, _, rfl, z.isLt.le, f1, fun _ ↦ f2⟩

theorem tpos_eq_iff {l l' : Layer} {τ τ' : TreeIndex} {lev lev' a a' : ℕ}
    (hl : lev ≤ 10) (hl' : lev' ≤ 10) (ha : a < 2 ^ 10) (ha' : a' < 2 ^ 10) :
    tpos l τ lev a = tpos l' τ' lev' a' ↔ l = l' ∧ τ = τ' ∧ lev = lev' ∧ a = a' := by
  have hT : layerHeight topLayer = 10 := rfl
  simp only [tpos, ValPos.tree.injEq, Fin.mk.injEq, hT]
  rw [Nat.mod_eq_of_lt (by omega : lev < 10 + 1), Nat.mod_eq_of_lt (by omega : lev' < 10 + 1),
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha']

theorem fpos_eq_iff {idx idx' : Index} {κ κ' : ForsTreeIndex} {h h' a a' : ℕ}
    (hh : h ≤ 10) (hh' : h' ≤ 10) (ha : a < 2 ^ 10) (ha' : a' < 2 ^ 10) :
    fpos idx κ h a = fpos idx' κ' h' a' ↔ idx = idx' ∧ κ = κ' ∧ h = h' ∧ a = a' := by
  have hF : forsTreeHeight = 10 := rfl
  simp only [fpos, ValPos.forsTree.injEq, Fin.mk.injEq, hF]
  rw [Nat.mod_eq_of_lt (by omega : h < 10 + 1), Nat.mod_eq_of_lt (by omega : h' < 10 + 1),
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha']

/-- An input position of an in-table node lies at a level below the tree's height, with an index
whose half is the node's index. -/
theorem isInput_node {q : ValPos} {l : Layer} {τ : TreeIndex} {level index : ℕ}
    (hs : InTable (.node l τ level index)) (hq : IsInput q (.node l τ level index)) :
    ∃ a, q = tpos l τ (level - 1) a ∧ a / 2 = index ∧ a < 2 ^ 10 ∧ 1 ≤ level ∧
      level ≤ layerHeight l := by
  obtain ⟨-, h1, h2, h3⟩ := hs
  have hb := two_mul_add_one_lt h3 h1 h2
  have hp := two_pow_layerHeight_le l
  have hT : 2 ^ layerHeight topLayer = 2 ^ 10 := rfl
  rcases hq with rfl | rfl
  · exact ⟨_, rfl, by omega, by omega, h1, h2⟩
  · exact ⟨_, rfl, by omega, by omega, h1, h2⟩

/-- An input position of an in-table FORS node lies at a height below `a`, with a node whose half
is the node's index. -/
theorem isInput_forsNode {q : ValPos} {idx : Index} {κ : ForsTreeIndex} {height node : ℕ}
    (hs : InTable (.forsNode idx κ height node)) (hq : IsInput q (.forsNode idx κ height node)) :
    ∃ a, q = fpos idx κ (height - 1) a ∧ a / 2 = node ∧ a < 2 ^ 10 ∧ 1 ≤ height ∧
      height ≤ forsTreeHeight := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hb := two_mul_add_one_lt h3 h1 h2
  have hF : 2 ^ forsTreeHeight = 2 ^ 10 := rfl
  rcases hq with rfl | rfl
  · exact ⟨_, rfl, by omega, by omega, h1, h2⟩
  · exact ⟨_, rfl, by omega, by omega, h1, h2⟩

/-- **A slot with an input revealed by a layer signature is one of the signature's slots.** -/
theorem mem_layerSlots_of_isInput {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {x : Encoding}
    {s : Slot} (hs : InTable s) {q : ValPos} (hq : IsInput q s) (hn : q ∈ layerNeed l τ e x) :
    s ∈ layerSlots l τ e x := by
  have hC : chainLength = 4 := rfl
  have hH := layerHeight_le l
  cases s with
  | chain l' τ' e' i step =>
    subst hq
    rcases mem_layerNeed hn with ⟨i₀, j, hj, hxj, h⟩ | ⟨lev, a, h, -⟩
    · simp only [cpos, ValPos.chain.injEq, Fin.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, hm⟩ := h
      have := step.isLt
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
      exact chain_mem_layerSlots (by omega)
    · simp [cpos, tpos] at h
  | leaf l' τ' e' =>
    obtain ⟨i, rfl⟩ := hq
    rcases mem_layerNeed hn with ⟨i₀, j, -, -, h⟩ | ⟨lev, a, h, -⟩
    · simp only [cpos, ValPos.chain.injEq] at h
      obtain ⟨rfl, rfl, rfl, -⟩ := h
      exact leaf_mem_layerSlots _ _ _ _
    · simp [cpos, tpos] at h
  | node l' τ' level index =>
    obtain ⟨a', rfl, ha', ha'b, h1, h2⟩ := isInput_node hs hq
    have hH' := layerHeight_le l'
    rcases mem_layerNeed hn with ⟨i₀, j, -, -, h⟩ | ⟨lev, a, h, hlev, ha, hdiv⟩
    · simp [cpos, tpos] at h
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := (tpos_eq_iff (by omega) (by omega) ha'b ha).1 h
      have hd := hdiv (by omega)
      rw [show level = level - 1 + 1 by omega, show index = e.val / 2 ^ (level - 1 + 1) by omega]
      exact node_mem_layerSlots x (by omega)
  | forsLeaf idx κ s =>
    subst hq
    rcases mem_layerNeed hn with ⟨i₀, j, -, -, h⟩ | ⟨lev, a, h, -⟩ <;> simp [cpos, tpos] at h
  | forsNode idx κ height node =>
    obtain ⟨a', rfl, -⟩ := isInput_forsNode hs hq
    rcases mem_layerNeed hn with ⟨i₀, j, -, -, h⟩ | ⟨lev, a, h, -⟩ <;> simp [cpos, tpos, fpos] at h
  | forsRoots idx =>
    obtain ⟨κ, rfl⟩ := hq
    rcases mem_layerNeed hn with ⟨i₀, j, -, -, h⟩ | ⟨lev, a, h, -⟩ <;> simp [cpos, tpos, fpos] at h
  | enc => exact hs.elim
  | prf => exact hs.elim
  | hmsg => exact hs.elim
  | prfMsg => exact hs.elim
  | expand => exact hs.elim

theorem forsLeaf_mem_forsSlots (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (κ : ForsTreeIndex) : Slot.forsLeaf idx κ (lv κ) ∈ forsSlots idx lv := by
  unfold forsSlots
  exact List.mem_append_left _ (List.mem_flatMap.2 ⟨κ, List.mem_finRange _, List.mem_cons_self⟩)

theorem forsNode_mem_forsSlots (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (κ : ForsTreeIndex) {h : ℕ} (hh : h < forsTreeHeight) :
    Slot.forsNode idx κ (h + 1) ((lv κ).val / 2 ^ (h + 1)) ∈ forsSlots idx lv := by
  unfold forsSlots
  rw [← Nat.shiftRight_eq_div_pow]
  exact List.mem_append_left _ (List.mem_flatMap.2 ⟨κ, List.mem_finRange _,
    List.mem_cons_of_mem _ (List.mem_map.2 ⟨h, List.mem_range.2 hh, rfl⟩)⟩)

theorem forsRoots_mem_forsSlots (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    Slot.forsRoots idx ∈ forsSlots idx lv := by
  unfold forsSlots
  exact List.mem_append_right _ List.mem_cons_self

/-- The slots of a FORS opening: the opened leaves, the nodes on their paths, the roots. -/
theorem mem_forsSlots_cases {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {s : Slot}
    (h : s ∈ forsSlots idx lv) :
    (∃ κ, s = .forsLeaf idx κ (lv κ)) ∨
      (∃ κ, ∃ hgt < forsTreeHeight,
        s = .forsNode idx κ (hgt + 1) ((lv κ).val / 2 ^ (hgt + 1))) ∨
      s = .forsRoots idx := by
  unfold forsSlots at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨κ, -, h⟩ := List.mem_flatMap.1 h
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl ⟨κ, rfl⟩
    · obtain ⟨hgt, hl, rfl⟩ := List.mem_map.1 h
      exact Or.inr (Or.inl ⟨κ, hgt, List.mem_range.1 hl, by rw [Nat.shiftRight_eq_div_pow]⟩)
  · rcases List.mem_singleton.1 h with rfl
    exact Or.inr (Or.inr rfl)

/-- **The positions a FORS opening reveals**: the opened secrets, the FORS key, and FORS tree
positions whose parent is on an opened path. -/
theorem mem_forsNeed {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {q : ValPos}
    (h : q ∈ forsNeed idx lv) :
    (∃ κ, q = .forsSecret idx κ (lv κ)) ∨ q = .forsKey idx ∨
      ∃ κ hgt a, q = fpos idx κ hgt a ∧ hgt ≤ forsTreeHeight ∧ a < 2 ^ 10 ∧
        (hgt < forsTreeHeight → a / 2 = (lv κ).val / 2 ^ (hgt + 1)) := by
  have hF : forsTreeHeight = 10 := rfl
  simp only [forsNeed, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
  rcases h with (h | ⟨κ, rfl⟩) | ⟨⟨κ, z⟩, rfl⟩
  · obtain ⟨s, hs, hq⟩ := mem_needUnion h
    rcases mem_forsSlots_cases hs with ⟨κ, rfl⟩ | ⟨κ, hgt, hh, rfl⟩ | rfl
    · have hl : (lv κ).val < 2 ^ 10 := (lv κ).isLt
      simp only [slotNeed, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Or.inl ⟨κ, rfl⟩
      · exact Or.inr (Or.inr ⟨κ, 0, _, rfl, Nat.zero_le _, hl, fun _ ↦ rfl⟩)
    · have hl : (lv κ).val < 2 ^ 10 := (lv κ).isLt
      obtain ⟨f1, f2, f3, f4⟩ := path_facts hl hgt
      simp only [slotNeed, Nat.add_sub_cancel, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact Or.inr (Or.inr ⟨κ, hgt, _, rfl, by omega, by omega, fun _ ↦ f3⟩)
      · exact Or.inr (Or.inr ⟨κ, hgt, _, rfl, by omega, f1, fun _ ↦ f4⟩)
      · exact Or.inr (Or.inr ⟨κ, hgt + 1, _, rfl, by omega, f2,
          fun _ ↦ (div_two_pow_succ (lv κ).val (hgt + 1)).symm⟩)
    · simp only [slotNeed, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hq
      rcases hq with rfl | ⟨κ, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨κ, forsTreeHeight, 0, rfl, le_rfl, by norm_num,
          fun h ↦ absurd h (lt_irrefl _)⟩)
  · exact Or.inl ⟨κ, rfl⟩
  · obtain ⟨f1, f2⟩ := sibling_facts (lv κ).isLt z.val
    exact Or.inr (Or.inr ⟨κ, z.val, _, rfl, z.isLt.le, f1, fun _ ↦ f2⟩)

/-- **A slot with an input revealed by a FORS opening is one of the opening's slots.** -/
theorem mem_forsSlots_of_isInput {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {s : Slot}
    (hs : InTable s) {q : ValPos} (hq : IsInput q s) (hn : q ∈ forsNeed idx lv) :
    s ∈ forsSlots idx lv := by
  have hF : forsTreeHeight = 10 := rfl
  cases s with
  | chain l τ e i step =>
    subst hq
    rcases mem_forsNeed hn with ⟨κ, h⟩ | h | ⟨κ, hgt, a, h, -⟩ <;> simp [cpos, fpos] at h
  | leaf l τ e =>
    obtain ⟨i, rfl⟩ := hq
    rcases mem_forsNeed hn with ⟨κ, h⟩ | h | ⟨κ, hgt, a, h, -⟩ <;> simp [cpos, fpos] at h
  | node l τ level index =>
    obtain ⟨a', rfl, -⟩ := isInput_node hs hq
    rcases mem_forsNeed hn with ⟨κ, h⟩ | h | ⟨κ, hgt, a, h, -⟩ <;> simp [tpos, fpos] at h
  | forsLeaf idx' κ' s' =>
    subst hq
    rcases mem_forsNeed hn with ⟨κ, h⟩ | h | ⟨κ, hgt, a, h, -⟩
    · simp only [ValPos.forsSecret.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact forsLeaf_mem_forsSlots _ _ _
    · simp at h
    · simp [fpos] at h
  | forsNode idx' κ' height node =>
    obtain ⟨a', rfl, ha', ha'b, h1, h2⟩ := isInput_forsNode hs hq
    rcases mem_forsNeed hn with ⟨κ, h⟩ | h | ⟨κ, hgt, a, h, hh, ha, hdiv⟩
    · simp [fpos] at h
    · simp [fpos] at h
    · obtain ⟨e1, e2, e3, e4⟩ := (fpos_eq_iff (by omega) (by omega) ha'b ha).1 h
      subst e1 e2 e3 e4
      have hd := hdiv (by omega)
      rw [show height = height - 1 + 1 by omega,
        show node = (lv κ').val / 2 ^ (height - 1 + 1) by omega]
      exact forsNode_mem_forsSlots _ _ _ (by omega)
  | forsRoots idx' =>
    obtain ⟨κ', rfl⟩ := hq
    rcases mem_forsNeed hn with ⟨κ, h⟩ | h | ⟨κ, hgt, a, h, hh, ha, -⟩
    · simp [fpos] at h
    · simp [fpos] at h
    · obtain ⟨rfl, -⟩ := (fpos_eq_iff le_rfl hh (Nat.two_pow_pos _) ha).1 h
      exact forsRoots_mem_forsSlots _ _
  | enc => exact hs.elim
  | prf => exact hs.elim
  | hmsg => exact hs.elim
  | prfMsg => exact hs.elim
  | expand => exact hs.elim

/-- **The roots of the trees are no slot's input** (`PK.root` among them). -/
theorem not_isInput_tpos_top {s : Slot} (hs : InTable s) (l : Layer) (τ : TreeIndex) (a : ℕ) :
    ¬IsInput (tpos l τ (layerHeight l) a) s := by
  intro hq
  cases s with
  | chain => simp [IsInput, cpos, tpos] at hq
  | leaf => simp [IsInput, cpos, tpos] at hq
  | node l' τ' level index =>
    obtain ⟨a', h, -, ha', h1, h2⟩ := isInput_node hs hq
    have hl := layerHeight_le l
    have hl' := layerHeight_le l'
    have hT : layerHeight topLayer = 10 := rfl
    simp only [tpos, ValPos.tree.injEq, Fin.mk.injEq, hT] at h
    obtain ⟨rfl, -, h3, -⟩ := h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
    omega
  | forsLeaf => simp [IsInput, tpos] at hq
  | forsNode => simp [IsInput, tpos, fpos] at hq
  | forsRoots => simp [IsInput, tpos, fpos] at hq
  | enc => exact hs.elim
  | prf => exact hs.elim
  | hmsg => exact hs.elim
  | prfMsg => exact hs.elim
  | expand => exact hs.elim

/-- A FORS key is no slot's input. -/
theorem not_isInput_forsKey (idx : Index) (s : Slot) : ¬IsInput (.forsKey idx) s := by
  cases s <;> simp [IsInput, cpos, tpos, fpos]

/-- **The value a key signs is no slot's input.** -/
theorem not_isInput_msgPos (K : Key) {s : Slot} (hs : InTable s) : ¬IsInput (msgPos K) s := by
  obtain ⟨l, τ, e⟩ := K
  show ¬IsInput (if l.val = 0 then .forsKey (indexBelow l τ e)
    else tpos (layerBelow l) (indexBelow l τ e) (layerHeight (layerBelow l)) 0) s
  split_ifs
  · exact not_isInput_forsKey _ s
  · exact not_isInput_tpos_top hs _ _ _

/-- `PK.root` is no slot's input. -/
theorem not_isInput_rootPos {s : Slot} (hs : InTable s) : ¬IsInput rootPos s :=
  not_isInput_tpos_top hs topLayer 0 0

end slots

/-! ## Digest policies revealing no value position -/

/-- **A digest policy revealing no value position.** -/
def DigestPolicy.ValFree (pol : DigestPolicy) : Prop :=
  ∀ T msg p, HPos.val p ∉ pol.need T msg

theorem valFree_msgPol : msgPol.ValFree := by
  intro T msg p
  simp [DigestPolicy.need, msgPol]

theorem valFree_strPol : strPol.ValFree := by
  intro T msg p hp
  have hout : ∀ i, HPos.val p ≠ strPol.out T msg i := by
    intro i
    show HPos.val p ≠ match streamIdx T msg with
      | some j => .str j i
      | none => .dig msg i
    split <;> simp
  have hmarks : HPos.val p ∉ strPol.marks T msg := by
    show HPos.val p ∉ match streamIdx T msg with
      | some j => ({HPos.asg msg j} : Finset HPos)
      | none => ∅
    split <;> simp
  simp only [DigestPolicy.need, Finset.mem_insert] at hp
  rcases hp with h | h | h
  · exact hout 0 h
  · exact hout 1 h
  · exact hmarks h

/-! ## The invariant with pending program ports -/

section pending

variable {M : Type}

/-- **The invariant with pending program ports `C`**: an in-table slot with a disclosed input has
each of its realized program ports hardwired or pending. -/
def InvP (pub : Pub) (v : (s : HPos) → XD s) (C : Set (HwProg X Z))
    (r : HwReg X Z (Finset HPos × M)) : Prop :=
  ∀ s, InTable s → ∀ q, IsInput q s → HPos.val q ∈ r.2.2.1 → ∀ p ∈ slotPorts pub s,
    CellHardwired (p.realize v) r.2.1 ∨ p.realize v ∈ C

/-- The realized program ports of the in-table slots with an input in `T`. -/
def revealSet (pub : Pub) (v : (s : HPos) → XD s) (T : Finset HPos) : Set (HwProg X Z) :=
  {c | ∃ s, InTable s ∧ (∃ q, IsInput q s ∧ HPos.val q ∈ T) ∧ ∃ p ∈ slotPorts pub s,
    p.realize v = c}

/-- The realized program ports of the slots `ss`. -/
def portsOf (pub : Pub) (v : (s : HPos) → XD s) (ss : List Slot) : Set (HwProg X Z) :=
  {c | ∃ s ∈ ss, ∃ p ∈ slotPorts pub s, p.realize v = c}

variable (pub : Pub) (v : (s : HPos) → XD s)

theorem revealSet_layerNeed_subset (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (x : Encoding) :
    revealSet pub v (valSet (layerNeed l τ e x)) ⊆ portsOf pub v (layerSlots l τ e x) := by
  rintro c ⟨s, hs, ⟨q, hq, hn⟩, hp⟩
  exact ⟨s, mem_layerSlots_of_isInput hs hq (val_mem_valSet.mp hn), hp⟩

theorem revealSet_forsNeed_subset (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    revealSet pub v (valSet (forsNeed idx lv)) ⊆ portsOf pub v (forsSlots idx lv) := by
  rintro c ⟨s, hs, ⟨q, hq, hn⟩, hp⟩
  exact ⟨s, mem_forsSlots_of_isInput hs hq (val_mem_valSet.mp hn), hp⟩

theorem revealSet_rootPos : revealSet pub v {.val rootPos} ⊆ ∅ := by
  rintro c ⟨s, hs, ⟨q, hq, hn⟩, -⟩
  obtain rfl := HPos.val.inj (Finset.mem_singleton.mp hn)
  exact not_isInput_rootPos hs hq

theorem revealSet_rootPos_rnd (msg : Message) :
    revealSet pub v {.val rootPos, .rnd msg} ⊆ ∅ := by
  rintro c ⟨s, hs, ⟨q, hq, hn⟩, -⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, HPos.val.injEq, reduceCtorEq,
    or_false] at hn
  subst hn
  exact not_isInput_rootPos hs hq

theorem revealSet_msgPos (K : Key) : revealSet pub v {.val (msgPos K)} ⊆ ∅ := by
  rintro c ⟨s, hs, ⟨q, hq, hn⟩, -⟩
  obtain rfl := HPos.val.inj (Finset.mem_singleton.mp hn)
  exact not_isInput_msgPos K hs hq

theorem revealSet_valFree {pol : DigestPolicy} (hpol : pol.ValFree) (T : Finset HPos)
    (msg : Message) : revealSet pub v (pol.need T msg) ⊆ ∅ := by
  rintro c ⟨s, -, ⟨q, -, hn⟩, -⟩
  exact hpol T msg q hn

variable {pub v}

theorem invP_of_label_empty {C : Set (HwProg X Z)} {r : HwReg X Z (Finset HPos × M)}
    (h : r.2.2.1 = ∅) : InvP pub v C r := by
  intro s _ q _ hl
  rw [h] at hl
  exact absurd hl (Finset.notMem_empty _)

/-- A step keeping the hardwired cells and the label keeps the invariant. -/
theorem invP_of_eq {C : Set (HwProg X Z)} {r r' : HwReg X Z (Finset HPos × M)}
    (h1 : r'.2.1 = r.2.1) (h2 : r'.2.2.1 = r.2.2.1) (hr : InvP pub v C r) : InvP pub v C r' := by
  intro s hs q hq hl p hp
  rw [h1]
  exact hr s hs q hq (h2 ▸ hl) p hp

/-- A program port hardwires its cell and keeps the others: it leaves the pending set. -/
theorem invP_prog {C : Set (HwProg X Z)} (c : HwProg X Z) {r r' : HwReg X Z (Finset HPos × M)}
    (h : r'.2 = (progUpdate c r.2.1, r.2.2)) (hr : InvP pub v C r) : InvP pub v (C \ {c}) r' := by
  intro s hs q hq hl p hp
  rw [h] at hl ⊢
  rcases hr s hs q hq hl p hp with hc | hc
  · exact Or.inl (cellHardwired_progUpdate hc)
  · by_cases he : p.realize v = c
    · rw [he]
      exact Or.inl (cellHardwired_progUpdate_self c _)
    · exact Or.inr ⟨hc, he⟩

/-- A reveal of `T` adds the ports of the slots with an input in `T` to the pending set. -/
theorem invP_reveal {C : Set (HwProg X Z)} (T : Finset HPos) {r r' : HwReg X Z (Finset HPos × M)}
    (h : r'.2 = (r.2.1, (r.2.2.1 ∪ T, r.2.2.2))) (hr : InvP pub v C r) :
    InvP pub v (C ∪ revealSet pub v T) r' := by
  intro s hs q hq hl p hp
  rw [h] at hl ⊢
  rcases Finset.mem_union.1 hl with hl | hl
  · exact (hr s hs q hq hl p hp).imp_right Or.inl
  · exact Or.inr (Or.inr ⟨s, hs, ⟨q, hq, hl⟩, p, hp, rfl⟩)

variable (pub) in
/-- The realized program ports of round `j` of an absorption. -/
theorem mem_pathCells_round (b : ℕ → X) (cor : X → X → X) {n j : ℕ} (hj : j < n) :
    HwProg.programK (cellK pub b j).1 (cellK pub b j).2 ∈ pathCells pub b cor n ∧
      HwProg.programK' (cellK' pub b j).1 (cellK' pub b j).2 ∈ pathCells pub b cor n ∧
      HwProg.programH (cellH pub b (n - 1) cor j).1 (cellH pub b (n - 1) cor j).2 ∈
        pathCells pub b cor n :=
  ⟨List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, by simp⟩,
    List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, by simp⟩,
    List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, by simp⟩⟩

/-- **No pending port is the invariant**: the realized program ports are the honest path's cells
(Exempt's `realize_slotPorts`). -/
theorem slotInv_of_invP {r : HwReg X Z (Finset HPos × M)} (h : InvP pub v ∅ r) :
    SlotInv M pub v r := by
  intro s hs q hq hl j hj
  have hin : ∀ c ∈ pathCells pub (slotBlk pub.seed s (valsOf v))
      (cor128 (valsOf v (slotOutPos s))) (nBlk pub.seed s), CellHardwired c r.2.1 := by
    intro c hc
    rw [← realize_slotPorts pub hs v] at hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    exact (h s hs q hq hl p hp).resolve_right (Set.notMem_empty _)
  obtain ⟨h1, h2, h3⟩ := mem_pathCells_round (pub := pub) (slotBlk pub.seed s (valsOf v))
    (cor128 (valsOf v (slotOutPos s))) hj
  have hH := hin _ h3
  simp only [CellHardwired, cellH_fst] at hH
  exact ⟨hin _ h1, hin _ h2, hH⟩

end pending

/-! ## The steps of `runtimeR` -/

section steps

variable {M : Type} [Fintype M] [DecidableEq M]

/-- A read port whose memory update keeps the memory label (Template's `liftRead`). -/
def LabKeep : HwRead X Z (Finset HPos × M) → Prop
  | .readH _ u => ∀ m o, (u m o).1 = m.1
  | .readK _ u => ∀ m o, (u m o).1 = m.1
  | .readK' _ u => ∀ m o, (u m o).1 = m.1

omit [Fintype M] [DecidableEq M] in
theorem labKeep_liftRead (c : HwRead X Z M) : LabKeep (liftRead (S := HPos) c) := by
  cases c <;> intro _ _ <;> rfl

omit [Fintype M] in
/-- A read port keeps the hardwired cells. -/
theorem hwReadKraus_ne_zero_hw (c : HwRead X Z (Finset HPos × M)) (r : c.Result) {u u' : Unit}
    {s s' : HwReg X Z (Finset HPos × M)} (h : hwReadKraus c r (u', s') (u, s) ≠ 0) :
    s'.2.1 = s.2.1 := by
  cases c with
  | readH z upd =>
    simp only [hwReadKraus, readKrausH] at h
    obtain ⟨-, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
  | readK x upd =>
    simp only [hwReadKraus, readKrausK] at h
    obtain ⟨-, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]
  | readK' x upd =>
    simp only [hwReadKraus, readKrausK'] at h
    obtain ⟨-, hφ⟩ := clsKraus_ne_zero_cls (one_kronecker_ne_zero h).2
    rw [hφ]

omit [Fintype M] in
/-- A read port keeping the label keeps the hardwired cells and the label. -/
theorem hwReadKraus_ne_zero_keep {c : HwRead X Z (Finset HPos × M)} (hc : LabKeep c)
    (r : c.Result) {u u' : Unit} {s s' : HwReg X Z (Finset HPos × M)}
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

/-- A step of `runtimeR` at port `i` carries support on `P` to support on `P'`. -/
def StepR (m₀ : Finset HPos × M) (i : (recHwSpec X Z HPos M).Port)
    (P P' : HwReg X Z (Finset HPos × M) → Prop) : Prop :=
  ∀ r σ, QuerySupportedOn (fun m : (recHwSpec X Z HPos M).In i × (runtimeR m₀).D ↦ m.2)
      {s | P s} σ →
    QuerySupportedOn (fun m : (recHwSpec X Z HPos M).Out i × (runtimeR m₀).D ↦ m.2)
      {s | P' s} (((runtimeR m₀).step i).branch r σ)

variable {P P' : HwReg X Z (Finset HPos × M) → Prop}

theorem stepR_sponge (m₀ : Finset HPos × M) (i : SpongePort)
    (hP : ∀ r r', r'.2 = r.2 → P r → P' r') : StepR m₀ (.inl (.inl (.inl i))) P P' := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r σ =
      MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U i) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m₀ i r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    hP _ _ (snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty X Z) m₀ i q.1 q'.1 q.2 q'.2 hK) hq

theorem stepR_read (m₀ : Finset HPos × M)
    (c : {c : HwRead X Z (Finset HPos × M) // ReadMono (memLab X Z HPos M) c})
    (hP : ∀ r r', r'.2.1 = r.2.1 → P r → P' r') : StepR m₀ (.inl (.inl (.inr c.1))) P P' := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c.1)))).branch r σ =
      MatrixMap.conj (hwReadKraus c.1 r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c.1 r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    hP _ _ (hwReadKraus_ne_zero_hw c.1 r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK) hq

theorem stepR_readKeep (m₀ : Finset HPos × M)
    (c : {c : HwRead X Z (Finset HPos × M) // ReadMono (memLab X Z HPos M) c})
    (hc : LabKeep c.1) (hP : ∀ r r', r'.2.1 = r.2.1 → r'.2.2.1 = r.2.2.1 → P r → P' r') :
    StepR m₀ (.inl (.inl (.inr c.1))) P P' := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c.1)))).branch r σ =
      MatrixMap.conj (hwReadKraus c.1 r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c.1 r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    obtain ⟨h1, h2⟩ := hwReadKraus_ne_zero_keep hc r (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK
    exact hP _ _ h1 h2 hq

theorem stepR_prog (m₀ : Finset HPos × M) (c : HwProg X Z)
    (hP : ∀ r r', r'.2 = (progUpdate c r.2.1, r.2.2) → P r → P' r') :
    StepR m₀ (.inl (.inr c)) P P' := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    hP _ _ (hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK) hq

theorem stepR_rec (m₀ : Finset HPos × M) (T : Finset HPos)
    (hP : ∀ r r', r'.2 = (r.2.1, (r.2.2.1 ∪ T, r.2.2.2)) → P r → P' r') :
    StepR m₀ (.inr T) P P' := by
  intro r σ hσ
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    hP _ _ (recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK) hq

/-- An operator supported on a set of register states presents, at a call, no diagonal mass
outside it. -/
theorem relabel_diag_eq_zero_of_supp (m₀ : Finset HPos × M)
    {S : Set (HwReg X Z (Finset HPos × M))} {A : QReg} {i : (recHwSpec X Z HPos M).Port}
    (E : QReg) (ℓ : A ≃ (recHwSpec X Z HPos M).In i × E)
    {ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) S ρ)
    (a : ((recHwSpec X Z HPos M).In i × (runtimeR m₀).D) × E) (ha : a.1.2 ∉ S) :
    (SubInstrument.relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).branch () ρ a a =
      0 := by
  by_contra h
  have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).imp
    (q' := fun m : ((recHwSpec X Z HPos M).In i × (runtimeR m₀).D) × E ↦ m.1.2)
    (S' := S) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  exact ha (h₁ a a h).1

/-- One call of a realized program, from support on `P` to support on `P'`. -/
theorem forallQueries_queryBind_of_stepR {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    (m₀ : Finset HPos × M) (I : L.Interp)
    {Sup : ∀ (i : (recHwSpec X Z HPos M).Port) (E : QReg),
      Matrix (((recHwSpec X Z HPos M).In i × (runtimeR m₀).D) × E)
        (((recHwSpec X Z HPos M).In i × (runtimeR m₀).D) × E) ℂ → Prop}
    {A : QReg} (i : (recHwSpec X Z HPos M).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z HPos M).In i × E)
    (k' : (recHwSpec X Z HPos M).Result i → QuantumComp L (recHwSpec X Z HPos M) Ω
      (QReg.of ((recHwSpec X Z HPos M).Out i × E)))
    (hpre : ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | P s} ρ →
        Sup i E ((SubInstrument.relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).branch
          () ρ))
    (hstep : StepR m₀ i P P')
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of ((recHwSpec X Z HPos M).Out i × E) ×
        (runtimeR m₀).D ↦ m.2) {s | P' s} ρ' → (runtimeR m₀).ForallQueries I Sup (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | P s} ρ) :
    (runtimeR m₀).ForallQueries I Sup (QuantumComp.queryBind i E ℓ k') ρ :=
  ⟨hpre ρ hρ, fun r ↦
    hk r _ (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) i r (hstep r) E ℓ hρ)⟩

end steps

/-! ## Templates that keep the invariant

`HP pub v y C C'`: run from states on the pending invariant `C`, the template `y` calls the sponge,
read and reveal ports with nothing pending, its read ports keep the label, a program port leaves the
pending set, a reveal of `T` adds the ports of the slots with an input in `T`; it ends on `C'`. -/

section hp

variable {M : Type} {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- The condition of `HP` on the pending set before a call. -/
def portPre : (SSpec M).Port → Set (HwProg X Z) → Prop
  | .inl (.inl (.inl _)), C => C = ∅
  | .inl (.inl (.inr c)), C => C = ∅ ∧ LabKeep c.1
  | .inl (.inr _), _ => True
  | .inr _, C => C = ∅

/-- The pending set after a call. -/
def portPost (pub : Pub) (v : (s : HPos) → XD s) :
    (SSpec M).Port → Set (HwProg X Z) → Set (HwProg X Z)
  | .inl (.inl (.inl _)), C => C
  | .inl (.inl (.inr _)), C => C
  | .inl (.inr p), C => C \ {p.1.realize v}
  | .inr T, C => C ∪ revealSet pub v T

/-- The condition before a command. -/
def cmdPre {A : QReg} : QuantumComp.Cmd L (SSpec M) A → Set (HwProg X Z) → Prop
  | .prim _, _ => True
  | .query i _ _, C => portPre i C

/-- The pending set after a command. -/
def cmdPost (pub : Pub) (v : (s : HPos) → XD s) {A : QReg} :
    QuantumComp.Cmd L (SSpec M) A → Set (HwProg X Z) → Set (HwProg X Z)
  | .prim _, C => C
  | .query i _ _, C => portPost pub v i C

/-- **A template that keeps the invariant**, from the pending set `C` to the pending set `C'`. -/
def HP (pub : Pub) (v : (s : HPos) → XD s) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A → Set (HwProg X Z) →
      Set (HwProg X Z) → Prop
  | _, .pure _, C, C' => C ⊆ C'
  | _, .liftBind c next, C, C' => cmdPre c C ∧ ∀ b, HP pub v (next b) (cmdPost pub v c C) C'

theorem cmdPre_anti {A : QReg} (c : QuantumComp.Cmd L (SSpec M) A) {C D : Set (HwProg X Z)}
    (hD : D ⊆ C) (h : cmdPre c C) : cmdPre c D := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · trivial
  · exact Set.subset_empty_iff.1 (h ▸ hD)
  · exact ⟨Set.subset_empty_iff.1 (h.1 ▸ hD), h.2⟩
  · trivial
  · exact Set.subset_empty_iff.1 (h ▸ hD)

theorem cmdPost_mono (pub : Pub) (v : (s : HPos) → XD s) {A : QReg}
    (c : QuantumComp.Cmd L (SSpec M) A) {C D : Set (HwProg X Z)} (hD : D ⊆ C) :
    cmdPost pub v c D ⊆ cmdPost pub v c C := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · exact hD
  · exact hD
  · exact hD
  · exact Set.sdiff_subset_sdiff_left hD
  · exact Set.union_subset_union_left _ hD

variable (pub : Pub) (v : (s : HPos) → XD s)

theorem hp_mono {A : QReg} (y : IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A)
    {C C' D D' : Set (HwProg X Z)} (hy : HP pub v y C C') (hD : D ⊆ C) (hD' : C' ⊆ D') :
    HP pub v y D D' := by
  induction y using IFreeM.inductionOn generalizing C D with
  | pure _ _ => exact hD.trans (hy.trans hD')
  | liftBind _ c next ih =>
    exact ⟨cmdPre_anti c hD hy.1, fun b ↦ ih b (hy.2 b) (cmdPost_mono pub v c hD)⟩

theorem hp_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A) (C C' : Set (HwProg X Z)) :
    HP pub v (e ▸ y) C C' ↔ HP pub v y C C' := by
  subst e
  rfl

theorem hp_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Y u)
    {C D C' : Set (HwProg X Z)} (hx : HP pub v x C D) (hg : ∀ u a, HP pub v (g u a) D C') :
    HP pub v (x.bind g) C C' := by
  induction x using IFreeM.inductionOn generalizing C with
  | pure _ a => exact hp_mono pub v _ (hg _ a) hx subset_rfl
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem hp₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L (SSpec M) A B α) (g : α → QuantumComp₂ L (SSpec M) B B' β)
    {C D C' : Set (HwProg X Z)} (hx : HP pub v x C D) (hg : ∀ a, HP pub v (g a) D C') :
    HP pub v (x.bind g) C C' := by
  refine hp_bind pub v x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

/-- Substituting trees that keep the invariant with nothing pending. -/
theorem hp_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor L spec)
      (QuantumComp.toIPFunctor L (SSpec M)))
    (hσ : ∀ A c, HP pub v (σ A c) ∅ ∅) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L spec) Ω A) : HP pub v (x.substitute σ) ∅ ∅ := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact hp_bind pub v _ _ (hσ s c) fun u ans ↦ (hp_cast pub v ans.2 _ _ _).mpr (ih ans.1)

/-- **Runtime 1's programs keep the invariant**: their sponge and read ports (the reads lifted,
keeping the label) leave nothing pending. -/
theorem hp_readLift {A : QReg} (y : QuantumComp L (hwReadSpec X Z M) Ω A) :
    HP pub v (readLift goodAll y) ∅ ∅ := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind _ c next ih =>
    show HP pub v (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next)) ∅ ∅
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨rfl, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨⟨rfl, labKeep_liftRead c⟩, fun b ↦ ?_⟩
      dsimp only
      exact ih _

theorem hp_act {A B : QReg} {α : Type} (p : SubInstrument A B α) (C : Set (HwProg X Z)) :
    HP pub v (QComp.act (spec := SSpec M) p) C C :=
  ⟨trivial, fun _ ↦ subset_rfl⟩

/-- A reveal with nothing pending makes the ports of the slots with an input in `T` pending. -/
theorem hp_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B B' α) {C' : Set (HwProg X Z)}
    (hk : ∀ r, HP pub v (k r) (revealSet pub v T) C') :
    HP pub v (revealThen goodAll T k) ∅ C' :=
  ⟨rfl, fun r ↦ hp₂_bind pub v _ _ (hp_act pub v _ _) fun _ ↦
    hp_mono pub v _ (hk r.down) (Set.empty_union _).le subset_rfl⟩

theorem hp_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec M) B B' α) {C C' : Set (HwProg X Z)}
    (hk : HP pub v k (C \ {p.realize v}) C') : HP pub v (progThen p hp k) C C' :=
  ⟨trivial, fun _ ↦ hp₂_bind pub v _ _ (hp_act pub v _ _) fun _ ↦ hk⟩

theorem hp_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) (C : Set (HwProg X Z)) :
    HP pub v (progPorts M B ps) C (C \ {c | ∃ p ∈ ps, p.realize v = c}) := by
  induction ps generalizing C with
  | nil => exact fun c hc ↦ ⟨hc, fun ⟨_, hp, _⟩ ↦ absurd hp List.not_mem_nil⟩
  | cons p ps ih =>
    refine hp_progThen pub v p trivial _ (hp_mono pub v _ (ih _) subset_rfl ?_)
    rintro c ⟨⟨hc, hne⟩, hn⟩
    refine ⟨hc, ?_⟩
    rintro ⟨p', hp', rfl⟩
    rcases List.mem_cons.1 hp' with rfl | hp'
    · exact hne (Set.mem_singleton _)
    · exact hn ⟨p', hp', rfl⟩

theorem hp_progSlots (B : QReg) (ss : List Slot) (C : Set (HwProg X Z)) :
    HP pub v (progSlots M pub B ss) C (C \ portsOf pub v ss) := by
  induction ss generalizing C with
  | nil => exact fun c hc ↦ ⟨hc, fun ⟨_, hs, _⟩ ↦ absurd hs List.not_mem_nil⟩
  | cons s ss ih =>
    refine hp₂_bind pub v _ _ (hp_progPorts pub v B (slotPorts pub s) C) fun _ ↦
      hp_mono pub v _ (ih _) subset_rfl ?_
    rintro c ⟨⟨hc, h1⟩, h2⟩
    refine ⟨hc, ?_⟩
    rintro ⟨s', hs', p, hp, rfl⟩
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact h1 ⟨p, hp, rfl⟩
    · exact h2 ⟨s', hs', p, hp, rfl⟩

/-- **A FORS opening keeps the invariant**: the slots with a revealed input are the opening's
slots, which it then programs. -/
theorem hp_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    HP pub v (forsOpenT M pub B idx lv) ∅ ∅ :=
  hp_revealThen pub v _ _ fun _ ↦ hp₂_bind pub v _ _ (hp_progSlots pub v B _ _) fun _ ↦ by
    rintro c ⟨hc, hn⟩
    exact hn (revealSet_forsNeed_subset pub v idx lv hc)

variable (upd : TrialUpd M)

/-- **A layer signature keeps the invariant**: the reveal of the value it signs makes nothing
pending (it is no slot's input), the counter search reads, the reveal of `layerNeed` makes the
ports of the slots with a revealed input pending, and those slots are the signature's slots, which
it then programs. -/
theorem hp_signLayerT (B : QReg) (K : Key) : HP pub v (signLayerT M upd pub B K) ∅ ∅ := by
  refine hp_revealThen pub v _ _ fun _ ↦ hp_mono pub v _
    (hp₂_bind pub v _ _ (hp_readLift pub v _) fun g ↦ ?_) (revealSet_msgPos pub v K) subset_rfl
  rcases g with _ | ⟨cnt, x⟩
  · exact subset_rfl
  · refine hp_revealThen pub v _ _ fun r ↦
      hp₂_bind pub v _ _ (hp_progSlots pub v B _ _) fun _ ↦ ?_
    rintro c ⟨hc, hn⟩
    exact hn (revealSet_layerNeed_subset pub v _ _ _ x hc)

/-- **A signature keeps the invariant**, for a digest policy revealing no value position: the
reveals of the root, the randomizer and the digest make nothing pending, the `H_msg` programs
remove ports, then the FORS opening and the three layer signatures. -/
theorem hp_signT {pol : DigestPolicy} (hpol : pol.ValFree) (B : QReg) (msg : Message) :
    HP pub v (signT M upd pol pub B msg) ∅ ∅ := by
  refine hp_revealThen pub v _ _ fun r₁ ↦ hp_mono pub v _ (hp_revealThen pub v _ _ fun r₂ ↦
    hp_mono pub v _ ?_ (revealSet_valFree pub v hpol _ msg) subset_rfl)
    (revealSet_rootPos_rnd pub v msg) subset_rfl
  refine hp₂_bind pub v _ _ (hp_mono pub v _ (hp_progPorts pub v B _ ∅) subset_rfl
    Set.sdiff_subset) fun _ ↦ ?_
  refine hp₂_bind pub v _ _ (hp_forsOpenT pub v B _ _) fun _ ↦ ?_
  refine hp₂_bind pub v _ _ (hp_signLayerT pub v upd B _) fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · exact subset_rfl
  · refine hp₂_bind pub v _ _ (hp_signLayerT pub v upd B _) fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · exact subset_rfl
    · refine hp₂_bind pub v _ _ (hp_signLayerT pub v upd B _) fun s₂ ↦ ?_
      rcases s₂ with _ | top <;> exact subset_rfl

/-- **The challenger keeps the invariant**, with nothing pending between commands. -/
theorem hp_challengeT {pol : DigestPolicy} (hpol : pol.ValFree) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    HP pub v (challengeT M upd pol pub A c) ∅ ∅ := by
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact hp_readLift pub v _
  · exact hp_readLift pub v _
  · exact hp_bind pub v _ _ (hp₂_bind pub v _ _ (hp_act pub v _ _) fun _ ↦
      hp_signT pub v upd hpol _ msg) fun _ _ ↦ subset_rfl

/-- **The game keeps the invariant**: the root's reveal makes nothing pending (the root is no
slot's input), then the challenged adversary and the verification. -/
theorem hp_gameT {pol : DigestPolicy} (hpol : pol.ValFree) (A : SAdversary) :
    HP pub v (gameT M upd pol pub A) ∅ ∅ :=
  hp_revealThen pub v _ _ fun _ ↦ hp_mono pub v _
    (hp₂_bind pub v _ _ (hp_substitute pub v _ (hp_challengeT pub v upd hpol) _) fun _ ↦
      hp₂_bind pub v _ _ (hp_readLift pub v _) fun _ ↦ subset_rfl)
    (revealSet_rootPos pub v) subset_rfl

end hp

/-! ## `hinv` -/

section hinv

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

theorem stepInv_sponge (m₀ : Finset HPos × M) (pub : Pub) (v : (s : HPos) → XD s)
    (i : SpongePort) (C : Set (HwProg X Z)) :
    StepR m₀ (.inl (.inl (.inl i))) (fun s ↦ InvP pub v C s) (fun s ↦ InvP pub v C s) :=
  stepR_sponge m₀ i fun _ _ he hr ↦ invP_of_eq (congrArg Prod.fst he)
    (congrArg (fun t ↦ t.2.1) he) hr

theorem stepInv_read (m₀ : Finset HPos × M) (pub : Pub) (v : (s : HPos) → XD s)
    (c : {c : HwRead X Z (Finset HPos × M) // ReadMono (memLab X Z HPos M) c})
    (hc : LabKeep c.1) (C : Set (HwProg X Z)) :
    StepR m₀ (.inl (.inl (.inr c.1))) (fun s ↦ InvP pub v C s) (fun s ↦ InvP pub v C s) :=
  stepR_readKeep m₀ c hc fun _ _ h1 h2 hr ↦ invP_of_eq h1 h2 hr

theorem stepInv_prog (m₀ : Finset HPos × M) (pub : Pub) (v : (s : HPos) → XD s)
    (c : HwProg X Z) (C : Set (HwProg X Z)) :
    StepR m₀ (.inl (.inr c)) (fun s ↦ InvP pub v C s) (fun s ↦ InvP pub v (C \ {c}) s) :=
  stepR_prog m₀ c fun _ _ h hr ↦ invP_prog c h hr

theorem stepInv_rec (m₀ : Finset HPos × M) (pub : Pub) (v : (s : HPos) → XD s)
    (T : Finset HPos) (C : Set (HwProg X Z)) :
    StepR m₀ (.inr T) (fun s ↦ InvP pub v C s) (fun s ↦ InvP pub v (C ∪ revealSet pub v T) s) :=
  stepR_rec m₀ T fun _ _ h hr ↦ invP_reveal T h hr

/-- One call of a realized program on the pending invariant. -/
theorem forallQueries_queryBind_of_stepInv {Q : (recHwSpec X Z HPos M).Port → Prop}
    (m₀ : Finset HPos × M) (I : L.Interp) (pub : Pub) (v : (s : HPos) → XD s) {A : QReg}
    (i : (recHwSpec X Z HPos M).Port) (E : QReg) (ℓ : A ≃ (recHwSpec X Z HPos M).In i × E)
    (k' : (recHwSpec X Z HPos M).Result i → QuantumComp L (recHwSpec X Z HPos M) Ω
      (QReg.of ((recHwSpec X Z HPos M).Out i × E)))
    {C C' : Set (HwProg X Z)} (hpre : Q i → C = ∅)
    (hstep : StepR m₀ i (fun s ↦ InvP pub v C s) (fun s ↦ InvP pub v C' s))
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of ((recHwSpec X Z HPos M).Out i × E) ×
        (runtimeR m₀).D ↦ m.2) {s | InvP pub v C' s} ρ' →
      (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (SlotInv M pub v)) (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | InvP pub v C s} ρ) :
    (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (SlotInv M pub v))
      (QuantumComp.queryBind i E ℓ k') ρ :=
  forallQueries_queryBind_of_stepR (Sup := invSupp (runtimeR m₀) Q (SlotInv M pub v))
    (P := fun s ↦ InvP pub v C s) (P' := fun s ↦ InvP pub v C' s) m₀ I i E ℓ k'
    (fun _ hρ hq a ha ↦ relabel_diag_eq_zero_of_supp m₀ E ℓ (hpre hq ▸ hρ) a
      fun h ↦ ha (slotInv_of_invP h)) hstep hk ρ hρ

/-- **The realized program of a template keeping the invariant presents, at every call of the
ports `Q` (no program port), only states of the invariant.** -/
theorem forallQueries_of_hp {Q : (recHwSpec X Z HPos M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (m₀ : Finset HPos × M) (I : L.Interp) (pub : Pub)
    (v : (s : HPos) → XD s) {A : QReg} (y : QuantumComp L (SSpec M) Ω A) :
    ∀ C C', HP pub v y C C' → ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | InvP pub v C s} ρ →
      (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (SlotInv M pub v))
        (realizeT v y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro C C' hy ρ hρ b
    exact ih b C C' (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro C C' hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_of_stepInv m₀ I pub v (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT v (k r)) (fun _ ↦ hy.1) (stepInv_sponge m₀ pub v i C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepInv m₀ I pub v (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT v (k r)) (fun _ ↦ hy.1.1) (stepInv_read m₀ pub v c hy.1.2 C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_stepInv m₀ I pub v
          (.inl (.inr ((LazyProg.programH T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepInv_prog m₀ pub v _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_stepInv m₀ I pub v
          (.inl (.inr ((LazyProg.programK T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepInv_prog m₀ pub v _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_stepInv m₀ I pub v
          (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepInv_prog m₀ pub v _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepInv m₀ I pub v (.inr T) E ℓ
        (fun m ↦ realizeT v (k (restrictTo T v, m))) (fun _ ↦ hy.1) (stepInv_rec m₀ pub v T C)
        (fun m ↦ ih (restrictTo T v, m) _ C' (hy.2 (ULift.up (restrictTo T v, m)))) ρ hρ

/-- An initial state whose memory label is empty is on the invariant. -/
theorem querySupportedOn_init (m₀ : Finset HPos × M) (hm₀ : m₀.1 = ∅) {A : QReg}
    (σ : Matrix A A ℂ) :
    QuerySupportedOn (fun a : A × QReg.of (HwReg X Z (Finset HPos × M)) ↦ a.2.2.2.1) {∅}
      (σ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  intro a b h
  change (σ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
    hwEmpty X Z, m₀) : HwReg X Z (Finset HPos × M))).matrix) a b ≠ 0 at h
  rw [SubState.matrix_basis, kroneckerMap_apply] at h
  have h' := right_ne_zero_of_mul h
  rw [Matrix.single_apply] at h'
  split_ifs at h' with he
  · show a.2.2.2.1 ∈ ({∅} : Set (Finset HPos)) ∧ b.2.2.2.1 ∈ ({∅} : Set (Finset HPos))
    rw [← he.1, ← he.2]
    exact ⟨hm₀, hm₀⟩
  · exact absurd rfl h'

variable (upd : TrialUpd M)

/-- **`hinv` for the realized template game**, at every public datum and digest policy revealing
no value position: from states with an empty memory label, every call of ports `Q` that are not
program ports sees the invariant `SlotInv`. -/
theorem forallQueries_gameT {pol : DigestPolicy} (hpol : pol.ValFree)
    {Q : (recHwSpec X Z HPos M).Port → Prop} (hQ : ∀ c, ¬Q (.inl (.inr c)))
    (m₀ : Finset HPos × M) (pub : Pub) (A : SAdversary) (v : (s : HPos) → XD s)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      a.2.2.2.1) {∅} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Q (SlotInv M pub v)) (realizeT v (gameT M upd pol pub A)) ρ :=
  forallQueries_of_hp hQ m₀ _ pub v _ ∅ ∅ (hp_gameT pub v upd hpol A) ρ
    (hρ.imp fun _ ha ↦ invP_of_label_empty (Set.mem_singleton_iff.1 ha))

/-- **Masses' `hinv`** with `Inv p v := SlotInv M (pubP p) v`, for any `pubP` and any digest policy
revealing no value position. -/
theorem hinv_gameT {P : Type} (pubP : P → Pub) {pol : DigestPolicy} (hpol : pol.ValFree)
    {Q : (recHwSpec X Z HPos M).Port → Prop} (hQ : ∀ c, ¬Q (.inl (.inr c)))
    (m₀ : Finset HPos × M) (A : SAdversary)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      a.2.2.2.1) {∅} ρ) :
    ∀ p v, (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Q ((fun p v ↦ SlotInv M (pubP p) v) p v))
      (realizeT v (gameT M upd pol (pubP p) A)) ρ :=
  fun p v ↦ forallQueries_gameT upd hpol hQ m₀ (pubP p) A v ρ hρ

/-- **The read mass is the hidden mass at the read and record ports.** -/
theorem readMass_eq_portMass (Hh : Set Z) (Hk Hk' : Set X) :
    readMass (S := HPos) (M' := M) Hh Hk Hk' =
      portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk' := by
  funext i σ
  rcases i with ((i | c) | c) | T
  · rfl
  · rfl
  · rfl
  · rfl

omit [Fintype M] [DecidableEq M] in
theorem readRecPort_prog (c : HwProg X Z) : ¬readRecPort M (.inl (.inr c)) = true :=
  Bool.false_ne_true

end hinv

/-! ## Batches of program ports

The ports of an absorption are called in order `k`, `k'`, `h`, round by round. `HB ok v y C C'`:
run from states holding the cells of `C` with their programmed values, every program port of the
template `y` satisfies `ok` at the states holding `C`, ending holding `C'`. A program port adds its
cell and keeps the cells agreeing with it (`heldNext`). -/

section heldGen

variable {X₁ Z₁ : Type} [DecidableEq X₁] [DecidableEq Z₁]

/-- `W` holds the cell of the program port `c` with its value. -/
def CellHeld : HwProg X₁ Z₁ → Hw X₁ Z₁ → Prop
  | .programH z a, W => W.1 z = some a
  | .programK x a, W => W.2.1 x = some a
  | .programK' x a, W => W.2.2 x = some a

/-- Two program ports agree on a common cell. -/
def Compat : HwProg X₁ Z₁ → HwProg X₁ Z₁ → Prop
  | .programH z a, .programH z' a' => z' = z → a' = a
  | .programK x a, .programK x' a' => x' = x → a' = a
  | .programK' x a, .programK' x' a' => x' = x → a' = a
  | _, _ => True

theorem cellHeld_progUpdate_self (c : HwProg X₁ Z₁) (W : Hw X₁ Z₁) :
    CellHeld c (progUpdate c W) := by
  cases c with
  | programH z a => exact Function.update_self z (some a) W.1
  | programK x a => exact Function.update_self x (some a) W.2.1
  | programK' x a => exact Function.update_self x (some a) W.2.2

/-- Programming a cell keeps every cell agreeing with it. -/
theorem cellHeld_progUpdate {c c' : HwProg X₁ Z₁} {W : Hw X₁ Z₁} (h : CellHeld c' W)
    (hc : Compat c c') : CellHeld c' (progUpdate c W) := by
  cases c with
  | programH z a =>
    cases c' with
    | programH z' a' =>
      show Function.update W.1 z (some a) z' = some a'
      by_cases hz : z' = z
      · subst hz
        rw [Function.update_self, hc rfl]
      · rw [Function.update_of_ne hz]
        exact h
    | programK => exact h
    | programK' => exact h
  | programK x a =>
    cases c' with
    | programH => exact h
    | programK x' a' =>
      show Function.update W.2.1 x (some a) x' = some a'
      by_cases hx : x' = x
      · subst hx
        rw [Function.update_self, hc rfl]
      · rw [Function.update_of_ne hx]
        exact h
    | programK' => exact h
  | programK' x a =>
    cases c' with
    | programH => exact h
    | programK => exact h
    | programK' x' a' =>
      show Function.update W.2.2 x (some a) x' = some a'
      by_cases hx : x' = x
      · subst hx
        rw [Function.update_self, hc rfl]
      · rw [Function.update_of_ne hx]
        exact h

/-- `W` holds the cells of the program ports `C` with their values. -/
def AllHeld (C : Set (HwProg X₁ Z₁)) (W : Hw X₁ Z₁) : Prop :=
  ∀ c ∈ C, CellHeld c W

/-- The held ports after programming `c`: `c` and the ports of `C` agreeing with it. -/
def heldNext (c : HwProg X₁ Z₁) (C : Set (HwProg X₁ Z₁)) : Set (HwProg X₁ Z₁) :=
  insert c {c' | c' ∈ C ∧ Compat c c'}

theorem allHeld_progUpdate {C : Set (HwProg X₁ Z₁)} {W : Hw X₁ Z₁} (h : AllHeld C W)
    (c : HwProg X₁ Z₁) : AllHeld (heldNext c C) (progUpdate c W) := by
  intro c' hc'
  rcases Set.mem_insert_iff.1 hc' with rfl | ⟨hc', hco⟩
  · exact cellHeld_progUpdate_self _ _
  · exact cellHeld_progUpdate (h c' hc') hco

omit [DecidableEq X₁] [DecidableEq Z₁] in
theorem heldNext_mono (c : HwProg X₁ Z₁) {C D : Set (HwProg X₁ Z₁)} (h : D ⊆ C) :
    heldNext c D ⊆ heldNext c C :=
  Set.insert_subset_insert fun _ hc ↦ ⟨h hc.1, hc.2⟩

omit [DecidableEq X₁] [DecidableEq Z₁] in
theorem mem_heldNext {c c' : HwProg X₁ Z₁} {C : Set (HwProg X₁ Z₁)} (h : c' ∈ C)
    (hc : Compat c c') : c' ∈ heldNext c C :=
  Set.mem_insert_of_mem _ ⟨h, hc⟩

theorem progUpdateH_self (z : Z₁) (a : X₁) (W : Hw X₁ Z₁) :
    (progUpdate (.programH z a) W).toDbs.h z = some a := by
  show Function.update W.1 z (some a) z = some a
  exact Function.update_self z (some a) W.1

theorem progUpdateH_of_ne {z z' : Z₁} (a : X₁) (W : Hw X₁ Z₁) (h : z' ≠ z) :
    (progUpdate (.programH z a) W).toDbs.h z' = W.toDbs.h z' :=
  Function.update_of_ne h _ _

theorem progUpdateH_k (z : Z₁) (a : X₁) (W : Hw X₁ Z₁) :
    (progUpdate (.programH z a) W).toDbs.k = W.toDbs.k :=
  rfl

theorem progUpdateH_k' (z : Z₁) (a : X₁) (W : Hw X₁ Z₁) :
    (progUpdate (.programH z a) W).toDbs.k' = W.toDbs.k' :=
  rfl

end heldGen

section held

variable (pub : Pub)

/-- The realized `k` port of round `j` of the absorption of the blocks `b`. -/
def rK (b : ℕ → X) (j : ℕ) : HwProg X Z :=
  .programK (cellK pub b j).1 (cellK pub b j).2

/-- The realized `k'` port of round `j`. -/
def rK' (b : ℕ → X) (j : ℕ) : HwProg X Z :=
  .programK' (cellK' pub b j).1 (cellK' pub b j).2

/-- The realized `h` port of round `j` (last round `last`, correction `cor`). -/
def rH (b : ℕ → X) (last : ℕ) (cor : X → X → X) (j : ℕ) : HwProg X Z :=
  .programH (cellH pub b last cor j).1 (cellH pub b last cor j).2

/-- The realized ports of the rounds before `a`. -/
def doneTo (b : ℕ → X) (last : ℕ) (cor : X → X → X) (a : ℕ) : Set (HwProg X Z) :=
  {c | ∃ i < a, c = rK pub b i ∨ c = rK' pub b i ∨ c = rH pub b last cor i}

theorem roundHeld_of_allHeld {b : ℕ → X} {last : ℕ} {cor : X → X → X} {a : ℕ} {W : Hw X Z}
    {C : Set (HwProg X Z)} (hC : doneTo pub b last cor a ⊆ C) (h : AllHeld C W) :
    ∀ i < a, RoundHeld pub W.toDbs b last cor i := fun i hi ↦
  ⟨h _ (hC ⟨i, hi, Or.inl rfl⟩), h _ (hC ⟨i, hi, Or.inr (Or.inl rfl)⟩),
    h _ (hC ⟨i, hi, Or.inr (Or.inr rfl)⟩)⟩

/-- The rounds before `a ≤ last` agree with the `k`, `k'` and (for `j ≠ last`) `h` ports of round
`j`: the values of the earlier cells are the keys' values. -/
theorem compat_doneTo {b : ℕ → X} {last : ℕ} {cor : X → X → X} {a : ℕ} (ha : a ≤ last)
    {c : HwProg X Z} (hc : c ∈ doneTo pub b last cor a) (j : ℕ) :
    Compat (rK pub b j) c ∧ Compat (rK' pub b j) c ∧
      (j ≠ last → Compat (rH pub b last cor j) c) := by
  obtain ⟨i, hi, rfl | rfl | rfl⟩ := hc
  · exact ⟨fun h ↦ congrArg pub.keys.2.1 h, trivial, fun _ ↦ trivial⟩
  · exact ⟨trivial, fun h ↦ congrArg pub.keys.2.2 h, fun _ ↦ trivial⟩
  · refine ⟨trivial, trivial, fun hj h ↦ ?_⟩
    show (cellH pub b last cor i).2 = (cellH pub b last cor j).2
    rw [cellH_snd, cellH_snd, ite_eq_right (by omega), ite_eq_right hj,
      ← cellH_fst pub b last cor i, ← cellH_fst pub b last cor j]
    exact congrArg pub.keys.1 h

variable {M : Type}

/-- **A condition `ok` holds at each port of an absorption** (blocks `b`, `n` rounds, last
correction `cor`), once the earlier rounds are held with their programmed values, and at the `k'`
and `h` ports of a round once its `k` (and `k'`) cell is. -/
def BatchOk (ok : HwProg X Z → HwReg X Z (Finset HPos × M) → Prop) (b : ℕ → X)
    (cor : X → X → X) (n : ℕ) : Prop :=
  ∀ j < n, ∀ r : HwReg X Z (Finset HPos × M),
    (∀ i < j, RoundHeld pub r.2.1.toDbs b (n - 1) cor i) →
      ok (rK pub b j) r ∧ (r.2.1.toDbs.k (cellK pub b j).1 = some (cellK pub b j).2 →
        ok (rK' pub b j) r ∧ (r.2.1.toDbs.k' (cellK' pub b j).1 = some (cellK' pub b j).2 →
          ok (rH pub b (n - 1) cor j) r))

/-- **After the final `h` program of a structural slot, the slot is exempted** (Events' `exS`,
obligation (1) of the event): before it the earlier rounds and the final `k`, `k'` cells are held
(as `BatchOk`'s hypotheses give), and the final `h`-cell is none of the earlier ones. -/
theorem mem_exS_progUpdate_final (v : (s : HPos) → XD s) {s : Slot} (hs : InTable s)
    {W : Hw X Z}
    (hW : ∀ i < nBlk pub.seed s - 1, RoundHeld pub W.toDbs (slotBlk pub.seed s (valsOf v))
      (nBlk pub.seed s - 1) (cor128 (valsOf v (slotOutPos s))) i)
    (hk : W.toDbs.k (cellK pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1)).1 =
      some (cellK pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1)).2)
    (hk' : W.toDbs.k' (cellK' pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1)).1 =
      some (cellK' pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1)).2)
    (hsep : FinalSep pub v s) :
    s ∈ (evData pub v).exS (progUpdate (rH pub (slotBlk pub.seed s (valsOf v))
      (nBlk pub.seed s - 1) (cor128 (valsOf v (slotOutPos s))) (nBlk pub.seed s - 1)) W) := by
  refine mem_exS_of_cells pub v hs (fun j hj ↦ ?_) hsep
  rw [rH]
  by_cases hjl : j = nBlk pub.seed s - 1
  · subst hjl
    refine ⟨?_, ?_, ?_⟩
    · rw [progUpdateH_k]
      exact hk
    · rw [progUpdateH_k']
      exact hk'
    · rw [progUpdateH_self]
  · obtain ⟨u1, u2, u3⟩ := hW j (by omega)
    have hne : (cellH pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1)
        (cor128 (valsOf v (slotOutPos s))) j).1 ≠ (cellH pub (slotBlk pub.seed s (valsOf v))
        (nBlk pub.seed s - 1) (cor128 (valsOf v (slotOutPos s))) (nBlk pub.seed s - 1)).1 := by
      rw [cellH_fst, cellH_fst]
      exact hsep j (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [progUpdateH_k]
      exact u1
    · rw [progUpdateH_k']
      exact u2
    · rw [progUpdateH_of_ne _ _ hne]
      exact u3

end held

section hb

variable {M : Type} {L : LocalSig.{u, v}} {Ω : QReg → Type w}
  (ok : HwProg X Z → HwReg X Z (Finset HPos × M) → Prop) (v : (s : HPos) → XD s)

/-- **A program port satisfies `ok` given the held cells `C`.** -/
def OkC (C : Set (HwProg X Z)) (c : HwProg X Z) : Prop :=
  ∀ r : HwReg X Z (Finset HPos × M), AllHeld C r.2.1 → ok c r

variable {ok} in
theorem OkC.anti {C D : Set (HwProg X Z)} {c : HwProg X Z} (h : OkC ok D c) (hD : D ⊆ C) :
    OkC ok C c :=
  fun r hC ↦ h r fun c' hc' ↦ hC c' (hD hc')

/-- The condition on a port before a call: a program port satisfies `ok` given `C`. -/
def portOk : (SSpec M).Port → Set (HwProg X Z) → Prop
  | .inl (.inr p), C => OkC ok C (p.1.realize v)
  | _, _ => True

/-- The held ports after a call: a program port adds its own. -/
def portNext : (SSpec M).Port → Set (HwProg X Z) → Set (HwProg X Z)
  | .inl (.inr p), C => heldNext (p.1.realize v) C
  | _, C => C

/-- The condition before a command. -/
def cmdOk {A : QReg} : QuantumComp.Cmd L (SSpec M) A → Set (HwProg X Z) → Prop
  | .prim _, _ => True
  | .query i _ _, C => portOk ok v i C

/-- The held ports after a command. -/
def cmdNext {A : QReg} : QuantumComp.Cmd L (SSpec M) A → Set (HwProg X Z) → Set (HwProg X Z)
  | .prim _, C => C
  | .query i _ _, C => portNext v i C

/-- **A template whose program ports satisfy `ok` in batch order**, run from the held ports `C`,
ending holding `C'`. -/
def HB : {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A →
    Set (HwProg X Z) → Set (HwProg X Z) → Prop
  | _, .pure _, C, C' => C' ⊆ C
  | _, .liftBind c next, C, C' => cmdOk ok v c C ∧ ∀ b, HB (next b) (cmdNext v c C) C'

theorem cmdOk_anti {A : QReg} (c : QuantumComp.Cmd L (SSpec M) A) {C D : Set (HwProg X Z)}
    (hD : D ⊆ C) (h : cmdOk ok v c D) : cmdOk ok v c C := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · trivial
  · trivial
  · trivial
  · exact OkC.anti h hD
  · trivial

theorem cmdNext_mono {A : QReg} (c : QuantumComp.Cmd L (SSpec M) A) {C D : Set (HwProg X Z)}
    (hD : D ⊆ C) : cmdNext v c D ⊆ cmdNext v c C := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · exact hD
  · exact hD
  · exact hD
  · exact heldNext_mono _ hD
  · exact hD

theorem hb_mono {A : QReg} (y : IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A)
    {C C' D D' : Set (HwProg X Z)} (hy : HB ok v y C C') (hD : C ⊆ D) (hD' : D' ⊆ C') :
    HB ok v y D D' := by
  induction y using IFreeM.inductionOn generalizing C D with
  | pure _ _ => exact hD'.trans (hy.trans hD)
  | liftBind _ c next ih =>
    exact ⟨cmdOk_anti ok v c hD hy.1, fun b ↦ ih b (hy.2 b) (cmdNext_mono v c hD)⟩

theorem hb_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A) (C C' : Set (HwProg X Z)) :
    HB ok v (e ▸ y) C C' ↔ HB ok v y C C' := by
  subst e
  rfl

theorem hb_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor L (SSpec M)) Y u)
    {C D C' : Set (HwProg X Z)} (hx : HB ok v x C D) (hg : ∀ u a, HB ok v (g u a) D C') :
    HB ok v (x.bind g) C C' := by
  induction x using IFreeM.inductionOn generalizing C with
  | pure _ a => exact hb_mono ok v _ (hg _ a) hx subset_rfl
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem hb₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L (SSpec M) A B α) (g : α → QuantumComp₂ L (SSpec M) B B' β)
    {C D C' : Set (HwProg X Z)} (hx : HB ok v x C D) (hg : ∀ a, HB ok v (g a) D C') :
    HB ok v (x.bind g) C C' := by
  refine hb_bind ok v x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

/-- Substituting trees whose program ports satisfy `ok` from nothing held. -/
theorem hb_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor L spec)
      (QuantumComp.toIPFunctor L (SSpec M)))
    (hσ : ∀ A c, HB ok v (σ A c) ∅ ∅) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L spec) Ω A) : HB ok v (x.substitute σ) ∅ ∅ := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact hb_bind ok v _ _ (hσ s c) fun u ans ↦ (hb_cast ok v ans.2 _ _ _).mpr (ih ans.1)

/-- Runtime 1's programs call no program port. -/
theorem hb_readLift {A : QReg} (y : QuantumComp L (hwReadSpec X Z M) Ω A)
    (C : Set (HwProg X Z)) : HB ok v (readLift goodAll y) C C := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind _ c next ih =>
    show HB ok v (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next)) C C
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _
    · refine ⟨trivial, fun b ↦ ?_⟩
      dsimp only
      exact ih _

theorem hb_act {A B : QReg} {α : Type} (p : SubInstrument A B α) (C : Set (HwProg X Z)) :
    HB ok v (QComp.act (spec := SSpec M) p) C C :=
  ⟨trivial, fun _ ↦ subset_rfl⟩

theorem hb_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B B' α)
    {C C' : Set (HwProg X Z)} (hk : ∀ r, HB ok v (k r) C C') :
    HB ok v (revealThen goodAll T k) C C' :=
  ⟨trivial, fun r ↦ hb₂_bind ok v _ _ (hb_act ok v _ _) fun _ ↦ hk r.down⟩

theorem hb_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec M) B B' α) {C C' : Set (HwProg X Z)}
    (hok : OkC ok C (p.realize v)) (hk : HB ok v k (heldNext (p.realize v) C) C') :
    HB ok v (progThen p hp k) C C' :=
  ⟨hok, fun _ ↦ hb₂_bind ok v _ _ (hb_act ok v _ _) fun _ ↦ hk⟩

/-- Calling the ports `ps ++ qs` is calling `ps`, then `qs`. -/
theorem progPorts_append (B : QReg) (ps qs : List (LazyProg X Z HPos XD)) :
    progPorts M B (ps ++ qs) = (progPorts M B ps).bind fun _ ↦ progPorts M B qs := by
  induction ps with
  | nil => exact (QuantumComp₂.pure_bind _ _).symm
  | cons p ps ih =>
    rw [List.cons_append, progPorts, progPorts, ih]
    rfl

variable (pub : Pub)

/-- **The rounds `a, …, a + m - 1` of an absorption**, in order, from the earlier rounds held. -/
theorem hb_rounds (B : QReg) (T₀ : Finset HPos) (bl : RevealVals XD T₀ → ℕ → X)
    (cor : RevealVals XD T₀ → X → X → X) (n : ℕ)
    (hok : BatchOk pub ok (bl (restrictTo T₀ v)) (cor (restrictTo T₀ v)) n) :
    ∀ m a, a + m = n → ∀ C, (m ≠ 0 →
      doneTo pub (bl (restrictTo T₀ v)) (n - 1) (cor (restrictTo T₀ v)) a ⊆ C) →
      HB ok v (progPorts M B ((List.range' a m).flatMap fun j ↦
        [.programK T₀ fun w ↦ cellK pub (bl w) j, .programK' T₀ fun w ↦ cellK' pub (bl w) j,
          .programH T₀ fun w ↦ cellH pub (bl w) (n - 1) (cor w) j])) C ∅
  | 0, _, _, C, _ => Set.empty_subset C
  | m + 1, a, hm, C, hC => by
    have hD := hC (Nat.succ_ne_zero m)
    have hk := hok a (by omega)
    have hla : a ≤ n - 1 := by omega
    have hD1 : doneTo pub (bl (restrictTo T₀ v)) (n - 1) (cor (restrictTo T₀ v)) a ⊆
        heldNext (rK pub (bl (restrictTo T₀ v)) a) C := fun c hc ↦
      mem_heldNext (hD hc) (compat_doneTo pub hla hc a).1
    have hD2 : doneTo pub (bl (restrictTo T₀ v)) (n - 1) (cor (restrictTo T₀ v)) a ⊆
        heldNext (rK' pub (bl (restrictTo T₀ v)) a)
          (heldNext (rK pub (bl (restrictTo T₀ v)) a) C) := fun c hc ↦
      mem_heldNext (hD1 hc) (compat_doneTo pub hla hc a).2.1
    have hK : rK pub (bl (restrictTo T₀ v)) a ∈ heldNext (rK' pub (bl (restrictTo T₀ v)) a)
        (heldNext (rK pub (bl (restrictTo T₀ v)) a) C) :=
      mem_heldNext (Set.mem_insert _ _) trivial
    have hD3 : m ≠ 0 →
        doneTo pub (bl (restrictTo T₀ v)) (n - 1) (cor (restrictTo T₀ v)) (a + 1) ⊆
          heldNext (rH pub (bl (restrictTo T₀ v)) (n - 1) (cor (restrictTo T₀ v)) a)
            (heldNext (rK' pub (bl (restrictTo T₀ v)) a)
              (heldNext (rK pub (bl (restrictTo T₀ v)) a) C)) := by
      rintro hm0 c ⟨i, hi, hc⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact mem_heldNext (hD2 ⟨i, hi, hc⟩)
          ((compat_doneTo pub hla ⟨i, hi, hc⟩ a).2.2 (by omega))
      · rcases hc with rfl | rfl | rfl
        · exact mem_heldNext hK trivial
        · exact mem_heldNext (Set.mem_insert _ _) trivial
        · exact Set.mem_insert _ _
    rw [List.range'_succ, List.flatMap_cons]
    refine hb_progThen ok v _ trivial _
      (fun r hr ↦ (hk r (roundHeld_of_allHeld pub hD hr)).1) ?_
    refine hb_progThen ok v _ trivial _
      (fun r hr ↦ ((hk r (roundHeld_of_allHeld pub hD1 hr)).2 (hr _ (Set.mem_insert _ _))).1) ?_
    refine hb_progThen ok v _ trivial _
      (fun r hr ↦ ((hk r (roundHeld_of_allHeld pub hD2 hr)).2 (hr _ hK)).2
        (hr _ (Set.mem_insert _ _))) ?_
    exact hb_rounds B T₀ bl cor n hok m (a + 1) (by omega) _ hD3

/-- **The ports of an absorption, in order**, from any held ports. -/
theorem hb_pathPorts (B : QReg) (T₀ : Finset HPos) (bl : RevealVals XD T₀ → ℕ → X)
    (cor : RevealVals XD T₀ → X → X → X) (n : ℕ)
    (hok : BatchOk pub ok (bl (restrictTo T₀ v)) (cor (restrictTo T₀ v)) n)
    (C : Set (HwProg X Z)) : HB ok v (progPorts M B (pathPorts pub T₀ bl cor n)) C ∅ := by
  rw [pathPorts, List.range_eq_range']
  exact hb_rounds ok v pub B T₀ bl cor n hok n 0 (Nat.zero_add n) C
    fun _ c ⟨i, hi, _⟩ ↦ absurd hi (Nat.not_lt_zero i)

/-- **The ports of an in-table structural slot**, in order. -/
theorem hb_slotPorts (B : QReg) {s : Slot} (hs : InTable s)
    (hslot : BatchOk pub ok (slotBlk pub.seed s (valsOf v)) (cor128 (valsOf v (slotOutPos s)))
      (nBlk pub.seed s))
    (C : Set (HwProg X Z)) : HB ok v (progPorts M B (slotPorts pub s)) C ∅ := by
  refine hb_pathPorts ok v pub B _ _ _ _ ?_ C
  rw [slotBlk_restrictTo,
    extendVals_restrictTo (val_mem_valSet.mpr (slotOutPos_mem_slotNeed hs)) v]
  exact hslot

theorem slotBlk_hmsg_restrictTo (pol : DigestPolicy) (T : Finset HPos) (msg : Message)
    (i : DigestCall) (R : Randomizer) :
    slotBlk pub.seed (.hmsg R msg i) (extendVals (restrictTo (hmsgNeed pol T msg i) v)) =
      slotBlk pub.seed (.hmsg R msg i) (valsOf v) := by
  funext j
  unfold slotBlk
  rw [slotInput_congr pub.seed (g := valsOf v) fun p hp ↦ by
    simp only [slotNeed, Finset.mem_singleton] at hp
    subst hp
    exact extendVals_restrictTo (by simp [hmsgNeed]) v]

/-- **The ports of an `H_msg` call**, in order. -/
theorem hb_hmsgPorts (B : QReg) (pol : DigestPolicy) (T : Finset HPos) (msg : Message)
    (i : DigestCall)
    (hmsg : ∀ R y, BatchOk pub ok (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) (cor256 y) 1)
    (C : Set (HwProg X Z)) : HB ok v (progPorts M B (hmsgPorts pub pol T msg i)) C ∅ := by
  refine hb_pathPorts ok v pub B _ _ _ _ ?_ C
  rw [slotBlk_hmsg_restrictTo]
  exact hmsg _ _

/-- **The ports of both `H_msg` calls.** -/
theorem hb_digestPorts (B : QReg) (pol : DigestPolicy) (T : Finset HPos) (msg : Message)
    (hmsg : ∀ R msg i y, BatchOk pub ok (slotBlk pub.seed (.hmsg R msg i) (valsOf v))
      (cor256 y) 1)
    (C : Set (HwProg X Z)) : HB ok v (progPorts M B (digestPorts pub pol T msg)) C ∅ := by
  rw [digestPorts, progPorts_append]
  exact hb₂_bind ok v _ _ (hb_hmsgPorts ok v pub B pol T msg 0 (fun R y ↦ hmsg R msg 0 y) C)
    fun _ ↦ hb_hmsgPorts ok v pub B pol T msg 1 (fun R y ↦ hmsg R msg 1 y) ∅

theorem hb_progSlots (B : QReg) (ss : List Slot)
    (h : ∀ s ∈ ss, ∀ C, HB ok v (progPorts M B (slotPorts pub s)) C ∅)
    (C : Set (HwProg X Z)) : HB ok v (progSlots M pub B ss) C ∅ := by
  induction ss generalizing C with
  | nil => exact Set.empty_subset C
  | cons s ss ih =>
    exact hb₂_bind ok v _ _ (h s List.mem_cons_self C) fun _ ↦
      ih (fun s' hs' ↦ h s' (List.mem_cons_of_mem _ hs')) ∅

variable
  (hslot : ∀ s, InTable s → BatchOk pub ok (slotBlk pub.seed s (valsOf v))
    (cor128 (valsOf v (slotOutPos s))) (nBlk pub.seed s))
  (hmsg : ∀ R msg i y, BatchOk pub ok (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) (cor256 y) 1)

include hslot in
/-- **A FORS opening's ports**, slot by slot. -/
theorem hb_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (C : Set (HwProg X Z)) : HB ok v (forsOpenT M pub B idx lv) C ∅ :=
  hb_revealThen ok v _ _ fun _ ↦ hb₂_bind ok v _ _ (hb_progSlots ok v pub B _
    (fun _ hs C ↦ hb_slotPorts ok v pub B (inTable_of_mem_forsSlots hs)
      (hslot _ (inTable_of_mem_forsSlots hs)) C) C) fun _ ↦ subset_rfl

variable (upd : TrialUpd M)

include hslot in
/-- **A layer signature's ports by an in-table key**: the counter search reads, then the slots it
makes public are programmed slot by slot. -/
theorem hb_signLayerT (B : QReg) (K : Key)
    (hK : KeyIn K)
    (C : Set (HwProg X Z)) : HB ok v (signLayerT M upd pub B K) C ∅ := by
  refine hb_revealThen ok v _ _ fun _ ↦ hb₂_bind ok v _ _ (hb_readLift ok v _ C) fun g ↦ ?_
  rcases g with _ | ⟨cnt, x⟩
  · exact Set.empty_subset _
  · exact hb_revealThen ok v _ _ fun _ ↦ hb₂_bind ok v _ _ (hb_progSlots ok v pub B _
      (fun _ hs C ↦ hb_slotPorts ok v pub B (inTable_of_mem_layerSlots hK hs)
        (hslot _ (inTable_of_mem_layerSlots hK hs)) C) C) fun _ ↦ subset_rfl

include hslot hmsg in
/-- **A signature's ports**, for every digest policy. -/
theorem hb_signT (pol : DigestPolicy) (B : QReg) (msg : Message) (C : Set (HwProg X Z)) :
    HB ok v (signT M upd pol pub B msg) C ∅ := by
  refine hb_revealThen ok v _ _ fun r₁ ↦ hb_revealThen ok v _ _ fun r₂ ↦ ?_
  refine hb₂_bind ok v _ _ (hb_digestPorts ok v pub B pol _ msg hmsg C) fun _ ↦ ?_
  refine hb₂_bind ok v _ _ (hb_forsOpenT ok v pub hslot B _ _ ∅) fun _ ↦ ?_
  refine hb₂_bind ok v _ _ (hb_signLayerT ok v pub hslot upd B _ (keyIn_keyOf _ _) ∅)
    fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · exact subset_rfl
  · refine hb₂_bind ok v _ _ (hb_signLayerT ok v pub hslot upd B _ (keyIn_keyOf _ _) ∅)
      fun s₁ ↦ ?_
    rcases s₁ with _ | middle
    · exact subset_rfl
    · refine hb₂_bind ok v _ _ (hb_signLayerT ok v pub hslot upd B _ (keyIn_keyOf _ _) ∅)
        fun s₂ ↦ ?_
      rcases s₂ with _ | top <;> exact subset_rfl

include hslot hmsg in
theorem hb_challengeT (pol : DigestPolicy) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    HB ok v (challengeT M upd pol pub A c) ∅ ∅ := by
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact hb_readLift ok v _ ∅
  · exact hb_readLift ok v _ ∅
  · exact hb_bind ok v _ _ (hb₂_bind ok v _ _ (hb_act ok v _ _) fun _ ↦
      hb_signT ok v pub hslot hmsg upd pol _ msg ∅) fun _ _ ↦ subset_rfl

include hslot hmsg in
/-- **The game's program ports satisfy `ok` in batch order.** -/
theorem hb_gameT (pol : DigestPolicy) (A : SAdversary) :
    HB ok v (gameT M upd pol pub A) ∅ ∅ :=
  hb_revealThen ok v _ _ fun _ ↦
    hb₂_bind ok v _ _ (hb_substitute ok v _ (hb_challengeT ok v pub hslot hmsg upd pol) _)
      fun _ ↦ hb₂_bind ok v _ _ (hb_readLift ok v _ ∅) fun _ ↦ subset_rfl

end hb

/-! ## The presented operators at the program calls -/

section present

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- **The program calls are presented states satisfying `ok`**; the other calls, anything. -/
def progSupp (m₀ : Finset HPos × M) (ok : HwProg X Z → HwReg X Z (Finset HPos × M) → Prop) :
    ∀ (i : (recHwSpec X Z HPos M).Port) (E : QReg),
      Matrix (((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D) × E)
        (((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D) × E) ℂ → Prop
  | .inl (.inr c), _, σ => ∀ a, ¬ok c a.1.2 → σ a a = 0
  | .inl (.inl _), _, _ => True
  | .inr _, _, _ => True

theorem stepHeld_sponge (m₀ : Finset HPos × M) (i : SpongePort) (C : Set (HwProg X Z)) :
    StepR m₀ (.inl (.inl (.inl i))) (fun s ↦ AllHeld C s.2.1) (fun s ↦ AllHeld C s.2.1) :=
  stepR_sponge m₀ i fun _ _ he hr ↦ (congrArg (fun t ↦ AllHeld C t.1) he).mpr hr

theorem stepHeld_read (m₀ : Finset HPos × M)
    (c : {c : HwRead X Z (Finset HPos × M) // ReadMono (memLab X Z HPos M) c})
    (C : Set (HwProg X Z)) :
    StepR m₀ (.inl (.inl (.inr c.1))) (fun s ↦ AllHeld C s.2.1) (fun s ↦ AllHeld C s.2.1) :=
  stepR_read m₀ c fun _ _ he hr ↦ (congrArg (AllHeld C) he).mpr hr

theorem stepHeld_prog (m₀ : Finset HPos × M) (c : HwProg X Z) (C : Set (HwProg X Z)) :
    StepR m₀ (.inl (.inr c)) (fun s ↦ AllHeld C s.2.1)
      (fun s ↦ AllHeld (heldNext c C) s.2.1) :=
  stepR_prog m₀ c fun _ _ h hr ↦
    (congrArg (fun t ↦ AllHeld (heldNext c C) t.1) h).mpr (allHeld_progUpdate hr c)

theorem stepHeld_rec (m₀ : Finset HPos × M) (T : Finset HPos) (C : Set (HwProg X Z)) :
    StepR m₀ (.inr T) (fun s ↦ AllHeld C s.2.1) (fun s ↦ AllHeld C s.2.1) :=
  stepR_rec m₀ T fun _ _ h hr ↦ (congrArg (fun t ↦ AllHeld C t.1) h).mpr hr

/-- A program port satisfying `ok` given the held cells `C` is presented only states satisfying
`ok` by an operator supported on the states holding `C`. -/
theorem progSupp_prog (m₀ : Finset HPos × M)
    (ok : HwProg X Z → HwReg X Z (Finset HPos × M) → Prop) {C : Set (HwProg X Z)}
    {c : HwProg X Z} (hc : OkC ok C c) {A : QReg} (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z HPos M).In (.inl (.inr c)) × E)
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | AllHeld C s.2.1} ρ) :
    progSupp m₀ ok (.inl (.inr c)) E
      ((SubInstrument.relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).branch () ρ) :=
  fun a ha ↦ relabel_diag_eq_zero_of_supp m₀ E ℓ hρ a fun h ↦ ha (hc _ h)

/-- One call of a realized program, from the held cells `C` to `C'`. -/
theorem forallQueries_queryBind_of_stepHeld (m₀ : Finset HPos × M) (I : L.Interp)
    (ok : HwProg X Z → HwReg X Z (Finset HPos × M) → Prop) {A : QReg}
    (i : (recHwSpec X Z HPos M).Port) (E : QReg) (ℓ : A ≃ (recHwSpec X Z HPos M).In i × E)
    (k' : (recHwSpec X Z HPos M).Result i → QuantumComp L (recHwSpec X Z HPos M) Ω
      (QReg.of ((recHwSpec X Z HPos M).Out i × E)))
    {C C' : Set (HwProg X Z)}
    (hpre : ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | AllHeld C s.2.1} ρ →
        progSupp m₀ ok i E
          ((SubInstrument.relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).branch () ρ))
    (hstep : StepR m₀ i (fun s ↦ AllHeld C s.2.1) (fun s ↦ AllHeld C' s.2.1))
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of ((recHwSpec X Z HPos M).Out i × E) ×
        (runtimeR m₀).D ↦ m.2) {s | AllHeld C' s.2.1} ρ' →
      (runtimeR m₀).ForallQueries I (progSupp m₀ ok) (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | AllHeld C s.2.1} ρ) :
    (runtimeR m₀).ForallQueries I (progSupp m₀ ok) (QuantumComp.queryBind i E ℓ k') ρ :=
  forallQueries_queryBind_of_stepR (Sup := progSupp m₀ ok) (P := fun s ↦ AllHeld C s.2.1)
    (P' := fun s ↦ AllHeld C' s.2.1) m₀ I i E ℓ k' hpre hstep hk ρ hρ

/-- **The realized program of a template whose program ports satisfy `ok` in batch order presents
only states satisfying `ok` at its program calls.** -/
theorem forallQueries_of_hb (m₀ : Finset HPos × M) (I : L.Interp)
    (ok : HwProg X Z → HwReg X Z (Finset HPos × M) → Prop) (v : (s : HPos) → XD s) {A : QReg}
    (y : QuantumComp L (SSpec M) Ω A) :
    ∀ C C', HB ok v y C C' → ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | AllHeld C s.2.1} ρ →
      (runtimeR m₀).ForallQueries I (progSupp m₀ ok) (realizeT v y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro C C' hy ρ hρ b
    exact ih b C C' (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro C C' hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_of_stepHeld m₀ I ok (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT v (k r)) (fun _ _ ↦ trivial) (stepHeld_sponge m₀ i C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepHeld m₀ I ok (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT v (k r)) (fun _ _ ↦ trivial) (stepHeld_read m₀ c C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_stepHeld m₀ I ok
          (.inl (.inr ((LazyProg.programH T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (progSupp_prog m₀ ok hy.1 E ℓ) (stepHeld_prog m₀ _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_stepHeld m₀ I ok
          (.inl (.inr ((LazyProg.programK T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (progSupp_prog m₀ ok hy.1 E ℓ) (stepHeld_prog m₀ _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_stepHeld m₀ I ok
          (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (progSupp_prog m₀ ok hy.1 E ℓ) (stepHeld_prog m₀ _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepHeld m₀ I ok (.inr T) E ℓ
        (fun m ↦ realizeT v (k (restrictTo T v, m))) (fun _ _ ↦ trivial) (stepHeld_rec m₀ T C)
        (fun m ↦ ih (restrictTo T v, m) _ C' (hy.2 (ULift.up (restrictTo T v, m)))) ρ hρ

/-- **`RoundHeld` of the earlier rounds at a round's port** (the run fact of the event's
exemptions): for any condition `ok` on program calls holding at the ports of every in-table
structural slot's path and every `H_msg` call's block once the earlier rounds of its batch are held
(`BatchOk`), every program call of the realized game, from any state, is presented only states
satisfying `ok`, for every digest policy, public datum and hidden values. -/
theorem forallQueries_progSupp_gameT (ok : HwProg X Z → HwReg X Z (Finset HPos × M) → Prop)
    (upd : TrialUpd M) (pol : DigestPolicy) (pub : Pub) (v : (s : HPos) → XD s)
    (A : SAdversary) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D)
      (QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ)
    (hslot : ∀ s, InTable s → BatchOk pub ok (slotBlk pub.seed s (valsOf v))
      (cor128 (valsOf v (slotOutPos s))) (nBlk pub.seed s))
    (hmsg : ∀ R msg i y, BatchOk pub ok (slotBlk pub.seed (.hmsg R msg i) (valsOf v))
      (cor256 y) 1) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments (progSupp m₀ ok)
      (realizeT v (gameT M upd pol pub A)) ρ :=
  forallQueries_of_hb m₀ _ ok v _ ∅ ∅ (hb_gameT ok v pub hslot hmsg upd pol A) ρ fun _ _ _ ↦
    ⟨fun c hc ↦ absurd hc (Set.notMem_empty c), fun c hc ↦ absurd hc (Set.notMem_empty c)⟩

end present

end Quantum.Sphincs.Assembly

end
