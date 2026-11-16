module

public import Quantum.Xmss.Assembly.Masses
public import Quantum.Xmss.Assembly.Costs

@[expose] public section

/-!
# The calls of the realized template game

Masses' hypotheses `hinv` and `hN` for `realizeT v (gameT M upd pub A)`, over a general public
datum `pub` (nothing depends on how `pubP` is built).

* **The invariant** (`SlotInv`): at a call, every in-table slot with a disclosed input
  (`IsInput`, a payload position in the memory label) has the `k`, `k'`, `h` cells of every round
  of its honest path at `(pub, v)` hardwired.
* **Combinatorics** (`mem_layerSlots_of_isInput`, `not_isInput_rootPos`): a slot with an input in
  `layerNeed l e x` is one of `layerSlots l e x`; the root is no slot's input.
* **Pending ports** (`InvP`, `HP`): between a reveal and the end of its program calls the slots it
  discloses are pending; `HP pub v y C C'` says that the template `y` calls its sponge, read and
  reveal ports with nothing pending (its reads keeping the label), a program call leaves the
  pending set and a reveal of `T` adds the ports of the slots with an input in `T` (`revealSet`).
  Per component: `hp_readLift` (runtime 1's programs: the simulated adversary calls, the
  randomizer search, the verification), `hp_signLayerT`, `hp_signT`, `hp_challengeT`, composed in
  `hp_gameT`. `forallQueries_of_hp` turns `HP` into `ForallQueries` of `invSupp` for the realized
  program and any ports `Q` other than the program ports (`hinv_gameT`, Masses' shape with
  `Inv p v := SlotInv M (pubP p) v`, from states with an empty memory label,
  `querySupportedOn_init`).
* **The read mass** (`readMass_eq_portMass`): the hidden sets are empty at the program and record
  ports, so `readMass` is `portMass` of the read and record ports (`readRecPort`); `hinv` holds
  there, not at the program ports (where `readMass`'s `Q = extCls` would ask it).
* **Charges by kind** (`tCharge`, `rCharge`: `a` per sponge call, `b` per read, `c` per program
  call, `d` per reveal or record): per component `isChargeBound_simulate` (`6a` per permutation
  call), `chg_readsProgram` (`3b` per block), `chg_grindR`, `chg_signLayerT` (`layerCalls`),
  `chg_signT`, `chg_challengeT`, composed in `chg_gameT_of_signT` and `chg_realizeT_gameT`
  (`gameCalls a b c d q`). `hN_sponge` (`6q`), `hN_cls` and `hN_readRec` (Security's `clsCap`,
  `gameCalls_cls_le`), `hN_prog` (`progCap`).
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker

universe u v w w₁

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## The invariant -/

section inv

/-- `q` is a payload position of the structural slot `s` (its output position is not an input). -/
def IsInput (q : ValPos) : Slot → Prop
  | .chain l e step i => q = cpos l e i step.val
  | .leaf l e => ∃ i : ChainIndex, q = cpos l e i (chainLength - 1)
  | .node l level index =>
      q = tpos l (level - 1) (2 * index) ∨ q = tpos l (level - 1) (2 * index + 1)
  | _ => False

variable (M : Type) in
/-- **The invariant at the sponge and read calls**: an in-table slot (`InTable`) with a disclosed
input has all its cells at `(pub, v)` hardwired. -/
def SlotInv (pub : Pub) (v : ValPos → Digest) (r : HwReg X Z (Finset ValPos × M)) : Prop :=
  ∀ s, InTable s → ∀ q, IsInput q s → q ∈ r.2.2.1 → ∀ j < nBlocks pub s,
    r.2.1.2.1 (roundK pub s v j).1 ≠ none ∧ r.2.1.2.2 (roundK' pub s v j).1 ≠ none ∧
      r.2.1.1 (roundH pub s v j).1 ≠ none

end inv

/-! ## The slots a layer signature discloses -/

section slots

theorem chain_mem_layerSlots {l : Layer} {e : KeyIndex} {x : Encoding} {i : ChainIndex}
    {step : ChainStep} (h : (x i).val ≤ step.val) : Slot.chain l e step i ∈ layerSlots l e x :=
  List.mem_append_left _ (List.mem_flatMap.2 ⟨i, List.mem_finRange _, List.mem_map.2
    ⟨step, List.mem_filter.2 ⟨List.mem_finRange _, by simpa using h⟩, rfl⟩⟩)

theorem leaf_mem_layerSlots (l : Layer) (e : KeyIndex) (x : Encoding) :
    Slot.leaf l e ∈ layerSlots l e x :=
  List.mem_append_right _ List.mem_cons_self

theorem node_mem_layerSlots {l : Layer} {e : KeyIndex} (x : Encoding) {lev : ℕ}
    (h : lev < layerHeight) :
    Slot.node l (lev + 1) (e.val / 2 ^ (lev + 1)) ∈ layerSlots l e x :=
  List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨lev, List.mem_range.2 h, rfl⟩))

/-- The slots of a layer signature: the chain steps from the opened positions, the leaf, the
nodes on the path. -/
theorem mem_layerSlots_cases {l : Layer} {e : KeyIndex} {x : Encoding} {s : Slot}
    (h : s ∈ layerSlots l e x) :
    (∃ (i : ChainIndex) (step : ChainStep), (x i).val ≤ step.val ∧ s = .chain l e step i) ∨
      s = .leaf l e ∨ ∃ lev < layerHeight, s = .node l (lev + 1) (e.val / 2 ^ (lev + 1)) := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨i, -, h⟩ := List.mem_flatMap.1 h
    obtain ⟨step, hs, rfl⟩ := List.mem_map.1 h
    exact Or.inl ⟨i, step, by simpa using (List.mem_filter.1 hs).2, rfl⟩
  · rcases List.mem_cons.1 h with rfl | h
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨lev, hl, rfl⟩ := List.mem_map.1 h
      exact Or.inr (Or.inr ⟨lev, List.mem_range.1 hl, rfl⟩)

theorem mem_needUnion {q : ValPos} {ss : List Slot} (h : q ∈ needUnion ss) :
    ∃ s ∈ ss, q ∈ slotNeed s := by
  induction ss with
  | nil => exact absurd h (Finset.notMem_empty q)
  | cons s ss ih =>
    rcases Finset.mem_union.1 h with h | h
    · exact ⟨s, List.mem_cons_self, h⟩
    · obtain ⟨s', hs', hq⟩ := ih h
      exact ⟨s', List.mem_cons_of_mem _ hs', hq⟩

theorem keyIndex_lt_two_pow (e : KeyIndex) : e.val < 2 ^ 32 := by
  have := e.isLt
  simpa [lifetime, layerCount, layerHeight] using this

theorem div_two_pow_succ (e lev : ℕ) : e / 2 ^ (lev + 1) = e / 2 ^ lev / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

theorem div_two_pow_le (e lev : ℕ) : e / 2 ^ lev ≤ e :=
  Nat.div_le_self _ _

/-- **The positions a layer signature reveals**: chain positions of its key from the opened
positions on, and tree positions whose parent is on its key's path (or the path's top). -/
theorem mem_layerNeed {l : Layer} {e : KeyIndex} {x : Encoding} {q : ValPos}
    (h : q ∈ layerNeed l e x) :
    (∃ (i : ChainIndex) (j : ℕ), j < chainLength ∧ (x i).val ≤ j ∧ q = cpos l e i j) ∨
      ∃ lev a, q = tpos l lev a ∧ lev ≤ layerHeight ∧ a < 2 ^ 32 ∧
        (lev < layerHeight → a / 2 = e.val / 2 ^ (lev + 1)) := by
  have he := keyIndex_lt_two_pow e
  have hH : layerHeight = 16 := rfl
  have hC : chainLength = 4 := rfl
  simp only [layerNeed, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
  rcases h with (h | ⟨i, rfl⟩) | ⟨lev, rfl⟩
  · obtain ⟨s, hs, hq⟩ := mem_needUnion h
    rcases mem_layerSlots_cases hs with ⟨i, step, hle, rfl⟩ | rfl | ⟨lev, hlev, rfl⟩
    · have := step.isLt
      simp only [slotNeed, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Or.inl ⟨i, step.val, by omega, hle, rfl⟩
      · exact Or.inl ⟨i, step.val + 1, by omega, by omega, rfl⟩
    · simp only [slotNeed, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hq
      rcases hq with rfl | ⟨i, rfl⟩
      · exact Or.inr ⟨0, e.val, rfl, by omega, he, fun _ ↦ by simp⟩
      · exact Or.inl ⟨i, chainLength - 1, by omega, by have := (x i).isLt; omega, rfl⟩
    · have h2 : 2 * (e.val / 2 ^ (lev + 1)) ≤ e.val := by
        rw [div_two_pow_succ]
        have := div_two_pow_le e.val lev
        omega
      have h2' := div_two_pow_le e.val (lev + 1)
      simp only [slotNeed, Nat.add_sub_cancel, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact Or.inr ⟨lev, _, rfl, by omega, by omega, fun _ ↦ by omega⟩
      · exact Or.inr ⟨lev, _, rfl, by omega, by omega, fun _ ↦ by omega⟩
      · refine Or.inr ⟨lev + 1, _, rfl, by omega, by omega, fun _ ↦ ?_⟩
        rw [div_two_pow_succ e.val (lev + 1)]
  · exact Or.inl ⟨i, (x i).val, (x i).isLt, le_rfl, rfl⟩
  · have h2 := div_two_pow_le e.val lev.val
    have hx := xor_one_div_two (e.val / 2 ^ lev.val)
    refine Or.inr ⟨lev.val, _, rfl, by omega, by omega, fun _ ↦ ?_⟩
    rw [hx, div_two_pow_succ]

/-- An input position of an in-table node lies at a level below `layerHeight`, with an index whose
half is the node's index. -/
theorem isInput_node {q : ValPos} {l : Layer} {level index : ℕ}
    (hs : InTable (.node l level index)) (hq : IsInput q (.node l level index)) :
    ∃ a, q = tpos l (level - 1) a ∧ a / 2 = index ∧ a < 2 ^ 32 ∧ 1 ≤ level ∧
      level ≤ layerHeight := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hk : 2 ^ (keyBits l - level) ≤ 2 ^ 31 :=
    Nat.pow_le_pow_right (by norm_num) (by have := keyBits_le l; omega)
  rcases hq with rfl | rfl
  · exact ⟨_, rfl, by omega, by omega, h1, h2⟩
  · exact ⟨_, rfl, by omega, by omega, h1, h2⟩

/-- **A slot with an input revealed by a layer signature is one of the signature's slots.** -/
theorem mem_layerSlots_of_isInput {l : Layer} {e : KeyIndex} {x : Encoding} {s : Slot}
    (hs : InTable s) {q : ValPos} (hq : IsInput q s) (hn : q ∈ layerNeed l e x) :
    s ∈ layerSlots l e x := by
  have hH : layerHeight = 16 := rfl
  have hC : chainLength = 4 := rfl
  cases s with
  | chain l' e' step i =>
    subst hq
    rcases mem_layerNeed hn with ⟨i₀, j, hj, hxj, h⟩ | ⟨lev, a, h, -⟩
    · simp only [cpos, ValPos.chain.injEq, Fin.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, hm⟩ := h
      have := step.isLt
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
      exact chain_mem_layerSlots (by omega)
    · simp [cpos, tpos] at h
  | leaf l' e' =>
    obtain ⟨i, rfl⟩ := hq
    rcases mem_layerNeed hn with ⟨i₀, j, -, -, h⟩ | ⟨lev, a, h, -⟩
    · simp only [cpos, ValPos.chain.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact leaf_mem_layerSlots _ _ _
    · simp [cpos, tpos] at h
  | node l' level index =>
    obtain ⟨a', rfl, ha', ha'32, h1, h2⟩ := isInput_node hs hq
    rcases mem_layerNeed hn with ⟨i₀, j, -, -, h⟩ | ⟨lev, a, h, hlev, ha, hdiv⟩
    · simp [cpos, tpos] at h
    · simp only [tpos, ValPos.tree.injEq, Fin.mk.injEq] at h
      obtain ⟨rfl, hl, hi⟩ := h
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hl
      rw [Nat.mod_eq_of_lt ha'32, Nat.mod_eq_of_lt ha] at hi
      subst hl hi
      have hd := hdiv (by omega)
      rw [show level = level - 1 + 1 by omega, show index = e.val / 2 ^ (level - 1 + 1) by omega]
      exact node_mem_layerSlots x (by omega)
  | msg => exact hs.elim
  | prf => exact hs.elim
  | rnd => exact hs.elim
  | param => exact hs.elim
  | seed => exact hs.elim

/-- The public key's root is no slot's input. -/
theorem not_isInput_rootPos {s : Slot} (hs : InTable s) : ¬IsInput rootPos s := by
  have hH : layerHeight = 16 := rfl
  intro hq
  cases s with
  | chain => simp [IsInput, rootPos, cpos, tpos] at hq
  | leaf => simp [IsInput, rootPos, cpos, tpos] at hq
  | node l level index =>
    obtain ⟨a, h, -, -, h1, h2⟩ := isInput_node hs hq
    simp only [rootPos, tpos, ValPos.tree.injEq, Fin.mk.injEq] at h
    have h3 := h.2.1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
    omega
  | msg => exact hs.elim
  | prf => exact hs.elim
  | rnd => exact hs.elim
  | param => exact hs.elim
  | seed => exact hs.elim

end slots

/-! ## The invariant with pending program ports -/

section pending

variable {M : Type}

/-- **The invariant with pending program ports `C`**: an in-table slot with a disclosed input has
each of its realized program ports hardwired or pending. -/
def InvP (pub : Pub) (v : ValPos → Digest) (C : Set (HwProg X Z))
    (r : HwReg X Z (Finset ValPos × M)) : Prop :=
  ∀ s, InTable s → ∀ q, IsInput q s → q ∈ r.2.2.1 → ∀ p ∈ slotPorts pub s,
    CellHardwired (p.realize v) r.2.1 ∨ p.realize v ∈ C

/-- The realized program ports of the in-table slots with an input in `T`. -/
def revealSet (pub : Pub) (v : ValPos → Digest) (T : Finset ValPos) : Set (HwProg X Z) :=
  {c | ∃ s, InTable s ∧ (∃ q, IsInput q s ∧ q ∈ T) ∧ ∃ p ∈ slotPorts pub s, p.realize v = c}

/-- The realized program ports of the slots `ss`. -/
def portsOf (pub : Pub) (v : ValPos → Digest) (ss : List Slot) : Set (HwProg X Z) :=
  {c | ∃ s ∈ ss, ∃ p ∈ slotPorts pub s, p.realize v = c}

theorem revealSet_layerNeed_subset (pub : Pub) (v : ValPos → Digest) (l : Layer) (e : KeyIndex)
    (x : Encoding) : revealSet pub v (layerNeed l e x) ⊆ portsOf pub v (layerSlots l e x) := by
  rintro c ⟨s, hs, ⟨q, hq, hn⟩, hp⟩
  exact ⟨s, mem_layerSlots_of_isInput hs hq hn, hp⟩

theorem revealSet_rootPos (pub : Pub) (v : ValPos → Digest) :
    revealSet pub v {rootPos} ⊆ ∅ := by
  rintro c ⟨s, hs, ⟨q, hq, hn⟩, -⟩
  rw [Finset.mem_singleton] at hn
  subst hn
  exact not_isInput_rootPos hs hq

theorem invP_mono {pub : Pub} {v : ValPos → Digest} {C C' : Set (HwProg X Z)} (h : C ⊆ C')
    {r : HwReg X Z (Finset ValPos × M)} (hr : InvP pub v C r) : InvP pub v C' r :=
  fun s hs q hq hl p hp ↦ (hr s hs q hq hl p hp).imp_right fun hc ↦ h hc

theorem invP_of_eq {pub : Pub} {v : ValPos → Digest} {C : Set (HwProg X Z)}
    {r r' : HwReg X Z (Finset ValPos × M)} (h1 : r'.2.1 = r.2.1) (h2 : r'.2.2.1 = r.2.2.1)
    (hr : InvP pub v C r) : InvP pub v C r' := by
  intro s hs q hq hl p hp
  rw [h1]
  exact hr s hs q hq (h2 ▸ hl) p hp

theorem invP_of_label_empty {pub : Pub} {v : ValPos → Digest} {C : Set (HwProg X Z)}
    {r : HwReg X Z (Finset ValPos × M)} (h : r.2.2.1 = ∅) : InvP pub v C r := by
  intro s _ q _ hl
  rw [h] at hl
  exact absurd hl (Finset.notMem_empty q)

theorem update_some_ne_none {α β : Type*} [DecidableEq α] (f : α → Option β) (a : α) (b : β) :
    Function.update f a (some b) a ≠ none := by
  rw [Function.update_self]
  exact Option.some_ne_none b

theorem update_some_ne_none_of {α β : Type*} [DecidableEq α] {f : α → Option β} (a : α)
    {a' : α} (b : β) (h : f a' ≠ none) : Function.update f a (some b) a' ≠ none := by
  by_cases ha : a' = a
  · subst ha
    exact update_some_ne_none f a' b
  · rw [Function.update_of_ne ha]
    exact h

theorem cellHardwired_progUpdate_self {X₁ Z₁ : Type} [DecidableEq X₁] [DecidableEq Z₁]
    (c : HwProg X₁ Z₁) (W : Hw X₁ Z₁) :
    CellHardwired c (progUpdate c W) := by
  cases c with
  | programH z a => exact update_some_ne_none W.1 z a
  | programK y a => exact update_some_ne_none W.2.1 y a
  | programK' y a => exact update_some_ne_none W.2.2 y a

theorem cellHardwired_progUpdate {X₁ Z₁ : Type} [DecidableEq X₁] [DecidableEq Z₁]
    {c c' : HwProg X₁ Z₁} {W : Hw X₁ Z₁} (h : CellHardwired c' W) :
    CellHardwired c' (progUpdate c W) := by
  cases c with
  | programH z a =>
    cases c' with
    | programH z' a' => exact update_some_ne_none_of z a h
    | programK => exact h
    | programK' => exact h
  | programK y a =>
    cases c' with
    | programH => exact h
    | programK y' a' => exact update_some_ne_none_of y a h
    | programK' => exact h
  | programK' y a =>
    cases c' with
    | programH => exact h
    | programK => exact h
    | programK' y' a' => exact update_some_ne_none_of y a h

/-- A program port hardwires its cell and keeps the others: it leaves the pending set. -/
theorem invP_prog {pub : Pub} {v : ValPos → Digest} {C : Set (HwProg X Z)} (c : HwProg X Z)
    {r r' : HwReg X Z (Finset ValPos × M)} (h : r'.2 = (progUpdate c r.2.1, r.2.2))
    (hr : InvP pub v C r) : InvP pub v (C \ {c}) r' := by
  intro s hs q hq hl p hp
  rw [h] at hl ⊢
  rcases hr s hs q hq hl p hp with hc | hc
  · exact Or.inl (cellHardwired_progUpdate hc)
  · by_cases he : p.realize v = c
    · rw [he]
      exact Or.inl (cellHardwired_progUpdate_self c _)
    · exact Or.inr ⟨hc, he⟩

/-- A reveal of `T` adds the ports of the slots with an input in `T` to the pending set. -/
theorem invP_reveal {pub : Pub} {v : ValPos → Digest} {C : Set (HwProg X Z)} (T : Finset ValPos)
    {r r' : HwReg X Z (Finset ValPos × M)} (h : r'.2 = (r.2.1, (r.2.2.1 ∪ T, r.2.2.2)))
    (hr : InvP pub v C r) : InvP pub v (C ∪ revealSet pub v T) r' := by
  intro s hs q hq hl p hp
  rw [h] at hl ⊢
  rcases Finset.mem_union.1 hl with hl | hl
  · exact (hr s hs q hq hl p hp).imp_right Or.inl
  · exact Or.inr (Or.inr ⟨s, hs, ⟨q, hq, hl⟩, p, hp, rfl⟩)

/-- The honest round cells depend on the values only at the slot's coordinates. -/
theorem slotInput_eq_of_need (pub : Pub) {s : Slot} {f g : ValPos → Digest}
    (h : ∀ q ∈ slotNeed s, f q = g q) : slotInput pub s f = slotInput pub s g := by
  unfold slotInput
  refine congrArg (thInput pub.param (slotFields s)) ?_
  cases s with
  | chain l e step i =>
    simp only [slotPayload]
    rw [h _ (by simp [slotNeed])]
  | leaf l e =>
    simp only [slotPayload]
    refine congrArg digestsPayload (funext fun i ↦ h _ ?_)
    simp [slotNeed]
  | node l level index =>
    simp only [slotPayload]
    rw [h _ (by simp [slotNeed]), h _ (by simp [slotNeed])]
  | msg => rfl
  | prf => rfl
  | rnd => rfl
  | param => rfl
  | seed => rfl

theorem slotOutPos_mem_slotNeed {s : Slot} (hs : InTable s) : slotOutPos s ∈ slotNeed s := by
  cases s with
  | chain => simp [slotNeed, slotOutPos]
  | leaf => simp [slotNeed, slotOutPos]
  | node => simp [slotNeed, slotOutPos]
  | msg => exact hs.elim
  | prf => exact hs.elim
  | rnd => exact hs.elim
  | param => exact hs.elim
  | seed => exact hs.elim

theorem extendVals_restrictTo_of_mem {T : Finset ValPos} {p : ValPos} (h : p ∈ T)
    (v : ValPos → Digest) : extendVals (restrictTo T v) p = v p := by
  rw [extendVals, dite_eq_left h]
  rfl

/-- **No pending port is the invariant**: the realized program ports are the honest round cells. -/
theorem slotInv_of_invP {pub : Pub} {v : ValPos → Digest} {r : HwReg X Z (Finset ValPos × M)}
    (h : InvP pub v ∅ r) : SlotInv M pub v r := by
  intro s hs q hq hl j hj
  have hv : ∀ q ∈ slotNeed s, extendVals (restrictTo (slotNeed s) v) q = v q :=
    fun q hq ↦ extendVals_restrictTo_of_mem hq v
  have hin : ∀ c ∈ slotPorts pub s, CellHardwired (c.realize v) r.2.1 := fun c hc ↦
    (h s hs q hq hl c hc).resolve_right (Set.notMem_empty _)
  have hmem : ∀ p ∈ [LazyProg.programK (slotNeed s) fun w ↦ roundK pub s (extendVals w) j,
      .programK' (slotNeed s) fun w ↦ roundK' pub s (extendVals w) j,
      .programH (slotNeed s) fun w ↦ roundH pub s (extendVals w) j], p ∈ slotPorts pub s :=
    fun p hp ↦ List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, hp⟩
  have hK := hin (.programK (slotNeed s) fun w ↦ roundK pub s (extendVals w) j)
    (hmem _ (by simp))
  have hK' := hin (.programK' (slotNeed s) fun w ↦ roundK' pub s (extendVals w) j)
    (hmem _ (by simp))
  have hH := hin (.programH (slotNeed s) fun w ↦ roundH pub s (extendVals w) j)
    (hmem _ (by simp))
  simp only [LazyProg.realize, CellHardwired] at hK hK' hH
  have e1 : roundK pub s (extendVals (restrictTo (slotNeed s) v)) j = roundK pub s v j := by
    simp only [roundK, slotInput_eq_of_need pub hv]
  have e2 : roundK' pub s (extendVals (restrictTo (slotNeed s) v)) j = roundK' pub s v j := by
    simp only [roundK', slotInput_eq_of_need pub hv]
  have e3 : roundH pub s (extendVals (restrictTo (slotNeed s) v)) j = roundH pub s v j := by
    simp only [roundH, slotInput_eq_of_need pub hv, hv _ (slotOutPos_mem_slotNeed hs)]
  rw [e1] at hK
  rw [e2] at hK'
  rw [e3] at hH
  exact ⟨hK, hK', hH⟩

end pending

/-! ## The steps of `runtimeR` on the pending invariant -/

section steps

variable {M : Type} [Fintype M] [DecidableEq M]

/-- A read port whose memory update keeps the memory label (Template's `liftRead`). -/
def LabKeep : HwRead X Z (Finset ValPos × M) → Prop
  | .readH _ u => ∀ m o, (u m o).1 = m.1
  | .readK _ u => ∀ m o, (u m o).1 = m.1
  | .readK' _ u => ∀ m o, (u m o).1 = m.1

omit [Fintype M] [DecidableEq M] in
theorem labKeep_liftRead (c : HwRead X Z M) : LabKeep (liftRead (S := ValPos) c) := by
  cases c <;> intro _ _ <;> rfl

omit [Fintype M] in
/-- A read port keeping the label keeps the hardwired cells and the label. -/
theorem hwReadKraus_ne_zero_keep {c : HwRead X Z (Finset ValPos × M)} (hc : LabKeep c)
    (r : c.Result) {u u' : Unit} {s s' : HwReg X Z (Finset ValPos × M)}
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

/-- A step of `runtimeR` at port `i` carries support on the pending invariant `C` to support on
the pending invariant `C'`. -/
def StepInv (m₀ : Finset ValPos × M) (pub : Pub) (v : ValPos → Digest)
    (i : (recHwSpec X Z ValPos M).Port) (C C' : Set (HwProg X Z)) : Prop :=
  ∀ r σ, QuerySupportedOn (fun m : (recHwSpec X Z ValPos M).In i × (runtimeR m₀).D ↦ m.2)
      {s | InvP pub v C s} σ →
    QuerySupportedOn (fun m : (recHwSpec X Z ValPos M).Out i × (runtimeR m₀).D ↦ m.2)
      {s | InvP pub v C' s} (((runtimeR m₀).step i).branch r σ)

theorem stepInv_sponge (m₀ : Finset ValPos × M) (pub : Pub) (v : ValPos → Digest)
    (i : SpongePort) (C : Set (HwProg X Z)) : StepInv m₀ pub v (.inl (.inl (.inl i))) C C := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r σ =
      MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U i) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m₀ i r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    have he := snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty X Z) m₀ i q.1 q'.1 q.2 q'.2 hK
    exact invP_of_eq (congrArg Prod.fst he) (congrArg (fun t ↦ t.2.1) he) hq

theorem stepInv_read (m₀ : Finset ValPos × M) (pub : Pub) (v : ValPos → Digest)
    (c : {c : HwRead X Z (Finset ValPos × M) // ReadMono (memLab X Z ValPos M) c})
    (hc : LabKeep c.1) (C : Set (HwProg X Z)) :
    StepInv m₀ pub v (.inl (.inl (.inr c.1))) C C := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c.1)))).branch r σ =
      MatrixMap.conj (hwReadKraus c.1 r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c.1 r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    obtain ⟨h1, h2⟩ := hwReadKraus_ne_zero_keep hc r (u := q.1) (s := q.2) (u' := q'.1)
      (s' := q'.2) hK
    exact invP_of_eq h1 h2 hq

theorem stepInv_prog (m₀ : Finset ValPos × M) (pub : Pub) (v : ValPos → Digest)
    (c : HwProg X Z) (C : Set (HwProg X Z)) : StepInv m₀ pub v (.inl (.inr c)) C (C \ {c}) := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    invP_prog c (hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK)
      hq

theorem stepInv_rec (m₀ : Finset ValPos × M) (pub : Pub) (v : ValPos → Digest)
    (T : Finset ValPos) (C : Set (HwProg X Z)) :
    StepInv m₀ pub v (.inr T) C (C ∪ revealSet pub v T) := by
  intro r σ hσ
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
    invP_reveal T (recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK) hq

/-- An operator supported on the invariant presents, at a call, no diagonal mass outside it. -/
theorem relabel_diag_eq_zero (m₀ : Finset ValPos × M) {pub : Pub} {v : ValPos → Digest}
    {A : QReg} {i : (recHwSpec X Z ValPos M).Port} (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z ValPos M).In i × E) {ρ : Matrix (A × (runtimeR m₀).D)
      (A × (runtimeR m₀).D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | InvP pub v ∅ s} ρ)
    (a : ((recHwSpec X Z ValPos M).In i × (runtimeR m₀).D) × E) (ha : ¬SlotInv M pub v a.1.2) :
    (SubInstrument.relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).branch () ρ a a =
      0 := by
  by_contra h
  have h₁ := (hρ.branch_relabel (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D)).imp
    (q' := fun m : ((recHwSpec X Z ValPos M).In i × (runtimeR m₀).D) × E ↦ m.1.2)
    (S' := {s | InvP pub v ∅ s}) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ (runtimeR m₀).D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  exact ha (slotInv_of_invP (h₁ a a h).1)

end steps

/-! ## Templates that keep the invariant

`HP pub v y C C'`: run from states on the pending invariant `C`, the template `y` calls the sponge,
read and reveal ports with nothing pending, its read ports keep the label, a program port leaves the
pending set, a reveal of `T` adds the ports of the slots with an input in `T`; it ends on `C'`. -/

section hp

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- The condition of `HP` on the pending set before a call. -/
def portPre : (XSpec M).Port → Set (HwProg X Z) → Prop
  | .inl (.inl (.inl _)), C => C = ∅
  | .inl (.inl (.inr c)), C => C = ∅ ∧ LabKeep c.1
  | .inl (.inr _), _ => True
  | .inr _, C => C = ∅

/-- The pending set after a call. -/
def portPost (pub : Pub) (v : ValPos → Digest) :
    (XSpec M).Port → Set (HwProg X Z) → Set (HwProg X Z)
  | .inl (.inl (.inl _)), C => C
  | .inl (.inl (.inr _)), C => C
  | .inl (.inr p), C => C \ {p.1.realize v}
  | .inr T, C => C ∪ revealSet pub v T

/-- The condition before a command. -/
def cmdPre {A : QReg} : QuantumComp.Cmd L (XSpec M) A → Set (HwProg X Z) → Prop
  | .prim _, _ => True
  | .query i _ _, C => portPre i C

/-- The pending set after a command. -/
def cmdPost (pub : Pub) (v : ValPos → Digest) {A : QReg} :
    QuantumComp.Cmd L (XSpec M) A → Set (HwProg X Z) → Set (HwProg X Z)
  | .prim _, C => C
  | .query i _ _, C => portPost pub v i C

/-- **A template that keeps the invariant**, from the pending set `C` to the pending set `C'`. -/
def HP (pub : Pub) (v : ValPos → Digest) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L (XSpec M)) Ω A → Set (HwProg X Z) →
      Set (HwProg X Z) → Prop
  | _, .pure _, C, C' => C ⊆ C'
  | _, .liftBind c next, C, C' => cmdPre c C ∧ ∀ b, HP pub v (next b) (cmdPost pub v c C) C'

omit [Fintype M] [DecidableEq M] in
theorem cmdPre_anti {A : QReg} (c : QuantumComp.Cmd L (XSpec M) A) {C D : Set (HwProg X Z)}
    (hD : D ⊆ C) (h : cmdPre c C) : cmdPre c D := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · trivial
  · exact Set.subset_empty_iff.1 (h ▸ hD)
  · exact ⟨Set.subset_empty_iff.1 (h.1 ▸ hD), h.2⟩
  · trivial
  · exact Set.subset_empty_iff.1 (h ▸ hD)

omit [Fintype M] [DecidableEq M] in
theorem cmdPost_mono (pub : Pub) (v : ValPos → Digest) {A : QReg}
    (c : QuantumComp.Cmd L (XSpec M) A) {C D : Set (HwProg X Z)} (hD : D ⊆ C) :
    cmdPost pub v c D ⊆ cmdPost pub v c C := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · exact hD
  · exact hD
  · exact hD
  · exact Set.sdiff_subset_sdiff_left hD
  · exact Set.union_subset_union_left _ hD

variable (pub : Pub) (v : ValPos → Digest)

omit [Fintype M] [DecidableEq M] in
theorem hp_mono {A : QReg} (y : IFreeM (QuantumComp.toIPFunctor L (XSpec M)) Ω A)
    {C C' D D' : Set (HwProg X Z)} (hy : HP pub v y C C') (hD : D ⊆ C) (hD' : C' ⊆ D') :
    HP pub v y D D' := by
  induction y using IFreeM.inductionOn generalizing C D with
  | pure _ _ => exact hD.trans (hy.trans hD')
  | liftBind _ c next ih =>
    exact ⟨cmdPre_anti c hD hy.1, fun b ↦ ih b (hy.2 b) (cmdPost_mono pub v c hD)⟩

omit [Fintype M] [DecidableEq M] in
theorem hp_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor L (XSpec M)) Ω A) (C C' : Set (HwProg X Z)) :
    HP pub v (e ▸ y) C C' ↔ HP pub v y C C' := by
  subst e
  rfl

omit [Fintype M] [DecidableEq M] in
theorem hp_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor L (XSpec M)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor L (XSpec M)) Y u)
    {C D C' : Set (HwProg X Z)} (hx : HP pub v x C D) (hg : ∀ u a, HP pub v (g u a) D C') :
    HP pub v (x.bind g) C C' := by
  induction x using IFreeM.inductionOn generalizing C with
  | pure _ a => exact hp_mono pub v _ (hg _ a) hx subset_rfl
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

omit [Fintype M] [DecidableEq M] in
theorem hp₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ L (XSpec M) A B α) (g : α → QuantumComp₂ L (XSpec M) B B' β)
    {C D C' : Set (HwProg X Z)} (hx : HP pub v x C D) (hg : ∀ a, HP pub v (g a) D C') :
    HP pub v (x.bind g) C C' := by
  refine hp_bind pub v x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

omit [Fintype M] [DecidableEq M] in
/-- Substituting trees that keep the invariant with nothing pending. -/
theorem hp_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor L spec)
      (QuantumComp.toIPFunctor L (XSpec M)))
    (hσ : ∀ A c, HP pub v (σ A c) ∅ ∅) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor L spec) Ω A) : HP pub v (x.substitute σ) ∅ ∅ := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact hp_bind pub v _ _ (hσ s c) fun u ans ↦ (hp_cast pub v ans.2 _ _ _).mpr (ih ans.1)

omit [Fintype M] [DecidableEq M] in
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

omit [Fintype M] [DecidableEq M] in
theorem hp_act {A B : QReg} {α : Type} (p : SubInstrument A B α) (C : Set (HwProg X Z)) :
    HP pub v (QComp.act (spec := XSpec M) p) C C :=
  ⟨trivial, fun _ ↦ subset_rfl⟩

omit [Fintype M] [DecidableEq M] in
/-- A reveal with nothing pending makes the ports of the slots with an input in `T` pending. -/
theorem hp_revealThen {B B' : QReg} {α : Type} (T : Finset ValPos)
    (k : RevealVals XD T × (Finset ValPos × M) → QComp (XSpec M) B B' α) {C' : Set (HwProg X Z)}
    (hk : ∀ r, HP pub v (k r) (revealSet pub v T) C') :
    HP pub v (revealThen goodAll T k) ∅ C' :=
  ⟨rfl, fun r ↦ hp₂_bind pub v _ _ (hp_act pub v _ _) fun _ ↦
    hp_mono pub v _ (hk r.down) (Set.empty_union _).le subset_rfl⟩

omit [Fintype M] [DecidableEq M] in
theorem hp_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z ValPos XD) (hp : goodAll p)
    (k : QComp (XSpec M) B B' α) {C C' : Set (HwProg X Z)}
    (hk : HP pub v k (C \ {p.realize v}) C') : HP pub v (progThen p hp k) C C' :=
  ⟨trivial, fun _ ↦ hp₂_bind pub v _ _ (hp_act pub v _ _) fun _ ↦ hk⟩

omit [Fintype M] [DecidableEq M] in
theorem hp_progPorts (B : QReg) (ps : List (LazyProg X Z ValPos XD)) (C : Set (HwProg X Z)) :
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

omit [Fintype M] [DecidableEq M] in
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

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
/-- **A layer signature keeps the invariant**: the randomizer search reads, the reveal of
`layerNeed` makes the ports of the slots with a revealed input pending, and those slots are the
signature's slots, which it then programs. -/
theorem hp_signLayerT (B : QReg) (l : Layer) (e : KeyIndex) (message : HashInput) :
    HP pub v (signLayerT M upd pub B l e message) ∅ ∅ := by
  refine hp₂_bind pub v _ _ (hp_readLift pub v _) fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · exact subset_rfl
  · refine hp_revealThen pub v _ _ fun r ↦
      hp₂_bind pub v _ _ (hp_progSlots pub v B _ _) fun _ ↦ ?_
    rintro c ⟨hc, hn⟩
    exact hn (revealSet_layerNeed_subset pub v l e x hc)

omit [Fintype M] [DecidableEq M] in
theorem hp_signT (B : QReg) (r : SigningRequest) : HP pub v (signT M upd pub B r) ∅ ∅ := by
  refine hp₂_bind pub v _ _ (hp_signLayerT pub v upd B _ _ _) fun b ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · exact subset_rfl
  · refine hp₂_bind pub v _ _ (hp_signLayerT pub v upd B _ _ _) fun t ↦ ?_
    rcases t with _ | ⟨top, _⟩ <;> exact subset_rfl

omit [Fintype M] [DecidableEq M] in
/-- **The challenger keeps the invariant**, with nothing pending between commands. -/
theorem hp_challengeT (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    HP pub v (challengeT M upd pub A c) ∅ ∅ := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact hp_readLift pub v _
  · exact hp_readLift pub v _
  · exact hp_bind pub v _ _ (hp₂_bind pub v _ _ (hp_act pub v _ _) fun _ ↦
      hp_signT pub v upd _ r) fun _ _ ↦ subset_rfl

omit [Fintype M] [DecidableEq M] in
/-- **The game keeps the invariant**: the root's reveal makes nothing pending (the root is no
slot's input), then the challenged adversary and the verification. -/
theorem hp_gameT (A : Adversary (X × Z)) : HP pub v (gameT M upd pub A) ∅ ∅ :=
  hp_revealThen pub v _ _ fun _ ↦ hp_mono pub v _
    (hp₂_bind pub v _ _ (hp_substitute pub v _ (hp_challengeT pub v upd) _) fun _ ↦
      hp₂_bind pub v _ _ (hp_readLift pub v _) fun _ ↦ subset_rfl)
    (revealSet_rootPos pub v) subset_rfl

end hp

/-! ## `hinv` -/

section hinv

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- One call of a realized program on the pending invariant. -/
theorem forallQueries_queryBind_of_step {Q : (recHwSpec X Z ValPos M).Port → Prop}
    (m₀ : Finset ValPos × M) (I : L.Interp) (pub : Pub) (v : ValPos → Digest) {A : QReg}
    (i : (recHwSpec X Z ValPos M).Port) (E : QReg) (ℓ : A ≃ (recHwSpec X Z ValPos M).In i × E)
    (k' : (recHwSpec X Z ValPos M).Result i → QuantumComp L (recHwSpec X Z ValPos M) Ω
      (QReg.of ((recHwSpec X Z ValPos M).Out i × E)))
    {C C' : Set (HwProg X Z)} (hpre : Q i → C = ∅) (hstep : StepInv m₀ pub v i C C')
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of ((recHwSpec X Z ValPos M).Out i × E) ×
        (runtimeR m₀).D ↦ m.2) {s | InvP pub v C' s} ρ' →
      (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (SlotInv M pub v)) (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | InvP pub v C s} ρ) :
    (runtimeR m₀).ForallQueries I (invSupp (runtimeR m₀) Q (SlotInv M pub v))
      (QuantumComp.queryBind i E ℓ k') ρ :=
  ⟨fun hq a ha ↦ relabel_diag_eq_zero (i := i) m₀ E ℓ (hpre hq ▸ hρ) a ha, fun r ↦
    hk r _ (querySupportedOn_queryStep (runtimeR m₀) (fun s ↦ s) i r (hstep r) E ℓ hρ)⟩

/-- **The realized program of a template keeping the invariant presents, at every call of the
ports `Q` (no program port), only states of the invariant.** -/
theorem forallQueries_of_hp {Q : (recHwSpec X Z ValPos M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (m₀ : Finset ValPos × M) (I : L.Interp) (pub : Pub)
    (v : ValPos → Digest) {A : QReg} (y : QuantumComp L (XSpec M) Ω A) :
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
    · exact forallQueries_queryBind_of_step m₀ I pub v (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT v (k r)) (fun _ ↦ hy.1) (stepInv_sponge m₀ pub v i C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_step m₀ I pub v (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT v (k r)) (fun _ ↦ hy.1.1) (stepInv_read m₀ pub v c hy.1.2 C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_step m₀ I pub v
          (.inl (.inr ((LazyProg.programH T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepInv_prog m₀ pub v _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_step m₀ I pub v
          (.inl (.inr ((LazyProg.programK T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepInv_prog m₀ pub v _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_step m₀ I pub v
          (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun hq ↦ absurd hq (hQ _)) (stepInv_prog m₀ pub v _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_step m₀ I pub v (.inr T) E ℓ
        (fun m ↦ realizeT v (k (restrictTo T v, m))) (fun _ ↦ hy.1) (stepInv_rec m₀ pub v T C)
        (fun m ↦ ih (restrictTo T v, m) _ C' (hy.2 (ULift.up (restrictTo T v, m)))) ρ hρ

/-- An initial state whose memory label is empty is on the invariant. -/
theorem querySupportedOn_init (m₀ : Finset ValPos × M) (hm₀ : m₀.1 = ∅) {A : QReg}
    (σ : Matrix A A ℂ) :
    QuerySupportedOn (fun a : A × QReg.of (HwReg X Z (Finset ValPos × M)) ↦ a.2.2.2.1) {∅}
      (σ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  intro a b h
  change (σ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
    hwEmpty X Z, m₀) : HwReg X Z (Finset ValPos × M))).matrix) a b ≠ 0 at h
  rw [SubState.matrix_basis, kroneckerMap_apply] at h
  have h' := right_ne_zero_of_mul h
  rw [Matrix.single_apply] at h'
  split_ifs at h' with he
  · show a.2.2.2.1 ∈ ({∅} : Set (Finset ValPos)) ∧ b.2.2.2.1 ∈ ({∅} : Set (Finset ValPos))
    rw [← he.1, ← he.2]
    exact ⟨hm₀, hm₀⟩
  · exact absurd rfl h'

variable (upd : TrialUpd M)

/-- **`hinv` for the realized template game**, at every public datum: from states with an empty
memory label, every call of ports `Q` that are not program ports sees the invariant `SlotInv`. -/
theorem forallQueries_gameT {Q : (recHwSpec X Z ValPos M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (m₀ : Finset ValPos × M) (pub : Pub) (A : Adversary (X × Z))
    (v : ValPos → Digest)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset ValPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset ValPos × M))) ℂ)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit × QReg.of (HwReg X Z (Finset ValPos × M)) ↦
      a.2.2.2.1) {∅} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Q (SlotInv M pub v)) (realizeT v (gameT M upd pub A)) ρ :=
  forallQueries_of_hp hQ m₀ _ pub v _ ∅ ∅ (hp_gameT pub v upd A) ρ
    (hρ.imp fun _ ha ↦ invP_of_label_empty (Set.mem_singleton_iff.1 ha))

/-- **Masses' `hinv`** with `Inv p v := SlotInv M (pubP p) v`, for any `pubP`. -/
theorem hinv_gameT {P : Type} (pubP : P → Pub) {Q : (recHwSpec X Z ValPos M).Port → Prop}
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (m₀ : Finset ValPos × M) (A : Adversary (X × Z))
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset ValPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset ValPos × M))) ℂ)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit × QReg.of (HwReg X Z (Finset ValPos × M)) ↦
      a.2.2.2.1) {∅} ρ) :
    ∀ p v, (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Q ((fun p v ↦ SlotInv M (pubP p) v) p v))
      (realizeT v (gameT M upd (pubP p) A)) ρ :=
  fun p v ↦ forallQueries_gameT upd hQ m₀ (pubP p) A v ρ hρ

end hinv

/-! ## The ports of the read mass

`readMass` charges the classical ports (`extCls`), program ports included, but its hidden sets are
empty at the program and record ports. The invariant holds at the read and record ports only, so
the read-mass bound goes through `portMass` of the read and record ports (`readRecPort`). -/

section readRec

variable {M : Type} [Fintype M] [DecidableEq M]

variable (M) in
/-- The read and record ports of runtime 2 with record ports. -/
def readRecPort : (recHwSpec X Z ValPos M).Port → Bool
  | .inl (.inl (.inr _)) => true
  | .inr _ => true
  | _ => false

omit [Fintype M] [DecidableEq M] in
theorem readRecPort_prog (c : HwProg X Z) : ¬readRecPort M (.inl (.inr c)) = true :=
  Bool.false_ne_true

/-- **The read mass is the hidden mass at the read and record ports.** -/
theorem readMass_eq_portMass (Hh : Set Z) (Hk Hk' : Set X) :
    readMass (S := ValPos) (M' := M) Hh Hk Hk' =
      portMass (fun i ↦ readRecPort M i = true) Hh Hk Hk' := by
  funext i σ
  rcases i with ((i | c) | c) | T
  · rfl
  · rfl
  · rfl
  · rfl

end readRec

/-! ## Charges of the calls -/

section charges

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

variable (M) in
/-- A charge on the template ports by kind: `a` per sponge call, `b` per read, `c` per program
call, `d` per reveal. -/
def tCharge (a b c d : ℕ) : (XSpec M).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr _)) => b
  | .inl (.inr _) => c
  | .inr _ => d

variable (M) in
/-- The same charge on runtime 2 with record ports (a reveal realizes as a record call). -/
def rCharge (a b c d : ℕ) : (recHwSpec X Z ValPos M).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr _)) => b
  | .inl (.inr _) => c
  | .inr _ => d

variable (M) in
/-- The charge on runtime 1's ports: `a` per sponge call, `b` per read. -/
def rdCharge (a b : ℕ) : (hwReadSpec X Z M).Port → ℕ
  | .inl _ => a
  | .inr _ => b

variable (a b c d : ℕ)

omit [Fintype M] [DecidableEq M] in
/-- **Realizing keeps the charges by kind.** -/
theorem isChargeBound_realizeT (v : ValPos → Digest) {A : QReg} {y : QuantumComp L (XSpec M) Ω A}
    {n : ℕ} (h : IFreeM.IsChargeBound y (portCharge (tCharge M a b c d)) n) :
    IFreeM.IsChargeBound (realizeT v y) (portCharge (rCharge M a b c d)) n := by
  refine IFreeM.IsChargeBound.mapLens (tmplLens v) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (rCharge M a b c d) s ((tmplLens v).toFunA s cmd)) =
      portCharge (tCharge M a b c d) := by
    funext s cmd
    rcases cmd with o | ⟨((i | c) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem isChargeBound_readLift {A : QReg} {y : QuantumComp L (hwReadSpec X Z M) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (rdCharge M a b)) n) :
    IFreeM.IsChargeBound (readLift goodAll y) (portCharge (tCharge M a b c d)) n := by
  refine IFreeM.IsChargeBound.mapLens (readLens goodAll) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (tCharge M a b c d) s
      ((readLens goodAll).toFunA s cmd)) = portCharge (rdCharge M a b) := by
    funext s cmd
    rcases cmd with o | ⟨i | c, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

omit [Fintype M] [DecidableEq M] in
/-- **The simulation of a permutation program** with at most `q` calls makes at most `6q` sponge
calls (`simulate`: two of each of the three ports per call). -/
theorem isChargeBound_simulate (π : Equiv.Perm (X × Z)) {A : QReg}
    {x : QuantumComp LocalSig.instruments.{0} (qrpmSpec (X × Z)) Ω A} {q : ℕ}
    (hx : x.IsTotalQueryBound q) :
    IFreeM.IsChargeBound ((simulate LocalSig.Interp.instruments π x).liftOrdinary
      (t := hwReadCmdSpec X Z M)) (portCharge (rdCharge M a b)) (a * (2 * q + 2 * q + 2 * q)) := by
  have hs := isQueryBound_simulate LocalSig.Interp.instruments π hx
  have h3 := (IFreeM.IsChargeBound.add (IFreeM.IsChargeBound.add (hs SpongePort.h)
    (hs SpongePort.k)) (hs SpongePort.k')).mul a
  refine IFreeM.IsChargeBound.mapLens QuantumComp.ordinaryLens ?_
  have he : (fun s cmd ↦ portCharge (L := LocalSig.instruments.{0}) (rdCharge M a b) s
      (QuantumComp.ordinaryLens.toFunA s cmd)) = fun s cmd ↦
      a * (QuantumComp.queryCharge SpongePort.h s cmd + QuantumComp.queryCharge SpongePort.k s cmd +
        QuantumComp.queryCharge SpongePort.k' s cmd) := by
    funext s cmd
    rcases cmd with o | ⟨j, E, ℓ⟩
    · simp [QuantumComp.queryCharge, portCharge, QuantumComp.ordinaryLens]
    · cases j <;> simp [QuantumComp.queryCharge, portCharge, QuantumComp.ordinaryLens, rdCharge]
  rw [he]
  exact h3

/-! ### Fixed-register programs and stateful read programs -/

theorem chg_act {spec : QuantumOracleSpec.{0, 0}} (κ : spec.Port → ℕ) {A B : QReg} {α : Type}
    (p : SubInstrument A B α) (n : ℕ) :
    IFreeM.IsChargeBound (QComp.act (spec := spec) p) (portCharge κ) n :=
  ⟨Nat.zero_le _, fun _ ↦ trivial⟩

theorem chg_map {spec : QuantumOracleSpec.{0, 0}} (κ : spec.Port → ℕ) {A B : QReg} {α β : Type}
    {x : QComp spec A B α} (f : α → β) {n : ℕ}
    (h : IFreeM.IsChargeBound x (portCharge κ) n) :
    IFreeM.IsChargeBound (x.map f) (portCharge κ) n := by
  rw [QuantumComp₂.map_eq_bind_pure]
  exact FreeM₂.isChargeBound_bind (n₂ := 0) h fun _ ↦ trivial

/-- A charge bound on a stateful program from every state. -/
def SChg {spec : QuantumOracleSpec.{0, 0}} (κ : spec.Port → ℕ) {B : QReg} {σ α : Type}
    (x : StateT σ (QComp spec B B) α) (n : ℕ) : Prop :=
  ∀ s, IFreeM.IsChargeBound (x.run s) (portCharge κ) n

section schg

variable {spec : QuantumOracleSpec.{0, 0}} (κ : spec.Port → ℕ) {B : QReg} {σ α β : Type}

theorem sChg_mono {x : StateT σ (QComp spec B B) α} {n n' : ℕ} (h : SChg κ x n) (hn : n ≤ n') :
    SChg κ x n' :=
  fun s ↦ IFreeM.IsChargeBound.mono (h s) hn

theorem sChg_pure (a : α) (n : ℕ) : SChg κ (pure a : StateT σ (QComp spec B B) α) n := by
  intro s
  rw [StateT.run_pure]
  trivial

theorem sChg_bind {x : StateT σ (QComp spec B B) α} {f : α → StateT σ (QComp spec B B) β}
    {n₁ n₂ : ℕ} (hx : SChg κ x n₁) (hf : ∀ a, SChg κ (f a) n₂) : SChg κ (x >>= f) (n₁ + n₂) := by
  intro s
  rw [StateT.run_bind]
  exact FreeM₂.isChargeBound_bind (hx s) fun p ↦ hf p.1 p.2

theorem sChg_map {x : StateT σ (QComp spec B B) α} (f : α → β) {n : ℕ} (hx : SChg κ x n) :
    SChg κ (f <$> x) n := by
  intro s
  rw [StateT.run_map]
  exact chg_map κ _ (hx s)

theorem sChg_foldlM {γ : Type} (f : α → γ → StateT σ (QComp spec B B) α) (k : ℕ)
    (hf : ∀ s b, SChg κ (f s b) k) (msg : List γ) (s : α) :
    SChg κ (msg.foldlM f s) (k * msg.length) := by
  induction msg generalizing s with
  | nil => exact sChg_pure κ s _
  | cons b msg ih =>
    rw [List.foldlM_cons]
    refine sChg_mono κ (sChg_bind κ (hf s b) fun s' ↦ ih s') ?_
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm]

end schg

omit [Fintype M] [DecidableEq M] in
theorem chg_readCall (c : HwRead X Z M) (B : QReg) :
    IFreeM.IsChargeBound (readCall c B) (portCharge (rdCharge M a b)) b := by
  unfold readCall
  exact FreeM₂.isChargeBound_bind (n₂ := 0)
    ((IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_rfl, fun _ ↦ trivial⟩) fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
theorem sChg_readCall (c : HwRead X Z M) (B : QReg) {β : Type}
    (g : c.Result → List (SpongeRead X Z) → β × List (SpongeRead X Z)) :
    SChg (rdCharge M a b) (fun log ↦ (readCall c B).bind fun r ↦ QuantumComp₂.pure (g r log) :
      StateT (List (SpongeRead X Z)) (QComp (hwReadSpec X Z M) B B) β) b := by
  intro log
  show IFreeM.IsChargeBound ((readCall c B).bind fun r ↦ QuantumComp₂.pure (g r log)) _ _
  exact FreeM₂.isChargeBound_bind (n₂ := 0) (chg_readCall a b c B) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- A round of reads: three read calls. -/
theorem sChg_rdRound (π : Equiv.Perm (X × Z)) (B : QReg) (s : X × Z) (blk : X) :
    SChg (rdCharge M a b) (rdRound M π B s blk) (3 * b) := by
  refine sChg_mono _ (sChg_bind _ (sChg_readCall a b _ B _) fun _ ↦
    sChg_bind _ (sChg_readCall a b _ B _) fun _ ↦
      sChg_bind _ (sChg_readCall a b _ B _) fun _ ↦ sChg_pure _ _ 0) (by omega)

omit [Fintype M] [DecidableEq M] in
/-- A trial's round of reads: three read calls. -/
theorem sChg_rdRoundU (u : X → X → M → Option X → M) (π : Equiv.Perm (X × Z)) (B : QReg)
    (s : X × Z) (blk : X) : SChg (rdCharge M a b) (rdRoundU M u π B s blk) (3 * b) := by
  refine sChg_mono _ (sChg_bind _ (sChg_readCall a b _ B _) fun _ ↦
    sChg_bind _ (sChg_readCall a b _ B _) fun _ ↦
      sChg_bind _ (sChg_readCall a b _ B _) fun _ ↦ sChg_pure _ _ 0) (by omega)

omit [Fintype M] [DecidableEq M] in
/-- **A randomizer trial's hash**: three reads per block. -/
theorem chg_hashTrial (u : X → X → M → Option X → M) (π : Equiv.Perm (X × Z)) (B : QReg)
    (input : HashInput) :
    IFreeM.IsChargeBound (hashTrial M u π B input) (portCharge (rdCharge M a b))
      (3 * b * (blocks input).length) := by
  unfold hashTrial
  rw [StateT.run'_eq]
  exact chg_map _ _ (sChg_map _ _ (sChg_map _ _
    (sChg_foldlM _ _ _ (sChg_rdRoundU a b u π B) (blocks input) (0, 0))) [])

omit [Fintype M] [DecidableEq M] in
theorem sChg_readsImpl (π : Equiv.Perm (X × Z)) (B : QReg) (input : HashInput) :
    SChg (rdCharge M a b) (readsImpl M π B input) (3 * b * hashBlocks input) := by
  rw [hashBlocks_eq_length_blocks]
  exact sChg_map _ _ (sChg_map _ _ (sChg_foldlM _ _ _ (sChg_rdRound a b π B) (blocks input) (0, 0)))

omit [Fintype M] [DecidableEq M] in
theorem sChg_simulateQ_readsImpl (π : Equiv.Perm (X × Z)) (B : QReg) {α : Type}
    (x : OracleComp LeanXmss.HashSpec α) {n : ℕ} (h : QueryCostAtMost x hashBlocks n) :
    SChg (rdCharge M a b) (simulateQ (readsImpl M π B) x) (3 * b * n) := by
  induction x using OracleComp.inductionOn generalizing n with
  | pure x => rw [simulateQ_pure]; exact sChg_pure _ x _
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_spec_query]
    refine sChg_mono _ (sChg_bind _ (sChg_readsImpl a b π B t) fun u ↦ ih u (h.2 u)) ?_
    rw [← Nat.mul_add, Nat.add_sub_cancel' h.1]

omit [Fintype M] [DecidableEq M] in
/-- **A hash computation through read ports**: three reads per block of a path bound. -/
theorem chg_readsProgram (π : Equiv.Perm (X × Z)) (B : QReg) {α : Type}
    {x : OracleComp LeanXmss.HashSpec α} {n : ℕ} (h : QueryCostAtMost x hashBlocks n) :
    IFreeM.IsChargeBound (readsProgram M π B x) (portCharge (rdCharge M a b)) (3 * b * n) :=
  sChg_simulateQ_readsImpl a b π B x h []

/-- A trial input of a message of at most `32` bytes is one block. -/
theorem length_blocks_trial (param : PublicParameter) (fields : TweakFields) {message : HashInput}
    (hm : message.length ≤ 32) (base : Randomizer) (trial : ℕ) :
    (blocks (thInput param fields (message ++ littleEndianBytes 16
      (base + BitVec.ofNat digestBits trial)))).length = 1 := by
  rw [length_blocks, XmssCost.thInput_length, List.length_append]
  simp only [littleEndianBytes, List.length_ofFn]
  omega

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
/-- **The randomizer search**: three reads per trial. -/
theorem chg_grindR (pub : Pub) (B : QReg) (l : Layer) (e : KeyIndex) {message : HashInput}
    (hm : message.length ≤ 32) (base : Randomizer) :
    ∀ n trial, IFreeM.IsChargeBound (grindR M upd pub B l e message base n trial)
      (portCharge (rdCharge M a b)) (n * (3 * b))
  | 0, _ => trivial
  | n + 1, trial => by
    have ht := chg_hashTrial a b (upd l e) pub.perm B (thInput pub.param
      (hashDomainFields (.message l e)) (message ++ littleEndianBytes 16
        (base + BitVec.ofNat digestBits trial)))
    rw [length_blocks_trial _ _ hm, Nat.mul_one] at ht
    rw [grindR]
    refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := n * (3 * b)) ht
      fun out ↦ ?_) (le_of_eq (by ring))
    show IFreeM.IsChargeBound (match Codeword.decode (truncateHash out) with
      | some x => QuantumComp₂.pure (some (base + BitVec.ofNat digestBits trial, x))
      | none => grindR M upd pub B l e message base n (trial + 1)) _ _
    split
    · trivial
    · exact chg_grindR pub B l e hm base n (trial + 1)

omit [Fintype M] [DecidableEq M] in
theorem chg_revealThen {B B' : QReg} {α : Type} (T : Finset ValPos)
    (k : RevealVals XD T × (Finset ValPos × M) → QComp (XSpec M) B B' α) {n : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (tCharge M a b c d)) n) :
    IFreeM.IsChargeBound (revealThen goodAll T k) (portCharge (tCharge M a b c d)) (d + n) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right d n, fun r ↦ ?_⟩
  simp only [tCharge, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hk r) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
theorem chg_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z ValPos XD) (hp : goodAll p)
    (k : QComp (XSpec M) B B' α) {n : ℕ}
    (hk : IFreeM.IsChargeBound k (portCharge (tCharge M a b c d)) n) :
    IFreeM.IsChargeBound (progThen p hp k) (portCharge (tCharge M a b c d)) (c + n) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right c n, fun r ↦ ?_⟩
  simp only [tCharge, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hk) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
theorem chg_progPorts (B : QReg) (ps : List (LazyProg X Z ValPos XD)) :
    IFreeM.IsChargeBound (progPorts M B ps) (portCharge (tCharge M a b c d)) (c * ps.length) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    refine IFreeM.IsChargeBound.mono (chg_progThen a b c d p trivial _ ih) (le_of_eq ?_)
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm]

omit [Fintype M] [DecidableEq M] in
theorem chg_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    IFreeM.IsChargeBound (progSlots M pub B ss) (portCharge (tCharge M a b c d))
      (c * (ss.map fun s ↦ (slotPorts pub s).length).sum) := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    refine IFreeM.IsChargeBound.mono
      (FreeM₂.isChargeBound_bind (chg_progPorts a b c d B _) fun _ ↦ ih) (le_of_eq ?_)
    rw [List.map_cons, List.sum_cons, Nat.mul_add]

theorem length_slotPorts (pub : Pub) (s : Slot) : (slotPorts pub s).length = 3 * nBlocks pub s := by
  simp [slotPorts, List.length_flatMap, Nat.mul_comm]

theorem nBlocks_chain (pub : Pub) (l : Layer) (e : KeyIndex) (step : ChainStep) (i : ChainIndex) :
    nBlocks pub (.chain l e step i) = 1 := by
  rw [nBlocks, length_blocks, slotInput, XmssCost.thInput_length]
  simp [slotPayload, Verification.chainPayload, littleEndianBytes]

theorem nBlocks_leaf (pub : Pub) (l : Layer) (e : KeyIndex) : nBlocks pub (.leaf l e) = 8 := by
  rw [nBlocks, length_blocks, slotInput, XmssCost.thInput_length]
  simp only [slotPayload, XmssCost.digestsPayload_length]
  simp [chainCount]

theorem nBlocks_node (pub : Pub) (l : Layer) (level index : ℕ) :
    nBlocks pub (.node l level index) = 1 := by
  rw [nBlocks, length_blocks, slotInput, XmssCost.thInput_length]
  simp [slotPayload, OverPermutation.nodePayload, littleEndianBytes]

/-- **The program calls of a layer signature**: at most `594` (three per block of the `174` chain
steps at most, the `8`-block leaf and the `16` nodes). -/
theorem sum_length_slotPorts_layerSlots_le (pub : Pub) (l : Layer) (e : KeyIndex) (x : Encoding) :
    ((layerSlots l e x).map fun s ↦ (slotPorts pub s).length).sum ≤ 594 := by
  have hchain : ∀ y ∈ ((List.finRange chainCount).flatMap fun i ↦
      ((List.finRange (chainLength - 1)).filter fun step ↦ decide ((x i).val ≤ step.val)).map
        fun step ↦ Slot.chain l e step i).map (fun s ↦ (slotPorts pub s).length), y ≤ 3 := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
    obtain ⟨i, -, hs⟩ := List.mem_flatMap.1 hs
    obtain ⟨step, -, rfl⟩ := List.mem_map.1 hs
    rw [length_slotPorts, nBlocks_chain]
  have hlen : ((List.finRange chainCount).flatMap fun i ↦
      ((List.finRange (chainLength - 1)).filter fun step ↦ decide ((x i).val ≤ step.val)).map
        fun step ↦ Slot.chain l e step i).length ≤ 174 := by
    rw [List.length_flatMap]
    refine (List.sum_le_length_nsmul _ 3 fun y hy ↦ ?_).trans
      (by rw [List.length_map, List.length_finRange]; simp [chainCount])
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    simp only [List.length_map]
    exact (List.length_filter_le _ _).trans
      (by rw [List.length_finRange]; simp [chainLength, winternitzBits])
  have hnode : ∀ y ∈ ((List.range layerHeight).map fun lev ↦
      Slot.node l (lev + 1) (e.val / 2 ^ (lev + 1))).map (fun s ↦ (slotPorts pub s).length),
      y ≤ 3 := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
    obtain ⟨lev, -, rfl⟩ := List.mem_map.1 hs
    rw [length_slotPorts, nBlocks_node]
  have h1 := List.sum_le_length_nsmul _ 3 hchain
  have h2 := List.sum_le_length_nsmul _ 3 hnode
  simp only [List.length_map, smul_eq_mul, List.length_range] at h1 h2
  rw [layerSlots, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    length_slotPorts, nBlocks_leaf]
  have hH : layerHeight = 16 := rfl
  omega

/-- The calls of one layer signature by kind: the randomizer search's reads, one reveal and the
program calls. -/
def layerCalls (b c d : ℕ) : ℕ :=
  randomizerAttemptLimit * (3 * b) + (d + c * 594)

omit [Fintype M] [DecidableEq M] in
/-- **A layer signature's calls.** -/
theorem chg_signLayerT (pub : Pub) (B : QReg) (l : Layer) (e : KeyIndex) {message : HashInput}
    (hm : message.length ≤ 32) :
    IFreeM.IsChargeBound (signLayerT M upd pub B l e message) (portCharge (tCharge M a b c d))
      (layerCalls b c d) := by
  unfold signLayerT
  refine FreeM₂.isChargeBound_bind (isChargeBound_readLift a b c d
    (chg_grindR a b upd pub B l e hm _ _ _)) fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · trivial
  · refine chg_revealThen a b c d _ _ fun r ↦ ?_
    refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
      (chg_progSlots a b c d pub B _) fun _ ↦ trivial) ?_
    rw [Nat.add_zero]
    exact Nat.mul_le_mul_left c (sum_length_slotPorts_layerSlots_le pub l e x)

omit [Fintype M] [DecidableEq M] in
/-- **A signature's calls**: two layer signatures. -/
theorem chg_signT (pub : Pub) (B : QReg) (r : SigningRequest) :
    IFreeM.IsChargeBound (signT M upd pub B r) (portCharge (tCharge M a b c d))
      (2 * layerCalls b c d) := by
  unfold signT
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := layerCalls b c d)
    (chg_signLayerT a b c d upd pub B _ _ (XmssCost.littleEndianBytes_length _ _).le)
    fun t ↦ ?_) (le_of_eq (by omega))
  rcases t with _ | ⟨bottom, f⟩
  · trivial
  · refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
      (chg_signLayerT a b c d upd pub B _ _
        ((XmssCost.littleEndianBytes_length _ _).le.trans (by norm_num))) fun t ↦ ?_) le_rfl
    rcases t with _ | ⟨top, _⟩ <;> trivial

/-- The source charge of the adversary's commands: `α` per permutation call, `β` per signing
request. -/
def advCharge (α β : ℕ) (A : QReg) (cmd : QuantumComp.Cmd LocalSig.instruments.{0}
    (advSpec (X × Z)) A) : ℕ :=
  α * cmdCharge permCharge A cmd + β * cmdCharge signCharge A cmd

omit [Fintype M] [DecidableEq M] in
/-- **The challenger's calls** per command: a local operation none, a permutation call `6a` (the
simulation), a signing request the signature's calls `S`. -/
theorem chg_challengeT (pub : Pub) {S : ℕ}
    (hS : ∀ B r, IFreeM.IsChargeBound (signT M upd pub B r) (portCharge (tCharge M a b c d)) S)
    (A : QReg) (cmd : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    IFreeM.IsChargeBound (challengeT M upd pub A cmd) (portCharge (tCharge M a b c d))
      (advCharge (6 * a) S A cmd) := by
  rcases cmd with o | ⟨p | r, E, ℓ⟩
  · refine IFreeM.IsChargeBound.mono (isChargeBound_readLift a b c d (isChargeBound_simulate a b
      _ (q := 0) ((QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦ trivial))) ?_
    simp [advCharge, cmdCharge]
  · refine IFreeM.IsChargeBound.mono (isChargeBound_readLift a b c d (isChargeBound_simulate a b
      _ (q := 1) ((QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
        ⟨Nat.one_pos, fun _ ↦ trivial⟩))) ?_
    simp only [advCharge, cmdCharge, permCharge, signCharge]
    omega
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind (FreeM₂.isChargeBound_bind
      (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hS _ r) fun _ _ ↦ IFreeM.isChargeBound_pure _ 0) ?_
    simp only [advCharge, cmdCharge, permCharge, signCharge]
    omega

omit [Fintype M] [DecidableEq M] in
/-- **The game's calls, by components**: the root's reveal, the challenged adversary (`6a` per
permutation call, `S` per signing request), and the verification's reads (three per block). -/
theorem chg_gameT_of_signT (pub : Pub) (A : Adversary (X × Z)) {q n S : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) n)
    (hS : ∀ B r, IFreeM.IsChargeBound (signT M upd pub B r) (portCharge (tCharge M a b c d)) S) :
    IFreeM.IsChargeBound (gameT M upd pub A) (portCharge (tCharge M a b c d))
      (d + ((6 * a * q + S * n) + 3 * b * verifyBlocks)) := by
  refine chg_revealThen a b c d _ _ fun r₀ ↦ ?_
  have hx := IFreeM.IsChargeBound.add
    ((isChargeBound_withSignLog (hperm ⟨extendVals r₀.1 rootPos, pub.param⟩)).mul (6 * a))
    ((isChargeBound_withSignLog (hsign ⟨extendVals r₀.1 rootPos, pub.param⟩)).mul S)
  have hh : ∀ s (cmd : (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec (X × Z))).A s),
      IFreeM.IsChargeBound (challengeT M upd pub s cmd) (portCharge (tCharge M a b c d))
        (advCharge (6 * a) S s cmd) :=
    chg_challengeT a b c d upd pub hS
  have hc := IFreeM.IsChargeBound.substitute (challengeT M upd pub) hh hx
  refine FreeM₂.isChargeBound_bind hc fun run ↦ ?_
  have hv := chg_readsProgram (M := M) a b pub.perm (QReg.of Unit)
    (verify_cost' ⟨extendVals r₀.1 rootPos, pub.param⟩ run.1)
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
    (isChargeBound_readLift a b c d (chg_map _ Prod.fst hv)) fun _ ↦ trivial) (Nat.add_zero _).le

/-- The calls of the game by kind: the root's reveal, `6a` per permutation call, two layer
signatures per signing request, three reads per verification block. -/
def gameCalls (a b c d q : ℕ) : ℕ :=
  d + ((6 * a * q + 2 * layerCalls b c d * lifetime) + 3 * b * verifyBlocks)

omit [Fintype M] [DecidableEq M] in
/-- **The realized game's calls by kind**, for an adversary making at most `q` permutation calls
and at most `lifetime` signing requests on every path, at every public datum and hidden values. -/
theorem chg_realizeT_gameT (A : Adversary (X × Z)) {q : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (pub : Pub) (v : ValPos → Digest) :
    IFreeM.IsChargeBound (realizeT v (gameT M upd pub A)) (portCharge (rCharge M a b c d))
      (gameCalls a b c d q) :=
  isChargeBound_realizeT a b c d v
    (chg_gameT_of_signT a b c d upd pub A hperm hsign (chg_signT a b c d upd pub))

end charges

/-! ## `hN` -/

section hN

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M) (A : Adversary (X × Z))
  {q : ℕ} (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

omit [Fintype M] [DecidableEq M] in
/-- **`hN` at the sponge ports**: at most `6q` sponge calls. -/
theorem hN_sponge (pub : Pub) (v : ValPos → Digest) :
    IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
      (portCharge fun i ↦ if extCls X Z (Finset ValPos × M) (recSpec ValPos M) i then 0 else 1)
      (6 * q) := by
  have he : (fun i ↦ if extCls X Z (Finset ValPos × M) (recSpec ValPos M) i then 0 else 1) =
      rCharge M 1 0 0 0 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_gameT 1 0 0 0 upd A hperm hsign pub v)
    (le_of_eq (by simp [gameCalls, layerCalls]))

omit hperm hsign in
/-- The true count of the classical calls: one reveal for the root, per signing request two
layer signatures of `3 · 2^32` reads, one reveal and at most `594` program calls, and
`3 · verifyBlocks` reads for the verification. -/
theorem gameCalls_cls_le (q : ℕ) :
    gameCalls 0 1 1 1 q ≤ 3 * (signBlocks * lifetime + verifyBlocks) + 2 * progCap := by
  rw [gameCalls, layerCalls, signBlocks_eq, verifyBlocks_eq, progCap_eq]
  simp [randomizerAttemptLimit, lifetime, layerCount, layerHeight]

omit [Fintype M] [DecidableEq M] in
/-- **`hN` at the classical ports** (reads, program and record calls): at most Security's
`clsCap = 3 (signBlocks · lifetime + verifyBlocks) + 2 progCap`. -/
theorem hN_cls (pub : Pub) (v : ValPos → Digest) :
    IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
      (portCharge fun i ↦ if extCls X Z (Finset ValPos × M) (recSpec ValPos M) i then 1 else 0)
      (3 * (signBlocks * lifetime + verifyBlocks) + 2 * progCap) := by
  have he : (fun i ↦ if extCls X Z (Finset ValPos × M) (recSpec ValPos M) i then 1 else 0) =
      rCharge M 0 1 1 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_gameT 0 1 1 1 upd A hperm hsign pub v)
    (gameCalls_cls_le q)

omit [Fintype M] [DecidableEq M] in
/-- **`hN` at the read and record ports** (`readRecPort`, the ports of the read mass on which the
invariant holds): at most `clsCap`. -/
theorem hN_readRec (pub : Pub) (v : ValPos → Digest) :
    IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
      (portCharge fun i ↦ if readRecPort M i = true then 1 else 0)
      (3 * (signBlocks * lifetime + verifyBlocks) + 2 * progCap) := by
  have he : (fun i ↦ if readRecPort M i = true then 1 else 0) = rCharge M 0 1 0 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  refine IFreeM.IsChargeBound.mono (chg_realizeT_gameT 0 1 0 1 upd A hperm hsign pub v)
    ((?_ : gameCalls 0 1 0 1 q ≤ gameCalls 0 1 1 1 q).trans (gameCalls_cls_le q))
  simp only [gameCalls, layerCalls]
  gcongr
  norm_num

omit [Fintype M] [DecidableEq M] in
/-- **`hN` at the program ports**: at most `progCap` program calls. -/
theorem hN_prog (pub : Pub) (v : ValPos → Digest) :
    IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
      (portCharge (extProgCharge X Z (Finset ValPos × M) (recSpec ValPos M))) progCap := by
  have he : extProgCharge X Z (Finset ValPos × M) (recSpec ValPos M) = rCharge M 0 0 1 0 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  refine IFreeM.IsChargeBound.mono (chg_realizeT_gameT 0 0 1 0 upd A hperm hsign pub v)
    (le_of_eq ?_)
  simp [gameCalls, layerCalls, progCap, reqCells]

end hN

end Quantum.Xmss.Assembly

end
