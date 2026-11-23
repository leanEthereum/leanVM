module

public import Quantum.Sphincs.Assembly.ProgView
public import Quantum.Xmss.Assembly.CoversFull
public import Quantum.Xmss.Assembly.MassSources

@[expose] public section

/-!
# The program calls of leanSPHINCS's template game are safe

Along the realized template game `realizeT v (gameT Selections upd pol pub A)` and its challenge
prefix (`prefixT`), for every digest policy `pol`, every program call is presented only states at
which the port is safe for the event `Bad (evData pub v) N` (ProgView's `safeSupp`;
`forallQueries_safeSupp_gameT`, `forallQueries_safeSupp_prefixT`), from any initial state whose
hardwired `k`, `k'` cells hold the public keys' values (the canonical start has none:
`querySupportedOn_init_keyHeld`). So the program flips are the fresh `k`, `k'` flips
(`progW_le_kW_gameT`, `progW_le_kW_prefixT`, averaged in `uavg_progW_le_kW_gameT`,
`uavg_progW_le_kW_prefixT`): `progRest` needs no bad-fraction term beyond `NoHmsgHead`.

The only condition on the data is `NoHmsgHead pub v`: the one-block prefix of a multi-block
structural slot's honest tail (the WOTS leaf's 8 blocks, the FORS roots' 4) is no `H_msg` tail.
`hmsgSlot` reads `PK.seed ‖ PK.root` at bytes `16` to `47` of an 84-byte padded block, where a
structural first block holds its address, so this fails only if `PK.seed` equals an address's first
16 bytes; its fraction is an obligation of the averaging slices. Everything else follows from the
event: off it the union is good, and a capacity of a good union has one head-tail.

* **Key values** (`KeyHeld`, `KeyPort`): every template port programs a `k`, `k'` cell with the
  public key's value, so the hardwired `k`, `k'` cells always hold them, and a `k`, `k'` port is
  either fresh (its flips are `kFlip`) or reprograms its own value (no flip: ProgView's
  `progSafe_programK`).
* **Sponge facts** (`absorbTail_take`, `rnAgree_of_absorbTail`, `mem_spongeReads_rn`,
  `kReads_held`): an absorption with the honest tail under keys `(h', k, k')` agrees with `h` at
  every capacity but the last, so its reads are at the honest cells.
* **Slots of prefixes** (`slotOf_take_honTail`, `tgt_take_honTail`): under `NoHmsgHead` a proper
  prefix of a structural honest tail lies in its slot or in a slot without targets (`PRF_msg`, the
  key expansion), so it has no Struct, Enc or coverage target.
* **Reprogrammed `h` cells keep the exemptions** (`exS_subset_setH`): a held path reading the cell
  reads it at the round whose prefix heads to the cell; in a good union that prefix is the port's
  tail, so the port is the same round of the same slot (`progSafe_slotH`), or no `H_msg` call
  (`progSafe_hmsgH`).
* **The `h` port of round `j` of a structural slot** (`progSafe_slotH`): its tail is the first
  `j + 1` blocks of the honest tail (`isHeadTail_slot_round`); at an earlier round it has no target,
  at the final round the slot is exempted once programmed (GameTCalls' `mem_exS_progUpdate_final`,
  with `FinalSep` from the good union: `finalSep_of_good`).
* **The `h` port of an `H_msg` call** (`progSafe_hmsgH`): its tail is the call's honest tail, which
  has no Struct or Enc target, and its pair is exempted from coverage once the cell is programmed
  (Events' `mem_covEx_programH`): coverage is static, so honest `H_msg` tails flip nothing.
* **The run** (`SafeOk`, `batchOk_slot`, `batchOk_hmsg`, `forallQueries_keySafe_of_hb`): GameTCalls'
  batch order (`HB`, `hb_gameT`, `hb_prefixT`) with the condition `SafeOk`, and the key values kept
  along the run.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message Randomizer)
open Quantum.Xmss (X Z blocks)
open Quantum.Xmss.Hybrid (LazyProg restrictTo progUpdate ReadMono uavg uavg_mono)
open Quantum.Xmss.Assembly (recHwSpec realizeT runtimeR RevealVals memLab rnSt rnK rnR rnZ
  RnAgree rnK_congr rnR_congr rnZ_congr exists_round_of_mem_spongeReads
  roundReads_subset_spongeReads)

namespace Quantum.Sphincs.Assembly

/- Membership in the concrete FORS opening's sets is otherwise decided by evaluating them. -/
attribute [local irreducible] forsNeed forsSlots

/-! ## Key values -/

section keys

variable {X₁ Z₁ : Type} [DecidableEq X₁] [DecidableEq Z₁]

/-- `W`'s hardwired `k`, `k'` cells hold the values of the keys `k`, `k'`. -/
def KeyHeldBy (k k' : X₁ → Z₁) (W : Hw X₁ Z₁) : Prop :=
  (∀ x a, W.2.1 x = some a → a = k x) ∧ ∀ x a, W.2.2 x = some a → a = k' x

/-- A program port programs a `k` or `k'` cell with the key's value. -/
def KeyPortBy (k k' : X₁ → Z₁) : HwProg X₁ Z₁ → Prop
  | .programH _ _ => True
  | .programK x a => a = k x
  | .programK' x a => a = k' x

theorem keyHeldBy_progUpdate {k k' : X₁ → Z₁} {W : Hw X₁ Z₁} (hW : KeyHeldBy k k' W)
    {c : HwProg X₁ Z₁} (hc : KeyPortBy k k' c) : KeyHeldBy k k' (progUpdate c W) := by
  cases c with
  | programH z a => exact hW
  | programK x a =>
    refine ⟨fun x' u hu ↦ ?_, hW.2⟩
    have hu' : Function.update W.2.1 x (some a) x' = some u := hu
    by_cases hx : x' = x
    · subst hx
      rw [Function.update_self, Option.some_inj] at hu'
      rw [← hu']
      exact hc
    · rw [Function.update_of_ne hx] at hu'
      exact hW.1 x' u hu'
  | programK' x a =>
    refine ⟨hW.1, fun x' u hu ↦ ?_⟩
    have hu' : Function.update W.2.2 x (some a) x' = some u := hu
    by_cases hx : x' = x
    · subst hx
      rw [Function.update_self, Option.some_inj] at hu'
      rw [← hu']
      exact hc
    · rw [Function.update_of_ne hx] at hu'
      exact hW.2 x' u hu'

omit [DecidableEq X₁] [DecidableEq Z₁] in
/-- No hardwired cell, no key value to hold. -/
theorem keyHeldBy_hwEmpty (k k' : X₁ → Z₁) : KeyHeldBy k k' (hwEmpty X₁ Z₁) := by
  refine ⟨fun x a h ↦ ?_, fun x a h ↦ ?_⟩
  · rw [show (hwEmpty X₁ Z₁).2.1 x = none from rfl] at h
    cases h
  · rw [show (hwEmpty X₁ Z₁).2.2 x = none from rfl] at h
    cases h

/-- `W`'s hardwired `k`, `k'` cells hold the public keys' values. -/
def KeyHeld (pub : Pub) (W : Hw X Z) : Prop :=
  KeyHeldBy pub.keys.2.1 pub.keys.2.2 W

/-- A program port programs a `k` or `k'` cell with the public key's value. -/
def KeyPort (pub : Pub) (c : HwProg X Z) : Prop :=
  KeyPortBy pub.keys.2.1 pub.keys.2.2 c

theorem keyHeld_progUpdate {pub : Pub} {W : Hw X Z} (hW : KeyHeld pub W) {c : HwProg X Z}
    (hc : KeyPort pub c) : KeyHeld pub (progUpdate c W) :=
  keyHeldBy_progUpdate hW hc

theorem keyHeld_hwEmpty (pub : Pub) : KeyHeld pub (hwEmpty X Z) :=
  keyHeldBy_hwEmpty _ _

end keys

/-! ## Sponge facts -/

section sponge

/-- **The tail of a prefix is the prefix of the tail** (leanXMSS's ProgSafe). -/
theorem absorbTail_take (φ : Equiv.Perm (X × Z)) (m : List X) (n : ℕ) :
    absorbTail φ (m.take n) = (absorbTail φ m).take n := by
  induction m using List.reverseRecOn with
  | nil => simp
  | append_singleton m b ih =>
    rw [absorbTail_append_singleton]
    by_cases hn : n ≤ m.length
    · rw [List.take_append_of_le_length hn, ih,
        List.take_append_of_le_length (by rw [length_absorbTail]; exact hn)]
    · have h1 : (m ++ [b]).length ≤ n := by
        rw [List.length_append, List.length_singleton]
        omega
      have h2 : (absorbTail φ m ++ [(absorb φ m).1 + b]).length ≤ n := by
        rw [List.length_append, List.length_singleton, length_absorbTail]
        omega
      rw [List.take_of_length_le h1, List.take_of_length_le h2, absorbTail_append_singleton]

variable (π : Equiv.Perm (X × Z))

/-- **An absorption with the same tail under `h'` agrees with `h` at every capacity but the
last**: the rate after round `j` is the next block's entry minus the block. -/
theorem rnAgree_of_absorbTail (h h' : Z → X) (k k' : X → Z) {msg : List X}
    (ht : absorbTail (spongePerm (h', k, k') π) msg = absorbTail (spongePerm (h, k, k') π) msg) :
    ∀ j, j + 1 ≤ msg.length → RnAgree π h k k' h' k k' (fun i ↦ msg.getD i 0) j
  | 0, _ => fun i hi ↦ absurd hi (Nat.not_lt_zero i)
  | j + 1, hj => by
    have hA := rnAgree_of_absorbTail h h' k k' ht j (by omega)
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hA i hi
    · refine ⟨rfl, rfl, ?_⟩
      have hm : msg.take (i + 1 + 1) = msg.take (i + 1) ++ [msg.getD (i + 1) 0] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
          List.getD_eq_getElem _ _ (by omega)]
      have e1 := congrArg (List.take (i + 1 + 1)) ht
      rw [← absorbTail_take, ← absorbTail_take, hm, absorbTail_append_singleton,
        absorbTail_append_singleton] at e1
      have e2 := add_right_cancel (List.singleton_injective (List.append_inj' e1 rfl).2)
      rw [absorb_take_eq_rnSt π h' k k' msg (i + 1) (by omega),
        absorb_take_eq_rnSt π h k k' msg (i + 1) (by omega)] at e2
      have e3 : rnR π h' k k' (fun i ↦ msg.getD i 0) i +
            h' (rnZ π h' k k' (fun i ↦ msg.getD i 0) i) =
          rnR π h k k' (fun i ↦ msg.getD i 0) i + h (rnZ π h k k' (fun i ↦ msg.getD i 0) i) :=
        e2
      rw [rnR_congr hA rfl, rnZ_congr hA rfl rfl] at e3
      exact add_left_cancel e3

variable {π}

/-- **The reads of an absorption with the honest tail are at the honest cells**: the `k`, `k'`
reads with the key values, the `h` reads with the `h'` values. -/
theorem mem_spongeReads_rn {h h' : Z → X} {k k' : X → Z} {msg : List X}
    (ht : absorbTail (spongePerm (h', k, k') π) msg = absorbTail (spongePerm (h, k, k') π) msg)
    {e : SpongeRead X Z} (he : e ∈ spongeReads π h' k k' msg) :
    ∃ j < msg.length,
      e = .k (rnK π h k k' (fun i ↦ msg.getD i 0) j)
          (k (rnK π h k k' (fun i ↦ msg.getD i 0) j)) ∨
        e = .k' (rnR π h k k' (fun i ↦ msg.getD i 0) j)
          (k' (rnR π h k k' (fun i ↦ msg.getD i 0) j)) ∨
        e = .h (rnZ π h k k' (fun i ↦ msg.getD i 0) j)
          (h' (rnZ π h k k' (fun i ↦ msg.getD i 0) j)) := by
  obtain ⟨j, hj, hje⟩ := exists_round_of_mem_spongeReads π h' k k' msg he
  rw [absorb_take_eq_rnSt π h' k k' msg j hj.le] at hje
  have hA := rnAgree_of_absorbTail π h h' k k' ht j hj
  have h3 := (congrArg (e ∈ ·) (roundReads_rnSt π h' k k' (fun i ↦ msg.getD i 0) j)).mp hje
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
  refine ⟨j, hj, ?_⟩
  rcases h3 with rfl | rfl | rfl
  · exact .inl (by rw [rnK_congr hA])
  · exact .inr (.inl (by rw [rnR_congr hA rfl]))
  · exact .inr (.inr (by rw [rnZ_congr hA rfl rfl]))

/-- **A database holding the reads of an absorption with the honest tail holds the `k`, `k'` cells
of every round** with the key values. -/
theorem kReads_held {h h' : Z → X} {k k' : X → Z} {msg : List X}
    (ht : absorbTail (spongePerm (h', k, k') π) msg = absorbTail (spongePerm (h, k, k') π) msg)
    {U : Dbs X Z} (hU : ∀ e ∈ spongeReads π h' k k' msg, e.HeldBy U) {j : ℕ}
    (hj : j < msg.length) :
    U.k (rnK π h k k' (fun i ↦ msg.getD i 0) j) =
        some (k (rnK π h k k' (fun i ↦ msg.getD i 0) j)) ∧
      U.k' (rnR π h k k' (fun i ↦ msg.getD i 0) j) =
        some (k' (rnR π h k k' (fun i ↦ msg.getD i 0) j)) := by
  have hA := rnAgree_of_absorbTail π h h' k k' ht j hj
  have hs := roundReads_subset_spongeReads π h' k k' msg hj
  rw [absorb_take_eq_rnSt π h' k k' msg j hj.le] at hs
  have h1 := hU _ (hs _ List.mem_cons_self)
  have h2 := hU _ (hs _ (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [← rnK_congr hA, ← rnR_congr hA rfl]
  exact ⟨h1, h2⟩

/-- **Setting an `h` cell keeps a held read** unless the read is at the cell with another value. -/
theorem heldBy_setH {X₁ Z₁ : Type} [DecidableEq Z₁] {W : Hw X₁ Z₁} {z : Z₁} {a : X₁}
    {e : SpongeRead X₁ Z₁} (he : e.HeldBy W.toDbs) (ha : ∀ w, e = .h z w → w = a) :
    e.HeldBy (DbReg.toDbs (Function.update W.1 z (some a), W.2)) := by
  cases e with
  | h z' w =>
    by_cases hz : z' = z
    · subst hz
      rw [ha w rfl]
      exact Function.update_self z' (some a) W.1
    · exact (Function.update_of_ne hz (some a) W.1).trans he
  | k x u => exact he
  | k' x u => exact he

end sponge

/-! ## Structural honest tails and their prefixes -/

section slots

variable (pub : Pub) (v : (s : HPos) → XD s)

theorem length_honTail (s : Slot) : ((evData pub v).honTail s).length = nBlk pub.seed s := by
  rw [EvData.honTail, length_absorbTail]
  exact length_blocks_slotInput pub.seed s (valsOf v)

/-- **No structural honest tail starts with an `H_msg` block**: the one-block prefix of the honest
tail of a multi-block structural slot is no `H_msg` tail. A property of good data. -/
def NoHmsgHead : Prop :=
  ∀ s, InTable s → 1 < nBlk pub.seed s → ∀ R M c,
    slotOf (evData pub v).pk (((evData pub v).honTail s).take 1) ≠ some (.hmsg R M c)

/-- `hmsgSlot` names only `H_msg` slots. -/
theorem hmsgSlot_eq_some {pk : PublicKey} {x : X} {s₁ : Slot} (h : hmsgSlot pk x = some s₁) :
    ∃ R M c, s₁ = .hmsg R M c := by
  unfold hmsgSlot at h
  split_ifs at h
  obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨_, _, c, rfl⟩

variable {pub v}

/-- **The slot of a proper prefix of a structural honest tail** is the slot itself, or (a one-block
prefix) a slot that is neither structural, an encoding slot, nor an `H_msg` call. -/
theorem slotOf_take_honTail (hnh : NoHmsgHead pub v) {s : Slot} (hs : InTable s) {k : ℕ}
    (hk0 : 0 < k) (hkn : k < nBlk pub.seed s) {s₁ : Slot}
    (h : slotOf (evData pub v).pk (((evData pub v).honTail s).take k) = some s₁) :
    s₁ = s ∨ (¬InTable s₁ ∧ (∀ l τ e, s₁ ≠ .enc l τ e) ∧ ∀ R M c, s₁ ≠ .hmsg R M c) := by
  have hl := length_honTail pub v s
  have hsl := (evData pub v).slotOf_honTail hs
  rcases hT : (evData pub v).honTail s with _ | ⟨x₀, _ | ⟨x₁, rest⟩⟩
  · rw [hT, List.length_nil] at hl
    omega
  · rw [hT, List.length_singleton] at hl
    omega
  rw [hT] at hsl h
  have hb : slotOfBlock (evData pub v).pk x₀ = some s := hsl
  rcases Nat.lt_or_ge 1 k with hk1 | hk1
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have h' : slotOfBlock (evData pub v).pk x₀ = some s₁ := h
    exact .inl (Option.some_injective _ (h'.symm.trans hb))
  · obtain rfl : k = 1 := by omega
    have hn := hnh s hs (by omega)
    rw [hT] at hn
    have h' : slotOfOneBlock (evData pub v).pk x₀ = some s₁ := h
    unfold slotOfOneBlock at h'
    split_ifs at h'
    · obtain ⟨R, M, c, rfl⟩ := hmsgSlot_eq_some h'
      exact absurd h (hn R M c)
    · obtain rfl := Option.some_injective _ h'
      exact .inr ⟨fun h ↦ h, fun _ _ _ h ↦ Slot.noConfusion h, fun _ _ _ h ↦ Slot.noConfusion h⟩
    · obtain rfl := Option.some_injective _ h'
      exact .inr ⟨fun h ↦ h, fun _ _ _ h ↦ Slot.noConfusion h, fun _ _ _ h ↦ Slot.noConfusion h⟩
    · exact .inl (Option.some_injective _ (h'.symm.trans hb))

/-- **A proper prefix of a structural honest tail has no target**: no Struct target (its slot's
honest tail is longer, or its slot is not structural), no Enc target, no coverage target. -/
theorem tgt_take_honTail (hnh : NoHmsgHead pub v) {s : Slot} (hs : InTable s) {k : ℕ}
    (hk0 : 0 < k) (hkn : k < nBlk pub.seed s) (Ex : Set Slot) (sel : Selections)
    (Ex' : Set (Randomizer × Message)) :
    (evData pub v).sphTgt Ex sel (((evData pub v).honTail s).take k) = none ∧
      covTgt (evData pub v).pk Ex' (((evData pub v).honTail s).take k) = none := by
  have hlen : ((evData pub v).honTail s).length ≠
      (((evData pub v).honTail s).take k).length := by
    rw [List.length_take, length_honTail]
    omega
  rcases hsl : slotOf (evData pub v).pk (((evData pub v).honTail s).take k) with _ | s₁
  · refine ⟨sphTgt_eq_none fun s₁ h ↦ ?_, covTgt_eq_none fun R M h ↦ ?_⟩
    · rw [hsl] at h
      cases h
    · rw [hsl] at h
      cases h
  rcases slotOf_take_honTail hnh hs hk0 hkn hsl with rfl | ⟨hT, he, hh⟩
  · exact ⟨sphTgt_short hsl hs hlen, covTgt_of_slot hsl fun R M h ↦ by subst h; exact hs⟩
  · exact ⟨sphTgt_of_slot hsl hT he, covTgt_of_slot hsl fun R M h ↦ hh R M 0 h⟩

variable (pub v)

/-- **Round `j` of a structural slot's honest path is a head-tail**: with the `k`, `k'` cells of
rounds `0, …, j` held with their key values, the first `j + 1` blocks of the honest tail head to
the round's `h`-cell. -/
theorem isHeadTail_slot_round (s : Slot) {j : ℕ} (hj : j < nBlk pub.seed s) {U : Dbs X Z}
    (hU : ∀ i ≤ j, U.k (cellK pub (slotBlk pub.seed s (valsOf v)) i).1 =
        some (cellK pub (slotBlk pub.seed s (valsOf v)) i).2 ∧
      U.k' (cellK' pub (slotBlk pub.seed s (valsOf v)) i).1 =
        some (cellK' pub (slotBlk pub.seed s (valsOf v)) i).2) :
    IsHeadTail pub.perm U (((evData pub v).honTail s).take (j + 1))
      (rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 (slotBlk pub.seed s (valsOf v)) j)
      (rnR pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 (slotBlk pub.seed s (valsOf v)) j) := by
  have h := isHeadTail_take_succ_rn pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2
    (msg := blocks (slotInput pub.seed s (valsOf v))) (j := j)
    (by rw [length_blocks_slotInput]; exact hj) hU
  rw [absorbTail_take] at h
  exact h

/-- **A good union separates the final cell** (`FinalSep`): with the `k`, `k'` cells of every
round hardwired, the final `h`-cell and an earlier one would be heads of two tails of different
lengths. -/
theorem finalSep_of_good {s : Slot} {D : DbReg X Z} {W : Hw X Z}
    (hG : Good pub.perm (union W D))
    (hK : ∀ i < nBlk pub.seed s, W.toDbs.k (cellK pub (slotBlk pub.seed s (valsOf v)) i).1 =
        some (cellK pub (slotBlk pub.seed s (valsOf v)) i).2 ∧
      W.toDbs.k' (cellK' pub (slotBlk pub.seed s (valsOf v)) i).1 =
        some (cellK' pub (slotBlk pub.seed s (valsOf v)) i).2) :
    FinalSep pub v s := by
  intro j hj heq
  have hn := nBlk_pos pub.seed s
  have hE := (EvData.extendsAll_union_hw W D).1
  have h1 := (isHeadTail_slot_round pub v s (j := j) (by omega)
    fun i _ ↦ hK i (by omega)).mono hE
  have h2 := (isHeadTail_slot_round pub v s (j := nBlk pub.seed s - 1) (by omega)
    fun i _ ↦ hK i (by omega)).mono hE
  rw [heq] at h1
  have e := congrArg List.length (hG.isHeadTail_unique h1 h2).1
  rw [List.length_take, List.length_take, length_honTail] at e
  omega

/-- **A reprogrammed `h` cell keeps the exempted structural slots.** Let the cell `z` be the head of
the tail `t₀` in the hardwired cells, in a good union. An exempted slot whose held path reads `z`
reads it at a round whose first blocks head to `z`, so they are `t₀`. If, whenever the first
`j + 1` blocks of an in-table slot's honest tail are `t₀`, the new value is the public one at an
earlier round and the slot is exempted after the program at its final round, every exempted slot
stays exempted. -/
theorem exS_subset_setH {D : DbReg X Z} {W : Hw X Z} (hG : Good pub.perm (union W D)) {z : Z}
    {t₀ : List X} {xi₀ : X} (h₀ : IsHeadTail pub.perm W.toDbs t₀ z xi₀) (a : X)
    (hval : ∀ s', InTable s' → ∀ j < nBlk pub.seed s',
      ((evData pub v).honTail s').take (j + 1) = t₀ →
        (j + 1 < nBlk pub.seed s' → a = pub.keys.1 z) ∧
          (j + 1 = nBlk pub.seed s' →
            s' ∈ (evData pub v).exS (Function.update W.1 z (some a), W.2))) :
    (evData pub v).exS W ⊆ (evData pub v).exS (Function.update W.1 z (some a), W.2) := by
  rintro s' ⟨hT, h', hr, ht, ho⟩
  have hr' : ∀ e ∈ spongeReads pub.perm h' pub.keys.2.1 pub.keys.2.2
      (blocks (slotInput pub.seed s' (valsOf v))), e.HeldBy W.toDbs := hr
  have ht' : absorbTail (spongePerm (h', pub.keys.2.1, pub.keys.2.2) pub.perm)
      (blocks (slotInput pub.seed s' (valsOf v))) =
        absorbTail (spongePerm (pub.keys.1, pub.keys.2.1, pub.keys.2.2) pub.perm)
          (blocks (slotInput pub.seed s' (valsOf v))) := ht
  have hlen := length_blocks_slotInput pub.seed s' (valsOf v)
  have hE := (EvData.extendsAll_union_hw W D).1
  by_cases hz : ∃ w, SpongeRead.h z w ∈ spongeReads pub.perm h' pub.keys.2.1 pub.keys.2.2
      (blocks (slotInput pub.seed s' (valsOf v)))
  · obtain ⟨w, hw⟩ := hz
    obtain ⟨j, hj, he⟩ := mem_spongeReads_rn ht' hw
    rcases he with he | he | he
    · cases he
    · cases he
    injection he with hzj
    subst hzj
    have h1 := isHeadTail_take_succ_rn pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2
      (msg := blocks (slotInput pub.seed s' (valsOf v))) (j := j) hj
      fun i hi ↦ kReads_held ht' hr' (by omega)
    rw [absorbTail_take] at h1
    have heq := (hG.isHeadTail_unique (h1.mono hE) (h₀.mono hE)).1
    rw [hlen] at hj
    obtain ⟨hv1, hv2⟩ := hval s' hT j hj heq
    rcases Nat.lt_or_ge (j + 1) (nBlk pub.seed s') with hlt | hge
    · have hz1 := (rnAgree_of_absorbTail pub.perm pub.keys.1 h' pub.keys.2.1 pub.keys.2.2 ht'
        (j + 1) (by omega) j (Nat.lt_succ_self j)).2.2
      refine ⟨hT, h', fun e he' ↦ heldBy_setH (hr' e he') fun w₁ hw₁ ↦ ?_, ht, ho⟩
      subst hw₁
      obtain ⟨j₁, -, he₁⟩ := mem_spongeReads_rn ht' he'
      rcases he₁ with he₁ | he₁ | he₁
      · cases he₁
      · cases he₁
      injection he₁ with hz₁ hw₁
      rw [hw₁, ← hz₁, hz1]
      exact (hv1 hlt).symm
    · exact hv2 (by omega)
  · refine ⟨hT, h', fun e he' ↦ heldBy_setH (hr' e he') fun w₁ hw₁ ↦ ?_, ht, ho⟩
    subst hw₁
    exact absurd ⟨w₁, he'⟩ hz

end slots

/-! ## The `h` ports of the game -/

section ports

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- **The `h` port of round `j` of a structural slot is safe** at a state holding the earlier
rounds and the round's `k`, `k'` cells with their programmed values. -/
theorem progSafe_slotH (N : ℕ) (hnh : NoHmsgHead pub v) {s : Slot} (hs : InTable s) {j : ℕ}
    (hj : j < nBlk pub.seed s) {r : HwReg X Z (Mem HPos)}
    (hR : ∀ i < j, RoundHeld pub r.2.1.toDbs (slotBlk pub.seed s (valsOf v))
      (nBlk pub.seed s - 1) (cor128 (valsOf v (slotOutPos s))) i)
    (hk : r.2.1.toDbs.k (cellK pub (slotBlk pub.seed s (valsOf v)) j).1 =
      some (cellK pub (slotBlk pub.seed s (valsOf v)) j).2)
    (hk' : r.2.1.toDbs.k' (cellK' pub (slotBlk pub.seed s (valsOf v)) j).1 =
      some (cellK' pub (slotBlk pub.seed s (valsOf v)) j).2) :
    ProgSafe (Bad (evData pub v) N) (rH pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1)
      (cor128 (valsOf v (slotOutPos s))) j) r := by
  intro hsB hp
  exfalso
  have hK : ∀ i ≤ j, r.2.1.toDbs.k (cellK pub (slotBlk pub.seed s (valsOf v)) i).1 =
        some (cellK pub (slotBlk pub.seed s (valsOf v)) i).2 ∧
      r.2.1.toDbs.k' (cellK' pub (slotBlk pub.seed s (valsOf v)) i).1 =
        some (cellK' pub (slotBlk pub.seed s (valsOf v)) i).2 := fun i hi ↦ by
    rcases hi.lt_or_eq with hi | rfl
    · exact ⟨(hR i hi).1, (hR i hi).2.1⟩
    · exact ⟨hk, hk'⟩
  have h₀ : IsHeadTail pub.perm r.2.1.toDbs (((evData pub v).honTail s).take (j + 1))
      (cellH pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1)
        (cor128 (valsOf v (slotOutPos s))) j).1
      (rnR pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 (slotBlk pub.seed s (valsOf v)) j) := by
    rw [cellH_fst]
    exact isHeadTail_slot_round pub v s hj hK
  have hE := (EvData.extendsAll_union_hw r.2.1 r.1).1
  have hlen := length_honTail pub v s
  have hfin : Good pub.perm (union r.2.1 r.1) → j + 1 = nBlk pub.seed s →
      s ∈ (evData pub v).exS (Function.update r.2.1.1
        (cellH pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1)
          (cor128 (valsOf v (slotOutPos s))) j).1
        (some (cellH pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1)
          (cor128 (valsOf v (slotOutPos s))) j).2), r.2.1.2) := by
    intro hG hjn
    obtain rfl : j = nBlk pub.seed s - 1 := by omega
    exact mem_exS_progUpdate_final pub v hs hR hk hk'
      (finalSep_of_good pub v hG fun i hi ↦ hK i (by omega))
  refine not_mem_bad_setH (D := r.1) (W := r.2.1) (m := r.2.2) hsB
    (cellH pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1)
      (cor128 (valsOf v (slotOutPos s))) j).1
    (cellH pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1)
      (cor128 (valsOf v (slotOutPos s))) j).2 (fun hG ↦ ?_) (fun hG t xi hi ↦ ?_) hp
  · by_cases hz : r.2.1.1 (cellH pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s - 1)
        (cor128 (valsOf v (slotOutPos s))) j).1 = none
    · exact EvData.exS_mono (hwLe_programH hz _)
    refine exS_subset_setH pub v hG h₀ _ fun s' hT j' hj' heq ↦ ?_
    have e := congrArg List.length heq
    rw [List.length_take, List.length_take, length_honTail pub v s', hlen] at e
    obtain rfl : j = j' := by omega
    refine ⟨fun hlt ↦ ?_, fun hn' ↦ ?_⟩
    · by_cases hjn : j + 1 < nBlk pub.seed s
      · rw [cellH_snd, ite_eq_right (by omega), cellH_fst]
      · exfalso
        have hsl := (evData pub v).slotOf_honTail hs
        rw [← List.take_of_length_le (show ((evData pub v).honTail s).length ≤ j + 1 by omega),
          ← heq] at hsl
        rcases slotOf_take_honTail hnh hT (Nat.succ_pos j) hlt hsl with he | ⟨hT', -⟩
        · subst he
          omega
        · exact hT' hs
    · by_cases hjn : j + 1 < nBlk pub.seed s
      · exfalso
        have hl' := length_honTail pub v s'
        have hsl := (evData pub v).slotOf_honTail hT
        rw [← List.take_of_length_le (show ((evData pub v).honTail s').length ≤ j + 1 by omega),
          heq] at hsl
        rcases slotOf_take_honTail hnh hs (Nat.succ_pos j) hjn hsl with he | ⟨hT', -⟩
        · subst he
          omega
        · exact hT' hT
      · have hl' := length_honTail pub v s'
        have h1 : (evData pub v).honTail s' = (evData pub v).honTail s := by
          rw [← List.take_of_length_le (show ((evData pub v).honTail s').length ≤ j + 1 by omega),
            heq, List.take_of_length_le (by omega)]
        have hsl := (evData pub v).slotOf_honTail hT
        rw [h1, (evData pub v).slotOf_honTail hs] at hsl
        obtain rfl := Option.some_injective _ hsl
        exact hfin hG (by omega)
  · obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi (h₀.mono hE)
    by_cases hjn : j + 1 < nBlk pub.seed s
    · exact tgt_take_honTail hnh hs (Nat.succ_pos j) hjn _ _ _
    · rw [List.take_of_length_le (by omega)]
      exact ⟨sphTgt_honTail hs (hfin hG (by omega)), covTgt_honTail hs⟩

/-- **No structural honest tail's first blocks are an `H_msg` call's tail.** -/
theorem take_honTail_ne_hmsg (hnh : NoHmsgHead pub v) {s : Slot} (hs : InTable s) {j : ℕ}
    (hj : j < nBlk pub.seed s) (R : Randomizer) (msg : Message) (i : DigestCall) :
    ((evData pub v).honTail s).take (j + 1) ≠ (evData pub v).honTail (.hmsg R msg i) := by
  intro heq
  have hl1 : ((evData pub v).honTail (.hmsg R msg i)).length = 1 := by
    rw [EvData.honTail, length_absorbTail]
    exact length_blocks_hmsg pub.seed R msg i (valsOf v)
  have hl := length_honTail pub v s
  have e := congrArg List.length heq
  rw [List.length_take, hl, hl1] at e
  have hslot := (evData pub v).slotOf_honTail_hmsg R msg i
  rw [← heq] at hslot
  obtain rfl : j = 0 := by omega
  rcases Nat.lt_or_ge 1 (nBlk pub.seed s) with h1 | h1
  · exact hnh s hs h1 R msg i hslot
  · rw [List.take_of_length_le (by omega), (evData pub v).slotOf_honTail hs] at hslot
    obtain rfl := Option.some_injective _ hslot
    exact hs

/-- **The `h` port of an `H_msg` call is safe** at a state holding the round's `k`, `k'` cells
with their key values, for every randomizer and output. -/
theorem progSafe_hmsgH (N : ℕ) (hnh : NoHmsgHead pub v) (R : Randomizer) (msg : Message)
    (i : DigestCall) (y : HashOutput) {r : HwReg X Z (Mem HPos)}
    (hk : r.2.1.toDbs.k (cellK pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0).1 =
      some (cellK pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0).2)
    (hk' : r.2.1.toDbs.k' (cellK' pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0).1 =
      some (cellK' pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0).2) :
    ProgSafe (Bad (evData pub v) N)
      (rH pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0 (cor256 y) 0) r := by
  intro hsB hp
  exfalso
  have h₀ := isHeadTail_hmsg pub v R msg i (cor256 y) hk hk'
  have hE := (EvData.extendsAll_union_hw r.2.1 r.1).1
  refine not_mem_bad_setH (D := r.1) (W := r.2.1) (m := r.2.2) hsB
    (cellH pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0 (cor256 y) 0).1
    (cellH pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0 (cor256 y) 0).2
    (fun hG ↦ ?_) (fun hG t xi hi ↦ ?_) hp
  · by_cases hz : r.2.1.1 (cellH pub (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) 0
        (cor256 y) 0).1 = none
    · exact EvData.exS_mono (hwLe_programH hz _)
    exact exS_subset_setH pub v hG h₀ _ fun s' hT j hj heq ↦
      absurd heq (take_honTail_ne_hmsg pub v hnh hT hj R msg i)
  · obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi (h₀.mono hE)
    exact ⟨sphTgt_hmsg ((evData pub v).slotOf_honTail_hmsg R msg i),
      covTgt_honTail_hmsg fun hi0 ↦ by
        subst hi0
        exact EvData.mem_covEx_programH h₀ _⟩

end ports

/-! ## The batches of the game -/

section batch

variable {M : Type} [Fintype M] [DecidableEq M]

/-- **The condition on program calls**: the port programs key values, and it is safe for the
event `B` at the states holding key values. -/
def SafeOk (B : Set (HwReg X Z (Finset HPos × M))) (pub : Pub) (c : HwProg X Z)
    (r : HwReg X Z (Finset HPos × M)) : Prop :=
  KeyPort pub c ∧ (KeyHeld pub r.2.1 → ProgSafe B c r)

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- **The ports of an in-table structural slot satisfy `SafeOk`** in batch order. -/
theorem batchOk_slot (N : ℕ) (hnh : NoHmsgHead pub v) {s : Slot} (hs : InTable s) :
    BatchOk pub (SafeOk (Bad (evData pub v) N) pub) (slotBlk pub.seed s (valsOf v))
      (cor128 (valsOf v (slotOutPos s))) (nBlk pub.seed s) := by
  intro j hj r hR
  refine ⟨⟨rfl, fun hK ↦ progSafe_programK fun u hu ↦ hK.1 _ u hu⟩, fun hk ↦
    ⟨⟨rfl, fun hK ↦ progSafe_programK' fun u hu ↦ hK.2 _ u hu⟩, fun hk' ↦
      ⟨trivial, fun _ ↦ progSafe_slotH pub v N hnh hs hj hR hk hk'⟩⟩⟩

/-- **The ports of an `H_msg` call satisfy `SafeOk`**, for every randomizer and output. -/
theorem batchOk_hmsg (N : ℕ) (hnh : NoHmsgHead pub v) (R : Randomizer) (msg : Message)
    (i : DigestCall) (y : HashOutput) :
    BatchOk pub (SafeOk (Bad (evData pub v) N) pub)
      (slotBlk pub.seed (.hmsg R msg i) (valsOf v)) (cor256 y) 1 := by
  intro j hj r _
  obtain rfl : j = 0 := by omega
  refine ⟨⟨rfl, fun hK ↦ progSafe_programK fun u hu ↦ hK.1 _ u hu⟩, fun hk ↦
    ⟨⟨rfl, fun hK ↦ progSafe_programK' fun u hu ↦ hK.2 _ u hu⟩, fun hk' ↦
      ⟨trivial, fun _ ↦ progSafe_hmsgH pub v N hnh R msg i y hk hk'⟩⟩⟩

end batch

/-! ## The run -/

section run

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

omit [Fintype M] [DecidableEq M] in
/-- **The challenge prefix's program ports satisfy `ok` in batch order** (GameTCalls' `hb_gameT`
without the verification). -/
theorem hb_prefixT (ok : HwProg X Z → HwReg X Z (Finset HPos × M) → Prop)
    (v : (s : HPos) → XD s) (pub : Pub)
    (hslot : ∀ s, InTable s → BatchOk pub ok (slotBlk pub.seed s (valsOf v))
      (cor128 (valsOf v (slotOutPos s))) (nBlk pub.seed s))
    (hmsg : ∀ R msg i y, BatchOk pub ok (slotBlk pub.seed (.hmsg R msg i) (valsOf v))
      (cor256 y) 1)
    (upd : TrialUpd M) (pol : DigestPolicy) (A : SAdversary) :
    HB ok v (prefixT M upd pol pub A) ∅ ∅ :=
  hb_revealThen ok v _ _ fun _ ↦
    hb₂_bind ok v _ _ (hb_substitute ok v _ (hb_challengeT ok v pub hslot
      (by intros; exact hmsg _ _ _ _) upd pol) _)
      fun _ ↦ subset_rfl

variable (B : Set (HwReg X Z (Finset HPos × M))) (pub : Pub)

/-- The register states holding key values and the cells of `C` with their values. -/
def KeyAll (C : Set (HwProg X Z)) (s : HwReg X Z (Finset HPos × M)) : Prop :=
  KeyHeld pub s.2.1 ∧ AllHeld C s.2.1

/-- **The presented states hold key values, and a called program port is safe there.** -/
def keySafeSupp (m₀ : Finset HPos × M) (i : (recHwSpec X Z HPos M).Port) (E : QReg)
    (σ : Matrix (((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D) × E)
      (((recHwSpec X Z HPos M).In i × (runtimeR (X := X) (Z := Z) m₀).D) × E) ℂ) : Prop :=
  ∀ a, ¬(KeyHeld pub a.1.2.2.1 ∧ PortSafe B i a.1.2) → σ a a = 0

theorem stepKA_sponge (m₀ : Finset HPos × M) (i : SpongePort) (C : Set (HwProg X Z)) :
    StepR m₀ (.inl (.inl (.inl i))) (KeyAll pub C) (KeyAll pub C) :=
  stepR_sponge m₀ i fun r r' he hr ↦ by
    unfold KeyAll at hr ⊢
    rw [he]
    exact hr

theorem stepKA_read (m₀ : Finset HPos × M)
    (c : {c : HwRead X Z (Finset HPos × M) // ReadMono (memLab X Z HPos M) c})
    (C : Set (HwProg X Z)) : StepR m₀ (.inl (.inl (.inr c.1))) (KeyAll pub C) (KeyAll pub C) :=
  stepR_read m₀ c fun r r' he hr ↦ by
    unfold KeyAll at hr ⊢
    rw [he]
    exact hr

theorem stepKA_prog (m₀ : Finset HPos × M) {c : HwProg X Z} {C : Set (HwProg X Z)}
    (hc : ∀ r : HwReg X Z (Finset HPos × M), KeyAll pub C r → KeyPort pub c) :
    StepR m₀ (.inl (.inr c)) (KeyAll pub C) (KeyAll pub (heldNext c C)) :=
  stepR_prog m₀ c fun r r' he hr ↦ by
    have hk := hc r hr
    unfold KeyAll at hr ⊢
    rw [he]
    exact ⟨keyHeld_progUpdate hr.1 hk, allHeld_progUpdate hr.2 c⟩

theorem stepKA_rec (m₀ : Finset HPos × M) (T : Finset HPos) (C : Set (HwProg X Z)) :
    StepR m₀ (.inr T) (KeyAll pub C) (KeyAll pub C) :=
  stepR_rec m₀ T fun r r' he hr ↦ by
    unfold KeyAll at hr ⊢
    rw [he]
    exact hr

/-- One call of a realized program, from the states `KeyAll pub C` to `KeyAll pub C'`. -/
theorem forallQueries_queryBind_keyAll (m₀ : Finset HPos × M) (I : L.Interp) {A : QReg}
    (i : (recHwSpec X Z HPos M).Port) (E : QReg) (ℓ : A ≃ (recHwSpec X Z HPos M).In i × E)
    (k' : (recHwSpec X Z HPos M).Result i → QuantumComp L (recHwSpec X Z HPos M) Ω
      (QReg.of ((recHwSpec X Z HPos M).Out i × E)))
    {C C' : Set (HwProg X Z)}
    (hpre : ∀ r, KeyAll pub C r → PortSafe B i r)
    (hstep : StepR m₀ i (KeyAll pub C) (KeyAll pub C'))
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of ((recHwSpec X Z HPos M).Out i × E) ×
        (runtimeR m₀).D ↦ m.2) {s | KeyAll pub C' s} ρ' →
      (runtimeR m₀).ForallQueries I (keySafeSupp B pub m₀) (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | KeyAll pub C s} ρ) :
    (runtimeR m₀).ForallQueries I (keySafeSupp B pub m₀) (QuantumComp.queryBind i E ℓ k') ρ :=
  forallQueries_queryBind_of_stepR (Sup := keySafeSupp B pub m₀) (P := KeyAll pub C)
    (P' := KeyAll pub C') m₀ I i E ℓ k'
    (fun _ hρ a ha ↦ relabel_diag_eq_zero_of_supp m₀ E ℓ hρ a fun h ↦ ha ⟨h.1, hpre _ h⟩)
    hstep hk ρ hρ

/-- **The realized program of a template whose program ports satisfy `SafeOk` in batch order
presents only states holding key values, safe at the program calls.** -/
theorem forallQueries_keySafe_of_hb (m₀ : Finset HPos × M) (I : L.Interp)
    (v : (s : HPos) → XD s) {A : QReg} (y : QuantumComp L (SSpec M) Ω A) :
    ∀ C C', HB (SafeOk B pub) v y C C' →
      ∀ ρ : Matrix (A × (runtimeR m₀).D) (A × (runtimeR m₀).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m₀).D ↦ m.2) {s | KeyAll pub C s} ρ →
      (runtimeR m₀).ForallQueries I (keySafeSupp B pub m₀) (realizeT v y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro C C' hy ρ hρ b
    exact ih b C C' (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro C C' hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_keyAll B pub m₀ I (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT v (k r)) (fun _ _ ↦ trivial) (stepKA_sponge pub m₀ i C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_keyAll B pub m₀ I (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT v (k r)) (fun _ _ ↦ trivial) (stepKA_read pub m₀ c C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_keyAll B pub m₀ I
          (.inl (.inr ((LazyProg.programH T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun r hr ↦ (hy.1 r hr.2).2 hr.1)
          (stepKA_prog pub m₀ fun r hr ↦ (hy.1 r hr.2).1)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_keyAll B pub m₀ I
          (.inl (.inr ((LazyProg.programK T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun r hr ↦ (hy.1 r hr.2).2 hr.1)
          (stepKA_prog pub m₀ fun r hr ↦ (hy.1 r hr.2).1)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_keyAll B pub m₀ I
          (.inl (.inr ((LazyProg.programK' T₀ c).realize v))) E ℓ (fun r ↦ realizeT v (k r))
          (fun r hr ↦ (hy.1 r hr.2).2 hr.1)
          (stepKA_prog pub m₀ fun r hr ↦ (hy.1 r hr.2).1)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_keyAll B pub m₀ I (.inr T) E ℓ
        (fun m ↦ realizeT v (k (restrictTo T v, m))) (fun _ _ ↦ trivial) (stepKA_rec pub m₀ T C)
        (fun m ↦ ih (restrictTo T v, m) _ C' (hy.2 (ULift.up (restrictTo T v, m)))) ρ hρ

/-- **The canonical start holds no hardwired cell**, so it holds key values. -/
theorem querySupportedOn_init_keyHeld (m₀ : Finset HPos × M) {A : QReg} (σ : Matrix A A ℂ) :
    QuerySupportedOn (fun a : A × QReg.of (HwReg X Z (Finset HPos × M)) ↦ a.2)
      {s | KeyHeld pub s.2.1} (σ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  intro a b h
  change (σ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
    hwEmpty X Z, m₀) : HwReg X Z (Finset HPos × M))).matrix) a b ≠ 0 at h
  rw [SubState.matrix_basis, kroneckerMap_apply] at h
  have h' := right_ne_zero_of_mul h
  rw [Matrix.single_apply] at h'
  split_ifs at h' with he
  · show KeyHeld pub a.2.2.1 ∧ KeyHeld pub b.2.2.1
    rw [← he.1, ← he.2]
    exact ⟨keyHeld_hwEmpty pub, keyHeld_hwEmpty pub⟩
  · exact absurd rfl h'

end run

/-! ## The game and its prefix -/

section game

variable (N : ℕ) (upd : TrialUpd Selections) (pol : DigestPolicy) (pub : Pub)
  (v : (s : HPos) → XD s) (A : SAdversary) (m₀ : Finset HPos × Selections)
  {ρ : Matrix (QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D)
    (QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D) ℂ}

/-- **Along the realized game, every call is presented safe states** for the event
`Bad (evData pub v) N`, from a start holding key values, for every digest policy. -/
theorem forallQueries_safeSupp_gameT (hnh : NoHmsgHead pub v)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D ↦ a.2)
      {s | KeyHeld pub s.2.1} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (safeSupp (Bad (evData pub v) N) m₀) (realizeT v (gameT Selections upd pol pub A)) ρ :=
  (forallQueries_keySafe_of_hb (Bad (evData pub v) N) pub m₀ _ v _ ∅ ∅
    (hb_gameT (SafeOk (Bad (evData pub v) N) pub) v pub
      (fun _ hs ↦ batchOk_slot pub v N hnh hs)
      (by intros; exact batchOk_hmsg pub v N hnh _ _ _ _) upd pol A) ρ
    (hρ.imp fun _ h ↦ ⟨h, fun c hc ↦ absurd hc (Set.notMem_empty c)⟩)).mono _
    fun _ _ _ h a ha ↦ h a fun hk ↦ ha hk.2

/-- **Along the realized challenge prefix, every call is presented safe states.** -/
theorem forallQueries_safeSupp_prefixT (hnh : NoHmsgHead pub v)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D ↦ a.2)
      {s | KeyHeld pub s.2.1} ρ) :
    (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (safeSupp (Bad (evData pub v) N) m₀) (realizeT v (prefixT Selections upd pol pub A)) ρ :=
  (forallQueries_keySafe_of_hb (Bad (evData pub v) N) pub m₀ _ v _ ∅ ∅
    (hb_prefixT (SafeOk (Bad (evData pub v) N) pub) v pub
      (fun _ hs ↦ batchOk_slot pub v N hnh hs)
      (by intros; exact batchOk_hmsg pub v N hnh _ _ _ _) upd pol A) ρ
    (hρ.imp fun _ h ↦ ⟨h, fun c hc ↦ absurd hc (Set.notMem_empty c)⟩)).mono _
    fun _ _ _ h a ha ↦ h a fun hk ↦ ha hk.2

variable [DecidablePred (· ∈ Bad (S := HPos) (evData pub v) N)]

/-- **The program flips along the game are the fresh `k`, `k'` flips.** -/
theorem progW_le_kW_gameT (hnh : NoHmsgHead pub v) (hρ₀ : ρ.PosSemidef)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D ↦ a.2)
      {s | KeyHeld pub s.2.1} ρ) :
    progW (Bad (evData pub v) N) m₀ (realizeT v (gameT Selections upd pol pub A)) ρ ≤
      kW (Bad (evData pub v) N) m₀ (realizeT v (gameT Selections upd pol pub A)) ρ :=
  progW_le_kW _ m₀ _ hρ₀ (forallQueries_safeSupp_gameT N upd pol pub v A m₀ hnh hρ)

/-- **The program flips along the challenge prefix are the fresh `k`, `k'` flips.** -/
theorem progW_le_kW_prefixT (hnh : NoHmsgHead pub v) (hρ₀ : ρ.PosSemidef)
    (hρ : QuerySupportedOn (fun a : QReg.of Unit × (runtimeR (X := X) (Z := Z) m₀).D ↦ a.2)
      {s | KeyHeld pub s.2.1} ρ) :
    progW (Bad (evData pub v) N) m₀ (realizeT v (prefixT Selections upd pol pub A)) ρ ≤
      kW (Bad (evData pub v) N) m₀ (realizeT v (prefixT Selections upd pol pub A)) ρ :=
  progW_le_kW _ m₀ _ hρ₀ (forallQueries_safeSupp_prefixT N upd pol pub v A m₀ hnh hρ)

end game

/-! ## Averages -/

/-- An average of a guarded quantity bounded pointwise by another on the guard. -/
theorem uavg_ite_le_of_le {P : Type} [Fintype P] (G : P → Prop) [DecidablePred G]
    {f g : P → ℝ≥0∞} (h : ∀ p, G p → f p ≤ g p) {κ : ℝ≥0∞}
    (hk : uavg (fun p ↦ if G p then g p else 0) ≤ κ) :
    uavg (fun p ↦ if G p then f p else 0) ≤ κ := by
  refine (uavg_mono fun p ↦ ?_).trans hk
  by_cases hp : G p
  · rw [ite_eq_left hp, ite_eq_left hp]
    exact h p hp
  · rw [ite_eq_right hp]
    exact zero_le

section avg

variable {P : Type} [Fintype P] (G : P → Prop) [DecidablePred G] (pubP : P → Pub)
  (vP : P → (s : HPos) → XD s) (N : ℕ) (upd : TrialUpd Selections) (pol : DigestPolicy)
  (A : SAdversary) (m₀ : Finset HPos × Selections) (σ : Matrix (QReg.of Unit) (QReg.of Unit) ℂ)
  [∀ p, DecidablePred (· ∈ Bad (S := HPos) (evData (pubP p) (vP p)) N)]

/-- **`progRest` without a bad fraction beyond `NoHmsgHead`**: averaged over data `p` with the
guard `G` (which gives `NoHmsgHead`), the program flips along the game are at most the averaged
fresh `k`, `k'` flips, from the runtime's initial state (no hardwired cell). -/
theorem uavg_progW_le_kW_gameT
    (hρ₀ : (σ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix).PosSemidef)
    (hnh : ∀ p, G p → NoHmsgHead (pubP p) (vP p)) {κ : ℝ≥0∞}
    (hk : uavg (fun p ↦ if G p then kW (Bad (evData (pubP p) (vP p)) N) m₀
      (realizeT (vP p) (gameT Selections upd pol (pubP p) A))
      (σ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ κ) :
    uavg (fun p ↦ if G p then progW (Bad (evData (pubP p) (vP p)) N) m₀
      (realizeT (vP p) (gameT Selections upd pol (pubP p) A))
      (σ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ κ :=
  uavg_ite_le_of_le G (fun p hp ↦ progW_le_kW_gameT N upd pol (pubP p) (vP p) A m₀ (hnh p hp)
    hρ₀ (querySupportedOn_init_keyHeld (pubP p) m₀ σ)) hk

/-- **`progRest` along the challenge prefix**, as `uavg_progW_le_kW_gameT`. -/
theorem uavg_progW_le_kW_prefixT
    (hρ₀ : (σ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix).PosSemidef)
    (hnh : ∀ p, G p → NoHmsgHead (pubP p) (vP p)) {κ : ℝ≥0∞}
    (hk : uavg (fun p ↦ if G p then kW (Bad (evData (pubP p) (vP p)) N) m₀
      (realizeT (vP p) (prefixT Selections upd pol (pubP p) A))
      (σ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ κ) :
    uavg (fun p ↦ if G p then progW (Bad (evData (pubP p) (vP p)) N) m₀
      (realizeT (vP p) (prefixT Selections upd pol (pubP p) A))
      (σ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) else 0) ≤ κ :=
  uavg_ite_le_of_le G (fun p hp ↦ progW_le_kW_prefixT N upd pol (pubP p) (vP p) A m₀ (hnh p hp)
    hρ₀ (querySupportedOn_init_keyHeld (pubP p) m₀ σ)) hk

end avg

end Quantum.Sphincs.Assembly

end
