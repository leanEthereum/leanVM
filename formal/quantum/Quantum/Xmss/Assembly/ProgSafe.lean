module

public import Quantum.Xmss.Assembly.ProgView

@[expose] public section

/-!
# The free `h` program calls of the game are safe

ProgView's remaining `hsafe` piece (1): along the canonical game `gameR A L`, every call of an `h`
program port whose cell is free is presented only states at which the port is safe
(`forallQueries_hFreeSupp_gameR`), for every table `L` (no good-table condition is needed). With
ProgView's `progTot_le_kTot`, the program flips are the fresh `k`, `k'` flips on every table
(`progTot_le_kTot_gameR`, averaged in `uavg_progTot_le_kTot`): `progRest` needs no bad-fraction
term.

* **Sponge facts** (`absorbTail_take`, `heldBy_spongeReads_of_rounds`, `agreesRounds_take_succ`):
  tails of prefixes are prefixes of tails; a database holding every round's reads holds every read;
  holding the `k`, `k'` points of rounds `0, …, j` is `AgreesRounds` of the first `j + 1` blocks.
* **A round of a slot** (`rPortK`, `rPortK'`, `rPortH`, `roundReads_slot`): `slotPorts` is the
  `k`, `k'`, `h` ports round by round; the reads of round `i` of the honest input are the cells of
  those ports with their `L.keys` values. Hardwired cells inside `tableHw L` hold the key values
  (`heldBy_k_of_le`, `heldBy_k'_of_le`, `heldBy_h_of_le`).
* **The `h` port of round `j` is safe** (`progSafe_round`) at a state inside `tableHw L` with the
  slot's cells of rounds `< j` and the `k`, `k'` cells of round `j` hardwired: they give
  `AgreesRounds` for the union and ProgView's `isHeadTail_roundH`. At the final round the slot is
  exempted once the cell is programmed (its honest input is `slotInput (pubOf L) s (valueAt L)`,
  GameT's `slotPayload_eq`, and all its reads are hardwired: `HeldIn`), so
  `progSafe_programH_honest` applies. At an earlier round the tail of the first `j + 1` blocks is a
  proper prefix of the honest tail: its slot is the slot `s` or (a one-block prefix of seed shape)
  `.seed`, neither a message slot, and neither has an honest tail of length `j + 1`
  (`slotOf_cons_take`), so `progSafe_programH_short` applies.
* **The batch order** (`AllHw`, `OkC`, `HB`): `HB L y C C'` says that run from states with the
  realized ports `C` hardwired, every program port of the template `y` is safe (`OkC`) at the
  states inside `tableHw L` with the ports before it hardwired, ending with `C'` hardwired. A
  program port adds its cell, the other ports keep the hardwired cells (`StepC`). Per component
  (GameTCalls' `HP` pattern): `hb_readLift`, `hb_rounds` and `hb_slotPorts` (the ports of a slot in
  `slotPorts` order), `hb_progSlots`, `hb_signLayerT`, `hb_signT`, `hb_challengeT`, `hb_gameT`;
  `forallQueries_of_hb` turns `HB` into `ForallQueries` of `bSupp`, which with ProgView's
  `forallQueries_hwSupp_gameR` gives `hFreeSupp`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

universe u v w w₁

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## Sponge facts -/

section sponge

variable {X₁ Z₁ : Type} [AddCommGroup X₁] [AddCommGroup Z₁]

/-- **The tail of a prefix is the prefix of the tail.** -/
theorem absorbTail_take (φ : Equiv.Perm (X₁ × Z₁)) (m : List X₁) (n : ℕ) :
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

variable (π : Equiv.Perm (X₁ × Z₁)) (h : Z₁ → X₁) (k k' : X₁ → Z₁)

/-- **A database holding every round's reads holds every read.** -/
theorem heldBy_spongeReads_of_rounds {D : Dbs X₁ Z₁} {msg : List X₁}
    (hr : ∀ i < msg.length, ∀ e ∈ roundReads π h k k'
      (absorb (spongePerm (h, k, k') π) (msg.take i)) (msg.getD i 0), e.HeldBy D) :
    ∀ e ∈ spongeReads π h k k' msg, e.HeldBy D := by
  induction msg using List.reverseRecOn with
  | nil =>
    intro e he
    rw [spongeReads_nil] at he
    exact absurd he List.not_mem_nil
  | append_singleton msg b ih =>
    intro e he
    rw [spongeReads_append_singleton, List.mem_append] at he
    rcases he with he | he
    · refine ih (fun i hi e' he' ↦ ?_) e he
      have hi' : i < (msg ++ [b]).length := by
        rw [List.length_append, List.length_singleton]
        omega
      have hg : (msg ++ [b]).getD i 0 = msg.getD i 0 := by
        rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi,
          List.getElem_append_left hi]
      have h1 := hr i hi' e'
      rw [List.take_append_of_le_length hi.le, hg] at h1
      exact h1 he'
    · have hg : (msg ++ [b]).getD msg.length 0 = b := by simp
      have h1 := hr msg.length (by simp) e
      rw [List.take_left' rfl, hg] at h1
      exact h1 he

/-- **The `k`, `k'` points of rounds `0, …, j` are the rounds of the first `j + 1` blocks.** -/
theorem agreesRounds_take_succ {D : Dbs X₁ Z₁} {msg : List X₁} {j : ℕ}
    (hr : ∀ i ≤ j,
      D.k ((absorb (spongePerm (h, k, k') π) (msg.take i)).1 + msg.getD i 0) =
          some (k ((absorb (spongePerm (h, k, k') π) (msg.take i)).1 + msg.getD i 0)) ∧
        D.k' (π ((absorb (spongePerm (h, k, k') π) (msg.take i)).1 + msg.getD i 0,
            (absorb (spongePerm (h, k, k') π) (msg.take i)).2 +
              k ((absorb (spongePerm (h, k, k') π) (msg.take i)).1 + msg.getD i 0))).1 =
          some (k' (π ((absorb (spongePerm (h, k, k') π) (msg.take i)).1 + msg.getD i 0,
            (absorb (spongePerm (h, k, k') π) (msg.take i)).2 +
              k ((absorb (spongePerm (h, k, k') π) (msg.take i)).1 + msg.getD i 0))).1)) :
    AgreesRounds π h k k' D (msg.take (j + 1)) := by
  intro i hi
  have hi₁ : i < min (j + 1) msg.length := by rwa [List.length_take] at hi
  have hlt : i < msg.length := by omega
  have e1 : (msg.take (j + 1)).take i = msg.take i := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have e2 : (msg.take (j + 1))[i] = msg.getD i 0 := by
    rw [List.getElem_take, List.getD_eq_getElem _ _ hlt]
  simp only [e1, e2]
  exact hr i (by omega)

end sponge

/-! ## A round of a slot -/

section round

/-- The slots of a layer signature by an in-table key are in the table. -/
theorem inTable_of_layerSlots {l : Layer} {e : KeyIndex} {w : Encoding} {s : Slot}
    (he : e.val < keyCount l) (hs : s ∈ layerSlots l e w) : InTable s := by
  simp only [layerSlots, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons,
    List.mem_range] at hs
  rcases hs with ⟨i, -, step, -, rfl⟩ | rfl | ⟨lev, hlev, rfl⟩
  · exact he
  · exact he
  · have hkb := le_keyBits l
    have hlev' : lev < 16 := hlev
    refine ⟨by omega, by simp only [layerHeight]; omega, ?_⟩
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.sub_add_cancel (by omega)]
    exact he

/-- The template `k` port of round `j` of slot `s`'s honest path. -/
def rPortK (pub : Pub) (s : Slot) (j : ℕ) : LazyProg X Z HPos XD :=
  .programK (inlSet (slotNeed s)) fun w ↦ roundK pub s (extendVals w) j

/-- The template `k'` port of round `j` of slot `s`'s honest path. -/
def rPortK' (pub : Pub) (s : Slot) (j : ℕ) : LazyProg X Z HPos XD :=
  .programK' (inlSet (slotNeed s)) fun w ↦ roundK' pub s (extendVals w) j

/-- The template `h` port of round `j` of slot `s`'s honest path. -/
def rPortH (pub : Pub) (s : Slot) (j : ℕ) : LazyProg X Z HPos XD :=
  .programH (inlSet (slotNeed s)) fun w ↦ roundH pub s (extendVals w) j

/-- **The ports of a slot, round by round.** -/
theorem slotPorts_eq_flatMap (pub : Pub) (s : Slot) :
    slotPorts pub s = (List.range' 0 (nBlocks pub s)).flatMap fun j ↦
      [rPortK pub s j, rPortK' pub s j, rPortH pub s j] := by
  rw [← List.range_eq_range']
  rfl

theorem rPortH_mem_slotPorts (pub : Pub) (s : Slot) {j : ℕ} (hj : j < nBlocks pub s) :
    rPortH pub s j ∈ slotPorts pub s :=
  List.mem_flatMap.2 ⟨j, List.mem_range.2 hj,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- **The reads of round `i` of a slot's input** are the cells of its round ports with their key
values. -/
theorem roundReads_slot (L : HonestTable) (s : Slot) (f : ValPos → Digest) (i : ℕ) :
    roundReads L.perm L.keys.1 L.keys.2.1 L.keys.2.2
        (absorb (spongePerm (L.keys.1, L.keys.2.1, L.keys.2.2) L.perm)
          ((blocks (slotInput (pubOf L) s f)).take i))
        ((blocks (slotInput (pubOf L) s f)).getD i 0) =
      [.k (roundK (pubOf L) s f i).1 (L.keys.2.1 (roundK (pubOf L) s f i).1),
        .k' (roundK' (pubOf L) s f i).1 (L.keys.2.2 (roundK' (pubOf L) s f i).1),
        .h (roundH (pubOf L) s f i).1 (L.keys.1 (roundH (pubOf L) s f i).1)] := by
  have hH : (roundH (pubOf L) s f i).1 =
      (midAt (pubOf L) (stateAt (pubOf L) (blocks (slotInput (pubOf L) s f)) i)
          ((blocks (slotInput (pubOf L) s f)).getD i 0)).2 +
        (pubOf L).keys.2.2 (midAt (pubOf L) (stateAt (pubOf L) (blocks (slotInput (pubOf L) s f)) i)
          ((blocks (slotInput (pubOf L) s f)).getD i 0)).1 := by
    unfold roundH
    dsimp only
    split_ifs <;> rfl
  rw [hH]
  rfl

theorem keys_eq_of_tableHw_h {L : HonestTable} {z : Z} {u : X} (h : (tableHw L).1 z = some u) :
    u = L.keys.1 z := by
  simp only [tableHw] at h
  split at h
  · exact (Option.some_inj.mp h).symm
  · exact absurd h.symm (Option.some_ne_none u)

theorem keys_eq_of_tableHw_k {L : HonestTable} {x : X} {u : Z} (h : (tableHw L).2.1 x = some u) :
    u = L.keys.2.1 x := by
  simp only [tableHw] at h
  split at h
  · exact (Option.some_inj.mp h).symm
  · exact absurd h.symm (Option.some_ne_none u)

theorem keys_eq_of_tableHw_k' {L : HonestTable} {x : X} {u : Z} (h : (tableHw L).2.2 x = some u) :
    u = L.keys.2.2 x := by
  simp only [tableHw] at h
  split at h
  · exact (Option.some_inj.mp h).symm
  · exact absurd h.symm (Option.some_ne_none u)

/-- A hardwired `h` cell inside `tableHw L` holds its key value. -/
theorem heldBy_h_of_le {L : HonestTable} {W : Hw X Z} (hle : Quantum.Sponge.HwLe W (tableHw L))
    {z : Z} (hz : W.1 z ≠ none) : (SpongeRead.h z (L.keys.1 z)).HeldBy W.toDbs := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hz
  show W.1 z = some (L.keys.1 z)
  rw [hu, keys_eq_of_tableHw_h (hle.1 z u hu)]

/-- A hardwired `k` cell inside `tableHw L` holds its key value. -/
theorem heldBy_k_of_le {L : HonestTable} {W : Hw X Z} (hle : Quantum.Sponge.HwLe W (tableHw L))
    {x : X} (hx : W.2.1 x ≠ none) : (SpongeRead.k x (L.keys.2.1 x)).HeldBy W.toDbs := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hx
  show W.2.1 x = some (L.keys.2.1 x)
  rw [hu, keys_eq_of_tableHw_k (hle.2.1 x u hu)]

/-- A hardwired `k'` cell inside `tableHw L` holds its key value. -/
theorem heldBy_k'_of_le {L : HonestTable} {W : Hw X Z} (hle : Quantum.Sponge.HwLe W (tableHw L))
    {x : X} (hx : W.2.2 x ≠ none) : (SpongeRead.k' x (L.keys.2.2 x)).HeldBy W.toDbs := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hx
  show W.2.2 x = some (L.keys.2.2 x)
  rw [hu, keys_eq_of_tableHw_k' (hle.2.2 x u hu)]

/-- **A proper prefix of a tail of several blocks lies in the tail's slot, or is seed-shaped.** -/
theorem slotOf_cons_take {P : PublicParameter} {x₀ : X} {rest : List X} {sl : Slot}
    (hr : rest ≠ []) (h : slotOf P (x₀ :: rest) = some sl) (j : ℕ) :
    slotOf P (x₀ :: rest.take j) = some sl ∨ slotOf P (x₀ :: rest.take j) = some .seed := by
  have hr' : ¬(rest.isEmpty = true ∧ SeedShaped x₀) := fun hc ↦ hr (List.isEmpty_iff.mp hc.1)
  rw [slotOf, ite_eq_right hr'] at h
  rw [slotOf]
  by_cases hc : (rest.take j).isEmpty = true ∧ SeedShaped x₀
  · exact Or.inr (ite_eq_left hc)
  · exact Or.inl ((ite_eq_right hc).trans h)

theorem honestTail_seed (L : HonestTable) : L.honestTail .seed = none := by
  rw [HonestTable.honestTail, HonestTable.honestInput,
    ite_eq_right (show ¬InTable Slot.seed from fun h ↦ h)]
  rfl

/-- **The `h` port of round `j` of a slot is safe** at a state inside `tableHw L` with the slot's
cells of rounds `< j` and the `k`, `k'` cells of round `j` hardwired (at values `f` agreeing with
the table on the slot's coordinates). -/
theorem progSafe_round (L : HonestTable) {l : Layer} {e : KeyIndex} {x : Encoding} {s : Slot}
    (he : e.val < keyCount l) (hs : s ∈ layerSlots l e x) {f : ValPos → Digest}
    (hf : ∀ q ∈ slotNeed s, f q = valuePos L q) {j : ℕ} (hj : j < nBlocks (pubOf L) s)
    {r : HwReg X Z Mem} (hle : Quantum.Sponge.HwLe r.2.1 (tableHw L))
    (hK : ∀ i ≤ j, r.2.1.2.1 (roundK (pubOf L) s f i).1 ≠ none)
    (hK' : ∀ i ≤ j, r.2.1.2.2 (roundK' (pubOf L) s f i).1 ≠ none)
    (hH : ∀ i < j, r.2.1.1 (roundH (pubOf L) s f i).1 ≠ none)
    (hprog : ProgOf (tableHw L)
      (.programH (roundH (pubOf L) s f j).1 (roundH (pubOf L) s f j).2))
    (hz : r.2.1.1 (roundH (pubOf L) s f j).1 = none) :
    ProgSafe L (.programH (roundH (pubOf L) s f j).1 (roundH (pubOf L) s f j).2) r := by
  have hInT : InTable s := inTable_of_layerSlots he hs
  have hinput : L.honestInput s = some (slotInput (pubOf L) s f) := by
    rw [HonestTable.honestInput, ite_eq_left hInT, slotInput, slotPayload_eq L hs hf]
    rfl
  have hlen : (blocks (slotInput (pubOf L) s f)).length = nBlocks (pubOf L) s :=
    blocks_slotInput_length (pubOf L) s f
  have ht : L.honestTail s = some (absorbTail (spongePerm (pubOf L).keys (pubOf L).perm)
      (blocks (slotInput (pubOf L) s f))) := by
    rw [HonestTable.honestTail, hinput]
    rfl
  have hAg : AgreesRounds L.perm L.keys.1 L.keys.2.1 L.keys.2.2 (union r.2.1 r.1)
      ((blocks (slotInput (pubOf L) s f)).take (j + 1)) :=
    agreesRounds_take_succ L.perm L.keys.1 L.keys.2.1 L.keys.2.2 fun i hi ↦
      ⟨heldBy_union r.1 (heldBy_k_of_le hle (hK i hi)),
        heldBy_union r.1 (heldBy_k'_of_le hle (hK' i hi))⟩
  have hhead := isHeadTail_roundH (pubOf L) s f (D := union r.2.1 r.1)
    (by rw [hlen]; exact hj) hAg
  rcases Nat.lt_or_ge (j + 1) (nBlocks (pubOf L) s) with hlt | hge
  · -- an intermediate round: the tail of the first `j + 1` blocks is a proper prefix
    refine progSafe_programH_short L hz fun _ ↦ ?_
    obtain ⟨x₀, rest, hft⟩ : ∃ x₀ rest, absorbTail (spongePerm (pubOf L).keys (pubOf L).perm)
        (blocks (slotInput (pubOf L) s f)) = x₀ :: rest := by
      refine List.exists_cons_of_ne_nil fun h0 ↦ ?_
      have h1 := congrArg List.length h0
      rw [length_absorbTail, hlen, List.length_nil] at h1
      omega
    have hrest : rest.length + 1 = nBlocks (pubOf L) s := by
      have h1 := congrArg List.length hft
      rw [length_absorbTail, hlen, List.length_cons] at h1
      omega
    have hne : rest ≠ [] := by
      rintro rfl
      rw [List.length_nil] at hrest
      omega
    have ht0 : absorbTail (spongePerm (pubOf L).keys (pubOf L).perm)
        ((blocks (slotInput (pubOf L) s f)).take (j + 1)) = x₀ :: rest.take j := by
      rw [absorbTail_take, hft, List.take_succ_cons]
    have hslot := L.slotOf_honestTail ht
    rw [hft] at hslot
    have hlen0 : (absorbTail (spongePerm (pubOf L).keys (pubOf L).perm)
        ((blocks (slotInput (pubOf L) s f)).take (j + 1))).length = j + 1 := by
      rw [length_absorbTail, List.length_take, hlen]
      omega
    rcases slotOf_cons_take hne hslot j with h1 | h1
    · refine ⟨s, absorbTail (spongePerm (pubOf L).keys (pubOf L).perm)
        ((blocks (slotInput (pubOf L) s f)).take (j + 1)), _, by rw [ht0]; exact h1,
        fun l' e' h ↦ ?_, ?_, hhead⟩
      · subst h
        exact hInT
      · rw [ht, hlen0, Option.map_some, length_absorbTail, hlen]
        intro h
        have h' := Option.some_inj.mp h
        omega
    · refine ⟨.seed, absorbTail (spongePerm (pubOf L).keys (pubOf L).perm)
        ((blocks (slotInput (pubOf L) s f)).take (j + 1)), _, by rw [ht0]; exact h1,
        fun _ _ h ↦ Slot.noConfusion h, ?_, hhead⟩
      rw [honestTail_seed]
      exact (Option.some_ne_none _).symm
  · -- the final round: the slot is exempted once the cell is programmed
    have htake : (blocks (slotInput (pubOf L) s f)).take (j + 1) =
        blocks (slotInput (pubOf L) s f) :=
      List.take_of_length_le (by rw [hlen]; omega)
    rw [htake] at hhead
    refine progSafe_programH_honest L hz fun _ ↦ ⟨s, _, _, ht, ⟨hInT, ?_⟩, hhead⟩
    have hle' := hwLe_progUpdate hle hprog
    intro input hi e' he'
    obtain rfl : input = slotInput (pubOf L) s f := Option.some_inj.mp (hi.symm.trans hinput)
    refine heldBy_spongeReads_of_rounds L.perm L.keys.1 L.keys.2.1 L.keys.2.2
      (fun i hi' e'' he'' ↦ ?_) e' he'
    have h3 := (congrArg (e'' ∈ ·) (roundReads_slot L s f i)).mp he''
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
    have hi'' : i ≤ j := by
      rw [hlen] at hi'
      omega
    rcases h3 with rfl | rfl | rfl
    · exact heldBy_k_of_le hle' (hK i hi'')
    · exact heldBy_k'_of_le hle' (hK' i hi'')
    · refine heldBy_h_of_le hle' ?_
      rcases hi''.lt_or_eq with hlt | rfl
      · exact cellHardwired_progUpdate
          (c := .programH (roundH (pubOf L) s f j).1 (roundH (pubOf L) s f j).2)
          (c' := .programH (roundH (pubOf L) s f i).1 0) (hH i hlt)
      · exact cellHardwired_progUpdate_self
          (.programH (roundH (pubOf L) s f i).1 (roundH (pubOf L) s f i).2) r.2.1

end round

/-! ## The hardwired cells of the earlier ports -/

section steps

variable {M : Type} [Fintype M] [DecidableEq M]

/-- The cells of the program ports `C` are hardwired in `W`. -/
def AllHw (C : Set (HwProg X Z)) (W : Hw X Z) : Prop :=
  ∀ c ∈ C, CellHardwired c W

theorem allHw_progUpdate {C : Set (HwProg X Z)} {W : Hw X Z} (h : AllHw C W) (c : HwProg X Z) :
    AllHw (insert c C) (progUpdate c W) := by
  intro c' hc'
  rcases Set.mem_insert_iff.1 hc' with rfl | hc'
  · exact cellHardwired_progUpdate_self _ _
  · exact cellHardwired_progUpdate (h c' hc')

/-- A step of `runtimeR` at port `i` carries support on the states with `C` hardwired to support
on the states with `C'` hardwired. -/
def StepC (m₀ : Finset HPos × M) (i : (recHwSpec X Z HPos M).Port) (C C' : Set (HwProg X Z)) :
    Prop :=
  ∀ r σ, QuerySupportedOn (fun m : (recHwSpec X Z HPos M).In i × (runtimeR m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × M) | AllHw C s.2.1} σ →
    QuerySupportedOn (fun m : (recHwSpec X Z HPos M).Out i × (runtimeR m₀).D ↦ m.2)
      {s : HwReg X Z (Finset HPos × M) | AllHw C' s.2.1} (((runtimeR m₀).step i).branch r σ)

theorem stepC_sponge (m₀ : Finset HPos × M) (i : SpongePort) (C : Set (HwProg X Z)) :
    StepC m₀ (.inl (.inl (.inl i))) C C := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inl i)))).branch r σ =
      MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U i) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m₀ i r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    have he := snd_eq_of_spongeHardwired_U_ne_zero (hwEmpty X Z) m₀ i q.1 q'.1 q.2 q'.2 hK
    show AllHw C q'.2.2.1
    rw [congrArg Prod.fst he]
    exact hq

theorem stepC_read (m₀ : Finset HPos × M)
    (c : {c : HwRead X Z (Finset HPos × M) // ReadMono (memLab X Z HPos M) c})
    (C : Set (HwProg X Z)) : StepC m₀ (.inl (.inl (.inr c.1))) C C := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inl (.inr c.1)))).branch r σ =
      MatrixMap.conj (hwReadKraus c.1 r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m₀ c.1 r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    show AllHw C q'.2.2.1
    rw [hwReadKraus_ne_zero_hw c.1 r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK]
    exact hq

theorem stepC_prog (m₀ : Finset HPos × M) (c : HwProg X Z) (C : Set (HwProg X Z)) :
    StepC m₀ (.inl (.inr c)) C (insert c C) := by
  intro r σ hσ
  have hb : ((runtimeR m₀).step (.inl (.inr c))).branch r σ =
      MatrixMap.conj (hwProgKraus c r) σ :=
    LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m₀ c r) σ
  refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    show AllHw (insert c C) q'.2.2.1
    rw [hwProgKraus_ne_zero_snd c r (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK]
    exact allHw_progUpdate hq c

theorem stepC_rec (m₀ : Finset HPos × M) (T : Finset HPos) (C : Set (HwProg X Z)) :
    StepC m₀ (.inr T) C C := by
  intro r σ hσ
  exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
    show AllHw C q'.2.2.1
    rw [recKraus_ne_zero (u := q.1) (s := q.2) (u' := q'.1) (s' := q'.2) hK]
    exact hq

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

end steps

/-! ## Templates whose program ports are safe in batch order -/

section hb

variable (L : HonestTable) {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- **A program port is safe given the hardwired cells `C`**: at every state inside `tableHw L`
with the cells of `C` hardwired (as `FreeHSafe`: an `h` port with its cell free is safe). -/
def OkC (C : Set (HwProg X Z)) (c : HwProg X Z) : Prop :=
  ∀ r : HwReg X Z Mem, AllHw C r.2.1 → Quantum.Sponge.HwLe r.2.1 (tableHw L) →
    FreeHSafe L (.inl (.inr c)) r

variable {L} in
theorem OkC.anti {C D : Set (HwProg X Z)} {c : HwProg X Z} (h : OkC L D c) (hD : D ⊆ C) :
    OkC L C c :=
  fun r hC hle ↦ h r (fun c' hc' ↦ hC c' (hD hc')) hle

/-- The condition on a port before a call: a program port is safe given `C`. -/
def portOk : (XSpec Selections).Port → Set (HwProg X Z) → Prop
  | .inl (.inr p), C => OkC L C (p.1.realize (valueAt L))
  | _, _ => True

/-- The hardwired ports after a call: a program port adds its own. -/
def portNext : (XSpec Selections).Port → Set (HwProg X Z) → Set (HwProg X Z)
  | .inl (.inr p), C => insert (p.1.realize (valueAt L)) C
  | _, C => C

/-- The condition before a command. -/
def cmdOk {A : QReg} : QuantumComp.Cmd Λ (XSpec Selections) A → Set (HwProg X Z) → Prop
  | .prim _, _ => True
  | .query i _ _, C => portOk L i C

/-- The hardwired ports after a command. -/
def cmdNext {A : QReg} :
    QuantumComp.Cmd Λ (XSpec Selections) A → Set (HwProg X Z) → Set (HwProg X Z)
  | .prim _, C => C
  | .query i _ _, C => portNext L i C

/-- **A template whose program ports are safe in batch order**, run from the hardwired ports `C`,
ending with the hardwired ports `C'`. -/
def HB : {A : QReg} → IFreeM (QuantumComp.toIPFunctor Λ (XSpec Selections)) Ω A →
    Set (HwProg X Z) → Set (HwProg X Z) → Prop
  | _, .pure _, C, C' => C' ⊆ C
  | _, .liftBind c next, C, C' => cmdOk L c C ∧ ∀ b, HB (next b) (cmdNext L c C) C'

theorem cmdOk_anti {A : QReg} (c : QuantumComp.Cmd Λ (XSpec Selections) A)
    {C D : Set (HwProg X Z)} (hD : D ⊆ C) (h : cmdOk L c D) : cmdOk L c C := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · trivial
  · trivial
  · trivial
  · exact OkC.anti h hD
  · trivial

theorem cmdNext_mono {A : QReg} (c : QuantumComp.Cmd Λ (XSpec Selections) A)
    {C D : Set (HwProg X Z)} (hD : D ⊆ C) : cmdNext L c D ⊆ cmdNext L c C := by
  rcases c with o | ⟨((i | c) | p) | T, E, ℓ⟩
  · exact hD
  · exact hD
  · exact hD
  · exact Set.insert_subset_insert hD
  · exact hD

theorem hb_mono {A : QReg} (y : IFreeM (QuantumComp.toIPFunctor Λ (XSpec Selections)) Ω A)
    {C C' D D' : Set (HwProg X Z)} (hy : HB L y C C') (hD : C ⊆ D) (hD' : D' ⊆ C') :
    HB L y D D' := by
  induction y using IFreeM.inductionOn generalizing C D with
  | pure _ _ => exact hD'.trans (hy.trans hD)
  | liftBind _ c next ih =>
    exact ⟨cmdOk_anti L c hD hy.1, fun b ↦ ih b (hy.2 b) (cmdNext_mono L c hD)⟩

theorem hb_cast {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor Λ (XSpec Selections)) Ω A) (C C' : Set (HwProg X Z)) :
    HB L (e ▸ y) C C' ↔ HB L y C C' := by
  subst e
  rfl

theorem hb_bind {A : QReg} {Y : QReg → Type w₁}
    (x : IFreeM (QuantumComp.toIPFunctor Λ (XSpec Selections)) Ω A)
    (g : ∀ u, Ω u → IFreeM (QuantumComp.toIPFunctor Λ (XSpec Selections)) Y u)
    {C D C' : Set (HwProg X Z)} (hx : HB L x C D) (hg : ∀ u a, HB L (g u a) D C') :
    HB L (x.bind g) C C' := by
  induction x using IFreeM.inductionOn generalizing C with
  | pure _ a => exact hb_mono L _ (hg _ a) hx subset_rfl
  | liftBind _ c next ih => exact ⟨hx.1, fun b ↦ ih b (hx.2 b)⟩

theorem hb₂_bind {A B B' : QReg} {α : Type w} {β : Type w₁}
    (x : QuantumComp₂ Λ (XSpec Selections) A B α)
    (g : α → QuantumComp₂ Λ (XSpec Selections) B B' β)
    {C D C' : Set (HwProg X Z)} (hx : HB L x C D) (hg : ∀ a, HB L (g a) D C') :
    HB L (x.bind g) C C' := by
  refine hb_bind L x _ hx fun u p ↦ ?_
  obtain ⟨e, a⟩ := p
  subst e
  exact hg a

/-- Substituting trees whose program ports are safe from nothing hardwired. -/
theorem hb_substitute {spec : QuantumOracleSpec.{0, 0}}
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor Λ spec)
      (QuantumComp.toIPFunctor Λ (XSpec Selections)))
    (hσ : ∀ A c, HB L (σ A c) ∅ ∅) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor Λ spec) Ω A) : HB L (x.substitute σ) ∅ ∅ := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind s c next ih =>
    rw [IFreeM.substitute_liftBind]
    exact hb_bind L _ _ (hσ s c) fun u ans ↦ (hb_cast L ans.2 _ _ _).mpr (ih ans.1)

/-- Runtime 1's programs call no program port. -/
theorem hb_readLift {A : QReg} (y : QuantumComp Λ (hwReadSpec X Z Selections) Ω A)
    (C : Set (HwProg X Z)) : HB L (readLift goodAll y) C C := by
  induction y using IFreeM.inductionOn with
  | pure _ _ => exact subset_rfl
  | liftBind _ c next ih =>
    show HB L (IFreeM.mapLens (readLens goodAll) (IFreeM.liftBind c next)) C C
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
    HB L (QComp.act (spec := XSpec Selections) p) C C :=
  ⟨trivial, fun _ ↦ subset_rfl⟩

theorem hb_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × Selections) → QComp (XSpec Selections) B B' α)
    {C C' : Set (HwProg X Z)} (hk : ∀ r, HB L (k r) C C') :
    HB L (revealThen goodAll T k) C C' :=
  ⟨trivial, fun r ↦ hb₂_bind L _ _ (hb_act L _ _) fun _ ↦ hk r.down⟩

theorem hb_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (XSpec Selections) B B' α) {C C' : Set (HwProg X Z)}
    (hok : OkC L C (p.realize (valueAt L))) (hk : HB L k (insert (p.realize (valueAt L)) C) C') :
    HB L (progThen p hp k) C C' :=
  ⟨hok, fun _ ↦ hb₂_bind L _ _ (hb_act L _ _) fun _ ↦ hk⟩

/-- The realized ports of the rounds `< a` of slot `s`'s honest path. -/
def doneTo (s : Slot) (a : ℕ) : Set (HwProg X Z) :=
  {c | ∃ i < a, c = (rPortK (pubOf L) s i).realize (valueAt L) ∨
    c = (rPortK' (pubOf L) s i).realize (valueAt L) ∨
    c = (rPortH (pubOf L) s i).realize (valueAt L)}

/-- **The `h` port of a round is safe after the earlier rounds and its `k`, `k'` ports.** -/
theorem okC_portH {l : Layer} {e : KeyIndex} {x : Encoding} {s : Slot}
    (he : e.val < keyCount l) (hs : s ∈ layerSlots l e x) {j : ℕ}
    (hj : j < nBlocks (pubOf L) s) :
    OkC L (insert ((rPortK' (pubOf L) s j).realize (valueAt L))
      (insert ((rPortK (pubOf L) s j).realize (valueAt L)) (doneTo L s j)))
      ((rPortH (pubOf L) s j).realize (valueAt L)) := fun r hC hle ↦
  progSafe_round L he hs (fun q hq ↦ extendVals_restrictTo (inl_mem_inlSet.mpr hq) (valueAt L))
    hj hle
    (fun i hi ↦ by
      rcases hi.lt_or_eq with hi | rfl
      · exact hC ((rPortK (pubOf L) s i).realize (valueAt L))
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, hi, Or.inl rfl⟩))
      · exact hC ((rPortK (pubOf L) s i).realize (valueAt L))
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
    (fun i hi ↦ by
      rcases hi.lt_or_eq with hi | rfl
      · exact hC ((rPortK' (pubOf L) s i).realize (valueAt L))
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, hi, Or.inr (Or.inl rfl)⟩))
      · exact hC ((rPortK' (pubOf L) s i).realize (valueAt L)) (Set.mem_insert _ _))
    (fun i hi ↦ hC ((rPortH (pubOf L) s i).realize (valueAt L))
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, hi, Or.inr (Or.inr rfl)⟩)))
    (progsOf_tableHw L l e x he s hs _ (rPortH_mem_slotPorts (pubOf L) s hj))

/-- **The rounds `a, …, a + m - 1` of a slot**, in order, from the earlier rounds hardwired. -/
theorem hb_rounds (B : QReg) {l : Layer} {e : KeyIndex} {x : Encoding} {s : Slot}
    (he : e.val < keyCount l) (hs : s ∈ layerSlots l e x) :
    ∀ m a, a + m = nBlocks (pubOf L) s → ∀ C, doneTo L s a ⊆ C →
      HB L (progPorts Selections B ((List.range' a m).flatMap fun j ↦
        [rPortK (pubOf L) s j, rPortK' (pubOf L) s j, rPortH (pubOf L) s j])) C ∅
  | 0, _, _, C, _ => Set.empty_subset C
  | m + 1, a, hm, C, hC => by
    rw [List.range'_succ, List.flatMap_cons]
    refine hb_progThen L (rPortK (pubOf L) s a) trivial _ (fun _ _ _ ↦ trivial)
      (hb_progThen L (rPortK' (pubOf L) s a) trivial _ (fun _ _ _ ↦ trivial)
        (hb_progThen L (rPortH (pubOf L) s a) trivial _
          ((okC_portH L he hs (j := a) (by omega)).anti ?_)
          (hb_rounds B he hs m (a + 1) (by omega) _ ?_)))
    · exact Set.insert_subset_insert (Set.insert_subset_insert hC)
    · rintro c ⟨i, hi, hc⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (hC ⟨i, hi, hc⟩)))
      · rcases hc with rfl | rfl | rfl
        · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
        · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
        · exact Set.mem_insert _ _

/-- **The ports of a slot of an in-table key's layer signature, in `slotPorts` order.** -/
theorem hb_slotPorts (B : QReg) {l : Layer} {e : KeyIndex} {x : Encoding} {s : Slot}
    (he : e.val < keyCount l) (hs : s ∈ layerSlots l e x) (C : Set (HwProg X Z)) :
    HB L (progPorts Selections B (slotPorts (pubOf L) s)) C ∅ := by
  rw [slotPorts_eq_flatMap]
  refine hb_rounds L B he hs _ 0 (zero_add _) C ?_
  rintro c ⟨i, hi, -⟩
  exact absurd hi (Nat.not_lt_zero i)

theorem hb_progSlots (B : QReg) (ss : List Slot)
    (h : ∀ s ∈ ss, ∀ C, HB L (progPorts Selections B (slotPorts (pubOf L) s)) C ∅)
    (C : Set (HwProg X Z)) : HB L (progSlots Selections (pubOf L) B ss) C ∅ := by
  induction ss generalizing C with
  | nil => exact Set.empty_subset C
  | cons s ss ih =>
    exact hb₂_bind L _ _ (h s List.mem_cons_self C) fun _ ↦
      ih (fun s' hs' ↦ h s' (List.mem_cons_of_mem _ hs')) ∅

variable (upd : TrialUpd Selections)

/-- **A layer signature of an in-table key**: the randomizer search reads, then the slots it makes
public are programmed slot by slot. -/
theorem hb_signLayerT (B : QReg) (lab : RLabel) (he : lab.key.val < keyCount lab.layer) :
    HB L (signLayerT Selections upd (pubOf L) B lab) ∅ ∅ := by
  refine hb_revealThen L _ _ fun _ ↦ hb₂_bind L _ _ (hb_readLift L _ ∅) fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · exact subset_rfl
  · exact hb_revealThen L _ _ fun _ ↦ hb₂_bind L _ _
      (hb_progSlots L B _ (fun s hs C ↦ hb_slotPorts L B he hs C) ∅) fun _ ↦ subset_rfl

theorem hb_signT (B : QReg) (r : SigningRequest) :
    HB L (signT Selections upd (pubOf L) B r) ∅ ∅ := by
  refine hb₂_bind L _ _ (hb_signLayerT L upd B (botLabel r)
    (keyIndexOnLayer_lt r.leafIndex bottomLayer)) fun b ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · exact subset_rfl
  · refine hb₂_bind L _ _ (hb_signLayerT L upd B (topLabel r _)
      (keyIndexOnLayer_lt r.leafIndex topLayer)) fun t ↦ ?_
    rcases t with _ | ⟨top, _⟩ <;> exact subset_rfl

theorem hb_challengeT (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (advSpec (X × Z)) A) :
    HB L (challengeT Selections upd (pubOf L) A c) ∅ ∅ := by
  rcases c with o | ⟨p | r, E, ℓ⟩
  · exact hb_readLift L _ ∅
  · exact hb_readLift L _ ∅
  · exact hb_bind L _ _ (hb₂_bind L _ _ (hb_act L _ _) fun _ ↦ hb_signT L upd _ r)
      fun _ _ ↦ subset_rfl

/-- **The game's program ports are safe in batch order.** -/
theorem hb_gameT (A : Adversary (X × Z)) : HB L (gameT Selections upd (pubOf L) A) ∅ ∅ :=
  hb_revealThen L _ _ fun _ ↦
    hb₂_bind L _ _ (hb_substitute L _ (hb_challengeT L upd) _) fun _ ↦
      hb₂_bind L _ _ (hb_readLift L _ ∅) fun _ ↦ subset_rfl

end hb

/-! ## The presented operators -/

section present

variable (L : HonestTable) {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- **The calls are presented states where the port is safe once inside `tableHw L`.** -/
def bSupp (i : (recHwSpec X Z HPos Selections).Port) (E : QReg)
    (σ : Matrix (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E)
      (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) × E) ℂ) :
    Prop :=
  ∀ a, ¬(Quantum.Sponge.HwLe a.1.2.2.1 (tableHw L) → FreeHSafe L i a.1.2) → σ a a = 0

/-- One call of a realized program, from the hardwired ports `C` to `C'`. -/
theorem forallQueries_queryBind_of_stepC (I : Λ.Interp) {A : QReg}
    (i : (recHwSpec X Z HPos Selections).Port) (E : QReg)
    (ℓ : A ≃ (recHwSpec X Z HPos Selections).In i × E)
    (k' : (recHwSpec X Z HPos Selections).Result i → QuantumComp Λ
      (recHwSpec X Z HPos Selections) Ω (QReg.of ((recHwSpec X Z HPos Selections).Out i × E)))
    {C C' : Set (HwProg X Z)}
    (hpre : ∀ r : HwReg X Z Mem, AllHw C r.2.1 → Quantum.Sponge.HwLe r.2.1 (tableHw L) →
      FreeHSafe L i r)
    (hstep : StepC m0R i C C')
    (hk : ∀ r ρ', QuerySupportedOn (fun m : QReg.of ((recHwSpec X Z HPos Selections).Out i × E) ×
        (runtimeR m0R).D ↦ m.2) {s : HwReg X Z Mem | AllHw C' s.2.1} ρ' →
      (runtimeR m0R).ForallQueries I (bSupp L) (k' r) ρ')
    (ρ : Matrix (A × (runtimeR m0R).D) (A × (runtimeR m0R).D) ℂ)
    (hρ : QuerySupportedOn (fun m : A × (runtimeR m0R).D ↦ m.2)
      {s : HwReg X Z Mem | AllHw C s.2.1} ρ) :
    (runtimeR m0R).ForallQueries I (bSupp L) (QuantumComp.queryBind i E ℓ k') ρ :=
  ⟨fun a ha ↦ relabel_diag_eq_zero_of_supp m0R E ℓ hρ a fun hC ↦ ha (hpre _ hC), fun r ↦
    hk r _ (querySupportedOn_queryStep (runtimeR m0R) (fun s ↦ s) i r (hstep r) E ℓ hρ)⟩

/-- **The realized program of a template whose program ports are safe in batch order presents
only states where the called port is safe once inside `tableHw L`.** -/
theorem forallQueries_of_hb (I : Λ.Interp) {A : QReg} (y : QuantumComp Λ (XSpec Selections) Ω A) :
    ∀ C C', HB L y C C' → ∀ ρ : Matrix (A × (runtimeR m0R).D) (A × (runtimeR m0R).D) ℂ,
      QuerySupportedOn (fun m : A × (runtimeR m0R).D ↦ m.2)
        {s : HwReg X Z Mem | AllHw C s.2.1} ρ →
      (runtimeR m0R).ForallQueries I (bSupp L) (realizeT (valueAt L) y) ρ := by
  induction y using QuantumComp.inductionOn with
  | pure _ _ => intro _ _ _ _ _; trivial
  | primBind _ o k ih =>
    intro C C' hy ρ hρ b
    exact ih b C C' (hy.2 (ULift.up b)) _ (QuerySupportedOn.amplify_snd (q := fun s ↦ s) hρ _)
  | queryBind _ i E ℓ k ih =>
    intro C C' hy ρ hρ
    rcases i with ((i | c) | ⟨p, hp⟩) | T
    · exact forallQueries_queryBind_of_stepC L I (.inl (.inl (.inl i))) E ℓ
        (fun r ↦ realizeT (valueAt L) (k r)) (fun _ _ _ ↦ trivial) (stepC_sponge m0R i C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepC L I (.inl (.inl (.inr c.1))) E ℓ
        (fun r ↦ realizeT (valueAt L) (k r)) (fun _ _ _ ↦ trivial) (stepC_read m0R c C)
        (fun r ↦ ih r C C' (hy.2 (ULift.up r))) ρ hρ
    · cases p with
      | programH T₀ c =>
        exact forallQueries_queryBind_of_stepC L I
          (.inl (.inr ((LazyProg.programH T₀ c).realize (valueAt L)))) E ℓ
          (fun r ↦ realizeT (valueAt L) (k r)) hy.1 (stepC_prog m0R _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK T₀ c =>
        exact forallQueries_queryBind_of_stepC L I
          (.inl (.inr ((LazyProg.programK T₀ c).realize (valueAt L)))) E ℓ
          (fun r ↦ realizeT (valueAt L) (k r)) hy.1 (stepC_prog m0R _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
      | programK' T₀ c =>
        exact forallQueries_queryBind_of_stepC L I
          (.inl (.inr ((LazyProg.programK' T₀ c).realize (valueAt L)))) E ℓ
          (fun r ↦ realizeT (valueAt L) (k r)) hy.1 (stepC_prog m0R _ C)
          (fun r ↦ ih r _ C' (hy.2 (ULift.up r))) ρ hρ
    · exact forallQueries_queryBind_of_stepC L I (.inr T) E ℓ
        (fun m ↦ realizeT (valueAt L) (k (restrictTo T (valueAt L), m))) (fun _ _ _ ↦ trivial)
        (stepC_rec m0R T C)
        (fun m ↦ ih (restrictTo T (valueAt L), m) _ C'
          (hy.2 (ULift.up (restrictTo T (valueAt L), m)))) ρ hρ

/-- **Along the game, every call is presented states where the port is safe once inside
`tableHw L`.** -/
theorem forallQueries_bSupp_gameR (A : Adversary (X × Z)) :
    (runtimeR m0R).ForallQueries .instruments (bSupp L) (gameR A L) initR :=
  forallQueries_of_hb L .instruments _ ∅ ∅ (hb_gameT L cwUpd A) initR fun _ _ _ ↦
    ⟨fun c hc ↦ absurd hc (Set.notMem_empty c), fun c hc ↦ absurd hc (Set.notMem_empty c)⟩

/-- **ProgView's remaining `hsafe` piece**: along the game at any table, every free `h` program
call is presented only states at which it is safe. -/
theorem forallQueries_hFreeSupp_gameR (A : Adversary (X × Z)) :
    (runtimeR m0R).ForallQueries .instruments (hFreeSupp L) (gameR A L) initR :=
  (forallQueries_and (forallQueries_hwSupp_gameR A L) (forallQueries_bSupp_gameR L A)).mono _
    fun _ _ _ h a ha ↦ by
      by_contra hne
      have hle : Quantum.Sponge.HwLe a.1.2.2.1 (tableHw L) := by
        by_contra hn
        exact hne (h.1.2 a hn)
      exact hne (h.2 a fun hf ↦ ha (hf hle))

/-- **The program flips are the fresh `k`, `k'` flips on every table.** -/
theorem progTot_le_kTot_gameR (A : Adversary (X × Z)) : progTot A L ≤ kTot A L :=
  progTot_le_kTot A L (forallQueries_safeSupp_gameR A L (forallQueries_hFreeSupp_gameR L A))

end present

/-- **`progRest` without a bad fraction**: the averaged program flips over the `PermGood` tables
are at most the averaged fresh `k`, `k'` flips there. -/
theorem uavg_progTot_le_kTot {A : Adversary (X × Z)} {κ : ℝ≥0∞}
    (hk : uavg (fun L ↦ if PermGood L.perm 18 then kTot A L else 0) ≤ κ) :
    uavg (fun L ↦ if PermGood L.perm 18 then progTot A L else 0) ≤ κ := by
  refine (uavg_mono fun L ↦ ?_).trans hk
  by_cases hπ : PermGood L.perm 18
  · rw [ite_eq_left hπ, ite_eq_left hπ]
    exact progTot_le_kTot_gameR L A
  · rw [ite_eq_right hπ]
    exact zero_le

end Quantum.Xmss.Assembly

end
