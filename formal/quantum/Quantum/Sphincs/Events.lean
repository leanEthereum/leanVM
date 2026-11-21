module

public import Quantum.Sphincs.HonestTable
public import Quantum.Sphincs.CovBad
public import Quantum.Sphincs.Codeword

@[expose] public section

/-!
# The leanSPHINCS event of the hardwired register

## Contract C3: memory and Bad

* **Memory** (`Mem S = Finset S × Selections`): the template's memory label (the revealed
  coordinates; `S` is the template's `HPos`, contract C2) and the selections, for each WOTS+C key
  `K = (l, τ, e)` the block of its selected encoding input (`PK.seed ‖ ADRS_enc(K) ‖ M_K ‖ BE32(c)`,
  68 bytes, one block) and the selected digest. A trial read records a codeword digest of an
  unselected key (`cwSel`, `cwUpd`); selections are never removed (`le_cwUpd`).
* **Data** (`EvData`): what the event reads of the template data `(p, v)` (contract C4): `PK.seed`,
  `π`, the keys `(h, k, k')`, the 128-bit values at the value positions (`ValPos`, contract C1), and
  the static coverage set `S★(v)`. No honest table: the Struct target of a structural slot `s` is
  the value at its output position, `value (slotOutPos s)`, its honest input the slot input at the
  values (`slotInput`), its honest tail the tail of that input under the public keys (`honTail`).
* **Bad** (`Bad d N = TgtBad d N ∪ CovBadOf d N`), at most `N` hardwired cells per function:
  `TgtBad` is `HwTargetBad` of the target function `sphTgt` (`trunc128` outputs): at a structural
  slot (`InTable`) the value at the output position for a tail of the honest tail's length, except
  the honest tail of an exempted slot (`exS`); at an encoding slot of a selected key the selected
  digest, except for the selected block. `CovBadOf` is `Quantum.Sphincs.CovBad` with the coverage
  set `S★` and the exemption `covEx`.

## The exemptions

Both exemptions are sets of hardwired honest paths, so they grow with the hardwired cells (`HwLe`)
and do not read the memory.

* `exS W`: the structural slots whose honest path `W` holds (`HeldIn`): every read of the slot's
  input under keys `(h', k, k')`, with `h'` the public `h` except possibly at the final capacity, so
  that the tail is the honest tail and the output digest is the value at the output position. The
  template programs the last round's `h` cell with a value corrected so that the digest is the value
  (`embed128`), so `h'` is the public `h` updated there. As in leanXMSS, a classification gets from
  `heldIn_union_of_mem_exS` that the union's view of an exempted slot's honest input is honest.
* `covEx W`: the pairs `(R, M)` whose call-0 `H_msg` tail (one block) has its path in `W`: its `k`
  and `k'` cells and the `h` cell at its capacity, with any value (`PathIn`).

**Why `covEx` is the hardwired call-0 paths and not the signed pairs of the memory.** The event
must not read the memory label: a record port of `runtimeR` grows the label, and only for an event
that does not read it do its Kraus operators commute with the event projector, so that record ports
cost `0` (`Quantum.Xmss.Assembly.eventWeight_runtimeR_le`, hypothesis `LabelFree`; here
`bad_label_iff`). With the hardwired paths, `CovBad`'s `covBad_progUpdate` hypothesis at the honest
program of the call-0 `h` cell of a signed pair `(R, M)` follows from two facts: the head-tail of
the cell is the call's tail, whose slot is `hmsg R M 0` and no other pair's (`slotOf` is a
function), and the template programs the `k` and `k'` cells of the round before its `h` cell, so the
path is in `W` (`mem_covEx_programH`). A classification gets that an exempted pair is a signed one
from the template's invariant that only signatures program `H_msg` cells.

## Results

* `upClosed_slice_bad`, `not_mem_bad_empty`, `freshBound_slice_bad`: the hypotheses of the graded
  event bound, with the rate `preimageRateBound (N + T) G 2^960 +
  preimageRateBound (N + T) G (2^838 coverMass S★)`; on `h`, `2^-128 + 2^16 price S★`
  (`freshRate_h_eq`); in all, at most `κ + 2^16 price S★` with `κ = 2^-128 + 2 capRate (N + T) G`
  (`freshRate_le`).
* Program ports (the cell not yet hardwired): at most `2^960 + 2^838 coverMass S★` values of an `h`
  cell (`card_flip_programH_bad_le`); none at the final cell of an exempted structural slot's
  honest path (`not_mem_bad_programH_honest`), of an exempted `H_msg` call
  (`not_mem_bad_programH_hmsg`), or at an intermediate cell of a multi-block honest path
  (`not_mem_bad_programH_short`); twice the capacity-scale counts for `k`, `k'`.
* Read ports: a selection read of key `K` flips at most `encCount K · 2^960` values
  (`card_flip_read_le`), a read selecting nothing none (`not_mem_bad_read_keep`); the coverage part
  never flips at a read whose cell's head-tail is not a call-0 `H_msg` tail
  (`mem_tgtBad_of_mem_bad_readH`). Record ports keep membership (`bad_label_iff`).
-/

open Finset Quantum Quantum.Sponge Sphincs
open HashSig (Digest Message PublicParameter Randomizer)
open Quantum.Xmss (X Z blocks trunc128 out256 card_X fiber_div_card_X card_fiber_trunc128_le
  heldBy_mono heldBy_union)
open scoped ENNReal

namespace Quantum.Sphincs

/-! ## Unions of events -/

section Union

/-- A filter for a predicate implying `Q ∨ R` has at most the two filters' elements. -/
theorem card_filter_le_add {γ : Type} [Fintype γ] [DecidableEq γ] {P Q R : γ → Prop}
    {_ : DecidablePred P} {_ : DecidablePred Q} {_ : DecidablePred R} (h : ∀ a, P a → Q a ∨ R a) :
    #(univ.filter P) ≤ #(univ.filter Q) + #(univ.filter R) :=
  (card_le_card fun a ha ↦ by
    rcases h a (mem_filter.1 ha).2 with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h⟩)).trans (card_union_le _ _)

/-- A filter for a predicate implying `Q` lies in the filter for `Q`. -/
theorem filter_univ_mono {γ : Type} [Fintype γ] {P Q : γ → Prop} {_ : DecidablePred P}
    {_ : DecidablePred Q} (h : ∀ a, P a → Q a) : univ.filter P ⊆ univ.filter Q :=
  fun a ha ↦ mem_filter.2 ⟨mem_univ _, h a (mem_filter.1 ha).2⟩

theorem natCast_div_le_add {a b c : ℕ} (e : ℝ≥0∞) (h : a ≤ b + c) :
    (a : ℝ≥0∞) / e ≤ (b : ℝ≥0∞) / e + (c : ℝ≥0∞) / e := by
  rw [← ENNReal.add_div]
  exact ENNReal.div_le_div_right (by exact_mod_cast h) _

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {S T U : Set (Dbs α β)}

omit [Fintype α] [Fintype β] in
/-- A union of upward-closed events is upward closed. -/
theorem upClosed_of_union (hU : ∀ D, D ∈ U ↔ D ∈ S ∨ D ∈ T) (hS : UpClosed S)
    (hT : UpClosed T) : UpClosed U where
  h D hD z u hz := (hU _).2 (((hU D).1 hD).imp (hS.h D · z u hz) (hT.h D · z u hz))
  k D hD x u hx := (hU _).2 (((hU D).1 hD).imp (hS.k D · x u hx) (hT.k D · x u hx))
  k' D hD x u hx := (hU _).2 (((hU D).1 hD).imp (hS.k' D · x u hx) (hT.k' D · x u hx))

/-- **The fresh bound of a union** is the sum of the fresh bounds. -/
theorem freshBound_of_union {_ : DecidablePred (· ∈ S)} {_ : DecidablePred (· ∈ T)}
    {_ : DecidablePred (· ∈ U)} (hU : ∀ D, D ∈ U ↔ D ∈ S ∨ D ∈ T) {t : ℕ} {ε ε' : ℝ≥0∞}
    (hS : FreshBound S t ε) (hT : FreshBound T t ε') : FreshBound U t (ε + ε') where
  h D hD h₁ h₂ h₃ z hz :=
    (natCast_div_le_add _ (card_filter_le_add fun _ hu ↦ (hU _).1 hu)).trans
      (add_le_add (hS.h D (fun h ↦ hD ((hU D).2 (.inl h))) h₁ h₂ h₃ z hz)
        (hT.h D (fun h ↦ hD ((hU D).2 (.inr h))) h₁ h₂ h₃ z hz))
  k D hD h₁ h₂ h₃ x hx :=
    (natCast_div_le_add _ (card_filter_le_add fun _ hu ↦ (hU _).1 hu)).trans
      (add_le_add (hS.k D (fun h ↦ hD ((hU D).2 (.inl h))) h₁ h₂ h₃ x hx)
        (hT.k D (fun h ↦ hD ((hU D).2 (.inr h))) h₁ h₂ h₃ x hx))
  k' D hD h₁ h₂ h₃ x hx :=
    (natCast_div_le_add _ (card_filter_le_add fun _ hu ↦ (hU _).1 hu)).trans
      (add_le_add (hS.k' D (fun h ↦ hD ((hU D).2 (.inl h))) h₁ h₂ h₃ x hx)
        (hT.k' D (fun h ↦ hD ((hU D).2 (.inr h))) h₁ h₂ h₃ x hx))

end Union

/-! ## The memory -/

/-- **The selections**: for each WOTS+C key, the block of its selected encoding input and the
selected digest. -/
abbrev Selections : Type :=
  Key → Option (X × Digest)

/-- **The memory of the hardwired register**: the template's memory label and the selections. -/
abbrev Mem (S : Type) : Type :=
  Finset S × Selections

namespace Selections

/-- Recording the selection of key `K`: block `x`, digest `y`. -/
def select (m : Selections) (K : Key) (x : X) (y : Digest) : Selections :=
  Function.update m K (some (x, y))

theorem select_self (m : Selections) (K : Key) (x : X) (y : Digest) :
    m.select K x y K = some (x, y) :=
  Function.update_self _ _ _

theorem select_of_ne (m : Selections) {K K' : Key} (x : X) (y : Digest) (h : K' ≠ K) :
    m.select K x y K' = m K' :=
  Function.update_of_ne h _ _

/-- `m'` holds every selection of `m`. -/
def Le (m m' : Selections) : Prop :=
  ∀ K c, m K = some c → m' K = some c

theorem Le.refl (m : Selections) : m.Le m :=
  fun _ _ h ↦ h

/-- **Selecting an unselected key keeps the other selections.** -/
theorem select_mono {m : Selections} {K : Key} (hm : m K = none) (x : X) (y : Digest) :
    m.Le (m.select K x y) := fun K' c h ↦ by
  by_cases hK : K' = K
  · subst hK
    rw [hm] at h
    cases h
  · rw [select_of_ne _ x y hK]
    exact h

end Selections

/-- **The memory after a trial read** of key `K` with block `x`, rate `xi` and value `v`: the
selection if the digest is a codeword. -/
noncomputable def cwSel (m : Selections) (K : Key) (x xi v : X) : Selections :=
  if Codeword.Valid (trunc128 (xi + v)) then m.select K x (trunc128 (xi + v)) else m

/-- **The memory update of a trial read**: select a codeword digest of an unselected key. -/
noncomputable def cwUpd (K : Key) (x xi : X) : Selections → Option X → Selections
  | m, some v => if m K = none then cwSel m K x xi v else m
  | m, none => m

theorem cwUpd_some (K : Key) (x xi : X) (m : Selections) (v : X) :
    cwUpd K x xi m (some v) = m ∨ cwUpd K x xi m (some v) = cwSel m K x xi v := by
  show (if m K = none then cwSel m K x xi v else m) = m ∨
    (if m K = none then cwSel m K x xi v else m) = cwSel m K x xi v
  split_ifs
  · exact .inr rfl
  · exact .inl rfl

theorem cwUpd_some_of_none (K : Key) (x xi : X) {m : Selections} (hm : m K = none) (v : X) :
    cwUpd K x xi m (some v) = cwSel m K x xi v :=
  ite_eq_left hm

theorem cwSel_eq (m : Selections) (K : Key) (x xi v : X) :
    cwSel m K x xi v = m ∨ cwSel m K x xi v = m.select K x (trunc128 (xi + v)) := by
  unfold cwSel
  split_ifs
  · exact .inr rfl
  · exact .inl rfl

/-- A trial of an unselected key leaves it unselected exactly when its digest is no codeword. -/
theorem cwSel_eq_none_iff {m : Selections} {K : Key} (hm : m K = none) (x xi v : X) :
    cwSel m K x xi v K = none ↔ ¬ Codeword.Valid (trunc128 (xi + v)) := by
  unfold cwSel
  split_ifs with hv
  · rw [Selections.select_self]
    exact iff_of_false (Option.some_ne_none _) (not_not.2 hv)
  · exact iff_of_true hm hv

/-- **A trial read never removes a selection.** -/
theorem le_cwUpd (K : Key) (x xi : X) (m : Selections) (u : Option X) :
    m.Le (cwUpd K x xi m u) := by
  cases u with
  | none => exact Selections.Le.refl m
  | some v =>
    by_cases hm : m K = none
    · rw [cwUpd_some_of_none K x xi hm]
      rcases cwSel_eq m K x xi v with h | h <;> rw [h]
      · exact Selections.Le.refl m
      · exact Selections.select_mono hm x _
    · show m.Le (if m K = none then cwSel m K x xi v else m)
      rw [ite_eq_right hm]
      exact Selections.Le.refl m

/-! ## The data of the event -/

/-- **The data of the event**: `PK.seed`, `π`, the keys `(h, k, k')`, the values at the value
positions, and the static coverage set. -/
structure EvData where
  /-- `PK.seed`. -/
  seed : PublicParameter
  /-- The permutation `π` of the sponge decomposition. -/
  perm : Equiv.Perm (X × Z)
  /-- The keys `(h, k, k')`. -/
  keys : SpongeKeys X Z
  /-- The 128-bit value at each value position. -/
  value : ValPos → Digest
  /-- The static coverage set `S★`. -/
  cover : Disclosures

namespace EvData

variable (d : EvData)

/-- The public key: `PK.seed` and the value at the root's position. -/
def pk : PublicKey :=
  ⟨d.seed, d.value rootPos⟩

/-- The sponge permutation of the public keys. -/
def view : Equiv.Perm (X × Z) :=
  spongePerm d.keys d.perm

/-- The blocks of a slot's input at the values. -/
def blocksOf (s : Slot) : List X :=
  blocks (slotInput d.seed s d.value)

/-- **The honest tail of a slot**: the tail of its input at the values under the public keys. -/
def honTail (s : Slot) : List X :=
  absorbTail d.view (d.blocksOf s)

/-- **The honest path of slot `s` is held by `U`**: `U` holds every read of the slot's input under
keys `(h', k, k')` for some `h'` that gives the honest tail and the value at the output position as
the digest (the public `h`, corrected at the final capacity). -/
def HeldIn (U : Dbs X Z) (s : Slot) : Prop :=
  ∃ h' : Z → X, (∀ e ∈ spongeReads d.perm h' d.keys.2.1 d.keys.2.2 (d.blocksOf s), e.HeldBy U) ∧
    absorbTail (spongePerm (h', d.keys.2.1, d.keys.2.2) d.perm) (d.blocksOf s) = d.honTail s ∧
    trunc128 (spongeHash (spongePerm (h', d.keys.2.1, d.keys.2.2) d.perm) (d.blocksOf s)) =
      d.value (slotOutPos s)

/-- **The exempted structural slots**: those whose honest path the hardwired cells hold. -/
def exS (W : Hw X Z) : Set Slot :=
  {s | InTable s ∧ d.HeldIn W.toDbs s}

/-- **`U` holds the path of the tail `t`**: its rounds and an `h` value at its final capacity. -/
def PathIn (U : Dbs X Z) (t : List X) : Prop :=
  ∃ z xi w, IsHeadTail d.perm U t z xi ∧ U.h z = some w

/-- **The exempted pairs of the coverage event**: those whose call-0 `H_msg` tail has its path in
the hardwired cells. -/
def covEx (W : Hw X Z) : Set (Randomizer × Message) :=
  {p | d.PathIn W.toDbs (d.honTail (.hmsg p.1 p.2 0))}

/-! ### Monotonicity of the exemptions -/

variable {d}

theorem heldIn_mono {U U' : Dbs X Z} (h : ∀ e : SpongeRead X Z, e.HeldBy U → e.HeldBy U')
    {s : Slot} (hs : d.HeldIn U s) : d.HeldIn U' s := by
  obtain ⟨h', hr, ht, ho⟩ := hs
  exact ⟨h', fun e he ↦ h e (hr e he), ht, ho⟩

theorem exS_mono {W W' : Hw X Z} (h : HwLe W W') : d.exS W ⊆ d.exS W' :=
  fun _ hs ↦ ⟨hs.1, heldIn_mono (fun _ he ↦ heldBy_mono h he) hs.2⟩

/-- **An exempted slot's honest path is held by the union.** -/
theorem heldIn_union_of_mem_exS {W : Hw X Z} (D : DbReg X Z) {s : Slot} (hs : s ∈ d.exS W) :
    d.HeldIn (union W D) s :=
  heldIn_mono (fun _ he ↦ heldBy_union D he) hs.2

theorem pathIn_mono {U U' : Dbs X Z} (hE : ExtendsAll U' U) {t : List X} (h : d.PathIn U t) :
    d.PathIn U' t := by
  obtain ⟨z, xi, w, hi, hw⟩ := h
  exact ⟨z, xi, w, hi.mono hE.1, hE.2 z w hw⟩

theorem extendsAll_of_hwLe {W W' : Hw X Z} (h : HwLe W W') : ExtendsAll W'.toDbs W.toDbs :=
  ⟨⟨fun x a hx ↦ h.2.1 x a hx, fun x a hx ↦ h.2.2 x a hx⟩, fun z w hz ↦ h.1 z w hz⟩

theorem extendsAll_union_hw (W D : DbReg X Z) : ExtendsAll (union W D) W.toDbs :=
  ⟨⟨fun x a hx ↦ heldBy_union D (e := .k x a) hx, fun x a hx ↦ heldBy_union D (e := .k' x a) hx⟩,
    fun z w hz ↦ heldBy_union D (e := .h z w) hz⟩

theorem covEx_mono {W W' : Hw X Z} (h : HwLe W W') : d.covEx W ⊆ d.covEx W' :=
  fun _ hp ↦ pathIn_mono (extendsAll_of_hwLe h) hp

theorem exMono_covEx {S : Type} : ExMono (M := Mem S) fun W _ ↦ d.covEx W :=
  fun _ _ _ h ↦ covEx_mono h

/-- **A path in the hardwired cells is a path of the union.** -/
theorem pathIn_union {W : Hw X Z} (D : DbReg X Z) {t : List X} (h : d.PathIn W.toDbs t) :
    d.PathIn (union W D) t :=
  pathIn_mono (extendsAll_union_hw W D) h

/-- **Programming the `h` cell of a call-0 `H_msg` tail exempts its pair**, once the `k` and `k'`
cells of its round are hardwired. -/
theorem mem_covEx_programH {W : Hw X Z} {R : Randomizer} {M : Message} {z : Z} {xi : X}
    (hi : IsHeadTail d.perm W.toDbs (d.honTail (.hmsg R M 0)) z xi) (v : X) :
    (R, M) ∈ d.covEx (Function.update W.1 z (some v), W.2) := by
  have hz : Function.update W.1 z (some v) z = some v := Function.update_self _ _ _
  generalize Function.update W.1 z (some v) = h₁ at hz ⊢
  exact ⟨z, xi, v, IsHeadTail.mono (D := DbReg.toDbs (h₁, W.2)) (D' := W.toDbs)
    ⟨fun _ _ h ↦ h, fun _ _ h ↦ h⟩ hi, hz⟩

/-! ### Slots of honest tails -/

variable (d)

/-- **The honest tail of a structural slot lies in its slot.** -/
theorem slotOf_honTail {s : Slot} (hs : InTable s) : slotOf d.pk (d.honTail s) = some s := by
  cases s with
  | chain l τ e i step => exact slotOf_chain d.view d.pk l τ e i step _
  | leaf l τ e => exact slotOf_leaf d.view d.pk l τ e _
  | node l τ height index =>
    obtain ⟨-, -, h2, h3⟩ := hs
    have hl := layerHeight_le l
    have hi := lt_two_pow_of_lt h3
    have hp : 2 ^ layerHeight l ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact slotOf_node d.view d.pk l τ height index
      (lt_of_le_of_lt (h2.trans hl) (by norm_num)) (lt_of_lt_of_le hi hp) _ _
  | forsLeaf idx κ s => exact slotOf_forsLeaf d.view d.pk idx κ s _
  | forsNode idx κ height node =>
    obtain ⟨h1, h2, h3⟩ := hs
    exact slotOf_forsNode d.view d.pk idx κ height node (by omega) h2 h3 _ _
  | forsRoots idx => exact slotOf_forsRoots d.view d.pk idx _
  | enc => exact hs.elim
  | prf => exact hs.elim
  | hmsg => exact hs.elim
  | prfMsg => exact hs.elim
  | expand => exact hs.elim

/-- **The honest tail of an `H_msg` call lies in its slot**, for every randomizer. -/
theorem slotOf_honTail_hmsg (R : Randomizer) (M : Message) (c : DigestCall) :
    slotOf d.pk (d.honTail (.hmsg R M c)) = some (.hmsg R M c) :=
  slotOf_messageDigestInput_self d.view d.pk R M c

end EvData

/-! ## Targets -/

open EvData

/-- **The structural target of a tail `t` at slot `s`**: at a structural slot, the value at the
output position for a tail of the honest tail's length, unless `t` is the honest tail of an
exempted slot. -/
noncomputable def EvData.structTgt (d : EvData) (Ex : Set Slot) (t : List X) (s : Slot) :
    Option Digest :=
  @ite _ (InTable s ∧ (d.honTail s).length = t.length ∧ ¬(t = d.honTail s ∧ s ∈ Ex))
    (Classical.propDecidable _) (some (d.value (slotOutPos s))) none

/-- **The encoding target of a tail `t` at slot `s`**: at the encoding slot of a selected key, the
selected digest, unless `t` is the selected block. -/
noncomputable def encTgt (sel : Selections) (t : List X) : Slot → Option Digest
  | .enc l τ e => (sel (l, τ, e)).bind fun c ↦
      @ite _ (t = [c.1]) (Classical.propDecidable _) none (some c.2)
  | _ => none

/-- **The target function of Struct and Enc**: a tail's target, read from its slot. -/
noncomputable def EvData.sphTgt (d : EvData) (Ex : Set Slot) (sel : Selections) (t : List X) :
    Option Digest :=
  (slotOf d.pk t).bind fun s ↦ (d.structTgt Ex t s).or (encTgt sel t s)

section Targets

variable {d : EvData} {Ex Ex' : Set Slot} {sel : Selections} {t : List X} {s : Slot} {y : Digest}

theorem structTgt_eq_some_iff :
    d.structTgt Ex t s = some y ↔
      (InTable s ∧ (d.honTail s).length = t.length ∧ ¬(t = d.honTail s ∧ s ∈ Ex)) ∧
        y = d.value (slotOutPos s) := by
  unfold EvData.structTgt
  split_ifs with h
  · rw [Option.some_inj]
    exact ⟨fun e ↦ ⟨h, e.symm⟩, fun e ↦ e.2.symm⟩
  · exact ⟨fun e ↦ e.elim, fun e ↦ absurd e.1 h⟩

theorem encTgt_eq_some_iff :
    encTgt sel t s = some y ↔
      ∃ l τ e x, s = .enc l τ e ∧ sel (l, τ, e) = some (x, y) ∧ t ≠ [x] := by
  cases s with
  | enc l τ e =>
    show (sel (l, τ, e)).bind _ = some y ↔ _
    constructor
    · intro h
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.1 h
      by_cases ht : t = [c.1]
      · rw [ite_eq_left ht] at h
        cases h
      · rw [ite_eq_right ht] at h
        exact ⟨l, τ, e, c.1, rfl, by rw [hc, ← Option.some.inj h], ht⟩
    · rintro ⟨l', τ', e', x, he, hc, ht⟩
      obtain ⟨rfl, rfl, rfl⟩ := Slot.enc.inj he
      rw [hc, Option.bind_some, ite_eq_right ht]
  | _ => simp [encTgt]

theorem encTgt_of_inTable (hs : InTable s) : encTgt sel t s = none := by
  cases s <;> first | rfl | exact hs.elim

theorem structTgt_of_not_inTable (hs : ¬ InTable s) : d.structTgt Ex t s = none :=
  ite_eq_right fun h ↦ hs h.1

theorem or_tgt_eq_some_iff :
    (d.structTgt Ex t s).or (encTgt sel t s) = some y ↔
      d.structTgt Ex t s = some y ∨ encTgt sel t s = some y := by
  by_cases hs : InTable s
  · rw [encTgt_of_inTable hs]
    cases d.structTgt Ex t s <;> simp
  · rw [structTgt_of_not_inTable hs]
    simp

theorem sphTgt_eq_some_iff :
    d.sphTgt Ex sel t = some y ↔
      ∃ s, slotOf d.pk t = some s ∧ (d.structTgt Ex t s = some y ∨ encTgt sel t s = some y) := by
  unfold EvData.sphTgt
  rw [Option.bind_eq_some_iff]
  exact exists_congr fun _ ↦ and_congr Iff.rfl or_tgt_eq_some_iff

/-- More exempted slots, fewer targets. -/
theorem sphTgt_mono (h : Ex ⊆ Ex') (ht : d.sphTgt Ex' sel t = some y) :
    d.sphTgt Ex sel t = some y := by
  obtain ⟨s, hs, hst | hst⟩ := sphTgt_eq_some_iff.1 ht
  · obtain ⟨⟨h1, h2, h3⟩, rfl⟩ := structTgt_eq_some_iff.1 hst
    exact sphTgt_eq_some_iff.2 ⟨s, hs, .inl (structTgt_eq_some_iff.2
      ⟨⟨h1, h2, fun hc ↦ h3 ⟨hc.1, h hc.2⟩⟩, rfl⟩)⟩
  · exact sphTgt_eq_some_iff.2 ⟨s, hs, .inr hst⟩

theorem sphTgt_eq_none (h : ∀ s, slotOf d.pk t = some s → d.structTgt Ex t s = none ∧
    encTgt sel t s = none) : d.sphTgt Ex sel t = none := by
  rcases ht : d.sphTgt Ex sel t with _ | y
  · rfl
  obtain ⟨s, hs, hst | hst⟩ := sphTgt_eq_some_iff.1 ht
  · rw [(h s hs).1] at hst
    cases hst
  · rw [(h s hs).2] at hst
    cases hst

/-- **A structural hit**: a tail at a structural slot, of the honest tail's length, other than the
honest tail of an exempted slot, has the value at the output position as its target. -/
theorem sphTgt_struct (hslot : slotOf d.pk t = some s) (hT : InTable s)
    (hlen : (d.honTail s).length = t.length) (hne : ¬(t = d.honTail s ∧ s ∈ Ex)) :
    d.sphTgt Ex sel t = some (d.value (slotOutPos s)) :=
  sphTgt_eq_some_iff.2 ⟨s, hslot, .inl (structTgt_eq_some_iff.2 ⟨⟨hT, hlen, hne⟩, rfl⟩)⟩

/-- **An encoding hit**: a tail at the encoding slot of a selected key, other than the selected
block, has the selected digest as its target. -/
theorem sphTgt_enc {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {x : X}
    (hslot : slotOf d.pk t = some (.enc l τ e)) (hm : sel (l, τ, e) = some (x, y)) (hne : t ≠ [x]) :
    d.sphTgt Ex sel t = some y :=
  sphTgt_eq_some_iff.2 ⟨_, hslot, .inr (encTgt_eq_some_iff.2 ⟨l, τ, e, x, rfl, hm, hne⟩)⟩

/-- **An exempted honest tail has no target.** -/
theorem sphTgt_honTail (hT : InTable s) (hs : s ∈ Ex) : d.sphTgt Ex sel (d.honTail s) = none :=
  sphTgt_eq_none fun s' hs' ↦ by
    obtain rfl := Option.some.inj ((d.slotOf_honTail hT).symm.trans hs')
    exact ⟨ite_eq_right fun h ↦ h.2.2 ⟨rfl, hs⟩, encTgt_of_inTable hT⟩

/-- **A tail of another length than its structural slot's honest tail has no target**: the
intermediate tails of the multi-block honest inputs (the one-time leaf's 8 blocks, the FORS roots'
4). -/
theorem sphTgt_short (hslot : slotOf d.pk t = some s) (hT : InTable s)
    (hlen : (d.honTail s).length ≠ t.length) : d.sphTgt Ex sel t = none :=
  sphTgt_eq_none fun s' hs' ↦ by
    obtain rfl := Option.some.inj (hslot.symm.trans hs')
    exact ⟨ite_eq_right fun h ↦ hlen h.2.1, encTgt_of_inTable hT⟩

/-- **A tail at a slot that is neither structural nor an encoding slot has no target**: `H_msg`,
the secrets, `PRF_msg`, the key expansion. -/
theorem sphTgt_of_slot (hslot : slotOf d.pk t = some s) (hT : ¬ InTable s)
    (henc : ∀ l τ e, s ≠ .enc l τ e) : d.sphTgt Ex sel t = none :=
  sphTgt_eq_none fun s' hs' ↦ by
    obtain rfl := Option.some.inj (hslot.symm.trans hs')
    refine ⟨structTgt_of_not_inTable hT, ?_⟩
    rcases he : encTgt sel t s with _ | y
    · rfl
    obtain ⟨l, τ, e, -, rfl, -⟩ := encTgt_eq_some_iff.1 he
    exact absurd rfl (henc l τ e)

/-- An `H_msg` tail has no Struct or Enc target. -/
theorem sphTgt_hmsg {R : Randomizer} {M : Message} {c : DigestCall}
    (hslot : slotOf d.pk t = some (.hmsg R M c)) : d.sphTgt Ex sel t = none :=
  sphTgt_of_slot hslot id fun _ _ _ h ↦ by cases h

/-- **A tail at the encoding slot of an unselected key has no target.** -/
theorem sphTgt_enc_none {K : Key} (hslot : slotOf d.pk t = some (.enc K.1 K.2.1 K.2.2))
    (hm : sel K = none) : d.sphTgt Ex sel t = none :=
  sphTgt_eq_none fun s' hs' ↦ by
    obtain rfl := Option.some.inj (hslot.symm.trans hs')
    refine ⟨structTgt_of_not_inTable id, ?_⟩
    rcases he : encTgt sel t (.enc K.1 K.2.1 K.2.2) with _ | y
    · rfl
    obtain ⟨l, τ, e, x, h, hc, -⟩ := encTgt_eq_some_iff.1 he
    obtain ⟨rfl, rfl, rfl⟩ := Slot.enc.inj h
    rw [hm] at hc
    cases hc

/-- **Recording a selection** adds the selected digest as the target of the other tails at its
encoding slot, and nothing else. -/
theorem sphTgt_select {K : Key} {x : X} {y' : Digest}
    (h : d.sphTgt Ex (sel.select K x y) t = some y') :
    d.sphTgt Ex sel t = some y' ∨
      (slotOf d.pk t = some (.enc K.1 K.2.1 K.2.2) ∧ t ≠ [x] ∧ y' = y) := by
  obtain ⟨s, hs, hst | hst⟩ := sphTgt_eq_some_iff.1 h
  · exact .inl (sphTgt_eq_some_iff.2 ⟨s, hs, .inl hst⟩)
  obtain ⟨l, τ, e, x', rfl, hc, hne⟩ := encTgt_eq_some_iff.1 hst
  by_cases hK : (l, τ, e) = K
  · subst hK
    rw [Selections.select_self] at hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
    exact .inr ⟨hs, hne, rfl⟩
  · rw [Selections.select_of_ne _ x y hK] at hc
    exact .inl (sphTgt_enc hs hc hne)

end Targets

/-! ## The coverage targets of honest tails -/

section Cov

variable {d : EvData} {Ex : Set (Randomizer × Message)} {t : List X} {s : Slot}

/-- A tail at a slot other than call 0 of `H_msg` has no coverage target. -/
theorem covTgt_of_slot (hslot : slotOf d.pk t = some s) (h : ∀ R M, s ≠ .hmsg R M 0) :
    covTgt d.pk Ex t = none :=
  covTgt_eq_none fun R M hs ↦ absurd (Option.some.inj (hslot.symm.trans hs)) (h R M)

/-- **An `H_msg` tail of an exempted pair has no coverage target**, nor has a call-1 tail. -/
theorem covTgt_honTail_hmsg {R : Randomizer} {M : Message} {c : DigestCall}
    (hex : c = 0 → (R, M) ∈ Ex) : covTgt d.pk Ex (d.honTail (.hmsg R M c)) = none :=
  covTgt_eq_none fun R' M' hs ↦ by
    obtain ⟨rfl, rfl, rfl⟩ := Slot.hmsg.inj (Option.some.inj
      ((d.slotOf_honTail_hmsg R M c).symm.trans hs))
    exact hex rfl

theorem covTgt_honTail (hT : InTable s) : covTgt d.pk Ex (d.honTail s) = none :=
  covTgt_of_slot (d.slotOf_honTail hT) fun R M h ↦ by subst h; exact hT

end Cov

/-! ## The event -/

namespace EvData

/-- The targets of Struct and Enc at the hardwired register's classical data `(W, m)`. -/
noncomputable def sphTgtHw {S : Type} (d : EvData) (W : Hw X Z) (m : Mem S) :
    List X → Option Digest :=
  d.sphTgt (d.exS W) m.2

theorem tgtAnti_sphTgtHw {S : Type} (d : EvData) : TgtAnti (M := Mem S) d.sphTgtHw :=
  fun _ _ _ h _ _ ↦ sphTgt_mono (exS_mono h)

end EvData

/-- **The Struct and Enc event**: at most `N` hardwired cells per function, and a tail of the union
reaching its target (or the union bad). -/
abbrev TgtBad {S : Type} (d : EvData) (N : ℕ) : Set (HwReg X Z (Mem S)) :=
  HwTargetBad d.perm trunc128 d.sphTgtHw N

/-- **The coverage event** of the data, with the hardwired call-0 paths exempted. -/
abbrev CovBadOf {S : Type} (d : EvData) (N : ℕ) : Set (HwReg X Z (Mem S)) :=
  CovBad d.perm d.pk d.cover (fun W _ ↦ d.covEx W) N

/-- **The leanSPHINCS event of the hardwired register** (contract C3). -/
abbrev Bad {S : Type} (d : EvData) (N : ℕ) : Set (HwReg X Z (Mem S)) :=
  TgtBad d N ∪ CovBadOf d N

section Event

variable {S : Type} {d : EvData} {N : ℕ}

theorem mem_bad_iff {D : DbReg X Z} {W : Hw X Z} {m : Mem S} :
    (D, W, m) ∈ Bad d N ↔ (D, W, m) ∈ TgtBad d N ∨ (D, W, m) ∈ CovBadOf d N :=
  Iff.rfl

theorem mem_tgtBad_iff {D : DbReg X Z} {W : Hw X Z} {m : Mem S} :
    (D, W, m) ∈ TgtBad d N ↔ dbGrade W ≤ N ∧
      union W D ∈ TargetBad d.perm trunc128 (d.sphTgt (d.exS W) m.2) :=
  Iff.rfl

/-- **The event does not read the memory label** (Template's `LabelFree`): record ports keep
membership. -/
theorem bad_label_iff {D : DbReg X Z} {W : Hw X Z} {T T' : Finset S} {sel : Selections} :
    (D, W, (T, sel)) ∈ Bad d N ↔ (D, W, (T', sel)) ∈ Bad d N :=
  Iff.rfl

/-- **The coverage event reads no memory.** -/
theorem covBadOf_memory_iff {D : DbReg X Z} {W : Hw X Z} {m m' : Mem S} :
    (D, W, m) ∈ CovBadOf d N ↔ (D, W, m') ∈ CovBadOf d N :=
  Iff.rfl

/-- **A Struct or Enc hit is in the event**: a tail of the union reaching its target, with few
hardwired cells. -/
theorem mem_bad_of_tgt {D : DbReg X Z} {W : Hw X Z} {m : Mem S} (hN : dbGrade W ≤ N) {t : List X}
    {y : Digest} (ht : d.sphTgt (d.exS W) m.2 t = some y)
    (hr : Reaches d.perm (union W D) trunc128 t y) : (D, W, m) ∈ Bad d N :=
  .inl ⟨hN, .inr ⟨t, y, ht, hr⟩⟩

/-- **A covered call-0 tail of a pair outside the exemption is in the event.** -/
theorem mem_bad_of_cov {D : DbReg X Z} {W : Hw X Z} {m : Mem S} (hN : dbGrade W ≤ N)
    {R : Randomizer} {M : Message} {t : List X} {y : HashSig.HashOutput}
    (hs : slotOf d.pk t = some (.hmsg R M 0)) (hn : (R, M) ∉ d.covEx W)
    (hr : Reaches d.perm (union W D) out256 t y) (hc : HalfCov d.cover (hiOf y, leavesOf y)) :
    (D, W, m) ∈ Bad d N :=
  .inr (mem_covBad_of (ex := fun W (_ : Mem S) ↦ d.covEx W) hN hs hn hr hc)

/-- **The start is outside the event**: no database and no hardwired cell. -/
theorem not_mem_bad_empty (m : Mem S) :
    ((Database.empty, Database.empty, Database.empty), (Database.empty, Database.empty,
      Database.empty), m) ∉ Bad d N := by
  rintro (h | h)
  · exact empty_not_mem_hwTargetBad m h
  · exact not_mem_covBad_empty m h

/-- **Every slice of the event is upward closed.** -/
theorem upClosed_slice_bad (W : Hw X Z) (m : Mem S) : UpClosed (slice (Bad d N) W m) :=
  upClosed_of_union (S := slice (TgtBad d N) W m) (T := slice (CovBadOf d N) W m)
    (fun _ ↦ Iff.rfl) (upClosed_slice_hwTargetBad W m) (upClosed_slice_covBad W m)

/-- **The fresh bound of every slice** below `T` database entries: the sum of the rates of Struct
and Enc (`2^960` values of an `h` cell per target) and of coverage (`2^838 coverMass S★`). -/
theorem freshBound_slice_bad [DecidablePred (· ∈ Bad (S := S) d N)] {G : ℕ}
    (hπ : PermGood d.perm G) (T : ℕ) (W : Hw X Z) (m : Mem S) :
    FreshBound (slice (Bad d N) W m) T
      (preimageRateBound (X := X) (Z := Z) (N + T) G (2 ^ 960) +
        preimageRateBound (X := X) (Z := Z) (N + T) G (2 ^ 838 * coverMass d.cover)) := by
  classical
  exact freshBound_of_union (S := slice (TgtBad d N) W m) (T := slice (CovBadOf d N) W m)
    (U := slice (Bad d N) W m)
    (fun _ ↦ Iff.rfl)
    (freshBound_slice_hwTargetBad_of_tgt hπ (fun _ _ _ y _ ↦ card_fiber_trunc128_le y) T W m)
    (freshBound_slice_covBad hπ T W m)

/-- **The `h` rates**: `2^960 / |X| + 2^838 coverMass S / |X| = 2^-128 + 2^16 price S`. -/
theorem freshRate_h_eq (S' : Disclosures) :
    ((2 ^ 960 : ℕ) : ℝ≥0∞) / Fintype.card X + ((2 ^ 838 * coverMass S' : ℕ) : ℝ≥0∞) /
        Fintype.card X =
      (2 ^ 128)⁻¹ + ENNReal.ofReal ((2 ^ 16 * price S' : ℚ) : ℝ) := by
  rw [fiber_div_card_X, covRate_eq]

theorem preimageRateBound_ne_top (T G F : ℕ) :
    preimageRateBound (X := X) (Z := Z) T G F ≠ ⊤ := by
  have hX : (Fintype.card X : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hZ : (Fintype.card Z : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold preimageRateBound
  exact max_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hX)
    (max_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hZ)
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hZ))

/-- The capacity part of `preimageRateBound`: the larger of the `k` and `k'` rates. -/
noncomputable def capRate (T G : ℕ) : ℝ≥0∞ :=
  max (((T + 1) * ((T + 1) * T + 2 * T) * G : ℕ) / Fintype.card Z : ℝ≥0∞)
    (((T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T : ℕ) / Fintype.card Z : ℝ≥0∞)

theorem preimageRateBound_le_add (T G F : ℕ) :
    preimageRateBound (X := X) (Z := Z) T G F ≤ (F : ℝ≥0∞) / Fintype.card X + capRate T G :=
  max_le le_self_add le_add_self

/-- **The fresh rate is `κ + 2^16 price S`** with `κ = 2^-128 + 2 capRate`: the `h` rates of
Struct and Enc and of coverage, and the capacity rates of both. -/
theorem freshRate_le (T G : ℕ) (S' : Disclosures) :
    preimageRateBound (X := X) (Z := Z) T G (2 ^ 960) +
        preimageRateBound (X := X) (Z := Z) T G (2 ^ 838 * coverMass S') ≤
      (2 ^ 128)⁻¹ + 2 * capRate T G + ENNReal.ofReal ((2 ^ 16 * price S' : ℚ) : ℝ) := by
  have h1 := preimageRateBound_le_add T G (2 ^ 960)
  have h2 := preimageRateBound_le_add T G (2 ^ 838 * coverMass S')
  rw [fiber_div_card_X] at h1
  rw [covRate_eq] at h2
  refine (add_le_add h1 h2).trans_eq ?_
  rw [two_mul]
  abel

/-! ### Program ports -/

open scoped Classical in
/-- **Programming an `h` cell** that is not hardwired: at most `2^960 + 2^838 coverMass S★` values
flip a state outside the event into it. -/
theorem card_flip_programH_bad_le {D : DbReg X Z} {W : Hw X Z} {m : Mem S}
    (hs : (D, W, m) ∉ Bad d N) {z : Z} (hW : W.1 z = none) :
    #(univ.filter fun v : X ↦
      ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∈
        Bad d N) ≤ 2 ^ 960 + 2 ^ 838 * coverMass d.cover :=
  (card_filter_le_add fun _ h ↦ h).trans (add_le_add
    (card_flip_programH_le d.tgtAnti_sphTgtHw card_fiber_trunc128_le (fun h ↦ hs (.inl h)) hW)
    (card_flip_programH_covBad_le exMono_covEx (fun h ↦ hs (.inr h)) hW))

/-- **Programming the final `h` cell of an exempted structural slot's honest path**: no value
flips. In the good union the head-tail of the cell is the honest tail, which has no Struct target
once the slot is exempted, and no coverage target at a structural slot. -/
theorem not_mem_bad_programH_honest {D : DbReg X Z} {W : Hw X Z} {m : Mem S}
    (hs : (D, W, m) ∉ Bad d N) {z : Z} (hW : W.1 z = none) (v : X) {s : Slot} (hT : InTable s)
    (hex : s ∈ d.exS (Function.update W.1 z (some v), W.2)) {xi₀ : X}
    (hhead : IsHeadTail d.perm (union W D) (d.honTail s) z xi₀) :
    ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∉ Bad d N := by
  rintro (h | h)
  · exact not_mem_programH d.tgtAnti_sphTgtHw (fun h ↦ hs (.inl h)) hW v (fun hG _ _ hi ↦ by
      obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hhead
      exact sphTgt_honTail hT hex) h
  · exact covBad_progUpdate exMono_covEx (fun h ↦ hs (.inr h)) hW v hhead
      (fun R M hsl ↦ absurd ((d.slotOf_honTail hT).symm.trans hsl) fun he ↦ by
        cases Option.some.inj he; exact hT) h

/-- **Programming the `h` cell of an `H_msg` call**: no value flips if the call is call 1, or its
pair is exempted once the cell is hardwired (`mem_covEx_programH`). In the good union the head-tail
of the cell is the call's tail, at its `hmsg` slot, which has no Struct or Enc target. -/
theorem not_mem_bad_programH_hmsg {D : DbReg X Z} {W : Hw X Z} {m : Mem S}
    (hs : (D, W, m) ∉ Bad d N) {z : Z} (hW : W.1 z = none) (v : X) {R : Randomizer}
    {M : Message} {c : DigestCall}
    (hex : c = 0 → (R, M) ∈ d.covEx (Function.update W.1 z (some v), W.2)) {xi₀ : X}
    (hhead : IsHeadTail d.perm (union W D) (d.honTail (.hmsg R M c)) z xi₀) :
    ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∉ Bad d N := by
  rintro (h | h)
  · exact not_mem_programH d.tgtAnti_sphTgtHw (fun h ↦ hs (.inl h)) hW v (fun hG _ _ hi ↦ by
      obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hhead
      exact sphTgt_hmsg (d.slotOf_honTail_hmsg R M c)) h
  · exact covBad_progUpdate exMono_covEx (fun h ↦ hs (.inr h)) hW v hhead
      (fun R' M' hsl ↦ by
        obtain ⟨rfl, rfl, rfl⟩ := Slot.hmsg.inj (Option.some.inj
          ((d.slotOf_honTail_hmsg R M c).symm.trans hsl))
        exact hex rfl) h

/-- **Programming an intermediate `h` cell of a multi-block honest path**: no value flips. In the
good union the head-tail of the cell is `t₀`, at a structural slot with a length other than the
honest tail's, so it has no target; and `h` never changes goodness. -/
theorem not_mem_bad_programH_short {D : DbReg X Z} {W : Hw X Z} {m : Mem S}
    (hs : (D, W, m) ∉ Bad d N) {z : Z} (hW : W.1 z = none) (v : X) {s : Slot} {t₀ : List X}
    {xi₀ : X} (hslot : slotOf d.pk t₀ = some s) (hT : InTable s)
    (hlen : (d.honTail s).length ≠ t₀.length)
    (hhead : IsHeadTail d.perm (union W D) t₀ z xi₀) :
    ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∉ Bad d N := by
  rintro (h | h)
  · exact not_mem_programH d.tgtAnti_sphTgtHw (fun h ↦ hs (.inl h)) hW v (fun hG _ _ hi ↦ by
      obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hhead
      exact sphTgt_short hslot hT hlen) h
  · exact covBad_progUpdate exMono_covEx (fun h ↦ hs (.inr h)) hW v hhead
      (fun R M hsl ↦ absurd (hslot.symm.trans hsl) fun he ↦ by
        cases Option.some.inj he; exact hT) h

open scoped Classical in
/-- **A program after which no value is in the event flips nothing.** -/
theorem card_programH_bad_eq_zero {D : DbReg X Z} {W : Hw X Z} {m : Mem S} {z : Z}
    (h : ∀ v : X, ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∉
      Bad d N) :
    #(univ.filter fun v : X ↦
      ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∈
        Bad d N) = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun v _ ↦ h v

open scoped Classical in
/-- **Programming a `k` cell** that is not hardwired: twice the capacity-scale count of
`preimageRateBound`, for at most `T ≥ N + dbGrade D` entries. -/
theorem card_flip_programK_bad_le {G T : ℕ} (hπ : PermGood d.perm G) {D : DbReg X Z} {W : Hw X Z}
    {m : Mem S} (hs : (D, W, m) ∉ Bad d N) (hT : N + dbGrade D ≤ T) {x : X}
    (hW : W.2.1 x = none) :
    #(univ.filter fun v : Z ↦
      ((D.1, Function.update D.2.1 x none, D.2.2), (W.1, Function.update W.2.1 x (some v), W.2.2),
        m) ∈ Bad d N) ≤ 2 * ((T + 1) * ((T + 1) * T + 2 * T) * G) :=
  (card_filter_le_add fun _ h ↦ h).trans ((add_le_add
    (card_flip_programK_le d.tgtAnti_sphTgtHw hπ (fun h ↦ hs (.inl h)) hT hW)
    (card_flip_programK_covBad_le exMono_covEx hπ (fun h ↦ hs (.inr h)) hT hW)).trans
      (two_mul _).symm.le)

open scoped Classical in
/-- **Programming a `k'` cell** that is not hardwired: twice the capacity-scale count of
`preimageRateBound`, for at most `T ≥ N + dbGrade D` entries. -/
theorem card_flip_programK'_bad_le {G T : ℕ} (hπ : PermGood d.perm G) {D : DbReg X Z}
    {W : Hw X Z} {m : Mem S} (hs : (D, W, m) ∉ Bad d N) (hT : N + dbGrade D ≤ T) {x : X}
    (hW : W.2.2 x = none) :
    #(univ.filter fun v : Z ↦
      ((D.1, D.2.1, Function.update D.2.2 x none), (W.1, W.2.1, Function.update W.2.2 x (some v)),
        m) ∈ Bad d N) ≤ 2 * ((T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T) :=
  (card_filter_le_add fun _ h ↦ h).trans ((add_le_add
    (card_flip_programK'_le d.tgtAnti_sphTgtHw hπ (fun h ↦ hs (.inl h)) hT hW)
    (card_flip_programK'_covBad_le exMono_covEx hπ (fun h ↦ hs (.inr h)) hT hW)).trans
      (two_mul _).symm.le)

/-! ### Read ports -/

/-- **A read whose cell's head-tails are no call-0 `H_msg` tails adds no coverage member**, for any
memory after the read: a state outside the event that lands in it lands in Struct and Enc. -/
theorem mem_tgtBad_of_mem_bad_readH {D : DbReg X Z} {W : Hw X Z} {m m' : Mem S}
    (hs : (D, W, m) ∉ Bad d N) {z : Z} (hW : W.1 z = none) (hD : D.1 z = none)
    (hhead : Good d.perm (union W D) → ∀ t xi, IsHeadTail d.perm (union W D) t z xi →
      ∀ R M, slotOf d.pk t ≠ some (.hmsg R M 0)) {u : Option X}
    (h : ((Function.update D.1 z u, D.2), W, m') ∈ Bad d N) :
    ((Function.update D.1 z u, D.2), W, m') ∈ TgtBad d N := by
  rcases h with h | h
  · exact h
  · exact absurd h (not_mem_covBad_readH (m' := m') (fun h ↦ hs (.inr h)) hW hD subset_rfl
      (fun hG t xi hi R M hsl ↦ absurd hsl (hhead hG t xi hi R M)) u)

/-- The `h` cells of `U` whose head-tail lies at the encoding slot of key `K`. -/
noncomputable def encCount (d : EvData) (U : Dbs X Z) (K : Key) : ℕ :=
  tailCount d.perm U fun t ↦ slotOf d.pk t = some (.enc K.1 K.2.1 K.2.2)

theorem encCount_le_size (d : EvData) (U : Dbs X Z) (K : Key) : encCount d U K ≤ U.h.size :=
  tailCount_le_size _ _ _

/-- **A selection read**: the read of the `h` cell `z` of an encoding trial of key `K` with block
`x` and rate `xi`. The cell is neither hardwired nor recorded, the key has no selection, and the
trial's tail (its one block) is the head-tail of `z` at the encoding slot of `K`. -/
structure SelectRead (d : EvData) (D : DbReg X Z) (W : Hw X Z) (sel : Selections) (z : Z)
    (K : Key) (x xi : X) : Prop where
  hw : W.1 z = none
  hd : D.1 z = none
  hm : sel K = none
  slot : slotOf d.pk [x] = some (.enc K.1 K.2.1 K.2.2)
  head : IsHeadTail d.perm (union W D) [x] z xi

theorem SelectRead.covHead {D : DbReg X Z} {W : Hw X Z} {sel : Selections} {z : Z} {K : Key}
    {x xi : X} (hr : SelectRead d D W sel z K x xi) (hG : Good d.perm (union W D)) (t : List X)
    (xi' : X) (hi : IsHeadTail d.perm (union W D) t z xi') (R : Randomizer) (M : Message) :
    slotOf d.pk t ≠ some (.hmsg R M 0) := by
  obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hr.head
  rw [hr.slot]
  exact fun h ↦ by cases Option.some.inj h

/-- Under a selection read, the head-tails of the read cell have no Struct or Enc target, before or
after the selection is recorded. -/
theorem SelectRead.head_none {D : DbReg X Z} {W : Hw X Z} {sel : Selections} {z : Z} {K : Key}
    {x xi : X} (hr : SelectRead d D W sel z K x xi) (hG : Good d.perm (union W D)) (T : Finset S)
    {y : Digest} {t : List X} {xi' : X} (hi : IsHeadTail d.perm (union W D) t z xi') :
    d.sphTgtHw W ((T, sel.select K x y) : Mem S) t = none := by
  obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hr.head
  rcases hy : d.sphTgtHw W ((T, sel.select K x y) : Mem S) [x] with _ | y'
  · rfl
  rcases sphTgt_select hy with h | ⟨-, hne, -⟩
  · rw [sphTgt_enc_none hr.slot hr.hm] at h
    cases h
  · exact absurd rfl hne

/-- **A selection read whose digest no other tail at the encoding slot reaches**: whatever the read
leaves in the cell, the state with the selection recorded is outside the event. -/
theorem not_mem_bad_read_select {D : DbReg X Z} {W : Hw X Z} {T : Finset S} {sel : Selections}
    {z : Z} {K : Key} {x xi : X} (hs : (D, W, (T, sel)) ∉ Bad d N)
    (hr : SelectRead d D W sel z K x xi) {v : X}
    (hv : ∀ t, slotOf d.pk t = some (.enc K.1 K.2.1 K.2.2) → t ≠ [x] →
      ¬ Reaches d.perm (union W D) trunc128 t (trunc128 (xi + v))) (u : Option X) :
    ((Function.update D.1 z u, D.2), W, (T, sel.select K x (trunc128 (xi + v)))) ∉ Bad d N :=
  fun h ↦ not_mem_readH (m' := ((T, sel.select K x (trunc128 (xi + v))) : Mem S))
    (fun h ↦ hs (.inl h)) hr.hw hr.hd
    (Q := fun t y ↦ slotOf d.pk t = some (.enc K.1 K.2.1 K.2.2) ∧ t ≠ [x] ∧
      y = trunc128 (xi + v))
    (fun _ _ ht ↦ sphTgt_select ht)
    (fun t _ ⟨hslot, hne, hy⟩ hreach ↦ hv t hslot hne (hy ▸ hreach))
    (fun hG _ _ hi ↦ hr.head_none hG T hi) u
    (mem_tgtBad_of_mem_bad_readH hs hr.hw hr.hd (fun hG ↦ hr.covHead hG) h)

/-- **A read that selects nothing flips nothing**: the trial's tail is at the encoding slot of an
unselected key, so it has no target. -/
theorem not_mem_bad_read_keep {D : DbReg X Z} {W : Hw X Z} {T : Finset S} {sel : Selections}
    {z : Z} {K : Key} {x xi : X} (hs : (D, W, (T, sel)) ∉ Bad d N)
    (hr : SelectRead d D W sel z K x xi) (u : Option X) :
    ((Function.update D.1 z u, D.2), W, (T, sel)) ∉ Bad d N :=
  fun h ↦ not_mem_readH (fun h ↦ hs (.inl h)) hr.hw hr.hd (Q := fun _ _ ↦ False)
    (fun _ _ ht ↦ .inl ht) (fun _ _ h ↦ h.elim)
    (fun hG t _ hi ↦ by
      obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hr.head
      exact sphTgt_enc_none hr.slot hr.hm) u
    (mem_tgtBad_of_mem_bad_readH hs hr.hw hr.hd (fun hG ↦ hr.covHead hG) h)

open scoped Classical in
/-- **`card_flip_read_le`**: a selection read of key `K` adds its Enc target, which flips a state
outside the event for at most `encCount * 2^960` values of the read cell, whatever the read leaves
in the cell: the flips are the old outputs of the other tails at the encoding slot of `K`. -/
theorem card_flip_read_le {D : DbReg X Z} {W : Hw X Z} {T : Finset S} {sel : Selections} {z : Z}
    {K : Key} {x xi : X} (hs : (D, W, (T, sel)) ∉ Bad d N) (hr : SelectRead d D W sel z K x xi) :
    #(univ.filter fun v : X ↦ ∃ u : Option X,
      ((Function.update D.1 z u, D.2), W, (T, sel.select K x (trunc128 (xi + v)))) ∈ Bad d N) ≤
        encCount d (union W D) K * 2 ^ 960 := by
  refine le_trans (card_le_card (filter_univ_mono fun v ⟨u, hu⟩ ↦ ⟨u, ?_⟩))
    (card_flip_readH_le card_fiber_trunc128_le (fun h ↦ hs (.inl h)) hr.hw hr.hd
      (fun t ↦ slotOf d.pk t = some (.enc K.1 K.2.1 K.2.2)) [x] xi
      (fun v ↦ ((T, sel.select K x (trunc128 (xi + v))) : Mem S))
      (fun _ _ _ ht ↦ sphTgt_select ht) (fun hG _ _ _ hi ↦ hr.head_none hG T hi))
  exact mem_tgtBad_of_mem_bad_readH hs hr.hw hr.hd (fun hG ↦ hr.covHead hG) hu

end Event

end Quantum.Sphincs

end
