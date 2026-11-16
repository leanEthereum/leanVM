module

public import Quantum.Xmss.Assembly.PrefixRun
public import Quantum.Xmss.Assembly.GameTCalls
public import Quantum.Xmss.Assembly.MassSources
public import Quantum.Xmss.Assembly.FullTable
public import Quantum.Xmss.TableLaw

@[expose] public section

/-!
# The prefix invariant of the canonical game, off the trial-hit event

WinDecomp's `endReads_wGame` needs the facts `PreFacts` of a winning prefix outcome on the register
(the public key, transcript signatures and records of one selection function, exempted slots
public). They hold in the decompressed basis (PrefixRun's `HT₂` semantics), off an event:

* **The trial-hit event** (`TrialHit L`): some trial of some top key's randomizer search,
  evaluated against the register's view `regFns s`, reads a cell of `tableHw L` (a cell the game
  may program). A top key's search reruns for every request under it; off this event the
  programmed cells never change what it reads (`topRec_congr`), so every rerun selects the same
  randomizer and the transcript is that of one selection function. The event depends only on the
  view off `tableHw L` (`trialHit_iff_of_offAgree`), which program calls keep
  (`ProgsRel.facts`); reveals, records, reads and sponge calls keep the view.
* **Selections and disclosures of a memory** (`selOf`, `discOf`): the selection function a memory
  records and the positions it discloses; `preFacts_of` gives `PreFacts` from recorded keys that
  were requested (`RecFrom`), transcript signatures of `selOf`, and hardwired cells on public
  honest paths (`exOf_subset_public` with `HonestPathsDisjoint`, `layerSlots_public`).
* **The invariant** (`Inv`) and its step: a layer signature moves the register by `LayerRel`
  (`ht₂_signLayerT`: memory after the search against the view, view moved only at programmable
  cells, new cells on the found word's honest paths, output the table's layer signature); a
  signature keeps `Inv` (`inv_of_bottom_none`, `inv_of_bottom_found`, `ht₂_signT`).
* **Results**: `prefixWinFactsOff` (on tables with disjoint honest paths, from a memory with no
  selection), `endReads_wGame_trialHit` (win ≤ event weight + read error + `trialHitMass`), and
  `endReads_wGame_of_trialHit_le` with a bound on the trial-hit mass as a hypothesis.
-/

open Matrix
open scoped ENNReal Kronecker

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid
open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma LeanXmss.RandomPermutationModel

/-! ## The selection function a memory records -/

section sel

/-- Two message-digest inputs of one key and message with the same blocks have the same
randomizer. -/
theorem msgInput_blocks_inj {P : PublicParameter} {l : Layer} {e : KeyIndex} {msg : HashInput}
    {ρ ρ' : Randomizer} (h : blocks (msgInput P l e msg ρ) = blocks (msgInput P l e msg ρ')) :
    ρ = ρ' := by
  have h' := blocks_injective h
  unfold msgInput at h'
  obtain ⟨-, hpay⟩ := thInput_injective _ h'
  obtain ⟨-, hρ⟩ := List.append_inj' hpay (by simp only [littleEndianBytes, List.length_ofFn])
  exact littleEndianBytes_injective 16 hρ

open Classical in
/-- **The selection function a memory records**: at a recorded key, the randomizer whose
message-digest input on `msg` has the recorded block, and the word of the recorded digest. -/
noncomputable def selOf (L : HonestTable) (m : Selections) : SelFn := fun l e msg ↦
  match m l e with
  | none => none
  | some b => if h : ∃ ρ, blocks (msgInput L.param l e msg ρ) = [b.1] then
      (Codeword.decode b.2).map fun x ↦ (h.choose, x) else none

variable {L : HonestTable}

theorem selOf_of_none {m : Selections} {l : Layer} {e : KeyIndex} (hm : m l e = none)
    (msg : HashInput) : selOf L m l e msg = none := by
  unfold selOf
  rw [hm]

theorem selOf_congr {m m' : Selections} {l : Layer} {e : KeyIndex} (h : m l e = m' l e)
    (msg : HashInput) : selOf L m l e msg = selOf L m' l e msg := by
  unfold selOf
  rw [h]

/-- A recorded selection of a randomizer whose input has the recorded block. -/
theorem selOf_of_eq {m : Selections} {l : Layer} {e : KeyIndex} {msg : HashInput} {b : X}
    {y : Digest} {ρ : Randomizer} {x : Encoding} (hm : m l e = some (b, y))
    (hb : blocks (msgInput L.param l e msg ρ) = [b]) (hy : Codeword.decode y = some x) :
    selOf L m l e msg = some (ρ, x) := by
  classical
  have hex : ∃ ρ', blocks (msgInput L.param l e msg ρ') = [(b, y).1] := ⟨ρ, hb⟩
  unfold selOf
  rw [hm]
  dsimp only
  rw [dite_eq_left hex, hy, Option.map_some,
    msgInput_blocks_inj (hex.choose_spec.trans hb.symm)]

/-- **What a recorded selection means**: the memory's entry is the selected message-digest input,
with a digest decoding to the selected word. -/
theorem selOf_spec {m : Selections} {l : Layer} {e : KeyIndex} {msg : HashInput}
    {sel : Randomizer × Encoding} (h : selOf L m l e msg = some sel) :
    ∃ b y, m l e = some (b, y) ∧ blocks (msgInput L.param l e msg sel.1) = [b] ∧
      Codeword.decode y = some sel.2 := by
  classical
  unfold selOf at h
  rcases hm : m l e with _ | ⟨b, y⟩
  · rw [hm] at h
    exact absurd h (by simp)
  · rw [hm] at h
    dsimp only at h
    split_ifs at h with hb
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨b, y, rfl, hb.choose_spec, hx⟩

/-- **A memory records the selections of its own selection function.** -/
theorem recordsSel_selOf (m : Selections) (req : SigningRequest) :
    m.toMemory.RecordsSel L (selOf L m) req := by
  intro l sel hs
  obtain ⟨b, y, hm, hb, hy⟩ := selOf_spec hs
  exact ⟨y, Selections.toMemory_of_blocks hm hb, hy⟩

theorem select_apply_of_ne (m : Selections) {l l' : Layer} {e e' : KeyIndex} (b : X) (y : Digest)
    (h : ¬(l' = l ∧ e' = e)) : m.select l e b y l' e' = m l' e' := by
  unfold Selections.select
  by_cases hl : l' = l
  · subst hl
    rw [Function.update_self, Function.update_of_ne fun he ↦ h ⟨rfl, he⟩]
  · rw [Function.update_of_ne hl]

theorem select_apply_self (m : Selections) (l : Layer) (e : KeyIndex) (b : X) (y : Digest) :
    m.select l e b y l e = some (b, y) := by
  simp [Selections.select]

end sel

/-! ## The disclosures a memory records -/

section disc

/-- **The positions a memory discloses**: the public key's root and, for every recorded key whose
digest decodes to a word, the layer disclosure of that word. -/
def discOf (m : Selections) : Set Pos :=
  {.tree topLayer layerHeight 0} ∪
    {p | ∃ l e b x, m l e = some b ∧ Codeword.decode b.2 = some x ∧ p ∈ layerDisclosed l e x}

theorem layerDisclosed_subset_discOf {m : Selections} {l : Layer} {e : KeyIndex} {b : X × Digest}
    {x : Encoding} (hm : m l e = some b) (hx : Codeword.decode b.2 = some x) :
    layerDisclosed l e x ⊆ discOf m :=
  fun _ hp ↦ Or.inr ⟨l, e, b, x, hm, hx, hp⟩

theorem discOf_select_mono {m : Selections} {l : Layer} {e : KeyIndex} (hm : m l e = none) (b : X)
    (y : Digest) : discOf m ⊆ discOf (m.select l e b y) := by
  rintro p (hp | ⟨l', e', b', x, hm', hx, hp⟩)
  · exact Or.inl hp
  · refine Or.inr ⟨l', e', b', x, ?_, hx, hp⟩
    rw [select_apply_of_ne m b y]
    · exact hm'
    · rintro ⟨rfl, rfl⟩
      rw [hm] at hm'
      exact absurd hm' (by simp)

end disc

/-! ## A layer signature's slots are public -/

section pubSlots

theorem known_chain_from {D : Set Pos} {l : Layer} {e : KeyIndex} {i : ChainIndex} {a : ℕ}
    (ha : Known D (.chain l e i a)) : ∀ j, a ≤ j → j < chainLength → Known D (.chain l e i j) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact fun _ ↦ ha
  | succ j _ ih =>
    intro hj1
    exact Known.chain l e i ⟨j, by omega⟩ (ih (by omega))

theorem known_chain_end {l : Layer} {e : KeyIndex} {x : Encoding} (i : ChainIndex) {j : ℕ}
    (hj : (x i).val ≤ j) (hj' : j < chainLength) : Known (layerDisclosed l e x) (.chain l e i j) :=
  known_chain_from (Known.disclosed _ (Or.inl ⟨i, rfl⟩)) j hj hj'

/-- The children of the node at `lev + 1` on a key's path are known: one on the path, one its
sibling. -/
theorem known_children {l : Layer} {e : KeyIndex} {x : Encoding} {lev : ℕ}
    (hlev : lev < layerHeight)
    (h : Known (layerDisclosed l e x) (.tree l lev (e.val / 2 ^ lev))) :
    Known (layerDisclosed l e x) (.tree l lev (2 * (e.val / 2 ^ (lev + 1)))) ∧
      Known (layerDisclosed l e x) (.tree l lev (2 * (e.val / 2 ^ (lev + 1)) + 1)) := by
  have hs : Known (layerDisclosed l e x) (.tree l lev (Nat.xor (e.val / 2 ^ lev) 1)) :=
    Known.disclosed _ (Or.inr ⟨⟨lev, hlev⟩, rfl⟩)
  have hd : e.val / 2 ^ (lev + 1) = e.val / 2 ^ lev / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hd]
  set a := e.val / 2 ^ lev
  rcases Nat.even_or_odd a with ha | ha
  · have hx : Nat.xor a 1 = a + 1 := Nat.xor_one_of_even ha
    have h2 := Nat.even_iff.1 ha
    rw [hx] at hs
    exact ⟨by rwa [show 2 * (a / 2) = a by omega], by rwa [show 2 * (a / 2) + 1 = a + 1 by omega]⟩
  · have hx : Nat.xor a 1 = a - 1 := Nat.xor_one_of_odd ha
    have h2 := Nat.odd_iff.1 ha
    rw [hx] at hs
    exact ⟨by rwa [show 2 * (a / 2) = a - 1 by omega], by rwa [show 2 * (a / 2) + 1 = a by omega]⟩

/-- The nodes on a key's path are known from its layer disclosure. -/
theorem known_path {l : Layer} {e : KeyIndex} {x : Encoding} :
    ∀ lev ≤ layerHeight, Known (layerDisclosed l e x) (.tree l lev (e.val / 2 ^ lev)) := by
  intro lev hlev
  induction lev with
  | zero =>
    rw [pow_zero, Nat.div_one]
    exact Known.leaf l e fun i ↦ known_chain_end i (by have := (x i).isLt; omega)
      (by decide)
  | succ lev ih =>
    obtain ⟨h1, h2⟩ := known_children (by omega) (ih (by omega))
    exact Known.node l lev _ h1 h2

/-- **A layer signature's slots are public from its disclosure.** -/
theorem layerSlots_public {l : Layer} {e : KeyIndex} {x : Encoding} (he : e.val < keyCount l)
    {s : Slot} (hs : s ∈ layerSlots l e x) : s ∈ Public (layerDisclosed l e x) := by
  refine ⟨inTable_of_mem_layerSlots he hs, ?_⟩
  rcases mem_layerSlots_cases hs with ⟨i, step, hle, rfl⟩ | rfl | ⟨lev, hlev, rfl⟩
  · exact known_chain_end i hle (by have := step.isLt; have : chainLength = 4 := rfl; omega)
  · exact fun i ↦ known_chain_end i (by have := (x i).isLt; omega) (by decide)
  · obtain ⟨h1, h2⟩ := known_children hlev (known_path lev (by omega))
    exact ⟨by omega, h1, h2⟩

end pubSlots

/-! ## Honest-path points and the exempted slots -/

section paths

/-- The cell a read reads, for a hardwired register: held. -/
def InHw (W : Hw X Z) : SpongeQuery X Z → Prop
  | .h z => W.1 z ≠ none
  | .k x => W.2.1 x ≠ none
  | .k' x => W.2.2 x ≠ none

/-- The cell of a program port. -/
def progPt : HwProg X Z → SpongeQuery X Z
  | .programH z _ => .h z
  | .programK x _ => .k x
  | .programK' x _ => .k' x

/-- The points of a slot's honest path. -/
def pathPts (L : HonestTable) (s : Slot) : Set (SpongeQuery X Z) :=
  {q | ∃ i, L.honestInput s = some i ∧ ∃ e ∈ inputReads L.keys L.perm i, e.point = q}

theorem inHw_of_heldBy {W : Hw X Z} {e : SpongeRead X Z} (h : e.HeldBy W.toDbs) :
    InHw W e.point := by
  cases e with
  | h z a => exact fun h0 ↦ by simp [SpongeRead.HeldBy, DbReg.toDbs] at h; rw [h] at h0; cases h0
  | k x a => exact fun h0 ↦ by simp [SpongeRead.HeldBy, DbReg.toDbs] at h; rw [h] at h0; cases h0
  | k' x a => exact fun h0 ↦ by simp [SpongeRead.HeldBy, DbReg.toDbs] at h; rw [h] at h0; cases h0

theorem inputReads_ne_nil (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (input : HashInput) :
    inputReads t π input ≠ [] := by
  intro h
  have := head?_inputReads t π input
  rw [h] at this
  cases this

variable {L : HonestTable}

/-- **The exempted slots are public** when every hardwired cell lies on the honest path of a
public slot and honest paths of distinct slots share no cell. -/
theorem exOf_subset_public (hd : HonestPathsDisjoint L) {W : Hw X Z} {Dsc : Set Pos}
    (hW : ∀ q, InHw W q → ∃ s ∈ Public Dsc, q ∈ pathPts L s) : exOf L W ⊆ Public Dsc := by
  rintro s' ⟨hs', hheld⟩
  obtain ⟨i', hi'⟩ : ∃ i', L.honestInput s' = some i' := ⟨_, by
    rw [HonestTable.honestInput, ite_eq_left hs']⟩
  obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil _ (inputReads_ne_nil L.keys L.perm i')
  obtain ⟨s, hs, i, hi, e₁, he₁, hpt⟩ := hW _ (inHw_of_heldBy (hheld i' hi' e₀ he₀))
  by_cases hss : s' = s
  · exact hss ▸ hs
  · exact absurd hpt.symm (hd s' s i' i hs' hs.1 hss hi' hi e₀ he₀ e₁ he₁)

/-- **A realized program port of a layer signature's slot programs a point of the slot's honest
path.** -/
theorem progPt_mem_pathPts {l : Layer} {e : KeyIndex} {x : Encoding} {s : Slot}
    (hs : s ∈ layerSlots l e x) (hin : InTable s) {p : LazyProg X Z HPos XD}
    (hp : p ∈ slotPorts (pubOf L) s) : progPt (p.realize (valueAt L)) ∈ pathPts L s := by
  set f := extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L)) with hf_def
  have hf : ∀ q ∈ slotNeed s, f q = valuePos L q := fun q hq ↦ by
    rw [hf_def, extendVals_restrictTo (inl_mem_inlSet.mpr hq)]
    rfl
  have hin' : L.honestInput s = some (slotInput (pubOf L) s f) := by
    rw [HonestTable.honestInput, ite_eq_left hin, slotInput, slotPayload_eq L hs hf]
    rfl
  simp only [slotPorts, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  obtain ⟨j, hj, rfl | rfl | rfl⟩ := hp
  · obtain ⟨a, ha⟩ := cellK_mem_inputReads L s f hj
    exact ⟨_, hin', _, ha, rfl⟩
  · obtain ⟨a, ha⟩ := cellK'_mem_inputReads L s f hj
    exact ⟨_, hin', _, ha, rfl⟩
  · obtain ⟨a, ha⟩ := mem_hCells.1 (cellH_mem_hCells_inputReads L s f hj)
    exact ⟨_, hin', _, ha, rfl⟩

/-- **A realized program port of an in-table layer signature programs a cell of `tableHw L`.** -/
theorem inHw_tableHw_progPt {l : Layer} {e : KeyIndex} {x : Encoding} (he : e.val < keyCount l)
    {s : Slot} (hs : s ∈ layerSlots l e x) {p : LazyProg X Z HPos XD}
    (hp : p ∈ slotPorts (pubOf L) s) : InHw (tableHw L) (progPt (p.realize (valueAt L))) := by
  have h := progOf_tableHw L (c := p.realize (valueAt L)) ⟨l, e, x, s, he, hs, p, hp, rfl⟩
  revert h
  cases p.realize (valueAt L) with
  | programH z a => exact fun h h0 ↦ by rw [h] at h0; cases h0
  | programK z a => exact fun h h0 ↦ by rw [h] at h0; cases h0
  | programK' z a => exact fun h h0 ↦ by rw [h] at h0; cases h0

end paths

/-! ## The trial-hit event -/

section hit

/-- The message the top key `e` signs: the root of the bottom tree under it. -/
def topMsg (L : HonestTable) (e : KeyIndex) : HashInput :=
  littleEndianBytes 16 (L.treeValue bottomLayer layerHeight e.val)

/-- The randomizer base of the top key `e`. -/
def topBase (L : HonestTable) (e : KeyIndex) : Randomizer :=
  L.randomizerBase topLayer e (topMsg L e)

/-- Trial `n` of the top key `e`'s randomizer search. -/
def topTrial (L : HonestTable) (e : KeyIndex) (n : ℕ) : HashInput :=
  msgInput L.param topLayer e (topMsg L e) (topBase L e + BitVec.ofNat digestBits n)

/-- **The trial-hit event** of the (decompressed) register: some trial of some top key's
randomizer search, evaluated against the register's view, reads a cell the game may program. -/
def TrialHit (L : HonestTable) : Set (HwReg X Z (Finset HPos × Selections)) :=
  {s | ∃ e : KeyIndex, e.val < keyCount topLayer ∧ ∃ n < randomizerAttemptLimit,
    ∃ rd ∈ inputReads (regFns s) L.perm (topTrial L e n), InHw (tableHw L) rd.point}

/-- Two views agree off the cells of `H`. -/
def OffAgree (H : Hw X Z) (t t' : SpongeKeys X Z) : Prop :=
  (∀ z, H.1 z = none → t.1 z = t'.1 z) ∧ (∀ x, H.2.1 x = none → t.2.1 x = t'.2.1 x) ∧
    ∀ x, H.2.2 x = none → t.2.2 x = t'.2.2 x

theorem OffAgree.symm {H : Hw X Z} {t t' : SpongeKeys X Z} (h : OffAgree H t t') :
    OffAgree H t' t :=
  ⟨fun z hz ↦ (h.1 z hz).symm, fun x hx ↦ (h.2.1 x hx).symm, fun x hx ↦ (h.2.2 x hx).symm⟩

theorem OffAgree.trans {H : Hw X Z} {t t' t'' : SpongeKeys X Z} (h : OffAgree H t t')
    (h' : OffAgree H t' t'') : OffAgree H t t'' :=
  ⟨fun z hz ↦ (h.1 z hz).trans (h'.1 z hz), fun x hx ↦ (h.2.1 x hx).trans (h'.2.1 x hx),
    fun x hx ↦ (h.2.2 x hx).trans (h'.2.2 x hx)⟩

theorem offAgree_refl (H : Hw X Z) (t : SpongeKeys X Z) : OffAgree H t t :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem answeredBy_of_offAgree {H : Hw X Z} {t t' : SpongeKeys X Z} (h : OffAgree H t t')
    {e : SpongeRead X Z} (he : e.AnsweredBy t) (hn : ¬InHw H e.point) : e.AnsweredBy t' := by
  cases e with
  | h z a => exact (h.1 z (not_not.1 hn)).symm.trans he
  | k x a => exact (h.2.1 x (not_not.1 hn)).symm.trans he
  | k' x a => exact (h.2.2 x (not_not.1 hn)).symm.trans he

/-- **Views agreeing off `H` read alike** an input whose reads avoid `H`. -/
theorem inputReads_eq_of_offAgree {H : Hw X Z} {t t' : SpongeKeys X Z} (h : OffAgree H t t')
    (π : Equiv.Perm (X × Z)) (input : HashInput)
    (hn : ∀ rd ∈ inputReads t π input, ¬InHw H rd.point) :
    inputReads t' π input = inputReads t π input ∧
      absorb (spongePerm t' π) (blocks input) = absorb (spongePerm t π) (blocks input) :=
  spongeReads_congr π (blocks input) fun e he ↦
    answeredBy_of_offAgree h (spongeReads_answeredBy π t _ e he) (hn e he)

/-- **The trial-hit event depends only on the view off the programmable cells.** -/
theorem trialHit_iff_of_offAgree {L : HonestTable} {s s' : HwReg X Z (Finset HPos × Selections)}
    (h : OffAgree (tableHw L) (regFns s) (regFns s')) : s ∈ TrialHit L ↔ s' ∈ TrialHit L := by
  have key : ∀ {s s' : HwReg X Z (Finset HPos × Selections)},
      OffAgree (tableHw L) (regFns s) (regFns s') → s' ∈ TrialHit L → s ∈ TrialHit L := by
    intro s s' h hs'
    obtain ⟨e, he, n, hn, rd, hrd, hin⟩ := hs'
    by_contra hs
    have hav : ∀ rd ∈ inputReads (regFns s) L.perm (topTrial L e n),
        ¬InHw (tableHw L) rd.point := fun rd hrd hin ↦ hs ⟨e, he, n, hn, rd, hrd, hin⟩
    rw [(inputReads_eq_of_offAgree h L.perm _ hav).1] at hrd
    exact hav rd hrd hin
  exact ⟨key h.symm, key h⟩

end hit

/-! ## The values a signature reads from a reveal -/

section values

variable (L : HonestTable)

theorem valuePos_cpos_digit (l : Layer) (e : KeyIndex) (i : ChainIndex) (x : Encoding) :
    valuePos L (cpos l e i (x i).val) = L.chainValue l e i (x i).val := by
  rw [valuePos_cpos, Nat.mod_eq_of_lt (x i).isLt]

theorem valuePos_siblingPos (l : Layer) (e : KeyIndex) (level : Fin layerHeight) :
    valuePos L (siblingPos l e level) = L.authPath l e level := by
  have he := keyIndex_lt_two_pow e
  have hlt : Nat.xor (e.val / 2 ^ level.val) 1 < 2 ^ 32 :=
    Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt he) (by norm_num)
  rw [siblingPos, valuePos_tpos, Nat.mod_eq_of_lt (show level.val < layerHeight + 1 by omega),
    Nat.mod_eq_of_lt hlt]
  rfl

theorem valuePos_rootPos : valuePos L rootPos = L.treeValue topLayer layerHeight 0 := by
  rw [rootPos, valuePos_tpos]
  rfl

theorem valuePos_botRootPos (r : SigningRequest) :
    valuePos L (botRootPos r) = L.bottomRoot r.leafIndex := by
  have h := keyIndexOnLayer_lt r.leafIndex topLayer
  have hk : keyCount topLayer ≤ 2 ^ 32 := keyCount_le topLayer
  rw [botRootPos, valuePos_tpos, Nat.mod_eq_of_lt (show layerHeight < layerHeight + 1 by omega),
    Nat.mod_eq_of_lt (by omega)]
  rfl

theorem botRootPos_mem_layerNeed (r : SigningRequest) (x : Encoding) :
    botRootPos r ∈ layerNeed bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) x := by
  have hs := node_mem_layerSlots (l := bottomLayer) (e := keyIndexOnLayer r.leafIndex bottomLayer)
    x (lev := layerHeight - 1) (by decide)
  have hn := slotNeed_subset_needUnion hs
  simp only [layerNeed, Finset.mem_union]
  refine Or.inl (Or.inl (hn ?_))
  have he : (keyIndexOnLayer r.leafIndex bottomLayer).val / 2 ^ (layerHeight - 1 + 1) =
      (keyIndexOnLayer r.leafIndex topLayer).val := by
    simp [keyIndexOnLayer, bottomLayer, topLayer, layerHeight]
  rw [he]
  simp only [slotNeed, Finset.mem_insert, Finset.mem_singleton, botRootPos]
  exact Or.inr (Or.inr rfl)

end values

/-! ## From recorded selections to the prefix facts -/

section facts

variable {L : HonestTable}

theorem layer_cases (l : Layer) : l = bottomLayer ∨ l = topLayer := by
  rcases l with ⟨n, hn⟩
  have hn' : n < 2 := hn
  interval_cases n
  · exact Or.inl rfl
  · exact Or.inr rfl

variable (L) in
/-- **Every recorded key was requested**: its block is that of a message-digest input of the
request's message on that layer. -/
def RecFrom (rs : List SigningRequest) (m : Selections) : Prop :=
  ∀ l e b, m l e = some b → ∃ r ∈ rs, keyIndexOnLayer r.leafIndex l = e ∧
    ∃ ρ, blocks (msgInput L.param l e (layerMessage L r l) ρ) = [b.1]

theorem RecFrom.mono {rs rs' : List SigningRequest} {m : Selections} (h : RecFrom L rs m)
    (hs : rs ⊆ rs') : RecFrom L rs' m := fun l e b hb ↦ by
  obtain ⟨r, hr, h'⟩ := h l e b hb
  exact ⟨r, hs hr, h'⟩

/-- **The memory's disclosures are those of its selection function on the requests.** -/
theorem discOf_subset_selDisclosures {rs : List SigningRequest} {m : Selections}
    (h : RecFrom L rs m) : discOf m ⊆ L.selDisclosures (selOf L m) rs := by
  rintro p (hp | ⟨l, e, b, x, hm, hx, hp⟩)
  · exact Or.inl hp
  obtain ⟨r, hr, hkey, ρ, hb⟩ := h l e b hm
  have hsel : selOf L m l e (layerMessage L r l) = some (ρ, x) :=
    selOf_of_eq (b := b.1) (y := b.2) hm hb hx
  refine Or.inr (Set.mem_iUnion₂.2 ⟨r, hr, ?_⟩)
  subst hkey
  unfold HonestTable.selDisclosedBy
  rcases layer_cases l with rfl | rfl
  · rw [layerMessage_bottom] at hsel
    rw [hsel]
    exact Or.inl hp
  · rw [layerMessage_top] at hsel
    rw [hsel]
    exact Or.inr hp

theorem selSignature_congr {S S' : SelFn} {r : SigningRequest}
    (hb : S bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) (littleEndianBytes 32 r.message) =
      S' bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) (littleEndianBytes 32 r.message))
    (ht : S topLayer (keyIndexOnLayer r.leafIndex topLayer)
        (littleEndianBytes 16 (L.bottomRoot r.leafIndex)) =
      S' topLayer (keyIndexOnLayer r.leafIndex topLayer)
        (littleEndianBytes 16 (L.bottomRoot r.leafIndex))) :
    L.selSignature S r = L.selSignature S' r := by
  simp only [HonestTable.selSignature, HonestTable.selLayerSignature, hb, ht]

theorem selSignature_of_bottom_none {S : SelFn} {r : SigningRequest}
    (h : S bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) (littleEndianBytes 32 r.message) =
      none) : L.selSignature S r = none := by
  simp only [HonestTable.selSignature, HonestTable.selLayerSignature, h, Option.map_none,
    Option.bind_none]

/-- **The prefix facts** from a memory whose recorded keys were requested, a transcript of its
selection function's signatures, and hardwired cells on public honest paths. -/
theorem preFacts_of (hd : HonestPathsDisjoint L) {pre : PublicKey × (Forgery × SignLog)}
    {b : Hw X Z × (Finset HPos × Selections)} (hpk : pre.1 = L.publicKey)
    (hrec : RecFrom L (pre.2.2.map Sigma.fst) b.2.2)
    (hsig : ∀ r ∈ pre.2.2, r.2 = L.selSignature (selOf L b.2.2) r.1)
    (hcells : ∀ q, InHw b.1 q → ∃ sl ∈ Public (discOf b.2.2), q ∈ pathPts L sl) :
    PreFacts L pre b :=
  ⟨hpk, selOf L b.2.2, hsig, fun _ _ ↦ recordsSel_selOf _ _,
    (exOf_subset_public hd hcells).trans (public_mono (discOf_subset_selDisclosures hrec))⟩

end facts

/-! ## The randomizer search as a function of the view -/

section grind

variable (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter) (l : Layer)
  (e : KeyIndex) (msg : HashInput) (base : Randomizer)

/-- A found selection's word is the decoding of its trial's digest. -/
theorem decode_of_grindV : ∀ {n trial : ℕ} {sel : Randomizer × Encoding},
    grindV t π P l e msg base n trial = some sel →
      Codeword.decode (trialDigest t π P l e msg sel.1) = some sel.2
  | 0, _, _, h => by simp [grindV] at h
  | n + 1, trial, sel, h => by
    simp only [grindV] at h
    split at h
    · next x hx =>
      cases h
      exact hx
    · exact decode_of_grindV h

/-- The search depends on the view only through the digests of its trials. -/
theorem grindV_congr {t t' : SpongeKeys X Z} :
    ∀ {n trial : ℕ}, (∀ k, trial ≤ k → k < trial + n →
      trialDigest t π P l e msg (base + BitVec.ofNat digestBits k) =
        trialDigest t' π P l e msg (base + BitVec.ofNat digestBits k)) →
      grindV t π P l e msg base n trial = grindV t' π P l e msg base n trial
  | 0, _, _ => rfl
  | n + 1, trial, h => by
    simp only [grindV]
    rw [h trial le_rfl (by omega), grindV_congr fun k hk hk' ↦ h k (by omega) (by omega)]

theorem grindMemV_of_some {n trial : ℕ} {m : Selections} {b : X × Digest}
    (hm : m l e = some b) : grindMemV t π P l e msg base n trial m = m := by
  unfold grindMemV
  rw [hm]

theorem grindMemV_of_none {n trial : ℕ} {m : Selections}
    (hg : grindV t π P l e msg base n trial = none) :
    grindMemV t π P l e msg base n trial m = m := by
  unfold grindMemV
  rw [hg]
  cases m l e <;> rfl

theorem grindMemV_of_found {n trial : ℕ} {m : Selections} (hm : m l e = none)
    {sel : Randomizer × Encoding} (hg : grindV t π P l e msg base n trial = some sel) :
    grindMemV t π P l e msg base n trial m =
      m.select l e ((blocks (msgInput P l e msg sel.1)).headD 0)
        (trialDigest t π P l e msg sel.1) := by
  unfold grindMemV
  rw [hm, hg]

theorem grindMemV_apply_of_ne {n trial : ℕ} (m : Selections) {l' : Layer} {e' : KeyIndex}
    (h : ¬(l' = l ∧ e' = e)) : grindMemV t π P l e msg base n trial m l' e' = m l' e' := by
  rcases hm : m l e with _ | b
  · rcases hg : grindV t π P l e msg base n trial with _ | sel
    · rw [grindMemV_of_none t π P l e msg base hg]
    · rw [grindMemV_of_found t π P l e msg base hm hg]
      exact select_apply_of_ne m _ _ h
  · rw [grindMemV_of_some t π P l e msg base hm]

end grind

/-! ## The records of the randomizer searches -/

section views

variable (L : HonestTable)

/-- The selection of a label's randomizer search against a view. -/
def labSel (t : SpongeKeys X Z) (lab : RLabel) : Option (Randomizer × Encoding) :=
  grindV t L.perm L.param lab.layer lab.key lab.msg (valueAt L (.inr lab)) randomizerAttemptLimit 0

/-- The memory after a label's randomizer search against a view. -/
noncomputable def labMem (t : SpongeKeys X Z) (lab : RLabel) (m : Selections) : Selections :=
  grindMemV t L.perm L.param lab.layer lab.key lab.msg (valueAt L (.inr lab))
    randomizerAttemptLimit 0 m

/-- The record of a found selection of a label against a view: its block and digest. -/
def recOf (t : SpongeKeys X Z) (lab : RLabel) (sel : Randomizer × Encoding) : X × Digest :=
  ((blocks (msgInput L.param lab.layer lab.key lab.msg sel.1)).headD 0,
    trialDigest t L.perm L.param lab.layer lab.key lab.msg sel.1)

/-- The layer signature of a selection, with the table's values, and the revealed values. -/
def labSig (lab : RLabel) (sel : Randomizer × Encoding) : LayerSignature × (ValPos → Digest) :=
  (⟨sel.1, fun i ↦ L.chainValue lab.layer lab.key i (sel.2 i).val, L.authPath lab.layer lab.key⟩,
    extendVals (restrictTo (inlSet (layerNeed lab.layer lab.key sel.2)) (valueAt L)))

/-- The label of the top key `e`'s search: the key with the root of the bottom tree under it. -/
def topLab (e : KeyIndex) : RLabel :=
  .inr (e, L.treeValue bottomLayer layerHeight e.val)

/-- The record of the top key `e`'s randomizer search against the view `t`. -/
def topRec (t : SpongeKeys X Z) (e : KeyIndex) : Option (X × Digest) :=
  (labSel L t (topLab L e)).map (recOf L t (topLab L e))

variable {L}

theorem labMem_apply_of_ne (t : SpongeKeys X Z) (lab : RLabel) (m : Selections) {l : Layer}
    {e : KeyIndex} (h : ¬(l = lab.layer ∧ e = lab.key)) : labMem L t lab m l e = m l e :=
  grindMemV_apply_of_ne _ _ _ _ _ _ _ m h

theorem labMem_of_some {t : SpongeKeys X Z} {lab : RLabel} {m : Selections} {b : X × Digest}
    (hm : m lab.layer lab.key = some b) : labMem L t lab m = m :=
  grindMemV_of_some _ _ _ _ _ _ _ hm

theorem labMem_of_none {t : SpongeKeys X Z} {lab : RLabel} {m : Selections}
    (hg : labSel L t lab = none) : labMem L t lab m = m :=
  grindMemV_of_none _ _ _ _ _ _ _ hg

theorem labMem_self_of_none {t : SpongeKeys X Z} {lab : RLabel} {m : Selections}
    (hm : m lab.layer lab.key = none) :
    labMem L t lab m lab.layer lab.key = (labSel L t lab).map (recOf L t lab) := by
  rcases hg : labSel L t lab with _ | sel
  · rw [labMem_of_none hg, hm, Option.map_none]
  · rw [labMem, grindMemV_of_found _ _ _ _ _ _ _ hm hg, select_apply_self, Option.map_some]
    rfl

theorem labMem_eq_or (t : SpongeKeys X Z) (lab : RLabel) (m : Selections) :
    labMem L t lab m = m ∨ (m lab.layer lab.key = none ∧ ∃ sel, labSel L t lab = some sel ∧
      labMem L t lab m =
        m.select lab.layer lab.key (recOf L t lab sel).1 (recOf L t lab sel).2) := by
  rcases hm : m lab.layer lab.key with _ | b
  · rcases hg : labSel L t lab with _ | sel
    · exact Or.inl (labMem_of_none hg)
    · exact Or.inr ⟨rfl, sel, rfl, grindMemV_of_found _ _ _ _ _ _ _ hm hg⟩
  · exact Or.inl (labMem_of_some hm)

theorem decode_recOf {t : SpongeKeys X Z} {lab : RLabel} {sel : Randomizer × Encoding}
    (h : labSel L t lab = some sel) : Codeword.decode (recOf L t lab sel).2 = some sel.2 :=
  decode_of_grindV _ _ _ _ _ _ _ h

theorem blocks_recOf (t : SpongeKeys X Z) (lab : RLabel) (sel : Randomizer × Encoding) :
    blocks (msgInput L.param lab.layer lab.key lab.msg sel.1) = [(recOf L t lab sel).1] :=
  blocks_msgInput _ _ _ lab.length_msg_le _

/-- **A found selection is what the memory recording it selects.** -/
theorem selOf_recOf {t : SpongeKeys X Z} {lab : RLabel} {sel : Randomizer × Encoding}
    (h : labSel L t lab = some sel) {m : Selections}
    (hm : m lab.layer lab.key = some (recOf L t lab sel)) :
    selOf L m lab.layer lab.key lab.msg = some sel :=
  selOf_of_eq hm (blocks_recOf t lab sel) (decode_recOf h)

theorem discOf_labMem (t : SpongeKeys X Z) (lab : RLabel) (m : Selections) :
    discOf m ⊆ discOf (labMem L t lab m) := by
  rcases labMem_eq_or t lab m with h | ⟨hm, _, _, h⟩ <;> rw [h]
  exact discOf_select_mono hm _ _

theorem trialDigest_eq_absorb (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z))
    (P : PublicParameter) (l : Layer) (e : KeyIndex) (msg : HashInput) (ρ : Randomizer) :
    trialDigest t π P l e msg ρ =
      trunc128 (absorb (spongePerm t π) (blocks (msgInput P l e msg ρ))).1 :=
  rfl

/-- **Off the trial-hit event, the top keys' trials read alike in views agreeing off the
programmable cells.** -/
theorem trialDigest_topLab_congr {s : HwReg X Z (Finset HPos × Selections)} (hs : s ∉ TrialHit L)
    {t' : SpongeKeys X Z} (h : OffAgree (tableHw L) (regFns s) t') {e : KeyIndex}
    (he : e.val < keyCount topLayer) {k : ℕ} (hk : k < randomizerAttemptLimit) :
    trialDigest (regFns s) L.perm L.param topLayer e (topMsg L e)
        (topBase L e + BitVec.ofNat digestBits k) =
      trialDigest t' L.perm L.param topLayer e (topMsg L e)
        (topBase L e + BitVec.ofNat digestBits k) := by
  have hav : ∀ rd ∈ inputReads (regFns s) L.perm (topTrial L e k), ¬InHw (tableHw L) rd.point :=
    fun rd hrd hin ↦ hs ⟨e, he, k, hk, rd, hrd, hin⟩
  have hab := (inputReads_eq_of_offAgree h L.perm _ hav).2
  rw [trialDigest_eq_absorb, trialDigest_eq_absorb]
  exact congrArg (fun st : X × Z ↦ trunc128 st.1) hab.symm

theorem labSel_topLab_congr {s : HwReg X Z (Finset HPos × Selections)} (hs : s ∉ TrialHit L)
    {t' : SpongeKeys X Z} (h : OffAgree (tableHw L) (regFns s) t') {e : KeyIndex}
    (he : e.val < keyCount topLayer) :
    labSel L t' (topLab L e) = labSel L (regFns s) (topLab L e) :=
  (grindV_congr _ _ _ _ _ _ fun k _ hk ↦
    trialDigest_topLab_congr hs h he (by simpa using hk)).symm

theorem grindV_spec (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
    (l : Layer) (e : KeyIndex) (msg : HashInput) (base : Randomizer) :
    ∀ {n trial : ℕ} {sel : Randomizer × Encoding}, grindV t π P l e msg base n trial = some sel →
      ∃ k, trial ≤ k ∧ k < trial + n ∧ sel.1 = base + BitVec.ofNat digestBits k
  | 0, _, _, h => by simp [grindV] at h
  | n + 1, trial, sel, h => by
    simp only [grindV] at h
    split at h
    · cases h
      exact ⟨trial, le_rfl, by omega, rfl⟩
    · obtain ⟨k, hk, hk', hs⟩ := grindV_spec t π P l e msg base h
      exact ⟨k, by omega, by omega, hs⟩

theorem topRec_congr {s : HwReg X Z (Finset HPos × Selections)} (hs : s ∉ TrialHit L)
    {t' : SpongeKeys X Z} (h : OffAgree (tableHw L) (regFns s) t') {e : KeyIndex}
    (he : e.val < keyCount topLayer) : topRec L t' e = topRec L (regFns s) e := by
  unfold topRec
  rw [labSel_topLab_congr hs h he]
  rcases hg : labSel L (regFns s) (topLab L e) with _ | sel
  · simp only [Option.map_none]
  · obtain ⟨k, -, hk, hsel⟩ := grindV_spec _ _ _ _ _ _ _ hg
    have hsel' : sel.1 = topBase L e + BitVec.ofNat digestBits k := hsel
    simp only [Option.map_some, recOf, Option.some.injEq, Prod.mk.injEq, true_and]
    show trialDigest t' L.perm L.param topLayer e (topMsg L e) sel.1 =
      trialDigest (regFns s) L.perm L.param topLayer e (topMsg L e) sel.1
    rw [hsel']
    exact (trialDigest_topLab_congr hs h he (k := k) (by simpa using hk)).symm

end views

/-! ## The invariant and a signature's step -/

section inv

variable (L : HonestTable)

/-- **A layer signature's move of the register** from `s` to `s'` with output `o`: no empty
cell, the memory after the label's search against the view, the view moved only at programmable
cells, new hardwired cells only on the honest paths of the found word's slots, and the output the
table's layer signature of the found selection. -/
structure LayerRel (lab : RLabel) (s : HwReg X Z (Finset HPos × Selections))
    (o : Option (LayerSignature × (ValPos → Digest))) (s' : HwReg X Z (Finset HPos × Selections)) :
    Prop where
  noBot : NoBot s'
  mem : s'.2.2.2 = labMem L (regFns s) lab s.2.2.2
  view : OffAgree (tableHw L) (regFns s) (regFns s')
  cells : ∀ q, InHw s'.2.1 q → InHw s.2.1 q ∨
    ∃ sel, labSel L (regFns s) lab = some sel ∧ ∃ sl ∈ layerSlots lab.layer lab.key sel.2,
      q ∈ pathPts L sl
  out : o = (labSel L (regFns s) lab).map (labSig L lab)

/-- **A signature's move of the register**: the bottom layer, then (if it signed) the top layer on
the bottom root it revealed; the answer as `signT` assembles it. -/
def SignRel (r : SigningRequest) (s : HwReg X Z (Finset HPos × Selections)) (sig : Option Signature)
    (s' : HwReg X Z (Finset HPos × Selections)) : Prop :=
  (LayerRel L (botLabel r) s none s' ∧ sig = none) ∨
    ∃ sB bottom f, LayerRel L (botLabel r) s (some (bottom, f)) sB ∧ ∃ oT,
      LayerRel L (topLabel r (f (botRootPos r))) sB oT s' ∧
      sig = oT.map fun top ↦ ⟨r.leafIndex, fun l ↦ if l = bottomLayer then bottom else top.1⟩

/-- **The facts off the trial-hit event** for a transcript `log`: hardwired cells on public honest
paths, transcript signatures of the memory's selection function, and every top key recorded, or
signed under by a request whose bottom layer is selected, recording its search against the view. -/
structure InvFacts (log : SignLog) (s : HwReg X Z (Finset HPos × Selections)) : Prop where
  cells : ∀ q, InHw s.2.1 q → ∃ sl ∈ Public (discOf s.2.2.2), q ∈ pathPts L sl
  sigs : ∀ r ∈ log, r.2 = L.selSignature (selOf L s.2.2.2) r.1
  top : ∀ e, (s.2.2.2 topLayer e ≠ none ∨ ∃ r ∈ log, keyIndexOnLayer r.1.leafIndex topLayer = e ∧
    selOf L s.2.2.2 bottomLayer (keyIndexOnLayer r.1.leafIndex bottomLayer)
      (littleEndianBytes 32 r.1.message) ≠ none) → s.2.2.2 topLayer e = topRec L (regFns s) e

/-- **The prefix invariant** between signing requests, after the transcript `log`: no empty cell,
every recorded key requested, and off the trial-hit event, for distinct leaf indices, the facts. -/
def Inv (log : SignLog) : Set (HwReg X Z (Finset HPos × Selections)) :=
  {s | NoBot s ∧ RecFrom L (log.map Sigma.fst) s.2.2.2 ∧
    (s ∉ TrialHit L → ((log.map Sigma.fst).map SigningRequest.leafIndex).Nodup → InvFacts L log s)}

variable {L}

theorem keyIndexOnLayer_bottom_val (idx : LeafIndex) :
    (keyIndexOnLayer idx bottomLayer).val = idx.val := by
  simp [keyIndexOnLayer, bottomLayer]

theorem topLabel_eq_topLab (r : SigningRequest) :
    topLabel r (L.bottomRoot r.leafIndex) = topLab L (keyIndexOnLayer r.leafIndex topLayer) :=
  rfl

theorem LayerRel.offAgree_trialHit {lab : RLabel} {s s' : HwReg X Z (Finset HPos × Selections)}
    {o : Option (LayerSignature × (ValPos → Digest))} (h : LayerRel L lab s o s') :
    s ∈ TrialHit L ↔ s' ∈ TrialHit L :=
  trialHit_iff_of_offAgree h.view

/-- The revealed values of a found bottom selection give the bottom root. -/
theorem bottomRoot_of_out {r : SigningRequest} {s sB : HwReg X Z (Finset HPos × Selections)}
    {bottom : LayerSignature} {f : ValPos → Digest}
    (h : LayerRel L (botLabel r) s (some (bottom, f)) sB) :
    ∃ sel, labSel L (regFns s) (botLabel r) = some sel ∧ bottom = (labSig L (botLabel r) sel).1 ∧
      f (botRootPos r) = L.bottomRoot r.leafIndex := by
  have ho := h.out
  rcases hg : labSel L (regFns s) (botLabel r) with _ | sel
  · rw [hg] at ho
    cases ho
  · rw [hg, Option.map_some, Option.some.injEq] at ho
    refine ⟨sel, rfl, (congrArg Prod.fst ho), ?_⟩
    have hf : f = (labSig L (botLabel r) sel).2 := congrArg Prod.snd ho
    rw [hf]
    show extendVals (restrictTo (inlSet (layerNeed bottomLayer
      (keyIndexOnLayer r.leafIndex bottomLayer) sel.2)) (valueAt L)) (botRootPos r) = _
    rw [extendVals_restrictTo (inl_mem_inlSet.mpr (botRootPos_mem_layerNeed r sel.2)), valueAt_inl,
      valuePos_botRootPos]

/-- A label's search keeps the recorded keys requested. -/
theorem recFrom_labMem {rs : List SigningRequest} {m : Selections} (h : RecFrom L rs m)
    {r : SigningRequest} (hr : r ∈ rs) {lab : RLabel}
    (hk : lab.key = keyIndexOnLayer r.leafIndex lab.layer)
    (hmsg : lab.msg = layerMessage L r lab.layer) (t : SpongeKeys X Z) :
    RecFrom L rs (labMem L t lab m) := by
  rcases labMem_eq_or t lab m with he | ⟨-, sel, -, he⟩ <;> rw [he]
  · exact h
  intro l e b hb
  by_cases hle : l = lab.layer ∧ e = lab.key
  · obtain ⟨rfl, rfl⟩ := hle
    rw [select_apply_self, Option.some.injEq] at hb
    subst hb
    refine ⟨r, hr, hk.symm, sel.1, ?_⟩
    rw [← hmsg]
    exact blocks_recOf t lab sel
  · rw [select_apply_of_ne m _ _ hle] at hb
    exact h l e b hb

end inv

/-! ## A signature keeps the invariant -/

section step

variable {L : HonestTable}

theorem nodup_of_snoc {α : Type*} {l : List α} {a : α} (h : (l ++ [a]).Nodup) :
    l.Nodup ∧ a ∉ l := by
  refine ⟨h.sublist (List.sublist_append_left _ _), fun ha ↦ ?_⟩
  have h' := List.nodup_append_comm.1 h
  exact (List.nodup_cons.1 h').1 ha

theorem bottomKey_ne {rs : List SigningRequest} {r r' : SigningRequest}
    (hn : r.leafIndex ∉ rs.map SigningRequest.leafIndex) (hr' : r' ∈ rs) :
    keyIndexOnLayer r'.leafIndex bottomLayer ≠ keyIndexOnLayer r.leafIndex bottomLayer := by
  intro he
  have hv := congrArg Fin.val he
  rw [keyIndexOnLayer_bottom_val, keyIndexOnLayer_bottom_val] at hv
  exact hn (List.mem_map.2 ⟨r', hr', Fin.ext hv⟩)

/-- A fresh leaf index's bottom key is not recorded. -/
theorem bottom_none {rs : List SigningRequest} {m : Selections} (h : RecFrom L rs m)
    {r : SigningRequest} (hn : r.leafIndex ∉ rs.map SigningRequest.leafIndex) :
    m bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) = none := by
  rcases hm : m bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer) with _ | b
  · rfl
  · obtain ⟨r', hr', hk, -⟩ := h _ _ b hm
    exact absurd hk (bottomKey_ne hn hr')

theorem topKey_lt_of {rs : List SigningRequest} {m : Selections} (h : RecFrom L rs m) {e : KeyIndex}
    (hm : m topLayer e ≠ none) : e.val < keyCount topLayer := by
  rcases hb : m topLayer e with _ | b
  · exact absurd hb hm
  · obtain ⟨r', -, rfl, -⟩ := h _ _ b hb
    exact keyIndexOnLayer_lt _ _

theorem bottomLayer_ne_topLayer : bottomLayer ≠ topLayer := by decide

/-- **A signature with its bottom search failing keeps the invariant.** -/
theorem inv_of_bottom_none {log : SignLog} {r : SigningRequest}
    {s s' : HwReg X Z (Finset HPos × Selections)} (hs : s ∈ Inv L log)
    (hL : LayerRel L (botLabel r) s none s') : s' ∈ Inv L (log ++ [⟨r, none⟩]) := by
  obtain ⟨-, hrec, hfacts⟩ := hs
  have hg : labSel L (regFns s) (botLabel r) = none := by
    have ho := hL.out
    rcases hg : labSel L (regFns s) (botLabel r) with _ | sel
    · rfl
    · rw [hg] at ho
      cases ho
  have hm' : s'.2.2.2 = s.2.2.2 := hL.mem.trans (labMem_of_none hg)
  have hmap : (log ++ [⟨r, none⟩] : SignLog).map Sigma.fst = log.map Sigma.fst ++ [r] := by simp
  refine ⟨hL.noBot, ?_, fun hhit hnd ↦ ?_⟩
  · rw [hmap, hm']
    exact hrec.mono (List.subset_append_left _ _)
  rw [hmap, List.map_append, List.map_singleton] at hnd
  obtain ⟨hnd, hn⟩ := nodup_of_snoc hnd
  have hs : s ∉ TrialHit L := fun h ↦ hhit (hL.offAgree_trialHit.1 h)
  have F := hfacts hs hnd
  have hb0 := bottom_none hrec hn
  have hsb : selOf L s.2.2.2 bottomLayer (keyIndexOnLayer r.leafIndex bottomLayer)
      (littleEndianBytes 32 r.message) = none := selOf_of_none hb0 _
  refine ⟨fun q hq ↦ ?_, fun r'' hr'' ↦ ?_, fun e he ↦ ?_⟩
  · rcases hL.cells q hq with hq | ⟨sel, hsel, -⟩
    · rw [hm']
      exact F.cells q hq
    · rw [hg] at hsel
      cases hsel
  · rw [hm']
    rcases List.mem_append.1 hr'' with hr'' | hr''
    · exact F.sigs r'' hr''
    · rw [List.mem_singleton] at hr''
      subst hr''
      exact (selSignature_of_bottom_none hsb).symm
  · rw [hm'] at he ⊢
    have he' : s.2.2.2 topLayer e ≠ none ∨ ∃ r ∈ log, keyIndexOnLayer r.1.leafIndex topLayer = e ∧
        selOf L s.2.2.2 bottomLayer (keyIndexOnLayer r.1.leafIndex bottomLayer)
          (littleEndianBytes 32 r.1.message) ≠ none := by
      rcases he with he | ⟨r'', hr'', hk, hsel⟩
      · exact Or.inl he
      · rcases List.mem_append.1 hr'' with hr'' | hr''
        · exact Or.inr ⟨r'', hr'', hk, hsel⟩
        · rw [List.mem_singleton] at hr''
          subst hr''
          exact absurd hsb hsel
    have hlt : e.val < keyCount topLayer := by
      rcases he' with he' | ⟨r'', -, rfl, -⟩
      · exact topKey_lt_of hrec he'
      · exact keyIndexOnLayer_lt _ _
    rw [F.top e he', topRec_congr hs hL.view hlt]

/-- **A signature whose bottom search succeeds keeps the invariant.** -/
theorem inv_of_bottom_found {log : SignLog} {r : SigningRequest}
    {s sB s' : HwReg X Z (Finset HPos × Selections)} (hs : s ∈ Inv L log)
    {bottom : LayerSignature} {f : ValPos → Digest}
    (hB : LayerRel L (botLabel r) s (some (bottom, f)) sB)
    {oT : Option (LayerSignature × (ValPos → Digest))}
    (hT : LayerRel L (topLabel r (f (botRootPos r))) sB oT s') :
    s' ∈ Inv L (log ++ [⟨r, oT.map fun top ↦
      ⟨r.leafIndex, fun l ↦ if l = bottomLayer then bottom else top.1⟩⟩]) := by
  obtain ⟨-, hrec, hfacts⟩ := hs
  obtain ⟨selB, hgB, hbot, hroot⟩ := bottomRoot_of_out hB
  set eB := keyIndexOnLayer r.leafIndex bottomLayer with heB
  set eT := keyIndexOnLayer r.leafIndex topLayer with heT
  rw [hroot, topLabel_eq_topLab] at hT
  set m := s.2.2.2 with hm
  set t := regFns s with ht
  set tB := regFns sB with htB
  have hmB : sB.2.2.2 = labMem L t (botLabel r) m := hB.mem
  have hm' : s'.2.2.2 = labMem L tB (topLab L eT) sB.2.2.2 := hT.mem
  set sig : Option Signature := oT.map fun top ↦
    ⟨r.leafIndex, fun l ↦ if l = bottomLayer then bottom else top.1⟩ with hsig
  have hmap : (log ++ [⟨r, sig⟩] : SignLog).map Sigma.fst = log.map Sigma.fst ++ [r] := by simp
  have heTlt : eT.val < keyCount topLayer := keyIndexOnLayer_lt _ _
  -- the memory after the two searches, off the two keys
  have hoff : ∀ l e, ¬(l = bottomLayer ∧ e = eB) → ¬(l = topLayer ∧ e = eT) →
      s'.2.2.2 l e = m l e := fun l e h1 h2 ↦ by
    rw [hm', labMem_apply_of_ne _ _ _ h2, hmB, labMem_apply_of_ne _ _ _ h1]
  have hBtop : sB.2.2.2 topLayer eT = m topLayer eT := by
    rw [hmB, labMem_apply_of_ne]
    exact fun h ↦ bottomLayer_ne_topLayer h.1.symm
  refine ⟨hT.noBot, ?_, fun hhit hnd ↦ ?_⟩
  · rw [hmap, hm']
    refine recFrom_labMem (lab := topLab L eT) ?_
      (List.mem_append_right _ (List.mem_singleton_self r)) rfl (layerMessage_top L r).symm tB
    rw [hmB]
    exact recFrom_labMem (lab := botLabel r) (hrec.mono (List.subset_append_left _ _))
      (List.mem_append_right _ (List.mem_singleton_self r)) rfl (layerMessage_bottom L r).symm t
  rw [hmap, List.map_append, List.map_singleton] at hnd
  obtain ⟨hnd, hn⟩ := nodup_of_snoc hnd
  have hsB : sB ∉ TrialHit L := fun h ↦ hhit (hT.offAgree_trialHit.1 h)
  have hs : s ∉ TrialHit L := fun h ↦ hsB (hB.offAgree_trialHit.1 h)
  have F := hfacts hs hnd
  have hb0 : m bottomLayer eB = none := bottom_none hrec hn
  have htt' : OffAgree (tableHw L) t (regFns s') := hB.view.trans hT.view
  -- the bottom record
  have hmbot : s'.2.2.2 bottomLayer eB = some (recOf L t (botLabel r) selB) := by
    rw [hm', labMem_apply_of_ne _ _ _ (fun h ↦ bottomLayer_ne_topLayer h.1), hmB]
    have := labMem_self_of_none (L := L) (t := t) (lab := botLabel r) hb0
    rw [hgB, Option.map_some] at this
    exact this
  -- the top record is the search's against the view
  have hselT : labSel L tB (topLab L eT) = labSel L t (topLab L eT) :=
    labSel_topLab_congr hs hB.view heTlt
  have hmtop : s'.2.2.2 topLayer eT = topRec L t eT := by
    rcases hmt : m topLayer eT with _ | b
    · have h0 : sB.2.2.2 (topLab L eT).layer (topLab L eT).key = none := by
        show sB.2.2.2 topLayer eT = none
        rw [hBtop, hmt]
      rw [hm']
      exact (labMem_self_of_none h0).trans (topRec_congr hs hB.view heTlt)
    · have h0 : sB.2.2.2 (topLab L eT).layer (topLab L eT).key = some b := by
        show sB.2.2.2 topLayer eT = some b
        rw [hBtop, hmt]
      rw [hm', labMem_of_some h0]
      show sB.2.2.2 topLayer eT = _
      rw [hBtop]
      have hne : m topLayer eT ≠ none := by
        rw [hmt]
        exact Option.some_ne_none b
      exact F.top eT (Or.inl hne)
  have hsbot : selOf L s'.2.2.2 bottomLayer eB (littleEndianBytes 32 r.message) = some selB :=
    selOf_recOf (lab := botLabel r) hgB hmbot
  have hstop : selOf L s'.2.2.2 topLayer eT (littleEndianBytes 16 (L.bottomRoot r.leafIndex)) =
      labSel L t (topLab L eT) := by
    rcases hg : labSel L t (topLab L eT) with _ | sel
    · refine selOf_of_none ?_ _
      rw [hmtop, topRec, hg, Option.map_none]
    · exact selOf_recOf (lab := topLab L eT) hg
        (show s'.2.2.2 topLayer eT = _ by rw [hmtop, topRec, hg, Option.map_some])
  have hoT : oT = (labSel L t (topLab L eT)).map (labSig L (topLab L eT)) := by
    rw [hT.out, hselT]
  -- disclosures grow
  have hdisc : discOf m ⊆ discOf s'.2.2.2 := by
    rw [hm', hmB]
    exact (discOf_labMem t _ m).trans (discOf_labMem tB _ _)
  refine ⟨fun q hq ↦ ?_, fun r'' hr'' ↦ ?_, fun e he ↦ ?_⟩
  · rcases hT.cells q hq with hq | ⟨sel, hsel, sl, hsl, hq⟩
    · rcases hB.cells q hq with hq | ⟨sel, hsel, sl, hsl, hq⟩
      · obtain ⟨sl, hsl, hq⟩ := F.cells q hq
        exact ⟨sl, public_mono hdisc hsl, hq⟩
      · rw [hgB, Option.some.injEq] at hsel
        subst hsel
        refine ⟨sl, public_mono (layerDisclosed_subset_discOf hmbot (decode_recOf hgB))
          (layerSlots_public (keyIndexOnLayer_lt _ _) hsl), hq⟩
    · rw [hselT] at hsel
      have hmt : s'.2.2.2 topLayer eT = some (recOf L t (topLab L eT) sel) := by
        rw [hmtop, topRec, hsel, Option.map_some]
      exact ⟨sl, public_mono (layerDisclosed_subset_discOf hmt (decode_recOf hsel))
        (layerSlots_public heTlt hsl), hq⟩
  · rcases List.mem_append.1 hr'' with hr'' | hr''
    · have hne := bottomKey_ne hn (List.mem_map.2 ⟨r'', hr'', rfl⟩)
      have hbk : selOf L s'.2.2.2 bottomLayer (keyIndexOnLayer r''.1.leafIndex bottomLayer)
          (littleEndianBytes 32 r''.1.message) = selOf L m bottomLayer
            (keyIndexOnLayer r''.1.leafIndex bottomLayer) (littleEndianBytes 32 r''.1.message) :=
        selOf_congr (hoff _ _ (fun h ↦ hne h.2) (fun h ↦ bottomLayer_ne_topLayer h.1)) _
      rw [F.sigs r'' hr'']
      by_cases hb : selOf L m bottomLayer (keyIndexOnLayer r''.1.leafIndex bottomLayer)
          (littleEndianBytes 32 r''.1.message) = none
      · rw [selSignature_of_bottom_none hb, selSignature_of_bottom_none (hbk.trans hb)]
      refine selSignature_congr hbk.symm (selOf_congr ?_ _)
      by_cases hk : keyIndexOnLayer r''.1.leafIndex topLayer = eT
      · rw [hk, hmtop]
        exact F.top eT (Or.inr ⟨r'', hr'', hk, hb⟩)
      · exact (hoff _ _ (fun h ↦ bottomLayer_ne_topLayer h.1.symm) (fun h ↦ hk h.2)).symm
    · rw [List.mem_singleton] at hr''
      subst hr''
      show sig = L.selSignature (selOf L s'.2.2.2) r
      rw [hsig, hoT, HonestTable.selSignature, HonestTable.selLayerSignature,
        HonestTable.selLayerSignature, hsbot, hstop, hbot]
      rcases labSel L t (topLab L eT) with _ | sel <;> rfl
  · have he' : (m topLayer e ≠ none ∨ ∃ r ∈ log, keyIndexOnLayer r.1.leafIndex topLayer = e ∧
        selOf L m bottomLayer (keyIndexOnLayer r.1.leafIndex bottomLayer)
          (littleEndianBytes 32 r.1.message) ≠ none) → s'.2.2.2 topLayer e = m topLayer e →
        s'.2.2.2 topLayer e = topRec L (regFns s') e := fun h1 h2 ↦ by
      have hlt : e.val < keyCount topLayer := by
        rcases h1 with h1 | ⟨r'', -, rfl, -⟩
        · exact topKey_lt_of hrec h1
        · exact keyIndexOnLayer_lt _ _
      exact h2.trans ((F.top e h1).trans (topRec_congr hs htt' hlt).symm)
    by_cases hk : e = eT
    · subst hk
      rw [hmtop, topRec_congr hs htt' heTlt]
    · have h2 : s'.2.2.2 topLayer e = m topLayer e :=
        hoff _ _ (fun h ↦ bottomLayer_ne_topLayer h.1.symm) (fun h ↦ hk h.2)
      refine he' ?_ h2
      rcases he with he | ⟨r'', hr'', hk', hsel⟩
      · exact Or.inl (h2 ▸ he)
      · rcases List.mem_append.1 hr'' with hr'' | hr''
        · have hne := bottomKey_ne hn (List.mem_map.2 ⟨r'', hr'', rfl⟩)
          refine Or.inr ⟨r'', hr'', hk', fun h0 ↦ hsel ?_⟩
          rw [selOf_congr (hoff _ _ (fun h ↦ hne h.2) (fun h ↦ bottomLayer_ne_topLayer h.1)) _]
          exact h0
        · rw [List.mem_singleton] at hr''
          subst hr''
          exact absurd hk'.symm hk

end step

/-! ## Program calls move the view only at their cells -/

section progs

theorem regFns_h_eq {s s' : PReg} {z : Z} (hW : s'.2.1.1 z = s.2.1.1 z)
    (hD : s'.1.1 z = s.1.1 z) : (regFns s').1 z = (regFns s).1 z := by
  show ((s'.2.1.1 z).or (s'.1.1 z)).getD 0 = ((s.2.1.1 z).or (s.1.1 z)).getD 0
  rw [hW, hD]

theorem regFns_k_eq {s s' : PReg} {x : X} (hW : s'.2.1.2.1 x = s.2.1.2.1 x)
    (hD : s'.1.2.1 x = s.1.2.1 x) : (regFns s').2.1 x = (regFns s).2.1 x := by
  show ((s'.2.1.2.1 x).or (s'.1.2.1 x)).getD 0 = ((s.2.1.2.1 x).or (s.1.2.1 x)).getD 0
  rw [hW, hD]

theorem regFns_k'_eq {s s' : PReg} {x : X} (hW : s'.2.1.2.2 x = s.2.1.2.2 x)
    (hD : s'.1.2.2 x = s.1.2.2 x) : (regFns s').2.2 x = (regFns s).2.2 x := by
  show ((s'.2.1.2.2 x).or (s'.1.2.2 x)).getD 0 = ((s.2.1.2.2 x).or (s.1.2.2 x)).getD 0
  rw [hW, hD]

section gen

variable {X₁ Z₁ : Type} [DecidableEq X₁] [DecidableEq Z₁]

theorem progUpdate_h {c : HwProg X₁ Z₁} {z : Z₁} (hz : ∀ a, c ≠ .programH z a) (W : Hw X₁ Z₁) :
    (progUpdate c W).1 z = W.1 z := by
  cases c with
  | programH z₀ a =>
    have hne : z ≠ z₀ := by
      rintro rfl
      exact hz a rfl
    exact Function.update_of_ne hne _ _
  | programK _ _ => rfl
  | programK' _ _ => rfl

theorem progUpdate_k {c : HwProg X₁ Z₁} {x : X₁} (hx : ∀ a, c ≠ .programK x a) (W : Hw X₁ Z₁) :
    (progUpdate c W).2.1 x = W.2.1 x := by
  cases c with
  | programH _ _ => rfl
  | programK x₀ a =>
    have hne : x ≠ x₀ := by
      rintro rfl
      exact hx a rfl
    exact Function.update_of_ne hne _ _
  | programK' _ _ => rfl

theorem progUpdate_k' {c : HwProg X₁ Z₁} {x : X₁} (hx : ∀ a, c ≠ .programK' x a)
    (W : Hw X₁ Z₁) : (progUpdate c W).2.2 x = W.2.2 x := by
  cases c with
  | programH _ _ => rfl
  | programK _ _ => rfl
  | programK' x₀ a =>
    have hne : x ≠ x₀ := by
      rintro rfl
      exact hx a rfl
    exact Function.update_of_ne hne _ _

end gen

/-- **A program call moves the view only at its cell.** -/
theorem ProgRel.offAgree {H : Hw X Z} {c : HwProg X Z} {s s' : PReg} (h : ProgRel c s s')
    (hc : InHw H (progPt c)) : OffAgree H (regFns s) (regFns s') := by
  obtain ⟨hs2, -, hh, hk, hk'⟩ := h
  have hW : s'.2.1 = progUpdate c s.2.1 := congrArg Prod.fst hs2
  have nh : ∀ z, H.1 z = none → ∀ a, c ≠ .programH z a := by
    rintro z hz a rfl
    exact hc hz
  have nk : ∀ x, H.2.1 x = none → ∀ a, c ≠ .programK x a := by
    rintro x hx a rfl
    exact hc hx
  have nk' : ∀ x, H.2.2 x = none → ∀ a, c ≠ .programK' x a := by
    rintro x hx a rfl
    exact hc hx
  refine ⟨fun z hz ↦ (regFns_h_eq ?_ (hh z (nh z hz))).symm,
    fun x hx ↦ (regFns_k_eq ?_ (hk x (nk x hx))).symm,
    fun x hx ↦ (regFns_k'_eq ?_ (hk' x (nk' x hx))).symm⟩
  · rw [hW]
    exact progUpdate_h (nh z hz) _
  · rw [hW]
    exact progUpdate_k (nk x hx) _
  · rw [hW]
    exact progUpdate_k' (nk' x hx) _

/-- A program call's new hardwired cells: its own. -/
theorem ProgRel.cells {c : HwProg X Z} {s s' : PReg} (h : ProgRel c s s') {q : SpongeQuery X Z}
    (hq : InHw s'.2.1 q) : InHw s.2.1 q ∨ q = progPt c := by
  have hW : s'.2.1 = progUpdate c s.2.1 := congrArg Prod.fst h.1
  rw [hW] at hq
  by_cases hc : q = progPt c
  · exact Or.inr hc
  refine Or.inl ?_
  cases q with
  | h z =>
    have hz : ∀ a, c ≠ .programH z a := by
      rintro a rfl
      exact hc rfl
    exact fun h0 ↦ hq (by show (progUpdate c s.2.1).1 z = none; rw [progUpdate_h hz]; exact h0)
  | k x =>
    have hx : ∀ a, c ≠ .programK x a := by
      rintro a rfl
      exact hc rfl
    exact fun h0 ↦ hq (by show (progUpdate c s.2.1).2.1 x = none; rw [progUpdate_k hx]; exact h0)
  | k' x =>
    have hx : ∀ a, c ≠ .programK' x a := by
      rintro a rfl
      exact hc rfl
    exact fun h0 ↦ hq (by show (progUpdate c s.2.1).2.2 x = none; rw [progUpdate_k' hx]; exact h0)

/-- **Program calls at cells of `H`**: no empty cell kept, the memory kept, the view moved only at
`H`, and new hardwired cells among the calls' cells. -/
theorem ProgsRel.facts {H : Hw X Z} :
    ∀ {cs : List (HwProg X Z)} {s s' : PReg}, ProgsRel cs s s' → (∀ c ∈ cs, InHw H (progPt c)) →
      (NoBot s → NoBot s') ∧ s'.2.2 = s.2.2 ∧ OffAgree H (regFns s) (regFns s') ∧
        ∀ q, InHw s'.2.1 q → InHw s.2.1 q ∨ ∃ c ∈ cs, q = progPt c
  | [], s, s', h, _ => by
    subst h
    exact ⟨id, rfl, offAgree_refl _ _, fun q hq ↦ Or.inl hq⟩
  | c :: cs, s, s', ⟨mid, h₁, h₂⟩, hH => by
    obtain ⟨n₂, m₂, v₂, c₂⟩ := ProgsRel.facts h₂ fun c' hc' ↦ hH c' (List.mem_cons_of_mem _ hc')
    have hm : mid.2.2 = s.2.2 := by rw [h₁.1]
    refine ⟨fun hs ↦ n₂ (h₁.2.1 hs), m₂.trans hm,
      (h₁.offAgree (hH c List.mem_cons_self)).trans v₂, fun q hq ↦ ?_⟩
    rcases c₂ q hq with hq | ⟨c', hc', rfl⟩
    · rcases h₁.cells hq with hq | rfl
      · exact Or.inl hq
      · exact Or.inr ⟨c, List.mem_cons_self, rfl⟩
    · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', rfl⟩

end progs

/-! ## The realized signer in the decompressed basis -/

section signer

variable {m₀ : Finset HPos × Selections} {L : HonestTable}

/-- The revealed values of a found selection give the table's layer signature. -/
theorem out_eq_labSig (lab : RLabel) (ρ : Randomizer) (x : Encoding) :
    (some (⟨ρ, fun i ↦ extendVals (restrictTo (inlSet (layerNeed lab.layer lab.key x)) (valueAt L))
        (cpos lab.layer lab.key i (x i).val),
      fun level ↦ extendVals (restrictTo (inlSet (layerNeed lab.layer lab.key x)) (valueAt L))
        (siblingPos lab.layer lab.key level)⟩,
      extendVals (restrictTo (inlSet (layerNeed lab.layer lab.key x)) (valueAt L))) :
        Option (LayerSignature × (ValPos → Digest))) =
      (some (ρ, x)).map (labSig L lab) := by
  rw [Option.map_some, labSig]
  congr 3
  · funext i
    rw [extendVals_restrictTo (inl_mem_inlSet.mpr (cpos_mem_layerNeed _ _ _ i)), valueAt_inl,
      valuePos_cpos_digit]
  · funext level
    rw [extendVals_restrictTo (inl_mem_inlSet.mpr (siblingPos_mem_layerNeed _ _ _ level)),
      valueAt_inl, valuePos_siblingPos]

/-- **A realized layer signature of an in-table key moves the register by `LayerRel`.** -/
theorem ht₂_signLayerT (B : QReg) (lab : RLabel) (he : lab.key.val < keyCount lab.layer)
    (P : Set PReg) (hP : ∀ s ∈ P, NoBot s) :
    HT₂ m₀ (realizeT (valueAt L) (signLayerT Selections cwUpd (pubOf L) B lab)) P
      (fun o ↦ {s' | ∃ s ∈ P, LayerRel L lab s o s'}) := by
  unfold signLayerT
  refine ht₂_revealThen m₀ (valueAt L) _ _ P _ fun mem ↦ ?_
  rw [realizeT_bind₂, extendBase_restrictTo (Finset.mem_singleton_self _)]
  set P₁ : Set PReg := {s | ∃ s₀ ∈ P, s₀.2.2 = mem ∧
    s = (s₀.1, s₀.2.1, (s₀.2.2.1 ∪ {.inr lab}, s₀.2.2.2))} with hP₁
  have hP₁nb : ∀ s ∈ P₁, NoBot s := by
    rintro s ⟨s₀, hs₀, -, rfl⟩
    exact hP s₀ hs₀
  refine HT₂.bind (det_grindR (pubOf L) B lab.layer lab.key lab.length_msg_le _ _ _ P₁ hP₁nb)
    fun g ↦ ?_
  rcases g with _ | ⟨ρ, x⟩
  · refine ht₂_pure none ?_
    rintro s' ⟨s₁, ⟨s₀, hs₀, -, rfl⟩, hg, rfl⟩
    refine ⟨s₀, hs₀, hP s₀ hs₀, rfl, offAgree_refl _ _, fun q hq ↦ Or.inl hq, ?_⟩
    have hg' : labSel L (regFns s₀) lab = none := hg.symm
    rw [hg', Option.map_none]
  · refine ht₂_revealThen m₀ (valueAt L) _ _ _ _ fun mem' ↦ ?_
    rw [realizeT_bind₂]
    refine HT₂.bind (ht₂_progSlots m₀ (valueAt L) (pubOf L) B _ _) fun _ ↦ ht₂_pure _ ?_
    rintro s₃ ⟨s₂, ⟨s₁', ⟨s₁, ⟨s₀, hs₀, -, rfl⟩, hg, rfl⟩, -, rfl⟩, hpr⟩
    have hports : ∀ c ∈ ((layerSlots lab.layer lab.key x).flatMap (slotPorts (pubOf L))).map
        (·.realize (valueAt L)), InHw (tableHw L) (progPt c) ∧
          ∃ sl ∈ layerSlots lab.layer lab.key x, progPt c ∈ pathPts L sl := by
      intro c hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
      obtain ⟨sl, hsl, hp⟩ := List.mem_flatMap.1 hp
      exact ⟨inHw_tableHw_progPt he hsl hp,
        sl, hsl, progPt_mem_pathPts hsl (inTable_of_mem_layerSlots he hsl) hp⟩
    obtain ⟨hnb, hmem, hview, hcells⟩ := ProgsRel.facts hpr fun c hc ↦ (hports c hc).1
    have hsel : labSel L (regFns s₀) lab = some (ρ, x) := hg.symm
    refine ⟨s₀, hs₀, hnb (hP s₀ hs₀), ?_, hview, fun q hq ↦ ?_, ?_⟩
    · rw [hmem]
      rfl
    · rcases hcells q hq with hq | ⟨c, hc, rfl⟩
      · exact Or.inl hq
      · obtain ⟨-, sl, hsl, hpt⟩ := hports c hc
        exact Or.inr ⟨(ρ, x), hsel, sl, hsl, hpt⟩
    · rw [hsel]
      exact out_eq_labSig lab ρ x

/-- **A realized signature keeps the invariant.** -/
theorem ht₂_signT (B : QReg) (r : SigningRequest) (log : SignLog) :
    HT₂ m₀ (realizeT (valueAt L) (signT Selections cwUpd (pubOf L) B r)) (Inv L log)
      (fun sig ↦ Inv L (log ++ [⟨r, sig⟩])) := by
  unfold signT
  rw [realizeT_bind₂]
  refine HT₂.bind (ht₂_signLayerT B (botLabel r) (keyIndexOnLayer_lt _ _) (Inv L log)
    fun s hs ↦ hs.1) fun b ↦ ?_
  rcases b with _ | ⟨bottom, f⟩
  · refine ht₂_pure none ?_
    rintro s' ⟨s, hs, hL⟩
    exact inv_of_bottom_none hs hL
  · rw [realizeT_bind₂]
    refine HT₂.bind (ht₂_signLayerT B (topLabel r (f (botRootPos r))) (keyIndexOnLayer_lt _ _)
      {sB | ∃ s ∈ Inv L log, LayerRel L (botLabel r) s (some (bottom, f)) sB}
      fun s hs ↦ by obtain ⟨_, _, hL⟩ := hs; exact hL.noBot) fun t ↦ ?_
    rcases t with _ | ⟨top, g⟩
    · refine ht₂_pure none ?_
      rintro s' ⟨sB, ⟨s, hs, hB⟩, hT⟩
      exact inv_of_bottom_found hs hB hT
    · refine ht₂_pure _ ?_
      rintro s' ⟨sB, ⟨s, hs, hB⟩, hT⟩
      exact inv_of_bottom_found hs hB hT

end signer

/-! ## The prefix invariant and `endReads` with the trial-hit mass -/

section final

variable {m₀ : Finset HPos × Selections} {L : HonestTable}

theorem inHw_hwEmpty (q : SpongeQuery X Z) : ¬InHw (hwEmpty X Z) q := by
  cases q <;> exact fun h ↦ h rfl

/-- The invariant at the start, after the root's reveal. -/
theorem inv_nil (hm₀ : m₀.2 = fun _ _ ↦ none) {s : PReg}
    (hs : NoBot s ∧ s.2 = (hwEmpty X Z, m₀)) :
    ((s.1, s.2.1, (s.2.2.1 ∪ {.inl rootPos}, s.2.2.2)) : PReg) ∈ Inv L [] := by
  obtain ⟨hnb, h2⟩ := hs
  have hm : s.2.2.2 = fun _ _ ↦ none := by rw [h2, hm₀]
  have hW : s.2.1 = hwEmpty X Z := congrArg Prod.fst h2
  refine ⟨hnb, fun l e b hb ↦ ?_, fun _ _ ↦ ⟨fun q hq ↦ ?_, fun r hr ↦ ?_, fun e he ↦ ?_⟩⟩
  · simp only [hm] at hb
    cases hb
  · exact absurd hq (by rw [hW]; exact inHw_hwEmpty q)
  · cases hr
  · rcases he with he | ⟨r, hr, -⟩
    · exact absurd (by simp only [hm]) he
    · cases hr

/-- **The prefix invariant off the trial-hit event**: on a table whose honest paths share no cell,
from a memory with no selection recorded, every winning branch of the challenge prefix is, in the
decompressed basis, supported where the register hits a trial or has the prefix facts. -/
theorem prefixWinFactsOff (hd : HonestPathsDisjoint L) (hm₀ : m₀.2 = fun _ _ ↦ none)
    (A : Adversary (X × Z)) : PrefixWinFactsOff m₀ A L (TrialHit L) := by
  intro pre hw
  rw [conj_branch₂ m₀ (wPrefix A L) pre (initU m₀)]
  have H := ht₂_prefixT m₀ (valueAt L) (pubOf L) A (Inv L) (fun B r log ↦ ht₂_signT B r log)
    {s | NoBot s ∧ s.2 = (hwEmpty X Z, m₀)} fun s hs ↦ inv_nil hm₀ hs
  refine (H _ (init_dec m₀) pre).mono ?_
  rintro s ⟨⟨-, hrec, hfacts⟩, hpk⟩ hhit
  have hwin := hw
  simp only [winCond, sufCmaScheme, decide_eq_true_eq] at hwin
  have hnd : ((pre.2.2.map Sigma.fst).map SigningRequest.leafIndex).Nodup := by
    rw [List.map_map]
    exact hwin.1
  have F := hfacts hhit hnd
  refine preFacts_of hd ?_ hrec F.sigs F.cells
  rw [hpk, extendVals_restrictTo (Finset.mem_singleton_self _), valueAt_inl, valuePos_rootPos]
  rfl

theorem prefixWinFactsOff_of_tableGood (hg : TableGood L) (hm₀ : m₀.2 = fun _ _ ↦ none)
    (A : Adversary (X × Z)) : PrefixWinFactsOff m₀ A L (TrialHit L) :=
  prefixWinFactsOff hg.2 hm₀ A

/-- **The trial-hit mass**: the weight, at the end of the canonical game, of the decompressed
registers where some top key's randomizer trial reads a cell the game may program. -/
noncomputable def trialHitMass (m₀ : Finset HPos × Selections) (A : Adversary (X × Z))
    (L : HonestTable) : ℝ≥0∞ :=
  @eventMassDec m₀ A L (TrialHit L) (Classical.decPred _)

/-- **`endReads` for the canonical game on a good table**: the win weight is at most the event
weight of `BadRS L progCap` at the end of the game, the read error of the verification, and the
trial-hit mass. -/
theorem endReads_wGame_trialHit [DecidablePred (· ∈ BadRS (S := HPos) L progCap)]
    {A : Adversary (X × Z)} (hg : TableGood L) (hm₀ : m₀.2 = fun _ _ ↦ none)
    (hprog : IPFunctor.IFreeM.IsChargeBound (wGame A L)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap) :
    (runtimeR m₀).evalDistMap .instruments (wGame A L) (SubState.basis ()) winBit {true} ≤
      (runtimeR m₀).eventWeight .instruments (hwProjector (BadRS L progCap)) (wGame A L)
          ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) +
        ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks) +
          trialHitMass m₀ A L :=
  @endReads_wGame m₀ A L (TrialHit L) _ (Classical.decPred _) hprog
    (prefixWinFactsOff_of_tableGood hg hm₀ A)

/-- `endReads_wGame_trialHit` with a bound `ε` on the trial-hit mass (to be supplied by the
trial-read source argument: fresh `k`, `k'` values uniform unless recorded, so about
`|tableHw L|`-many capacities per top trial read over `|Z|`, plus the recorded mass). -/
theorem endReads_wGame_of_trialHit_le [DecidablePred (· ∈ BadRS (S := HPos) L progCap)]
    {A : Adversary (X × Z)} (hg : TableGood L) (hm₀ : m₀.2 = fun _ _ ↦ none)
    (hprog : IPFunctor.IFreeM.IsChargeBound (wGame A L)
      (portCharge (L := LocalSig.instruments.{0})
        (extProgCharge X Z (Finset HPos × Selections) (recSpec HPos Selections))) progCap)
    {ε : ℝ≥0∞} (hhit : trialHitMass m₀ A L ≤ ε) :
    (runtimeR m₀).evalDistMap .instruments (wGame A L) (SubState.basis ()) winBit {true} ≤
      (runtimeR m₀).eventWeight .instruments (hwProjector (BadRS L progCap)) (wGame A L)
          ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) +
        ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks) + ε :=
  (endReads_wGame_trialHit hg hm₀ hprog).trans (add_le_add le_rfl hhit)

end final

end Quantum.Xmss.Assembly

end
