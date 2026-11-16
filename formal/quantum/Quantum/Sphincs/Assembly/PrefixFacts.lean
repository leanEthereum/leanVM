module

public import Quantum.Sphincs.Assembly.PrefixRun
public import Quantum.Sphincs.Assembly.Template.Exempt
public import Quantum.Sphincs.Classify

@[expose] public section

/-!
# The prefix facts of leanSPHINCS's event side, off the trial-hit and conflict events

The event side's prefix facts (contract C4, `strPol`, template data `(pub, v)`): on every winning
branch of the realized challenge prefix `realizeT v (prefixT Selections cwUpd strPol pub A)`, in
the decompressed basis (PrefixRun's `HT₂` semantics), the register is in one of two events or has
the facts Classify's `WinFacts` needs, all but the grade (`PreFactsS`, `winFacts_of_preFacts`).

* **Moves** (`Moves`, `ProgsRel.moves`): a program batch at cells `P` keeps the view and the
  hardwired cells off `P`, loses no hardwired cell and writes the public key values at `k`, `k'`.
  The template programs the cells of in-table slots' honest paths (`slotPt`) and of `H_msg` calls
  at their randomizers (`hmsgPt`); together `ProgCell`.
* **The events.** `TrialHit pub v`: some trial (counter below `encodingAttemptLimit`) of a key
  `K_l(idx)` on the value it signs reads, against the register's view, a cell of `ProgCell`; off it
  every rerun search reads the same digests (`kSel_congr`, `kRec_congr`), so the transcript is that
  of one selection function. `HConflict pub v`: two distinct `H_msg` calls with hardwired `k`- and
  `k'`-cells share their `h`-cell; off it no `H_msg` output is overwritten. Their masses are
  separate obligations: the trial-hit mass (SP-PF2, a decompressed trial-read argument) and the
  conflict mass (the compressed hidden-randomizer argument, `HConflict`'s docstring); the event of
  `prefixWinFactsOff` is their union, to be split into two summands downstream.
* **Good data** (static, on `(pub, v)`, fractions for SP-RR/SP-PB): `PathsDisjoint pub.xw
  pub.keys.1 (valsOf v)` (SP-PB), `HmsgSep` (no in-table `k`-cell is an `H_msg` block, needed for
  `exempt` and `covEx`), `HmsgHSep` (no in-table `h`-cell is an `H_msg` `h`-cell, needed for
  `digests`).
* **The searches against the view** (`kSel`, `kRec`, `kMem`, PrefixRun's `grindKV`), the
  selection function of a memory (`selOfM`, `recordsSel_selOfM`), the stream entries of marked
  messages (`MarksOK`, `digS`, `streamIdx_of_mem`), the held `H_msg` calls (`HHeldV`,
  `hashHeld_of_hHeldV`), the public slots of FORS openings and layer signatures
  (`forsSlots_public`, `layerSlots_public`).
* **The invariant** `InvS pub v log`: base facts (`SBase`) and, off the events and within the
  signature limit, `CoreFacts`; a signature is its head (`HeadRel`: reveals, both `H_msg` batches,
  the FORS opening; `headRel_of`) and its layers (`LayerRelS`, `ht₂_signLayerT`, `LayersRel`);
  `inv_step` keeps the invariant, `ht₂_signT` realizes it, `inv_nil` starts it.
* **Results**: `prefixWinFactsOff`, from a memory with no mark and no selection, on good data.
-/

open Matrix
open scoped Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput HashInput Message PublicParameter Randomizer littleEndianBytes
  chainLength truncateHash)
open Quantum.Xmss (X Z blocks trunc128 out256 length_blocks blocks_injective)
open Quantum.Xmss.Hybrid (LazyProg restrictTo progUpdate)
open Quantum.Xmss.Assembly (PRegOf HT HT₂ ht₂_pure ht_of_ht₂ ht₂_of_ht ht₂_realizeT_bind
  ht₂_revealThen ProgRel ProgsRel NoBot Det regFns realizeT realizeT_bind₂ revealThen recHwSpec
  RevealVals rnK rnR rnZ runtimeR initU conj_branch₂ init_dec)

namespace Quantum.Sphincs.Assembly

/- Instance search for the run families over the register `SReg` exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## Cells, views and moves of the register -/

section cells

/-- The cell a read reads is hardwired. -/
def InHw (W : Hw X Z) : SpongeQuery X Z → Prop
  | .h z => W.1 z ≠ none
  | .k x => W.2.1 x ≠ none
  | .k' x => W.2.2 x ≠ none

/-- The cell of a program port. -/
def progPt : HwProg X Z → SpongeQuery X Z
  | .programH z _ => .h z
  | .programK x _ => .k x
  | .programK' x _ => .k' x

/-- Two views agree off the cells `P`. -/
def OffAgree (P : SpongeQuery X Z → Prop) (t t' : SpongeKeys X Z) : Prop :=
  (∀ z, ¬P (.h z) → t.1 z = t'.1 z) ∧ (∀ x, ¬P (.k x) → t.2.1 x = t'.2.1 x) ∧
    ∀ x, ¬P (.k' x) → t.2.2 x = t'.2.2 x

theorem OffAgree.symm {P : SpongeQuery X Z → Prop} {t t' : SpongeKeys X Z} (h : OffAgree P t t') :
    OffAgree P t' t :=
  ⟨fun z hz ↦ (h.1 z hz).symm, fun x hx ↦ (h.2.1 x hx).symm, fun x hx ↦ (h.2.2 x hx).symm⟩

theorem OffAgree.trans {P : SpongeQuery X Z → Prop} {t t' t'' : SpongeKeys X Z}
    (h : OffAgree P t t') (h' : OffAgree P t' t'') : OffAgree P t t'' :=
  ⟨fun z hz ↦ (h.1 z hz).trans (h'.1 z hz), fun x hx ↦ (h.2.1 x hx).trans (h'.2.1 x hx),
    fun x hx ↦ (h.2.2 x hx).trans (h'.2.2 x hx)⟩

theorem OffAgree.mono {P P' : SpongeQuery X Z → Prop} {t t' : SpongeKeys X Z}
    (h : OffAgree P t t') (hP : ∀ q, P q → P' q) : OffAgree P' t t' :=
  ⟨fun z hz ↦ h.1 z fun h' ↦ hz (hP _ h'), fun x hx ↦ h.2.1 x fun h' ↦ hx (hP _ h'),
    fun x hx ↦ h.2.2 x fun h' ↦ hx (hP _ h')⟩

theorem offAgree_refl (P : SpongeQuery X Z → Prop) (t : SpongeKeys X Z) : OffAgree P t t :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- Two hardwired registers agree off the cells `P`. -/
def HwOff (P : SpongeQuery X Z → Prop) (W W' : Hw X Z) : Prop :=
  (∀ z, ¬P (.h z) → W'.1 z = W.1 z) ∧ (∀ x, ¬P (.k x) → W'.2.1 x = W.2.1 x) ∧
    ∀ x, ¬P (.k' x) → W'.2.2 x = W.2.2 x

/-- Every hardwired cell of `W` is hardwired in `W'`. -/
def HwGrow (W W' : Hw X Z) : Prop :=
  ∀ q, InHw W q → InHw W' q

/-- **The hardwired `k`- and `k'`-cells hold the public keys' values.** -/
def KeyVals (pub : Pub) (W : Hw X Z) : Prop :=
  (∀ x a, W.2.1 x = some a → a = pub.keys.2.1 x) ∧ ∀ x a, W.2.2 x = some a → a = pub.keys.2.2 x

/-- A program call writes the public keys' values at `k`- and `k'`-cells. -/
def PubKV (pub : Pub) : HwProg X Z → Prop
  | .programH _ _ => True
  | .programK x a => a = pub.keys.2.1 x
  | .programK' x a => a = pub.keys.2.2 x

/-- **A move of the register off the cells `P`**: no empty cell after, the view and the hardwired
cells kept off `P`, no hardwired cell lost, and the public key values kept. -/
structure Moves (pub : Pub) (P : SpongeQuery X Z → Prop) (s s' : SReg) : Prop where
  noBot : NoBot s'
  view : OffAgree P (regFns s) (regFns s')
  hw : HwOff P s.2.1 s'.2.1
  grow : HwGrow s.2.1 s'.2.1
  keyVals : KeyVals pub s.2.1 → KeyVals pub s'.2.1

variable {pub : Pub}

theorem Moves.mono {P P' : SpongeQuery X Z → Prop} {s s' : SReg} (h : Moves pub P s s')
    (hP : ∀ q, P q → P' q) : Moves pub P' s s' :=
  ⟨h.noBot, h.view.mono hP, ⟨fun z hz ↦ h.hw.1 z fun h' ↦ hz (hP _ h'),
    fun x hx ↦ h.hw.2.1 x fun h' ↦ hx (hP _ h'), fun x hx ↦ h.hw.2.2 x fun h' ↦ hx (hP _ h')⟩,
    h.grow, h.keyVals⟩

theorem Moves.trans {P P' : SpongeQuery X Z → Prop} {s s' s'' : SReg} (h : Moves pub P s s')
    (h' : Moves pub P' s' s'') : Moves pub (fun q ↦ P q ∨ P' q) s s'' :=
  ⟨h'.noBot, (h.view.mono fun _ hq ↦ Or.inl hq).trans (h'.view.mono fun _ hq ↦ Or.inr hq),
    ⟨fun z hz ↦ (h'.hw.1 z fun h₁ ↦ hz (Or.inr h₁)).trans (h.hw.1 z fun h₁ ↦ hz (Or.inl h₁)),
      fun x hx ↦ (h'.hw.2.1 x fun h₁ ↦ hx (Or.inr h₁)).trans
        (h.hw.2.1 x fun h₁ ↦ hx (Or.inl h₁)),
      fun x hx ↦ (h'.hw.2.2 x fun h₁ ↦ hx (Or.inr h₁)).trans
        (h.hw.2.2 x fun h₁ ↦ hx (Or.inl h₁))⟩,
    fun q hq ↦ h'.grow q (h.grow q hq), fun hk ↦ h'.keyVals (h.keyVals hk)⟩

/-- A step keeping the databases and the hardwired cells moves nothing. -/
theorem moves_of_eq (P : SpongeQuery X Z → Prop) {s s' : SReg} (hnb : NoBot s')
    (h1 : s'.1 = s.1) (h2 : s'.2.1 = s.2.1) : Moves pub P s s' := by
  have hv : regFns s' = regFns s := by
    show (union s'.2.1 s'.1).fill = (union s.2.1 s.1).fill
    rw [h1, h2]
  refine ⟨hnb, ?_, ⟨fun z _ ↦ by rw [h2], fun x _ ↦ by rw [h2], fun x _ ↦ by rw [h2]⟩,
    fun q hq ↦ by rw [h2]; exact hq, fun hk ↦ by rw [h2]; exact hk⟩
  rw [hv]
  exact offAgree_refl _ _

/-- A move after a step keeping the databases and the hardwired cells. -/
theorem Moves.of_eq_left {P : SpongeQuery X Z → Prop} {s s' s'' : SReg} (h : Moves pub P s' s'')
    (h1 : s'.1 = s.1) (h2 : s'.2.1 = s.2.1) : Moves pub P s s'' := by
  have hv : regFns s' = regFns s := by
    show (union s'.2.1 s'.1).fill = (union s.2.1 s.1).fill
    rw [h1, h2]
  refine ⟨h.noBot, ?_, ?_, ?_, ?_⟩
  · rw [← hv]
    exact h.view
  · rw [← h2]
    exact h.hw
  · rw [← h2]
    exact h.grow
  · rw [← h2]
    exact h.keyVals

section gen

variable {X₁ Z₁ : Type} [DecidableEq X₁] [DecidableEq Z₁]

theorem progUpdate_h_of_ne {c : HwProg X₁ Z₁} {z : Z₁} (hz : ∀ a, c ≠ .programH z a)
    (W : Hw X₁ Z₁) : (progUpdate c W).1 z = W.1 z := by
  cases c with
  | programH z₀ a =>
    have hne : z ≠ z₀ := by
      rintro rfl
      exact hz a rfl
    exact Function.update_of_ne hne _ _
  | programK _ _ => rfl
  | programK' _ _ => rfl

theorem progUpdate_k_of_ne {c : HwProg X₁ Z₁} {x : X₁} (hx : ∀ a, c ≠ .programK x a)
    (W : Hw X₁ Z₁) : (progUpdate c W).2.1 x = W.2.1 x := by
  cases c with
  | programH _ _ => rfl
  | programK x₀ a =>
    have hne : x ≠ x₀ := by
      rintro rfl
      exact hx a rfl
    exact Function.update_of_ne hne _ _
  | programK' _ _ => rfl

theorem progUpdate_k'_of_ne {c : HwProg X₁ Z₁} {x : X₁} (hx : ∀ a, c ≠ .programK' x a)
    (W : Hw X₁ Z₁) : (progUpdate c W).2.2 x = W.2.2 x := by
  cases c with
  | programH _ _ => rfl
  | programK _ _ => rfl
  | programK' x₀ a =>
    have hne : x ≠ x₀ := by
      rintro rfl
      exact hx a rfl
    exact Function.update_of_ne hne _ _

theorem progUpdate_h_ne_none (c : HwProg X₁ Z₁) {W : Hw X₁ Z₁} {z : Z₁} (h : W.1 z ≠ none) :
    (progUpdate c W).1 z ≠ none := by
  by_cases hc : ∃ a, c = .programH z a
  · obtain ⟨a, rfl⟩ := hc
    show Function.update W.1 z (some a) z ≠ none
    rw [Function.update_self]
    exact Option.some_ne_none a
  · rw [progUpdate_h_of_ne (fun a he ↦ hc ⟨a, he⟩)]
    exact h

theorem progUpdate_k_ne_none (c : HwProg X₁ Z₁) {W : Hw X₁ Z₁} {x : X₁} (h : W.2.1 x ≠ none) :
    (progUpdate c W).2.1 x ≠ none := by
  by_cases hc : ∃ a, c = .programK x a
  · obtain ⟨a, rfl⟩ := hc
    show Function.update W.2.1 x (some a) x ≠ none
    rw [Function.update_self]
    exact Option.some_ne_none a
  · rw [progUpdate_k_of_ne (fun a he ↦ hc ⟨a, he⟩)]
    exact h

theorem progUpdate_k'_ne_none (c : HwProg X₁ Z₁) {W : Hw X₁ Z₁} {x : X₁} (h : W.2.2 x ≠ none) :
    (progUpdate c W).2.2 x ≠ none := by
  by_cases hc : ∃ a, c = .programK' x a
  · obtain ⟨a, rfl⟩ := hc
    show Function.update W.2.2 x (some a) x ≠ none
    rw [Function.update_self]
    exact Option.some_ne_none a
  · rw [progUpdate_k'_of_ne (fun a he ↦ hc ⟨a, he⟩)]
    exact h

theorem progUpdate_k_eq_some {c : HwProg X₁ Z₁} {W : Hw X₁ Z₁} {x : X₁} {b : Z₁}
    (h : (progUpdate c W).2.1 x = some b) : c = .programK x b ∨ W.2.1 x = some b := by
  by_cases hc : ∃ a, c = .programK x a
  · obtain ⟨a, rfl⟩ := hc
    change Function.update W.2.1 x (some a) x = some b at h
    rw [Function.update_self, Option.some.injEq] at h
    exact Or.inl (by rw [h])
  · rw [progUpdate_k_of_ne (fun a he ↦ hc ⟨a, he⟩)] at h
    exact Or.inr h

theorem progUpdate_k'_eq_some {c : HwProg X₁ Z₁} {W : Hw X₁ Z₁} {x : X₁} {b : Z₁}
    (h : (progUpdate c W).2.2 x = some b) : c = .programK' x b ∨ W.2.2 x = some b := by
  by_cases hc : ∃ a, c = .programK' x a
  · obtain ⟨a, rfl⟩ := hc
    change Function.update W.2.2 x (some a) x = some b at h
    rw [Function.update_self, Option.some.injEq] at h
    exact Or.inl (by rw [h])
  · rw [progUpdate_k'_of_ne (fun a he ↦ hc ⟨a, he⟩)] at h
    exact Or.inr h

end gen

theorem hwGrow_progUpdate (c : HwProg X Z) (W : Hw X Z) : HwGrow W (progUpdate c W) := by
  intro q hq
  cases q with
  | h z => exact progUpdate_h_ne_none c hq
  | k x => exact progUpdate_k_ne_none c hq
  | k' x => exact progUpdate_k'_ne_none c hq

theorem keyVals_progUpdate {c : HwProg X Z} (hc : PubKV pub c) {W : Hw X Z} (hW : KeyVals pub W) :
    KeyVals pub (progUpdate c W) := by
  refine ⟨fun x b hb ↦ ?_, fun x b hb ↦ ?_⟩
  · rcases progUpdate_k_eq_some hb with rfl | hb
    · exact hc
    · exact hW.1 x b hb
  · rcases progUpdate_k'_eq_some hb with rfl | hb
    · exact hc
    · exact hW.2 x b hb

/-- **A program call moves the register off its cell.** -/
theorem ProgRel.moves {c : HwProg X Z} {s s' : SReg} (h : ProgRel c s s')
    {P : SpongeQuery X Z → Prop} (hc : P (progPt c)) (hkv : PubKV pub c) (hs : NoBot s) :
    Moves pub P s s' := by
  obtain ⟨hs2, hnb, hh, hk, hk'⟩ := h
  have hW : s'.2.1 = progUpdate c s.2.1 := congrArg Prod.fst hs2
  have nh : ∀ z, ¬P (.h z) → ∀ a, c ≠ .programH z a := by
    rintro z hz a rfl
    exact hz hc
  have nk : ∀ x, ¬P (.k x) → ∀ a, c ≠ .programK x a := by
    rintro x hx a rfl
    exact hx hc
  have nk' : ∀ x, ¬P (.k' x) → ∀ a, c ≠ .programK' x a := by
    rintro x hx a rfl
    exact hx hc
  have hwh : ∀ z, ¬P (.h z) → s'.2.1.1 z = s.2.1.1 z := fun z hz ↦ by
    rw [hW]
    exact progUpdate_h_of_ne (nh z hz) _
  have hwk : ∀ x, ¬P (.k x) → s'.2.1.2.1 x = s.2.1.2.1 x := fun x hx ↦ by
    rw [hW]
    exact progUpdate_k_of_ne (nk x hx) _
  have hwk' : ∀ x, ¬P (.k' x) → s'.2.1.2.2 x = s.2.1.2.2 x := fun x hx ↦ by
    rw [hW]
    exact progUpdate_k'_of_ne (nk' x hx) _
  refine ⟨hnb hs, ⟨fun z hz ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩, ⟨hwh, hwk, hwk'⟩,
    fun q hq ↦ by rw [hW]; exact hwGrow_progUpdate c _ q hq,
    fun hkv' ↦ by rw [hW]; exact keyVals_progUpdate hkv hkv'⟩
  · show ((s.2.1.1 z).or (s.1.1 z)).getD 0 = ((s'.2.1.1 z).or (s'.1.1 z)).getD 0
    rw [hwh z hz, hh z (nh z hz)]
  · show ((s.2.1.2.1 x).or (s.1.2.1 x)).getD 0 = ((s'.2.1.2.1 x).or (s'.1.2.1 x)).getD 0
    rw [hwk x hx, hk x (nk x hx)]
  · show ((s.2.1.2.2 x).or (s.1.2.2 x)).getD 0 = ((s'.2.1.2.2 x).or (s'.1.2.2 x)).getD 0
    rw [hwk' x hx, hk' x (nk' x hx)]

/-- **Program calls at cells of `P` writing the public key values move the register off `P`** and
keep its memory. -/
theorem ProgsRel.moves {P : SpongeQuery X Z → Prop} :
    ∀ {cs : List (HwProg X Z)} {s s' : SReg}, ProgsRel cs s s' →
      (∀ c ∈ cs, P (progPt c) ∧ PubKV pub c) → NoBot s → Moves pub P s s' ∧ s'.2.2 = s.2.2
  | [], s, s', h, _, hs => by
    change s = s' at h
    subst h
    exact ⟨moves_of_eq P hs rfl rfl, rfl⟩
  | c :: cs, s, s', ⟨mid, h₁, h₂⟩, hc, hs => by
    have hm := ProgRel.moves h₁ (hc c List.mem_cons_self).1 (hc c List.mem_cons_self).2 hs
    obtain ⟨hm', hmem⟩ := ProgsRel.moves h₂ (fun c' hc' ↦ hc c' (List.mem_cons_of_mem _ hc'))
      hm.noBot
    refine ⟨(hm.trans hm').mono fun _ hq ↦ hq.elim id id, hmem.trans ?_⟩
    rw [h₁.1]

theorem progsRel_append_inv {s s' : SReg} :
    ∀ {l₁ l₂ : List (HwProg X Z)}, ProgsRel (l₁ ++ l₂) s s' →
      ∃ mid, ProgsRel l₁ s mid ∧ ProgsRel l₂ mid s'
  | [], _, h => ⟨s, rfl, h⟩
  | c :: l₁, l₂, ⟨mid, h₁, h₂⟩ => by
    obtain ⟨mid', h₃, h₄⟩ := progsRel_append_inv (s := mid) h₂
    exact ⟨mid', ⟨mid, h₁, h₃⟩, h₄⟩

end cells

/-! ## The cells the template programs -/

section ports

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- **The cells of an absorption's rounds** under the public keys: the `k`-, `k'`- and `h`-cells
of rounds `0, …, n - 1` of the blocks `b`. -/
def pathPt (b : ℕ → X) (n : ℕ) (q : SpongeQuery X Z) : Prop :=
  ∃ j < n, q = .k (cellK pub b j).1 ∨ q = .k' (cellK' pub b j).1 ∨
    q = .h (rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 b j)

/-- The cells of slot `s`'s honest path at the values. -/
def slotPt (s : Slot) : SpongeQuery X Z → Prop :=
  pathPt pub (slotBlk pub.seed s (valsOf v)) (nBlk pub.seed s)

/-- The randomizer of `M`, `R(M)`, at the hidden values. -/
def rndOf (M : Message) : Randomizer :=
  v (.rnd M)

/-- The blocks of `H_msg` call `i` on `M` at its randomizer `v (.rnd M)`. -/
def hBlk (M : Message) (i : DigestCall) : ℕ → X :=
  slotBlk pub.seed (.hmsg (v (.rnd M)) M i) (valsOf v)

/-- The cells of `H_msg` call `i` on `M` at its randomizer. -/
def hmsgPt (M : Message) (i : DigestCall) : SpongeQuery X Z → Prop :=
  pathPt pub (hBlk pub v M i) 1

/-- **The cells the template may program**: those of in-table slots' honest paths and of every
message's `H_msg` calls at its randomizer. -/
def ProgCell (q : SpongeQuery X Z) : Prop :=
  (∃ s, InTable s ∧ slotPt pub v s q) ∨ ∃ M i, hmsgPt pub v M i q

variable {pub}

theorem mem_pathCells {b : ℕ → X} {cor : X → X → X} {n : ℕ} {c : HwProg X Z}
    (hc : c ∈ pathCells pub b cor n) : pathPt pub b n (progPt c) ∧ PubKV pub c := by
  simp only [pathCells, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, rfl | rfl | rfl⟩ := hc
  · exact ⟨⟨j, hj, Or.inl rfl⟩, rfl⟩
  · exact ⟨⟨j, hj, Or.inr (Or.inl rfl)⟩, rfl⟩
  · exact ⟨⟨j, hj, Or.inr (Or.inr (congrArg SpongeQuery.h (cellH_fst pub _ _ _ j)))⟩, trivial⟩

/-- **The realized ports of in-table slots** program cells of their honest paths, with the public
key values. -/
theorem slotPorts_pt {ss : List Slot} (hss : ∀ s ∈ ss, InTable s) {c : HwProg X Z}
    (hc : c ∈ (ss.flatMap (slotPorts pub)).map (·.realize v)) :
    ∃ s ∈ ss, slotPt pub v s (progPt c) ∧ PubKV pub c := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  obtain ⟨s, hs, hp⟩ := List.mem_flatMap.1 hp
  have hc' : p.realize v ∈ pathCells pub (slotBlk pub.seed s (valsOf v))
      (cor128 (valsOf v (slotOutPos s))) (nBlk pub.seed s) := by
    rw [← realize_slotPorts pub (hss s hs) v]
    exact List.mem_map.2 ⟨p, hp, rfl⟩
  exact ⟨s, hs, mem_pathCells hc'⟩

/-- **The realized `H_msg` ports** program cells of the calls at the randomizer, with the public key
values. -/
theorem digestPorts_pt {pol : DigestPolicy} {T : Finset HPos} {M : Message} {c : HwProg X Z}
    (hc : c ∈ (digestPorts pub pol T M).map (·.realize v)) :
    ∃ i, hmsgPt pub v M i (progPt c) ∧ PubKV pub c := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  have key : ∀ i, p ∈ hmsgPorts pub pol T M i → hmsgPt pub v M i (progPt (p.realize v)) ∧
      PubKV pub (p.realize v) := fun i hpi ↦ by
    have hc' : p.realize v ∈ pathCells pub (hBlk pub v M i)
        (cor256 (hashOut _ (v (pol.out T M i)))) 1 := by
      rw [hBlk, ← realize_hmsgPorts pub pol T M i v]
      exact List.mem_map.2 ⟨p, hpi, rfl⟩
    exact mem_pathCells hc'
  rcases List.mem_append.1 hp with hp | hp
  · exact ⟨0, key 0 hp⟩
  · exact ⟨1, key 1 hp⟩

end ports

/-! ## The events and the good data -/

section events

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- The `h`-cell of `H_msg` call `i` on `M` at its randomizer. -/
def hZ (M : Message) (i : DigestCall) : Z :=
  rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 (hBlk pub v M i) 0

/-- `W` holds the `k`- and `k'`-cells of `H_msg` call `i` on `M` at its randomizer. -/
def HHeld (W : Hw X Z) (M : Message) (i : DigestCall) : Prop :=
  W.2.1 (cellK pub (hBlk pub v M i) 0).1 ≠ none ∧ W.2.2 (cellK' pub (hBlk pub v M i) 0).1 ≠ none

/-- **The conflict event** of the (decompressed) register: two distinct `H_msg` calls (at their
messages' randomizers) whose `k`- and `k'`-cells are hardwired share their `h`-cell, so a later
program of one overwrites the other's output. It only grows along a run (`HConflict.mono`): the
`k`- and `k'`-cells, once hardwired, stay hardwired.

Its mass is not bounded here. Intended bound (the compressed hidden-randomizer argument, as in
CwRev): when `M'` is first signed its randomizer `R(M')` is hidden, so the `H_msg` `k`-cell keyed
by it is unrecorded (but for a first-disclosure mass) and its `k'`, `h` outcomes are fresh; its two
`h`-cells hit one of the at most `2N` held `H_msg` cells with probability at most `2N · 2 / |Z|`
per message, in total about `N² · 2^-509`. -/
def HConflict : Set SReg :=
  {s | ∃ M i M' i', (M, i) ≠ (M', i') ∧ HHeld pub v s.2.1 M i ∧ HHeld pub v s.2.1 M' i' ∧
    hZ pub v M i = hZ pub v M' i'}

/-- **The trial-hit event** of the (decompressed) register: some trial (counter below
`encodingAttemptLimit`) of some key `K_l(idx)` on the value it signs, evaluated against the
register's view, reads a cell the template may program. -/
def TrialHit : Set SReg :=
  {s | ∃ l idx, ∃ c < encodingAttemptLimit, ∃ rd ∈ inputReads (regFns s) pub.perm
    (encIn pub (keyOf l idx) (valsOf v (msgPos (keyOf l idx))) (BitVec.ofNat counterBits c)),
      ProgCell pub v rd.point}

/-- **Good data: no in-table round's `k`-cell is the block of an `H_msg` call** at `PK.seed` and
the root, for any randomizer, message and call. Single-block slots of lengths other than 84 bytes
satisfy it by their padding; the first blocks of multi-block slots need the seed, root and payload
bytes to differ from an `H_msg` block, the later rounds' `k`-cells are uniform rates: the bad
fraction is about `2^35 · 2^385 / 2^1088 ≈ 2^-668` [INFERENCE]. -/
def HmsgSep : Prop :=
  ∀ (R : Randomizer) (M : Message) (i : DigestCall) (s : Slot), InTable s →
    ∀ j < nBlk pub.seed s, sCellK pub.xw pub.keys.1 s (valsOf v) j ≠
      slotBlk pub.seed (.hmsg R M i) (valsOf v) 0

/-- **Good data: no in-table round's `h`-cell is the `h`-cell of an `H_msg` call** at its message's
randomizer: about `2^35 · 2^257` pairs of capacities, a fraction about `2^-220` [INFERENCE]. -/
def HmsgHSep : Prop :=
  ∀ (M : Message) (i : DigestCall) (s : Slot), InTable s →
    ∀ j < nBlk pub.seed s, sCellZ pub.xw pub.keys.1 s (valsOf v) j ≠ hZ pub v M i

variable {pub v}

/-- **The conflict event only grows** along moves keeping the hardwired cells. -/
theorem HConflict.mono {s s' : SReg} (hg : HwGrow s.2.1 s'.2.1) (h : s ∈ HConflict pub v) :
    s' ∈ HConflict pub v := by
  obtain ⟨M, i, M', i', hne, ⟨h1, h2⟩, ⟨h3, h4⟩, hz⟩ := h
  exact ⟨M, i, M', i', hne, ⟨hg (.k _) h1, hg (.k' _) h2⟩, ⟨hg (.k _) h3, hg (.k' _) h4⟩, hz⟩

theorem answeredBy_of_offAgree {P : SpongeQuery X Z → Prop} {t t' : SpongeKeys X Z}
    (h : OffAgree P t t') {e : SpongeRead X Z} (he : e.AnsweredBy t) (hn : ¬P e.point) :
    e.AnsweredBy t' := by
  cases e with
  | h z a => exact (h.1 z hn).symm.trans he
  | k x a => exact (h.2.1 x hn).symm.trans he
  | k' x a => exact (h.2.2 x hn).symm.trans he

/-- **Views agreeing off `P` read alike** an input whose reads avoid `P`. -/
theorem inputReads_eq_of_offAgree {P : SpongeQuery X Z → Prop} {t t' : SpongeKeys X Z}
    (h : OffAgree P t t') (π : Equiv.Perm (X × Z)) (input : HashInput)
    (hn : ∀ rd ∈ inputReads t π input, ¬P rd.point) :
    inputReads t' π input = inputReads t π input ∧
      absorb (spongePerm t' π) (blocks input) = absorb (spongePerm t π) (blocks input) :=
  spongeReads_congr π (blocks input) fun e he ↦
    answeredBy_of_offAgree h (spongeReads_answeredBy π t _ e he) (hn e he)

/-- **The trial-hit event depends only on the view off the programmable cells.** -/
theorem trialHit_iff_of_offAgree {s s' : SReg}
    (h : OffAgree (ProgCell pub v) (regFns s) (regFns s')) :
    s ∈ TrialHit pub v ↔ s' ∈ TrialHit pub v := by
  have key : ∀ {s s' : SReg}, OffAgree (ProgCell pub v) (regFns s) (regFns s') →
      s' ∈ TrialHit pub v → s ∈ TrialHit pub v := by
    intro s s' h hs'
    obtain ⟨l, idx, c, hc, rd, hrd, hin⟩ := hs'
    by_contra hs
    have hav : ∀ rd ∈ inputReads (regFns s) pub.perm (encIn pub (keyOf l idx)
        (valsOf v (msgPos (keyOf l idx))) (BitVec.ofNat counterBits c)),
        ¬ProgCell pub v rd.point :=
      fun rd hrd hin ↦ hs ⟨l, idx, c, hc, rd, hrd, hin⟩
    rw [(inputReads_eq_of_offAgree h pub.perm _ hav).1] at hrd
    exact hav rd hrd hin
  exact ⟨key h.symm, key h⟩

end events

/-! ## The counter searches of the keys against the view -/

section search

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- The value key `K` signs. -/
def kVal (K : Key) : Digest :=
  valsOf v (msgPos K)

/-- **The selection of key `K`'s counter search** against the view `t`. -/
def kSel (t : SpongeKeys X Z) (K : Key) : Option (EncodingCounter × Encoding) :=
  grindKV pub t K (kVal v K) encodingAttemptLimit 0

/-- The record of a found selection of key `K` against the view `t`: its block and digest. -/
def kRecOf (t : SpongeKeys X Z) (K : Key) (sel : EncodingCounter × Encoding) : X × Digest :=
  ((blocks (encIn pub K (kVal v K) sel.1)).headD 0, encDigest pub t K (kVal v K) sel.1)

/-- **The record of key `K`'s counter search** against the view `t`. -/
def kRec (t : SpongeKeys X Z) (K : Key) : Option (X × Digest) :=
  (kSel pub v t K).map (kRecOf pub v t K)

/-- The memory after key `K`'s counter search against the view `t`. -/
noncomputable def kMem (t : SpongeKeys X Z) (K : Key) (m : Selections) : Selections :=
  grindMemK pub t K (kVal v K) encodingAttemptLimit 0 m

variable {pub v}

theorem decode_of_grindKV (t : SpongeKeys X Z) (K : Key) (m : Digest) :
    ∀ {n c : ℕ} {sel : EncodingCounter × Encoding}, grindKV pub t K m n c = some sel →
      TargetSum.decodeDigest (encDigest pub t K m sel.1) = some sel.2
  | 0, _, _, h => by simp [grindKV] at h
  | n + 1, c, sel, h => by
    simp only [grindKV] at h
    split at h
    · next x hx =>
      cases h
      exact hx
    · exact decode_of_grindKV t K m h

theorem grindKV_spec (t : SpongeKeys X Z) (K : Key) (m : Digest) :
    ∀ {n c : ℕ} {sel : EncodingCounter × Encoding}, grindKV pub t K m n c = some sel →
      ∃ k, c ≤ k ∧ k < c + n ∧ sel.1 = BitVec.ofNat counterBits k
  | 0, _, _, h => by simp [grindKV] at h
  | n + 1, c, sel, h => by
    simp only [grindKV] at h
    split at h
    · cases h
      exact ⟨c, le_rfl, by omega, rfl⟩
    · obtain ⟨k, hk, hk', hs⟩ := grindKV_spec t K m h
      exact ⟨k, by omega, by omega, hs⟩

/-- The search depends on the view only through the digests of its trials. -/
theorem grindKV_congr {t t' : SpongeKeys X Z} (K : Key) (m : Digest) :
    ∀ {n c : ℕ}, (∀ k, c ≤ k → k < c + n →
      encDigest pub t K m (BitVec.ofNat counterBits k) =
        encDigest pub t' K m (BitVec.ofNat counterBits k)) →
      grindKV pub t K m n c = grindKV pub t' K m n c
  | 0, _, _ => rfl
  | n + 1, c, h => by
    simp only [grindKV]
    rw [h c le_rfl (by omega), grindKV_congr K m fun k hk hk' ↦ h k (by omega) (by omega)]

theorem encDigest_eq_absorb (t : SpongeKeys X Z) (K : Key) (m : Digest) (c : EncodingCounter) :
    encDigest pub t K m c =
      trunc128 (absorb (spongePerm t pub.perm) (blocks (encIn pub K m c))).1 :=
  rfl

/-- **Off the trial-hit event, the keys' trials read alike in views agreeing off the programmable
cells.** -/
theorem encDigest_congr {s : SReg} (hs : s ∉ TrialHit pub v) {t' : SpongeKeys X Z}
    (h : OffAgree (ProgCell pub v) (regFns s) t') (l : Layer) (idx : Index) {k : ℕ}
    (hk : k < encodingAttemptLimit) :
    encDigest pub t' (keyOf l idx) (kVal v (keyOf l idx)) (BitVec.ofNat counterBits k) =
      encDigest pub (regFns s) (keyOf l idx) (kVal v (keyOf l idx))
        (BitVec.ofNat counterBits k) := by
  have hav : ∀ rd ∈ inputReads (regFns s) pub.perm (encIn pub (keyOf l idx)
      (valsOf v (msgPos (keyOf l idx))) (BitVec.ofNat counterBits k)),
      ¬ProgCell pub v rd.point := fun rd hrd hin ↦ hs ⟨l, idx, k, hk, rd, hrd, hin⟩
  have hab := (inputReads_eq_of_offAgree h pub.perm _ hav).2
  rw [encDigest_eq_absorb, encDigest_eq_absorb]
  exact congrArg (fun st : X × Z ↦ trunc128 st.1) hab

theorem kSel_congr {s : SReg} (hs : s ∉ TrialHit pub v) {t' : SpongeKeys X Z}
    (h : OffAgree (ProgCell pub v) (regFns s) t') (l : Layer) (idx : Index) :
    kSel pub v t' (keyOf l idx) = kSel pub v (regFns s) (keyOf l idx) :=
  grindKV_congr _ _ fun k _ hk ↦ encDigest_congr hs h l idx (by simpa using hk)

theorem kRec_congr {s : SReg} (hs : s ∉ TrialHit pub v) {t' : SpongeKeys X Z}
    (h : OffAgree (ProgCell pub v) (regFns s) t') (l : Layer) (idx : Index) :
    kRec pub v t' (keyOf l idx) = kRec pub v (regFns s) (keyOf l idx) := by
  unfold kRec
  rw [kSel_congr hs h l idx]
  rcases hg : kSel pub v (regFns s) (keyOf l idx) with _ | sel
  · rw [Option.map_none, Option.map_none]
  · obtain ⟨k, -, hk, hsel⟩ := grindKV_spec _ _ _ hg
    have he := encDigest_congr hs h l idx (k := k) (by simpa using hk)
    rw [← hsel] at he
    rw [Option.map_some, Option.map_some, kRecOf, kRecOf, he]

theorem kMem_apply_of_ne (t : SpongeKeys X Z) (K : Key) (m : Selections) {K' : Key}
    (h : K' ≠ K) : kMem pub v t K m K' = m K' := by
  unfold kMem grindMemK
  rcases m K with _ | b
  · rcases grindKV pub t K (kVal v K) encodingAttemptLimit 0 with _ | ⟨cc, x⟩
    · rfl
    · exact Selections.select_of_ne m _ _ h
  · rfl

theorem kMem_of_some {t : SpongeKeys X Z} {K : Key} {m : Selections} {b : X × Digest}
    (hm : m K = some b) : kMem pub v t K m = m := by
  unfold kMem grindMemK
  rw [hm]

theorem kMem_of_none {t : SpongeKeys X Z} {K : Key} {m : Selections}
    (hg : kSel pub v t K = none) : kMem pub v t K m = m := by
  unfold kMem grindMemK
  rw [show grindKV pub t K (kVal v K) encodingAttemptLimit 0 = none from hg]
  cases m K <;> rfl

theorem kMem_of_found {t : SpongeKeys X Z} {K : Key} {m : Selections} (hm : m K = none)
    {sel : EncodingCounter × Encoding} (hg : kSel pub v t K = some sel) :
    kMem pub v t K m = m.select K (kRecOf pub v t K sel).1 (kRecOf pub v t K sel).2 := by
  unfold kMem grindMemK
  rw [hm, show grindKV pub t K (kVal v K) encodingAttemptLimit 0 = some sel from hg]
  rfl

/-- **After its search a key records its search against the view**, if it was unselected. -/
theorem kMem_self_of_none {t : SpongeKeys X Z} {K : Key} {m : Selections} (hm : m K = none) :
    kMem pub v t K m K = kRec pub v t K := by
  rcases hg : kSel pub v t K with _ | sel
  · rw [kMem_of_none hg, hm, kRec, hg, Option.map_none]
  · rw [kMem_of_found hm hg, Selections.select_self, kRec, hg, Option.map_some]

/-- A key's search keeps every selection. -/
theorem kMem_mono {t : SpongeKeys X Z} {K K' : Key} {m : Selections} {b : X × Digest}
    (h : m K' = some b) : kMem pub v t K m K' = some b := by
  by_cases e : K' = K
  · subst e
    rw [kMem_of_some h, h]
  · rw [kMem_apply_of_ne _ _ _ e, h]

end search

/-! ## The selections a memory records -/

section sel

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- **The selection function a memory records**: at a recorded key, the counter whose trial input
has the recorded block, and the word of the recorded digest. -/
noncomputable def selOfM (m : Selections) : SelFn := fun K ↦
  match m K with
  | none => none
  | some b => @dite _ (∃ c, blocks (encIn pub K (kVal v K) c) = [b.1])
      (Classical.propDecidable _) (fun h ↦ (TargetSum.decodeDigest b.2).map fun x ↦ (h.choose, x))
      fun _ ↦ none

variable {pub v}

theorem encIn_blocks_inj {K : Key} {m : Digest} {c c' : EncodingCounter}
    (h : blocks (encIn pub K m c) = blocks (encIn pub K m c')) : c = c' := by
  have h' := blocks_injective h
  unfold encIn at h'
  obtain ⟨-, hpay⟩ := addressedHashInput_injective _ h'
  obtain ⟨-, hc⟩ := List.append_inj' hpay (by simp [bigEndianBytes])
  exact bigEndianBytes_injective 4 hc

theorem selOfM_of_none {m : Selections} {K : Key} (hm : m K = none) :
    selOfM pub v m K = none := by
  unfold selOfM
  rw [hm]

theorem selOfM_of_eq {m : Selections} {K : Key} {b : X} {y : Digest} {c : EncodingCounter}
    {x : Encoding} (hm : m K = some (b, y)) (hb : blocks (encIn pub K (kVal v K) c) = [b])
    (hy : TargetSum.decodeDigest y = some x) : selOfM pub v m K = some (c, x) := by
  have hex : ∃ c', blocks (encIn pub K (kVal v K) c') = [(b, y).1] := ⟨c, hb⟩
  unfold selOfM
  rw [hm]
  dsimp only
  rw [dite_eq_left hex, hy, Option.map_some, encIn_blocks_inj (hex.choose_spec.trans hb.symm)]

/-- **What a recorded selection means**: the memory's entry is the selected trial's block with a
digest decoding to the selected word. -/
theorem selOfM_spec {m : Selections} {K : Key} {sel : EncodingCounter × Encoding}
    (h : selOfM pub v m K = some sel) :
    ∃ b y, m K = some (b, y) ∧ blocks (encIn pub K (kVal v K) sel.1) = [b] ∧
      TargetSum.decodeDigest y = some sel.2 := by
  unfold selOfM at h
  rcases hm : m K with _ | ⟨b, y⟩
  · rw [hm] at h
    exact absurd h (by simp)
  · rw [hm] at h
    dsimp only at h
    split_ifs at h with hb
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨b, y, rfl, hb.choose_spec, hx⟩

/-- **A memory records the selections of its own selection function** (Classify's
`RecordsSel`). -/
theorem recordsSel_selOfM (m : Selections) : (evData pub v).RecordsSel (selOfM pub v m) m := by
  intro K sel hs
  obtain ⟨b, y, hm, hb, hy⟩ := selOfM_spec hs
  exact ⟨b, y, hm, hb, hy⟩

/-- **A memory recording a key's search selects the search's selection.** -/
theorem selOfM_of_kRec {m : Selections} {t : SpongeKeys X Z} {K : Key}
    (h : m K = kRec pub v t K) : selOfM pub v m K = kSel pub v t K := by
  rcases hg : kSel pub v t K with _ | sel
  · rw [kRec, hg, Option.map_none] at h
    exact selOfM_of_none h
  · rw [kRec, hg, Option.map_some] at h
    exact selOfM_of_eq (b := (kRecOf pub v t K sel).1) (y := (kRecOf pub v t K sel).2) h
      (blocks_encIn pub K _ _) (decode_of_grindKV _ _ _ hg)

/-- The selection function grows with the selections. -/
theorem selOfM_mono {m m' : Selections} {K : Key} (h : ∀ b, m K = some b → m' K = some b)
    {sel : EncodingCounter × Encoding} (hs : selOfM pub v m K = some sel) :
    selOfM pub v m' K = some sel := by
  obtain ⟨b, y, hm, hb, hy⟩ := selOfM_spec hs
  exact selOfM_of_eq (h _ hm) hb hy

variable (d : EvData)

/-- **A signature depends on the selection only at the keys it reaches**: the bottom key, the
middle key if the bottom one is selected, the top key if both are. -/
theorem selSig_congr {S S' : SelFn} (R : Randomizer) (w : View)
    (h0 : S (keyOf 0 w.1) = S' (keyOf 0 w.1))
    (h1 : S' (keyOf 0 w.1) ≠ none → S (keyOf 1 w.1) = S' (keyOf 1 w.1))
    (h2 : S' (keyOf 0 w.1) ≠ none → S' (keyOf 1 w.1) ≠ none →
      S (keyOf 2 w.1) = S' (keyOf 2 w.1)) :
    d.selSig S R w = d.selSig S' R w := by
  unfold EvData.selSig EvData.selLayerSig
  rcases e0 : S' (keyOf 0 w.1) with _ | a
  · rw [h0, e0]
    rfl
  · have e1 := h1 (by rw [e0]; exact Option.some_ne_none a)
    rw [h0, e0, e1]
    rcases e1' : S' (keyOf 1 w.1) with _ | b
    · rfl
    · rw [h2 (by rw [e0]; exact Option.some_ne_none a) (by rw [e1']; exact Option.some_ne_none b)]

end sel

/-! ## The slots a signature makes public -/

section pubSlots

private theorem pp_shr_lt {a n k : ℕ} (ha : a < 2 ^ n) (hk : k ≤ n) : a >>> k < 2 ^ (n - k) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
    Nat.sub_add_cancel hk]
  exact ha

/-- The children of the parent of `b` are `b` and its sibling `b ^^^ 1`. -/
private theorem pp_children (b : ℕ) {P : ℕ → Prop} (h0 : P b) (h1 : P (b ^^^ 1)) :
    P (2 * (b >>> 1)) ∧ P (2 * (b >>> 1) + 1) := by
  rw [Nat.shiftRight_eq_div_pow, pow_one]
  rcases Nat.mod_two_eq_zero_or_one b with h2 | h2
  · have hx : b ^^^ 1 = b + 1 := Nat.xor_one_of_even (Nat.even_iff.2 h2)
    have e0 : 2 * (b / 2) = b := by omega
    rw [hx] at h1
    rw [e0]
    exact ⟨h0, h1⟩
  · have hx : b ^^^ 1 = b - 1 := Nat.xor_one_of_odd (Nat.odd_iff.2 h2)
    have e0 : 2 * (b / 2) = b - 1 := by omega
    have e1 : 2 * (b / 2) + 1 = b := by omega
    rw [hx] at h1
    rw [e1, e0]
    exact ⟨h1, h0⟩

/-- The slots of a FORS opening are in the table. -/
theorem forsSlots_inTable {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {s : Slot}
    (hs : s ∈ forsSlots idx lv) : InTable s := by
  simp only [forsSlots, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hs
  rcases hs with ⟨κ, rfl | ⟨h, hh, rfl⟩⟩ | rfl
  · trivial
  · exact ⟨by omega, by omega, pp_shr_lt (lv κ).isLt (by omega)⟩
  · trivial

/-- The slots of a layer signature by a key `K_l(idx)` are in the table. -/
theorem layerSlots_inTable (l : Layer) (idx : Index) (x : Encoding) {s : Slot}
    (hs : s ∈ layerSlots l (treeOfIndex l idx) (leafOfIndex l idx) x) : InTable s := by
  have hτ := treeOfIndex_lt_treeBits l idx
  have he := leafOfIndex_lt l idx
  simp only [layerSlots, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_cons, List.mem_map, List.mem_range, List.mem_filter] at hs
  rcases hs with ⟨i, step, -, rfl⟩ | rfl | ⟨lev, hlev, rfl⟩
  · exact ⟨hτ, he⟩
  · exact ⟨hτ, he⟩
  · exact ⟨hτ, by omega, by omega, pp_shr_lt he (by omega)⟩

/-- The FORS node above a known path node at height `z` has a known payload. -/
private theorem pp_fors_kids {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex}
    {κ : ForsTreeIndex} (z : ℕ) (hz : z < forsTreeHeight)
    (hp : Known (forsDisclosed idx lv) (fpos idx κ z ((lv κ).val >>> z))) :
    PayloadIn (Known (forsDisclosed idx lv))
      (.forsNode idx κ (z + 1) ((lv κ).val >>> (z + 1))) := by
  have hc := pp_children ((lv κ).val >>> z)
    (P := fun n ↦ Known (forsDisclosed idx lv) (fpos idx κ z n)) hp
    (Known.disclosed _ (Set.mem_ofPred.2 ⟨κ, Or.inr ⟨⟨z, hz⟩, rfl⟩⟩))
  rw [← Nat.shiftRight_add] at hc
  show Known _ (fpos idx κ (z + 1 - 1) _) ∧ Known _ (fpos idx κ (z + 1 - 1) _)
  rw [Nat.add_sub_cancel]
  exact hc

/-- The FORS path nodes of an opening are known. -/
private theorem pp_fors_path (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (κ : ForsTreeIndex) :
    ∀ z, z ≤ forsTreeHeight → Known (forsDisclosed idx lv) (fpos idx κ z ((lv κ).val >>> z))
  | 0, _ => by
    rw [Nat.shiftRight_zero]
    exact Known.forsLeaf idx κ (lv κ) (Known.disclosed _ (Set.mem_ofPred.2 ⟨κ, Or.inl rfl⟩))
  | z + 1, hz => by
    have hk := pp_fors_kids z (by omega) (pp_fors_path idx lv κ z (by omega))
    exact Known.forsNode idx κ (z + 1) _ ⟨by omega, hz, pp_shr_lt (lv κ).isLt hz⟩ hk.1 hk.2

/-- **A FORS opening's slots are public from its disclosure.** -/
theorem forsSlots_public {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {s : Slot}
    (hs : s ∈ forsSlots idx lv) : s ∈ Public (forsDisclosed idx lv) := by
  refine ⟨forsSlots_inTable hs, ?_⟩
  simp only [forsSlots, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hs
  rcases hs with ⟨κ, rfl | ⟨h, hh, rfl⟩⟩ | rfl
  · exact Known.disclosed _ (Set.mem_ofPred.2 ⟨κ, Or.inl rfl⟩)
  · exact pp_fors_kids h hh (pp_fors_path idx lv κ h (by omega))
  · exact fun κ ↦ by
      have h := pp_fors_path idx lv κ forsTreeHeight le_rfl
      rwa [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (lv κ).isLt] at h

/-- The chain positions from the opened one up are known. -/
private theorem pp_chain {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {x : Encoding}
    (hτ : τ.val < 2 ^ treeBits l) (he : e.val < 2 ^ layerHeight l) (i : ChainIndex) (j : ℕ)
    (hxj : (x i).val ≤ j) :
    j < chainLength → Known (layerDisclosed l τ e x) (cpos l τ e i j) := by
  induction j, hxj using Nat.le_induction with
  | base => exact fun _ ↦ Known.disclosed _ (Set.mem_ofPred.2 (Or.inl ⟨i, rfl⟩))
  | succ j _ ih =>
    intro hj
    exact Known.chain l τ e i ⟨j, by omega⟩ ⟨hτ, he⟩ (ih (by omega))

/-- The tree node above a known path node at level `z` has a known payload. -/
private theorem pp_layer_kids {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {x : Encoding}
    (z : ℕ) (hz : z < layerHeight l)
    (hp : Known (layerDisclosed l τ e x) (tpos l τ z (e.val >>> z))) :
    PayloadIn (Known (layerDisclosed l τ e x)) (.node l τ (z + 1) (e.val >>> (z + 1))) := by
  have hc := pp_children (e.val >>> z)
    (P := fun n ↦ Known (layerDisclosed l τ e x) (tpos l τ z n)) hp
    (Known.disclosed _ (Set.mem_ofPred.2 (Or.inr ⟨⟨z, hz⟩, rfl⟩)))
  rw [← Nat.shiftRight_add] at hc
  show Known _ (tpos l τ (z + 1 - 1) _) ∧ Known _ (tpos l τ (z + 1 - 1) _)
  rw [Nat.add_sub_cancel]
  exact hc

/-- The path nodes of a layer signature are known. -/
private theorem pp_layer_path {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {x : Encoding}
    (hτ : τ.val < 2 ^ treeBits l) (he : e.val < 2 ^ layerHeight l) :
    ∀ z, z ≤ layerHeight l → Known (layerDisclosed l τ e x) (tpos l τ z (e.val >>> z))
  | 0, _ => by
    rw [Nat.shiftRight_zero]
    exact Known.leaf l τ e ⟨hτ, he⟩ fun i ↦
      pp_chain hτ he i _ (by have := (x i).isLt; omega) (by have := (x i).isLt; omega)
  | z + 1, hz => by
    have hk := pp_layer_kids (x := x) z (by omega) (pp_layer_path (x := x) hτ he z (by omega))
    exact Known.node l τ (z + 1) _ ⟨hτ, by omega, hz, pp_shr_lt he hz⟩ hk.1 hk.2

/-- **A layer signature's slots are public from its disclosure.** -/
theorem layerSlots_public (l : Layer) (idx : Index) (x : Encoding) {s : Slot}
    (hs : s ∈ layerSlots l (treeOfIndex l idx) (leafOfIndex l idx) x) :
    s ∈ Public (layerDisclosed l (treeOfIndex l idx) (leafOfIndex l idx) x) := by
  refine ⟨layerSlots_inTable l idx x hs, ?_⟩
  have hτ := treeOfIndex_lt_treeBits l idx
  have he := leafOfIndex_lt l idx
  simp only [layerSlots, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_cons, List.mem_map, List.mem_range, List.mem_filter, decide_eq_true_eq] at hs
  rcases hs with ⟨i, step, hstep, rfl⟩ | rfl | ⟨lev, hlev, rfl⟩
  · have := step.isLt
    exact pp_chain hτ he i step.val hstep (by omega)
  · exact fun i ↦
      pp_chain hτ he i _ (by have := (x i).isLt; omega) (by have := (x i).isLt; omega)
  · exact pp_layer_kids lev hlev (pp_layer_path hτ he lev (by omega))

end pubSlots

/-! ## Marks, stream entries and digests -/

section labels

/-- No mark among the coordinates `U`. -/
def AsgFree (U : Finset HPos) : Prop :=
  ∀ M j, HPos.asg M j ∉ U

/-- **Each message has at most one mark** in the label `T`. -/
def MarksOK (T : Finset HPos) : Prop :=
  ∀ M j j', HPos.asg M j ∈ T → HPos.asg M j' ∈ T → j = j'

/-- **The `H_msg` outputs of `M` under `strPol`** at the label `T`. -/
noncomputable def digS (v : (s : HPos) → XD s) (T : Finset HPos) (M : Message) :
    DigestCall → HashOutput :=
  fun i ↦ hashOut (strPol.out T M i) (v (strPol.out T M i))

theorem asgFree_union {U U' : Finset HPos} (h : AsgFree U) (h' : AsgFree U') : AsgFree (U ∪ U') :=
  fun M j hm ↦ (Finset.mem_union.1 hm).elim (h M j) (h' M j)

theorem asgFree_valSet (U : Finset ValPos) : AsgFree (valSet U) := fun M j hm ↦ by
  obtain ⟨p, -, hp⟩ := Finset.mem_map.1 hm
  cases hp

theorem asgFree_rootRnd (M : Message) : AsgFree {.val rootPos, .rnd M} := fun M' j hm ↦ by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h <;> cases h

theorem marksOK_union {T U : Finset HPos} (hT : MarksOK T) (hU : AsgFree U) : MarksOK (T ∪ U) :=
  fun M j j' h h' ↦ hT M j j' ((Finset.mem_union.1 h).resolve_right (hU M j))
    ((Finset.mem_union.1 h').resolve_right (hU M j'))

theorem filter_isAsg_eq_empty {U : Finset HPos} (hU : AsgFree U) :
    U.filter (fun s ↦ s.isAsg = true) = ∅ := by
  refine Finset.filter_eq_empty_iff.2 fun s hs ha ↦ ?_
  cases s with
  | asg M j => exact hU M j hs
  | _ => cases ha

theorem asgCount_union_of_free {T U : Finset HPos} (hU : AsgFree U) :
    asgCount (T ∪ U) = asgCount T := by
  unfold asgCount
  rw [Finset.filter_union, filter_isAsg_eq_empty hU, Finset.union_empty]

/-- **The stream entry of a marked message** is its mark. -/
theorem streamIdx_of_mem {T : Finset HPos} (hT : MarksOK T) {M : Message}
    {j : Fin signatureLimit} (h : HPos.asg M j ∈ T) : streamIdx T M = some j := by
  have hex : ∃ j, HPos.asg M j ∈ T := ⟨j, h⟩
  unfold streamIdx
  rw [dite_eq_left hex]
  exact congrArg some (hT M _ _ (Classical.choose_spec hex) h)

theorem strPol_out_of_idx {T : Finset HPos} {M : Message} {j : Fin signatureLimit}
    (h : streamIdx T M = some j) (i : DigestCall) : strPol.out T M i = .str j i := by
  show (match streamIdx T M with
    | some j => HPos.str j i
    | none => .dig M i) = _
  rw [h]

theorem strPol_marks_of_idx {T : Finset HPos} {M : Message} {j : Fin signatureLimit}
    (h : streamIdx T M = some j) : strPol.marks T M = {.asg M j} := by
  show (match streamIdx T M with
    | some j => ({HPos.asg M j} : Finset HPos)
    | none => ∅) = _
  rw [h]

theorem strPol_marks_of_none {T : Finset HPos} {M : Message} (h : streamIdx T M = none) :
    strPol.marks T M = ∅ := by
  show (match streamIdx T M with
    | some j => ({HPos.asg M j} : Finset HPos)
    | none => ∅) = _
  rw [h]

theorem strPol_out_of_none {T : Finset HPos} {M : Message} (h : streamIdx T M = none)
    (i : DigestCall) : strPol.out T M i = .dig M i := by
  show (match streamIdx T M with
    | some j => HPos.str j i
    | none => .dig M i) = _
  rw [h]

/-- The digest of a message with stream entry `j` is the stream's entry. -/
theorem digS_of_idx (v : (s : HPos) → XD s) {T : Finset HPos} {M : Message}
    {j : Fin signatureLimit} (h : streamIdx T M = some j) :
    digS v T M = fun i ↦ (v (.str j i) : HashOutput) := by
  funext i
  unfold digS
  rw [strPol_out_of_idx h]
  rfl

theorem mem_need_asg {T : Finset HPos} {M M' : Message} {j : Fin signatureLimit}
    (h : HPos.asg M' j ∈ strPol.need T M) : M' = M ∧ streamIdx T M = some j := by
  unfold DigestPolicy.need at h
  rcases hs : streamIdx T M with _ | j₀
  · rw [strPol_out_of_none hs, strPol_out_of_none hs, strPol_marks_of_none hs] at h
    simp at h
  · rw [strPol_out_of_idx hs, strPol_out_of_idx hs, strPol_marks_of_idx hs] at h
    simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, false_or,
      HPos.asg.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem asgCount_need_le (T : Finset HPos) (M : Message) :
    asgCount (strPol.need T M) ≤ 1 := by
  unfold asgCount
  rcases hs : streamIdx T M with _ | j
  · refine (Finset.card_le_card (s := _) (t := ∅) fun s hs' ↦ ?_).trans (by simp)
    obtain ⟨hs', ha⟩ := Finset.mem_filter.1 hs'
    cases s with
    | asg M' j => exact absurd (mem_need_asg hs').2 (by rw [hs]; simp)
    | _ => cases ha
  · refine (Finset.card_le_card (t := {HPos.asg M j}) fun s hs' ↦ ?_).trans (by simp)
    obtain ⟨hs', ha⟩ := Finset.mem_filter.1 hs'
    cases s with
    | asg M' j' =>
      obtain ⟨rfl, h⟩ := mem_need_asg hs'
      rw [hs, Option.some.injEq] at h
      rw [h]
      exact Finset.mem_singleton_self _
    | _ => cases ha

/-- **The marks after a signature's digest reveal**: still at most one per message. -/
theorem marksOK_need {T : Finset HPos} (hT : MarksOK T) (M : Message) :
    MarksOK (T ∪ strPol.need T M) := by
  intro M' j j' h h'
  have key : ∀ {k}, HPos.asg M' k ∈ T ∪ strPol.need T M → (HPos.asg M' k ∈ T) ∨
      (M' = M ∧ streamIdx T M = some k) := fun hk ↦
    (Finset.mem_union.1 hk).imp id mem_need_asg
  rcases key h with h₁ | ⟨rfl, h₁⟩ <;> rcases key h' with h₂ | ⟨e, h₂⟩
  · exact hT M' j j' h₁ h₂
  · rw [e] at h₁
    rw [streamIdx_of_mem hT h₁, Option.some.injEq] at h₂
    exact h₂
  · rw [streamIdx_of_mem hT h₂, Option.some.injEq] at h₁
    exact h₁.symm
  · rw [h₁, Option.some.injEq] at h₂
    exact h₂

/-- **A message's stream entry after its digest reveal**: if the label had fewer marks than the
stream, the message has a stream entry, marked. -/
theorem idx_of_need {T : Finset HPos} (M : Message) (hc : asgCount T < signatureLimit) :
    ∃ j, streamIdx T M = some j ∧ HPos.asg M j ∈ T ∪ strPol.need T M := by
  rcases hs : streamIdx T M with _ | j
  · exfalso
    unfold streamIdx at hs
    split at hs
    · cases hs
    · simp at hs
  · refine ⟨j, rfl, Finset.mem_union_right _ ?_⟩
    unfold DigestPolicy.need
    rw [strPol_marks_of_idx hs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

end labels

/-! ## The hardwired `H_msg` calls -/

section held

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- **The hardwired cells hold `H_msg` call `i` on `M` with output `y`**: its `k`- and `k'`-cells,
and its `h`-cell with the value correcting the output to `y`. -/
def HHeldV (W : Hw X Z) (M : Message) (i : DigestCall) (y : HashOutput) : Prop :=
  HHeld pub v W M i ∧ W.1 (hZ pub v M i) = some (cor256 y
    (rnR pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 (hBlk pub v M i) 0)
      (pub.keys.1 (hZ pub v M i)))

variable {pub v}

theorem out256_add_embed256 (x : X) (y : HashOutput) :
    out256 (x + embed256 y) = out256 x ^^^ y := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj' : j < 256 := hj
  rw [BitVec.getLsbD_xor, Quantum.Xmss.getLsbD_out256 _ _ hj',
    Quantum.Xmss.getLsbD_out256 _ _ hj']
  have he : embed256 y ⟨j, by omega⟩ = Quantum.Xmss.bitOf (y.getLsbD j) := ite_eq_left hj'
  rw [Pi.add_apply, he]
  generalize x ⟨j, by omega⟩ = a
  cases y.getLsbD j <;> revert a <;> decide

/-- **The `H_msg` correction** makes the output `y`. -/
theorem out256_cor256 (y : HashOutput) (r w : X) : out256 (r + cor256 y r w) = y := by
  rw [cor256, ← add_assoc, out256_add_embed256, BitVec.xor_comm y, ← BitVec.xor_assoc,
    BitVec.xor_self, BitVec.zero_xor]

/- Matching Exempt's reads with Classify's `HashHeld` compares their sponge instances at the
Keccak sizes, deeper than the default recursion depth. -/
set_option maxRecDepth 8000 in
/-- **A held `H_msg` call is Classify's `HashHeld`** of its input with the output `y`. -/
theorem hashHeld_of_hHeldV {W : Hw X Z} (hkv : KeyVals pub W) {M : Message} {i : DigestCall}
    {y : HashOutput} (h : HHeldV pub v W M i y) :
    (evData pub v).HashHeld W.toDbs ((evData pub v).hmsgInput (rndOf v M) M i) y := by
  obtain ⟨⟨hk, hk'⟩, hz⟩ := h
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hk
  obtain ⟨a', ha'⟩ := Option.ne_none_iff_exists'.1 hk'
  have e1 := hkv.1 _ _ ha
  have e2 := hkv.2 _ _ ha'
  have hl : (blocks (slotInput pub.seed (.hmsg (rndOf v M) M i) (valsOf v))).length = 1 :=
    length_blocks_hmsg pub.seed (rndOf v M) M i (valsOf v)
  have hne : blocks (slotInput pub.seed (.hmsg (rndOf v M) M i) (valsOf v)) ≠ [] := fun h0 ↦ by
    rw [h0] at hl
    cases hl
  have hl1 :
      (blocks (slotInput pub.seed (.hmsg (rndOf v M) M i) (valsOf v))).length - 1 = 0 := by
    rw [hl]
  set h' : Z → X := Function.update pub.keys.1 (hZ pub v M i) (cor256 y
    (rnR pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 (hBlk pub v M i) 0)
      (pub.keys.1 (hZ pub v M i))) with hh'
  obtain ⟨hr, -, hh⟩ := held_update_final pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 hne
    (cor256 y) h' (by rw [hl1, hh']; exact Function.update_self _ _ _)
    (fun j hj ↦ absurd hj (by omega)) (U := W.toDbs) (fun j hj ↦ by
      obtain rfl : j = 0 := by omega
      rw [hl1, ite_eq_left rfl]
      refine ⟨?_, ?_, hz⟩
      · exact ha.trans (congrArg some e1)
      · exact ha'.trans (congrArg some e2))
  have hu : (evData pub v).hmsgInput (rndOf v M) M i =
      slotInput pub.seed (.hmsg (rndOf v M) M i) (valsOf v) := by
    unfold EvData.hmsgInput
    rfl
  have hp : (evData pub v).perm = pub.perm := rfl
  rw [hu]
  unfold EvData.HashHeld
  rw [hp]
  refine ⟨(h', pub.keys.2.1, pub.keys.2.2), hr, ?_⟩
  rw [hh, hl1]
  exact out256_cor256 _ _ _

/-- An in-table slot's honest path has no `H_msg` `h`-cell, on good data. -/
theorem not_slotPt_hZ (hsep : HmsgHSep pub v) {sl : Slot} (hsl : InTable sl) (M : Message)
    (i : DigestCall) : ¬slotPt pub v sl (.h (hZ pub v M i)) := by
  rintro ⟨j, hj, h | h | h⟩
  · cases h
  · cases h
  · exact hsep M i sl hsl j hj (SpongeQuery.h.inj h).symm

/-- A held `H_msg` call stays held along a move off its `h`-cell. -/
theorem HHeldV.of_moves {P : SpongeQuery X Z → Prop} {s s' : SReg} {M : Message}
    {i : DigestCall} {y : HashOutput} (h : HHeldV pub v s.2.1 M i y) (hm : Moves pub P s s')
    (hz : ¬P (.h (hZ pub v M i))) : HHeldV pub v s'.2.1 M i y :=
  ⟨⟨hm.grow (.k _) h.1.1, hm.grow (.k' _) h.1.2⟩, (hm.hw.1 _ hz).trans h.2⟩

end held

/-! ## A layer signature in the decompressed basis -/

section layer

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- The layer signature of a selection of key `K` at the values. -/
def kSig (K : Key) (sel : EncodingCounter × Encoding) : LayerSignature K.1 :=
  ⟨sel.1, fun i ↦ valsOf v (cpos K.1 K.2.1 K.2.2 i (sel.2 i).val),
    fun z ↦ valsOf v (siblingPos K.1 K.2.1 K.2.2 z)⟩

theorem selLayerSig_evData (S : SelFn) (l : Layer) (idx : Index) :
    (evData pub v).selLayerSig S l idx = (S (keyOf l idx)).map (kSig v (keyOf l idx)) :=
  rfl

/-- The cells a layer signature by `K` programs, from the register's view `t`: those of the found
word's slots. -/
def layerPt (t : SpongeKeys X Z) (K : Key) (q : SpongeQuery X Z) : Prop :=
  ∃ sel, kSel pub v t K = some sel ∧ ∃ sl ∈ layerSlots K.1 K.2.1 K.2.2 sel.2, slotPt pub v sl q

/-- **A layer signature's move of the register** from `s` to `s'` with output `o`: a move off the
found word's slot cells, the label grown by coordinates without marks, the memory after the
key's search against the view, the output the selection's layer signature. -/
structure LayerRelS (K : Key) (s : SReg) (o : Option (LayerSignature K.1)) (s' : SReg) :
    Prop where
  moves : Moves pub (layerPt pub v (regFns s) K) s s'
  lab : ∃ U, AsgFree U ∧ s'.2.2.1 = s.2.2.1 ∪ U
  mem : s'.2.2.2 = kMem pub v (regFns s) K s.2.2.2
  out : o = (kSel pub v (regFns s) K).map (kSig v K)

variable {pub v} {m₀ : Finset HPos × Selections}

/-- **A realized layer signature by `K_l(idx)` moves the register by `LayerRelS`.** -/
theorem ht₂_signLayerT (B : QReg) (l : Layer) (idx : Index) (P : Set SReg)
    (hP : ∀ s ∈ P, NoBot s) :
    HT₂ m₀ (realizeT v (signLayerT Selections cwUpd pub B (keyOf l idx))) P
      (fun o ↦ {s' | ∃ s ∈ P, LayerRelS pub v (keyOf l idx) s o s'}) := by
  unfold signLayerT
  refine ht₂_revealThen m₀ v _ _ P _ fun mem ↦ ?_
  rw [realizeT_bind₂, extendVals_restrictTo (Finset.mem_singleton_self _)]
  set P₁ : Set SReg := {s | ∃ s₀ ∈ P, s₀.2.2 = mem ∧
    s = (s₀.1, s₀.2.1, (s₀.2.2.1 ∪ {.val (msgPos (keyOf l idx))}, s₀.2.2.2))} with hP₁
  have hP₁nb : ∀ s ∈ P₁, NoBot s := by
    rintro s ⟨s₀, hs₀, -, rfl⟩
    exact hP s₀ hs₀
  refine HT₂.bind (det_grindK pub B (keyOf l idx) _ encodingAttemptLimit 0 P₁ hP₁nb) fun g ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · refine ht₂_pure none ?_
    rintro s' ⟨s₁, ⟨s₀, hs₀, -, rfl⟩, hg, rfl⟩
    refine ⟨s₀, hs₀, moves_of_eq _ (hP s₀ hs₀) rfl rfl,
      ⟨_, asgFree_valSet {msgPos (keyOf l idx)}, rfl⟩, rfl, ?_⟩
    have hg' : kSel pub v (regFns s₀) (keyOf l idx) = none := hg.symm
    rw [hg', Option.map_none]
  · refine ht₂_revealThen m₀ v _ _ _ _ fun mem' ↦ ?_
    rw [realizeT_bind₂]
    refine HT₂.bind (ht₂_progSlots m₀ v pub B _ _) fun _ ↦ ht₂_pure _ ?_
    rintro s₃ ⟨s₂, ⟨s₁', ⟨s₁, ⟨s₀, hs₀, -, rfl⟩, hg, rfl⟩, -, rfl⟩, hpr⟩
    have hsel : kSel pub v (regFns s₀) (keyOf l idx) = some (c, x) := hg.symm
    obtain ⟨hmv, hmem⟩ := ProgsRel.moves (P := layerPt pub v (regFns s₀) (keyOf l idx)) hpr
      (fun c' hc' ↦ by
        obtain ⟨sl, hsl, hpt, hkv⟩ := slotPorts_pt (pub := pub) v
          (fun sl hsl ↦ layerSlots_inTable l idx x hsl) hc'
        exact ⟨⟨(c, x), hsel, sl, hsl, hpt⟩, hkv⟩) (hP s₀ hs₀)
    refine ⟨s₀, hs₀, hmv.of_eq_left rfl rfl,
      ⟨{.val (msgPos (keyOf l idx))} ∪ valSet (layerNeed l (treeOfIndex l idx)
        (leafOfIndex l idx) x), asgFree_union (asgFree_valSet {msgPos (keyOf l idx)})
          (asgFree_valSet _), ?_⟩, ?_, ?_⟩
    · rw [congrArg Prod.fst hmem, Finset.union_assoc]
      rfl
    · rw [congrArg Prod.snd hmem]
      rfl
    · rw [hsel, Option.map_some]
      refine congrArg some (layerSignature_ext rfl (funext fun i ↦ ?_) (funext fun z ↦ ?_))
      · exact extendVals_restrictTo (val_mem_valSet.mpr (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))) v
      · exact extendVals_restrictTo (val_mem_valSet.mpr (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_univ z)))) v

end layer

/-! ## The head of a signature: the digest and the FORS opening -/

section head

section gen

variable {X₁ Z₁ : Type} [DecidableEq X₁] [DecidableEq Z₁]

theorem progUpdate_programK_self (x : X₁) (a : Z₁) (W : Hw X₁ Z₁) :
    (progUpdate (.programK x a) W).2.1 x = some a :=
  Function.update_self _ _ _

theorem progUpdate_programK'_self (x : X₁) (a : Z₁) (W : Hw X₁ Z₁) :
    (progUpdate (.programK' x a) W).2.2 x = some a :=
  Function.update_self _ _ _

theorem progUpdate_programH_self (z : Z₁) (a : X₁) (W : Hw X₁ Z₁) :
    (progUpdate (.programH z a) W).1 z = some a :=
  Function.update_self _ _ _

end gen

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- The FORS opening at the values of instance `idx` at the leaves `lv`. -/
def forsOpenOf (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    ForsTreeIndex → ForsTreeOpening :=
  fun κ ↦ ⟨valsOf v (.forsSecret idx κ (lv κ)), fun z ↦ valsOf v (forsSibPos idx lv κ z)⟩

/-- The cells of a FORS opening's slots. -/
def forsPt (w : View) (q : SpongeQuery X Z) : Prop :=
  ∃ sl ∈ forsSlots w.1 w.2, slotPt pub v sl q

/-- The cells a signature's head programs: both `H_msg` calls and the FORS opening's slots. -/
def headPt (M : Message) (w : View) (q : SpongeQuery X Z) : Prop :=
  hmsgPt pub v M 0 q ∨ hmsgPt pub v M 1 q ∨ forsPt pub v w q

/-- **The head's move of the register** from `s` to `s'` with the FORS opening `fo`, for the
message `M`: a move off the head's cells, the label grown by the digest's coordinates and further
coordinates without marks, the memory kept, the opening of the values at the digest's view, both
`H_msg` calls held with the digest (or a conflict), and every held `H_msg` call still held (or a
call of `M`, or a conflict). -/
structure HeadRel (M : Message) (s : SReg) (fo : ForsTreeIndex → ForsTreeOpening) (s' : SReg) :
    Prop where
  moves : Moves pub (headPt pub v M (digestView (digS v s.2.2.1 M))) s s'
  lab : ∃ U, AsgFree U ∧ s'.2.2.1 = (s.2.2.1 ∪ strPol.need s.2.2.1 M) ∪ U
  mem : s'.2.2.2 = s.2.2.2
  fo : fo = (evData pub v).forsOpen (digestView (digS v s.2.2.1 M))
  hmsg : (∀ c, HHeldV pub v s'.2.1 M c (digS v s.2.2.1 M c)) ∨ s' ∈ HConflict pub v
  old : ∀ M' c y, HHeldV pub v s.2.1 M' c y →
    HHeldV pub v s'.2.1 M' c y ∨ M' = M ∨ s' ∈ HConflict pub v

variable {pub v} {m₀ : Finset HPos × Selections}

theorem digestOf_need (T : Finset HPos) (M : Message) :
    digestOf strPol T M (restrictTo (strPol.need T M) v) = truncateMessageDigest (digS v T M) :=
  congrArg truncateMessageDigest (funext fun i ↦ extendOut_restrictTo (strPol.out_mem_need T M i) v)

theorem pathCells_one (b : ℕ → X) (cor : X → X → X) :
    pathCells pub b cor 1 = [.programK (cellK pub b 0).1 (cellK pub b 0).2,
      .programK' (cellK' pub b 0).1 (cellK' pub b 0).2,
      .programH (cellH pub b 0 cor 0).1 (cellH pub b 0 cor 0).2] :=
  rfl

theorem hmsgPt_h {M : Message} {i : DigestCall} {z : Z} (h : hmsgPt pub v M i (.h z)) :
    z = hZ pub v M i := by
  obtain ⟨j, hj, h | h | h⟩ := h
  · cases h
  · cases h
  · obtain rfl : j = 0 := by omega
    exact SpongeQuery.h.inj h

/-- **An `H_msg` batch**: the realized ports of call `c` on `M` at the label `T` move the register
off the call's cells, keep the memory, and hold the call with the digest. -/
theorem hmsgBatch {T : Finset HPos} {M : Message} {c : DigestCall} {s s' : SReg}
    (h : ProgsRel ((hmsgPorts pub strPol T M c).map (·.realize v)) s s') (hs : NoBot s) :
    Moves pub (hmsgPt pub v M c) s s' ∧ s'.2.2 = s.2.2 ∧
      HHeldV pub v s'.2.1 M c (digS v T M c) := by
  rw [realize_hmsgPorts] at h
  obtain ⟨hm, hmem⟩ := ProgsRel.moves h (fun c' hc' ↦ mem_pathCells hc') hs
  rw [pathCells_one] at h
  obtain ⟨m1, r1, m2, r2, m3, r3, e⟩ := h
  change m3 = s' at e
  subst e
  have hW : m3.2.1 = progUpdate (.programH (cellH pub (hBlk pub v M c) 0
      (cor256 (digS v T M c)) 0).1 (cellH pub (hBlk pub v M c) 0 (cor256 (digS v T M c)) 0).2)
      (progUpdate (.programK' (cellK' pub (hBlk pub v M c) 0).1
        (cellK' pub (hBlk pub v M c) 0).2) (progUpdate (.programK (cellK pub (hBlk pub v M c) 0).1
          (cellK pub (hBlk pub v M c) 0).2) s.2.1)) := by
    rw [congrArg Prod.fst r3.1, congrArg Prod.fst r2.1, congrArg Prod.fst r1.1]
    rfl
  refine ⟨hm, hmem, ⟨?_, ?_⟩, ?_⟩
  · rw [hW]
    refine progUpdate_k_ne_none _ (progUpdate_k_ne_none _ ?_)
    rw [progUpdate_programK_self]
    exact Option.some_ne_none _
  · rw [hW]
    refine progUpdate_k'_ne_none _ ?_
    rw [progUpdate_programK'_self]
    exact Option.some_ne_none _
  · rw [hW]
    have h1 := cellH_fst pub (hBlk pub v M c) 0 (cor256 (digS v T M c)) 0
    have h2 := cellH_snd pub (hBlk pub v M c) 0 (cor256 (digS v T M c)) 0
    rw [ite_eq_left rfl] at h2
    show (progUpdate _ _).1 (rnZ pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2 (hBlk pub v M c) 0) =
      _
    rw [← h1, progUpdate_programH_self, h2]
    rfl

/-- **An old held `H_msg` call through an `H_msg` batch**: still held, or the batch's call, or a
conflict. -/
theorem held_after_batch {s s' : SReg} {M M' : Message} {c c' : DigestCall} {y y' : HashOutput}
    (hm : Moves pub (hmsgPt pub v M c) s s') (hnew : HHeldV pub v s'.2.1 M c y)
    (hold : HHeldV pub v s.2.1 M' c' y') :
    HHeldV pub v s'.2.1 M' c' y' ∨ (M', c') = (M, c) ∨ s' ∈ HConflict pub v := by
  by_cases hz : hZ pub v M' c' = hZ pub v M c
  · by_cases e : (M', c') = (M, c)
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr ⟨M', c', M, c, e, ⟨hm.grow (.k _) hold.1.1, hm.grow (.k' _) hold.1.2⟩,
        hnew.1, hz⟩)
  · exact Or.inl (hold.of_moves hm fun h ↦ hz (hmsgPt_h h))

omit pub in
theorem forsNeed_unfold (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    forsNeed idx lv = needUnion (forsSlots idx lv) ∪
      Finset.univ.image (fun κ ↦ ValPos.forsSecret idx κ (lv κ)) ∪
      Finset.univ.image
        (fun p : ForsTreeIndex × Fin forsTreeHeight ↦ forsSibPos idx lv p.1 p.2) := by
  rw [forsNeed]

/- Membership in the concrete FORS opening's sets is otherwise decided by evaluating them. -/
attribute [local irreducible] forsNeed forsSlots

omit pub in
theorem forsSecret_mem_valSet (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (κ : ForsTreeIndex) : HPos.val (.forsSecret idx κ (lv κ)) ∈ valSet (forsNeed idx lv) := by
  rw [forsNeed_unfold]
  exact val_mem_valSet.mpr (Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ κ))))

omit pub in
theorem forsSibPos_mem_valSet (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (κ : ForsTreeIndex) (z : Fin forsTreeHeight) :
    HPos.val (forsSibPos idx lv κ z) ∈ valSet (forsNeed idx lv) := by
  rw [forsNeed_unfold]
  exact val_mem_valSet.mpr (Finset.mem_union_right _
    (Finset.mem_image_of_mem (fun p : ForsTreeIndex × Fin forsTreeHeight ↦
      forsSibPos idx lv p.1 p.2) (Finset.mem_univ (κ, z))))

/-- **A realized FORS opening**: the label grown by its coordinates, the memory kept, a move off its
slots' cells, the opening of the values. -/
theorem ht₂_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (P : Set SReg) (hP : ∀ s ∈ P, NoBot s) :
    HT₂ m₀ (realizeT v (forsOpenT Selections pub B idx lv)) P (fun fo ↦ {s' | ∃ s ∈ P,
      fo = forsOpenOf v idx lv ∧ s'.2.2 = (s.2.2.1 ∪ valSet (forsNeed idx lv), s.2.2.2) ∧
        Moves pub (forsPt pub v (idx, lv)) s s'}) := by
  unfold forsOpenT
  refine ht₂_revealThen m₀ v _ _ P _ fun mem ↦ ?_
  rw [realizeT_bind₂]
  refine HT₂.bind (ht₂_progSlots m₀ v pub B _ _) fun _ ↦ ht₂_pure _ ?_
  rintro s₂ ⟨s₁, ⟨s₀, hs₀, -, rfl⟩, hpr⟩
  obtain ⟨hmv, hmem⟩ := ProgsRel.moves (P := forsPt pub v (idx, lv)) hpr
    (fun c' hc' ↦ by
      obtain ⟨sl, hsl, hpt, hkv⟩ := slotPorts_pt (pub := pub) v
        (fun sl hsl ↦ forsSlots_inTable hsl) hc'
      exact ⟨⟨sl, hsl, hpt⟩, hkv⟩) (hP s₀ hs₀)
  refine ⟨s₀, hs₀, funext fun κ ↦ forsTreeOpening_ext
    (extendVals_restrictTo (forsSecret_mem_valSet idx lv κ) v)
    (funext fun z ↦ extendVals_restrictTo (forsSibPos_mem_valSet idx lv κ z) v), hmem,
    hmv.of_eq_left rfl rfl⟩

/-- **The head's move** from the realized reveals, `H_msg` batches and FORS opening. -/
theorem headRel_of (hsep : HmsgHSep pub v) {M : Message} {s₀ s₂ s₃ s₄ : SReg}
    {fo : ForsTreeIndex → ForsTreeOpening} (hnb : NoBot s₀)
    (h₂ : s₂ = (s₀.1, s₀.2.1, (s₀.2.2.1 ∪ {.val rootPos, .rnd M} ∪ strPol.need s₀.2.2.1 M,
      s₀.2.2.2)))
    (h₃ : ProgsRel ((digestPorts pub strPol s₀.2.2.1 M).map (·.realize v)) s₂ s₃)
    (hfo : fo = forsOpenOf v (digestView (digS v s₀.2.2.1 M)).1
      (digestView (digS v s₀.2.2.1 M)).2)
    (h₄2 : s₄.2.2 = (s₃.2.2.1 ∪ valSet (forsNeed (digestView (digS v s₀.2.2.1 M)).1
      (digestView (digS v s₀.2.2.1 M)).2), s₃.2.2.2))
    (h₄ : Moves pub (forsPt pub v (digestView (digS v s₀.2.2.1 M))) s₃ s₄) :
    HeadRel pub v M s₀ fo s₄ := by
  set w := digestView (digS v s₀.2.2.1 M) with hw
  rw [digestPorts, List.map_append] at h₃
  obtain ⟨sa, ha, hb⟩ := progsRel_append_inv h₃
  have hnb₂ : NoBot s₂ := by rw [h₂]; exact hnb
  obtain ⟨ma, mema, hela⟩ := hmsgBatch ha hnb₂
  obtain ⟨mb, memb, helb⟩ := hmsgBatch hb ma.noBot
  have hfors : ∀ M' c, ¬forsPt pub v w (.h (hZ pub v M' c)) := fun M' c ⟨sl, hsl, hpt⟩ ↦
    not_slotPt_hZ hsep (forsSlots_inTable hsl) M' c hpt
  have hs₂1 : s₂.1 = s₀.1 := by rw [h₂]
  have hs₂2 : s₂.2.1 = s₀.2.1 := by rw [h₂]
  have hmv : Moves pub (headPt pub v M w) s₀ s₄ :=
    (((ma.of_eq_left hs₂1 hs₂2).trans mb).trans h₄).mono fun q hq ↦ by
      rcases hq with (hq | hq) | hq
      · exact Or.inl hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr hq)
  refine ⟨hmv, ⟨{.val rootPos, .rnd M} ∪ valSet (forsNeed w.1 w.2),
    asgFree_union (asgFree_rootRnd M) (asgFree_valSet _), ?_⟩, ?_, hfo, ?_, ?_⟩
  · rw [congrArg Prod.fst h₄2, congrArg Prod.fst memb, congrArg Prod.fst mema, h₂]
    show s₀.2.2.1 ∪ {.val rootPos, .rnd M} ∪ strPol.need s₀.2.2.1 M ∪ valSet (forsNeed w.1 w.2) = _
    rw [Finset.union_right_comm s₀.2.2.1, Finset.union_assoc]
  · rw [congrArg Prod.snd h₄2, congrArg Prod.snd memb, congrArg Prod.snd mema, h₂]
  · rcases held_after_batch mb helb hela with h0 | h0 | h0
    · exact Or.inl fun c ↦ by
        rcases digestCall_cases c with rfl | rfl
        · exact h0.of_moves h₄ (hfors M 0)
        · exact helb.of_moves h₄ (hfors M 1)
    · exact absurd (congrArg Prod.snd h0).symm digestCall_one_ne_zero
    · exact Or.inr (HConflict.mono h₄.grow h0)
  · intro M' c y hold
    have hold₂ : HHeldV pub v s₂.2.1 M' c y := by rw [hs₂2]; exact hold
    rcases held_after_batch ma hela hold₂ with h1 | h1 | h1
    · rcases held_after_batch mb helb h1 with h2 | h2 | h2
      · exact Or.inl (h2.of_moves h₄ (hfors M' c))
      · exact Or.inr (Or.inl (congrArg Prod.fst h2))
      · exact Or.inr (Or.inr (HConflict.mono h₄.grow h2))
    · exact Or.inr (Or.inl (congrArg Prod.fst h1))
    · exact Or.inr (Or.inr (HConflict.mono h₄.grow (HConflict.mono mb.grow h1)))

end head

/-! ## The prefix invariant -/

section inv

variable (pub : Pub) (v : (s : HPos) → XD s)

/-- **The keys a signature on index `idx` searched record their searches** against the view `t`:
the bottom key, the middle key if the bottom search found a selection, the top key if both
did. -/
def Done (t : SpongeKeys X Z) (m : Selections) (idx : Index) : Prop :=
  m (keyOf 0 idx) = kRec pub v t (keyOf 0 idx) ∧ (kSel pub v t (keyOf 0 idx) ≠ none →
    m (keyOf 1 idx) = kRec pub v t (keyOf 1 idx) ∧ (kSel pub v t (keyOf 1 idx) ≠ none →
      m (keyOf 2 idx) = kRec pub v t (keyOf 2 idx)))

/-- **The facts of the register off the events** for the signed entries `rs` (their signatures
and searched keys) and the messages `msgs` whose signatures are under way or done: the messages
marked, every selection the search against the view, the searched keys recorded, the signatures
those of the view's selections, every hardwired cell on a public slot's honest path or an
`H_msg` call of a message, and both `H_msg` calls of every message held with its digest. -/
structure CoreFacts (rs : SignLog Message (Option Signature)) (msgs : List Message) (s : SReg) :
    Prop where
  marked : ∀ M ∈ msgs, ∃ j, HPos.asg M j ∈ s.2.2.1
  keys : ∀ K, s.2.2.2 K ≠ none → s.2.2.2 K = kRec pub v (regFns s) K
  done : ∀ r ∈ rs, Done pub v (regFns s) s.2.2.2 (digestView (digS v s.2.2.1 r.1)).1
  sigs : ∀ r ∈ rs, r.2 = (evData pub v).selSig (kSel pub v (regFns s)) (rndOf v r.1)
    (digestView (digS v s.2.2.1 r.1))
  cells : ∀ q, InHw s.2.1 q →
    (∃ sl ∈ Public (selDisclosures (selOfM pub v s.2.2.2) (digS v s.2.2.1) msgs),
      slotPt pub v sl q) ∨ ∃ M ∈ msgs, ∃ i, hmsgPt pub v M i q
  held : ∀ M ∈ msgs, ∀ i, HHeldV pub v s.2.1 M i (digS v s.2.2.1 M i)

/-- **The facts of every register** after `n` signatures: no empty cell, at most one mark per
message and at most `n` marks, the public key values hardwired, only keys `K_l(idx)`
selected. -/
structure SBase (n : ℕ) (s : SReg) : Prop where
  noBot : NoBot s
  marks : MarksOK s.2.2.1
  count : asgCount s.2.2.1 ≤ n
  keyVals : KeyVals pub s.2.1
  ground : ∀ K, s.2.2.2 K ≠ none → ∃ l idx, K = keyOf l idx

/-- **The prefix invariant** after the transcript `log`: the base facts, and off the trial-hit and
conflict events, within the signature limit, the facts of `log`. -/
def InvS (log : SignLog Message (Option Signature)) : Set SReg :=
  {s | SBase pub log.length s ∧ (s ∉ TrialHit pub v → s ∉ HConflict pub v →
    log.length ≤ signatureLimit → CoreFacts pub v log (log.map Sigma.fst) s)}

variable {pub v}

theorem asgCount_union_le (T U : Finset HPos) : asgCount (T ∪ U) ≤ asgCount T + asgCount U := by
  unfold asgCount
  rw [Finset.filter_union]
  exact Finset.card_union_le _ _

/-- The digest of a marked message stays as the label grows. -/
theorem digS_stable {T T' : Finset HPos} (hT : MarksOK T) (hT' : MarksOK T') (hsub : T ⊆ T')
    {M : Message} {j : Fin signatureLimit} (h : HPos.asg M j ∈ T) : digS v T' M = digS v T M := by
  rw [digS_of_idx v (streamIdx_of_mem hT' (hsub h)), digS_of_idx v (streamIdx_of_mem hT h)]

theorem selDisclosures_mono {S S' : SelFn} {dig dig' : Message → DigestCall → HashOutput}
    {msgs msgs' : List Message}
    (hS : ∀ l idx sel, S (keyOf l idx) = some sel → S' (keyOf l idx) = some sel)
    (hd : ∀ M ∈ msgs, dig M = dig' M) (hsub : msgs ⊆ msgs') :
    selDisclosures S dig msgs ⊆ selDisclosures S' dig' msgs' := by
  rintro p (hp | ⟨M, hM, hp⟩)
  · exact Or.inl hp
  · refine Or.inr ⟨M, hsub hM, ?_⟩
    rw [← hd M hM]
    rcases hp with hp | ⟨l, sel, hsel, hp⟩
    · exact Or.inl hp
    · exact Or.inr ⟨l, sel, hS l _ sel hsel, hp⟩

theorem selSig_congr_all (d : EvData) {S S' : SelFn} (R : Randomizer) (w : View)
    (hS : ∀ l, S (keyOf l w.1) = S' (keyOf l w.1)) : d.selSig S R w = d.selSig S' R w :=
  selSig_congr d R w (hS 0) (fun _ ↦ hS 1) (fun _ _ ↦ hS 2)

theorem headPt_progCell {M : Message} {w : View} {q : SpongeQuery X Z}
    (h : headPt pub v M w q) : ProgCell pub v q := by
  rcases h with h | h | ⟨sl, hsl, h⟩
  · exact Or.inr ⟨M, 0, h⟩
  · exact Or.inr ⟨M, 1, h⟩
  · exact Or.inl ⟨sl, forsSlots_inTable hsl, h⟩

theorem layerPt_progCell {t : SpongeKeys X Z} {l : Layer} {idx : Index} {q : SpongeQuery X Z}
    (h : layerPt pub v t (keyOf l idx) q) : ProgCell pub v q := by
  obtain ⟨sel, -, sl, hsl, h⟩ := h
  exact Or.inl ⟨sl, layerSlots_inTable l idx sel.2 hsl, h⟩

/-- A key's search keeps every recorded search, if the memory's selections are the view's. -/
theorem kMem_preserve {t : SpongeKeys X Z} {K K' : Key} {m : Selections}
    (hkeys : m K ≠ none → m K = kRec pub v t K) (h : m K' = kRec pub v t K') :
    kMem pub v t K m K' = kRec pub v t K' := by
  by_cases hK : K' = K
  · subst hK
    rcases hm : m K' with _ | b
    · exact kMem_self_of_none hm
    · rw [kMem_of_some hm, hm]
      rw [hm] at h
      exact h
  · rw [kMem_apply_of_ne _ _ _ hK]
    exact h

theorem keyOf_ne {l l' : Layer} (idx idx' : Index) (h : l ≠ l') : keyOf l idx ≠ keyOf l' idx' :=
  fun he ↦ h (congrArg Prod.fst he)

/-- **The base facts after the head**, with one more possible mark. -/
theorem base_head {n : ℕ} {M : Message} {s s' : SReg} {fo : ForsTreeIndex → ForsTreeOpening}
    (hb : SBase pub n s) (hH : HeadRel pub v M s fo s') : SBase pub (n + 1) s' := by
  obtain ⟨U, hU, hlab⟩ := hH.lab
  refine ⟨hH.moves.noBot, ?_, ?_, hH.moves.keyVals hb.keyVals, ?_⟩
  · rw [hlab]
    exact marksOK_union (marksOK_need hb.marks M) hU
  · rw [hlab, asgCount_union_of_free hU]
    exact (asgCount_union_le _ _).trans (add_le_add hb.count (asgCount_need_le _ M))
  · rw [hH.mem]
    exact hb.ground

/-- **The base facts after a layer signature.** -/
theorem base_layer {n : ℕ} {l : Layer} {idx : Index} {s s' : SReg}
    {o : Option (LayerSignature (keyOf l idx).1)} (hb : SBase pub n s)
    (hL : LayerRelS pub v (keyOf l idx) s o s') : SBase pub n s' := by
  obtain ⟨U, hU, hlab⟩ := hL.lab
  refine ⟨hL.moves.noBot, ?_, ?_, hL.moves.keyVals hb.keyVals, fun K hK ↦ ?_⟩
  · rw [hlab]
    exact marksOK_union hb.marks hU
  · rw [hlab, asgCount_union_of_free hU]
    exact hb.count
  · by_cases e : K = keyOf l idx
    · exact ⟨l, idx, e⟩
    · rw [hL.mem, kMem_apply_of_ne _ _ _ e] at hK
      exact hb.ground K hK

theorem inHw_of_hwOff {P : SpongeQuery X Z → Prop} {W W' : Hw X Z} (h : HwOff P W W')
    {q : SpongeQuery X Z} (hq : ¬P q) (hin : InHw W' q) : InHw W q := by
  cases q with
  | h z => exact fun h0 ↦ hin (by show W'.1 z = none; rw [h.1 z hq]; exact h0)
  | k x => exact fun h0 ↦ hin (by show W'.2.1 x = none; rw [h.2.1 x hq]; exact h0)
  | k' x => exact fun h0 ↦ hin (by show W'.2.2 x = none; rw [h.2.2 x hq]; exact h0)

/-- **The facts after the head** of `M`'s signature, off the events and below the limit: those
of the transcript, with `M` among the messages. -/
theorem core_head {log : SignLog Message (Option Signature)}
    {M : Message} {s s' : SReg} {fo : ForsTreeIndex → ForsTreeOpening}
    (hb : SBase pub log.length s) (hF : CoreFacts pub v log (log.map Sigma.fst) s)
    (hH : HeadRel pub v M s fo s') (hhit : s ∉ TrialHit pub v) (hconf : s' ∉ HConflict pub v)
    (hlim : log.length < signatureLimit) :
    CoreFacts pub v log (log.map Sigma.fst ++ [M]) s' ∧ digS v s'.2.2.1 M = digS v s.2.2.1 M := by
  obtain ⟨U, hU, hlab⟩ := hH.lab
  have hT' : MarksOK s'.2.2.1 := by
    rw [hlab]
    exact marksOK_union (marksOK_need hb.marks M) hU
  have hsub : s.2.2.1 ⊆ s'.2.2.1 := by
    rw [hlab]
    exact Finset.subset_union_left.trans Finset.subset_union_left
  have hview : OffAgree (ProgCell pub v) (regFns s) (regFns s') :=
    hH.moves.view.mono fun _ ↦ headPt_progCell
  have hsel := fun l idx ↦ kSel_congr hhit hview l idx
  have hrec := fun l idx ↦ kRec_congr hhit hview l idx
  obtain ⟨j, hj, hjm⟩ := idx_of_need M (lt_of_le_of_lt hb.count hlim)
  have hjm' : HPos.asg M j ∈ s'.2.2.1 := by
    rw [hlab]
    exact Finset.mem_union_left _ hjm
  have hdM : digS v s'.2.2.1 M = digS v s.2.2.1 M := by
    rw [digS_of_idx v (streamIdx_of_mem hT' hjm'), digS_of_idx v hj]
  have hdold : ∀ M' ∈ log.map Sigma.fst, digS v s'.2.2.1 M' = digS v s.2.2.1 M' := fun M' hM' ↦ by
    obtain ⟨j', hj'⟩ := hF.marked M' hM'
    exact digS_stable hb.marks hT' hsub hj'
  have hmM : M ∈ log.map Sigma.fst ++ [M] := List.mem_append_right _ (List.mem_singleton_self M)
  refine ⟨⟨fun M' hM' ↦ ?_, fun K hK ↦ ?_, fun r hr ↦ ?_, fun r hr ↦ ?_, fun q hq ↦ ?_,
    fun M' hM' i ↦ ?_⟩, hdM⟩
  · rcases List.mem_append.1 hM' with h | h
    · obtain ⟨j', hj'⟩ := hF.marked M' h
      exact ⟨j', hsub hj'⟩
    · rw [List.mem_singleton.1 h]
      exact ⟨j, hjm'⟩
  · rw [hH.mem] at hK ⊢
    obtain ⟨l, idx, rfl⟩ := hb.ground K hK
    rw [hF.keys _ hK, hrec]
  · have hm := hF.done r hr
    rw [hH.mem, hdold r.1 (List.mem_map.2 ⟨r, hr, rfl⟩)]
    obtain ⟨h0, h1⟩ := hm
    refine ⟨by rw [hrec]; exact h0, fun hne ↦ ?_⟩
    rw [hsel] at hne
    obtain ⟨h1a, h1b⟩ := h1 hne
    refine ⟨by rw [hrec]; exact h1a, fun hne' ↦ ?_⟩
    rw [hsel] at hne'
    rw [hrec]
    exact h1b hne'
  · rw [hF.sigs r hr, hdold r.1 (List.mem_map.2 ⟨r, hr, rfl⟩)]
    exact selSig_congr_all _ _ _ fun l ↦ (hsel l _).symm
  · by_cases hp : headPt pub v M (digestView (digS v s.2.2.1 M)) q
    · rcases hp with hp | hp | ⟨sl, hsl, hp⟩
      · exact Or.inr ⟨M, hmM, 0, hp⟩
      · exact Or.inr ⟨M, hmM, 1, hp⟩
      · refine Or.inl ⟨sl, public_mono (fun p hp' ↦ ?_) (forsSlots_public hsl), hp⟩
        refine Or.inr ⟨M, hmM, ?_⟩
        rw [hdM]
        exact Or.inl hp'
    · rcases hF.cells q (inHw_of_hwOff hH.moves.hw hp hq) with ⟨sl, hsl, hp'⟩ | ⟨M', hM', i, hp'⟩
      · exact Or.inl ⟨sl, public_mono (selDisclosures_mono (fun l idx sel h ↦ by
          rw [hH.mem]; exact h)
          (fun M' hM' ↦ (hdold M' hM').symm) (List.subset_append_left _ _)) hsl, hp'⟩
      · exact Or.inr ⟨M', List.mem_append_left _ hM', i, hp'⟩
  · have hnew : ∀ i, HHeldV pub v s'.2.1 M i (digS v s'.2.2.1 M i) := fun i ↦ by
      rcases hH.hmsg with h'' | h''
      · rw [hdM]
        exact h'' i
      · exact absurd h'' hconf
    rcases List.mem_append.1 hM' with h | h
    · rcases hH.old M' i _ (hF.held M' h i) with h' | rfl | h'
      · rw [hdold M' h]
        exact h'
      · exact hnew i
      · exact absurd h' hconf
    · rw [List.mem_singleton.1 h]
      exact hnew i

/-- **The facts after a layer signature** by `K_l(idx)`, `idx` the index of a message under way,
off the trial-hit event: kept, the key recording its search, the other keys kept, the view's
searches and the digests unchanged. -/
theorem core_layer (hsep : HmsgHSep pub v) {rs : SignLog Message (Option Signature)}
    {msgs : List Message} (hrs : ∀ r ∈ rs, r.1 ∈ msgs) {n : ℕ} {l : Layer} {idx : Index}
    {s s' : SReg} {o : Option (LayerSignature (keyOf l idx).1)} (hb : SBase pub n s)
    (hF : CoreFacts pub v rs msgs s) (hL : LayerRelS pub v (keyOf l idx) s o s')
    (hhit : s ∉ TrialHit pub v) (hidx : ∃ M ∈ msgs, (digestView (digS v s.2.2.1 M)).1 = idx) :
    CoreFacts pub v rs msgs s' ∧ s'.2.2.2 (keyOf l idx) = kRec pub v (regFns s) (keyOf l idx) ∧
      (∀ K, K ≠ keyOf l idx → s'.2.2.2 K = s.2.2.2 K) ∧
      (∀ l' idx', kSel pub v (regFns s') (keyOf l' idx') = kSel pub v (regFns s) (keyOf l' idx')) ∧
      (∀ l' idx', kRec pub v (regFns s') (keyOf l' idx') = kRec pub v (regFns s) (keyOf l' idx')) ∧
      (∀ M ∈ msgs, digS v s'.2.2.1 M = digS v s.2.2.1 M) := by
  obtain ⟨U, hU, hlab⟩ := hL.lab
  have hT' : MarksOK s'.2.2.1 := by
    rw [hlab]
    exact marksOK_union hb.marks hU
  have hsub : s.2.2.1 ⊆ s'.2.2.1 := by
    rw [hlab]
    exact Finset.subset_union_left
  have hview : OffAgree (ProgCell pub v) (regFns s) (regFns s') :=
    hL.moves.view.mono fun _ ↦ layerPt_progCell
  have hsel := fun l' idx' ↦ kSel_congr hhit hview l' idx'
  have hrec := fun l' idx' ↦ kRec_congr hhit hview l' idx'
  have hd : ∀ M ∈ msgs, digS v s'.2.2.1 M = digS v s.2.2.1 M := fun M hM ↦ by
    obtain ⟨j, hj⟩ := hF.marked M hM
    exact digS_stable hb.marks hT' hsub hj
  have hmK : s'.2.2.2 (keyOf l idx) = kRec pub v (regFns s) (keyOf l idx) := by
    rw [hL.mem]
    rcases hm : s.2.2.2 (keyOf l idx) with _ | b
    · exact kMem_self_of_none hm
    · rw [kMem_of_some hm]
      exact hF.keys _ (by rw [hm]; exact Option.some_ne_none b)
  have hoff : ∀ K, K ≠ keyOf l idx → s'.2.2.2 K = s.2.2.2 K := fun K hK ↦ by
    rw [hL.mem, kMem_apply_of_ne _ _ _ hK]
  have hpres : ∀ K, s.2.2.2 K = kRec pub v (regFns s) K →
      s'.2.2.2 K = kRec pub v (regFns s) K := fun K h ↦ by
    rw [hL.mem]
    exact kMem_preserve (hF.keys _) h
  refine ⟨⟨fun M hM ↦ ?_, fun K hK ↦ ?_, fun r hr ↦ ?_, fun r hr ↦ ?_, fun q hq ↦ ?_,
    fun M hM i ↦ ?_⟩, hmK, hoff, hsel, hrec, hd⟩
  · obtain ⟨j, hj⟩ := hF.marked M hM
    exact ⟨j, hsub hj⟩
  · by_cases e : K = keyOf l idx
    · subst e
      rw [hmK, hrec]
    · rw [hoff K e] at hK ⊢
      obtain ⟨l', idx', rfl⟩ := hb.ground K hK
      rw [hF.keys _ hK, hrec]
  · rw [hd r.1 (hrs r hr)]
    obtain ⟨h0, h1⟩ := hF.done r hr
    refine ⟨by rw [hrec]; exact hpres _ h0, fun hne ↦ ?_⟩
    rw [hsel] at hne
    obtain ⟨h1a, h1b⟩ := h1 hne
    refine ⟨by rw [hrec]; exact hpres _ h1a, fun hne' ↦ ?_⟩
    rw [hsel] at hne'
    rw [hrec]
    exact hpres _ (h1b hne')
  · rw [hF.sigs r hr, hd r.1 (hrs r hr)]
    exact selSig_congr_all _ _ _ fun l' ↦ (hsel l' _).symm
  · by_cases hp : layerPt pub v (regFns s) (keyOf l idx) q
    · obtain ⟨sel, hs, sl, hsl, hq'⟩ := hp
      obtain ⟨M, hM, hMidx⟩ := hidx
      refine Or.inl ⟨sl, public_mono (fun p hp' ↦ ?_) (layerSlots_public l idx sel.2 hsl), hq'⟩
      refine Or.inr ⟨M, hM, Or.inr ⟨l, sel, ?_, ?_⟩⟩
      · rw [hd M hM, hMidx]
        exact (selOfM_of_kRec hmK).trans hs
      · rw [hd M hM, hMidx]
        exact hp'
    · rcases hF.cells q (inHw_of_hwOff hL.moves.hw hp hq) with ⟨sl, hsl, h⟩ | h
      · exact Or.inl ⟨sl, public_mono (selDisclosures_mono (fun l' idx' sel h ↦
          selOfM_mono (fun b hb ↦ by rw [hL.mem]; exact kMem_mono hb) h)
          (fun M hM ↦ (hd M hM).symm) (List.Subset.refl _)) hsl, h⟩
      · exact Or.inr h
  · rw [hd M hM]
    exact (hF.held M hM i).of_moves hL.moves fun ⟨sel, _, sl, hsl, h⟩ ↦
      not_slotPt_hZ hsep (layerSlots_inTable l idx sel.2 hsl) M i h

variable (pub v) in
/-- **The layers' moves** of a signature on index `idx` from `s` (after the head) to `s'` with the
layer signatures `out`: the bottom layer, the middle one if the bottom found a selection, the top
one if both did. -/
def LayersRel (idx : Index) (s : SReg)
    (out : Option (LayerSignature 0 × LayerSignature 1 × LayerSignature 2)) (s' : SReg) : Prop :=
  ∃ s₅ o₀, LayerRelS pub v (keyOf 0 idx) s o₀ s₅ ∧ ((o₀ = none ∧ out = none ∧ s' = s₅) ∨
    ∃ b, o₀ = some b ∧ ∃ s₆ o₁, LayerRelS pub v (keyOf 1 idx) s₅ o₁ s₆ ∧
      ((o₁ = none ∧ out = none ∧ s' = s₆) ∨ ∃ m, o₁ = some m ∧ ∃ o₂,
        LayerRelS pub v (keyOf 2 idx) s₆ o₂ s' ∧ out = o₂.map fun t ↦ (b, m, t)))

/-- A signature by a selection, layer by layer. -/
theorem selSig_of_outs (S : SelFn) (R : Randomizer) (w : View) :
    (evData pub v).selSig S R w = ((S (keyOf 0 w.1)).map (kSig v (keyOf 0 w.1))).bind fun b ↦
      ((S (keyOf 1 w.1)).map (kSig v (keyOf 1 w.1))).bind fun m ↦
        ((S (keyOf 2 w.1)).map (kSig v (keyOf 2 w.1))).map fun t ↦
          (⟨R, (evData pub v).forsOpen w, KeyGenerationAndSigning.layerSignatures b m t⟩ :
            Signature) := by
  unfold EvData.selSig
  rw [selLayerSig_evData, selLayerSig_evData, selLayerSig_evData]
  rcases S (keyOf 0 w.1) with _ | a <;> rcases S (keyOf 1 w.1) with _ | b <;>
    rcases S (keyOf 2 w.1) with _ | c <;> rfl

theorem not_trialHit_of_moves {P : SpongeQuery X Z → Prop} {s s' : SReg} (hm : Moves pub P s s')
    (hP : ∀ q, P q → ProgCell pub v q) (h : s' ∉ TrialHit pub v) : s ∉ TrialHit pub v :=
  fun hs ↦ h ((trialHit_iff_of_offAgree (hm.view.mono hP)).1 hs)

theorem not_conflict_of_moves {P : SpongeQuery X Z → Prop} {s s' : SReg} (hm : Moves pub P s s')
    (h : s' ∉ HConflict pub v) : s ∉ HConflict pub v :=
  fun hs ↦ h (HConflict.mono hm.grow hs)

theorem kSel_of_out {K : Key} {t : SpongeKeys X Z} {b : LayerSignature K.1}
    (h : some b = (kSel pub v t K).map (kSig v K)) :
    ∃ sel, kSel pub v t K = some sel ∧ b = kSig v K sel := by
  rcases hk : kSel pub v t K with _ | sel
  · rw [hk] at h
    cases h
  · rw [hk, Option.map_some] at h
    exact ⟨sel, rfl, Option.some.inj h⟩

theorem kSel_of_out_none {K : Key} {t : SpongeKeys X Z}
    (h : none = (kSel pub v t K).map (kSig v K)) : kSel pub v t K = none := by
  rcases hk : kSel pub v t K with _ | sel
  · rfl
  · rw [hk, Option.map_some] at h
    cases h

/-- **A signature keeps the prefix invariant**: the head and the layers, with the signature
assembled from the layers' outputs. -/
theorem inv_step (hsep : HmsgHSep pub v) {log : SignLog Message (Option Signature)}
    {M : Message} {s sH s' : SReg} {fo : ForsTreeIndex → ForsTreeOpening}
    {out : Option (LayerSignature 0 × LayerSignature 1 × LayerSignature 2)}
    {sig : Option Signature} (hs : s ∈ InvS pub v log) (hH : HeadRel pub v M s fo sH)
    (hL : LayersRel pub v (digestView (digS v s.2.2.1 M)).1 sH out s')
    (hsig : sig = out.map fun x ↦
      ⟨rndOf v M, fo, KeyGenerationAndSigning.layerSignatures x.1 x.2.1 x.2.2⟩) :
    s' ∈ InvS pub v (log ++ [⟨M, sig⟩]) := by
  obtain ⟨hb, hfacts⟩ := hs
  have hbH := base_head hb hH
  obtain ⟨idx, hidx⟩ : ∃ idx, (digestView (digS v s.2.2.1 M)).1 = idx := ⟨_, rfl⟩
  rw [hidx] at hL
  have hlen : (log ++ [⟨M, sig⟩] : SignLog Message (Option Signature)).length =
      log.length + 1 := by simp
  have hmsgs : (log ++ [⟨M, sig⟩] : SignLog Message (Option Signature)).map Sigma.fst =
      log.map Sigma.fst ++ [M] := by simp
  have hrs : ∀ r ∈ log, r.1 ∈ log.map Sigma.fst ++ [M] := fun r hr ↦
    List.mem_append_left _ (List.mem_map.2 ⟨r, hr, rfl⟩)
  have hmM : M ∈ log.map Sigma.fst ++ [M] := List.mem_append_right _ (List.mem_singleton_self M)
  rw [hH.fo] at hsig
  have atH : sH ∉ TrialHit pub v → sH ∉ HConflict pub v → log.length < signatureLimit →
      CoreFacts pub v log (log.map Sigma.fst ++ [M]) sH ∧
        digS v sH.2.2.1 M = digS v s.2.2.1 M := fun h1 h2 h3 ↦
    core_head hb (hfacts (not_trialHit_of_moves hH.moves (fun _ ↦ headPt_progCell) h1)
      (not_conflict_of_moves hH.moves h2) h3.le) hH
      (not_trialHit_of_moves hH.moves (fun _ ↦ headPt_progCell) h1) h2 h3
  have finish : ∀ {s₉ : SReg}, SBase pub (log.length + 1) s₉ →
      (s₉ ∉ TrialHit pub v → s₉ ∉ HConflict pub v → log.length < signatureLimit →
        CoreFacts pub v log (log.map Sigma.fst ++ [M]) s₉ ∧
          Done pub v (regFns s₉) s₉.2.2.2 (digestView (digS v s₉.2.2.1 M)).1 ∧
          sig = (evData pub v).selSig (kSel pub v (regFns s₉)) (rndOf v M)
            (digestView (digS v s₉.2.2.1 M))) →
      s₉ ∈ InvS pub v (log ++ [⟨M, sig⟩]) := by
    intro s₉ hb9 h9
    refine ⟨by rw [hlen]; exact hb9, fun hhit hconf hlim ↦ ?_⟩
    rw [hlen] at hlim
    obtain ⟨F, hd, hsg⟩ := h9 hhit hconf (by omega)
    rw [hmsgs]
    refine ⟨F.marked, F.keys, fun r hr ↦ ?_, fun r hr ↦ ?_, F.cells, F.held⟩
    · rcases List.mem_append.1 hr with hr | hr
      · exact F.done r hr
      · rw [List.mem_singleton.1 hr]
        exact hd
    · rcases List.mem_append.1 hr with hr | hr
      · exact F.sigs r hr
      · rw [List.mem_singleton.1 hr]
        exact hsg
  have hne01 : keyOf 0 idx ≠ keyOf 1 idx := keyOf_ne _ _ (by decide)
  have hne02 : keyOf 0 idx ≠ keyOf 2 idx := keyOf_ne _ _ (by decide)
  have hne12 : keyOf 1 idx ≠ keyOf 2 idx := keyOf_ne _ _ (by decide)
  obtain ⟨s₅, o₀, h0, hrest⟩ := hL
  have hb5 := base_layer hbH h0
  rcases hrest with ⟨rfl, rfl, rfl⟩ | ⟨b, rfl, s₆, o₁, h1, hrest⟩
  · refine finish hb5 fun hhit hconf hlim ↦ ?_
    have hHhit := not_trialHit_of_moves h0.moves (fun _ ↦ layerPt_progCell) hhit
    have hHconf := not_conflict_of_moves h0.moves hconf
    obtain ⟨FH, hdH⟩ := atH hHhit hHconf hlim
    obtain ⟨F5, hK0, -, hsel5, hrec5, hd5⟩ :=
      core_layer hsep hrs hbH FH h0 hHhit ⟨M, hmM, by rw [hdH, hidx]⟩
    have hdM : digS v s'.2.2.1 M = digS v s.2.2.1 M := (hd5 M hmM).trans hdH
    have h0none := kSel_of_out_none h0.out
    refine ⟨F5, ?_, ?_⟩
    · rw [hdM, hidx]
      exact ⟨by rw [hK0, hrec5], fun hne ↦ absurd ((hsel5 0 idx).trans h0none) hne⟩
    · rw [hsig, hdM, selSig_of_outs, hidx, (hsel5 0 idx).trans h0none]
      rfl
  · have hb6 := base_layer hb5 h1
    rcases hrest with ⟨rfl, rfl, rfl⟩ | ⟨m, rfl, o₂, h2, rfl⟩
    · refine finish hb6 fun hhit hconf hlim ↦ ?_
      have h5hit := not_trialHit_of_moves h1.moves (fun _ ↦ layerPt_progCell) hhit
      have h5conf := not_conflict_of_moves h1.moves hconf
      have hHhit := not_trialHit_of_moves h0.moves (fun _ ↦ layerPt_progCell) h5hit
      have hHconf := not_conflict_of_moves h0.moves h5conf
      obtain ⟨FH, hdH⟩ := atH hHhit hHconf hlim
      obtain ⟨F5, hK0, -, hsel5, hrec5, hd5⟩ :=
        core_layer hsep hrs hbH FH h0 hHhit ⟨M, hmM, by rw [hdH, hidx]⟩
      obtain ⟨F6, hK1, hoff6, hsel6, hrec6, hd6⟩ :=
        core_layer hsep hrs hb5 F5 h1 h5hit ⟨M, hmM, by rw [hd5 M hmM, hdH, hidx]⟩
      have hdM : digS v s'.2.2.1 M = digS v s.2.2.1 M :=
        (hd6 M hmM).trans ((hd5 M hmM).trans hdH)
      obtain ⟨sel0, hsel0, rfl⟩ := kSel_of_out h0.out
      have h1none := kSel_of_out_none h1.out
      refine ⟨F6, ?_, ?_⟩
      · rw [hdM, hidx]
        refine ⟨by rw [hoff6 _ hne01, hK0, hrec6, hrec5], fun _ ↦
          ⟨by rw [hK1, hrec6], fun hne ↦ absurd ((hsel6 1 idx).trans h1none) hne⟩⟩
      · rw [hsig, hdM, selSig_of_outs, hidx, (hsel6 0 idx).trans ((hsel5 0 idx).trans hsel0),
          (hsel6 1 idx).trans h1none]
        rfl
    · refine finish (base_layer hb6 h2) fun hhit hconf hlim ↦ ?_
      have h6hit := not_trialHit_of_moves h2.moves (fun _ ↦ layerPt_progCell) hhit
      have h6conf := not_conflict_of_moves h2.moves hconf
      have h5hit := not_trialHit_of_moves h1.moves (fun _ ↦ layerPt_progCell) h6hit
      have h5conf := not_conflict_of_moves h1.moves h6conf
      have hHhit := not_trialHit_of_moves h0.moves (fun _ ↦ layerPt_progCell) h5hit
      have hHconf := not_conflict_of_moves h0.moves h5conf
      obtain ⟨FH, hdH⟩ := atH hHhit hHconf hlim
      obtain ⟨F5, hK0, -, hsel5, hrec5, hd5⟩ :=
        core_layer hsep hrs hbH FH h0 hHhit ⟨M, hmM, by rw [hdH, hidx]⟩
      obtain ⟨F6, hK1, hoff6, hsel6, hrec6, hd6⟩ :=
        core_layer hsep hrs hb5 F5 h1 h5hit ⟨M, hmM, by rw [hd5 M hmM, hdH, hidx]⟩
      obtain ⟨F7, hK2, hoff7, hsel7, hrec7, hd7⟩ :=
        core_layer hsep hrs hb6 F6 h2 h6hit ⟨M, hmM, by rw [hd6 M hmM, hd5 M hmM, hdH, hidx]⟩
      have hdM : digS v s'.2.2.1 M = digS v s.2.2.1 M :=
        (hd7 M hmM).trans ((hd6 M hmM).trans ((hd5 M hmM).trans hdH))
      obtain ⟨sel0, hsel0, rfl⟩ := kSel_of_out h0.out
      obtain ⟨sel1, hsel1, rfl⟩ := kSel_of_out h1.out
      refine ⟨F7, ?_, ?_⟩
      · rw [hdM, hidx]
        refine ⟨by rw [hoff7 _ hne02, hoff6 _ hne01, hK0, hrec7, hrec6, hrec5], fun _ ↦
          ⟨by rw [hoff7 _ hne12, hK1, hrec7, hrec6], fun _ ↦ by rw [hK2, hrec7]⟩⟩
      · rw [hsig, hdM, selSig_of_outs, hidx,
          (hsel7 0 idx).trans ((hsel6 0 idx).trans ((hsel5 0 idx).trans hsel0)),
          (hsel7 1 idx).trans ((hsel6 1 idx).trans hsel1), hsel7 2 idx, h2.out]
        rcases kSel pub v (regFns s₆) (keyOf 2 idx) with _ | sel2 <;> rfl

end inv

/-! ## The realized signer and the challenge prefix -/

section final

variable {pub : Pub} {v : (s : HPos) → XD s} {m₀ : Finset HPos × Selections}

/-- **A realized signature under `strPol` keeps the prefix invariant**, on good data. -/
theorem ht₂_signT (hsep : HmsgHSep pub v) (B : QReg) (M : Message)
    (log : SignLog Message (Option Signature)) :
    HT₂ m₀ (realizeT v (signT Selections cwUpd strPol pub B M)) (InvS pub v log)
      (fun sig ↦ InvS pub v (log ++ [⟨M, sig⟩])) := by
  unfold signT
  refine ht₂_revealThen m₀ v _ _ _ _ fun mem ↦ ?_
  refine ht₂_revealThen m₀ v _ _ _ _ fun mem₂ ↦ ?_
  rw [realizeT_bind₂]
  refine HT₂.bind (ht₂_progPorts m₀ v B _ _) fun _ ↦ ?_
  rw [realizeT_bind₂]
  refine HT₂.bind (ht₂_forsOpenT B _ _ _ ?_) fun fo ↦ ?_
  · rintro s ⟨s₂, ⟨s₁, ⟨s₀, hs₀, -, rfl⟩, -, rfl⟩, hpr⟩
    refine (ProgsRel.moves (pub := pub) (P := fun _ ↦ True) hpr (fun c hc ↦ ⟨trivial, ?_⟩)
      hs₀.1.noBot).1.noBot
    obtain ⟨i, -, hkv⟩ := digestPorts_pt v hc
    exact hkv
  rw [realizeT_bind₂]
  refine HT₂.mono (P := {sH | ∃ s ∈ InvS pub v log, s.2.2.1 = mem.1 ∧ HeadRel pub v M s fo sH})
    ?_ ?_ fun _ ↦ subset_rfl
  rotate_left
  · rintro s₄ ⟨s₃, ⟨s₂, ⟨s₁, ⟨s₀, hs₀, hm0, rfl⟩, -, rfl⟩, hpr⟩, hfo, h42, hmv⟩
    subst hm0
    rw [digestOf_need] at hfo h42 hmv
    exact ⟨s₀, hs₀, rfl, headRel_of hsep hs₀.1.noBot rfl hpr hfo h42 hmv⟩
  have e : ∀ s : SReg, s.2.2.1 = mem.1 → (digestView (digS v s.2.2.1 M)).1 =
      digestIndex (digestOf strPol mem.1 M (restrictTo (strPol.need mem.1 M) v)) :=
    fun s hT ↦ by rw [hT, digestOf_need]; rfl
  refine HT₂.bind (ht₂_signLayerT B 0 _ _ fun s hs ↦ by obtain ⟨_, _, _, hH⟩ := hs; exact
    hH.moves.noBot) fun o₀ ↦ ?_
  rcases o₀ with _ | bottom
  · refine ht₂_pure none ?_
    rintro s' ⟨sH, ⟨s, hs, hT, hH⟩, h0⟩
    refine inv_step hsep hs hH (out := none) ?_ rfl
    rw [e s hT]
    exact ⟨s', none, h0, Or.inl ⟨rfl, rfl, rfl⟩⟩
  rw [realizeT_bind₂]
  refine HT₂.bind (ht₂_signLayerT B 1 _ _ fun s hs ↦ by obtain ⟨_, _, h⟩ := hs; exact
    h.moves.noBot) fun o₁ ↦ ?_
  rcases o₁ with _ | middle
  · refine ht₂_pure none ?_
    rintro s' ⟨s₅, ⟨sH, ⟨s, hs, hT, hH⟩, h0⟩, h1⟩
    refine inv_step hsep hs hH (out := none) ?_ rfl
    rw [e s hT]
    exact ⟨s₅, some bottom, h0, Or.inr ⟨bottom, rfl, s', none, h1, Or.inl ⟨rfl, rfl, rfl⟩⟩⟩
  rw [realizeT_bind₂]
  refine HT₂.bind (ht₂_signLayerT B 2 _ _ fun s hs ↦ by obtain ⟨_, _, h⟩ := hs; exact
    h.moves.noBot) fun o₂ ↦ ?_
  rcases o₂ with _ | top
  · refine ht₂_pure none ?_
    rintro s' ⟨s₆, ⟨s₅, ⟨sH, ⟨s, hs, hT, hH⟩, h0⟩, h1⟩, h2⟩
    refine inv_step hsep hs hH (out := none) ?_ rfl
    rw [e s hT]
    exact ⟨s₅, some bottom, h0, Or.inr ⟨bottom, rfl, s₆, some middle, h1,
      Or.inr ⟨middle, rfl, none, h2, rfl⟩⟩⟩
  · refine ht₂_pure _ ?_
    rintro s' ⟨s₆, ⟨s₅, ⟨sH, ⟨s, hs, hT, hH⟩, h0⟩, h1⟩, h2⟩
    refine inv_step hsep hs hH (out := some (bottom, middle, top)) ?_ ?_
    · rw [e s hT]
      exact ⟨s₅, some bottom, h0, Or.inr ⟨bottom, rfl, s₆, some middle, h1,
        Or.inr ⟨middle, rfl, some top, h2, rfl⟩⟩⟩
    · rw [extendRnd_restrictTo (by simp) v]
      rfl

/-- The invariant at the start, after the root's reveal. -/
theorem inv_nil (hm₀l : AsgFree m₀.1) (hm₀ : m₀.2 = fun _ ↦ none) {s : SReg}
    (hs : NoBot s ∧ s.2 = (hwEmpty X Z, m₀)) :
    ((s.1, s.2.1, (s.2.2.1 ∪ {.val rootPos}, s.2.2.2)) : SReg) ∈ InvS pub v [] := by
  obtain ⟨hnb, h2⟩ := hs
  have hm : s.2.2.2 = fun _ ↦ none := by rw [h2]; exact hm₀
  have hW : s.2.1 = hwEmpty X Z := congrArg Prod.fst h2
  have hT : s.2.2.1 = m₀.1 := by rw [h2]
  have hroot : AsgFree {HPos.val rootPos} := fun M j h ↦ by
    rw [Finset.mem_singleton] at h
    cases h
  have hfree : AsgFree (s.2.2.1 ∪ {HPos.val rootPos}) := by
    rw [hT]
    exact asgFree_union hm₀l hroot
  refine ⟨⟨hnb, fun M j _ h ↦ absurd h (hfree M j), ?_, ?_, ?_⟩,
    fun _ _ _ ↦ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show asgCount (s.2.2.1 ∪ {HPos.val rootPos}) ≤ 0
    unfold asgCount
    rw [filter_isAsg_eq_empty hfree]
    rfl
  · show KeyVals pub s.2.1
    rw [hW]
    exact ⟨fun _ _ h ↦ absurd h (by simp [hwEmpty]), fun _ _ h ↦ absurd h (by simp [hwEmpty])⟩
  · show ∀ K, s.2.2.2 K ≠ none → _
    rw [hm]
    exact fun K h ↦ absurd rfl h
  · intro M hM
    cases hM
  · show ∀ K, s.2.2.2 K ≠ none → _
    rw [hm]
    exact fun K h ↦ absurd rfl h
  · intro r hr
    cases hr
  · intro r hr
    cases hr
  · intro q hq
    exfalso
    change InHw s.2.1 q at hq
    rw [hW] at hq
    cases q <;> exact hq rfl
  · intro M hM
    cases hM

theorem rnK_zero (π : Equiv.Perm (X × Z)) (h : Z → X) (k k' : X → Z) (b : ℕ → X) :
    rnK π h k k' b 0 = b 0 :=
  zero_add (b 0)

/-- **The honest tail of an `H_msg` call** is its one block, as a `k`-cell. -/
theorem honTail_hmsg (R : Randomizer) (M : Message) (c : DigestCall) :
    (evData pub v).honTail (.hmsg R M c) =
      [rnK pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2
        (slotBlk pub.seed (.hmsg R M c) (valsOf v)) 0] := by
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 (length_blocks_hmsg pub.seed R M c (valsOf v))
  have hs0 : slotBlk pub.seed (.hmsg R M c) (valsOf v) 0 = b := by
    unfold slotBlk
    rw [hb]
    rfl
  show absorbTail _ (blocks (slotInput pub.seed (.hmsg R M c) (valsOf v))) =
    [((0, 0) : X × Z).1 + slotBlk pub.seed (.hmsg R M c) (valsOf v) 0]
  rw [hb, hs0]
  rfl

/-- An exempted slot's first `k`-cell is hardwired. -/
theorem inHw_k0_of_heldIn {W : Hw X Z} {s : Slot} (h : (evData pub v).HeldIn W.toDbs s) :
    InHw W (.k (rnK pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2
      (slotBlk pub.seed s (valsOf v)) 0)) := by
  obtain ⟨h', hr, -, -⟩ := h
  have hl : (blocks (slotInput pub.seed s (valsOf v))).length = nBlk pub.seed s :=
    length_blocks_slotInput pub.seed s (valsOf v)
  have hne : blocks (slotInput pub.seed s (valsOf v)) ≠ [] := by
    intro h0
    have := nBlk_pos pub.seed s
    rw [← hl, h0] at this
    exact absurd this (by simp)
  obtain ⟨b, rest, hmsg⟩ := List.exists_cons_of_ne_nil hne
  have hs0 : slotBlk pub.seed s (valsOf v) 0 = b := by
    unfold slotBlk
    rw [hmsg]
    rfl
  have key : ∀ (l : List X) (st : X × Z) (L : List (SpongeRead X Z)), ∀ e ∈ L,
      e ∈ (l.foldl (logStep pub.perm h' pub.keys.2.1 pub.keys.2.2) (st, L)).2 := by
    intro l
    induction l with
    | nil => exact fun _ _ _ he ↦ he
    | cons b' l ih => exact fun st L e he ↦ ih _ _ e (List.mem_append_left _ he)
  have hmem : SpongeRead.k (((0, 0) : X × Z).1 + b) (pub.keys.2.1 (((0, 0) : X × Z).1 + b)) ∈
      spongeReads pub.perm h' pub.keys.2.1 pub.keys.2.2
        (blocks (slotInput pub.seed s (valsOf v))) := by
    rw [hmsg]
    exact key rest _ _ _ (List.mem_append_right _ List.mem_cons_self)
  have hk := hr _ hmem
  show W.2.1 (((0, 0) : X × Z).1 + slotBlk pub.seed s (valsOf v) 0) ≠ none
  rw [hs0]
  intro h0
  change W.2.1 _ = some _ at hk
  rw [hk] at h0
  cases h0

variable (pub v) in
/-- **The prefix facts** of a prefix outcome `pre` at the hardwired cells and memory `b`: the public
key, and a selection function and digests with Classify's `WinFacts` fields but the grade (the
transcript's signatures, the memory's records, the exempted slots public, the signed digests
covered by the stream, the coverage-exempted pairs signed, both `H_msg` calls of every signed pair
held with its digests, the forgery fresh). -/
def PreFactsS (pre : PublicKey × (Forgery × SignLog Message (Option Signature)))
    (b : Hw X Z × (Finset HPos × Selections)) : Prop :=
  pre.1 = (evData pub v).pk ∧ ∃ (S : SelFn) (dig : Message → DigestCall → HashOutput),
    (∀ r ∈ pre.2.2, r.2 = (evData pub v).selSig S (rndOf v r.1) (digestView (dig r.1))) ∧
    (evData pub v).RecordsSel S b.2.2 ∧
    (evData pub v).exS b.1 ⊆ Public (selDisclosures S dig (pre.2.2.map Sigma.fst)) ∧
    (∀ r ∈ pre.2.2, Covered (evData pub v).cover (digestView (dig r.1))) ∧
    (∀ p ∈ (evData pub v).covEx b.1, ∃ r ∈ pre.2.2, r.1 = p.2 ∧ p.1 = rndOf v r.1) ∧
    (∀ r ∈ pre.2.2, ∀ c, (evData pub v).HashHeld b.1.toDbs
      ((evData pub v).hmsgInput (rndOf v r.1) r.1 c) (dig r.1 c)) ∧
    ¬Common.SufCma.SignerReturnedForgery id pre.2.2 pre.2.1.message pre.2.1.signature

/-- **Classify's `WinFacts` from the prefix facts** and the grade. -/
theorem winFacts_of_preFacts {pre : PublicKey × (Forgery × SignLog Message (Option Signature))}
    {W : Hw X Z} {m : Finset HPos × Selections} {N : ℕ} (h : PreFactsS pub v pre (W, m))
    (hN : dbGrade W ≤ N) :
    ∃ S dig, WinFacts (evData pub v) N S (rndOf v) dig pre.2.2 pre.2.1 W m := by
  obtain ⟨-, S, dig, hsig, hrec, hex, hcov, hcex, hdig, hfr⟩ := h
  exact ⟨S, dig, hN, hsig, hrec, hex, hcov, hcex, hdig, hfr⟩

/-- **The prefix facts from the invariant's facts**, on good data. -/
theorem preFacts_of (hpd : PathsDisjoint pub.xw pub.keys.1 (valsOf v)) (hsepK : HmsgSep pub v)
    {pre : PublicKey × (Forgery × SignLog Message (Option Signature))} {s : SReg}
    (hb : SBase pub pre.2.2.length s) (hF : CoreFacts pub v pre.2.2 (pre.2.2.map Sigma.fst) s)
    (hpk : pre.1 = pkOf pub (restrictTo {.val rootPos} v))
    (hfr : ¬Common.SufCma.SignerReturnedForgery id pre.2.2 pre.2.1.message pre.2.1.signature) :
    PreFactsS pub v pre s.2 := by
  have hmem : ∀ r ∈ pre.2.2, r.1 ∈ pre.2.2.map Sigma.fst := fun r hr ↦ List.mem_map.2 ⟨r, hr, rfl⟩
  refine ⟨?_, selOfM pub v s.2.2.2, digS v s.2.2.1, fun r hr ↦ ?_, recordsSel_selOfM _, ?_,
    fun r hr ↦ ?_, ?_, fun r hr c ↦ hashHeld_of_hHeldV hb.keyVals (hF.held r.1 (hmem r hr) c), hfr⟩
  · rw [hpk]
    unfold pkOf EvData.pk
    rw [extendVals_restrictTo (Finset.mem_singleton_self _)]
    rfl
  · rw [hF.sigs r hr]
    obtain ⟨h0, h1⟩ := hF.done r hr
    refine (selSig_congr _ _ _ (selOfM_of_kRec h0) (fun hne ↦ selOfM_of_kRec (h1 hne).1)
      (fun hne hne' ↦ selOfM_of_kRec ((h1 hne).2 hne'))).symm
  · rintro s' ⟨hin, hheld⟩
    rcases hF.cells _ (inHw_k0_of_heldIn hheld) with ⟨sl, hsl, j, hj, hq⟩ | ⟨M', -, i, j, hj, hq⟩
    · by_cases e : s' = sl
      · rw [e]
        exact hsl
      · exfalso
        rcases hq with hq | hq | hq
        · exact hpd ⟨s', sl, hin, hsl.1, e, 0, nBlk_pos _ _, j, hj,
            Or.inl (SpongeQuery.k.inj hq)⟩
        · cases hq
        · cases hq
    · exfalso
      obtain rfl : j = 0 := by omega
      rcases hq with hq | hq | hq
      · refine hsepK (v (.rnd M')) M' i s' hin 0 (nBlk_pos _ _) ?_
        have hq' := SpongeQuery.k.inj hq
        show rnK pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2
          (slotBlk pub.seed s' (valsOf v)) 0 = _
        rw [hq']
        exact rnK_zero _ _ _ _ _
      · cases hq
      · cases hq
  · obtain ⟨j, hj⟩ := hF.marked r.1 (hmem r hr)
    rw [digS_of_idx v (streamIdx_of_mem hb.marks hj)]
    exact (covered_revealed_iff _ _ _).2 fun κ ↦ ⟨j, rfl, rfl⟩
  · rintro ⟨R, M⟩ ⟨z, xi, w, ⟨t0, zp, xp, a, zi, b, ht, -, hk, -⟩, -⟩
    rw [honTail_hmsg] at ht
    have hx : xp = rnK pub.perm pub.keys.1 pub.keys.2.1 pub.keys.2.2
        (slotBlk pub.seed (.hmsg R M 0) (valsOf v)) 0 := by
      have := congrArg List.getLast? ht
      simp only [List.getLast?_singleton, List.getLast?_append, Option.some_or] at this
      exact (Option.some.inj this).symm
    have hin : InHw s.2.1 (.k xp) := fun h0 ↦ by
      change s.2.1.2.1 xp = some a at hk
      rw [hk] at h0
      cases h0
    rcases hF.cells _ hin with ⟨sl, hsl, j, hj, hq⟩ | ⟨M', hM', i, j, hj, hq⟩
    · exfalso
      rcases hq with hq | hq | hq
      · refine hsepK R M 0 sl hsl.1 j hj ?_
        have hq' := SpongeQuery.k.inj hq
        rw [hx, rnK_zero] at hq'
        exact hq'.symm
      · cases hq
      · cases hq
    · obtain rfl : j = 0 := by omega
      rcases hq with hq | hq | hq
      · have hq' := SpongeQuery.k.inj hq
        rw [hx] at hq'
        have ht' : (evData pub v).honTail (.hmsg R M 0) =
            (evData pub v).honTail (.hmsg (rndOf v M') M' i) := by
          rw [honTail_hmsg, honTail_hmsg, hq']
          rfl
        obtain ⟨hR, -, -, hM, -⟩ := absorbTail_blocks_messageDigestInput_injective _ ht'
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM'
        exact ⟨r, hr, hM.symm, hR⟩
      · cases hq
      · cases hq

/-- The winning condition of the game on a prefix outcome. -/
noncomputable def winCondS (pre : PublicKey × (Forgery × SignLog Message (Option Signature))) :
    Bool :=
  RandomPermutationModel.sufCmaScheme.winningCondition pre.2.2 pre.2.1

/-- **The prefix facts off the trial-hit and conflict events** (leanSPHINCS's `PrefixWinFactsOff`,
event side, `strPol`): on good data (disjoint honest paths of in-table slots, no in-table `k`-cell
an `H_msg` block, no in-table `h`-cell an `H_msg` `h`-cell), from a memory with no mark and no
selection, every winning branch of the realized challenge prefix is, in the decompressed basis,
supported where the register hits a trial, has a conflict, or has the prefix facts. The two events
are separate exceptions: `TrialHit pub v` (mass from a decompressed trial-read argument) and
`HConflict pub v` (mass from the compressed hidden-randomizer argument, see `HConflict`). -/
theorem prefixWinFactsOff (hpd : PathsDisjoint pub.xw pub.keys.1 (valsOf v))
    (hsepK : HmsgSep pub v) (hsepH : HmsgHSep pub v) (hm₀l : AsgFree m₀.1)
    (hm₀ : m₀.2 = fun _ ↦ none) (A : SAdversary)
    (pre : PublicKey × (Forgery × SignLog Message (Option Signature))) (hw : winCondS pre = true) :
    QuerySupportedOn (fun p : Unit × SReg ↦ p.2)
      {s | s ∉ TrialHit pub v → s ∉ HConflict pub v → PreFactsS pub v pre s.2}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset HPos × Selections))
        (((runtimeR m₀).run₂ .instruments
          (realizeT v (prefixT Selections cwUpd strPol pub A))).branch pre (initU m₀))) := by
  have hc := conj_branch₂ m₀ (realizeT (good := goodAll) (M := Selections) v
    (prefixT Selections cwUpd strPol pub A)) pre (initU m₀)
  erw [hc]
  have H := ht₂_prefixT m₀ v strPol pub A (InvS pub v) (fun B M log ↦ ht₂_signT hsepH B M log)
    {s | NoBot s ∧ s.2 = (hwEmpty X Z, m₀)} fun s hs ↦ inv_nil hm₀l hm₀ hs
  refine (H _ (init_dec m₀) pre).mono ?_
  rintro s ⟨⟨hb, hfacts⟩, hpk⟩ hhit hconf
  have hwin := hw
  simp only [winCondS, RandomPermutationModel.sufCmaScheme, decide_eq_true_eq] at hwin
  exact preFacts_of hpd hsepK hb (hfacts hhit hconf hwin.1) hpk hwin.2

end final

end Quantum.Sphincs.Assembly

end
