module

public import Quantum.Qrom.CellEvent
public import Quantum.Qrom.Xmss.Slots
public import Quantum.Xmss.EncCost

@[expose] public section

/-!
# The XMSS event of the random oracle

The register of the hardwired runtime at `(Y, D) := (HashOutput, HashDomain)` holds the
adversary's database, the hardwired cells `W` and a finite memory `m : SelMem`: for each signed
key, the cell of its selected message-digest input and the selected digest. Each input `x` has at
most one slot (`slotOf`), hence at most one target digest `tgtDigest hon W m x`:

* **Struct** (a chain, leaf or node slot `s` of the table): the honest digest of `s` (`hon s`),
  unless `x` is the honest cell of `s` and hardwired;
* **Enc** (`msg l e` of a signed key): the selected digest, unless `x` is the selected cell.

The event `BadQ hon` is `CellTargetBad` for the targets `{y | truncateHash y = d}`:

* `upClosed_slice_badQ`, `not_mem_badQ_start`, `freshBound_slice_badQ`: the graded-bound
  hypotheses, with fresh fraction `2^-128` per input (`card_fiber_truncateHash`).
* **Program ports**: hardwiring a cell without a target once hardwired (an honest cell, a cell of
  a slot without targets, `ExemptCell`) costs nothing (`flipCost_programH_badQ_eq_zero`).
* **Read ports**: a trial read of key `(l, e)` (`SelectRead`) that records the selection only for
  a codeword digest (`cwSel`, `cwUpd`) flips at most `msgCwCount * 2^128` values
  (`card_flip_readCw_le`); its flip cost (`flipCost_selectReadCw_le`, `selectReadCwE_le`) and the
  survival of an unselected key (`survive_selectRead_le`, fraction `rhoCw`) reuse
  `Quantum.Xmss.EncCost`.
-/

open Matrix
open scoped ENNReal ComplexOrder

namespace Quantum.Qrom.Xmss

open Quantum Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss (Slot)

/-! ## Digests of hash outputs -/

theorem truncateHash_eq (y : HashOutput) :
    truncateHash y = (Quantum.Xmss.bitsEquiv 128).symm
      fun j ↦ Quantum.Xmss.bitsEquiv 256 y (Fin.castAdd 128 j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hj : j < 128 := hj
  change (y.extractLsb' 0 128).getLsbD j = ((Quantum.Xmss.bitsEquiv 128).symm _).getLsbD j
  rw [Quantum.Xmss.getLsbD_bitsEquiv_symm _ _ j hj, BitVec.getLsbD_extractLsb',
    Quantum.Xmss.bitsEquiv_apply]
  simp [hj]

/-- The pairs with a given first component number the second factor. -/
theorem card_filter_fst_eq_card {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] (a : A) :
    (Finset.univ.filter fun p : A × B ↦ p.1 = a).card = Fintype.card B := by
  rw [show (Finset.univ.filter fun p : A × B ↦ p.1 = a) =
      Finset.univ.map (Function.Embedding.sectR a B) by
    ext ⟨a', b⟩
    simp [eq_comm], Finset.card_map, Finset.card_univ]

/-- Each digest has `2^128` preimages under `truncateHash`. -/
theorem card_fiber_truncateHash (d : Digest) :
    (Finset.univ.filter fun y : HashOutput ↦ truncateHash y = d).card = 2 ^ 128 := by
  calc (Finset.univ.filter fun y : HashOutput ↦ truncateHash y = d).card
      = (Finset.univ.filter fun p : (Fin 128 → ZMod 2) × (Fin 128 → ZMod 2) ↦
          p.1 = Quantum.Xmss.bitsEquiv 128 d).card :=
        Finset.card_equiv ((Quantum.Xmss.bitsEquiv 256).trans
          (Fin.appendEquiv (α := ZMod 2) 128 128).symm) fun y ↦ by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, truncateHash_eq]
          exact (Quantum.Xmss.bitsEquiv 128).symm_apply_eq
    _ = Fintype.card (Fin 128 → ZMod 2) := card_filter_fst_eq_card _
    _ = 2 ^ 128 := by simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem card_fiber_truncateHash_le (d : Digest) :
    (Finset.univ.filter fun y : HashOutput ↦ truncateHash y = d).card ≤ 2 ^ 128 :=
  (card_fiber_truncateHash d).le

theorem card_hashOutput : Fintype.card HashOutput = 2 ^ 256 := by
  rw [Fintype.card_congr (Quantum.Xmss.bitsEquiv 256)]
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- The fraction of one digest's preimages: `2^128 / 2^256 = 2^-128`. -/
theorem fiber_div_card_hashOutput :
    ((2 ^ 128 : ℕ) : ℝ≥0∞) / Fintype.card HashOutput = (2 ^ 128)⁻¹ := by
  rw [card_hashOutput, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
    show (256 : ℕ) = 128 + 128 from rfl, pow_add]
  calc (2 : ℝ≥0∞) ^ 128 / (2 ^ 128 * 2 ^ 128) = 2 ^ 128 * 1 / (2 ^ 128 * 2 ^ 128) := by
        rw [mul_one]
    _ = 1 / 2 ^ 128 := ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ (by simp))
        (ENNReal.pow_ne_top (by simp))
    _ = (2 ^ 128)⁻¹ := one_div _

/-- The same fraction over the reals. -/
theorem two_pow_div_card_hashOutput : (2 : ℝ) ^ 128 / Fintype.card HashOutput = (2 ^ 128)⁻¹ := by
  rw [card_hashOutput, Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 128 + 128 from rfl,
    pow_add, div_mul_cancel_left₀ (pow_ne_zero _ two_ne_zero)]

/-- **The codeword values of a cell**: `cwCount * 2^128` hash outputs truncate to a codeword. -/
theorem card_codeword_truncateHash :
    (Finset.univ.filter fun v : HashOutput ↦ Codeword.Valid (truncateHash v)).card =
      Quantum.Xmss.cwCount * 2 ^ 128 := by
  rw [Quantum.Xmss.cwCount]
  have h := Quantum.Xmss.card_filter_out_add (out := truncateHash) (F := 2 ^ 128)
    card_fiber_truncateHash (fun d ↦ Codeword.Valid d) (0 : HashOutput)
  simp only [zero_add] at h
  exact h

/-- The codeword values of a cell are a fraction `rhoCw` of its values. -/
theorem card_codeword_div_card_hashOutput :
    ((Finset.univ.filter fun v : HashOutput ↦ Codeword.Valid (truncateHash v)).card : ℝ) /
      Fintype.card HashOutput = Quantum.Xmss.rhoCw := by
  rw [card_codeword_truncateHash, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc,
    two_pow_div_card_hashOutput, Quantum.Xmss.rhoCw, div_eq_mul_inv]

/-! ## The finite memory -/

/-- **The memory of the hardwired register**: for each signed key, the cell of its selected
message-digest input and the selected digest. -/
abbrev SelMem := Layer → KeyIndex → Option (HashDomain × Digest)

instance instFintypeSelMem : Fintype SelMem := by
  unfold SelMem
  infer_instance

instance instDecidableEqSelMem : DecidableEq SelMem := by
  unfold SelMem
  infer_instance

/-- Recording the selection of key `e` of layer `l`: cell `c`, digest `d`. -/
def SelMem.select (m : SelMem) (l : Layer) (e : KeyIndex) (c : HashDomain) (d : Digest) :
    SelMem :=
  Function.update m l (Function.update (m l) e (some (c, d)))

theorem SelMem.select_self (m : SelMem) (l : Layer) (e : KeyIndex) (c : HashDomain)
    (d : Digest) : m.select l e c d l e = some (c, d) := by
  simp [SelMem.select]

theorem SelMem.select_of_ne (m : SelMem) {l l' : Layer} {e e' : KeyIndex} (c : HashDomain)
    (d : Digest) (h : ¬(l' = l ∧ e' = e)) : m.select l e c d l' e' = m l' e' := by
  simp only [SelMem.select]
  by_cases hl : l' = l
  · subst hl
    rw [Function.update_self, Function.update_of_ne fun he ↦ h ⟨rfl, he⟩]
  · rw [Function.update_of_ne hl]

/-! ## Targets -/

/-- **The honest cells**: for each Struct slot of the table, the cell of its honest input and its
honest digest; `none` for the other slots. -/
abbrev HonestCells := Slot → Option (HashDomain × Digest)

/-- The target digest of the input `x` at a non-message slot `s`: the honest digest of `s`,
unless `x` is the honest cell of `s` and hardwired. -/
def structDigest (hon : HonestCells) (W : Database HashDomain HashOutput) (x : HashDomain)
    (s : Slot) : Option Digest :=
  (hon s).bind fun h ↦ if h.1 = x ∧ (W x).isSome then none else some h.2

/-- The target digest of the input `x` at slot `s`: at the message slot of a signed key its
selected digest unless `x` is the selected cell, elsewhere `structDigest`. -/
def slotDigest (hon : HonestCells) (W : Database HashDomain HashOutput) (m : SelMem)
    (x : HashDomain) : Slot → Option Digest
  | .msg l e => (m l e).bind fun sel ↦ if sel.1 = x then none else some sel.2
  | s => structDigest hon W x s

/-- **The target digest of an input**, read from its slot. -/
def tgtDigest (hon : HonestCells) (W : Database HashDomain HashOutput) (m : SelMem)
    (x : HashDomain) : Option Digest :=
  (slotOf x).bind (slotDigest hon W m x)

/-- **The XMSS targets** of the hardwired register's classical data `(W, m)`: the outputs of
`x` truncating to its target digest. -/
def xmssTgtQ (hon : HonestCells) (W : Hw HashOutput HashDomain) (m : SelMem) (x : HashDomain) :
    Set HashOutput :=
  {y | tgtDigest hon W.1 m x = some (truncateHash y)}

/-- **The XMSS event of the random oracle**: a recorded or hardwired cell whose value truncates to
its target digest. -/
abbrev BadQ (hon : HonestCells) : Set (RomReg HashDomain HashOutput SelMem) :=
  CellTargetBad (xmssTgtQ hon)

variable {hon : HonestCells}

theorem mem_xmssTgtQ {W : Hw HashOutput HashDomain} {m : SelMem} {x : HashDomain}
    {y : HashOutput} : y ∈ xmssTgtQ hon W m x ↔ tgtDigest hon W.1 m x = some (truncateHash y) :=
  Iff.rfl

theorem mem_badQ_iff {s : RomReg HashDomain HashOutput SelMem} :
    s ∈ BadQ hon ↔
      ∃ x y, unionH s x = some y ∧ tgtDigest hon s.2.1.1 s.2.2 x = some (truncateHash y) :=
  Iff.rfl

theorem slotDigest_of_ne_msg (W : Database HashDomain HashOutput) (m : SelMem) (x : HashDomain)
    {s : Slot} (h : ∀ l e, s ≠ .msg l e) : slotDigest hon W m x s = structDigest hon W x s := by
  cases s with
  | msg l e => exact absurd rfl (h l e)
  | _ => rfl

theorem slotDigest_msg (W : Database HashDomain HashOutput) (m : SelMem) (x : HashDomain)
    (l : Layer) (e : KeyIndex) :
    slotDigest hon W m x (.msg l e) =
      (m l e).bind fun sel ↦ if sel.1 = x then none else some sel.2 :=
  rfl

/-- The target of `x` depends on the hardwired cells only through whether `x` is hardwired. -/
theorem tgtDigest_congr {W W' : Database HashDomain HashOutput} (m : SelMem) {x : HashDomain}
    (h : (W x).isSome = (W' x).isSome) : tgtDigest hon W m x = tgtDigest hon W' m x := by
  unfold tgtDigest
  cases slotOf x with
  | none => rfl
  | some s =>
    simp only [Option.bind_some]
    by_cases hs : ∀ l e, s ≠ .msg l e
    · rw [slotDigest_of_ne_msg _ _ _ hs, slotDigest_of_ne_msg _ _ _ hs, structDigest,
        structDigest, h]
    · push Not at hs
      obtain ⟨l, e, rfl⟩ := hs
      rfl

/-- **More hardwired cells, fewer targets.** -/
theorem tgtDigest_anti {W W' : Database HashDomain HashOutput} (m : SelMem) {x : HashDomain}
    (h : (W x).isSome → (W' x).isSome) {d : Digest} (hd : tgtDigest hon W' m x = some d) :
    tgtDigest hon W m x = some d := by
  unfold tgtDigest at hd ⊢
  revert hd
  cases slotOf x with
  | none => exact id
  | some s =>
    simp only [Option.bind_some]
    by_cases hs : ∀ l e, s ≠ .msg l e
    · rw [slotDigest_of_ne_msg _ _ _ hs, slotDigest_of_ne_msg _ _ _ hs, structDigest,
        structDigest]
      cases hon s with
      | none => exact id
      | some hc =>
        simp only [Option.bind_some]
        intro hd
        by_cases hc' : hc.1 = x ∧ (W' x).isSome
        · rw [ite_eq_left hc'] at hd
          cases hd
        · rw [ite_eq_right hc'] at hd
          rw [ite_eq_right fun hc'' ↦ hc' ⟨hc''.1, h hc''.2⟩]
          exact hd
    · push Not at hs
      obtain ⟨l, e, rfl⟩ := hs
      exact id

/-- An input of no slot has no target. -/
theorem tgtDigest_of_slotOf_none (W : Database HashDomain HashOutput) (m : SelMem)
    {x : HashDomain} (hx : slotOf x = none) : tgtDigest hon W m x = none := by
  rw [tgtDigest, hx]
  rfl

/-- An input at a non-message slot without honest cell has no target. -/
theorem tgtDigest_of_hon_none (W : Database HashDomain HashOutput) (m : SelMem)
    {x : HashDomain} {s : Slot} (hx : slotOf x = some s) (hmsg : ∀ l e, s ≠ .msg l e)
    (hs : hon s = none) : tgtDigest hon W m x = none := by
  rw [tgtDigest, hx, Option.bind_some, slotDigest_of_ne_msg _ _ _ hmsg, structDigest, hs]
  rfl

/-- **A hardwired honest cell has no target.** -/
theorem tgtDigest_honest_of_hw {W : Database HashDomain HashOutput} (m : SelMem)
    {z : HashDomain} {s : Slot} {d : Digest} (hz : slotOf z = some s)
    (hmsg : ∀ l e, s ≠ .msg l e) (hs : hon s = some (z, d)) (hW : (W z).isSome) :
    tgtDigest hon W m z = none := by
  rw [tgtDigest, hz, Option.bind_some, slotDigest_of_ne_msg _ _ _ hmsg, structDigest, hs,
    Option.bind_some, ite_eq_left ⟨rfl, hW⟩]

/-- A cell at the message slot of an unselected key has no target. -/
theorem tgtDigest_msg_none (W : Database HashDomain HashOutput) {m : SelMem} {x : HashDomain}
    {l : Layer} {e : KeyIndex} (hx : slotOf x = some (.msg l e)) (hm : m l e = none) :
    tgtDigest hon W m x = none := by
  rw [tgtDigest, hx, Option.bind_some, slotDigest_msg, hm]
  rfl

/-- The selected cell has no target. -/
theorem tgtDigest_select_self (W : Database HashDomain HashOutput) (m : SelMem) {c : HashDomain}
    {l : Layer} {e : KeyIndex} (hc : slotOf c = some (.msg l e)) (d : Digest) :
    tgtDigest hon W (m.select l e c d) c = none := by
  rw [tgtDigest, hc, Option.bind_some, slotDigest_msg, SelMem.select_self, Option.bind_some,
    ite_eq_left rfl]

/-- Recording a selection adds the selected digest as the target of the other cells at its
message slot, and nothing else. -/
theorem tgtDigest_select {W : Database HashDomain HashOutput} {m : SelMem} {l : Layer}
    {e : KeyIndex} {c x : HashDomain} {d d' : Digest}
    (h : tgtDigest hon W (m.select l e c d) x = some d') :
    tgtDigest hon W m x = some d' ∨ (slotOf x = some (.msg l e) ∧ x ≠ c ∧ d' = d) := by
  unfold tgtDigest at h ⊢
  revert h
  cases hs : slotOf x with
  | none => exact fun h ↦ absurd h (by simp)
  | some s =>
    simp only [Option.bind_some]
    intro h
    by_cases hmsg : ∀ l e, s ≠ .msg l e
    · rw [slotDigest_of_ne_msg _ _ _ hmsg] at h
      rw [slotDigest_of_ne_msg _ _ _ hmsg]
      exact .inl h
    · push Not at hmsg
      obtain ⟨l', e', rfl⟩ := hmsg
      rw [slotDigest_msg] at h ⊢
      by_cases hk : l' = l ∧ e' = e
      · obtain ⟨rfl, rfl⟩ := hk
        right
        rw [SelMem.select_self, Option.bind_some] at h
        by_cases hx : c = x
        · rw [ite_eq_left hx] at h
          cases h
        · rw [ite_eq_right hx] at h
          exact ⟨rfl, fun h' ↦ hx h'.symm, (Option.some.inj h).symm⟩
      · left
        rw [SelMem.select_of_ne m c d hk] at h
        exact h

/-- Recording the selection of an unselected key keeps every target. -/
theorem tgtDigest_select_mono {W : Database HashDomain HashOutput} {m : SelMem} {l : Layer}
    {e : KeyIndex} (hm : m l e = none) (c : HashDomain) (d : Digest) {x : HashDomain}
    {d' : Digest} (h : tgtDigest hon W m x = some d') :
    tgtDigest hon W (m.select l e c d) x = some d' := by
  unfold tgtDigest at h ⊢
  revert h
  cases slotOf x with
  | none => exact id
  | some s =>
    simp only [Option.bind_some]
    by_cases hmsg : ∀ l e, s ≠ .msg l e
    · rw [slotDigest_of_ne_msg _ _ _ hmsg, slotDigest_of_ne_msg _ _ _ hmsg]
      exact id
    · push Not at hmsg
      obtain ⟨l', e', rfl⟩ := hmsg
      rw [slotDigest_msg, slotDigest_msg]
      by_cases hk : l' = l ∧ e' = e
      · obtain ⟨rfl, rfl⟩ := hk
        rw [hm]
        exact fun h ↦ absurd h (by simp)
      · rw [SelMem.select_of_ne m c d hk]
        exact id

/-! ## The graded-bound hypotheses -/

/-- **Every slice of the event is upward closed.** -/
theorem upClosed_slice_badQ (W : Hw HashOutput HashDomain) (m : SelMem) :
    UpClosed (slice (BadQ hon) W m) :=
  upClosed_slice_cellTargetBad W m

/-- **The start is outside the event** when no hardwired cell has a target. -/
theorem not_mem_badQ_start (W₀ : Hw HashOutput HashDomain) (m₀ : SelMem)
    (h : ∀ x, (W₀.1 x).isSome → tgtDigest hon W₀.1 m₀ x = none) :
    (((Database.empty, Database.empty, Database.empty), W₀, m₀) :
      RomReg HashDomain HashOutput SelMem) ∉ BadQ hon :=
  not_mem_cellTargetBad_start W₀ m₀ fun x y hxy hy ↦ by
    have h0 := h x (by rw [hxy]; rfl)
    rw [mem_xmssTgtQ, h0] at hy
    cases hy

/-- The start without hardwired cells is outside the event. -/
theorem empty_not_mem_badQ (m₀ : SelMem) :
    (((Database.empty, Database.empty, Database.empty),
      (Database.empty, Database.empty, Database.empty), m₀) :
      RomReg HashDomain HashOutput SelMem) ∉ BadQ hon :=
  not_mem_badQ_start _ m₀ fun _ h ↦ absurd h (by simp [Database.empty])

open scoped Classical in
/-- The targets of an input are at most one digest's preimages. -/
theorem card_xmssTgtQ_le (W : Hw HashOutput HashDomain) (m : SelMem) (x : HashDomain) :
    (Finset.univ.filter fun y ↦ y ∈ xmssTgtQ hon W m x).card ≤ 2 ^ 128 := by
  cases hd : tgtDigest hon W.1 m x with
  | none =>
    rw [Finset.filter_false_of_mem fun y _ hy ↦ by rw [mem_xmssTgtQ, hd] at hy; cases hy]
    simp
  | some d =>
    refine le_trans (Finset.card_le_card fun y hy ↦ ?_) (card_fiber_truncateHash_le d)
    have hy : y ∈ xmssTgtQ hon W m x := (Finset.mem_filter.1 hy).2
    rw [mem_xmssTgtQ, hd] at hy
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Option.some.inj hy).symm⟩

/-- **The fresh bound of every slice**: a fresh cell enters the event with probability at most
`2^-128`, a fresh `k`, `k'` cell never. -/
theorem freshBound_slice_badQ (W : Hw HashOutput HashDomain) (m : SelMem) (t : ℕ) :
    FreshBound (slice (BadQ hon) W m) t (2 ^ 128)⁻¹ := by
  classical
  refine freshBound_slice_cellTargetBad W m (fun x _ ↦ ?_) t
  rw [← fiber_div_card_hashOutput]
  exact ENNReal.div_le_div_right (by exact_mod_cast card_xmssTgtQ_le W m x) _

/-! ## Program ports -/

/-- A cell without a target once hardwired, whatever the other cells and the memory: an honest
cell, a cell of a non-message slot without honest cell, a cell of no slot. -/
def ExemptCell (hon : HonestCells) (z : HashDomain) : Prop :=
  ∀ (W : Database HashDomain HashOutput) (m : SelMem), (W z).isSome → tgtDigest hon W m z = none

theorem exemptCell_honest {z : HashDomain} {s : Slot} {d : Digest} (hz : slotOf z = some s)
    (hmsg : ∀ l e, s ≠ .msg l e) (hs : hon s = some (z, d)) : ExemptCell hon z :=
  fun _ m hW ↦ tgtDigest_honest_of_hw m hz hmsg hs hW

theorem exemptCell_of_hon_none {z : HashDomain} {s : Slot} (hz : slotOf z = some s)
    (hmsg : ∀ l e, s ≠ .msg l e) (hs : hon s = none) : ExemptCell hon z :=
  fun W m _ ↦ tgtDigest_of_hon_none W m hz hmsg hs

theorem exemptCell_of_slotOf_none {z : HashDomain} (hz : slotOf z = none) : ExemptCell hon z :=
  fun W m _ ↦ tgtDigest_of_slotOf_none W m hz

/-- An exempt cell has no target once hardwired. -/
theorem ExemptCell.tgtDigest_update {z : HashDomain} (hz : ExemptCell hon z)
    (W : Database HashDomain HashOutput) (m : SelMem) (v : HashOutput) :
    tgtDigest hon (Function.update W z (some v)) m z = none :=
  hz _ _ (by rw [Function.update_self]; rfl)

/-- Hardwiring `z` leaves the targets of the other cells. -/
theorem tgtDigest_update_of_ne (W : Database HashDomain HashOutput) (m : SelMem)
    {z x : HashDomain} (hx : x ≠ z) (o : Option HashOutput) :
    tgtDigest hon (Function.update W z o) m x = tgtDigest hon W m x :=
  tgtDigest_congr m (by rw [Function.update_of_ne hx])

/-- **Programming an exempt cell flips nothing**: its new target is empty and the other targets
are unchanged. -/
theorem not_mem_badQ_programH {s : RomReg HashDomain HashOutput SelMem} (hs : s ∉ BadQ hon)
    {z : HashDomain} (hz : ExemptCell hon z) (v : HashOutput) :
    progMap (.programH z v) s ∉ BadQ hon :=
  not_mem_cellTargetBad_programH hs z v
    (fun _ hx _ hy ↦ (tgtDigest_update_of_ne s.2.1.1 s.2.2 hx (some v)).symm.trans hy)
    (fun hv ↦ Option.some_ne_none _ ((hz.tgtDigest_update s.2.1.1 s.2.2 v).symm.trans hv).symm)

/-- **Programming cost zero**: hardwiring an exempt cell, in particular an honest cell
(`exemptCell_honest`), costs nothing. -/
theorem flipCost_programH_badQ_eq_zero {z : HashDomain} (hz : ExemptCell hon z) (v : HashOutput)
    {σ : Matrix (Unit × RomReg HashDomain HashOutput SelMem)
      (Unit × RomReg HashDomain HashOutput SelMem) ℂ} (hσ : σ.PosSemidef) :
    flipCost (BadQ hon) (hwProgKraus (.programH z v)) 0 σ = 0 :=
  flipCost_programH_cellTargetBad_eq_zero z v hσ fun q _ _ ↦
    ⟨fun _ hx _ hy ↦ (tgtDigest_update_of_ne q.2.2.1.1 q.2.2.2 hx (some v)).symm.trans hy,
      fun hv ↦ Option.some_ne_none _
        ((hz.tgtDigest_update q.2.2.1.1 q.2.2.2 v).symm.trans hv).symm⟩

/-! ## Read ports -/

/-- **A trial read**: the read of the cell `z` of a message-digest trial of the unselected key
`(l, e)`, neither hardwired nor recorded. -/
structure SelectRead (s : RomReg HashDomain HashOutput SelMem) (z : HashDomain) (l : Layer)
    (e : KeyIndex) : Prop where
  hw : s.2.1.1 z = none
  hd : s.1.1 z = none
  hm : s.2.2 l e = none
  slot : slotOf z = some (.msg l e)

/-- **The memory after a trial read** of key `(l, e)` at cell `z` with value `v`: the selection if
the digest is a codeword. -/
def cwSel (m : SelMem) (l : Layer) (e : KeyIndex) (z : HashDomain) (v : HashOutput) : SelMem :=
  if Codeword.Valid (truncateHash v) then m.select l e z (truncateHash v) else m

/-- **The memory update of a trial read**: select a codeword digest of an unselected key. -/
def cwUpd (l : Layer) (e : KeyIndex) (z : HashDomain) : SelMem → Option HashOutput → SelMem
  | m, some v => if m l e = none then cwSel m l e z v else m
  | m, none => m

theorem cwUpd_some (l : Layer) (e : KeyIndex) (z : HashDomain) (m : SelMem) (v : HashOutput) :
    cwUpd l e z m (some v) = m ∨ cwUpd l e z m (some v) = cwSel m l e z v := by
  show (if m l e = none then cwSel m l e z v else m) = m ∨
    (if m l e = none then cwSel m l e z v else m) = cwSel m l e z v
  split_ifs
  · exact .inr rfl
  · exact .inl rfl

theorem cwUpd_some_of_none (l : Layer) (e : KeyIndex) (z : HashDomain) {m : SelMem}
    (hm : m l e = none) (v : HashOutput) : cwUpd l e z m (some v) = cwSel m l e z v :=
  ite_eq_left hm

/-- A trial of an unselected key leaves it unselected exactly when its digest is no codeword. -/
theorem cwSel_eq_none_iff {m : SelMem} {l : Layer} {e : KeyIndex} (hm : m l e = none)
    (z : HashDomain) (v : HashOutput) :
    cwSel m l e z v l e = none ↔ ¬ Codeword.Valid (truncateHash v) := by
  unfold cwSel
  split_ifs with hv
  · rw [SelMem.select_self]
    exact iff_of_false (Option.some_ne_none _) (not_not.2 hv)
  · exact iff_of_true hm hv

/-- A trial read keeps or grows every target. -/
theorem tgtDigest_cwSel_mono {W : Database HashDomain HashOutput} {m : SelMem} {l : Layer}
    {e : KeyIndex} (hm : m l e = none) (z : HashDomain) (v : HashOutput) {x : HashDomain}
    {d : Digest} (h : tgtDigest hon W m x = some d) :
    tgtDigest hon W (cwSel m l e z v) x = some d := by
  unfold cwSel
  split_ifs
  · exact tgtDigest_select_mono hm z _ h
  · exact h

/-- **A read that keeps the memory flips nothing**: the trial's cell is at the message slot of an
unselected key, so it has no target. -/
theorem not_mem_badQ_read_keep {s : RomReg HashDomain HashOutput SelMem} (hs : s ∉ BadQ hon)
    {z : HashDomain} {l : Layer} {e : KeyIndex} (hr : SelectRead s z l e) (u : Option HashOutput) :
    ((Function.update s.1.1 z u, s.1.2), s.2.1, s.2.2) ∉ BadQ hon :=
  not_mem_cellTargetBad_readH hs s.2.2
    (Set.eq_empty_iff_forall_notMem.2 fun y hy ↦ by
      rw [mem_xmssTgtQ, tgtDigest_msg_none _ hr.slot hr.hm] at hy
      cases hy)
    (fun _ _ _ h ↦ h) u

section Generic

variable {D Y M : Type} [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y]

open scoped Classical in
/-- The recorded or hardwired cells of a union view satisfying `P` whose value satisfies `Qo`. -/
noncomputable def cellOutCount (U : D → Option Y) (P : D → Prop) (Qo : Y → Prop) : ℕ :=
  (Finset.univ.filter fun x ↦ P x ∧ ∃ y, U x = some y ∧ Qo y).card

omit [Fintype Y] [DecidableEq Y] in
/-- **Exclusive predicates share the cells**: the counts of predicates no cell satisfies twice
add up to at most the cells of their union. -/
theorem sum_cellOutCount_le {κ : Type} [Fintype κ] (U : D → Option Y) (P : κ → D → Prop)
    (hP : ∀ k k' x, P k x → P k' x → k = k') (Qo : Y → Prop) :
    ∑ k, cellOutCount U (P k) Qo ≤ cellOutCount U (fun x ↦ ∃ k, P k x) fun _ ↦ True := by
  unfold cellOutCount
  rw [← Finset.card_biUnion]
  · refine Finset.card_le_card fun x hx ↦ ?_
    obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨hPk, y, hy, -⟩ := hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨k, hPk⟩, y, hy, trivial⟩
  · intro k _ k' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact hne (hP k k' x hx.1 hx'.1)

open scoped Classical in
/-- **The flip count of a read with output-restricted new targets**: reading a cell `z` without a
target after the read, with memory `m' v` after reading `v`, whose new targets on other cells are
the values `y` with `out y = out v` on cells satisfying `P`, and only if `Qo (out v)`. Then at most
`cellOutCount P (Qo ∘ out) * F` values flip a state outside the event, whatever the read leaves
in the cell; `F` bounds the fibers of `out`. -/
theorem card_flip_readH_out_le {tgt : Hw Y D → M → D → Set Y} {O : Type} [DecidableEq O]
    (out : Y → O) {F : ℕ} (hF : ∀ o, (Finset.univ.filter fun y ↦ out y = o).card ≤ F)
    {s : RomReg D Y M} (hs : s ∉ CellTargetBad tgt) {z : D} (P : D → Prop) (Qo : O → Prop)
    (m' : Y → M) (hz : ∀ v, tgt s.2.1 (m' v) z = ∅)
    (hext : ∀ v x, x ≠ z → ∀ y ∈ tgt s.2.1 (m' v) x,
      y ∈ tgt s.2.1 s.2.2 x ∨ (P x ∧ Qo (out v) ∧ out y = out v)) :
    (Finset.univ.filter fun v : Y ↦ ∃ u : Option Y,
      ((Function.update s.1.1 z u, s.1.2), s.2.1, m' v) ∈ CellTargetBad tgt).card ≤
        cellOutCount (unionH s) P (fun y ↦ Qo (out y)) * F := by
  let C := Finset.univ.filter fun x ↦ P x ∧ ∃ y, unionH s x = some y ∧ Qo (out y)
  let S : D → Finset Y := fun x ↦ Finset.univ.filter fun v ↦
    ∃ y, unionH s x = some y ∧ out v = out y
  have hsub : (Finset.univ.filter fun v : Y ↦ ∃ u : Option Y,
      ((Function.update s.1.1 z u, s.1.2), s.2.1, m' v) ∈ CellTargetBad tgt) ⊆ C.biUnion S := by
    intro v hv
    obtain ⟨u, x, y, hxy, hy⟩ := (Finset.mem_filter.1 hv).2
    by_cases hx : x = z
    · subst hx
      rw [hz v] at hy
      exact absurd hy (Set.notMem_empty y)
    · change (s.2.1.1 x).or (Function.update s.1.1 z u x) = some y at hxy
      rw [Function.update_of_ne hx] at hxy
      rcases hext v x hx y hy with hy' | ⟨hP, hQ, ho⟩
      · exact absurd ⟨x, y, hxy, hy'⟩ hs
      · exact Finset.mem_biUnion.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, hP, y, hxy,
          by rw [ho]; exact hQ⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, y, hxy, ho.symm⟩⟩
  have hS : ∀ x ∈ C, (S x).card ≤ F := by
    intro x _
    rcases hx : unionH s x with _ | y₀
    · have h0 : S x = ∅ := Finset.filter_eq_empty_iff.mpr fun v _ ⟨y, hy, _⟩ ↦ by
        rw [hx] at hy
        cases hy
      rw [h0, Finset.card_empty]
      exact Nat.zero_le F
    · refine le_trans (Finset.card_le_card fun v hv ↦ ?_) (hF (out y₀))
      obtain ⟨y, hy, hv'⟩ := (Finset.mem_filter.1 hv).2
      rw [hx] at hy
      cases hy
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hv'⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul C S _ hS)

end Generic

/-- The recorded or hardwired cells of a union view at the message slot of key `(l, e)` whose
value truncates to a codeword. -/
noncomputable def msgCwCount (U : HashDomain → Option HashOutput) (l : Layer) (e : KeyIndex) :
    ℕ :=
  cellOutCount U (fun x ↦ slotOf x = some (.msg l e)) fun y ↦ Codeword.Valid (truncateHash y)

/-- The recorded or hardwired cells of a union view at a message slot. -/
noncomputable def msgSlotCount (U : HashDomain → Option HashOutput) : ℕ :=
  cellOutCount U (fun x ↦ ∃ k : Layer × KeyIndex, slotOf x = some (.msg k.1 k.2)) fun _ ↦ True

/-- **The keys share the message-slot cells**: each cell has one slot, so the codeword counts of
all keys add up to at most the message-slot cells. -/
theorem sum_msgCwCount_le (U : HashDomain → Option HashOutput) :
    ∑ k : Layer × KeyIndex, msgCwCount U k.1 k.2 ≤ msgSlotCount U := by
  have hP : ∀ (k k' : Layer × KeyIndex) (x : HashDomain),
      slotOf x = some (.msg k.1 k.2) → slotOf x = some (.msg k'.1 k'.2) → k = k' :=
    fun k k' x h h' ↦ by
      obtain ⟨h1, h2⟩ := Slot.msg.inj (Option.some.inj (h.symm.trans h'))
      exact Prod.ext h1 h2
  -- Named arguments: unifying the generic sum with this one would unfold `Finset.univ`.
  have h := sum_cellOutCount_le (κ := Layer × KeyIndex) (D := HashDomain) (Y := HashOutput) U
    (fun k x ↦ slotOf x = some (.msg k.1 k.2)) hP fun y ↦ Codeword.Valid (truncateHash y)
  exact h

/-- After a trial read the read cell has no target. -/
theorem tgtDigest_cwSel_self (W : Database HashDomain HashOutput) {m : SelMem} {z : HashDomain}
    {l : Layer} {e : KeyIndex} (hz : slotOf z = some (.msg l e)) (hm : m l e = none)
    (v : HashOutput) : tgtDigest hon W (cwSel m l e z v) z = none := by
  unfold cwSel
  split_ifs
  · exact tgtDigest_select_self W m hz _
  · exact tgtDigest_msg_none W hz hm

/-- A trial read adds, for a codeword digest, the digest as the target of the other cells at its
message slot, and nothing else. -/
theorem tgtDigest_cwSel {W : Database HashDomain HashOutput} {m : SelMem} {l : Layer}
    {e : KeyIndex} {z x : HashDomain} {v : HashOutput} {d : Digest}
    (h : tgtDigest hon W (cwSel m l e z v) x = some d) :
    tgtDigest hon W m x = some d ∨ (slotOf x = some (.msg l e) ∧
      Codeword.Valid (truncateHash v) ∧ d = truncateHash v) := by
  unfold cwSel at h
  split_ifs at h with hv
  · rcases tgtDigest_select h with h' | ⟨h1, -, h3⟩
    · exact .inl h'
    · exact .inr ⟨h1, hv, h3⟩
  · exact .inl h

/-- **`card_flip_readCw_le`**: a trial read of key `(l, e)` that records the selection only for a
codeword digest flips a state outside `BadQ` for at most `msgCwCount * 2^128` values of the read
cell, whatever the read leaves in the cell: the flips are the codeword outputs of the other cells
at `msg l e`. -/
theorem card_flip_readCw_le {s : RomReg HashDomain HashOutput SelMem} (hs : s ∉ BadQ hon)
    {z : HashDomain} {l : Layer} {e : KeyIndex} (hr : SelectRead s z l e) :
    (Finset.univ.filter fun v : HashOutput ↦ ∃ u : Option HashOutput,
      ((Function.update s.1.1 z u, s.1.2), s.2.1, cwSel s.2.2 l e z v) ∈ BadQ hon).card ≤
        msgCwCount (unionH s) l e * 2 ^ 128 :=
  card_flip_readH_out_le (D := HashDomain) (Y := HashOutput) (M := SelMem) truncateHash
    card_fiber_truncateHash_le hs (fun x ↦ slotOf x = some (.msg l e))
    (fun d ↦ Codeword.Valid d) (fun v ↦ cwSel s.2.2 l e z v)
    (fun v ↦ Set.eq_empty_iff_forall_notMem.2 fun _ hy ↦ Option.some_ne_none _
      ((tgtDigest_cwSel_self s.2.1.1 hr.slot hr.hm v).symm.trans hy).symm)
    (fun _ _ _ _ hy ↦ (tgtDigest_cwSel hy).imp id fun h ↦ ⟨h.1, h.2.1, h.2.2⟩)

open scoped Classical in
/-- **The flip cost of a codeword-selecting read**: for a memory update that keeps the memory or
records the selection only for a codeword digest (`cwUpd`),
`E = ∑_{SelectRead, ∉ BadQ} msgCwCount · 2^128 / |Y| · σ_ss`. -/
theorem flipCost_selectReadCw_le (z : HashDomain) (l : Layer) (e : KeyIndex)
    (upd : SelMem → Option HashOutput → SelMem)
    (hupd : ∀ m v, upd m (some v) = m ∨ upd m (some v) = cwSel m l e z v)
    {σ : Matrix (Unit × RomReg HashDomain HashOutput SelMem)
      (Unit × RomReg HashDomain HashOutput SelMem) ℂ} (hσ : σ.PosSemidef) :
    flipCost (BadQ hon) (hwReadKraus (.readH z upd)) (readPs fun s ↦ SelectRead s z l e) σ ≤
      ENNReal.ofReal (∑ q, if SelectRead q.2 z l e ∧ q.2 ∉ BadQ hon then
          ((msgCwCount (unionH q.2) l e * 2 ^ 128 : ℕ) : ℝ) / Fintype.card HashOutput *
            (σ q q).re else 0) +
        ENNReal.ofReal ((readPs fun s ↦ SelectRead s z l e) * σ).trace.re +
      2 * (ENNReal.ofReal (∑ q, if SelectRead q.2 z l e ∧ q.2 ∉ BadQ hon then
          ((msgCwCount (unionH q.2) l e * 2 ^ 128 : ℕ) : ℝ) / Fintype.card HashOutput *
            (σ q q).re else 0) *
        ENNReal.ofReal ((readPs fun s ↦ SelectRead s z l e) * σ).trace.re) ^ (2⁻¹ : ℝ) := by
  refine flipCost_readH_le (BadQ hon) z upd (fun m v ↦ cwSel m l e z v)
    (fun s ↦ SelectRead s z l e) (fun s ↦ msgCwCount (unionH s) l e * 2 ^ 128) ?_ hupd ?_ ?_ ?_
    ?_ hσ
  · exact fun _ hs ↦ ⟨hs.hd, hs.hw⟩
  · exact fun _ u hs hS ↦ not_mem_badQ_read_keep hS hs u
  · intro s hs hS
    convert card_flip_readCw_le hS hs using 3
  · exact fun s u hs hS ↦ mem_cellTargetBad_fill hS hs.hd u s.2.2 fun _ _ ht ↦ ht
  · exact fun s u v hs hS ↦ mem_cellTargetBad_fill hS hs.hd u _ fun _ _ ht ↦
      tgtDigest_cwSel_mono hs.hm z v ht

open scoped Classical in
/-- **The selecting-read term** of `flipCost_selectReadCw_le`: if `msgCwCount ≤ C` on the
selection reads of the support outside `BadQ`, then `E ≤ C 2^-128 e`, with `e` the weight of the
selection reads. -/
theorem selectReadCwE_le (z : HashDomain) (l : Layer) (e : KeyIndex) (C : ℕ)
    {σ : Matrix (Unit × RomReg HashDomain HashOutput SelMem)
      (Unit × RomReg HashDomain HashOutput SelMem) ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ q, SelectRead q.2 z l e → q.2 ∉ BadQ hon → σ q q ≠ 0 →
      msgCwCount (unionH q.2) l e ≤ C) :
    (∑ q, if SelectRead q.2 z l e ∧ q.2 ∉ BadQ hon then
        ((msgCwCount (unionH q.2) l e * 2 ^ 128 : ℕ) : ℝ) / Fintype.card HashOutput *
          (σ q q).re else 0) ≤
      C * (2 ^ 128)⁻¹ * ∑ q, if SelectRead q.2 z l e then (σ q q).re else 0 := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hC0 : (0 : ℝ) ≤ C * (2 ^ 128)⁻¹ := by positivity
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases hq : SelectRead q.2 z l e
  · rw [ite_eq_left hq]
    by_cases hb : q.2 ∉ BadQ hon
    · rw [ite_eq_left ⟨hq, hb⟩]
      by_cases hσq : σ q q = 0
      · rw [hσq, Complex.zero_re, mul_zero, mul_zero]
      refine mul_le_mul_of_nonneg_right ?_ (hre q)
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc,
        two_pow_div_card_hashOutput]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (hC q hq hb hσq)) (by positivity)
    · rw [ite_eq_right fun h ↦ hb h.2]
      exact mul_nonneg hC0 (hre q)
  · rw [ite_eq_right fun h ↦ hq h.1, ite_eq_right hq, mul_zero]

/-! ## Survival of a trial -/

/-- The memories whose key `(l, e)` has no selection. -/
def unselMem (l : Layer) (e : KeyIndex) : Set SelMem := {m | m l e = none}

instance instDecidablePredUnselMem (l : Layer) (e : KeyIndex) :
    DecidablePred (· ∈ unselMem l e) :=
  fun m ↦ inferInstanceAs (Decidable (m l e = none))

open scoped Classical in
/-- **Survival of a trial read**: the outcomes of a trial of the unselected key `(l, e)` that
leave it unselected weigh at most `w - ρ_c e + p + 2 √(ρ_c e p)`, with `w` the weight of the
states where the key is unselected, `e` the weight of the selection reads `SR` (cell empty and not
hardwired, key unselected) and `p = tr (P σ)` the rest: on an empty cell the trial's digest is a
codeword with probability `rhoCw`. -/
theorem survive_selectRead_le (z : HashDomain) (l : Layer) (e : KeyIndex)
    (upd : SelMem → Option HashOutput → SelMem)
    (hupd : ∀ m v, m l e = none → upd m (some v) = cwSel m l e z v)
    (SR : RomReg HashDomain HashOutput SelMem → Prop) [DecidablePred SR]
    (hSR : ∀ s, SR s → s.1.1 z = none ∧ s.2.1.1 z = none ∧ s.2.2 ∈ unselMem l e)
    {σ : Matrix (Unit × RomReg HashDomain HashOutput SelMem)
      (Unit × RomReg HashDomain HashOutput SelMem) ℂ} (hσ : σ.PosSemidef) :
    (∑ r : Option HashOutput × SelMem, if upd r.2 r.1 ∈ unselMem l e then
        (MatrixMap.conj (hwReadKraus (.readH z upd) r) σ).trace.re else 0) ≤
      (∑ q, if q.2.2.2 ∈ unselMem l e then (σ q q).re else 0) -
        Quantum.Xmss.rhoCw * (∑ q, if SR q.2 then (σ q q).re else 0) +
        (readPs SR * σ).trace.re +
        2 * √(Quantum.Xmss.rhoCw * (∑ q, if SR q.2 then (σ q q).re else 0) *
          (readPs SR * σ).trace.re) :=
  survive_readH_le z upd (unselMem l e) (fun v ↦ Codeword.Valid (truncateHash v))
    card_codeword_div_card_hashOutput
    (fun m hm v ↦ by
      show upd m (some v) l e = none ↔ _
      rw [hupd m v hm]
      exact cwSel_eq_none_iff hm z v) SR hSR hσ

end Quantum.Qrom.Xmss

end
