module

public import Quantum.Qrom.Xmss.Multi.Table

@[expose] public section

/-!
# The XMSS event of the random oracle for `n` users

The memory of the hardwired register holds one single-user memory per user (`SelMemN n`). The
users' public parameters `P` determine the owner of an input (`ownerOf P prefixOf`): the user whose
parameter is its prefix. Each input has at most one owner, hence at most one target digest, its
owner's single-user target (`tgtDigestN`): the honest digests `hon i` and selections `m i` of the
owner `i`. The event `BadQN hon P` is `CellTargetBad` for the targets `{y | truncateHash y = d}`:

* `upClosed_slice_badQN`, `not_mem_badQN_start`, `freshBound_slice_badQN`: the graded-bound
  hypotheses, with fresh fraction `2^-128` per input.
* **Program ports**: hardwiring a cell exempt for its owner (`exemptCellN_of_owner`), or of no
  owner, costs nothing (`flipCost_programH_badQN_eq_zero`).
* **Read ports**: a trial read of key `(l, e)` of user `i` (`SelectReadN`, the read cell owned by
  `i`) that records the selection only for a codeword digest (`cwSelN`, `cwUpdN`) flips at most
  `msgCwCountN * 2^128` values (`card_flip_readCwN_le`), the codeword cells at `msg l e` owned by
  `i`; the counts of all users' keys add up to at most the message-slot cells
  (`sum_msgCwCountN_le`). Flip cost (`flipCost_selectReadCwN_le`, `selectReadCwNE_le`) and
  survival (`survive_selectReadN_le`) as for one user.
-/

open Matrix
open scoped ENNReal ComplexOrder

namespace Quantum.Qrom.Xmss.Multi

open Quantum Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss (Slot)
open Quantum.Qrom.MultiUser (ownerOf ownerOf_eq_some)

variable {n : ℕ}

/-! ## Owners of cells -/

/-- **The owner of a prefixed cell** under distinct parameters is the user whose parameter it is
hashed under. -/
theorem ownerOf_cell {P : Fin n → PublicParameter} (hP : Function.Injective P) (i : Fin n)
    {s : Slot} (hs : Addressable s) (hp : prefixedSlot s = true) (d : Payload s) :
    ownerOf P prefixOf (cell (P i) s d) = some i :=
  ownerOf_eq_some hP (prefixOf_cell _ hs hp d)

/-! ## The memory -/

/-- **The memory of `n` users**: one single-user selection memory per user. -/
abbrev SelMemN (n : ℕ) := Fin n → SelMem

instance instFintypeSelMemN : Fintype (SelMemN n) := by
  unfold SelMemN
  infer_instance

instance instDecidableEqSelMemN : DecidableEq (SelMemN n) := by
  unfold SelMemN
  infer_instance

/-! ## Targets -/

/-- **The target digest of an input for `n` users**: its owner's single-user target. -/
def tgtDigestN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter)
    (W : Database HashDomain HashOutput) (m : SelMemN n) (x : HashDomain) : Option Digest :=
  (ownerOf P prefixOf x).bind fun i ↦ tgtDigest (hon i) W (m i) x

/-- **The XMSS targets for `n` users**: the outputs of `x` truncating to its target digest. -/
def xmssTgtQN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter)
    (W : Hw HashOutput HashDomain) (m : SelMemN n) (x : HashDomain) : Set HashOutput :=
  {y | tgtDigestN hon P W.1 m x = some (truncateHash y)}

/-- **The XMSS event of the random oracle for `n` users**: a recorded or hardwired cell whose
value truncates to its owner's target digest. -/
abbrev BadQN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter) :
    Set (RomReg HashDomain HashOutput (SelMemN n)) :=
  CellTargetBad (xmssTgtQN hon P)

/-- The users' honest cells of the table `w` at the master seeds `S0`. -/
def honN (S0 : Fin n → MasterSeed) (w : QTableN n) : Fin n → HonestCells :=
  fun i ↦ QTable.honCell (S0 i) (w.user i)

variable {hon : Fin n → HonestCells} {P : Fin n → PublicParameter}

theorem mem_xmssTgtQN {W : Hw HashOutput HashDomain} {m : SelMemN n} {x : HashDomain}
    {y : HashOutput} :
    y ∈ xmssTgtQN hon P W m x ↔ tgtDigestN hon P W.1 m x = some (truncateHash y) :=
  Iff.rfl

theorem mem_badQN_iff {s : RomReg HashDomain HashOutput (SelMemN n)} :
    s ∈ BadQN hon P ↔
      ∃ x y, unionH s x = some y ∧ tgtDigestN hon P s.2.1.1 s.2.2 x = some (truncateHash y) :=
  Iff.rfl

theorem tgtDigestN_of_owner (W : Database HashDomain HashOutput) (m : SelMemN n)
    {x : HashDomain} {i : Fin n} (h : ownerOf P prefixOf x = some i) :
    tgtDigestN hon P W m x = tgtDigest (hon i) W (m i) x := by
  rw [tgtDigestN, h, Option.bind_some]

theorem tgtDigestN_of_owner_none (W : Database HashDomain HashOutput) (m : SelMemN n)
    {x : HashDomain} (h : ownerOf P prefixOf x = none) : tgtDigestN hon P W m x = none := by
  rw [tgtDigestN, h, Option.bind_none]

/-- A target comes from the input's owner. -/
theorem exists_owner_of_tgtDigestN {W : Database HashDomain HashOutput} {m : SelMemN n}
    {x : HashDomain} {d : Digest} (h : tgtDigestN hon P W m x = some d) :
    ∃ i, ownerOf P prefixOf x = some i ∧ tgtDigest (hon i) W (m i) x = some d := by
  cases ho : ownerOf P prefixOf x with
  | none => rw [tgtDigestN_of_owner_none W m ho] at h; cases h
  | some i => exact ⟨i, rfl, (tgtDigestN_of_owner W m ho).symm.trans h⟩

/-- The target of `x` depends on the hardwired cells only through whether `x` is hardwired. -/
theorem tgtDigestN_congr {W W' : Database HashDomain HashOutput} (m : SelMemN n)
    {x : HashDomain} (h : (W x).isSome = (W' x).isSome) :
    tgtDigestN hon P W m x = tgtDigestN hon P W' m x := by
  cases ho : ownerOf P prefixOf x with
  | none => rw [tgtDigestN_of_owner_none W m ho, tgtDigestN_of_owner_none W' m ho]
  | some i =>
    rw [tgtDigestN_of_owner W m ho, tgtDigestN_of_owner W' m ho]
    exact tgtDigest_congr (m i) h

/-- **More hardwired cells, fewer targets.** -/
theorem tgtDigestN_anti {W W' : Database HashDomain HashOutput} (m : SelMemN n)
    {x : HashDomain} (h : (W x).isSome → (W' x).isSome) {d : Digest}
    (hd : tgtDigestN hon P W' m x = some d) : tgtDigestN hon P W m x = some d := by
  obtain ⟨i, ho, hi⟩ := exists_owner_of_tgtDigestN hd
  rw [tgtDigestN_of_owner W m ho]
  exact tgtDigest_anti (m i) h hi

/-! ## The graded-bound hypotheses -/

/-- **Every slice of the event is upward closed.** -/
theorem upClosed_slice_badQN (W : Hw HashOutput HashDomain) (m : SelMemN n) :
    UpClosed (slice (BadQN hon P) W m) :=
  upClosed_slice_cellTargetBad W m

/-- **The start is outside the event** when no hardwired cell has a target. -/
theorem not_mem_badQN_start (W₀ : Hw HashOutput HashDomain) (m₀ : SelMemN n)
    (h : ∀ x, (W₀.1 x).isSome → tgtDigestN hon P W₀.1 m₀ x = none) :
    (((Database.empty, Database.empty, Database.empty), W₀, m₀) :
      RomReg HashDomain HashOutput (SelMemN n)) ∉ BadQN hon P :=
  not_mem_cellTargetBad_start W₀ m₀ fun x y hxy hy ↦ by
    have h0 := h x (by rw [hxy]; rfl)
    rw [mem_xmssTgtQN, h0] at hy
    cases hy

/-- The start without hardwired cells is outside the event. -/
theorem empty_not_mem_badQN (m₀ : SelMemN n) :
    (((Database.empty, Database.empty, Database.empty),
      (Database.empty, Database.empty, Database.empty), m₀) :
      RomReg HashDomain HashOutput (SelMemN n)) ∉ BadQN hon P :=
  not_mem_badQN_start _ m₀ fun _ h ↦ absurd h (by simp [Database.empty])

open scoped Classical in
/-- The targets of an input are at most one digest's preimages. -/
theorem card_xmssTgtQN_le (W : Hw HashOutput HashDomain) (m : SelMemN n) (x : HashDomain) :
    (Finset.univ.filter fun y ↦ y ∈ xmssTgtQN hon P W m x).card ≤ 2 ^ 128 := by
  cases hd : tgtDigestN hon P W.1 m x with
  | none =>
    rw [Finset.filter_false_of_mem fun y _ hy ↦ by rw [mem_xmssTgtQN, hd] at hy; cases hy]
    simp
  | some d =>
    refine le_trans (Finset.card_le_card fun y hy ↦ ?_) (card_fiber_truncateHash_le d)
    have hy : y ∈ xmssTgtQN hon P W m x := (Finset.mem_filter.1 hy).2
    rw [mem_xmssTgtQN, hd] at hy
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Option.some.inj hy).symm⟩

/-- **The fresh bound of every slice**: a fresh cell enters the event with probability at most
`2^-128`, a fresh `k`, `k'` cell never. -/
theorem freshBound_slice_badQN (W : Hw HashOutput HashDomain) (m : SelMemN n) (t : ℕ) :
    FreshBound (slice (BadQN hon P) W m) t (2 ^ 128)⁻¹ := by
  classical
  refine freshBound_slice_cellTargetBad W m (fun x _ ↦ ?_) t
  rw [← fiber_div_card_hashOutput]
  exact ENNReal.div_le_div_right (by exact_mod_cast card_xmssTgtQN_le W m x) _

/-! ## Program ports -/

/-- A cell without a target once hardwired, whatever the other cells and the memory. -/
def ExemptCellN (hon : Fin n → HonestCells) (P : Fin n → PublicParameter) (z : HashDomain) :
    Prop :=
  ∀ (W : Database HashDomain HashOutput) (m : SelMemN n), (W z).isSome →
    tgtDigestN hon P W m z = none

/-- **A cell exempt for its owner is exempt**, for instance an honest cell of its owner. -/
theorem exemptCellN_of_owner {z : HashDomain} {i : Fin n} (ho : ownerOf P prefixOf z = some i)
    (hz : ExemptCell (hon i) z) : ExemptCellN hon P z :=
  fun W m hW ↦ (tgtDigestN_of_owner W m ho).trans (hz W (m i) hW)

/-- A cell without owner is exempt. -/
theorem exemptCellN_of_owner_none {z : HashDomain} (ho : ownerOf P prefixOf z = none) :
    ExemptCellN hon P z :=
  fun W m _ ↦ tgtDigestN_of_owner_none W m ho

/-- An exempt cell has no target once hardwired. -/
theorem ExemptCellN.tgtDigestN_update {z : HashDomain} (hz : ExemptCellN hon P z)
    (W : Database HashDomain HashOutput) (m : SelMemN n) (v : HashOutput) :
    tgtDigestN hon P (Function.update W z (some v)) m z = none :=
  hz _ _ (by rw [Function.update_self]; rfl)

/-- Hardwiring `z` leaves the targets of the other cells. -/
theorem tgtDigestN_update_of_ne (W : Database HashDomain HashOutput) (m : SelMemN n)
    {z x : HashDomain} (hx : x ≠ z) (o : Option HashOutput) :
    tgtDigestN hon P (Function.update W z o) m x = tgtDigestN hon P W m x :=
  tgtDigestN_congr m (by rw [Function.update_of_ne hx])

/-- **Programming an exempt cell flips nothing.** -/
theorem not_mem_badQN_programH {s : RomReg HashDomain HashOutput (SelMemN n)}
    (hs : s ∉ BadQN hon P) {z : HashDomain} (hz : ExemptCellN hon P z) (v : HashOutput) :
    progMap (.programH z v) s ∉ BadQN hon P :=
  not_mem_cellTargetBad_programH hs z v
    (fun _ hx _ hy ↦ (tgtDigestN_update_of_ne s.2.1.1 s.2.2 hx (some v)).symm.trans hy)
    (fun hv ↦ Option.some_ne_none _ ((hz.tgtDigestN_update s.2.1.1 s.2.2 v).symm.trans hv).symm)

/-- **Programming cost zero**: hardwiring an exempt cell costs nothing. -/
theorem flipCost_programH_badQN_eq_zero {z : HashDomain} (hz : ExemptCellN hon P z)
    (v : HashOutput)
    {σ : Matrix (Unit × RomReg HashDomain HashOutput (SelMemN n))
      (Unit × RomReg HashDomain HashOutput (SelMemN n)) ℂ} (hσ : σ.PosSemidef) :
    flipCost (BadQN hon P) (hwProgKraus (.programH z v)) 0 σ = 0 :=
  flipCost_programH_cellTargetBad_eq_zero z v hσ fun q _ _ ↦
    ⟨fun _ hx _ hy ↦ (tgtDigestN_update_of_ne q.2.2.1.1 q.2.2.2 hx (some v)).symm.trans hy,
      fun hv ↦ Option.some_ne_none _
        ((hz.tgtDigestN_update q.2.2.1.1 q.2.2.2 v).symm.trans hv).symm⟩

/-! ## Read ports -/

/-- **A trial read of user `i`**: the read of the cell `z`, owned by `i`, of a message-digest
trial of `i`'s unselected key `(l, e)`, neither hardwired nor recorded. -/
structure SelectReadN (P : Fin n → PublicParameter) (s : RomReg HashDomain HashOutput (SelMemN n))
    (z : HashDomain) (i : Fin n) (l : Layer) (e : KeyIndex) : Prop where
  hw : s.2.1.1 z = none
  hd : s.1.1 z = none
  hm : s.2.2 i l e = none
  slot : slotOf z = some (.msg l e)
  owner : ownerOf P prefixOf z = some i

/-- **The memory after a trial read of user `i`**: user `i`'s selection if the digest is a
codeword. -/
def cwSelN (m : SelMemN n) (i : Fin n) (l : Layer) (e : KeyIndex) (z : HashDomain)
    (v : HashOutput) : SelMemN n :=
  Function.update m i (cwSel (m i) l e z v)

/-- **The memory update of a trial read of user `i`**: user `i`'s single-user update. -/
def cwUpdN (i : Fin n) (l : Layer) (e : KeyIndex) (z : HashDomain) (m : SelMemN n)
    (o : Option HashOutput) : SelMemN n :=
  Function.update m i (cwUpd l e z (m i) o)

theorem cwUpdN_some (i : Fin n) (l : Layer) (e : KeyIndex) (z : HashDomain) (m : SelMemN n)
    (v : HashOutput) : cwUpdN i l e z m (some v) = m ∨ cwUpdN i l e z m (some v) =
      cwSelN m i l e z v := by
  rcases cwUpd_some l e z (m i) v with h | h
  · left
    rw [cwUpdN, h, Function.update_eq_self]
  · right
    rw [cwUpdN, h, cwSelN]

theorem cwUpdN_some_of_none (i : Fin n) (l : Layer) (e : KeyIndex) (z : HashDomain)
    {m : SelMemN n} (hm : m i l e = none) (v : HashOutput) :
    cwUpdN i l e z m (some v) = cwSelN m i l e z v := by
  rw [cwUpdN, cwUpd_some_of_none l e z hm, cwSelN]

theorem cwUpdN_none (i : Fin n) (l : Layer) (e : KeyIndex) (z : HashDomain) (m : SelMemN n) :
    cwUpdN i l e z m none = m :=
  Function.update_eq_self i m

/-- A trial of an unselected key leaves it unselected exactly when its digest is no codeword. -/
theorem cwSelN_eq_none_iff {m : SelMemN n} {i : Fin n} {l : Layer} {e : KeyIndex}
    (hm : m i l e = none) (z : HashDomain) (v : HashOutput) :
    cwSelN m i l e z v i l e = none ↔ ¬ Codeword.Valid (truncateHash v) := by
  rw [cwSelN, Function.update_self]
  exact cwSel_eq_none_iff hm z v

/-- A trial read keeps or grows every target. -/
theorem tgtDigestN_cwSelN_mono {W : Database HashDomain HashOutput} {m : SelMemN n} {i : Fin n}
    {l : Layer} {e : KeyIndex} (hm : m i l e = none) (z : HashDomain) (v : HashOutput)
    {x : HashDomain} {d : Digest} (h : tgtDigestN hon P W m x = some d) :
    tgtDigestN hon P W (cwSelN m i l e z v) x = some d := by
  obtain ⟨j, ho, hj⟩ := exists_owner_of_tgtDigestN h
  rw [tgtDigestN_of_owner W _ ho, cwSelN]
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self]
    exact tgtDigest_cwSel_mono hm z v hj
  · rw [Function.update_of_ne hji]
    exact hj

/-- After a trial read the read cell has no target. -/
theorem tgtDigestN_cwSelN_self (W : Database HashDomain HashOutput) {m : SelMemN n}
    {z : HashDomain} {i : Fin n} {l : Layer} {e : KeyIndex} (hz : slotOf z = some (.msg l e))
    (ho : ownerOf P prefixOf z = some i) (hm : m i l e = none) (v : HashOutput) :
    tgtDigestN hon P W (cwSelN m i l e z v) z = none := by
  rw [tgtDigestN_of_owner W _ ho, cwSelN, Function.update_self]
  exact tgtDigest_cwSel_self W hz hm v

/-- A trial read of user `i` adds, for a codeword digest, the digest as the target of the other
cells of `i` at its message slot, and nothing else. -/
theorem tgtDigestN_cwSelN {W : Database HashDomain HashOutput} {m : SelMemN n} {i : Fin n}
    {l : Layer} {e : KeyIndex} {z x : HashDomain} {v : HashOutput} {d : Digest}
    (h : tgtDigestN hon P W (cwSelN m i l e z v) x = some d) :
    tgtDigestN hon P W m x = some d ∨ ((ownerOf P prefixOf x = some i ∧
      slotOf x = some (.msg l e)) ∧ Codeword.Valid (truncateHash v) ∧ d = truncateHash v) := by
  obtain ⟨j, ho, hj⟩ := exists_owner_of_tgtDigestN h
  rw [tgtDigestN_of_owner W _ ho]
  by_cases hji : j = i
  · subst hji
    rw [cwSelN, Function.update_self] at hj
    rcases tgtDigest_cwSel hj with h' | ⟨h1, h2, h3⟩
    · exact .inl h'
    · exact .inr ⟨⟨ho, h1⟩, h2, h3⟩
  · rw [cwSelN, Function.update_of_ne hji] at hj
    exact .inl hj

/-- **A read that keeps the memory flips nothing**: the trial's cell is at the message slot of an
unselected key of its owner, so it has no target. -/
theorem not_mem_badQN_read_keep {s : RomReg HashDomain HashOutput (SelMemN n)}
    (hs : s ∉ BadQN hon P) {z : HashDomain} {i : Fin n} {l : Layer} {e : KeyIndex}
    (hr : SelectReadN P s z i l e) (u : Option HashOutput) :
    ((Function.update s.1.1 z u, s.1.2), s.2.1, s.2.2) ∉ BadQN hon P :=
  not_mem_cellTargetBad_readH hs s.2.2
    (Set.eq_empty_iff_forall_notMem.2 fun y hy ↦ by
      rw [mem_xmssTgtQN, tgtDigestN_of_owner _ _ hr.owner,
        tgtDigest_msg_none _ hr.slot hr.hm] at hy
      cases hy)
    (fun _ _ _ h ↦ h) u

/-- Counts grow with the cell and value predicates. -/
theorem cellOutCount_mono {D Y : Type} [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y]
    (U : D → Option Y) (P P' : D → Prop) (Qo Qo' : Y → Prop) (hP : ∀ x, P x → P' x)
    (hQ : ∀ y, Qo y → Qo' y) : cellOutCount U P Qo ≤ cellOutCount U P' Qo' := by
  classical
  unfold cellOutCount
  refine Finset.card_le_card fun x hx ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨hx, y, hy, hq⟩ := hx
  exact ⟨hP x hx, y, hy, hQ y hq⟩

/-- The recorded or hardwired cells of a union view owned by user `i` at the message slot of key
`(l, e)` whose value truncates to a codeword. -/
noncomputable def msgCwCountN (P : Fin n → PublicParameter) (U : HashDomain → Option HashOutput)
    (i : Fin n) (l : Layer) (e : KeyIndex) : ℕ :=
  cellOutCount U (fun x ↦ ownerOf P prefixOf x = some i ∧ slotOf x = some (.msg l e))
    fun y ↦ Codeword.Valid (truncateHash y)

/-- A user's codeword count is at most the single-user count of its key. -/
theorem msgCwCountN_le (P : Fin n → PublicParameter) (U : HashDomain → Option HashOutput)
    (i : Fin n) (l : Layer) (e : KeyIndex) : msgCwCountN P U i l e ≤ msgCwCount U l e := by
  -- Named arguments: unifying the generic count with this one would unfold `Finset.univ`.
  exact cellOutCount_mono (D := HashDomain) (Y := HashOutput) U
    (fun x ↦ ownerOf P prefixOf x = some i ∧ slotOf x = some (.msg l e))
    (fun x ↦ slotOf x = some (.msg l e)) (fun y ↦ Codeword.Valid (truncateHash y))
    (fun y ↦ Codeword.Valid (truncateHash y)) (fun _ h ↦ h.2) fun _ h ↦ h

/-- **All users' keys share the message-slot cells**: each cell has one owner and one slot, so the
codeword counts of all users' keys add up to at most the message-slot cells. -/
theorem sum_msgCwCountN_le (P : Fin n → PublicParameter) (U : HashDomain → Option HashOutput) :
    ∑ k : Fin n × Layer × KeyIndex, msgCwCountN P U k.1 k.2.1 k.2.2 ≤ msgSlotCount U := by
  classical
  have hP : ∀ (k k' : Fin n × Layer × KeyIndex) (x : HashDomain),
      (ownerOf P prefixOf x = some k.1 ∧ slotOf x = some (.msg k.2.1 k.2.2)) →
      (ownerOf P prefixOf x = some k'.1 ∧ slotOf x = some (.msg k'.2.1 k'.2.2)) → k = k' :=
    fun k k' x h h' ↦ by
      have hi := Option.some.inj (h.1.symm.trans h'.1)
      obtain ⟨h1, h2⟩ := Slot.msg.inj (Option.some.inj (h.2.symm.trans h'.2))
      exact Prod.ext hi (Prod.ext h1 h2)
  -- Named arguments: unifying the generic sum with this one would unfold `Finset.univ`.
  have h := sum_cellOutCount_le (κ := Fin n × Layer × KeyIndex) (D := HashDomain)
    (Y := HashOutput) U
    (fun k x ↦ ownerOf P prefixOf x = some k.1 ∧ slotOf x = some (.msg k.2.1 k.2.2)) hP
    fun y ↦ Codeword.Valid (truncateHash y)
  refine h.trans ?_
  exact cellOutCount_mono (D := HashDomain) (Y := HashOutput) U _
    (fun x ↦ ∃ k : Layer × KeyIndex, slotOf x = some (.msg k.1 k.2)) _ (fun _ ↦ True)
    (fun _ hx ↦ by obtain ⟨k, -, hk⟩ := hx; exact ⟨k.2, hk⟩) fun _ h ↦ h

/-- **`card_flip_readCwN_le`**: a trial read of key `(l, e)` of user `i` flips a state outside
`BadQN` for at most `msgCwCountN * 2^128` values of the read cell, whatever the read leaves in the
cell: the flips are the codeword outputs of the other cells of `i` at `msg l e`. -/
theorem card_flip_readCwN_le {s : RomReg HashDomain HashOutput (SelMemN n)}
    (hs : s ∉ BadQN hon P) {z : HashDomain} {i : Fin n} {l : Layer} {e : KeyIndex}
    (hr : SelectReadN P s z i l e) :
    (Finset.univ.filter fun v : HashOutput ↦ ∃ u : Option HashOutput,
      ((Function.update s.1.1 z u, s.1.2), s.2.1, cwSelN s.2.2 i l e z v) ∈ BadQN hon P).card ≤
        msgCwCountN P (unionH s) i l e * 2 ^ 128 :=
  card_flip_readH_out_le (D := HashDomain) (Y := HashOutput) (M := SelMemN n) truncateHash
    card_fiber_truncateHash_le hs
    (fun x ↦ ownerOf P prefixOf x = some i ∧ slotOf x = some (.msg l e))
    (fun d ↦ Codeword.Valid d) (fun v ↦ cwSelN s.2.2 i l e z v)
    (fun v ↦ Set.eq_empty_iff_forall_notMem.2 fun _ hy ↦ Option.some_ne_none _
      ((tgtDigestN_cwSelN_self s.2.1.1 hr.slot hr.owner hr.hm v).symm.trans hy).symm)
    (fun _ _ _ _ hy ↦ (tgtDigestN_cwSelN hy).imp id fun h ↦ ⟨h.1, h.2.1, h.2.2⟩)

open scoped Classical in
/-- **The flip cost of a codeword-selecting read of user `i`**: for a memory update that keeps the
memory or records `i`'s selection only for a codeword digest (`cwUpdN`),
`E = ∑_{SelectReadN, ∉ BadQN} msgCwCountN · 2^128 / |Y| · σ_ss`. -/
theorem flipCost_selectReadCwN_le (z : HashDomain) (i : Fin n) (l : Layer) (e : KeyIndex)
    (upd : SelMemN n → Option HashOutput → SelMemN n)
    (hupd : ∀ m v, upd m (some v) = m ∨ upd m (some v) = cwSelN m i l e z v)
    {σ : Matrix (Unit × RomReg HashDomain HashOutput (SelMemN n))
      (Unit × RomReg HashDomain HashOutput (SelMemN n)) ℂ} (hσ : σ.PosSemidef) :
    flipCost (BadQN hon P) (hwReadKraus (.readH z upd))
        (readPs fun s ↦ SelectReadN P s z i l e) σ ≤
      ENNReal.ofReal (∑ q, if SelectReadN P q.2 z i l e ∧ q.2 ∉ BadQN hon P then
          ((msgCwCountN P (unionH q.2) i l e * 2 ^ 128 : ℕ) : ℝ) / Fintype.card HashOutput *
            (σ q q).re else 0) +
        ENNReal.ofReal ((readPs fun s ↦ SelectReadN P s z i l e) * σ).trace.re +
      2 * (ENNReal.ofReal (∑ q, if SelectReadN P q.2 z i l e ∧ q.2 ∉ BadQN hon P then
          ((msgCwCountN P (unionH q.2) i l e * 2 ^ 128 : ℕ) : ℝ) / Fintype.card HashOutput *
            (σ q q).re else 0) *
        ENNReal.ofReal ((readPs fun s ↦ SelectReadN P s z i l e) * σ).trace.re) ^ (2⁻¹ : ℝ) := by
  refine flipCost_readH_le (BadQN hon P) z upd (fun m v ↦ cwSelN m i l e z v)
    (fun s ↦ SelectReadN P s z i l e) (fun s ↦ msgCwCountN P (unionH s) i l e * 2 ^ 128) ?_ hupd
    ?_ ?_ ?_ ?_ hσ
  · exact fun _ hs ↦ ⟨hs.hd, hs.hw⟩
  · exact fun _ u hs hS ↦ not_mem_badQN_read_keep hS hs u
  · intro s hs hS
    convert card_flip_readCwN_le hS hs using 3
  · exact fun s u hs hS ↦ mem_cellTargetBad_fill hS hs.hd u s.2.2 fun _ _ ht ↦ ht
  · exact fun s u v hs hS ↦ mem_cellTargetBad_fill hS hs.hd u _ fun _ _ ht ↦
      tgtDigestN_cwSelN_mono hs.hm z v ht

open scoped Classical in
/-- **The selecting-read term** of `flipCost_selectReadCwN_le`: if `msgCwCountN ≤ C` on the
selection reads of the support outside `BadQN`, then `E ≤ C 2^-128 e`, with `e` the weight of the
selection reads. -/
theorem selectReadCwNE_le (z : HashDomain) (i : Fin n) (l : Layer) (e : KeyIndex) (C : ℕ)
    {σ : Matrix (Unit × RomReg HashDomain HashOutput (SelMemN n))
      (Unit × RomReg HashDomain HashOutput (SelMemN n)) ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ q, SelectReadN P q.2 z i l e → q.2 ∉ BadQN hon P → σ q q ≠ 0 →
      msgCwCountN P (unionH q.2) i l e ≤ C) :
    (∑ q, if SelectReadN P q.2 z i l e ∧ q.2 ∉ BadQN hon P then
        ((msgCwCountN P (unionH q.2) i l e * 2 ^ 128 : ℕ) : ℝ) / Fintype.card HashOutput *
          (σ q q).re else 0) ≤
      C * (2 ^ 128)⁻¹ * ∑ q, if SelectReadN P q.2 z i l e then (σ q q).re else 0 := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hC0 : (0 : ℝ) ≤ C * (2 ^ 128)⁻¹ := by positivity
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases hq : SelectReadN P q.2 z i l e
  · rw [ite_eq_left hq]
    by_cases hb : q.2 ∉ BadQN hon P
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

/-- The memories whose key `(l, e)` of user `i` has no selection. -/
def unselMemN (i : Fin n) (l : Layer) (e : KeyIndex) : Set (SelMemN n) := {m | m i l e = none}

instance instDecidablePredUnselMemN (i : Fin n) (l : Layer) (e : KeyIndex) :
    DecidablePred (· ∈ unselMemN i l e) :=
  fun m ↦ inferInstanceAs (Decidable (m i l e = none))

open scoped Classical in
/-- **Survival of a trial read of user `i`**: the outcomes of a trial of `i`'s unselected key
`(l, e)` that leave it unselected weigh at most `w - ρ_c e + p + 2 √(ρ_c e p)`, as for one user. -/
theorem survive_selectReadN_le (z : HashDomain) (i : Fin n) (l : Layer) (e : KeyIndex)
    (upd : SelMemN n → Option HashOutput → SelMemN n)
    (hupd : ∀ m v, m i l e = none → upd m (some v) = cwSelN m i l e z v)
    (SR : RomReg HashDomain HashOutput (SelMemN n) → Prop) [DecidablePred SR]
    (hSR : ∀ s, SR s → s.1.1 z = none ∧ s.2.1.1 z = none ∧ s.2.2 ∈ unselMemN i l e)
    {σ : Matrix (Unit × RomReg HashDomain HashOutput (SelMemN n))
      (Unit × RomReg HashDomain HashOutput (SelMemN n)) ℂ} (hσ : σ.PosSemidef) :
    (∑ r : Option HashOutput × SelMemN n, if upd r.2 r.1 ∈ unselMemN i l e then
        (MatrixMap.conj (hwReadKraus (.readH z upd) r) σ).trace.re else 0) ≤
      (∑ q, if q.2.2.2 ∈ unselMemN i l e then (σ q q).re else 0) -
        Quantum.Xmss.rhoCw * (∑ q, if SR q.2 then (σ q q).re else 0) +
        (readPs SR * σ).trace.re +
        2 * √(Quantum.Xmss.rhoCw * (∑ q, if SR q.2 then (σ q q).re else 0) *
          (readPs SR * σ).trace.re) :=
  survive_readH_le z upd (unselMemN i l e) (fun v ↦ Codeword.Valid (truncateHash v))
    card_codeword_div_card_hashOutput
    (fun m hm v ↦ by
      show upd m (some v) i l e = none ↔ _
      rw [hupd m v hm]
      exact cwSelN_eq_none_iff hm z v) SR hSR hσ

end Quantum.Qrom.Xmss.Multi

end
