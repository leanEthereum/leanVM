module

public import Quantum.Qrom.Sphincs.Events
public import Quantum.Qrom.Sphincs.Multi.Table

@[expose] public section

/-!
# The leanSPHINCS event of the random oracle for `n` users

The memory of the hardwired register holds one single-user memory per user (`SelMemN n`). The
users' public keys `pk` determine the owner of an input (`ownerS pk`): the user whose `PK.seed` is
the input's `PK.seed` field (`prefixS`). Each input has at most one owner, hence at most one target
digest, its owner's single-user target (`tgtDigestN`), and a call-0 `H_msg` cell is a Cov target
of its owner's disclosures (`covTgtN`). The event `BadQN pk hon S` is `CellTargetBad` of the union
of both targets (`sphTgtQN`):

* `upClosed_slice_badQN`, `not_mem_badQN_start`, `freshBound_slice_badQN`: the graded-bound
  hypotheses, with fresh fraction `epsQN S = 2^-128 + ⨆ i, price (S i)` per cell.
* **Program ports**: hardwiring a cell exempt for its owner (`ExemptCellN`), or of no owner,
  costs nothing (`flipCost_programH_badQN_eq_zero`).
* **Read ports**: a trial read of key `K` of user `i` (`SelectReadN`, the read cell owned by `i`)
  that records the selection only for a codeword digest (`cwSelN`, `cwUpdN`) flips at most
  `encCwCountN * 2^384` pairs (`card_flip_readCwN_le`); flip cost (`flipCost_selectReadCwN_le`,
  `selectReadCwNE_le`) and survival (`survive_selectReadN_le`) as for one user.
* A cell at a slot of user `i` carrying `PK.seed` (`PrefixedSlot`) is owned by `i` when the
  `PK.seed`s are distinct (`ownerS_of_slotOf`).
-/

open Matrix
open scoped ENNReal ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (Slot Key Disclosures Covered price)

namespace Quantum.Qrom.Sphincs.Multi

open Quantum Quantum.Sponge
open Quantum.Qrom.MultiUser (ownerOf ownerOf_eq_some prefix_of_ownerOf)

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

variable {n : ℕ}

/-! ## Owners of cells -/

/-- **The owner of an input**: the user whose `PK.seed` is the input's `PK.seed` field. -/
def ownerS (pk : Fin n → PublicKey) (x : Qrom.HashDomain) : Option (Fin n) :=
  ownerOf (fun i ↦ (pk i).publicSeed) prefixS x

theorem prefixS_of_ownerS {pk : Fin n → PublicKey} {x : Qrom.HashDomain} {i : Fin n}
    (h : ownerS pk x = some i) : prefixS x = some (pk i).publicSeed :=
  prefix_of_ownerOf h

/-- With distinct `PK.seed`s, the owner of an input with `PK.seed` field `(pk i).publicSeed` is
`i`. -/
theorem ownerS_eq_some {pk : Fin n → PublicKey} (hP : Function.Injective fun i ↦ (pk i).publicSeed)
    {x : Qrom.HashDomain} {i : Fin n} (h : prefixS x = some (pk i).publicSeed) :
    ownerS pk x = some i :=
  ownerOf_eq_some hP h

/-- **A cell at a `PK.seed`-carrying slot of user `i` is owned by `i`** when the `PK.seed`s are
distinct. -/
theorem ownerS_of_slotOf {pk : Fin n → PublicKey}
    (hP : Function.Injective fun i ↦ (pk i).publicSeed) {x : Qrom.HashDomain} {i : Fin n}
    {s : Slot} (h : slotOf (pk i) x = some s) (hs : PrefixedSlot s) : ownerS pk x = some i :=
  ownerS_eq_some hP (prefixS_of_slotOf h hs)

/-! ## The memory -/

/-- **The memory of `n` users**: one single-user selection memory per user. -/
abbrev SelMemN (n : ℕ) : Type := Fin n → SelMem

instance instFintypeSelMemN : Fintype (SelMemN n) := by
  unfold SelMemN
  infer_instance

instance instDecidableEqSelMemN : DecidableEq (SelMemN n) := by
  unfold SelMemN
  infer_instance

/-! ## Targets -/

/-- **The target digest of an input for `n` users**: its owner's single-user target. -/
def tgtDigestN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells)
    (W : Database Qrom.HashDomain PairOut) (m : SelMemN n) (x : Qrom.HashDomain) :
    Option Digest :=
  (ownerS pk x).bind fun i ↦ tgtDigest (pk i) (hon i) W (m i) x

/-- **The Cov targets for `n` users**: a call-0 `H_msg` cell that is not hardwired is hit when its
pair is covered by its owner's disclosures. -/
def covTgtN (pk : Fin n → PublicKey) (S : Fin n → Disclosures) (W : Hw PairOut Qrom.HashDomain)
    (_m : SelMemN n) (x : Qrom.HashDomain) : Set PairOut :=
  {ω | hmsgCall x = some 0 ∧ W.1 x = none ∧ ∃ i, ownerS pk x = some i ∧ Covered (S i) (pairView ω)}

/-- **The leanSPHINCS targets for `n` users**: the owner's Struct and Enc targets and the owner's
Cov targets. -/
def sphTgtQN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells) (S : Fin n → Disclosures)
    (W : Hw PairOut Qrom.HashDomain) (m : SelMemN n) (x : Qrom.HashDomain) : Set PairOut :=
  {ω | tgtDigestN pk hon W.1 m x = some (pairDigest ω) ∨ ω ∈ covTgtN pk S W m x}

/-- **The leanSPHINCS event of the random oracle for `n` users**: a recorded or hardwired cell
whose pair is in its owner's Struct, Enc or Cov target. -/
abbrev BadQN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells) (S : Fin n → Disclosures) :
    Set (RomReg Qrom.HashDomain PairOut (SelMemN n)) :=
  CellTargetBad (sphTgtQN pk hon S)

/-- **The fresh fraction**: `2^-128` plus the worst user's price. -/
noncomputable def epsQN (S : Fin n → Disclosures) : ℝ≥0∞ :=
  (2 ^ 128 : ℝ≥0∞)⁻¹ + ⨆ i, ENNReal.ofReal (price (S i))

variable {pk : Fin n → PublicKey} {hon : Fin n → HonestCells} {S : Fin n → Disclosures}

theorem mem_covTgtN {W : Hw PairOut Qrom.HashDomain} {m : SelMemN n} {x : Qrom.HashDomain}
    {ω : PairOut} :
    ω ∈ covTgtN pk S W m x ↔ hmsgCall x = some 0 ∧ W.1 x = none ∧
      ∃ i, ownerS pk x = some i ∧ Covered (S i) (pairView ω) :=
  Iff.rfl

theorem mem_sphTgtQN {W : Hw PairOut Qrom.HashDomain} {m : SelMemN n} {x : Qrom.HashDomain}
    {ω : PairOut} :
    ω ∈ sphTgtQN pk hon S W m x ↔
      tgtDigestN pk hon W.1 m x = some (pairDigest ω) ∨ ω ∈ covTgtN pk S W m x :=
  Iff.rfl

theorem mem_badQN_iff {s : RomReg Qrom.HashDomain PairOut (SelMemN n)} :
    s ∈ BadQN pk hon S ↔ ∃ x ω, unionH s x = some ω ∧
      (tgtDigestN pk hon s.2.1.1 s.2.2 x = some (pairDigest ω) ∨
        ω ∈ covTgtN pk S s.2.1 s.2.2 x) :=
  Iff.rfl

/-- The Cov targets do not read the memory. -/
theorem mem_covTgtN_memory {W : Hw PairOut Qrom.HashDomain} {m m' : SelMemN n}
    {x : Qrom.HashDomain} {ω : PairOut} (h : ω ∈ covTgtN pk S W m x) : ω ∈ covTgtN pk S W m' x :=
  h

/-- **A Cov hit**: a recorded call-0 `H_msg` cell of user `i`, not hardwired, whose pair is
covered by `S i`. -/
theorem mem_badQN_of_cov {s : RomReg Qrom.HashDomain PairOut (SelMemN n)} {x : Qrom.HashDomain}
    {ω : PairOut} {i : Fin n} (hx : unionH s x = some ω) (h0 : hmsgCall x = some 0)
    (hw : s.2.1.1 x = none) (ho : ownerS pk x = some i) (hc : Covered (S i) (pairView ω)) :
    s ∈ BadQN pk hon S :=
  ⟨x, ω, hx, .inr ⟨h0, hw, i, ho, hc⟩⟩

theorem tgtDigestN_of_owner (W : Database Qrom.HashDomain PairOut) (m : SelMemN n)
    {x : Qrom.HashDomain} {i : Fin n} (h : ownerS pk x = some i) :
    tgtDigestN pk hon W m x = tgtDigest (pk i) (hon i) W (m i) x := by
  rw [tgtDigestN, h, Option.bind_some]

theorem tgtDigestN_of_owner_none (W : Database Qrom.HashDomain PairOut) (m : SelMemN n)
    {x : Qrom.HashDomain} (h : ownerS pk x = none) : tgtDigestN pk hon W m x = none := by
  rw [tgtDigestN, h, Option.bind_none]

/-- A target comes from the input's owner. -/
theorem exists_owner_of_tgtDigestN {W : Database Qrom.HashDomain PairOut} {m : SelMemN n}
    {x : Qrom.HashDomain} {d : Digest} (h : tgtDigestN pk hon W m x = some d) :
    ∃ i, ownerS pk x = some i ∧ tgtDigest (pk i) (hon i) W (m i) x = some d := by
  cases ho : ownerS pk x with
  | none => rw [tgtDigestN_of_owner_none W m ho] at h; cases h
  | some i => exact ⟨i, rfl, (tgtDigestN_of_owner W m ho).symm.trans h⟩

/-- An input without owner has no Cov target. -/
theorem not_mem_covTgtN_of_owner_none {W : Hw PairOut Qrom.HashDomain} {m : SelMemN n}
    {x : Qrom.HashDomain} (h : ownerS pk x = none) (ω : PairOut) : ω ∉ covTgtN pk S W m x :=
  fun hω ↦ by
    obtain ⟨-, -, i, hi, -⟩ := hω
    rw [h] at hi
    cases hi

/-- The Cov targets of an input of user `i` are `i`'s single-user Cov targets. -/
theorem mem_covTgt_of_mem_covTgtN {W : Hw PairOut Qrom.HashDomain} {m : SelMemN n}
    {x : Qrom.HashDomain} {i : Fin n} (ho : ownerS pk x = some i) {ω : PairOut}
    (h : ω ∈ covTgtN pk S W m x) : ω ∈ covTgt (S i) W (m i) x := by
  obtain ⟨h0, hw, j, hj, hc⟩ := h
  rw [ho, Option.some.injEq] at hj
  subst hj
  exact ⟨h0, hw, hc⟩

/-- The target of `x` depends on the hardwired cells only through whether `x` is hardwired. -/
theorem tgtDigestN_congr {W W' : Database Qrom.HashDomain PairOut} (m : SelMemN n)
    {x : Qrom.HashDomain} (h : (W x).isSome = (W' x).isSome) :
    tgtDigestN pk hon W m x = tgtDigestN pk hon W' m x := by
  cases ho : ownerS pk x with
  | none => rw [tgtDigestN_of_owner_none W m ho, tgtDigestN_of_owner_none W' m ho]
  | some i =>
    rw [tgtDigestN_of_owner W m ho, tgtDigestN_of_owner W' m ho]
    exact tgtDigest_congr (m i) h

/-- **More hardwired cells, fewer targets.** -/
theorem tgtDigestN_anti {W W' : Database Qrom.HashDomain PairOut} (m : SelMemN n)
    {x : Qrom.HashDomain} (h : (W x).isSome → (W' x).isSome) {d : Digest}
    (hd : tgtDigestN pk hon W' m x = some d) : tgtDigestN pk hon W m x = some d := by
  obtain ⟨i, ho, hi⟩ := exists_owner_of_tgtDigestN hd
  rw [tgtDigestN_of_owner W m ho]
  exact tgtDigest_anti (m i) h hi

/-! ## The graded-bound hypotheses -/

/-- **Every slice of the event is upward closed.** -/
theorem upClosed_slice_badQN (W : Hw PairOut Qrom.HashDomain) (m : SelMemN n) :
    UpClosed (slice (BadQN pk hon S) W m) :=
  upClosed_slice_cellTargetBad W m

/-- **The start is outside the event** when no hardwired cell has a Struct or Enc target (a
hardwired cell has no Cov target). -/
theorem not_mem_badQN_start (W₀ : Hw PairOut Qrom.HashDomain) (m₀ : SelMemN n)
    (h : ∀ x, (W₀.1 x).isSome → tgtDigestN pk hon W₀.1 m₀ x = none) :
    (((Database.empty, Database.empty, Database.empty), W₀, m₀) :
      RomReg Qrom.HashDomain PairOut (SelMemN n)) ∉ BadQN pk hon S :=
  not_mem_cellTargetBad_start W₀ m₀ fun x y hxy hy ↦ by
    rcases hy with hy | hy
    · have h0 := h x (by rw [hxy]; rfl)
      rw [h0] at hy
      cases hy
    · exact Option.some_ne_none y (hxy.symm.trans hy.2.1)

/-- The start without hardwired cells is outside the event. -/
theorem empty_not_mem_badQN (m₀ : SelMemN n) :
    (((Database.empty, Database.empty, Database.empty),
      (Database.empty, Database.empty, Database.empty), m₀) :
      RomReg Qrom.HashDomain PairOut (SelMemN n)) ∉ BadQN pk hon S :=
  not_mem_badQN_start _ m₀ fun _ h ↦ absurd h (by simp [Database.empty])

/-- **The fresh bound of every slice**: a fresh cell of user `i` enters the event with probability
at most `2^-128 + price (S i) ≤ epsQN S` (Struct or Enc, then Cov), a cell without owner never, a
fresh `k`, `k'` cell never. -/
theorem freshBound_slice_badQN (W : Hw PairOut Qrom.HashDomain) (m : SelMemN n) (t : ℕ) :
    FreshBound (slice (BadQN pk hon S) W m) t (epsQN S) := by
  classical
  refine freshBound_slice_cellTargetBad W m (fun x _ ↦ ?_) t
  cases ho : ownerS pk x with
  | none =>
    rw [Finset.filter_false_of_mem fun ω _ hω ↦ by
      rcases hω with h | h
      · rw [tgtDigestN_of_owner_none W.1 m ho] at h
        cases h
      · exact not_mem_covTgtN_of_owner_none ho ω h]
    simp
  | some i =>
    have hsub : (Finset.univ.filter fun ω ↦ ω ∈ sphTgtQN pk hon S W m x) ⊆
        (Finset.univ.filter fun ω ↦ ω ∈ structTgtQ (pk i) (hon i) W (m i) x) ∪
          (Finset.univ.filter fun ω : PairOut ↦ Covered (S i) (pairView ω)) := by
      intro ω hω
      rcases (Finset.mem_filter.1 hω).2 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _,
          (tgtDigestN_of_owner W.1 m ho).symm.trans h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _,
          (mem_covTgt_of_mem_covTgtN ho h).2.2⟩)
    refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2
      ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))) _) ?_
    refine le_trans ?_ (add_le_add_right (le_iSup (fun j ↦ ENNReal.ofReal (price (S j))) i) _)
    rw [Nat.cast_add, ENNReal.add_div, ← covFrac_eq (S i), ← pairFiber_div_card]
    exact add_le_add (ENNReal.div_le_div_right
      (by exact_mod_cast card_structTgtQ_le W (m i) x) _) le_rfl

/-! ## Program ports -/

/-- A cell exempt for its owner (`ExemptCell`): no Struct or Enc target once hardwired. -/
def ExemptCellN (pk : Fin n → PublicKey) (hon : Fin n → HonestCells) (z : Qrom.HashDomain) :
    Prop :=
  ∀ i, ownerS pk z = some i → ExemptCell (pk i) (hon i) z

/-- A cell without owner is exempt. -/
theorem exemptCellN_of_owner_none {z : Qrom.HashDomain} (ho : ownerS pk z = none) :
    ExemptCellN pk hon z :=
  fun i hi ↦ by rw [ho] at hi; cases hi

/-- **A cell exempt for its owner is exempt**, for instance an honest cell of its owner. -/
theorem exemptCellN_of_owner {z : Qrom.HashDomain} {i : Fin n} (ho : ownerS pk z = some i)
    (hz : ExemptCell (pk i) (hon i) z) : ExemptCellN pk hon z :=
  fun j hj ↦ by
    rw [ho, Option.some.injEq] at hj
    exact hj ▸ hz

/-- An exempt cell has no target once hardwired. -/
theorem ExemptCellN.tgtDigestN_eq_none {z : Qrom.HashDomain} (hz : ExemptCellN pk hon z)
    (W : Database Qrom.HashDomain PairOut) (m : SelMemN n) (hW : (W z).isSome) :
    tgtDigestN pk hon W m z = none := by
  cases ho : ownerS pk z with
  | none => exact tgtDigestN_of_owner_none W m ho
  | some i => exact (tgtDigestN_of_owner W m ho).trans (hz i ho W (m i) hW)

/-- Hardwiring `z` leaves the targets of the other cells. -/
theorem tgtDigestN_update_of_ne (W : Database Qrom.HashDomain PairOut) (m : SelMemN n)
    {z x : Qrom.HashDomain} (hx : x ≠ z) (o : Option PairOut) :
    tgtDigestN pk hon (Function.update W z o) m x = tgtDigestN pk hon W m x :=
  tgtDigestN_congr m (by rw [Function.update_of_ne hx])

/-- Programming `z` with `v`: the other targets do not grow and `v` is outside the new target of
an exempt `z`. -/
theorem programH_badQN_conds {W : Hw PairOut Qrom.HashDomain} {m : SelMemN n}
    {z : Qrom.HashDomain} (hz : ExemptCellN pk hon z) (v : PairOut) :
    (∀ x, x ≠ z → ∀ ω ∈ sphTgtQN pk hon S (Function.update W.1 z (some v), W.2) m x,
      ω ∈ sphTgtQN pk hon S W m x) ∧
    v ∉ sphTgtQN pk hon S (Function.update W.1 z (some v), W.2) m z := by
  refine ⟨fun x hx ω hω ↦ ?_, fun hv ↦ ?_⟩
  · rcases hω with h | h
    · exact .inl ((tgtDigestN_update_of_ne W.1 m hx (some v)).symm.trans h)
    · exact .inr ⟨h.1, (Function.update_of_ne hx (some v) W.1).symm.trans h.2.1, h.2.2⟩
  · rcases hv with h | h
    · exact Option.some_ne_none _ (h.symm.trans (hz.tgtDigestN_eq_none _ m
        (by simp only [Function.update_self, Option.isSome_some])))
    · exact Option.some_ne_none v ((Function.update_self z (some v) W.1).symm.trans h.2.1)

/-- **Programming an exempt cell flips nothing.** -/
theorem not_mem_badQN_programH {s : RomReg Qrom.HashDomain PairOut (SelMemN n)}
    (hs : s ∉ BadQN pk hon S) {z : Qrom.HashDomain} (hz : ExemptCellN pk hon z) (v : PairOut) :
    progMap (.programH z v) s ∉ BadQN pk hon S :=
  not_mem_cellTargetBad_programH hs z v (programH_badQN_conds hz v).1
    (programH_badQN_conds hz v).2

/-- **Programming cost zero**: hardwiring a cell exempt for its owner costs nothing. -/
theorem flipCost_programH_badQN_eq_zero {z : Qrom.HashDomain} (hz : ExemptCellN pk hon z)
    (a : PairOut)
    {σ : Matrix (Unit × RomReg Qrom.HashDomain PairOut (SelMemN n))
      (Unit × RomReg Qrom.HashDomain PairOut (SelMemN n)) ℂ} (hσ : σ.PosSemidef) :
    flipCost (BadQN pk hon S) (hwProgKraus (.programH z a)) 0 σ = 0 :=
  flipCost_programH_cellTargetBad_eq_zero z a hσ fun _ _ _ ↦ programH_badQN_conds hz a

/-! ## Read ports -/

/-- **A trial read of user `i`**: the read of the cell `z`, owned by `i`, of an encoding trial of
`i`'s unselected key `K`, neither hardwired nor recorded. -/
structure SelectReadN (pk : Fin n → PublicKey) (s : RomReg Qrom.HashDomain PairOut (SelMemN n))
    (z : Qrom.HashDomain) (i : Fin n) (K : Key) : Prop where
  hw : s.2.1.1 z = none
  hd : s.1.1 z = none
  hm : s.2.2 i K = none
  slot : slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2)
  owner : ownerS pk z = some i

/-- **The memory after a trial read of user `i`**: user `i`'s selection if the digest is a
codeword. -/
def cwSelN (m : SelMemN n) (i : Fin n) (K : Key) (z : Qrom.HashDomain) (ω : PairOut) :
    SelMemN n :=
  Function.update m i (cwSel (m i) K z ω)

/-- **The memory update of a trial read of user `i`**: user `i`'s single-user update. -/
def cwUpdN (i : Fin n) (K : Key) (z : Qrom.HashDomain) (m : SelMemN n) (o : Option PairOut) :
    SelMemN n :=
  Function.update m i (cwUpd K z (m i) o)

theorem cwUpdN_some (i : Fin n) (K : Key) (z : Qrom.HashDomain) (m : SelMemN n) (ω : PairOut) :
    cwUpdN i K z m (some ω) = m ∨ cwUpdN i K z m (some ω) = cwSelN m i K z ω := by
  rcases cwUpd_some K z (m i) ω with h | h
  · left
    rw [cwUpdN, h, Function.update_eq_self]
  · right
    rw [cwUpdN, h, cwSelN]

theorem cwUpdN_some_of_none (i : Fin n) (K : Key) (z : Qrom.HashDomain) {m : SelMemN n}
    (hm : m i K = none) (ω : PairOut) : cwUpdN i K z m (some ω) = cwSelN m i K z ω := by
  rw [cwUpdN, cwUpd_some_of_none K z hm, cwSelN]

theorem cwUpdN_none (i : Fin n) (K : Key) (z : Qrom.HashDomain) (m : SelMemN n) :
    cwUpdN i K z m none = m :=
  Function.update_eq_self i m

/-- A trial of user `i` leaves the other users' memories. -/
theorem cwUpdN_apply_of_ne {i j : Fin n} (K : Key) (z : Qrom.HashDomain) (m : SelMemN n)
    (o : Option PairOut) (h : j ≠ i) : cwUpdN i K z m o j = m j :=
  Function.update_of_ne h _ _

/-- A trial of an unselected key leaves it unselected exactly when its digest is no codeword. -/
theorem cwSelN_eq_none_iff {m : SelMemN n} {i : Fin n} {K : Key} (hm : m i K = none)
    (z : Qrom.HashDomain) (ω : PairOut) :
    cwSelN m i K z ω i K = none ↔ ¬ Quantum.Sphincs.Codeword.Valid (pairDigest ω) := by
  rw [cwSelN, Function.update_self]
  exact cwSel_eq_none_iff hm z ω

/-- A trial read keeps or grows every target. -/
theorem tgtDigestN_cwSelN_mono {W : Database Qrom.HashDomain PairOut} {m : SelMemN n}
    {i : Fin n} {K : Key} (hm : m i K = none) (z : Qrom.HashDomain) (ω : PairOut)
    {x : Qrom.HashDomain} {d : Digest} (h : tgtDigestN pk hon W m x = some d) :
    tgtDigestN pk hon W (cwSelN m i K z ω) x = some d := by
  obtain ⟨j, ho, hj⟩ := exists_owner_of_tgtDigestN h
  rw [tgtDigestN_of_owner W _ ho, cwSelN]
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self]
    exact tgtDigest_cwSel_mono hm z ω hj
  · rw [Function.update_of_ne hji]
    exact hj

/-- After a trial read the read cell has no target. -/
theorem tgtDigestN_cwSelN_self (W : Database Qrom.HashDomain PairOut) {m : SelMemN n}
    {z : Qrom.HashDomain} {i : Fin n} {K : Key}
    (hz : slotOf (pk i) z = some (.enc K.1 K.2.1 K.2.2)) (ho : ownerS pk z = some i)
    (hm : m i K = none) (ω : PairOut) : tgtDigestN pk hon W (cwSelN m i K z ω) z = none := by
  rw [tgtDigestN_of_owner W _ ho, cwSelN, Function.update_self]
  exact tgtDigest_cwSel_self W hz hm ω

/-- A trial read of user `i` adds, for a codeword digest, the digest as the target of the other
cells of `i` at its encoding slot, and nothing else. -/
theorem tgtDigestN_cwSelN {W : Database Qrom.HashDomain PairOut} {m : SelMemN n} {i : Fin n}
    {K : Key} {z x : Qrom.HashDomain} {ω : PairOut} {d : Digest}
    (h : tgtDigestN pk hon W (cwSelN m i K z ω) x = some d) :
    tgtDigestN pk hon W m x = some d ∨ ((ownerS pk x = some i ∧
      slotOf (pk i) x = some (.enc K.1 K.2.1 K.2.2)) ∧
        Quantum.Sphincs.Codeword.Valid (pairDigest ω) ∧ d = pairDigest ω) := by
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

/-- **A read that keeps the memory flips nothing**: the trial's cell is at the encoding slot of an
unselected key of its owner, so it has no target. -/
theorem not_mem_badQN_read_keep {s : RomReg Qrom.HashDomain PairOut (SelMemN n)}
    (hs : s ∉ BadQN pk hon S) {z : Qrom.HashDomain} {i : Fin n} {K : Key}
    (hr : SelectReadN pk s z i K) (u : Option PairOut) :
    ((Function.update s.1.1 z u, s.1.2), s.2.1, s.2.2) ∉ BadQN pk hon S :=
  not_mem_cellTargetBad_readH hs s.2.2
    (Set.eq_empty_iff_forall_notMem.2 fun ω hω ↦ by
      rcases hω with h | h
      · rw [tgtDigestN_of_owner _ _ hr.owner, tgtDigest_enc_none _ hr.slot hr.hm] at h
        cases h
      · exact hmsgCall_ne_zero_of_enc hr.slot h.1)
    (fun _ _ _ h ↦ h) u

/-- The recorded or hardwired cells of a union view owned by user `i` at the encoding slot of
`i`'s key `K` whose pair has a codeword digest. -/
noncomputable def encCwCountN (pk : Fin n → PublicKey) (U : Qrom.HashDomain → Option PairOut)
    (i : Fin n) (K : Key) : ℕ :=
  Quantum.Qrom.Xmss.cellOutCount U
    (fun x ↦ ownerS pk x = some i ∧ slotOf (pk i) x = some (.enc K.1 K.2.1 K.2.2))
    fun ω ↦ Quantum.Sphincs.Codeword.Valid (pairDigest ω)

/-- A user's codeword count is at most the single-user count of its key. -/
theorem encCwCountN_le (pk : Fin n → PublicKey) (U : Qrom.HashDomain → Option PairOut)
    (i : Fin n) (K : Key) : encCwCountN pk U i K ≤ encCwCount (pk i) U K := by
  classical
  unfold encCwCountN encCwCount Quantum.Qrom.Xmss.cellOutCount
  refine Finset.card_le_card fun x hx ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact ⟨hx.1.2, hx.2⟩

/-- **`card_flip_readCwN_le`**: a trial read of key `K` of user `i` flips a state outside `BadQN`
for at most `encCwCountN * 2^384` pairs of the read cell, whatever the read leaves in the cell:
the flips are the codeword digests of the other cells of `i` at `enc K`. -/
theorem card_flip_readCwN_le {s : RomReg Qrom.HashDomain PairOut (SelMemN n)}
    (hs : s ∉ BadQN pk hon S) {z : Qrom.HashDomain} {i : Fin n} {K : Key}
    (hr : SelectReadN pk s z i K) :
    (Finset.univ.filter fun ω : PairOut ↦ ∃ u : Option PairOut,
      ((Function.update s.1.1 z u, s.1.2), s.2.1, cwSelN s.2.2 i K z ω) ∈ BadQN pk hon S).card ≤
        encCwCountN pk (unionH s) i K * (2 ^ 128 * 2 ^ 256) :=
  Quantum.Qrom.Xmss.card_flip_readH_out_le (D := Qrom.HashDomain) (Y := PairOut)
    (M := SelMemN n) pairDigest card_fiber_pairDigest_le hs
    (fun x ↦ ownerS pk x = some i ∧ slotOf (pk i) x = some (.enc K.1 K.2.1 K.2.2))
    (fun d ↦ Quantum.Sphincs.Codeword.Valid d) (fun ω ↦ cwSelN s.2.2 i K z ω)
    (fun ω ↦ Set.eq_empty_iff_forall_notMem.2 fun _ hy ↦ by
      rcases hy with h | h
      · exact Option.some_ne_none _
          ((tgtDigestN_cwSelN_self s.2.1.1 hr.slot hr.owner hr.hm ω).symm.trans h).symm
      · exact hmsgCall_ne_zero_of_enc hr.slot h.1)
    (fun _ _ _ _ hy ↦ by
      rcases hy with h | h
      · exact (tgtDigestN_cwSelN h).imp Or.inl fun h ↦ ⟨h.1, h.2.1, h.2.2⟩
      · exact .inl (.inr (mem_covTgtN_memory h)))

open scoped Classical in
/-- **The flip cost of a codeword-selecting read of user `i`**: for a memory update that keeps the
memory or records `i`'s selection only for a codeword digest (`cwUpdN`),
`E = ∑_{SelectReadN, ∉ BadQN} encCwCountN · 2^384 / |Y × Y| · σ_ss`. -/
theorem flipCost_selectReadCwN_le (z : Qrom.HashDomain) (i : Fin n) (K : Key)
    (upd : SelMemN n → Option PairOut → SelMemN n)
    (hupd : ∀ m ω, upd m (some ω) = m ∨ upd m (some ω) = cwSelN m i K z ω)
    {σ : Matrix (Unit × RomReg Qrom.HashDomain PairOut (SelMemN n))
      (Unit × RomReg Qrom.HashDomain PairOut (SelMemN n)) ℂ} (hσ : σ.PosSemidef) :
    flipCost (BadQN pk hon S) (hwReadKraus (.readH z upd))
        (readPs fun s ↦ SelectReadN pk s z i K) σ ≤
      ENNReal.ofReal (∑ q, if SelectReadN pk q.2 z i K ∧ q.2 ∉ BadQN pk hon S then
          ((encCwCountN pk (unionH q.2) i K * (2 ^ 128 * 2 ^ 256) : ℕ) : ℝ) /
            Fintype.card PairOut * (σ q q).re else 0) +
        ENNReal.ofReal ((readPs fun s ↦ SelectReadN pk s z i K) * σ).trace.re +
      2 * (ENNReal.ofReal (∑ q, if SelectReadN pk q.2 z i K ∧ q.2 ∉ BadQN pk hon S then
          ((encCwCountN pk (unionH q.2) i K * (2 ^ 128 * 2 ^ 256) : ℕ) : ℝ) /
            Fintype.card PairOut * (σ q q).re else 0) *
        ENNReal.ofReal ((readPs fun s ↦ SelectReadN pk s z i K) * σ).trace.re) ^ (2⁻¹ : ℝ) := by
  refine flipCost_readH_le (BadQN pk hon S) z upd (fun m ω ↦ cwSelN m i K z ω)
    (fun s ↦ SelectReadN pk s z i K)
    (fun s ↦ encCwCountN pk (unionH s) i K * (2 ^ 128 * 2 ^ 256)) ?_ hupd ?_ ?_ ?_ ?_ hσ
  · exact fun _ hs ↦ ⟨hs.hd, hs.hw⟩
  · exact fun _ u hs hS ↦ not_mem_badQN_read_keep hS hs u
  · intro s hs hS
    convert card_flip_readCwN_le hS hs using 3
  · exact fun s u hs hS ↦ mem_cellTargetBad_fill hS hs.hd u s.2.2 fun _ _ ht ↦ ht
  · exact fun s u ω hs hS ↦ mem_cellTargetBad_fill hS hs.hd u _ fun _ _ ht ↦
      ht.imp (tgtDigestN_cwSelN_mono hs.hm z ω) mem_covTgtN_memory

open scoped Classical in
/-- **The selecting-read term** of `flipCost_selectReadCwN_le`: if `encCwCountN ≤ C` on the
selection reads of the support outside `BadQN`, then `E ≤ C 2^-128 e`, with `e` the weight of the
selection reads. -/
theorem selectReadCwNE_le (z : Qrom.HashDomain) (i : Fin n) (K : Key) (C : ℕ)
    {σ : Matrix (Unit × RomReg Qrom.HashDomain PairOut (SelMemN n))
      (Unit × RomReg Qrom.HashDomain PairOut (SelMemN n)) ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ q, SelectReadN pk q.2 z i K → q.2 ∉ BadQN pk hon S → σ q q ≠ 0 →
      encCwCountN pk (unionH q.2) i K ≤ C) :
    (∑ q, if SelectReadN pk q.2 z i K ∧ q.2 ∉ BadQN pk hon S then
        ((encCwCountN pk (unionH q.2) i K * (2 ^ 128 * 2 ^ 256) : ℕ) : ℝ) /
          Fintype.card PairOut * (σ q q).re else 0) ≤
      C * (2 ^ 128)⁻¹ * ∑ q, if SelectReadN pk q.2 z i K then (σ q q).re else 0 := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hC0 : (0 : ℝ) ≤ C * (2 ^ 128)⁻¹ := by positivity
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases hq : SelectReadN pk q.2 z i K
  · rw [ite_eq_left hq]
    by_cases hb : q.2 ∉ BadQN pk hon S
    · rw [ite_eq_left ⟨hq, hb⟩]
      by_cases hσq : σ q q = 0
      · rw [hσq, Complex.zero_re, mul_zero, mul_zero]
      refine mul_le_mul_of_nonneg_right ?_ (hre q)
      rw [Nat.cast_mul, mul_div_assoc, pairFiber_div_card_real]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (hC q hq hb hσq)) (by positivity)
    · rw [ite_eq_right fun h ↦ hb h.2]
      exact mul_nonneg hC0 (hre q)
  · rw [ite_eq_right fun h ↦ hq h.1, ite_eq_right hq, mul_zero]

/-! ## Survival of a trial -/

/-- The memories whose key `K` of user `i` has no selection. -/
def unselMemN (i : Fin n) (K : Key) : Set (SelMemN n) := {m | m i K = none}

instance instDecidablePredUnselMemN (i : Fin n) (K : Key) : DecidablePred (· ∈ unselMemN i K) :=
  fun m ↦ inferInstanceAs (Decidable (m i K = none))

open scoped Classical in
/-- **Survival of a trial read of user `i`**: the outcomes of a trial of `i`'s unselected key `K`
that leave it unselected weigh at most `w - ρ_c e + p + 2 √(ρ_c e p)`, as for one user. -/
theorem survive_selectReadN_le (z : Qrom.HashDomain) (i : Fin n) (K : Key)
    (upd : SelMemN n → Option PairOut → SelMemN n)
    (hupd : ∀ m ω, m i K = none → upd m (some ω) = cwSelN m i K z ω)
    (SR : RomReg Qrom.HashDomain PairOut (SelMemN n) → Prop) [DecidablePred SR]
    (hSR : ∀ s, SR s → s.1.1 z = none ∧ s.2.1.1 z = none ∧ s.2.2 ∈ unselMemN i K)
    {σ : Matrix (Unit × RomReg Qrom.HashDomain PairOut (SelMemN n))
      (Unit × RomReg Qrom.HashDomain PairOut (SelMemN n)) ℂ} (hσ : σ.PosSemidef) :
    (∑ r : Option PairOut × SelMemN n, if upd r.2 r.1 ∈ unselMemN i K then
        (MatrixMap.conj (hwReadKraus (.readH z upd) r) σ).trace.re else 0) ≤
      (∑ q, if q.2.2.2 ∈ unselMemN i K then (σ q q).re else 0) -
        Quantum.Sphincs.rhoCw * (∑ q, if SR q.2 then (σ q q).re else 0) +
        (readPs SR * σ).trace.re +
        2 * √(Quantum.Sphincs.rhoCw * (∑ q, if SR q.2 then (σ q q).re else 0) *
          (readPs SR * σ).trace.re) :=
  survive_readH_le z upd (unselMemN i K) (fun ω ↦ Quantum.Sphincs.Codeword.Valid (pairDigest ω))
    card_codeword_pair_div
    (fun m hm ω ↦ by
      show upd m (some ω) i K = none ↔ _
      rw [hupd m ω hm]
      exact cwSelN_eq_none_iff hm z ω) SR hSR hσ

end Quantum.Qrom.Sphincs.Multi

end
