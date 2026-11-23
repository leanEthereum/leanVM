module

public import Quantum.Qrom.Sphincs.Cov
public import Quantum.Qrom.Xmss.Events
public import Quantum.Sphincs.Codeword
public import Quantum.Sphincs.HonestTable.Disclosure

@[expose] public section

/-!
# The leanSPHINCS event of the random oracle

After regrouping (`Quantum.Qrom.Regroup`, `hmsgRoute`) the register of the hardwired runtime is at
`(Y × Y, HashDomain)`, `Y = HashOutput`: a cell holds a pair, the hash of an input other than a
call 1 of `H_msg` is the first component of its own cell. The register holds the adversary's
database, the hardwired cells `W` and a finite memory `m : SelMem`: for each signed WOTS+C key, the
cell of its selected encoding input and the selected digest. Each input `x` has at most one slot
for the public key `pk` (`slotOf pk`), hence at most one target digest `tgtDigest pk hon W m x`:

* **Struct** (a chain, leaf or node of the hypertree, a FORS leaf, node or roots compression, slot
  `s`): the honest digest of `s` (`hon s`), unless `x` is the honest cell of `s` and hardwired;
* **Enc** (`enc K` of a signed key `K`): the selected digest, unless `x` is the selected cell.

`structTgtQ` are the pairs whose first component truncates to the target digest. **Cov**
(`Quantum.Qrom.Sphincs.covTgt S`): a call-0 `H_msg` cell that is not hardwired is hit when its pair
is covered by the disclosures `S`. The event `BadQ pk hon S` is `CellTargetBad` of the union of
both targets (`sphTgtQ`):

* `upClosed_slice_badQ`, `not_mem_badQ_start`, `freshBound_slice_badQ`: the graded-bound
  hypotheses, with fresh fraction `2^-128 + price S` per cell (`card_structTgtQ_le`,
  `pairFiber_div_card`, `covFrac_eq`).
* **Program ports**: hardwiring a cell without a Struct or Enc target once hardwired
  (`ExemptCell`, for instance an honest cell) costs nothing (`flipCost_programH_badQ_eq_zero`).
* **Read ports**: a trial read of key `K` (`SelectRead`) that records the selection only for a
  codeword digest (`cwSel`, `cwUpd`) flips at most `encCwCount * 2^384` pairs
  (`card_flip_readCw_le`); its flip cost (`flipCost_selectReadCw_le`, `selectReadCwE_le`) and the
  survival of an unselected key (`survive_selectRead_le`, fraction `Quantum.Sphincs.rhoCw`) reuse
  `Quantum.Xmss.EncCost`.
-/

open Matrix
open scoped ENNReal ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (Slot Key Disclosures Covered)

namespace Quantum.Qrom.Sphincs

open Quantum Quantum.Sponge

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

/-! ## Digests of pairs -/

/-- The digest of a regrouped pair: its first component, truncated. -/
def pairDigest (ω : HashOutput × HashOutput) : Digest :=
  truncateHash ω.1

/-- **Each digest has `2^128 · 2^256` pairs.** -/
theorem card_fiber_pairDigest (d : Digest) :
    (Finset.univ.filter fun ω : HashOutput × HashOutput ↦ pairDigest ω = d).card =
      2 ^ 128 * 2 ^ 256 := by
  rw [show (Finset.univ.filter fun ω : HashOutput × HashOutput ↦ pairDigest ω = d) =
      (Finset.univ.filter fun y : HashOutput ↦ truncateHash y = d) ×ˢ Finset.univ by
    rw [← Finset.univ_product_univ, ← Finset.filter_product_left]
    rfl, Finset.card_product,
    Quantum.Qrom.Xmss.card_fiber_truncateHash,
    Finset.card_univ, Quantum.Qrom.Xmss.card_hashOutput]

theorem card_fiber_pairDigest_le (d : Digest) :
    (Finset.univ.filter fun ω : HashOutput × HashOutput ↦ pairDigest ω = d).card ≤
      2 ^ 128 * 2 ^ 256 :=
  (card_fiber_pairDigest d).le

theorem card_hashOutput_ne_zero : (Fintype.card HashOutput : ℝ≥0∞) ≠ 0 := by
  rw [Quantum.Qrom.Xmss.card_hashOutput]
  simp

/-- The fraction of one digest's pairs: `2^-128`. -/
theorem pairFiber_div_card :
    ((2 ^ 128 * 2 ^ 256 : ℕ) : ℝ≥0∞) / Fintype.card (HashOutput × HashOutput) = (2 ^ 128)⁻¹ := by
  rw [Fintype.card_prod, Nat.cast_mul, Nat.cast_mul,
    show ((2 ^ 256 : ℕ) : ℝ≥0∞) = Fintype.card HashOutput by
      rw [Quantum.Qrom.Xmss.card_hashOutput],
    ENNReal.mul_div_mul_right _ _ card_hashOutput_ne_zero (ENNReal.natCast_ne_top _)]
  exact Quantum.Qrom.Xmss.fiber_div_card_hashOutput

/-- The same fraction over the reals. -/
theorem pairFiber_div_card_real :
    ((2 ^ 128 * 2 ^ 256 : ℕ) : ℝ) / Fintype.card (HashOutput × HashOutput) = (2 ^ 128)⁻¹ := by
  rw [Fintype.card_prod, Nat.cast_mul, Nat.cast_mul,
    show ((2 ^ 256 : ℕ) : ℝ) = Fintype.card HashOutput by
      rw [Quantum.Qrom.Xmss.card_hashOutput],
    mul_div_mul_right _ _ (by rw [Quantum.Qrom.Xmss.card_hashOutput]; positivity),
    Nat.cast_pow, Nat.cast_ofNat]
  exact Quantum.Qrom.Xmss.two_pow_div_card_hashOutput

/-- **The codeword pairs**: `cwCount · 2^384` pairs have a codeword digest. -/
theorem card_codeword_pair :
    (Finset.univ.filter fun ω : HashOutput × HashOutput ↦
      Quantum.Sphincs.Codeword.Valid (pairDigest ω)).card =
      Quantum.Sphincs.cwCount * (2 ^ 128 * 2 ^ 256) := by
  rw [Quantum.Sphincs.cwCount]
  have h := Quantum.Xmss.card_filter_out_add (out := pairDigest) (F := 2 ^ 128 * 2 ^ 256)
    card_fiber_pairDigest (fun d ↦ Quantum.Sphincs.Codeword.Valid d)
    (0 : HashOutput × HashOutput)
  simp only [zero_add] at h
  exact h

/-- The codeword pairs are a fraction `rhoCw` of the pairs. -/
theorem card_codeword_pair_div :
    ((Finset.univ.filter fun ω : HashOutput × HashOutput ↦
      Quantum.Sphincs.Codeword.Valid (pairDigest ω)).card : ℝ) /
      Fintype.card (HashOutput × HashOutput) = Quantum.Sphincs.rhoCw := by
  rw [card_codeword_pair, Nat.cast_mul, mul_div_assoc, pairFiber_div_card_real,
    Quantum.Sphincs.rhoCw, div_eq_mul_inv]

/-! ## The finite memory -/

/-- **The memory of the hardwired register**: for each signed WOTS+C key, the cell of its selected
encoding input and the selected digest. -/
abbrev SelMem := Key → Option (Qrom.HashDomain × Digest)

instance instFintypeSelMemSphincs : Fintype SelMem := by
  unfold SelMem
  infer_instance

instance instDecidableEqSelMemSphincs : DecidableEq SelMem := by
  unfold SelMem
  infer_instance

/-- Recording the selection of key `K`: cell `c`, digest `d`. -/
def SelMem.select (m : SelMem) (K : Key) (c : Qrom.HashDomain) (d : Digest) : SelMem :=
  Function.update m K (some (c, d))

theorem SelMem.select_self (m : SelMem) (K : Key) (c : Qrom.HashDomain) (d : Digest) :
    m.select K c d K = some (c, d) :=
  Function.update_self _ _ _

theorem SelMem.select_of_ne (m : SelMem) {K K' : Key} (c : Qrom.HashDomain) (d : Digest)
    (h : K' ≠ K) : m.select K c d K' = m K' :=
  Function.update_of_ne h _ _

/-! ## Targets -/

/-- **The honest cells**: for each Struct slot, the cell of its honest input and its honest
digest; `none` for the other slots. -/
abbrev HonestCells := Slot → Option (Qrom.HashDomain × Digest)

/-- The target digest of the input `x` at a Struct slot `s`: the honest digest of `s`, unless `x`
is the honest cell of `s` and hardwired. -/
def structDigest (hon : HonestCells) (W : Database Qrom.HashDomain (HashOutput × HashOutput))
    (x : Qrom.HashDomain) (s : Slot) : Option Digest :=
  (hon s).bind fun h ↦ if h.1 = x ∧ (W x).isSome then none else some h.2

/-- The target digest of the input `x` at slot `s`: at the encoding slot of a signed key its
selected digest unless `x` is the selected cell, elsewhere `structDigest`. -/
def slotDigest (hon : HonestCells) (W : Database Qrom.HashDomain (HashOutput × HashOutput))
    (m : SelMem) (x : Qrom.HashDomain) : Slot → Option Digest
  | .enc l τ e => (m (l, τ, e)).bind fun sel ↦ if sel.1 = x then none else some sel.2
  | s => structDigest hon W x s

/-- **The target digest of an input**, read from its slot for the public key `pk`. -/
def tgtDigest (pk : PublicKey) (hon : HonestCells)
    (W : Database Qrom.HashDomain (HashOutput × HashOutput)) (m : SelMem)
    (x : Qrom.HashDomain) : Option Digest :=
  (slotOf pk x).bind (slotDigest hon W m x)

/-- **The Struct and Enc targets** of the classical data `(W, m)`: the pairs of `x` whose digest
is its target digest. -/
def structTgtQ (pk : PublicKey) (hon : HonestCells)
    (W : Hw (HashOutput × HashOutput) Qrom.HashDomain)
    (m : SelMem) (x : Qrom.HashDomain) : Set (HashOutput × HashOutput) :=
  {ω | tgtDigest pk hon W.1 m x = some (pairDigest ω)}

/-- **The leanSPHINCS targets**: the Struct and Enc targets and the Cov targets of `S`. -/
def sphTgtQ (pk : PublicKey) (hon : HonestCells) (S : Disclosures)
    (W : Hw (HashOutput × HashOutput) Qrom.HashDomain) (m : SelMem) (x : Qrom.HashDomain) :
    Set (HashOutput × HashOutput) :=
  {ω | ω ∈ structTgtQ pk hon W m x ∨ ω ∈ covTgt S W m x}

/-- **The leanSPHINCS event of the random oracle**: a recorded or hardwired cell whose pair is in
its Struct, Enc or Cov target. -/
abbrev BadQ (pk : PublicKey) (hon : HonestCells) (S : Disclosures) :
    Set (RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem) :=
  CellTargetBad (sphTgtQ pk hon S)

variable {pk : PublicKey} {hon : HonestCells} {S : Disclosures}

theorem mem_structTgtQ {W : Hw (HashOutput × HashOutput) Qrom.HashDomain} {m : SelMem}
    {x : Qrom.HashDomain} {ω : HashOutput × HashOutput} :
    ω ∈ structTgtQ pk hon W m x ↔ tgtDigest pk hon W.1 m x = some (pairDigest ω) :=
  Iff.rfl

theorem mem_sphTgtQ {W : Hw (HashOutput × HashOutput) Qrom.HashDomain} {m : SelMem}
    {x : Qrom.HashDomain} {ω : HashOutput × HashOutput} :
    ω ∈ sphTgtQ pk hon S W m x ↔ ω ∈ structTgtQ pk hon W m x ∨ ω ∈ covTgt S W m x :=
  Iff.rfl

theorem mem_badQ_iff {s : RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem} :
    s ∈ BadQ pk hon S ↔ ∃ x ω, unionH s x = some ω ∧
      (tgtDigest pk hon s.2.1.1 s.2.2 x = some (pairDigest ω) ∨ ω ∈ covTgt S s.2.1 s.2.2 x) :=
  Iff.rfl

/-- The Cov targets do not read the memory. -/
theorem mem_covTgt_memory {M : Type} {W : Hw (HashOutput × HashOutput) Qrom.HashDomain}
    {m m' : M} {x : Qrom.HashDomain} {ω : HashOutput × HashOutput} (h : ω ∈ covTgt S W m x) :
    ω ∈ covTgt S W m' x :=
  h

/-- **A Cov hit**: a recorded call-0 `H_msg` cell, not hardwired, whose pair is covered. -/
theorem mem_badQ_of_cov {s : RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem}
    {x : Qrom.HashDomain} {ω : HashOutput × HashOutput} (hx : unionH s x = some ω)
    (h0 : hmsgCall x = some 0) (hw : s.2.1.1 x = none) (hc : Covered S (pairView ω)) :
    s ∈ BadQ pk hon S :=
  ⟨x, ω, hx, .inr ⟨h0, hw, hc⟩⟩

theorem slotDigest_of_ne_enc (W : Database Qrom.HashDomain (HashOutput × HashOutput)) (m : SelMem)
    (x : Qrom.HashDomain) {s : Slot} (h : ∀ l τ e, s ≠ .enc l τ e) :
    slotDigest hon W m x s = structDigest hon W x s := by
  cases s with
  | enc l τ e => exact absurd rfl (h l τ e)
  | _ => rfl

theorem slotDigest_enc (W : Database Qrom.HashDomain (HashOutput × HashOutput)) (m : SelMem)
    (x : Qrom.HashDomain) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) :
    slotDigest hon W m x (.enc l τ e) =
      (m (l, τ, e)).bind fun sel ↦ if sel.1 = x then none else some sel.2 :=
  rfl

/-- The target of `x` depends on the hardwired cells only through whether `x` is hardwired. -/
theorem tgtDigest_congr {W W' : Database Qrom.HashDomain (HashOutput × HashOutput)} (m : SelMem)
    {x : Qrom.HashDomain} (h : (W x).isSome = (W' x).isSome) :
    tgtDigest pk hon W m x = tgtDigest pk hon W' m x := by
  unfold tgtDigest
  cases slotOf pk x with
  | none => rfl
  | some s =>
    simp only [Option.bind_some]
    by_cases hs : ∀ l τ e, s ≠ .enc l τ e
    · rw [slotDigest_of_ne_enc _ _ _ hs, slotDigest_of_ne_enc _ _ _ hs, structDigest,
        structDigest, h]
    · push Not at hs
      obtain ⟨l, τ, e, rfl⟩ := hs
      rfl

/-- **More hardwired cells, fewer targets.** -/
theorem tgtDigest_anti {W W' : Database Qrom.HashDomain (HashOutput × HashOutput)} (m : SelMem)
    {x : Qrom.HashDomain} (h : (W x).isSome → (W' x).isSome) {d : Digest}
    (hd : tgtDigest pk hon W' m x = some d) : tgtDigest pk hon W m x = some d := by
  unfold tgtDigest at hd ⊢
  revert hd
  cases slotOf pk x with
  | none => exact id
  | some s =>
    simp only [Option.bind_some]
    by_cases hs : ∀ l τ e, s ≠ .enc l τ e
    · rw [slotDigest_of_ne_enc _ _ _ hs, slotDigest_of_ne_enc _ _ _ hs, structDigest,
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
      obtain ⟨l, τ, e, rfl⟩ := hs
      exact id

/-- An input of no slot has no target. -/
theorem tgtDigest_of_slotOf_none (W : Database Qrom.HashDomain (HashOutput × HashOutput))
    (m : SelMem) {x : Qrom.HashDomain} (hx : slotOf pk x = none) :
    tgtDigest pk hon W m x = none := by
  rw [tgtDigest, hx]
  rfl

/-- An input at a non-encoding slot without honest cell has no target. -/
theorem tgtDigest_of_hon_none (W : Database Qrom.HashDomain (HashOutput × HashOutput))
    (m : SelMem) {x : Qrom.HashDomain} {s : Slot} (hx : slotOf pk x = some s)
    (henc : ∀ l τ e, s ≠ .enc l τ e) (hs : hon s = none) : tgtDigest pk hon W m x = none := by
  rw [tgtDigest, hx, Option.bind_some, slotDigest_of_ne_enc _ _ _ henc, structDigest, hs]
  rfl

/-- **A hardwired honest cell has no target.** -/
theorem tgtDigest_honest_of_hw {W : Database Qrom.HashDomain (HashOutput × HashOutput)}
    (m : SelMem) {z : Qrom.HashDomain} {s : Slot} {d : Digest} (hz : slotOf pk z = some s)
    (henc : ∀ l τ e, s ≠ .enc l τ e) (hs : hon s = some (z, d)) (hW : (W z).isSome) :
    tgtDigest pk hon W m z = none := by
  rw [tgtDigest, hz, Option.bind_some, slotDigest_of_ne_enc _ _ _ henc, structDigest, hs,
    Option.bind_some, ite_eq_left ⟨rfl, hW⟩]

/-- A cell at the encoding slot of an unselected key has no target. -/
theorem tgtDigest_enc_none (W : Database Qrom.HashDomain (HashOutput × HashOutput)) {m : SelMem}
    {x : Qrom.HashDomain} {K : Key} (hx : slotOf pk x = some (.enc K.1 K.2.1 K.2.2))
    (hm : m K = none) : tgtDigest pk hon W m x = none := by
  rw [tgtDigest, hx, Option.bind_some, slotDigest_enc]
  change (m K).bind _ = none
  rw [hm]
  rfl

/-- The selected cell has no target. -/
theorem tgtDigest_select_self (W : Database Qrom.HashDomain (HashOutput × HashOutput)) (m : SelMem)
    {c : Qrom.HashDomain} {K : Key} (hc : slotOf pk c = some (.enc K.1 K.2.1 K.2.2)) (d : Digest) :
    tgtDigest pk hon W (m.select K c d) c = none := by
  rw [tgtDigest, hc, Option.bind_some, slotDigest_enc]
  change ((m.select K c d) K).bind _ = none
  rw [SelMem.select_self, Option.bind_some, ite_eq_left rfl]

/-- Recording a selection adds the selected digest as the target of the other cells at its
encoding slot, and nothing else. -/
theorem tgtDigest_select {W : Database Qrom.HashDomain (HashOutput × HashOutput)} {m : SelMem}
    {K : Key} {c x : Qrom.HashDomain} {d d' : Digest}
    (h : tgtDigest pk hon W (m.select K c d) x = some d') :
    tgtDigest pk hon W m x = some d' ∨
      (slotOf pk x = some (.enc K.1 K.2.1 K.2.2) ∧ x ≠ c ∧ d' = d) := by
  unfold tgtDigest at h ⊢
  revert h
  cases hs : slotOf pk x with
  | none => exact fun h ↦ absurd h (by simp)
  | some s =>
    simp only [Option.bind_some]
    intro h
    by_cases henc : ∀ l τ e, s ≠ .enc l τ e
    · rw [slotDigest_of_ne_enc _ _ _ henc] at h
      rw [slotDigest_of_ne_enc _ _ _ henc]
      exact .inl h
    · push Not at henc
      obtain ⟨l, τ, e, rfl⟩ := henc
      rw [slotDigest_enc] at h ⊢
      by_cases hk : (l, τ, e) = K
      · subst hk
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
theorem tgtDigest_select_mono {W : Database Qrom.HashDomain (HashOutput × HashOutput)}
    {m : SelMem} {K : Key} (hm : m K = none) (c : Qrom.HashDomain) (d : Digest)
    {x : Qrom.HashDomain} {d' : Digest} (h : tgtDigest pk hon W m x = some d') :
    tgtDigest pk hon W (m.select K c d) x = some d' := by
  unfold tgtDigest at h ⊢
  revert h
  cases slotOf pk x with
  | none => exact id
  | some s =>
    simp only [Option.bind_some]
    by_cases henc : ∀ l τ e, s ≠ .enc l τ e
    · rw [slotDigest_of_ne_enc _ _ _ henc, slotDigest_of_ne_enc _ _ _ henc]
      exact id
    · push Not at henc
      obtain ⟨l, τ, e, rfl⟩ := henc
      rw [slotDigest_enc, slotDigest_enc]
      by_cases hk : (l, τ, e) = K
      · subst hk
        rw [hm]
        exact fun h ↦ absurd h (by simp)
      · rw [SelMem.select_of_ne m c d hk]
        exact id

/-- **An `H_msg` call is at an `H_msg` slot**: a point naming a digest call has no other slot. -/
theorem slotOf_of_hmsgCall {x : Qrom.HashDomain} {call : DigestCall} (h : hmsgCall x = some call)
    {s : Slot} (hs : slotOf pk x = some s) : ∃ R M c, s = .hmsg R M c := by
  obtain ⟨-, hx⟩ := hmsgCall_eq_some_iff.mp h
  have hl := (hmsgCallOf_eq_some_iff.mp hx).1
  rw [slotOf, slotOfInput, ite_eq_left hl, hmsgSlotOf] at hs
  split_ifs at hs
  obtain ⟨c, -, hc⟩ := Option.map_eq_some_iff.mp hs
  exact ⟨_, _, _, hc.symm⟩

/-- A point at an encoding slot is no call-0 `H_msg` cell. -/
theorem hmsgCall_ne_zero_of_enc {x : Qrom.HashDomain} {K : Key}
    (hx : slotOf pk x = some (.enc K.1 K.2.1 K.2.2)) : hmsgCall x ≠ some 0 := fun h ↦ by
  obtain ⟨R, M, c, hc⟩ := slotOf_of_hmsgCall h hx
  cases hc

/-! ## The graded-bound hypotheses -/

/-- **Every slice of the event is upward closed.** -/
theorem upClosed_slice_badQ (W : Hw (HashOutput × HashOutput) Qrom.HashDomain) (m : SelMem) :
    UpClosed (slice (BadQ pk hon S) W m) :=
  upClosed_slice_cellTargetBad W m

/-- **The start is outside the event** when no hardwired cell has a Struct or Enc target (a
hardwired cell has no Cov target). -/
theorem not_mem_badQ_start (W₀ : Hw (HashOutput × HashOutput) Qrom.HashDomain) (m₀ : SelMem)
    (h : ∀ x, (W₀.1 x).isSome → tgtDigest pk hon W₀.1 m₀ x = none) :
    (((Database.empty, Database.empty, Database.empty), W₀, m₀) :
      RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem) ∉ BadQ pk hon S :=
  not_mem_cellTargetBad_start W₀ m₀ fun x y hxy hy ↦ by
    rcases hy with hy | hy
    · have h0 := h x (by rw [hxy]; rfl)
      rw [mem_structTgtQ, h0] at hy
      cases hy
    · exact Option.some_ne_none y (hxy.symm.trans hy.2.1)

/-- The start without hardwired cells is outside the event. -/
theorem empty_not_mem_badQ (m₀ : SelMem) :
    (((Database.empty, Database.empty, Database.empty),
      (Database.empty, Database.empty, Database.empty), m₀) :
      RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem) ∉ BadQ pk hon S :=
  not_mem_badQ_start _ m₀ fun _ h ↦ absurd h (by simp [Database.empty])

open scoped Classical in
/-- The Struct and Enc targets of a cell are at most one digest's pairs. -/
theorem card_structTgtQ_le (W : Hw (HashOutput × HashOutput) Qrom.HashDomain) (m : SelMem)
    (x : Qrom.HashDomain) :
    (Finset.univ.filter fun ω ↦ ω ∈ structTgtQ pk hon W m x).card ≤ 2 ^ 128 * 2 ^ 256 := by
  cases hd : tgtDigest pk hon W.1 m x with
  | none =>
    rw [Finset.filter_false_of_mem fun ω _ hω ↦ by rw [mem_structTgtQ, hd] at hω; cases hω]
    simp
  | some d =>
    refine le_trans (Finset.card_le_card fun ω hω ↦ ?_) (card_fiber_pairDigest_le d)
    have hω : ω ∈ structTgtQ pk hon W m x := (Finset.mem_filter.1 hω).2
    rw [mem_structTgtQ, hd] at hω
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Option.some.inj hω).symm⟩

/-- **The fresh bound of every slice**: a fresh cell enters the event with probability at most
`2^-128 + price S` (Struct or Enc, then Cov), a fresh `k`, `k'` cell never. -/
theorem freshBound_slice_badQ (W : Hw (HashOutput × HashOutput) Qrom.HashDomain) (m : SelMem)
    (t : ℕ) :
    FreshBound (slice (BadQ pk hon S) W m) t
      ((2 ^ 128)⁻¹ + ENNReal.ofReal (Quantum.Sphincs.price S)) := by
  classical
  refine freshBound_slice_cellTargetBad W m (fun x _ ↦ ?_) t
  have hsub : (Finset.univ.filter fun ω ↦ ω ∈ sphTgtQ pk hon S W m x) ⊆
      (Finset.univ.filter fun ω ↦ ω ∈ structTgtQ pk hon W m x) ∪
        (Finset.univ.filter fun ω : HashOutput × HashOutput ↦ Covered S (pairView ω)) := by
    intro ω hω
    rcases (Finset.mem_filter.1 hω).2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h.2.2⟩)
  refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2
    ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))) _) ?_
  rw [Nat.cast_add, ENNReal.add_div, ← covFrac_eq S, ← pairFiber_div_card]
  exact add_le_add (ENNReal.div_le_div_right (by exact_mod_cast card_structTgtQ_le W m x) _)
    le_rfl

/-! ## Program ports -/

/-- A cell without a Struct or Enc target once hardwired, whatever the other cells and the memory:
an honest cell, a cell of a non-encoding slot without honest cell, a cell of no slot. -/
def ExemptCell (pk : PublicKey) (hon : HonestCells) (z : Qrom.HashDomain) : Prop :=
  ∀ (W : Database Qrom.HashDomain (HashOutput × HashOutput)) (m : SelMem), (W z).isSome →
    tgtDigest pk hon W m z = none

theorem exemptCell_honest {z : Qrom.HashDomain} {s : Slot} {d : Digest}
    (hz : slotOf pk z = some s) (henc : ∀ l τ e, s ≠ .enc l τ e) (hs : hon s = some (z, d)) :
    ExemptCell pk hon z :=
  fun _ m hW ↦ tgtDigest_honest_of_hw m hz henc hs hW

theorem exemptCell_of_hon_none {z : Qrom.HashDomain} {s : Slot} (hz : slotOf pk z = some s)
    (henc : ∀ l τ e, s ≠ .enc l τ e) (hs : hon s = none) : ExemptCell pk hon z :=
  fun W m _ ↦ tgtDigest_of_hon_none W m hz henc hs

theorem exemptCell_of_slotOf_none {z : Qrom.HashDomain} (hz : slotOf pk z = none) :
    ExemptCell pk hon z :=
  fun W m _ ↦ tgtDigest_of_slotOf_none W m hz

/-- Hardwiring `z` leaves the targets of the other cells. -/
theorem tgtDigest_update_of_ne (W : Database Qrom.HashDomain (HashOutput × HashOutput))
    (m : SelMem) {z x : Qrom.HashDomain} (hx : x ≠ z) (o : Option (HashOutput × HashOutput)) :
    tgtDigest pk hon (Function.update W z o) m x = tgtDigest pk hon W m x :=
  tgtDigest_congr m (by rw [Function.update_of_ne hx])

/-- Programming `z` with `v`: the other targets do not grow and `v` is outside the new target of
an exempt `z`. -/
theorem programH_badQ_conds {W : Hw (HashOutput × HashOutput) Qrom.HashDomain} {m : SelMem}
    {z : Qrom.HashDomain} (hz : ExemptCell pk hon z) (v : HashOutput × HashOutput) :
    (∀ x, x ≠ z → ∀ ω ∈ sphTgtQ pk hon S (Function.update W.1 z (some v), W.2) m x,
      ω ∈ sphTgtQ pk hon S W m x) ∧
    v ∉ sphTgtQ pk hon S (Function.update W.1 z (some v), W.2) m z := by
  refine ⟨fun x hx ω hω ↦ ?_, fun hv ↦ ?_⟩
  · rcases hω with h | h
    · exact .inl ((tgtDigest_update_of_ne W.1 m hx (some v)).symm.trans h)
    · exact .inr (mem_covTgt_update_of_ne hx v h)
  · rcases hv with h | h
    · exact Option.some_ne_none _
        (h.symm.trans (hz _ m (by simp only [Function.update_self, Option.isSome_some])))
    · exact not_mem_covTgt_update_self W m z v v h

/-- **Programming an exempt cell flips nothing.** -/
theorem not_mem_badQ_programH {s : RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem}
    (hs : s ∉ BadQ pk hon S) {z : Qrom.HashDomain} (hz : ExemptCell pk hon z)
    (v : HashOutput × HashOutput) : progMap (.programH z v) s ∉ BadQ pk hon S :=
  not_mem_cellTargetBad_programH hs z v (programH_badQ_conds hz v).1 (programH_badQ_conds hz v).2

/-- **Programming cost zero**: hardwiring an exempt cell, in particular an honest cell
(`exemptCell_honest`), costs nothing. -/
theorem flipCost_programH_badQ_eq_zero {z : Qrom.HashDomain} (hz : ExemptCell pk hon z)
    (v : HashOutput × HashOutput)
    {σ : Matrix (Unit × RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem)
      (Unit × RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem) ℂ} (hσ : σ.PosSemidef) :
    flipCost (BadQ pk hon S) (hwProgKraus (.programH z v)) 0 σ = 0 :=
  flipCost_programH_cellTargetBad_eq_zero z v hσ fun _ _ _ ↦ programH_badQ_conds hz v

/-! ## Read ports -/

/-- **A trial read**: the read of the cell `z` of an encoding trial of the unselected key `K`,
neither hardwired nor recorded. -/
structure SelectRead (pk : PublicKey) (s : RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem)
    (z : Qrom.HashDomain) (K : Key) : Prop where
  hw : s.2.1.1 z = none
  hd : s.1.1 z = none
  hm : s.2.2 K = none
  slot : slotOf pk z = some (.enc K.1 K.2.1 K.2.2)

/-- **The memory after a trial read** of key `K` at cell `z` with pair `ω`: the selection if the
digest is a codeword. -/
def cwSel (m : SelMem) (K : Key) (z : Qrom.HashDomain) (ω : HashOutput × HashOutput) : SelMem :=
  if Quantum.Sphincs.Codeword.Valid (pairDigest ω) then m.select K z (pairDigest ω) else m

/-- **The memory update of a trial read**: select a codeword digest of an unselected key. -/
def cwUpd (K : Key) (z : Qrom.HashDomain) : SelMem → Option (HashOutput × HashOutput) → SelMem
  | m, some ω => if m K = none then cwSel m K z ω else m
  | m, none => m

theorem cwUpd_some (K : Key) (z : Qrom.HashDomain) (m : SelMem) (ω : HashOutput × HashOutput) :
    cwUpd K z m (some ω) = m ∨ cwUpd K z m (some ω) = cwSel m K z ω := by
  show (if m K = none then cwSel m K z ω else m) = m ∨
    (if m K = none then cwSel m K z ω else m) = cwSel m K z ω
  split_ifs
  · exact .inr rfl
  · exact .inl rfl

theorem cwUpd_some_of_none (K : Key) (z : Qrom.HashDomain) {m : SelMem} (hm : m K = none)
    (ω : HashOutput × HashOutput) : cwUpd K z m (some ω) = cwSel m K z ω :=
  ite_eq_left hm

/-- A trial of an unselected key leaves it unselected exactly when its digest is no codeword. -/
theorem cwSel_eq_none_iff {m : SelMem} {K : Key} (hm : m K = none) (z : Qrom.HashDomain)
    (ω : HashOutput × HashOutput) :
    cwSel m K z ω K = none ↔ ¬ Quantum.Sphincs.Codeword.Valid (pairDigest ω) := by
  unfold cwSel
  split_ifs with hv
  · rw [SelMem.select_self]
    exact iff_of_false (Option.some_ne_none _) (not_not.2 hv)
  · exact iff_of_true hm hv

/-- A trial read keeps or grows every target. -/
theorem tgtDigest_cwSel_mono {W : Database Qrom.HashDomain (HashOutput × HashOutput)} {m : SelMem}
    {K : Key} (hm : m K = none) (z : Qrom.HashDomain) (ω : HashOutput × HashOutput)
    {x : Qrom.HashDomain} {d : Digest} (h : tgtDigest pk hon W m x = some d) :
    tgtDigest pk hon W (cwSel m K z ω) x = some d := by
  unfold cwSel
  split_ifs
  · exact tgtDigest_select_mono hm z _ h
  · exact h

/-- After a trial read the read cell has no target. -/
theorem tgtDigest_cwSel_self (W : Database Qrom.HashDomain (HashOutput × HashOutput)) {m : SelMem}
    {z : Qrom.HashDomain} {K : Key} (hz : slotOf pk z = some (.enc K.1 K.2.1 K.2.2))
    (hm : m K = none) (ω : HashOutput × HashOutput) :
    tgtDigest pk hon W (cwSel m K z ω) z = none := by
  unfold cwSel
  split_ifs
  · exact tgtDigest_select_self W m hz _
  · exact tgtDigest_enc_none W hz hm

/-- A trial read adds, for a codeword digest, the digest as the target of the other cells at its
encoding slot, and nothing else. -/
theorem tgtDigest_cwSel {W : Database Qrom.HashDomain (HashOutput × HashOutput)} {m : SelMem}
    {K : Key} {z x : Qrom.HashDomain} {ω : HashOutput × HashOutput} {d : Digest}
    (h : tgtDigest pk hon W (cwSel m K z ω) x = some d) :
    tgtDigest pk hon W m x = some d ∨ (slotOf pk x = some (.enc K.1 K.2.1 K.2.2) ∧
      Quantum.Sphincs.Codeword.Valid (pairDigest ω) ∧ d = pairDigest ω) := by
  unfold cwSel at h
  split_ifs at h with hv
  · rcases tgtDigest_select h with h' | ⟨h1, -, h3⟩
    · exact .inl h'
    · exact .inr ⟨h1, hv, h3⟩
  · exact .inl h

/-- **A read that keeps the memory flips nothing**: the trial's cell is at the encoding slot of an
unselected key, so it has no target. -/
theorem not_mem_badQ_read_keep {s : RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem}
    (hs : s ∉ BadQ pk hon S) {z : Qrom.HashDomain} {K : Key} (hr : SelectRead pk s z K)
    (u : Option (HashOutput × HashOutput)) :
    ((Function.update s.1.1 z u, s.1.2), s.2.1, s.2.2) ∉ BadQ pk hon S :=
  not_mem_cellTargetBad_readH hs s.2.2
    (Set.eq_empty_iff_forall_notMem.2 fun ω hω ↦ by
      rcases hω with h | h
      · rw [mem_structTgtQ, tgtDigest_enc_none _ hr.slot hr.hm] at h
        cases h
      · exact hmsgCall_ne_zero_of_enc hr.slot h.1)
    (fun _ _ _ h ↦ h) u

/-- The recorded or hardwired cells of a union view at the encoding slot of key `K` whose pair has
a codeword digest. -/
noncomputable def encCwCount (pk : PublicKey)
    (U : Qrom.HashDomain → Option (HashOutput × HashOutput))
    (K : Key) : ℕ :=
  Quantum.Qrom.Xmss.cellOutCount U (fun x ↦ slotOf pk x = some (.enc K.1 K.2.1 K.2.2))
    fun ω ↦ Quantum.Sphincs.Codeword.Valid (pairDigest ω)

/-- The recorded or hardwired cells of a union view at an encoding slot. -/
noncomputable def encSlotCount (pk : PublicKey)
    (U : Qrom.HashDomain → Option (HashOutput × HashOutput)) : ℕ :=
  Quantum.Qrom.Xmss.cellOutCount U (fun x ↦ ∃ K : Key, slotOf pk x = some (.enc K.1 K.2.1 K.2.2))
    fun _ ↦ True

/-- **The keys share the encoding-slot cells**: each cell has one slot, so the codeword counts of
all keys add up to at most the encoding-slot cells. -/
theorem sum_encCwCount_le (U : Qrom.HashDomain → Option (HashOutput × HashOutput)) :
    ∑ K : Key, encCwCount pk U K ≤ encSlotCount pk U := by
  have hP : ∀ (K K' : Key) (x : Qrom.HashDomain),
      slotOf pk x = some (.enc K.1 K.2.1 K.2.2) → slotOf pk x = some (.enc K'.1 K'.2.1 K'.2.2) →
        K = K' :=
    fun K K' x h h' ↦ by
      obtain ⟨h1, h2, h3⟩ := Slot.enc.inj (Option.some.inj (h.symm.trans h'))
      exact Prod.ext h1 (Prod.ext h2 h3)
  have h := Quantum.Qrom.Xmss.sum_cellOutCount_le (κ := Key) (D := Qrom.HashDomain)
    (Y := HashOutput × HashOutput) U (fun K x ↦ slotOf pk x = some (.enc K.1 K.2.1 K.2.2)) hP
    fun ω ↦ Quantum.Sphincs.Codeword.Valid (pairDigest ω)
  exact h

/-- **`card_flip_readCw_le`**: a trial read of key `K` that records the selection only for a
codeword digest flips a state outside `BadQ` for at most `encCwCount * 2^384` pairs of the read
cell, whatever the read leaves in the cell: the flips are the codeword digests of the other cells
at `enc K`. -/
theorem card_flip_readCw_le {s : RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem}
    (hs : s ∉ BadQ pk hon S) {z : Qrom.HashDomain} {K : Key} (hr : SelectRead pk s z K) :
    (Finset.univ.filter fun ω : HashOutput × HashOutput ↦ ∃ u : Option (HashOutput × HashOutput),
      ((Function.update s.1.1 z u, s.1.2), s.2.1, cwSel s.2.2 K z ω) ∈ BadQ pk hon S).card ≤
        encCwCount pk (unionH s) K * (2 ^ 128 * 2 ^ 256) :=
  Quantum.Qrom.Xmss.card_flip_readH_out_le (D := Qrom.HashDomain) (Y := HashOutput × HashOutput)
    (M := SelMem) pairDigest card_fiber_pairDigest_le hs
    (fun x ↦ slotOf pk x = some (.enc K.1 K.2.1 K.2.2)) (fun d ↦ Quantum.Sphincs.Codeword.Valid d)
    (fun ω ↦ cwSel s.2.2 K z ω)
    (fun ω ↦ Set.eq_empty_iff_forall_notMem.2 fun _ hy ↦ by
      rcases hy with h | h
      · exact Option.some_ne_none _
          ((tgtDigest_cwSel_self s.2.1.1 hr.slot hr.hm ω).symm.trans h).symm
      · exact hmsgCall_ne_zero_of_enc hr.slot h.1)
    (fun _ _ _ _ hy ↦ by
      rcases hy with h | h
      · exact (tgtDigest_cwSel h).imp Or.inl fun h ↦ ⟨h.1, h.2.1, h.2.2⟩
      · exact .inl (.inr (mem_covTgt_memory h)))

open scoped Classical in
/-- **The flip cost of a codeword-selecting read**: for a memory update that keeps the memory or
records the selection only for a codeword digest (`cwUpd`),
`E = ∑_{SelectRead, ∉ BadQ} encCwCount · 2^384 / |Y × Y| · σ_ss`. -/
theorem flipCost_selectReadCw_le (z : Qrom.HashDomain) (K : Key)
    (upd : SelMem → Option (HashOutput × HashOutput) → SelMem)
    (hupd : ∀ m ω, upd m (some ω) = m ∨ upd m (some ω) = cwSel m K z ω)
    {σ : Matrix (Unit × RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem)
      (Unit × RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem) ℂ} (hσ : σ.PosSemidef) :
    flipCost (BadQ pk hon S) (hwReadKraus (.readH z upd)) (readPs fun s ↦ SelectRead pk s z K) σ ≤
      ENNReal.ofReal (∑ q, if SelectRead pk q.2 z K ∧ q.2 ∉ BadQ pk hon S then
          ((encCwCount pk (unionH q.2) K * (2 ^ 128 * 2 ^ 256) : ℕ) : ℝ) /
            Fintype.card (HashOutput × HashOutput) * (σ q q).re else 0) +
        ENNReal.ofReal ((readPs fun s ↦ SelectRead pk s z K) * σ).trace.re +
      2 * (ENNReal.ofReal (∑ q, if SelectRead pk q.2 z K ∧ q.2 ∉ BadQ pk hon S then
          ((encCwCount pk (unionH q.2) K * (2 ^ 128 * 2 ^ 256) : ℕ) : ℝ) /
            Fintype.card (HashOutput × HashOutput) * (σ q q).re else 0) *
        ENNReal.ofReal ((readPs fun s ↦ SelectRead pk s z K) * σ).trace.re) ^ (2⁻¹ : ℝ) := by
  refine flipCost_readH_le (BadQ pk hon S) z upd (fun m ω ↦ cwSel m K z ω)
    (fun s ↦ SelectRead pk s z K) (fun s ↦ encCwCount pk (unionH s) K * (2 ^ 128 * 2 ^ 256)) ?_
    hupd ?_ ?_ ?_ ?_ hσ
  · exact fun _ hs ↦ ⟨hs.hd, hs.hw⟩
  · exact fun _ u hs hS ↦ not_mem_badQ_read_keep hS hs u
  · intro s hs hS
    convert card_flip_readCw_le hS hs using 3
  · exact fun s u hs hS ↦ mem_cellTargetBad_fill hS hs.hd u s.2.2 fun _ _ ht ↦ ht
  · exact fun s u ω hs hS ↦ mem_cellTargetBad_fill hS hs.hd u _ fun _ _ ht ↦
      ht.imp (tgtDigest_cwSel_mono hs.hm z ω) mem_covTgt_memory

open scoped Classical in
/-- **The selecting-read term** of `flipCost_selectReadCw_le`: if `encCwCount ≤ C` on the
selection reads of the support outside `BadQ`, then `E ≤ C 2^-128 e`, with `e` the weight of the
selection reads. -/
theorem selectReadCwE_le (z : Qrom.HashDomain) (K : Key) (C : ℕ)
    {σ : Matrix (Unit × RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem)
      (Unit × RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem) ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ q, SelectRead pk q.2 z K → q.2 ∉ BadQ pk hon S → σ q q ≠ 0 →
      encCwCount pk (unionH q.2) K ≤ C) :
    (∑ q, if SelectRead pk q.2 z K ∧ q.2 ∉ BadQ pk hon S then
        ((encCwCount pk (unionH q.2) K * (2 ^ 128 * 2 ^ 256) : ℕ) : ℝ) /
          Fintype.card (HashOutput × HashOutput) * (σ q q).re else 0) ≤
      C * (2 ^ 128)⁻¹ * ∑ q, if SelectRead pk q.2 z K then (σ q q).re else 0 := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hC0 : (0 : ℝ) ≤ C * (2 ^ 128)⁻¹ := by positivity
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases hq : SelectRead pk q.2 z K
  · rw [ite_eq_left hq]
    by_cases hb : q.2 ∉ BadQ pk hon S
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

/-- The memories whose key `K` has no selection. -/
def unselMem (K : Key) : Set SelMem := {m | m K = none}

instance instDecidablePredUnselMemSphincs (K : Key) : DecidablePred (· ∈ unselMem K) :=
  fun m ↦ inferInstanceAs (Decidable (m K = none))

open scoped Classical in
/-- **Survival of a trial read**: the outcomes of a trial of the unselected key `K` that leave it
unselected weigh at most `w - ρ_c e + p + 2 √(ρ_c e p)`, with `w` the weight of the states where
the key is unselected, `e` the weight of the selection reads `SR` (cell empty and not hardwired,
key unselected) and `p = tr (P σ)` the rest: on an empty cell the trial's digest is a codeword
with probability `Quantum.Sphincs.rhoCw`. -/
theorem survive_selectRead_le (z : Qrom.HashDomain) (K : Key)
    (upd : SelMem → Option (HashOutput × HashOutput) → SelMem)
    (hupd : ∀ m ω, m K = none → upd m (some ω) = cwSel m K z ω)
    (SR : RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem → Prop) [DecidablePred SR]
    (hSR : ∀ s, SR s → s.1.1 z = none ∧ s.2.1.1 z = none ∧ s.2.2 ∈ unselMem K)
    {σ : Matrix (Unit × RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem)
      (Unit × RomReg Qrom.HashDomain (HashOutput × HashOutput) SelMem) ℂ} (hσ : σ.PosSemidef) :
    (∑ r : Option (HashOutput × HashOutput) × SelMem, if upd r.2 r.1 ∈ unselMem K then
        (MatrixMap.conj (hwReadKraus (.readH z upd) r) σ).trace.re else 0) ≤
      (∑ q, if q.2.2.2 ∈ unselMem K then (σ q q).re else 0) -
        Quantum.Sphincs.rhoCw * (∑ q, if SR q.2 then (σ q q).re else 0) +
        (readPs SR * σ).trace.re +
        2 * √(Quantum.Sphincs.rhoCw * (∑ q, if SR q.2 then (σ q q).re else 0) *
          (readPs SR * σ).trace.re) :=
  survive_readH_le z upd (unselMem K) (fun ω ↦ Quantum.Sphincs.Codeword.Valid (pairDigest ω))
    card_codeword_pair_div
    (fun m hm ω ↦ by
      show upd m (some ω) K = none ↔ _
      rw [hupd m ω hm]
      exact cwSel_eq_none_iff hm z ω) SR hSR hσ

end Quantum.Qrom.Sphincs

end
