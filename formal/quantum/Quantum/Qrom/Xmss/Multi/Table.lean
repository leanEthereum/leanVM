module

public import Quantum.Qrom.TableLawOn
public import Quantum.Qrom.MultiUser.Owner
public import Quantum.Qrom.Xmss.HonestTable
public import Quantum.Qrom.Xmss.Events
public import Quantum.Qrom.SufCma.MultiGame

@[expose] public section

/-!
# leanXMSS's honest table for `n` users

User `i` has master seed `S0 i` and the single-user honest table (`Quantum.Qrom.Xmss.table`) at
the positions `(i, p)`; together the positions `PosN n = Fin n × Pos` and values
`QTableN n = PosN n → HashOutput`.

* **Domain separation.** Every input leanXMSS hashes outside the scheme seed's and the public
  parameter's derivations is prefixed by the public parameter (`sliceBits_cell`, from
  `inputBit_thInput_prefix`); `prefixOf x` reads it, `prefixOf_cell`. Hence
  (`cellN_injective_of`): if the master seeds, the scheme seeds and the public parameters of the
  users are pairwise distinct, the cells of all users' positions are pairwise distinct.
  `ownerOf_cellOfN`: with distinct parameters, the owner of a prefixed cell of user `i` is `i`.
* `tableN S0`: the `LazyTableOn (PosN n) HashDomain HashOutput`, good when its cells are injective
  and the public parameters distinct (`goodN`); `user_tab_tableN`: user `i`'s part of the table of
  `H` is the single-user table of `H` at `S0 i`; `consistent_fillN`. `simulateQ_generateAll`:
  against a function consistent with every user, the key generation of all users returns the
  tables' keys.
* **The collision bound** (`prob_not_goodN_le`): over uniform master seeds and table values, the
  table is bad with probability at most `C(n,2) (2^-128 + 2 · 2^-256)` (equal parameters, equal
  master seeds, equal scheme seeds).
-/

open scoped ENNReal
open HashSig HashSig.OverPermutation LeanXmss
open Quantum.Xmss (Slot inputBit bitOf inputBit_thInput_prefix)
open Quantum.Xmss.Hybrid (uavg uavg_mono uavg_add)
open Quantum.Qrom.MultiUser (ownerOf ownerOf_eq_some uavg_restrict_injective
  uavg_not_injective_le)
open Quantum.Qrom.SufCma.Multi (generateAll)

namespace Quantum.Qrom.Xmss.Multi

/-! ## Prefixes -/

/-- The slots hashed under the public parameter: all but the parameter's and the scheme seed's
derivations. -/
def prefixedSlot : Slot → Bool
  | .param => false
  | .seed => false
  | _ => true

/-- **The prefix of an input**: bytes `0` to `15` of a prefixed slot's input. -/
def prefixOf (x : HashDomain) : Option PublicParameter :=
  (slotOf x).bind fun s ↦ if prefixedSlot s then some (sliceBits (decodeInput x) 0 128) else none

theorem sliceBits_thInput_prefix (Q : PublicParameter) (fields : TweakFields)
    (payload : HashInput) : sliceBits (thInput Q fields payload) 0 128 = Q :=
  sliceBits_eq fun j hj ↦ by rw [zero_add, inputBit_thInput_prefix _ _ _ _ hj]

/-- **A prefixed slot's input starts with the public parameter.** -/
theorem sliceBits_cell (P : PublicParameter) {s : Slot} (hs : prefixedSlot s = true)
    (d : Payload s) : sliceBits (decodeInput (cell P s d)) 0 128 = P := by
  rw [decodeInput_cell]
  cases s <;> first
    | exact absurd hs (by decide)
    | exact sliceBits_thInput_prefix _ _ _

theorem prefixOf_cell (P : PublicParameter) {s : Slot} (hs : Addressable s)
    (hp : prefixedSlot s = true) (d : Payload s) : prefixOf (cell P s d) = some P := by
  rw [prefixOf, slotOf_cell P hs d, Option.bind_some, ite_eq_left hp, sliceBits_cell P hp]

theorem prefixOf_cell_eq_none (P : PublicParameter) {s : Slot} (hs : Addressable s)
    (hp : prefixedSlot s = false) (d : Payload s) : prefixOf (cell P s d) = none := by
  rw [prefixOf, slotOf_cell P hs d, Option.bind_some,
    ite_eq_right (show ¬(prefixedSlot s = true) by simp [hp])]

theorem prefixedSlot_slot {p : Pos} (h1 : p ≠ .seed) (h2 : p ≠ .param) :
    prefixedSlot p.slot = true := by
  cases p <;> simp_all [Pos.slot, prefixedSlot]

theorem Pos.eq_seed_of_slot {p : Pos} (h : p.slot = .seed) : p = .seed := by
  cases p <;> simp_all [Pos.slot]

theorem Pos.eq_param_of_slot {p : Pos} (h : p.slot = .param) : p = .param := by
  cases p <;> simp_all [Pos.slot]

/-! ## Positions and values of `n` users -/

/-- **The positions of `n` users**: a user and a single-user position. -/
abbrev PosN (n : ℕ) := Fin n × Pos

/-- The honest values of `n` users. -/
abbrev QTableN (n : ℕ) := PosN n → HashOutput

namespace QTableN

variable {n : ℕ} (w : QTableN n)

/-- User `i`'s values. -/
def user (i : Fin n) : QTable := fun p ↦ w (i, p)

/-- The users' public parameters. -/
def params : Fin n → PublicParameter := fun i ↦ (w.user i).param

/-- The users' scheme seeds. -/
def seeds : Fin n → MasterSeed := fun i ↦ (w.user i).seed

end QTableN

variable {n : ℕ}

/-- **Distinct public parameters.** -/
def PDistinct (w : QTableN n) : Prop :=
  Function.Injective w.params

/-- **The cell of a position of user `i`**: the single-user cell at `S0 i` and `i`'s values. -/
def cellOfN (S0 : Fin n → MasterSeed) (a : PosN n) (w : QTableN n) : HashDomain :=
  cellOf (S0 a.1) a.2 (w.user a.1)

/-- Equal cells of two users' positions belong to the same user, when master seeds, scheme seeds
and public parameters are distinct. -/
theorem user_eq_of_cellOfN_eq {S0 : Fin n → MasterSeed} {w : QTableN n}
    (hS0 : Function.Injective S0) (hS : Function.Injective w.seeds) (hP : PDistinct w)
    {i j : Fin n} {p q : Pos} (h : cellOfN S0 (i, p) w = cellOfN S0 (j, q) w) : i = j := by
  have hslot : p.slot = q.slot := Option.some.inj ((slotOf_cellOf _ _ p).symm.trans
    ((congrArg slotOf h).trans (slotOf_cellOf _ _ q)))
  by_cases hp1 : p = .seed
  · subst hp1
    obtain rfl := Pos.eq_seed_of_slot hslot.symm
    have h' : cell (w.params i) .seed (S0 i) = cell (w.params i) .seed (S0 j) :=
      h.trans (cell_seed_eq _ _ _)
    exact hS0 (eq_of_heq (Sigma.mk.inj (cell_injective _ (addressable_slot .seed)
      (addressable_slot .seed) h')).2)
  by_cases hp2 : p = .param
  · subst hp2
    obtain rfl := Pos.eq_param_of_slot hslot.symm
    have h' : cell (w.params i) .param (w.seeds i) = cell (w.params i) .param (w.seeds j) :=
      h.trans (cell_param_eq _ _ _)
    exact hS (eq_of_heq (Sigma.mk.inj (cell_injective _ (addressable_slot .param)
      (addressable_slot .param) h')).2)
  have hq1 : q ≠ .seed := fun hq ↦
    hp1 (Pos.eq_seed_of_slot (hslot.trans (by rw [hq]; rfl : q.slot = .seed)))
  have hq2 : q ≠ .param := fun hq ↦
    hp2 (Pos.eq_param_of_slot (hslot.trans (by rw [hq]; rfl : q.slot = .param)))
  have e := congrArg (fun x ↦ sliceBits (decodeInput x) 0 128) h
  simp only [cellOfN, cellOf] at e
  rw [sliceBits_cell _ (prefixedSlot_slot hp1 hp2), sliceBits_cell _ (prefixedSlot_slot hq1 hq2)]
    at e
  exact hP e

/-- **Multi-user domain separation**: with distinct master seeds, scheme seeds and public
parameters, distinct positions of all users hash distinct inputs. -/
theorem cellN_injective_of {S0 : Fin n → MasterSeed} {w : QTableN n}
    (hS0 : Function.Injective S0) (hS : Function.Injective w.seeds) (hP : PDistinct w) :
    Function.Injective fun a : PosN n ↦ cellOfN S0 a w := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  obtain rfl := user_eq_of_cellOfN_eq hS0 hS hP h
  exact Prod.ext rfl ((table (S0 i)).inj (w.user i) h)

/-- **The owner of a prefixed cell of user `i`** is `i`, with distinct public parameters. -/
theorem ownerOf_cellOfN {w : QTableN n} (hP : PDistinct w) (S0 : Fin n → MasterSeed) (i : Fin n)
    {p : Pos} (h1 : p ≠ .seed) (h2 : p ≠ .param) :
    ownerOf w.params prefixOf (cellOfN S0 (i, p) w) = some i :=
  ownerOf_eq_some hP (prefixOf_cell _ (addressable_slot p) (prefixedSlot_slot h1 h2) _)

/-! ## The table of `n` users -/

/-- The good tables: injective cells and distinct public parameters. -/
def goodN (S0 : Fin n → MasterSeed) (w : QTableN n) : Prop :=
  (Function.Injective fun a : PosN n ↦ cellOfN S0 a w) ∧ PDistinct w

theorem goodN_of {S0 : Fin n → MasterSeed} {w : QTableN n} (hS0 : Function.Injective S0)
    (hS : Function.Injective w.seeds) (hP : PDistinct w) : goodN S0 w :=
  ⟨cellN_injective_of hS0 hS hP, hP⟩

/-- **The honest table of `n` users at the master seeds `S0`**: cells `cellOfN S0`, ordered by
rank, good on `goodN S0`. -/
def tableN (S0 : Fin n → MasterSeed) : LazyTableOn (PosN n) HashDomain HashOutput where
  cell := cellOfN S0
  pre a b := a.2.rank < b.2.rank
  wf := (measure fun a : PosN n ↦ a.2.rank).wf
  dep a _ _ h := cellOf_congr (S0 a.1) fun q hq ↦ h (a.1, q) hq
  good := goodN S0
  inj _ h := h.1

noncomputable instance instDecidablePredGoodTableN (S0 : Fin n → MasterSeed) :
    DecidablePred (tableN S0).good :=
  Classical.decPred _

/-- User `i`'s part of the table of `H` is the single-user table of `H` at `S0 i`. -/
theorem user_tab_tableN (S0 : Fin n → MasterSeed) (H : HashDomain → HashOutput) (i : Fin n) :
    QTableN.user ((tableN S0).tab H) i = (table (S0 i)).tab H :=
  ((table (S0 i)).tab_unique fun p ↦ ((tableN S0).tab_eq H (i, p)).symm).symm

theorem tab_tableN_eq_iff {S0 : Fin n → MasterSeed} {H : HashDomain → HashOutput}
    {w : QTableN n} : (tableN S0).tab H = w ↔ ∀ i, Consistent (S0 i) (w.user i) H :=
  ⟨fun h i p ↦ (tableN S0).tab_eq_iff.1 h (i, p),
    fun h ↦ (tableN S0).tab_eq_iff.2 fun a ↦ h a.1 a.2⟩

/-- A function overwritten at the cells of a good `w` by `w` is consistent with every user. -/
theorem consistent_fillN {S0 : Fin n → MasterSeed} {w : QTableN n} (hw : (tableN S0).good w)
    (H : HashDomain → HashOutput) (i : Fin n) :
    Consistent (S0 i) (w.user i) ((tableN S0).fill w w H) :=
  fun p ↦ (tableN S0).fill_cell hw w H (i, p)

/-- **Key generation of all users, run by any implementation answering `H` consistent with every
user**, returns the users' table keys. -/
theorem simulateQ_generateAll {r : Type → Type} [Monad r] [LawfulMonad r]
    {impl : QueryImpl RomOracles r} {H : HashDomain → HashOutput}
    (himpl : ∀ x, impl (.inr x) = pure (H x)) :
    ∀ (n : ℕ) (S0 : Fin n → MasterSeed) (w : QTableN n),
      (∀ i, Consistent (S0 i) (w.user i) H) →
      simulateQ impl (generateAll xmssRom n S0) =
        pure fun i ↦ ((w.user i).publicKey, (w.user i).secretKey (S0 i))
  | 0, S0, w, _ => by
    rw [generateAll, simulateQ_pure]
    exact congrArg pure (funext fun i ↦ i.elim0)
  | n + 1, S0, w, hw => by
    rw [generateAll, simulateQ_bind, QTable.simulateQ_generateKeys (hw 0) himpl, pure_bind,
      simulateQ_bind, simulateQ_generateAll himpl n (S0 ∘ Fin.succ) (fun a ↦ w (a.1.succ, a.2))
        fun i ↦ hw i.succ, pure_bind, simulateQ_pure]
    refine congrArg pure (funext fun i ↦ ?_)
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [Fin.cons_zero]
    · rw [Fin.cons_succ]
      rfl

/-! ## The collision bound -/

theorem inv_card_mul_card_filter_not_eq_uavg {Θ : Type*} [Fintype Θ] (G : Θ → Prop)
    [DecidablePred G] :
    (Fintype.card Θ : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun θ ↦ ¬G θ).card =
      uavg (fun θ ↦ if G θ then (0 : ℝ≥0∞) else 1) := by
  unfold uavg
  rw [Finset.card_filter, Nat.cast_sum]
  exact congrArg _ (Finset.sum_congr rfl fun θ _ ↦ by by_cases h : G θ <;> simp [h])

theorem card_filter_eq_le_one {β : Type} [Fintype β] [DecidableEq β] (a : β) :
    (Finset.univ.filter fun b : β ↦ b = a).card ≤ 1 := by
  rw [Finset.filter_eq']
  simp

theorem one_div_card_hashOutput : ((1 : ℕ) : ℝ≥0∞) / Fintype.card HashOutput = (2 ^ 256)⁻¹ := by
  rw [card_hashOutput, Nat.cast_one, one_div, Nat.cast_pow, Nat.cast_ofNat]

/-- Uniform values at injective positions `e` collide with probability at most `C(n,2) 2^-256`. -/
theorem uavg_not_injective_at_le {P : Type} [Fintype P] [DecidableEq P] (e : Fin n → P)
    (he : Function.Injective e) :
    uavg (fun θ : P → HashOutput ↦ if Function.Injective (θ ∘ e) then (0 : ℝ≥0∞) else 1) ≤
      n.choose 2 * (2 ^ 256)⁻¹ := by
  have hr := uavg_restrict_injective e he
    fun u : Fin n → HashOutput ↦ if Function.Injective fun i ↦ u i then (0 : ℝ≥0∞) else 1
  have h := uavg_not_injective_le (n := n) (fun b : HashOutput ↦ b) (c := 1)
    (card_filter_eq_le_one (β := HashOutput))
  rw [one_div_card_hashOutput] at h
  exact hr.trans_le h

/-- Uniform values at injective positions `e` have colliding truncations with probability at
most `C(n,2) 2^-128`. -/
theorem uavg_not_injective_truncate_at_le {P : Type} [Fintype P] [DecidableEq P]
    (e : Fin n → P) (he : Function.Injective e) :
    uavg (fun θ : P → HashOutput ↦
        if Function.Injective fun i ↦ truncateHash (θ (e i)) then (0 : ℝ≥0∞) else 1) ≤
      n.choose 2 * (2 ^ 128)⁻¹ := by
  have hr := uavg_restrict_injective e he
    fun u : Fin n → HashOutput ↦
      if Function.Injective fun i ↦ truncateHash (u i) then (0 : ℝ≥0∞) else 1
  have h := uavg_not_injective_le (n := n) truncateHash (c := 2 ^ 128) card_fiber_truncateHash_le
  rw [fiber_div_card_hashOutput] at h
  exact hr.trans_le h

theorem uavg_const_eq {Θ : Type*} [Fintype Θ] [Nonempty Θ] (c : ℝ≥0∞) :
    uavg (fun _ : Θ ↦ c) = c := by
  unfold uavg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), one_mul]

/-- **The collision bound**: over uniform master seeds and table values, the table of `n` users
is bad with probability at most `C(n,2) (2^-128 + 2 · 2^-256)`. -/
theorem prob_not_goodN_le :
    uavg (fun S0 : Fin n → MasterSeed ↦ (Fintype.card (QTableN n) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun w ↦ ¬(tableN S0).good w).card) ≤
      n.choose 2 * ((2 ^ 128 : ℝ≥0∞)⁻¹ + 2 * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
  have hS0 := uavg_not_injective_at_le (P := Fin n) (n := n) id Function.injective_id
  have hseed := uavg_not_injective_at_le (P := PosN n) (n := n) (fun i ↦ (i, Pos.seed))
    fun _ _ h ↦ (Prod.mk.inj h).1
  have hpar := uavg_not_injective_truncate_at_le (P := PosN n) (n := n) (fun i ↦ (i, Pos.param))
    fun _ _ h ↦ (Prod.mk.inj h).1
  have hpt : ∀ (S0 : Fin n → MasterSeed) (w : QTableN n),
      (if (tableN S0).good w then (0 : ℝ≥0∞) else 1) ≤
        (if Function.Injective (S0 ∘ id) then (0 : ℝ≥0∞) else 1) +
          (if Function.Injective (w ∘ fun i ↦ (i, Pos.seed)) then (0 : ℝ≥0∞) else 1) +
          (if Function.Injective fun i ↦ truncateHash (w (i, Pos.param)) then (0 : ℝ≥0∞)
            else 1) := fun S0 w ↦ by
    by_cases h1 : Function.Injective (S0 ∘ id)
    · by_cases h2 : Function.Injective (w ∘ fun i ↦ (i, Pos.seed))
      · by_cases h3 : Function.Injective fun i ↦ truncateHash (w (i, Pos.param))
        · rw [ite_eq_left (show (tableN S0).good w from goodN_of (S0 := S0) (w := w) h1 h2 h3)]
          exact zero_le
        · rw [ite_eq_right h3]
          split_ifs <;> simp
      · rw [ite_eq_right h2]
        split_ifs <;> simp
    · rw [ite_eq_right h1]
      split_ifs <;> simp
  have hw : ∀ S0 : Fin n → MasterSeed,
      (Fintype.card (QTableN n) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun w ↦ ¬(tableN S0).good w).card ≤
        (if Function.Injective (S0 ∘ id) then (0 : ℝ≥0∞) else 1) +
          n.choose 2 * (2 ^ 256)⁻¹ + n.choose 2 * (2 ^ 128)⁻¹ := fun S0 ↦ by
    rw [inv_card_mul_card_filter_not_eq_uavg]
    refine (uavg_mono (hpt S0)).trans ?_
    rw [uavg_add, uavg_add]
    exact add_le_add (add_le_add (uavg_const_eq _).le hseed) hpar
  refine (uavg_mono hw).trans ?_
  rw [uavg_add, uavg_add, uavg_const_eq, uavg_const_eq]
  calc uavg (fun S0 : Fin n → MasterSeed ↦
          if Function.Injective (S0 ∘ id) then (0 : ℝ≥0∞) else 1) +
        n.choose 2 * (2 ^ 256)⁻¹ + n.choose 2 * (2 ^ 128)⁻¹
      ≤ n.choose 2 * (2 ^ 256)⁻¹ + n.choose 2 * (2 ^ 256)⁻¹ + n.choose 2 * (2 ^ 128)⁻¹ := by
        gcongr
    _ = n.choose 2 * ((2 ^ 128 : ℝ≥0∞)⁻¹ + 2 * (2 ^ 256 : ℝ≥0∞)⁻¹) := by ring

end Quantum.Qrom.Xmss.Multi

end
