module

public import Quantum.Qrom.TableLawOn
public import Quantum.Qrom.MultiUser.Owner
public import Quantum.Qrom.Sphincs.Hybrid
public import Quantum.Qrom.SufCma.MultiGame

@[expose] public section

/-!
# leanSPHINCS's honest table for `n` users

User `i` has master seed `S0 i` and the single-user honest table (`Quantum.Qrom.Sphincs.table`)
at the positions `(i, p)`; together the positions `PosN n = Fin n × Pos` and values
`QTableN n = PosN n → PairOut`.

* **Prefixes.** `prefixS x` reads the `PK.seed` field of an input by its length: bytes `16..31`
  of an `H_msg` call, `32..47` of `PRF_msg`, none for the key expansion, else bytes `0..15`.
  Every position's cell but the key expansion's carries its table's `PK.seed`
  (`prefixS_cellOf`); every input `slotOf pk` reads at a prefixed slot carries `pk.publicSeed`
  (`prefixS_of_slotOf`).
* **Domain separation** (`cellN_injective_of`): with distinct master seeds and distinct
  `PK.seed`s (`PDistinct`), the cells of all users' positions are pairwise distinct;
  `ownerOf_cellOfN`: the owner of a non-expansion cell of user `i` is `i`.
* `tableN S0`: the `LazyTableOn (PosN n) HashDomain PairOut`, good on `goodN`;
  `user_tab_tableN`, `tab_tableN_eq_iff`, `consistent_fillN`. `simulateQ_generateAll`: against
  a function agreeing with every user, the key generation of all users returns the tables' keys.
-/

open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (keyDerivationInput)
open Quantum.Sphincs (Slot prfMessageInput length_prfMessageInput length_keyDerivationInput
  keyDerivationInput_injective)
open Quantum.Xmss (length_littleEndianBytes)
open Quantum.Qrom.MultiUser (ownerOf ownerOf_eq_some)
open Quantum.Qrom.SufCma.Multi (generateAll)

namespace Quantum.Qrom.Sphincs.Multi

attribute [local irreducible] sphincsRom

/-! ## Prefixes -/

/-- The `PK.seed` field of an input, by kind: bytes 16..31 of an `H_msg` call (84 bytes), bytes
32..47 of `PRF_msg` (93 bytes), none for the key expansion (44 bytes), else bytes 0..15. -/
def prefixS (x : HashDomain) : Option PublicParameter :=
  if (decodeInput x).length = 84 then some (leAt (decodeInput x) 16 16)
  else if (decodeInput x).length = 93 then some (leAt (decodeInput x) 32 16)
  else if (decodeInput x).length = 44 then none
  else some (leAt (decodeInput x) 0 16)

/-- The key-expansion positions (inputs `leanSPHINCS ‖ SK.seed ‖ 0/1`, no `PK.seed`). -/
def IsExpandPos (p : Pos) : Prop :=
  p.1 = .prfKey ∨ p.1 = .publicSeed

instance instDecidablePredIsExpandPos : DecidablePred IsExpandPos := fun p ↦
  inferInstanceAs (Decidable (p.1 = .prfKey ∨ p.1 = .publicSeed))

/-- Slots whose inputs carry `PK.seed` where `slotOfInput pk` checks it. -/
def PrefixedSlot : Slot → Prop
  | .prfMsg _ => False
  | .expand _ => False
  | _ => True

theorem prefixedSlot_chain (l τ e i step) : PrefixedSlot (.chain l τ e i step) := trivial
theorem prefixedSlot_leaf (l τ e) : PrefixedSlot (.leaf l τ e) := trivial
theorem prefixedSlot_node (l τ h j) : PrefixedSlot (.node l τ h j) := trivial
theorem prefixedSlot_enc (l τ e) : PrefixedSlot (.enc l τ e) := trivial
theorem prefixedSlot_forsLeaf (idx κ s) : PrefixedSlot (.forsLeaf idx κ s) := trivial
theorem prefixedSlot_forsNode (idx κ h j) : PrefixedSlot (.forsNode idx κ h j) := trivial
theorem prefixedSlot_forsRoots (idx) : PrefixedSlot (.forsRoots idx) := trivial
theorem prefixedSlot_prf (d) : PrefixedSlot (.prf d) := trivial
theorem prefixedSlot_hmsg (R M c) : PrefixedSlot (.hmsg R M c) := trivial

/-- **An input read at a prefixed slot under `pk` carries `pk`'s `PK.seed`.** -/
theorem prefixS_of_slotOf {pk : PublicKey} {x : HashDomain} {s : Slot}
    (h : slotOf pk x = some s) (hs : PrefixedSlot s) : prefixS x = some pk.publicSeed := by
  unfold slotOf slotOfInput at h
  unfold prefixS
  by_cases h84 : (decodeInput x).length = 84
  · rw [ite_eq_left h84] at h ⊢
    unfold hmsgSlotOf at h
    by_cases hc : leAt (decodeInput x) 16 16 = pk.publicSeed ∧
        leDigest (decodeInput x) 32 = pk.root
    · exact congrArg some hc.1
    · rw [ite_eq_right hc] at h
      exact nomatch h
  rw [ite_eq_right h84] at h ⊢
  by_cases h93 : (decodeInput x).length = 93
  · rw [ite_eq_left h93] at h
    obtain rfl := Option.some.inj h
    exact False.elim hs
  rw [ite_eq_right h93] at h ⊢
  by_cases h44 : (decodeInput x).length = 44
  · rw [ite_eq_left h44] at h
    obtain rfl := Option.some.inj h
    exact False.elim hs
  rw [ite_eq_right h44] at h ⊢
  by_cases hc : leAt (decodeInput x) 0 16 = pk.publicSeed
  · exact congrArg some hc
  · rw [ite_eq_right hc] at h
    exact nomatch h

theorem decodeInput_cellOfS (S0 : MasterSeed) (v : QTable) (p : Pos) :
    decodeInput (cellOf S0 p v) = posInput S0 v p.1 :=
  decodeInput_of_encodeInput_eq_some (encodeInput_posInput S0 v p)

/-- A key-expansion cell codes `leanSPHINCS ‖ S0 ‖ d`. -/
theorem decodeInput_cellOf_expand (S0 : MasterSeed) (v : QTable) {p : Pos}
    (hp : IsExpandPos p) : ∃ d, decodeInput (cellOf S0 p v) = keyDerivationInput S0 d := by
  obtain ⟨p, hp'⟩ := p
  rcases hp with h | h
  · obtain rfl : p = .prfKey := h
    exact ⟨1, decodeInput_cellOfS S0 v _⟩
  · obtain rfl : p = .publicSeed := h
    exact ⟨0, decodeInput_cellOfS S0 v _⟩

/-- **Every cell but the key expansion's carries the table's `PK.seed`.** -/
theorem prefixS_cellOf (S0 : MasterSeed) (v : QTable) {p : Pos} (hp : ¬IsExpandPos p) :
    prefixS (cellOf S0 p v) = some v.publicSeed := by
  obtain ⟨p, hp'⟩ := p
  cases p with
  | prfKey => exact absurd (Or.inl rfl) hp
  | publicSeed => exact absurd (Or.inr rfl) hp
  | prfMsg m =>
    have hd : decodeInput (cellOf S0 ⟨.prfMsg m, hp'⟩ v) =
        prfMessageInput v.prfKey v.publicSeed m :=
      decodeInput_cellOfS S0 v _
    have hl : (prfMessageInput v.prfKey v.publicSeed m).length = 93 :=
      length_prfMessageInput _ _ _
    rw [prefixS, hd, hl, ite_eq_right (show ¬(93 = 84) by decide), ite_eq_left rfl]
    exact congrArg some (leAt_of_prefix (List.prefix_append _ _) (length_littleEndianBytes _ _))
  | _ =>
    exact prefixS_of_slotOf (slotOf_cell (v.expandedKey S0) v.root
      (slotInRange_posSlot v ⟨_, hp'⟩) _) trivial

theorem prefixS_cellOf_expand (S0 : MasterSeed) (v : QTable) {p : Pos} (hp : IsExpandPos p) :
    prefixS (cellOf S0 p v) = none := by
  obtain ⟨d, hd⟩ := decodeInput_cellOf_expand S0 v hp
  rw [prefixS, hd, length_keyDerivationInput, ite_eq_right (show ¬(44 = 84) by decide),
    ite_eq_right (show ¬(44 = 93) by decide), ite_eq_left rfl]

/-- Equal key-expansion cells have equal master seeds. -/
theorem cellOf_expand_eq {S0 S0' : MasterSeed} {v v' : QTable} {p : Pos} (hp : IsExpandPos p)
    (h : cellOf S0 p v = cellOf S0' p v') : S0 = S0' := by
  obtain ⟨d, hd⟩ := decodeInput_cellOf_expand S0 v hp
  obtain ⟨d', hd'⟩ := decodeInput_cellOf_expand S0' v' hp
  exact (keyDerivationInput_injective (hd.symm.trans ((congrArg decodeInput h).trans hd'))).1

/-! ## Positions and values of `n` users -/

/-- **The positions of `n` users**: a user and a single-user position. -/
abbrev PosN (n : ℕ) : Type := Fin n × Pos

/-- The honest values of `n` users. -/
abbrev QTableN (n : ℕ) : Type := PosN n → PairOut

variable {n : ℕ}

/-- User `i`'s values. -/
def QTableN.user (w : QTableN n) (i : Fin n) : QTable := fun p ↦ w (i, p)

/-- The users' public keys. -/
def QTableN.pks (w : QTableN n) : Fin n → PublicKey := fun i ↦ (w.user i).publicKey

/-- Distinct `PK.seed`s. -/
def PDistinct (w : QTableN n) : Prop :=
  Function.Injective fun i ↦ (w.user i).publicSeed

theorem card_publicParameterS : Fintype.card PublicParameter = 2 ^ 128 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

/-- Distinct `PK.seed`s number at most `2^128`. -/
theorem le_of_pDistinctS {w : QTableN n} (h : PDistinct w) : n ≤ 2 ^ 128 := by
  have hc := Fintype.card_le_of_injective _ h
  rwa [Fintype.card_fin, card_publicParameterS] at hc

/-- **The cell of a position of user `i`**: the single-user cell at `S0 i` and `i`'s values. -/
def cellOfN (S0 : Fin n → MasterSeed) (a : PosN n) (w : QTableN n) : HashDomain :=
  cellOf (S0 a.1) a.2 (w.user a.1)

/-- **Multi-user domain separation**: with distinct master seeds and `PK.seed`s, distinct
positions of all users hash distinct inputs. -/
theorem cellN_injective_of {S0 : Fin n → MasterSeed} {w : QTableN n}
    (hS0 : Function.Injective S0) (hP : PDistinct w) :
    Function.Injective fun a : PosN n ↦ cellOfN S0 a w := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  have h' : cellOf (S0 i) p (w.user i) = cellOf (S0 j) q (w.user j) := h
  obtain rfl : p = q := pos_eq_of_cellOf_eq h'
  by_cases hp : IsExpandPos p
  · rw [hS0 (cellOf_expand_eq hp h')]
  · have e := congrArg prefixS h'
    rw [prefixS_cellOf _ _ hp, prefixS_cellOf _ _ hp] at e
    rw [hP (Option.some.inj e)]

/-- **The owner of a non-expansion cell of user `i`** is `i`, with distinct `PK.seed`s. -/
theorem ownerOf_cellOfN {w : QTableN n} (hP : PDistinct w) (S0 : Fin n → MasterSeed) (i : Fin n)
    {p : Pos} (hp : ¬IsExpandPos p) :
    ownerOf (fun j ↦ (w.user j).publicSeed) prefixS (cellOfN S0 (i, p) w) = some i :=
  ownerOf_eq_some hP (prefixS_cellOf (S0 i) (w.user i) hp)

/-! ## The table of `n` users -/

/-- The good tables: injective cells and distinct `PK.seed`s. -/
def goodN (S0 : Fin n → MasterSeed) (w : QTableN n) : Prop :=
  (Function.Injective fun a : PosN n ↦ cellOfN S0 a w) ∧ PDistinct w

theorem goodN_of {S0 : Fin n → MasterSeed} {w : QTableN n} (hS0 : Function.Injective S0)
    (hP : PDistinct w) : goodN S0 w :=
  ⟨cellN_injective_of hS0 hP, hP⟩

/-- **The honest table of `n` users at the master seeds `S0`**: cells `cellOfN S0`, ordered by
rank, good on `goodN S0`. -/
def tableN (S0 : Fin n → MasterSeed) : LazyTableOn (PosN n) HashDomain PairOut where
  cell := cellOfN S0
  pre a b := a.2.1.rank < b.2.1.rank
  wf := (measure fun a : PosN n ↦ a.2.1.rank).wf
  dep a _ _ h := cellOf_congr (S0 a.1) fun q hq ↦ h (a.1, q) hq
  good := goodN S0
  inj _ h := h.1

noncomputable instance instDecidablePredGoodTableN (S0 : Fin n → MasterSeed) :
    DecidablePred (tableN S0).good :=
  Classical.decPred _

/-- User `i`'s part of the table of `F` is the single-user table of `F` at `S0 i`. -/
theorem user_tab_tableN (S0 : Fin n → MasterSeed) (F : HashDomain → PairOut) (i : Fin n) :
    QTableN.user ((tableN S0).tab F) i = (table (S0 i)).tab F :=
  ((table (S0 i)).tab_unique fun p ↦ ((tableN S0).tab_eq F (i, p)).symm).symm

theorem tab_tableN_eq_iff {S0 : Fin n → MasterSeed} {F : HashDomain → PairOut}
    {w : QTableN n} : (tableN S0).tab F = w ↔ ∀ i, Consistent (S0 i) (w.user i) F :=
  ⟨fun h i p ↦ (tableN S0).tab_eq_iff.1 h (i, p),
    fun h ↦ (tableN S0).tab_eq_iff.2 fun a ↦ h a.1 a.2⟩

/-- A function overwritten at the cells of a good `w` by `w` is consistent with every user. -/
theorem consistent_fillN {S0 : Fin n → MasterSeed} {w : QTableN n} (hw : (tableN S0).good w)
    (F : HashDomain → PairOut) (i : Fin n) :
    Consistent (S0 i) (w.user i) ((tableN S0).fill w w F) :=
  fun p ↦ (tableN S0).fill_cell hw w F (i, p)

/-- **Key generation of all users, run by any implementation answering `H`, agreeing with every
user**, returns the users' table keys. -/
theorem simulateQ_generateAll {r : Type → Type} [Monad r] [LawfulMonad r]
    {impl : QueryImpl RomOracles r} {H : HashDomain → HashOutput}
    (himpl : ∀ x, impl (.inr x) = pure (H x)) :
    ∀ (n : ℕ) (S0 : Fin n → MasterSeed) (w : QTableN n), (∀ i, Agrees (S0 i) (w.user i) H) →
      simulateQ impl (generateAll sphincsRom n S0) = pure fun i ↦ ((w.user i).publicKey, S0 i)
  | 0, S0, w, _ => by
    rw [generateAll, simulateQ_pure]
    exact congrArg pure (funext fun i ↦ i.elim0)
  | n + 1, S0, w, hw => by
    rw [generateAll, simulateQ_bind, simulateQ_generateKeys_eq impl (hw 0) fun x _ ↦ himpl x,
      pure_bind, simulateQ_bind,
      simulateQ_generateAll himpl n (S0 ∘ Fin.succ) (fun a ↦ w (a.1.succ, a.2))
        fun i ↦ hw i.succ, pure_bind, simulateQ_pure]
    refine congrArg pure (funext fun i ↦ ?_)
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [Fin.cons_zero]
    · rw [Fin.cons_succ]
      rfl

end Quantum.Qrom.Sphincs.Multi

end
