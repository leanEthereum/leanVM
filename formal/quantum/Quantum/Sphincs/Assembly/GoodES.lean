module

public import Quantum.Sphincs.Assembly.EventSide

@[expose] public section

/-!
# leanSPHINCS's good event-side data, averaged over all data

EventSide's `uavg_p2R_le_es` pays twice the fraction of the data `θ = ((k, k'), v)` off the good set
`GoodES par perm hk`. Here that fraction is bounded averaged over all the data
`ω = ((PK.seed, π, h), ((k, k'), v))` (`FullES`), condition by condition.

* **Splitting the hidden values** (`valSplit`, `rawEquiv`, `disjEquiv`): the values at the
  positions and the rest, so the static conditions of the raw data `((h, w), valsOf v)` (PathBad's
  coordinates) average as there (`uavg_rawEquiv`, `uavg_disjEquiv`).
* **`PK.seed` against the addresses** (`adrsSeed`, `seedBadSet`): bytes `16` to `31` of an
  in-table slot's first block are the first half of its address, of an `H_msg` block `PK.seed`
  (`rateSlice_slotBlk_inTable`, `rateSlice_slotBlk_hmsg`). So ProgSafe's `NoHmsgHead` fails, and
  an `H_msg` block is an in-table first block, only if `PK.seed` is in `seedBadSet`, the first
  halves of the at most `2^47` in-table addresses (`seed_mem_of_not_noHmsgHead`,
  `uavg_seedBad_le`: `2^-81`).
* **`HmsgSep`** (`HmsgSepR`, `exists_rnd_of_not_hmsgSepR`, `hmsgSepR_frac_le_keccak`): off
  `seedBadSet`, a violation is a later round's `k`-cell among the at most `2^641` `H_msg` blocks
  (`hmsgSet`), counted as TrialsOff's trial blocks: `2^-396`.
* **The key conditions** (`uavg_pair_ite_le`, `uavg_hZLoad_le`, `uavg_hSelfSep_le`): HConflict's
  card forms normalized, `2^-639` and `2^-128`.
* **The bound** (`uavg_not_goodES_le`): the fraction of all data off `GoodES` is at most
  `goodESCap` plus the fraction off `HmsgHSep`.
-/

open scoped ENNReal

open Quantum Quantum.Sponge Quantum.SufCma Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer HashInput littleEndianBytes)
open Quantum.Xmss (X Z blocks blockOf firstBlock rateSlice inputBit length_littleEndianBytes
  absorbTail_blocks)
open Quantum.Xmss.Hybrid (uavg uavg_mono uavg_add uavg_ite_zero_one natCast_le_mul_div_of_mul_le)
open Quantum.Xmss.Assembly (rnK famK rnds mem_rnds rnK_zero frac_pathTrial_le XW
  card_filter_le_add_of_imp inv_card_mul_card_filter_comp_fst natCast_div_eq_ofReal rnCard_X
  rnCard_Z permTerm_le_keccak card_prod_four card_publicParameter card_digest uavg_const_le
  uavg_const)

namespace Quantum.Sphincs.Assembly

/- Instance search for `Fintype` of the products of all data exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## The data and the split of the hidden values -/

section split

/-- The hidden coordinates at the positions. -/
def isValPos : HPos → Bool
  | .val _ => true
  | _ => false

/-- The hidden values off the positions. -/
abbrev HRest : Type :=
  (s : {s : HPos // isValPos s = false}) → XD s.1

/-- Hidden values from the values at the positions and the rest. -/
def valJoin (f : ValPos → Digest) (r : HRest) : (s : HPos) → XD s
  | .val p => f p
  | .rnd M => r ⟨.rnd M, rfl⟩
  | .dig M i => r ⟨.dig M i, rfl⟩
  | .str j i => r ⟨.str j i, rfl⟩
  | .asg M j => r ⟨.asg M j, rfl⟩

/-- **The hidden values as the values at the positions and the rest.** -/
def valSplit : ((s : HPos) → XD s) ≃ (ValPos → Digest) × HRest where
  toFun v := (valsOf v, fun s ↦ v s.1)
  invFun w := valJoin w.1 w.2
  left_inv v := funext fun s ↦ by cases s <;> rfl
  right_inv w := by
    refine Prod.ext (funext fun _ ↦ rfl) (funext fun s ↦ ?_)
    obtain ⟨s, hs⟩ := s
    cases s with
    | val p => simp [isValPos] at hs
    | rnd M => rfl
    | dig M i => rfl
    | str j i => rfl
    | asg M j => rfl

/-- **All the data of the event side**: `PK.seed`, `π`, `h`, the keys `(k, k')` and the hidden
values. -/
abbrev FullES : Type :=
  (PublicParameter × Equiv.Perm (X × Z) × (Z → X)) × (((X → Z) × (X → Z)) × ((s : HPos) → XD s))

/-- The data as PathBad's raw coordinates `((h, w), valsOf v)` and the rest. -/
def rawEquiv : FullES ≃ (((Z → X) × XW) × (ValPos → Digest)) × HRest where
  toFun ω := (((ω.1.2.2, (ω.1.1, ω.1.2.1, ω.2.1.1, ω.2.1.2)), (valSplit ω.2.2).1),
    (valSplit ω.2.2).2)
  invFun y := ((y.1.1.2.1, y.1.1.2.2.1, y.1.1.1),
    ((y.1.1.2.2.2.1, y.1.1.2.2.2.2), valSplit.symm (y.1.2, y.2)))
  left_inv ω := by
    obtain ⟨⟨P, π, h⟩, ⟨k, k'⟩, v⟩ := ω
    show ((P, π, h), ((k, k'), valSplit.symm ((valSplit v).1, (valSplit v).2))) =
      ((P, π, h), ((k, k'), v))
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv y := by
    obtain ⟨⟨⟨h, P, π, k, k'⟩, f⟩, r⟩ := y
    show (((h, (P, π, k, k')), (valSplit (valSplit.symm (f, r))).1),
      (valSplit (valSplit.symm (f, r))).2) = (((h, (P, π, k, k')), f), r)
    rw [Equiv.apply_symm_apply]

/-- The data as PathsDisjoint's coordinates `(((h, w), rest), valsOf v)`. -/
def disjEquiv : FullES ≃ (((Z → X) × XW) × HRest) × (ValPos → Digest) where
  toFun ω := (((ω.1.2.2, (ω.1.1, ω.1.2.1, ω.2.1.1, ω.2.1.2)), (valSplit ω.2.2).2),
    (valSplit ω.2.2).1)
  invFun y := ((y.1.1.2.1, y.1.1.2.2.1, y.1.1.1),
    ((y.1.1.2.2.2.1, y.1.1.2.2.2.2), valSplit.symm (y.2, y.1.2)))
  left_inv ω := by
    obtain ⟨⟨P, π, h⟩, ⟨k, k'⟩, v⟩ := ω
    show ((P, π, h), ((k, k'), valSplit.symm ((valSplit v).1, (valSplit v).2))) =
      ((P, π, h), ((k, k'), v))
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv y := by
    obtain ⟨⟨⟨h, P, π, k, k'⟩, r⟩, f⟩ := y
    show (((h, (P, π, k, k')), (valSplit (valSplit.symm (f, r))).2),
      (valSplit (valSplit.symm (f, r))).1) = (((h, (P, π, k, k')), r), f)
    rw [Equiv.apply_symm_apply]

/-- **A function of the raw coordinates averages as on them.** -/
theorem uavg_rawEquiv (F : ((Z → X) × XW) × (ValPos → Digest) → ℝ≥0∞) :
    uavg (fun ω : FullES ↦ F (rawEquiv ω).1) = uavg F :=
  (uavg_comp_equiv rawEquiv fun y ↦ F y.1).trans (uavg_fst_marg F)

theorem uavg_disjEquiv (F : (((Z → X) × XW) × HRest) × (ValPos → Digest) → ℝ≥0∞) :
    uavg (fun ω : FullES ↦ F (disjEquiv ω)) = uavg F :=
  uavg_comp_equiv disjEquiv F

/-- **A function of `PK.seed` averages as over `PK.seed`.** -/
theorem uavg_seed (F : PublicParameter → ℝ≥0∞) :
    uavg (fun ω : FullES ↦ F ω.1.1) = uavg F :=
  (uavg_fst_marg (fun o : PublicParameter × Equiv.Perm (X × Z) × (Z → X) ↦ F o.1)).trans
    (uavg_fst_marg F)

/-- **A function of `PK.seed`, `π`, `h` and the keys averages over them.** -/
theorem uavg_le_of_keys {F : PublicParameter → Equiv.Perm (X × Z) → (Z → X) →
    ((X → Z) × (X → Z)) → ℝ≥0∞} {ε : ℝ≥0∞} (h : ∀ P π hk, uavg (F P π hk) ≤ ε) :
    uavg (fun ω : FullES ↦ F ω.1.1 ω.1.2.1 ω.1.2.2 ω.2.1) ≤ ε := by
  rw [uavg_prod_iter]
  refine (uavg_mono fun o ↦ ?_).trans (uavg_const_le ε)
  exact (uavg_fst_marg (F o.1 o.2.1 o.2.2)).trans_le (h _ _ _)

/-- **A function of `PK.seed`, `π`, `h`, the keys and the hidden values averages over the keys at
fixed hidden values.** -/
theorem uavg_le_of_keys_vals {F : PublicParameter → Equiv.Perm (X × Z) → (Z → X) →
    ((X → Z) × (X → Z)) → ((s : HPos) → XD s) → ℝ≥0∞} {ε : ℝ≥0∞}
    (h : ∀ P π hk v, uavg (fun kk ↦ F P π hk kk v) ≤ ε) :
    uavg (fun ω : FullES ↦ F ω.1.1 ω.1.2.1 ω.1.2.2 ω.2.1 ω.2.2) ≤ ε := by
  rw [uavg_prod_iter]
  refine (uavg_mono fun o ↦ ?_).trans (uavg_const_le ε)
  rw [← uavg_comp_equiv (Equiv.prodComm _ _) (fun θ ↦ F o.1 o.2.1 o.2.2 θ.1 θ.2), uavg_prod_iter]
  exact (uavg_mono fun v ↦ h o.1 o.2.1 o.2.2 v).trans (uavg_const_le ε)

end split

/-! ## `PK.seed` against the addresses -/

section seed

/-- **Bytes `16` to `31` of an addressed input's first block**: the first half of the address, read
as `hmsgSlot` reads `PK.seed`. -/
def adrsSeed (a : Address) : PublicParameter :=
  rateSlice (blockOf (firstBlock (addressedHashInput 0 a []))) 128 128 (by norm_num)

theorem addressed_bit (Q : PublicParameter) (a : Address) (payload : HashInput) (j : ℕ)
    (hj : j < 128) :
    blockOf (firstBlock (addressedHashInput Q a payload)) ⟨128 + j, by omega⟩ =
      inputBit a.toBytes j := by
  have h := blockOf_firstBlock_of_prefix (input := addressedHashInput Q a payload)
    (a := littleEndianBytes 16 Q) (b := a.toBytes) ⟨payload, rfl⟩ j
    (by rw [length_toBytes]; omega) (by rw [length_littleEndianBytes, length_toBytes]; omega)
  rw [← h]
  exact congrArg _ (Fin.ext (by simp [length_littleEndianBytes]))

theorem rateSlice_addressed (Q : PublicParameter) (a : Address) (payload : HashInput) :
    rateSlice (blockOf (firstBlock (addressedHashInput Q a payload))) 128 128 (by norm_num) =
      adrsSeed a := by
  unfold adrsSeed rateSlice
  exact congrArg _ (funext fun j ↦
    (addressed_bit Q a payload j j.isLt).trans (addressed_bit 0 a [] j j.isLt).symm)

/-- **Bytes `16` to `31` of an in-table slot's first block** are the first half of its address. -/
theorem rateSlice_slotBlk_inTable (P : PublicParameter) (f : ValPos → Digest) {s : Slot}
    (hs : InTable s) :
    rateSlice (slotBlk P s f 0) 128 128 (by norm_num) =
      adrsSeed (hashDomainFields (slotDomain s)) := by
  rw [slotBlk_zero, slotInput_of_ne (ne_hmsg_of_inTable hs)]
  exact rateSlice_addressed _ _ _

/-- **Bytes `16` to `31` of an `H_msg` block** are `PK.seed`. -/
theorem rateSlice_slotBlk_hmsg (P : PublicParameter) (f : ValPos → Digest) (R : Randomizer)
    (M : Message) (i : DigestCall) :
    rateSlice (slotBlk P (.hmsg R M i) f 0) 128 128 (by norm_num) = P := by
  rw [slotBlk_zero]
  exact rateSlice_firstBlock (a := littleEndianBytes 16 R) (n := 16)
    (by
      show _ <+: messageDigestInput R P (f rootPos) M i
      rw [messageDigestInput]
      simp [List.append_assoc])
    (by simp [littleEndianBytes]) (by norm_num)

/-- **The seeds meeting an in-table address**: the first halves of the in-table addresses. -/
def seedBadSet : Finset PublicParameter :=
  xI.image fun p ↦ adrsSeed (hashDomainFields (slotDomain (outSlot p)))

theorem mem_seedBadSet {s : Slot} (hs : InTable s) :
    adrsSeed (hashDomainFields (slotDomain s)) ∈ seedBadSet :=
  Finset.mem_image.mpr ⟨slotOutPos s, mem_xI.mpr (inPos_slotOutPos hs), by
    rw [outSlot_slotOutPos hs]⟩

theorem card_seedBadSet_le : seedBadSet.card ≤ 2 ^ 47 :=
  Finset.card_image_le.trans card_xI_le

attribute [irreducible] seedBadSet

/-- A one-block tail naming an `H_msg` call whose block names an in-table slot holds `PK.seed` at
bytes `16` to `31`. -/
theorem rateSlice_of_slotOfOneBlock {pk : PublicKey} {x : X} {s : Slot} {R : Randomizer}
    {M : Message} {c : DigestCall} (he : slotOfOneBlock pk x = some (.hmsg R M c))
    (hb : slotOfBlock pk x = some s) (hs : InTable s) :
    rateSlice x 128 128 (by norm_num) = pk.publicSeed := by
  unfold slotOfOneBlock at he
  split_ifs at he with h84 h93 h44
  · unfold hmsgSlot at he
    by_contra hq
    rw [ite_eq_right hq] at he
    exact absurd he (by simp)
  · exact absurd he (by simp)
  · exact absurd he (by simp)
  · rw [hb] at he
    exact absurd (Option.some.inj he) (ne_hmsg_of_inTable hs R M c)

/-- **`NoHmsgHead` fails only at a seed of `seedBadSet`.** -/
theorem seed_mem_of_not_noHmsgHead {pub : Pub} {v : (s : HPos) → XD s}
    (h : ¬NoHmsgHead pub v) : pub.seed ∈ seedBadSet := by
  simp only [NoHmsgHead, not_forall, not_not] at h
  obtain ⟨s, hs, -, R, M, c, he⟩ := h
  obtain ⟨rest, hr, -⟩ := absorbTail_blocks (evData pub v).view (slotInput pub.seed s (valsOf v))
  have ht : (evData pub v).honTail s =
      blockOf (firstBlock (slotInput pub.seed s (valsOf v))) :: rest := hr
  rw [ht, List.take_succ_cons, List.take_zero, slotOf_singleton, ← slotBlk_zero] at he
  have key := rateSlice_of_slotOfOneBlock he
    (slotOfBlock_slotBlk pub.seed (valsOf v rootPos) (valsOf v) hs) hs
  rw [rateSlice_slotBlk_inTable _ _ hs] at key
  have e : (evData pub v).pk.publicSeed = pub.seed := rfl
  rw [e] at key
  rw [← key]
  exact mem_seedBadSet hs

set_option exponentiation.threshold 4096 in
/-- **The seeds of `seedBadSet` are at most `2^-81` of all.** -/
theorem uavg_seedBad_le :
    uavg (fun P : PublicParameter ↦ if P ∉ seedBadSet then (0 : ℝ≥0∞) else 1) ≤
      ENNReal.ofReal (1 / 2 ^ 81) := by
  rw [uavg_ite_zero_one]
  have hf : (Finset.univ.filter fun P : PublicParameter ↦ ¬P ∉ seedBadSet) = seedBadSet := by
    ext P
    simp
  rw [hf, mul_comm, ← div_eq_mul_inv, card_publicParameter,
    natCast_div_eq_ofReal _ _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hc : (seedBadSet.card : ℝ) ≤ 2 ^ 47 := by exact_mod_cast card_seedBadSet_le
  calc (seedBadSet.card : ℝ) / ((2 ^ 128 : ℕ) : ℝ) ≤ 2 ^ 47 / 2 ^ 128 := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact div_le_div_of_nonneg_right hc (by positivity)
    _ = 1 / 2 ^ 81 := by norm_num

end seed

/-! ## `HmsgSep` -/

section hmsgSep

/-- `HmsgSep` on the raw coordinates `(w, h, valsOf v)`. -/
def HmsgSepR (w : XW) (h : Z → X) (f : ValPos → Digest) : Prop :=
  ∀ (R : Randomizer) (M : Message) (i : DigestCall) (s : Slot), InTable s →
    ∀ j < nBlk w.1 s, sCellK w h s f j ≠ slotBlk w.1 (.hmsg R M i) f 0

/-- The block of an `H_msg` call at a seed, root, randomizer, message and call. -/
def hmsgBlkOf (a : PublicParameter × Digest × Randomizer × Message × DigestCall) : X :=
  blockOf (firstBlock (messageDigestInput a.2.2.1 a.1 a.2.1 a.2.2.2.1 a.2.2.2.2))

/-- **The `H_msg` blocks** at every seed, root, randomizer, message and call. -/
def hmsgSet : Finset X :=
  Finset.univ.image hmsgBlkOf

theorem mem_hmsgSet_of (a : PublicParameter × Digest × Randomizer × Message × DigestCall) :
    hmsgBlkOf a ∈ hmsgSet := by
  simp only [hmsgSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨a, rfl⟩

attribute [irreducible] hmsgSet

theorem slotBlk_hmsg_mem (P : PublicParameter) (f : ValPos → Digest) (R : Randomizer)
    (M : Message) (i : DigestCall) : slotBlk P (.hmsg R M i) f 0 ∈ hmsgSet := by
  have e : slotBlk P (.hmsg R M i) f 0 = hmsgBlkOf (P, f rootPos, R, M, i) := by
    rw [slotBlk_zero]
    rfl
  rw [e]
  exact mem_hmsgSet_of (P, f rootPos, R, M, i)

set_option exponentiation.threshold 4096 in
/-- **At most `2^641` `H_msg` blocks.** -/
theorem card_hmsgSet_le : hmsgSet.card ≤ 2 ^ 641 := by
  unfold hmsgSet
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, card_prod_four card_publicParameter card_digest card_randomizer
    card_message_digestCall]
  norm_num

/-- **Off `seedBadSet`, a violation of `HmsgSep` is a later `k`-cell in `hmsgSet`**: a first block
of an in-table slot holds its address at bytes `16` to `31`, an `H_msg` block `PK.seed`. -/
theorem exists_rnd_of_not_hmsgSepR {w : XW} {h : Z → X} {f : ValPos → Digest}
    (hb : ¬HmsgSepR w h f) (hs0 : w.1 ∉ seedBadSet) :
    ∃ a ∈ rnds xI (xLen w.1), 1 ≤ a.2 ∧ famK w.2.1 (xBlk w.1 f) h w.2.2.1 w.2.2.2 a ∈ hmsgSet := by
  simp only [HmsgSepR, not_forall, not_not] at hb
  obtain ⟨R, M, i, s, hs, j, hj, he⟩ := hb
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hs0
    have e : sCellK w h s f 0 = slotBlk w.1 s f 0 := rnK_zero ..
    have h1 := rateSlice_slotBlk_inTable w.1 f hs
    rw [← e, he, rateSlice_slotBlk_hmsg] at h1
    rw [h1]
    exact mem_seedBadSet hs
  refine ⟨(slotOutPos s, j), mem_rnds.mpr ⟨mem_xI.mpr (inPos_slotOutPos hs), ?_⟩,
    Nat.one_le_iff_ne_zero.mpr hj0, ?_⟩
  · show j < nBlk w.1 (outSlot (slotOutPos s))
    rw [outSlot_slotOutPos hs]
    exact hj
  · have e : famK w.2.1 (xBlk w.1 f) h w.2.2.1 w.2.2.2 (slotOutPos s, j) = sCellK w h s f j := by
      show rnK w.2.1 h w.2.2.1 w.2.2.2 (slotBlk w.1 (outSlot (slotOutPos s)) f) j = _
      rw [outSlot_slotOutPos hs]
      rfl
    rw [e, he]
    exact slotBlk_hmsg_mem _ _ _ _ _

open scoped Classical in
/-- **The `HmsgSep` event on good permutations off `seedBadSet`**: at most a fraction
`N² / |X| + N² (G + 1) / |Z| + N |hmsgSet| / |X|` of the raw coordinates, `N = 8 |xI|`. -/
theorem hmsgSepR_good_frac_le (G : ℕ) :
    (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          PermGood y.1.2.2.1 G ∧ (¬HmsgSepR y.1.2 y.1.1 y.2 ∧ y.1.2.1 ∉ seedBadSet)).card ≤
      ((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
        ((8 * xI.card * (8 * xI.card) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
        ((8 * xI.card * hmsgSet.card : ℕ) : ℝ≥0∞) / Fintype.card X :=
  frac_pathTrial_le rnEquiv (fun q ↦ q.2.1) (fun q ↦ xBlk q.1 q.2.2) (fun q ↦ xLen q.1) xI
    (fun q ↦ xBlk_injOn q.1 q.2.2) G _ (fun q ↦ card_rnds_xI_le q.1) hmsgSet _ fun q t hb ↦
      ⟨hb.1, exists_rnd_of_not_hmsgSepR (w := (q.1, q.2.1, t.2.1, t.2.2)) (h := t.1)
        (f := q.2.2) hb.2.1 hb.2.2⟩

set_option exponentiation.threshold 4096 in
/-- The `H_msg`-block term at Keccak's sizes, for `n ≤ 2^47` outputs and at most `2^641` blocks:
`2^691 / 2^1088`. -/
theorem hmsgTerm_le {n m cX : ℕ} (hn : n ≤ 2 ^ 47) (hm : m ≤ 2 ^ 641)
    (hX : cX = 2 ^ 1088) : ((8 * n * m : ℕ) : ℝ≥0∞) / cX ≤ ENNReal.ofReal (1 / 2 ^ 397) := by
  subst hX
  have hK : 8 * n * m ≤ 2 ^ 691 :=
    calc 8 * n * m ≤ 8 * 2 ^ 47 * 2 ^ 641 := by gcongr
      _ = 2 ^ 691 := by norm_num
  rw [natCast_div_eq_ofReal _ (2 ^ 1088) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc ((8 * n * m : ℕ) : ℝ) / ((2 ^ 1088 : ℕ) : ℝ) ≤ 2 ^ 691 / 2 ^ 1088 := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hK) (by positivity)
    _ ≤ 1 / 2 ^ 397 := by norm_num

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The `HmsgSep` fraction off `seedBadSet` at Keccak's sizes**: at most `2^-396` of the raw
coordinates (the bad permutations `2^-777`, the collisions `2^-407`, the `H_msg` blocks
`2^-397`). -/
theorem hmsgSepR_frac_le_keccak :
    (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          ¬HmsgSepR y.1.2 y.1.1 y.2 ∧ y.1.2.1 ∉ seedBadSet).card ≤
      ENNReal.ofReal (1 / 2 ^ 396) := by
  set N := Fintype.card (((Z → X) × XW) × (ValPos → Digest))
  have hsub := card_filter_le_add_of_imp
    (fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
      ¬HmsgSepR y.1.2 y.1.1 y.2 ∧ y.1.2.1 ∉ seedBadSet)
    (fun y : ((Z → X) × XW) × (ValPos → Digest) ↦ ¬PermGood (permEquiv y).1 18)
    (fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
      PermGood y.1.2.2.1 18 ∧ (¬HmsgSepR y.1.2 y.1.1 y.2 ∧ y.1.2.1 ∉ seedBadSet))
    fun y hy ↦ by
      by_cases hG : PermGood y.1.2.2.1 18
      · exact Or.inr ⟨hG, hy⟩
      · exact Or.inl hG
  calc (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
        ¬HmsgSepR y.1.2 y.1.1 y.2 ∧ y.1.2.1 ∉ seedBadSet).card
      ≤ (N : ℝ≥0∞)⁻¹ * (((Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          ¬PermGood (permEquiv y).1 18).card : ℝ≥0∞) +
        (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          PermGood y.1.2.2.1 18 ∧ (¬HmsgSepR y.1.2 y.1.1 y.2 ∧ y.1.2.1 ∉ seedBadSet)).card) := by
        gcongr
        exact_mod_cast hsub
    _ = (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          ¬PermGood (permEquiv y).1 18).card +
        (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          PermGood y.1.2.2.1 18 ∧ (¬HmsgSepR y.1.2 y.1.1 y.2 ∧ y.1.2.1 ∉ seedBadSet)).card :=
        mul_add _ _ _
    _ ≤ ENNReal.ofReal (1 / 2 ^ 777) + (ENNReal.ofReal (1 / 2 ^ 407) +
          ENNReal.ofReal (1 / 2 ^ 397)) := by
        rw [inv_card_mul_card_filter_comp_fst permEquiv fun π ↦ ¬PermGood π 18]
        exact add_le_add permTerm_le_keccak ((hmsgSepR_good_frac_le 18).trans
          (add_le_add (collTerms_le card_xI_le rnCard_X rnCard_Z)
            (hmsgTerm_le card_xI_le card_hmsgSet_le rnCard_X)))
    _ ≤ ENNReal.ofReal (1 / 2 ^ 396) := by
        rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 407)
            (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 397),
          ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 777) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)

end hmsgSep

/-! ## The key conditions -/

section keys

/-- **A pair condition's card form as an average**: if `c · Σ_k #{k' | ¬G k k'} ≤ L |K|²`, the
average over the pairs of the indicator of `¬G` is at most `L / c`. -/
theorem uavg_pair_ite_le {K : Type} [Fintype K] (G : K → K → Prop) [∀ k, DecidablePred (G k)]
    {c L : ℕ} (hc : c ≠ 0)
    (h : c * ∑ k, (Finset.univ.filter fun k' ↦ ¬G k k').card ≤
      L * (Fintype.card K * Fintype.card K)) :
    uavg (fun kk : K × K ↦ if G kk.1 kk.2 then (0 : ℝ≥0∞) else 1) ≤ (L : ℝ≥0∞) / c := by
  rw [uavg_ite_zero_one, Fintype.card_prod]
  have hcount : (Finset.univ.filter fun kk : K × K ↦ ¬G kk.1 kk.2).card =
      ∑ k, (Finset.univ.filter fun k' ↦ ¬G k k').card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp only [Finset.card_filter]
  rw [hcount]
  rcases Nat.eq_zero_or_pos (Fintype.card K) with hK | hK
  · have : IsEmpty K := Fintype.card_eq_zero_iff.mp hK
    simp
  have hne : ((Fintype.card K * Fintype.card K : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hK.ne' hK.ne')
  calc ((Fintype.card K * Fintype.card K : ℕ) : ℝ≥0∞)⁻¹ *
        ((∑ k, (Finset.univ.filter fun k' ↦ ¬G k k').card : ℕ) : ℝ≥0∞)
      ≤ ((Fintype.card K * Fintype.card K : ℕ) : ℝ≥0∞)⁻¹ *
          ((L : ℝ≥0∞) * (((Fintype.card K * Fintype.card K : ℕ) : ℝ≥0∞) / c)) := by
        push_cast
        gcongr
        exact_mod_cast natCast_le_mul_div_of_mul_le hc h
    _ = (L : ℝ≥0∞) / c := by
        rw [mul_left_comm, ← mul_div_assoc, ENNReal.inv_mul_cancel hne (ENNReal.natCast_ne_top _),
          one_div, div_eq_mul_inv]

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **`HZLoad` fails for at most `2^-639` of the keys** (HConflict's `hZLoad_frac_le`: `2^897`
choices at `|Z|^-3` each). -/
theorem uavg_hZLoad_le (P : PublicParameter) (π : Equiv.Perm (X × Z)) (h : Z → X) :
    uavg (fun kk : (X → Z) × (X → Z) ↦ if HZLoad (pubES P π h kk) then (0 : ℝ≥0∞) else 1) ≤
      ENNReal.ofReal (1 / 2 ^ 639) := by
  refine (uavg_pair_ite_le (fun k k' ↦ HZLoad (pubES P π h (k, k')))
    (pow_ne_zero 3 Fintype.card_ne_zero) (hZLoad_frac_le P π h)).trans ?_
  rw [Fintype.card_prod (Digest × Message × DigestCall)
      (Randomizer × Randomizer × Randomizer × Randomizer),
    card_prod_four card_randomizer card_randomizer card_randomizer card_randomizer,
    Fintype.card_prod Digest (Message × DigestCall), card_digest, card_message_digestCall,
    rnCard_Z, natCast_div_eq_ofReal _ _ (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **`HSelfSep` fails for at most `2^-128` of the keys** at every hidden values (HConflict's
`hSelfSep_frac_le`: `2^384` choices at `|Z|^-1` each). -/
theorem uavg_hSelfSep_le (P : PublicParameter) (π : Equiv.Perm (X × Z)) (h : Z → X)
    (v : (s : HPos) → XD s) :
    uavg (fun kk : (X → Z) × (X → Z) ↦ if HSelfSep (pubES P π h kk) v then (0 : ℝ≥0∞) else 1) ≤
      ENNReal.ofReal (1 / 2 ^ 128) := by
  refine (uavg_pair_ite_le (fun k k' ↦ HSelfSep (pubES P π h (k, k')) v) Fintype.card_ne_zero
    (hSelfSep_frac_le P π h v)).trans ?_
  rw [Fintype.card_prod Message Randomizer, card_randomizer, Quantum.Xmss.Assembly.card_message,
    rnCard_Z, natCast_div_eq_ofReal _ _ (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end keys

/-! ## Stage events of path families, counted

Generic over the types: `ring` on concrete `Fintype.card` terms makes the kernel evaluate them. -/

section evGen

open Quantum.Xmss.Assembly (EvK EvR EvZ DownClosed card_mul_sum_evK_le card_mul_sum_evR_le
  card_mul_sum_evZ_le card_mul_sum_triple_le₁ card_mul_sum_triple_le₂ card_mul_sum_triple_le₃)

variable {X₁ Z₁ : Type} [AddCommGroup X₁] [AddCommGroup Z₁] (π₁ : Equiv.Perm (X₁ × Z₁))

/-- **A stage event** (PathBad's `EvK`, `EvR`, `EvZ`) of rounds `a`, `b` at the keys `t`. -/
def EvAny {S : Type} (blk : S → ℕ → X₁) (R : Finset (S × ℕ)) (a b : S × ℕ)
    (t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁)) : Prop :=
  EvK π₁ blk R a b t.1 t.2.1 t.2.2 ∨ EvR π₁ blk R a b t.1 t.2.1 t.2.2 ∨
    EvZ π₁ blk R a b t.1 t.2.1 t.2.2

open scoped Classical in
/-- The stage events of rounds `a`, `b` at the keys `t`, as a count. -/
noncomputable def evN {S : Type} (blk : S → ℕ → X₁) (R : Finset (S × ℕ)) (a b : S × ℕ)
    (t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁)) : ℕ :=
  (if EvK π₁ blk R a b t.1 t.2.1 t.2.2 then 1 else 0) +
    (if EvR π₁ blk R a b t.1 t.2.1 t.2.2 then 1 else 0) +
    (if EvZ π₁ blk R a b t.1 t.2.1 t.2.2 then 1 else 0)

variable {π₁}

theorem one_le_evN {S : Type} {blk : S → ℕ → X₁} {R : Finset (S × ℕ)} {a b : S × ℕ}
    {t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁)} (h : EvAny π₁ blk R a b t) :
    1 ≤ evN π₁ blk R a b t := by
  classical
  unfold evN
  rcases h with h1 | h2 | h3
  · exact le_add_right (le_add_right (by rw [ite_eq_left h1]))
  · exact le_add_right (le_add_left (by rw [ite_eq_left h2]))
  · exact le_add_left (by rw [ite_eq_left h3])

open scoped Classical in
/-- **The stage events of a pair of rounds** for at most `1/|X| + (G + 1)/|Z|` of the keys
(PathBad's `card_mul_sum_evK_le`, `card_mul_sum_evR_le`, `card_mul_sum_evZ_le`). -/
theorem card_mul_sum_evN_le [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
    {S : Type} (blk : S → ℕ → X₁) {R : Finset (S × ℕ)} (hR : DownClosed R) {G : ℕ}
    (hG : ∀ x r, rateCount π₁ x r ≤ G) {a b : S × ℕ} (ha : a ∈ R) (hb : b ∈ R) :
    Fintype.card X₁ * Fintype.card Z₁ *
        ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁), evN π₁ blk R a b t ≤
      Fintype.card (Z₁ → X₁) * Fintype.card (X₁ → Z₁) * Fintype.card (X₁ → Z₁) *
        (Fintype.card Z₁ + (G + 1) * Fintype.card X₁) := by
  set M := Fintype.card (Z₁ → X₁) * Fintype.card (X₁ → Z₁) * Fintype.card (X₁ → Z₁)
  have hK : Fintype.card X₁ * ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
      (if EvK π₁ blk R a b t.1 t.2.1 t.2.2 then 1 else 0) ≤ M * 1 :=
    card_mul_sum_triple_le₁ (fun h k k' ↦ if EvK π₁ blk R a b h k k' then 1 else 0) _ _
      fun k k' ↦ card_mul_sum_evK_le hR ha hb k k'
  have hRr : Fintype.card Z₁ * ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
      (if EvR π₁ blk R a b t.1 t.2.1 t.2.2 then 1 else 0) ≤ M * G :=
    card_mul_sum_triple_le₂ (fun h k k' ↦ if EvR π₁ blk R a b h k k' then 1 else 0) _ _
      fun h k' ↦ card_mul_sum_evR_le hR hG ha hb h k'
  have hZz : Fintype.card Z₁ * ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
      (if EvZ π₁ blk R a b t.1 t.2.1 t.2.2 then 1 else 0) ≤ M * 1 :=
    card_mul_sum_triple_le₃ (fun h k k' ↦ if EvZ π₁ blk R a b h k k' then 1 else 0) _ _
      fun h k ↦ card_mul_sum_evZ_le hR ha hb h k
  simp only [evN, Finset.sum_add_distrib]
  calc Fintype.card X₁ * Fintype.card Z₁ * (∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
        (if EvK π₁ blk R a b t.1 t.2.1 t.2.2 then 1 else 0) +
        ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
          (if EvR π₁ blk R a b t.1 t.2.1 t.2.2 then 1 else 0) +
        ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
          (if EvZ π₁ blk R a b t.1 t.2.1 t.2.2 then 1 else 0))
      = Fintype.card Z₁ * (Fintype.card X₁ * ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
          (if EvK π₁ blk R a b t.1 t.2.1 t.2.2 then 1 else 0)) +
        Fintype.card X₁ * (Fintype.card Z₁ * ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
          (if EvR π₁ blk R a b t.1 t.2.1 t.2.2 then 1 else 0)) +
        Fintype.card X₁ * (Fintype.card Z₁ * ∑ t : (Z₁ → X₁) × (X₁ → Z₁) × (X₁ → Z₁),
          (if EvZ π₁ blk R a b t.1 t.2.1 t.2.2 then 1 else 0)) := by ring
    _ ≤ Fintype.card Z₁ * (M * 1) + Fintype.card X₁ * (M * G) + Fintype.card X₁ * (M * 1) :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hK)
          (Nat.mul_le_mul_left _ hRr)) (Nat.mul_le_mul_left _ hZz)
    _ = M * (Fintype.card Z₁ + (G + 1) * Fintype.card X₁) := by ring

/-- A count over pairs of indices, exchanged with the sum over the keys. -/
theorem mul_sum_sum_sum_le {T A B : Type} [Fintype T] (s : Finset A) (u : Finset B)
    (g : T → A → B → ℕ) (n K : ℕ) (h : ∀ a ∈ s, ∀ b ∈ u, n * ∑ t, g t a b ≤ K) :
    n * ∑ t, ∑ a ∈ s, ∑ b ∈ u, g t a b ≤ s.card * (u.card * K) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  calc ∑ a ∈ s, n * ∑ t, ∑ b ∈ u, g t a b = ∑ a ∈ s, ∑ b ∈ u, n * ∑ t, g t a b :=
        Finset.sum_congr rfl fun a _ ↦ by rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _a ∈ s, ∑ _b ∈ u, K :=
        Finset.sum_le_sum fun a ha ↦ Finset.sum_le_sum fun b hb ↦ h a ha b hb
    _ = s.card * (u.card * K) := by simp only [Finset.sum_const, smul_eq_mul]

/-- The count's rearrangement, over abstract numbers. -/
theorem hsep_count_eq (N T C M : ℕ) :
    N * (N * (T * C)) + M * (N * (2 * (T * C))) = T * ((N * N + M * (2 * N)) * C) := by
  ring

/-- The card of a triple, over abstract types. -/
theorem card_triple_eq (A B C : Type) [Fintype A] [Fintype B] [Fintype C] :
    Fintype.card (A × B × C) = Fintype.card A * Fintype.card B * Fintype.card C := by
  rw [Fintype.card_prod, Fintype.card_prod, mul_assoc]

end evGen

/-! ## `HmsgHSep`

For one `H_msg` call with block `y`, the in-table paths and the call's one-round path form one
family of paths (`blkH`, rounds `rndH`). Off `seedBadSet` their first blocks are distinct, so an
in-table `h`-cell meeting the call's is a stage event of PathBad (`hsep_ev`): either among the
in-table rounds alone (independent of the call), or between an in-table round and the call's
round, counted per call (`card_mul_sum_not_hmsgHSep_le`): `(N² + 2^258 N) (1/|X| + 19/|Z|)`,
`N ≤ 2^50`. -/

section hmsgHSep

open Quantum.Xmss.Assembly (EvK EvR EvZ InjBelow famR famZ rnZ exists_ev_of_not_injOn
  injBelow_congr downClosed_rnds card_rnds_le)

/-- **The in-table paths and one `H_msg` call**: an in-table output's blocks at `some p`, the one
block `y` at `none`. -/
def blkH (P : PublicParameter) (f : ValPos → Digest) (y : X) : Option ValPos → ℕ → X
  | none => fun _ ↦ y
  | some p => xBlk P f p

/-- The path lengths: one round for the `H_msg` call. -/
def lenH (P : PublicParameter) : Option ValPos → ℕ
  | none => 1
  | some p => xLen P p

/-- **The in-table rounds.** -/
def rndT (P : PublicParameter) : Finset (Option ValPos × ℕ) :=
  rnds (xI.image some) (lenH P)

/-- **The in-table rounds and the `H_msg` round** `(none, 0)`. -/
def rndH (P : PublicParameter) : Finset (Option ValPos × ℕ) :=
  rnds (insert none (xI.image some)) (lenH P)

theorem mem_rndT {P : PublicParameter} {a : Option ValPos × ℕ} :
    a ∈ rndT P ↔ ∃ p ∈ xI, a.1 = some p ∧ a.2 < xLen P p := by
  rw [rndT, mem_rnds, Finset.mem_image]
  constructor
  · rintro ⟨⟨p, hp, hpa⟩, hl⟩
    rw [← hpa] at hl
    exact ⟨p, hp, hpa.symm, hl⟩
  · rintro ⟨p, hp, ha, hl⟩
    refine ⟨⟨p, hp, ha.symm⟩, ?_⟩
    rw [ha]
    exact hl

theorem rndT_subset (P : PublicParameter) : rndT P ⊆ rndH P := fun a ha ↦ by
  rw [rndT, mem_rnds] at ha
  rw [rndH, mem_rnds]
  exact ⟨Finset.mem_insert_of_mem ha.1, ha.2⟩

theorem hround_mem (P : PublicParameter) : ((none, 0) : Option ValPos × ℕ) ∈ rndH P := by
  rw [rndH, mem_rnds]
  exact ⟨Finset.mem_insert_self _ _, Nat.zero_lt_one⟩

theorem mem_rndT_of_mem_rndH {P : PublicParameter} {a : Option ValPos × ℕ} (ha : a ∈ rndH P)
    {p : ValPos} (hp : a.1 = some p) : a ∈ rndT P := by
  rw [rndH, mem_rnds, Finset.mem_insert, hp] at ha
  rw [rndT, mem_rnds, hp]
  rcases ha with ⟨h1 | h1, h2⟩
  · exact absurd h1 (by simp)
  · exact ⟨h1, h2⟩

theorem eq_hround {P : PublicParameter} {a : Option ValPos × ℕ} (ha : a ∈ rndH P)
    (hn : a.1 = none) : a = (none, 0) := by
  rw [rndH, mem_rnds, hn] at ha
  exact Prod.ext hn (Nat.lt_one_iff.mp ha.2)

theorem mem_xI_of_rndT {P : PublicParameter} {a : Option ValPos × ℕ} (ha : a ∈ rndT P)
    {p : ValPos} (hp : a.1 = some p) : p ∈ xI := by
  obtain ⟨q, hq, h1, -⟩ := mem_rndT.mp ha
  rw [hp] at h1
  rw [Option.some.inj h1]
  exact hq

theorem lenH_le (P : PublicParameter) (o : Option ValPos) : lenH P o ≤ 8 := by
  cases o with
  | none => exact (by norm_num : 1 ≤ 8)
  | some p => exact xLen_le P p

theorem card_rndT_le (P : PublicParameter) : (rndT P).card ≤ 2 ^ 50 :=
  (card_rnds_le _ _ (lenH_le P)).trans ((Nat.mul_le_mul_left _
    (Finset.card_image_le.trans card_xI_le)).trans (by norm_num))

/-! ### Events of the family -/

variable {π : Equiv.Perm (X × Z)}

theorem injBelow_mono {S β : Type} {R R' : Finset (S × ℕ)} (h : R ⊆ R') {f : S × ℕ → β}
    {J : ℕ} (hf : InjBelow R' f J) : InjBelow R f J :=
  fun a ha b hb ↦ hf a (h ha) b (h hb)

theorem evAny_mono {S : Type} {blk : S → ℕ → X} {R R' : Finset (S × ℕ)} (h : R ⊆ R')
    {a b : S × ℕ} {t : (Z → X) × (X → Z) × (X → Z)} (he : EvAny π blk R' a b t) :
    EvAny π blk R a b t := by
  rcases he with he | he | he
  · exact .inl ⟨⟨he.1.1, he.1.2.1, he.1.2.2.1, injBelow_mono h he.1.2.2.2.1,
      injBelow_mono h he.1.2.2.2.2.1, injBelow_mono h he.1.2.2.2.2.2⟩, he.2⟩
  · exact .inr (.inl ⟨⟨he.1.1, he.1.2.1, ⟨injBelow_mono h he.1.2.2.1.1,
      injBelow_mono h he.1.2.2.1.2.1, injBelow_mono h he.1.2.2.1.2.2⟩,
      injBelow_mono h he.1.2.2.2⟩, he.2⟩)
  · exact .inr (.inr ⟨⟨he.1.1, he.1.2.1, ⟨⟨injBelow_mono h he.1.2.2.1.1.1,
      injBelow_mono h he.1.2.2.1.1.2.1, injBelow_mono h he.1.2.2.1.1.2.2⟩,
      injBelow_mono h he.1.2.2.1.2⟩, injBelow_mono h he.1.2.2.2⟩, he.2⟩)

theorem ne_of_evAny {S : Type} {blk : S → ℕ → X} {R : Finset (S × ℕ)} {a b : S × ℕ}
    {t : (Z → X) × (X → Z) × (X → Z)} (he : EvAny π blk R a b t) : a ≠ b := by
  rcases he with he | he | he
  · exact he.1.2.2.1
  · exact he.1.2.1
  · exact he.1.2.1

/-- At the in-table rounds the family does not see the `H_msg` block. -/
theorem fam_blkH_eq {P : PublicParameter} {f : ValPos → Digest} (y y' : X)
    {x : Option ValPos × ℕ} (hx : x ∈ rndT P) (t : (Z → X) × (X → Z) × (X → Z)) :
    famK π (blkH P f y) t.1 t.2.1 t.2.2 x = famK π (blkH P f y') t.1 t.2.1 t.2.2 x ∧
      famR π (blkH P f y) t.1 t.2.1 t.2.2 x = famR π (blkH P f y') t.1 t.2.1 t.2.2 x ∧
      famZ π (blkH P f y) t.1 t.2.1 t.2.2 x = famZ π (blkH P f y') t.1 t.2.1 t.2.2 x := by
  obtain ⟨o, j⟩ := x
  obtain ⟨p, -, h1, -⟩ := mem_rndT.mp hx
  cases h1
  exact ⟨rfl, rfl, rfl⟩

theorem evAny_change {P : PublicParameter} {f : ValPos → Digest} (y y' : X)
    {a b : Option ValPos × ℕ} (ha : a ∈ rndT P) (hb : b ∈ rndT P)
    {t : (Z → X) × (X → Z) × (X → Z)} (he : EvAny π (blkH P f y) (rndT P) a b t) :
    EvAny π (blkH P f y') (rndT P) a b t := by
  have hK : ∀ {J}, InjBelow (rndT P) (famK π (blkH P f y) t.1 t.2.1 t.2.2) J →
      InjBelow (rndT P) (famK π (blkH P f y') t.1 t.2.1 t.2.2) J :=
    injBelow_congr fun x hx _ ↦ (fam_blkH_eq y y' hx t).1.symm
  have hR : ∀ {J}, InjBelow (rndT P) (famR π (blkH P f y) t.1 t.2.1 t.2.2) J →
      InjBelow (rndT P) (famR π (blkH P f y') t.1 t.2.1 t.2.2) J :=
    injBelow_congr fun x hx _ ↦ (fam_blkH_eq y y' hx t).2.1.symm
  have hZ : ∀ {J}, InjBelow (rndT P) (famZ π (blkH P f y) t.1 t.2.1 t.2.2) J →
      InjBelow (rndT P) (famZ π (blkH P f y') t.1 t.2.1 t.2.2) J :=
    injBelow_congr fun x hx _ ↦ (fam_blkH_eq y y' hx t).2.2.symm
  have ea := fam_blkH_eq (π := π) (f := f) y y' ha t
  have eb := fam_blkH_eq (π := π) (f := f) y y' hb t
  rcases he with he | he | he
  · exact .inl ⟨⟨he.1.1, he.1.2.1, he.1.2.2.1, hK he.1.2.2.2.1, hR he.1.2.2.2.2.1,
      hZ he.1.2.2.2.2.2⟩, ea.1.symm.trans (he.2.trans eb.1)⟩
  · exact .inr (.inl ⟨⟨he.1.1, he.1.2.1, ⟨hK he.1.2.2.1.1, hR he.1.2.2.1.2.1,
      hZ he.1.2.2.1.2.2⟩, hK he.1.2.2.2⟩, ea.2.1.symm.trans (he.2.trans eb.2.1)⟩)
  · exact .inr (.inr ⟨⟨he.1.1, he.1.2.1, ⟨⟨hK he.1.2.2.1.1.1, hR he.1.2.2.1.1.2.1,
      hZ he.1.2.2.1.1.2.2⟩, hK he.1.2.2.1.2⟩, hR he.1.2.2.2⟩,
      ea.2.2.symm.trans (he.2.trans eb.2.2)⟩)

/-- The block of `H_msg` call `i` on `M` at its randomizer. -/
def hmsgY (P : PublicParameter) (v : (s : HPos) → XD s) (mi : Message × DigestCall) : X :=
  slotBlk P (.hmsg (v (.rnd mi.1)) mi.1 mi.2) (valsOf v) 0

/-- **A violation of `HmsgHSep` off `seedBadSet` is a stage event**: among the in-table rounds, or
between an in-table round and the round of an `H_msg` call. -/
theorem hsep_ev {P : PublicParameter} {v : (s : HPos) → XD s}
    {t : (Z → X) × (X → Z) × (X → Z)} (hs : P ∉ seedBadSet)
    (hn : ¬HmsgHSep (pubES P π t.1 (t.2.1, t.2.2)) v) :
    (∃ a ∈ rndT P, ∃ b ∈ rndT P, EvAny π (blkH P (valsOf v) 0) (rndT P) a b t) ∨
      ∃ mi : Message × DigestCall, ∃ c ∈ rndT P,
        EvAny π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) c (none, 0) t ∨
          EvAny π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) (none, 0) c t := by
  simp only [HmsgHSep, not_forall, not_not] at hn
  obtain ⟨M, i, s, hs', j, hj, he⟩ := hn
  have key : ∀ p ∈ xI, hmsgY P v (M, i) ≠ xBlk P (valsOf v) p 0 := fun p hp e ↦ by
    have hin := inTable_outSlot (mem_xI.mp hp)
    have h1 := rateSlice_slotBlk_inTable P (valsOf v) hin
    have h2 := rateSlice_slotBlk_hmsg P (valsOf v) (v (.rnd M)) M i
    have e' : slotBlk P (.hmsg (v (.rnd M)) M i) (valsOf v) 0 =
        slotBlk P (outSlot p) (valsOf v) 0 := e
    rw [e', h1] at h2
    rw [← h2] at hs
    exact hs (mem_seedBadSet hin)
  have hfirst : ∀ a ∈ rndH P, ∀ b ∈ rndH P, a.2 = 0 → b.2 = 0 →
      blkH P (valsOf v) (hmsgY P v (M, i)) a.1 0 = blkH P (valsOf v) (hmsgY P v (M, i)) b.1 0 →
        a.1 = b.1 := by
    intro a ha b hb _ _ e
    rcases ha' : a.1 with _ | p <;> rcases hb' : b.1 with _ | q
    · rfl
    · rw [ha', hb'] at e
      exact absurd e (key q (mem_xI_of_rndT (mem_rndT_of_mem_rndH hb hb') hb'))
    · rw [ha', hb'] at e
      exact absurd e.symm (key p (mem_xI_of_rndT (mem_rndT_of_mem_rndH ha ha') ha'))
    · rw [ha', hb'] at e
      exact congrArg some (xBlk_injOn P (valsOf v)
        (Finset.mem_coe.mpr (mem_xI_of_rndT (mem_rndT_of_mem_rndH ha ha') ha'))
        (Finset.mem_coe.mpr (mem_xI_of_rndT (mem_rndT_of_mem_rndH hb hb') hb')) e)
  have hsT : ((some (slotOutPos s), j) : Option ValPos × ℕ) ∈ rndT P :=
    mem_rndT.mpr ⟨slotOutPos s, mem_xI.mpr (inPos_slotOutPos hs'), rfl, by
      show j < nBlk P (outSlot (slotOutPos s))
      rw [outSlot_slotOutPos hs']
      exact hj⟩
  have hz : famZ π (blkH P (valsOf v) (hmsgY P v (M, i))) t.1 t.2.1 t.2.2 (some (slotOutPos s), j) =
      famZ π (blkH P (valsOf v) (hmsgY P v (M, i))) t.1 t.2.1 t.2.2 (none, 0) := by
    show rnZ π t.1 t.2.1 t.2.2 (slotBlk P (outSlot (slotOutPos s)) (valsOf v)) j =
      rnZ π t.1 t.2.1 t.2.2 (fun _ ↦ hmsgY P v (M, i)) 0
    rw [outSlot_slotOutPos hs']
    exact he
  have hni : ¬Set.InjOn (famZ π (blkH P (valsOf v) (hmsgY P v (M, i))) t.1 t.2.1 t.2.2)
      ↑(rndH P) := fun hinj ↦ absurd (congrArg Prod.fst (hinj
        (Finset.mem_coe.mpr (rndT_subset P hsT)) (Finset.mem_coe.mpr (hround_mem P)) hz))
        (by simp)
  obtain ⟨a, ha, b, hb, hev⟩ := exists_ev_of_not_injOn hfirst hni
  have hev' : EvAny π (blkH P (valsOf v) (hmsgY P v (M, i))) (rndH P) a b t := hev
  rcases ha1 : a.1 with _ | p
  · have haH := eq_hround ha ha1
    rcases hb1 : b.1 with _ | q
    · exact absurd ((eq_hround ha ha1).trans (eq_hround hb hb1).symm) (ne_of_evAny hev')
    · rw [haH] at hev'
      exact .inr ⟨(M, i), b, mem_rndT_of_mem_rndH hb hb1, .inr hev'⟩
  · rcases hb1 : b.1 with _ | q
    · rw [eq_hround hb hb1] at hev'
      exact .inr ⟨(M, i), a, mem_rndT_of_mem_rndH ha ha1, .inl hev'⟩
    · have haT := mem_rndT_of_mem_rndH ha ha1
      have hbT := mem_rndT_of_mem_rndH hb hb1
      exact .inl ⟨a, haT, b, hbT,
        evAny_change _ 0 haT hbT (evAny_mono (rndT_subset P) hev')⟩

open scoped Classical in
/-- **The keys violating `HmsgHSep`** at good `π` and `PK.seed` off `seedBadSet`: as a count, at
most `(N² + 2 |Message × DigestCall| N) (|Z| + 19 |X|)` per `|X| |Z|`, `N = |rndT P|`. -/
theorem card_mul_sum_not_hmsgHSep_le {P : PublicParameter} (hG : ∀ x r, rateCount π x r ≤ 18)
    (hs : P ∉ seedBadSet) (v : (s : HPos) → XD s) :
    Fintype.card X * Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
        (if HmsgHSep (pubES P π t.1 (t.2.1, t.2.2)) v then 0 else 1) ≤
      ((rndT P).card * ((rndT P).card *
        (Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) *
          (Fintype.card Z + (18 + 1) * Fintype.card X))) +
        Fintype.card (Message × DigestCall) * ((rndT P).card *
          (2 * (Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) *
            (Fintype.card Z + (18 + 1) * Fintype.card X))))) := by
  set T := Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) *
    (Fintype.card Z + (18 + 1) * Fintype.card X)
  have hpt : ∀ t : (Z → X) × (X → Z) × (X → Z),
      (if HmsgHSep (pubES P π t.1 (t.2.1, t.2.2)) v then 0 else 1) ≤
        ∑ a ∈ rndT P, ∑ b ∈ rndT P, evN π (blkH P (valsOf v) 0) (rndT P) a b t +
          ∑ mi ∈ (Finset.univ : Finset (Message × DigestCall)), ∑ c ∈ rndT P,
            (evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) c (none, 0) t +
              evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) (none, 0) c t) := by
    intro t
    by_cases hh : HmsgHSep (pubES P π t.1 (t.2.1, t.2.2)) v
    · rw [ite_eq_left hh]
      exact Nat.zero_le _
    rw [ite_eq_right hh]
    rcases hsep_ev hs hh with ⟨a, ha, b, hb, h⟩ | ⟨mi, c, hc, h | h⟩
    · refine le_trans ?_ le_self_add
      exact (one_le_evN h).trans ((Finset.single_le_sum (f := fun b ↦
        evN π (blkH P (valsOf v) 0) (rndT P) a b t) (fun _ _ ↦ Nat.zero_le _) hb).trans
        (Finset.single_le_sum (f := fun a ↦ ∑ b ∈ rndT P,
          evN π (blkH P (valsOf v) 0) (rndT P) a b t) (fun _ _ ↦ Nat.zero_le _) ha))
    · refine le_trans ?_ le_add_self
      exact (one_le_evN h).trans (le_self_add.trans ((Finset.single_le_sum (f := fun c ↦
        evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) c (none, 0) t +
          evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) (none, 0) c t)
        (fun _ _ ↦ Nat.zero_le _) hc).trans (Finset.single_le_sum (f := fun mi ↦
          ∑ c ∈ rndT P, (evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) c (none, 0) t +
            evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) (none, 0) c t))
          (fun _ _ ↦ Nat.zero_le _) (by simp))))
    · refine le_trans ?_ le_add_self
      exact (one_le_evN h).trans (le_add_self.trans ((Finset.single_le_sum (f := fun c ↦
        evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) c (none, 0) t +
          evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) (none, 0) c t)
        (fun _ _ ↦ Nat.zero_le _) hc).trans (Finset.single_le_sum (f := fun mi ↦
          ∑ c ∈ rndT P, (evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) c (none, 0) t +
            evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) (none, 0) c t))
          (fun _ _ ↦ Nat.zero_le _) (by simp))))
  have h0 := mul_sum_sum_sum_le (rndT P) (rndT P)
    (fun t a b ↦ evN π (blkH P (valsOf v) 0) (rndT P) a b t) (Fintype.card X * Fintype.card Z) T
    fun a ha b hb ↦ card_mul_sum_evN_le (blkH P (valsOf v) 0) (downClosed_rnds _ _) hG ha hb
  have h1 := mul_sum_sum_sum_le (Finset.univ : Finset (Message × DigestCall)) (rndT P)
    (fun t mi c ↦ evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) c (none, 0) t +
      evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) (none, 0) c t)
    (Fintype.card X * Fintype.card Z) (2 * T) fun mi _ c hc ↦ by
      rw [Finset.sum_add_distrib, mul_add, two_mul]
      exact Nat.add_le_add
        (card_mul_sum_evN_le _ (downClosed_rnds _ _) hG (rndT_subset P hc) (hround_mem P))
        (card_mul_sum_evN_le _ (downClosed_rnds _ _) hG (hround_mem P) (rndT_subset P hc))
  calc Fintype.card X * Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
        (if HmsgHSep (pubES P π t.1 (t.2.1, t.2.2)) v then 0 else 1)
      ≤ Fintype.card X * Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
          (∑ a ∈ rndT P, ∑ b ∈ rndT P, evN π (blkH P (valsOf v) 0) (rndT P) a b t +
            ∑ mi ∈ (Finset.univ : Finset (Message × DigestCall)), ∑ c ∈ rndT P,
              (evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) c (none, 0) t +
                evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) (none, 0) c t)) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun t _ ↦ hpt t)
    _ = Fintype.card X * Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
          ∑ a ∈ rndT P, ∑ b ∈ rndT P, evN π (blkH P (valsOf v) 0) (rndT P) a b t +
        Fintype.card X * Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
          ∑ mi ∈ (Finset.univ : Finset (Message × DigestCall)), ∑ c ∈ rndT P,
            (evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) c (none, 0) t +
              evN π (blkH P (valsOf v) (hmsgY P v mi)) (rndH P) (none, 0) c t) := by
        rw [Finset.sum_add_distrib, mul_add]
    _ ≤ _ := by
        rw [Finset.card_univ] at h1
        exact Nat.add_le_add h0 h1

set_option exponentiation.threshold 4096 in
/-- The count's constant at Keccak's sizes: at most `2^-199`. -/
theorem hsepTerm_le {N cM cX cZ : ℕ} (hN : N ≤ 2 ^ 50) (hM : cM = 2 ^ 257) (hX : cX = 2 ^ 1088)
    (hZ : cZ = 2 ^ 512) :
    (((N * N + cM * (2 * N)) * (cZ + (18 + 1) * cX) : ℕ) : ℝ≥0∞) / ((cX * cZ : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (1 / 2 ^ 199) := by
  subst hM hX hZ
  have hK : (N * N + 2 ^ 257 * (2 * N)) * (2 ^ 512 + (18 + 1) * 2 ^ 1088) ≤
      (2 ^ 50 * 2 ^ 50 + 2 ^ 257 * (2 * 2 ^ 50)) * (2 ^ 512 + (18 + 1) * 2 ^ 1088) := by
    gcongr
  rw [natCast_div_eq_ofReal _ _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc ((((N * N + 2 ^ 257 * (2 * N)) * (2 ^ 512 + (18 + 1) * 2 ^ 1088) : ℕ) : ℝ) /
        ((2 ^ 1088 * 2 ^ 512 : ℕ) : ℝ)) ≤
      (((2 ^ 50 * 2 ^ 50 + 2 ^ 257 * (2 * 2 ^ 50)) * (2 ^ 512 + (18 + 1) * 2 ^ 1088) : ℕ) : ℝ) /
        ((2 ^ 1088 * 2 ^ 512 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hK) (by positivity)
    _ ≤ 1 / 2 ^ 199 := by norm_num

open scoped Classical in
/-- **`HmsgHSep` fails, off `seedBadSet`, for at most `2^-199` of the keys** at good `π`. -/
theorem uavg_hmsgHSep_le {P : PublicParameter} (hG : ∀ x r, rateCount π x r ≤ 18)
    (hs : P ∉ seedBadSet) (v : (s : HPos) → XD s) :
    uavg (fun t : (Z → X) × (X → Z) × (X → Z) ↦
      if HmsgHSep (pubES P π t.1 (t.2.1, t.2.2)) v then (0 : ℝ≥0∞) else 1) ≤
      ENNReal.ofReal (1 / 2 ^ 199) := by
  obtain ⟨T3, hT3⟩ : ∃ n,
      n = Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) := ⟨_, rfl⟩
  obtain ⟨Cn, hCn⟩ : ∃ n, n = ((rndT P).card * (rndT P).card +
      Fintype.card (Message × DigestCall) * (2 * (rndT P).card)) *
        (Fintype.card Z + (18 + 1) * Fintype.card X) := ⟨_, rfl⟩
  have hT : Fintype.card ((Z → X) × (X → Z) × (X → Z)) = T3 :=
    (card_triple_eq _ _ _).trans hT3.symm
  have hc : (Finset.univ.filter fun t : (Z → X) × (X → Z) × (X → Z) ↦
      ¬HmsgHSep (pubES P π t.1 (t.2.1, t.2.2)) v).card =
      ∑ t : (Z → X) × (X → Z) × (X → Z),
        (if HmsgHSep (pubES P π t.1 (t.2.1, t.2.2)) v then 0 else 1) := by
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun t _ ↦ by
      by_cases hh : HmsgHSep (pubES P π t.1 (t.2.1, t.2.2)) v
      · rw [ite_eq_right (not_not.mpr hh), ite_eq_left hh]
      · rw [ite_eq_left hh, ite_eq_right hh]
  have hnat := card_mul_sum_not_hmsgHSep_le hG hs v
  rw [← hc, ← hT3, hsep_count_eq, ← hCn] at hnat
  have h1 := natCast_le_mul_div_of_mul_le
    (Nat.mul_ne_zero Fintype.card_ne_zero Fintype.card_ne_zero) hnat
  have hT0 : (T3 : ℝ≥0∞) ≠ 0 := by
    rw [← hT]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [uavg_ite_zero_one, hT]
  calc (T3 : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun t : (Z → X) × (X → Z) × (X → Z) ↦
        ¬HmsgHSep (pubES P π t.1 (t.2.1, t.2.2)) v).card : ℝ≥0∞)
      ≤ (T3 : ℝ≥0∞)⁻¹ * (T3 * ((Cn : ℝ≥0∞) /
          ((Fintype.card X * Fintype.card Z : ℕ) : ℝ≥0∞))) := by gcongr
    _ = (Cn : ℝ≥0∞) / ((Fintype.card X * Fintype.card Z : ℕ) : ℝ≥0∞) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hT0 (ENNReal.natCast_ne_top _), one_mul]
    _ ≤ ENNReal.ofReal (1 / 2 ^ 199) := by
        rw [hCn]
        exact hsepTerm_le (card_rndT_le P) card_message_digestCall rnCard_X rnCard_Z

/-- The data as the keys `(h, k, k')` and the rest `(PK.seed, π, v)`. -/
def hsepEquiv : FullES ≃
    (PublicParameter × Equiv.Perm (X × Z) × ((s : HPos) → XD s)) × ((Z → X) × (X → Z) × (X → Z))
    where
  toFun ω := ((ω.1.1, ω.1.2.1, ω.2.2), (ω.1.2.2, ω.2.1.1, ω.2.1.2))
  invFun y := ((y.1.1, y.1.2.1, y.2.1), ((y.2.2.1, y.2.2.2), y.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Classical in
/-- **`HmsgHSep` fails, off `seedBadSet`, for at most `2^-199 + 2^-777` of all data** (the bad
permutations `2^-777`). -/
theorem uavg_hmsgHSep_full_le :
    uavg (fun ω : FullES ↦ if HmsgHSep (pubES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2.1) ω.2.2 ∨
      ω.1.1 ∈ seedBadSet then (0 : ℝ≥0∞) else 1) ≤
      ENNReal.ofReal (1 / 2 ^ 199) + ENNReal.ofReal (1 / 2 ^ 777) := by
  refine (le_of_eq (uavg_comp_equiv hsepEquiv fun y ↦
    if HmsgHSep (pubES y.1.1 y.1.2.1 y.2.1 (y.2.2.1, y.2.2.2)) y.1.2.2 ∨ y.1.1 ∈ seedBadSet then
      (0 : ℝ≥0∞) else 1)).trans ?_
  rw [uavg_prod_iter]
  refine (uavg_mono (g := fun q : PublicParameter × Equiv.Perm (X × Z) × ((s : HPos) → XD s) ↦
    ENNReal.ofReal (1 / 2 ^ 199) + if PermGood q.2.1 18 then (0 : ℝ≥0∞) else 1)
    fun q ↦ ?_).trans ?_
  · by_cases hG : PermGood q.2.1 18
    · rw [ite_eq_left hG, add_zero]
      by_cases hb : q.1 ∈ seedBadSet
      · refine (uavg_mono (g := fun _ ↦ (0 : ℝ≥0∞)) fun t ↦ ?_).trans
          ((uavg_const_le 0).trans zero_le)
        rw [ite_eq_left (Or.inr hb)]
      · refine (uavg_mono (g := fun t : (Z → X) × (X → Z) × (X → Z) ↦
          if HmsgHSep (pubES q.1 q.2.1 t.1 (t.2.1, t.2.2)) q.2.2 then (0 : ℝ≥0∞) else 1)
          fun t ↦ ?_).trans (uavg_hmsgHSep_le hG.rate hb q.2.2)
        by_cases hh : HmsgHSep (pubES q.1 q.2.1 t.1 (t.2.1, t.2.2)) q.2.2
        · rw [ite_eq_left (Or.inl hh), ite_eq_left hh]
        · rw [ite_eq_right fun h ↦ h.elim hh hb, ite_eq_right hh]
    · rw [ite_eq_right hG]
      refine (uavg_mono (g := fun _ ↦ (1 : ℝ≥0∞)) fun t ↦ ?_).trans
        ((uavg_const_le 1).trans le_add_self)
      split_ifs
      · exact zero_le
      · exact le_rfl
  · rw [uavg_add]
    refine add_le_add (uavg_const_le _) ?_
    have hπ : uavg (fun q : PublicParameter × Equiv.Perm (X × Z) × ((s : HPos) → XD s) ↦
        if PermGood q.2.1 18 then (0 : ℝ≥0∞) else 1) =
        uavg (fun π : Equiv.Perm (X × Z) ↦ if PermGood π 18 then (0 : ℝ≥0∞) else 1) :=
      (uavg_snd_marg (K := PublicParameter)
        (fun r : Equiv.Perm (X × Z) × ((s : HPos) → XD s) ↦
          if PermGood r.1 18 then (0 : ℝ≥0∞) else 1)).trans
        (uavg_fst_marg fun π : Equiv.Perm (X × Z) ↦ if PermGood π 18 then (0 : ℝ≥0∞) else 1)
    rw [hπ, uavg_ite_zero_one, mul_comm, ← div_eq_mul_inv]
    exact permTerm_le_keccak

end hmsgHSep

/-! ## The bound -/

section bound

/-- An indicator below `1` is `0`. -/
theorem of_ite_lt_one {p : Prop} [Decidable p] (h : (if p then (0 : ℝ≥0∞) else 1) < 1) : p := by
  by_contra hp
  rw [ite_eq_right hp] at h
  exact lt_irrefl _ h

/-- **The fraction off `GoodES`**: `2^-639` (`HZLoad`), `2^-128` (`HSelfSep`), `2^-400`
(`PathsDisjoint`), `2^-400` (`TrialsOff`), `2^-81` (`seedBadSet`: `NoHmsgHead` and the first
blocks of `HmsgSep`), `2^-396` (the later rounds of `HmsgSep`), `2^-199 + 2^-777` (`HmsgHSep`). -/
noncomputable def goodESCap : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 2 ^ 639) + ENNReal.ofReal (1 / 2 ^ 128) + (2 ^ 400 : ℝ≥0∞)⁻¹ +
    ENNReal.ofReal (1 / 2 ^ 400) + ENNReal.ofReal (1 / 2 ^ 81) + ENNReal.ofReal (1 / 2 ^ 396) +
    (ENNReal.ofReal (1 / 2 ^ 199) + ENNReal.ofReal (1 / 2 ^ 777))

set_option exponentiation.threshold 4096 in
theorem goodESCap_le : goodESCap ≤ ENNReal.ofReal (1 / 2 ^ 80) := by
  have e : (2 ^ 400 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 ^ 400) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  unfold goodESCap
  rw [e, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 199)
      (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 777),
    ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 639)
      (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 128),
    ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 639 + 1 / 2 ^ 128)
      (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 400),
    ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 639 + 1 / 2 ^ 128 + 1 / 2 ^ 400)
      (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 400),
    ← ENNReal.ofReal_add
      (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 639 + 1 / 2 ^ 128 + 1 / 2 ^ 400 + 1 / 2 ^ 400)
      (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 81),
    ← ENNReal.ofReal_add (by positivity :
      (0 : ℝ) ≤ 1 / 2 ^ 639 + 1 / 2 ^ 128 + 1 / 2 ^ 400 + 1 / 2 ^ 400 + 1 / 2 ^ 81)
      (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 396),
    ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤
      1 / 2 ^ 639 + 1 / 2 ^ 128 + 1 / 2 ^ 400 + 1 / 2 ^ 400 + 1 / 2 ^ 81 + 1 / 2 ^ 396)
      (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 199 + 1 / 2 ^ 777)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

open scoped Classical in
/-- **The fraction of all data off `GoodES`**: averaged over `PK.seed`, `π`, `h`, the keys and the
hidden values, at most `goodESCap ≤ 2^-80` (`goodESCap_le`). -/
theorem uavg_not_goodES_le :
    uavg (fun ω : FullES ↦ if GoodES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2 then (0 : ℝ≥0∞) else 1) ≤
      goodESCap := by
  have hpt : ∀ ω : FullES, (if GoodES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2 then (0 : ℝ≥0∞) else 1) ≤
      (if HZLoad (pubES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2.1) then (0 : ℝ≥0∞) else 1) +
        (if HSelfSep (pubES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2.1) ω.2.2 then (0 : ℝ≥0∞) else 1) +
        (if PathsDisjoint (disjEquiv ω).1.1.2 (disjEquiv ω).1.1.1 (disjEquiv ω).2 then
          (0 : ℝ≥0∞) else 1) +
        (if TrialsOff (rawEquiv ω).1.1.2 (rawEquiv ω).1.1.1 (rawEquiv ω).1.2 then
          (0 : ℝ≥0∞) else 1) +
        (if ω.1.1 ∉ seedBadSet then (0 : ℝ≥0∞) else 1) +
        (if HmsgSepR (rawEquiv ω).1.1.2 (rawEquiv ω).1.1.1 (rawEquiv ω).1.2 ∨
          (rawEquiv ω).1.1.2.1 ∈ seedBadSet then (0 : ℝ≥0∞) else 1) +
        (if HmsgHSep (pubES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2.1) ω.2.2 ∨ ω.1.1 ∈ seedBadSet then
          (0 : ℝ≥0∞) else 1) := by
    intro ω
    by_cases hg : GoodES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2
    · rw [ite_eq_left hg]
      exact zero_le
    rw [ite_eq_right hg]
    by_contra hlt
    rw [not_le] at hlt
    have c1 := of_ite_lt_one ((le_self_add.trans (le_self_add.trans (le_self_add.trans
      (le_self_add.trans (le_self_add.trans le_self_add))))).trans_lt hlt)
    have c2 := of_ite_lt_one ((le_add_self.trans (le_self_add.trans (le_self_add.trans
      (le_self_add.trans (le_self_add.trans le_self_add))))).trans_lt hlt)
    have c3 := of_ite_lt_one ((le_add_self.trans (le_self_add.trans (le_self_add.trans
      (le_self_add.trans le_self_add)))).trans_lt hlt)
    have c4 := of_ite_lt_one ((le_add_self.trans (le_self_add.trans (le_self_add.trans
      le_self_add))).trans_lt hlt)
    have c5 := of_ite_lt_one ((le_add_self.trans (le_self_add.trans le_self_add)).trans_lt hlt)
    have c6 := of_ite_lt_one ((le_add_self.trans le_self_add).trans_lt hlt)
    have c7 := of_ite_lt_one (le_add_self.trans_lt hlt)
    refine hg ⟨c1, c3, c6.resolve_right c5, c7.resolve_right c5, c2, c4, ?_⟩
    by_contra hh
    exact c5 (seed_mem_of_not_noHmsgHead hh)
  have h1 : uavg (fun ω : FullES ↦
      if HZLoad (pubES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2.1) then (0 : ℝ≥0∞) else 1) ≤
      ENNReal.ofReal (1 / 2 ^ 639) :=
    uavg_le_of_keys (F := fun P π hk kk ↦ if HZLoad (pubES P π hk kk) then (0 : ℝ≥0∞) else 1)
      fun P π hk ↦ uavg_hZLoad_le P π hk
  have h2 : uavg (fun ω : FullES ↦
      if HSelfSep (pubES ω.1.1 ω.1.2.1 ω.1.2.2 ω.2.1) ω.2.2 then (0 : ℝ≥0∞) else 1) ≤
      ENNReal.ofReal (1 / 2 ^ 128) :=
    uavg_le_of_keys_vals
      (F := fun P π hk kk v ↦ if HSelfSep (pubES P π hk kk) v then (0 : ℝ≥0∞) else 1)
      fun P π hk v ↦ uavg_hSelfSep_le P π hk v
  have h3 : uavg (fun ω : FullES ↦
      if PathsDisjoint (disjEquiv ω).1.1.2 (disjEquiv ω).1.1.1 (disjEquiv ω).2 then
        (0 : ℝ≥0∞) else 1) ≤ (2 ^ 400 : ℝ≥0∞)⁻¹ :=
    (uavg_disjEquiv fun y ↦ if PathsDisjoint y.1.1.2 y.1.1.1 y.2 then (0 : ℝ≥0∞) else 1).trans_le
      (uavg_not_pathsDisjoint_le HRest)
  have h4 : uavg (fun ω : FullES ↦
      if TrialsOff (rawEquiv ω).1.1.2 (rawEquiv ω).1.1.1 (rawEquiv ω).1.2 then
        (0 : ℝ≥0∞) else 1) ≤ ENNReal.ofReal (1 / 2 ^ 400) := by
    rw [uavg_rawEquiv fun y ↦ if TrialsOff y.1.2 y.1.1 y.2 then (0 : ℝ≥0∞) else 1,
      uavg_ite_zero_one]
    exact trialsOff_frac_le_keccak
  have h5 : uavg (fun ω : FullES ↦ if ω.1.1 ∉ seedBadSet then (0 : ℝ≥0∞) else 1) ≤
      ENNReal.ofReal (1 / 2 ^ 81) :=
    (uavg_seed fun P ↦ if P ∉ seedBadSet then (0 : ℝ≥0∞) else 1).trans_le uavg_seedBad_le
  have h6 : uavg (fun ω : FullES ↦
      if HmsgSepR (rawEquiv ω).1.1.2 (rawEquiv ω).1.1.1 (rawEquiv ω).1.2 ∨
        (rawEquiv ω).1.1.2.1 ∈ seedBadSet then (0 : ℝ≥0∞) else 1) ≤
      ENNReal.ofReal (1 / 2 ^ 396) := by
    rw [uavg_rawEquiv fun y ↦ if HmsgSepR y.1.2 y.1.1 y.2 ∨ y.1.2.1 ∈ seedBadSet then
      (0 : ℝ≥0∞) else 1, uavg_ite_zero_one]
    have hf : (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
        ¬(HmsgSepR y.1.2 y.1.1 y.2 ∨ y.1.2.1 ∈ seedBadSet)) =
        Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          ¬HmsgSepR y.1.2 y.1.1 y.2 ∧ y.1.2.1 ∉ seedBadSet :=
      Finset.filter_congr fun _ _ ↦ not_or
    rw [hf]
    exact hmsgSepR_frac_le_keccak
  refine (uavg_mono hpt).trans ?_
  rw [uavg_add, uavg_add, uavg_add, uavg_add, uavg_add, uavg_add]
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5)
    h6) uavg_hmsgHSep_full_le

end bound

end Quantum.Sphincs.Assembly

end
