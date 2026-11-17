module

public import Quantum.Qrom.Sphincs.Multi.GameT
public import Quantum.Qrom.Sphincs.Multi.StreamGame
public import Quantum.Qrom.Sphincs.Multi.GameTCalls
public import Quantum.Qrom.Sphincs.Multi.GameTFactsPre
public import Quantum.Qrom.Xmss.Multi.Hybrid

@[expose] public section

/-!
# The hidden-value hybrid of multi-user leanSPHINCS in the QROM (runtime 1 against runtime 2)

The `n`-user analog of `Quantum.Qrom.Sphincs.Hybrid`, after `Quantum.Qrom.Xmss.Multi.Hybrid`. The
multi-user QROM game is at most the bad fraction of tables plus runtime 1 on the realized template
over good tables (`muWinProb_le_uavg_goodSN`); the masked graded hybrid
(`uavg_mask_win_runtime1R_le_graded`, mask `GoodSN`) compares it with runtime 2.

* **The mask** (`GoodSN`): distinct `PK.seed`s. The template's result is `false` off it (`pdOK`),
  so runtime 2 never wins there (`p2SN_eq_zero_of_not`).
* **The collision term** (`uavg_not_goodTabN_le`): the table is bad with probability at most
  `C(n,2) (2^-128 + 2^-256)` (`collTermSN`): equal master seeds or equal `PK.seed`s.
* **Sources** (`cellSrcN`, `srcValsN`, `sourcesQSN`): a hidden cell of user `i` at a position `p`
  names the coordinates `(j, srcOf p)` of all users `j`. A key-expansion cell (`IsExpandCell`, no
  `PK.seed`) takes the single-user values of every user: they fix the master seed, `2^256` of
  `2^512` values each. Any other cell takes user `j`'s single-user values when no other user can
  make it its own, else none: at most one user contributes, `2^-128`. Per call `kappaQN n =
  2^-128 + n 2^-256`. On `GoodSN` the owner contributes (`srcVals_eq_empty_of_goodSN`).
* **Masses** (`uavg_mask_spongeMass_leSN`, `uavg_mask_readMass_leSN`): `q · kappaQN n` at the
  sponge calls, `verifyCalls · kappaQN n` at the reads; reads of encoding cells carry no mass
  (`readMass_le_readQSN`: no table cell is an encoding cell).
* **The hybrid** (`muWinProb_le_hybridSN`):
  `muWinProb ≤ collTermSN n + (√(E p2SN strPolN) + hybTermSN n q)²`.
-/

open Matrix IPFunctor MeasureTheory
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

set_option synthInstance.maxSize 2000

namespace Quantum.Qrom.Sphincs.Multi

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT runtime1R extCls Sources
  sum_totalWeight_portMass_runtimeR_le_inv revealThen revealThen_bind realizeT_bind₂ RevealVals)
open Quantum.Qrom.SufCma.Multi (muWinProb cmdCharge hashCharge signCharge)
open Quantum.Qrom.MultiUser (uavg_comp_fst' uavg_restrict_injective uavg_not_injective_le)

attribute [local irreducible] sphincsRom

variable {n : ℕ}

/-! ## The hidden cells -/

section cells

/-- **The hidden cells at `θ`**: the cells of all users' tables. -/
def hidCellsN (θ : TValsN n) : Set HashDomain :=
  {z | ∃ i p, cellOf (seedsOf θ i) p (tabOf (userOf θ i)) = z}

theorem covers_hwTN (θ : TValsN n) : Covers (hwTN θ) (hidCellsN θ) ∅ ∅ := by
  refine ⟨fun z hz ↦ ?_, fun _ hx ↦ absurd rfl hx, fun _ hx ↦ absurd rfl hx⟩
  by_contra h
  exact hz ((tableN (seedsOf θ)).tableDb_of_forall_ne fun a ha ↦ h ⟨a.1, a.2, ha⟩)

/-- No hidden cell is an encoding cell. -/
theorem isEncCell_of_mem_hidCellsN {θ : TValsN n} {z : HashDomain} (hz : z ∈ hidCellsN θ) :
    isEncCell z = false := by
  obtain ⟨i, p, rfl⟩ := hz
  exact isEncCell_cellOf _ _ _

/-- **A key-expansion cell**: a 44-byte input (no `PK.seed`). -/
def IsExpandCell (z : HashDomain) : Prop :=
  (decodeInput z).length = 44

instance instDecidablePredIsExpandCell : DecidablePred IsExpandCell := fun z ↦
  inferInstanceAs (Decidable ((decodeInput z).length = 44))

theorem isExpandCell_iff {z : HashDomain} : IsExpandCell z ↔ prefixS z = none := by
  unfold IsExpandCell prefixS
  by_cases h84 : (decodeInput z).length = 84
  · rw [ite_eq_left h84]
    exact ⟨fun h ↦ absurd (h.symm.trans h84) (by decide), fun h ↦ nomatch h⟩
  rw [ite_eq_right h84]
  by_cases h93 : (decodeInput z).length = 93
  · rw [ite_eq_left h93]
    exact ⟨fun h ↦ absurd (h.symm.trans h93) (by decide), fun h ↦ nomatch h⟩
  rw [ite_eq_right h93]
  by_cases h44 : (decodeInput z).length = 44
  · rw [ite_eq_left h44]
    exact ⟨fun _ ↦ rfl, fun _ ↦ h44⟩
  · rw [ite_eq_right h44]
    exact ⟨fun h ↦ absurd h h44, fun h ↦ nomatch h⟩

/-- A key-expansion cell is the cell of a key-expansion position. -/
theorem isExpandPos_of_isExpandCell {S0 : MasterSeed} {v : QTable} {p : Pos}
    (h : IsExpandCell (cellOf S0 p v)) : IsExpandPos p := by
  by_contra hp
  rw [isExpandCell_iff, prefixS_cellOf S0 v hp] at h
  exact nomatch h

theorem isExpandCell_cellOf {S0 : MasterSeed} {v : QTable} {p : Pos} (hp : IsExpandPos p) :
    IsExpandCell (cellOf S0 p v) :=
  isExpandCell_iff.2 (prefixS_cellOf_expand S0 v hp)

/-- The key expansion's source is the master seed. -/
theorem srcOf_of_isExpandPos {p : Pos} (hp : IsExpandPos p) : srcOf p = .val none := by
  obtain ⟨q, hq⟩ := p
  rcases hp with h | h
  · obtain rfl : q = .prfKey := h
    rfl
  · obtain rfl : q = .publicSeed := h
    rfl

end cells

/-! ## The good set and the collision term -/

section good

/-- **The mask of the hybrid**: the users' `PK.seed`s are pairwise distinct. -/
def GoodSN (θ : TValsN n) : Prop :=
  PDistinct (tabOfN θ)

noncomputable instance instDecidablePredGoodSN : DecidablePred (GoodSN (n := n)) :=
  Classical.decPred _

/-- **The collision term**: `C(n,2) (2^-128 + 2^-256)`. -/
noncomputable def collTermSN (n : ℕ) : ℝ≥0∞ :=
  n.choose 2 * ((2 ^ 128 : ℝ≥0∞)⁻¹ + (2 ^ 256 : ℝ≥0∞)⁻¹)

/-- A user's `PK.seed` is the digest of its pair at the position `PK.seed`. -/
theorem publicSeed_user_eq_pairDigest (w : QTableN n) (i : Fin n) :
    (w.user i).publicSeed = pairDigest (w (i, ⟨.publicSeed, trivial⟩)) := by
  unfold QTable.publicSeed QTable.dig pairDigest
  rw [QTable.out_of_inRange (w.user i) (p := .publicSeed) trivial]
  rfl

theorem pDistinct_of_pairDigest {w : QTableN n}
    (h : Function.Injective fun i ↦ pairDigest (w (i, ⟨.publicSeed, trivial⟩))) :
    PDistinct w := fun a b hab ↦
  h ((publicSeed_user_eq_pairDigest w a).symm.trans
    (hab.trans (publicSeed_user_eq_pairDigest w b)))

/-- **The collision bound**: the table of the hidden values is bad with probability at most
`C(n,2) (2^-128 + 2^-256)`. -/
theorem uavg_not_goodTabN_le :
    uavg (fun θ : TValsN n ↦ if (tableN (seedsOf θ)).good (tabOfN θ) then (0 : ℝ≥0∞) else 1) ≤
      collTermSN n := by
  refine (uavg_seedsOf_tabOfN (n := n)
    (fun S0 w ↦ if (tableN S0).good w then (0 : ℝ≥0∞) else 1)).trans_le ?_
  have hpt : ∀ x : (Fin n → MasterSeed) × QTableN n,
      (if (tableN x.1).good x.2 then (0 : ℝ≥0∞) else 1) ≤
        (if Function.Injective x.1 then (0 : ℝ≥0∞) else 1) +
          (if Function.Injective fun i ↦ pairDigest (x.2 (i, ⟨.publicSeed, trivial⟩))
            then (0 : ℝ≥0∞) else 1) := fun x ↦ by
    by_cases a : Function.Injective x.1
    · by_cases b : Function.Injective fun i ↦ pairDigest (x.2 (i, ⟨.publicSeed, trivial⟩))
      · rw [ite_eq_left (show (tableN x.1).good x.2 from
          goodN_of a (pDistinct_of_pairDigest b))]
        exact zero_le
      · rw [ite_eq_right b]
        split_ifs <;> simp
    · rw [ite_eq_right a]
      split_ifs <;> simp
  refine (uavg_mono hpt).trans ?_
  rw [uavg_add]
  have hcard : (Fintype.card MasterSeed : ℝ≥0∞) = 2 ^ 256 := by
    rw [Fintype.card_congr (Quantum.Xmss.bitsEquiv 256)]
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  have h1 : uavg (fun x : (Fin n → MasterSeed) × QTableN n ↦
      if Function.Injective x.1 then (0 : ℝ≥0∞) else 1) ≤ n.choose 2 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    refine (uavg_comp_fst' (B := QTableN n)
      fun S0 : Fin n → MasterSeed ↦ if Function.Injective S0 then (0 : ℝ≥0∞) else 1).trans_le ?_
    refine (uavg_not_injective_le (n := n) (fun b : MasterSeed ↦ b) (c := 1)
      (Quantum.Qrom.Xmss.Multi.card_filter_eq_le_one (β := MasterSeed))).trans_eq ?_
    rw [hcard, Nat.cast_one, one_div]
  have h2 : uavg (fun x : (Fin n → MasterSeed) × QTableN n ↦
      if Function.Injective fun i ↦ pairDigest (x.2 (i, ⟨.publicSeed, trivial⟩))
        then (0 : ℝ≥0∞) else 1) ≤ n.choose 2 * (2 ^ 128 : ℝ≥0∞)⁻¹ := by
    set g : QTableN n → ℝ≥0∞ := fun w ↦
      if Function.Injective fun i ↦ pairDigest (w (i, ⟨.publicSeed, trivial⟩))
        then (0 : ℝ≥0∞) else 1 with hg
    refine ((Quantum.Sphincs.uavg_comp_equiv (Equiv.prodComm _ _)
      fun y : QTableN n × (Fin n → MasterSeed) ↦ g y.1).trans (uavg_comp_fst' g)).trans_le ?_
    have he : Function.Injective fun i : Fin n ↦ ((i, ⟨.publicSeed, trivial⟩) : PosN n) :=
      fun _ _ h ↦ (Prod.mk.inj h).1
    refine (uavg_restrict_injective _ he fun u : Fin n → PairOut ↦
      if Function.Injective fun i ↦ pairDigest (u i) then (0 : ℝ≥0∞) else 1).trans_le ?_
    refine (uavg_not_injective_le (n := n) pairDigest (c := 2 ^ 128 * 2 ^ 256)
      card_fiber_pairDigest_le).trans_eq ?_
    rw [pairFiber_div_card]
  refine (add_le_add h1 h2).trans_eq ?_
  rw [collTermSN, mul_add, add_comm]

end good

/-! ## The sources of the hidden cells -/

section sources

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

/-- **The mass per call**: `2^-128` for a cell with a `PK.seed` (one owner), `n 2^-256` for a
key-expansion cell (every user's master seed). -/
noncomputable def kappaQN (n : ℕ) : ℝ≥0∞ :=
  (2 ^ 128 : ℝ≥0∞)⁻¹ + n * (2 ^ 256 : ℝ≥0∞)⁻¹

/-- On a key-expansion cell, only the master seed is a source. -/
theorem srcVals_expand_eq_empty {z : HashDomain} (hz : IsExpandCell z) {s : TPos}
    (hs : s ≠ .val none) (θ : TVals) : srcVals z s θ = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun d hd ↦ ?_
  obtain ⟨p, hp, hc⟩ := mem_srcVals.1 hd
  have h' : IsExpandCell (cellQ (Function.update θ s d) p) := by
    rw [hc]
    exact hz
  exact hs (hp.symm.trans (srcOf_of_isExpandPos (isExpandPos_of_isExpandCell h')))

/-- The values of a key-expansion cell's source share the master seed. -/
theorem fst_eq_of_mem_srcVals_expand {z : HashDomain} (hz : IsExpandCell z) {θ : TVals}
    {d d' : TVal (.val none)} (hd : d ∈ srcVals z (.val none) θ)
    (hd' : d' ∈ srcVals z (.val none) θ) : (d : PairOut).1 = (d' : PairOut).1 := by
  obtain ⟨p, -, hc⟩ := mem_srcVals.1 hd
  obtain ⟨p', -, hc'⟩ := mem_srcVals.1 hd'
  have hpp : p = p' := pos_eq_of_cellOf_eq (hc.trans hc'.symm)
  rw [← hpp] at hc'
  have h' : IsExpandCell (cellQ (Function.update θ (.val none) d) p) := by
    rw [hc]
    exact hz
  have h := cellOf_expand_eq (isExpandPos_of_isExpandCell h') (hc.trans hc'.symm)
  simpa only [seedOf, Function.update_self] using h

/-- A set of pairs sharing their first component has at most `2^256` elements. -/
theorem card_le_of_fst_eq {F : Finset (HashOutput × HashOutput)}
    (h : ∀ d ∈ F, ∀ d' ∈ F, d.1 = d'.1) : F.card ≤ 2 ^ 256 := by
  have hinj : Set.InjOn Prod.snd (F : Set (HashOutput × HashOutput)) := fun d hd d' hd' he ↦
    Prod.ext (h d hd d' hd') he
  rw [← Finset.card_image_of_injOn hinj]
  exact (Finset.card_le_univ _).trans_eq Quantum.Qrom.Xmss.card_hashOutput

/-- **At most `2^256` values of a key-expansion cell's source**: they fix the master seed. -/
theorem card_srcVals_expand_le {z : HashDomain} (hz : IsExpandCell z) (θ : TVals) :
    (srcVals z (.val none) θ).card ≤ 2 ^ 256 :=
  card_le_of_fst_eq fun _ hd _ hd' ↦ fst_eq_of_mem_srcVals_expand hz hd hd'

theorem srcVals_frac_expand_le {z : HashDomain} (hz : IsExpandCell z) (s : TPos) (θ : TVals) :
    ((srcVals z s θ).card : ℝ≥0∞) * (Fintype.card (TVal s) : ℝ≥0∞)⁻¹ ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  by_cases hs : s = .val none
  · subst hs
    have hc : Fintype.card (TVal (.val none)) = Fintype.card (HashOutput × HashOutput) :=
      Fintype.card_congr (Equiv.refl _)
    have h0 : ((2 ^ 256 : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
    have ht : ((2 ^ 256 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [hc, Fintype.card_prod, Quantum.Qrom.Xmss.card_hashOutput]
    calc ((srcVals z (.val none) θ).card : ℝ≥0∞) * ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹
        ≤ ((2 ^ 256 : ℕ) : ℝ≥0∞) * ((2 ^ 256 * 2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ := by
          gcongr
          exact_mod_cast card_srcVals_expand_le hz θ
      _ = (2 ^ 256 : ℝ≥0∞)⁻¹ := by
          rw [Nat.cast_mul, ENNReal.mul_inv (.inl h0) (.inl ht), ← mul_assoc,
            ENNReal.mul_inv_cancel h0 ht, one_mul, Nat.cast_pow, Nat.cast_ofNat]
  · rw [srcVals_expand_eq_empty hz hs θ, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact zero_le

/-- The source coordinates of a cell: those of its position, for every user. -/
noncomputable def cellSrcN (z : HashDomain) : Finset (TPosN n) :=
  Finset.univ ×ˢ cellSrc z

/-- **User `i`'s values of the coordinate `t`** making `z` its cell: the single-user ones at a
key-expansion cell; elsewhere those when no other user can make `z` its cell by changing its own
coordinate `t`, else none (classical decidability spelled out). -/
noncomputable def srcValsN (z : HashDomain) (i : Fin n) (t : TPos) (θ : TValsN n) :
    Finset (TVal t) :=
  @ite _ (IsExpandCell z) (Classical.propDecidable _) (srcVals z t (userOf θ i))
    (@ite _ (∀ j, j ≠ i → srcVals z t (userOf θ j) = ∅) (Classical.propDecidable _)
      (srcVals z t (userOf θ i)) ∅)

theorem srcValsN_of_isExpandCell {z : HashDomain} (hz : IsExpandCell z) (i : Fin n) (t : TPos)
    (θ : TValsN n) : srcValsN z i t θ = srcVals z t (userOf θ i) :=
  ite_eq_left hz

theorem srcValsN_of_not {z : HashDomain} (hz : ¬IsExpandCell z) (i : Fin n) (t : TPos)
    (θ : TValsN n) : srcValsN z i t θ =
      @ite _ (∀ j, j ≠ i → srcVals z t (userOf θ j) = ∅) (Classical.propDecidable _)
        (srcVals z t (userOf θ i)) ∅ :=
  ite_eq_right hz

theorem srcValsN_subset (z : HashDomain) (i : Fin n) (t : TPos) (θ : TValsN n) :
    srcValsN z i t θ ⊆ srcVals z t (userOf θ i) := by
  unfold srcValsN
  split_ifs
  · exact subset_rfl
  · exact subset_rfl
  · exact Finset.empty_subset _

theorem srcValsN_update (z : HashDomain) (i : Fin n) (t : TPos) (θ : TValsN n) (d : TVal t) :
    srcValsN z i t (Function.update θ (i, t) d) = srcValsN z i t θ := by
  have hc : (∀ j, j ≠ i → srcVals z t (userOf (Function.update θ (i, t) d) j) = ∅) ↔
      ∀ j, j ≠ i → srcVals z t (userOf θ j) = ∅ :=
    forall_congr' fun j ↦ imp_congr_right fun hj ↦ by rw [userOf_update_of_ne θ hj]
  by_cases hz : IsExpandCell z
  · rw [srcValsN_of_isExpandCell hz, srcValsN_of_isExpandCell hz, userOf_update_self,
      srcVals_update]
  · rw [srcValsN_of_not hz, srcValsN_of_not hz, userOf_update_self, srcVals_update]
    by_cases h : ∀ j, j ≠ i → srcVals z t (userOf θ j) = ∅
    · rw [ite_eq_left h, ite_eq_left (hc.2 h)]
    · rw [ite_eq_right h, ite_eq_right (mt hc.1 h)]

/-- **At most one user has source values** at a cell other than a key-expansion cell. -/
theorem srcValsN_eq_empty {z : HashDomain} (hz : ¬IsExpandCell z) {t : TPos} {θ : TValsN n}
    {i j : Fin n} (h : (srcValsN z i t θ).Nonempty) (hji : j ≠ i) : srcValsN z j t θ = ∅ := by
  rw [srcValsN_of_not hz] at h ⊢
  by_cases hi : ∀ k, k ≠ i → srcVals z t (userOf θ k) = ∅
  · have hj := hi j hji
    split_ifs
    · exact hj
    · rfl
  · rw [ite_eq_right hi] at h
    exact absurd h Finset.not_nonempty_empty

/-- **On `GoodSN` no other user makes a cell with a `PK.seed` its own** by changing its value at
the cell's source coordinate. -/
theorem srcVals_eq_empty_of_goodSN {θ : TValsN n} (hG : GoodSN θ) (i j : Fin n) (hji : j ≠ i)
    {p : Pos} (hp : ¬IsExpandPos p) :
    srcVals (cellOf (seedsOf θ i) p (tabOf (userOf θ i))) (srcOf p) (userOf θ j) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun d hd ↦ ?_
  obtain ⟨p', -, hc⟩ := mem_srcVals.1 hd
  have hpp : p' = p := pos_eq_of_cellOf_eq hc
  rw [hpp] at hc
  have hP := (prefixS_cellOf _ _ hp).symm.trans ((congrArg prefixS hc).trans
    (prefixS_cellOf _ _ hp))
  have hs : pairAt (Function.update (userOf θ j) (srcOf p) d) seedC =
      pairAt (userOf θ j) seedC :=
    Function.update_of_ne (srcOf_ne_seedC p).symm _ _
  have he : (tabOf (userOf θ j)).publicSeed = (tabOf (userOf θ i)).publicSeed :=
    (publicSeed_tabOf_congr hs).symm.trans (Option.some.inj hP)
  exact hji (hG he)

/-- **The sum of the source fractions** of a cell is at most `kappaQN n`. -/
theorem sum_cellSrcN_le (z : HashDomain) (θ : TValsN n) :
    ∑ a ∈ cellSrcN (n := n) z, ((srcValsN z a.1 a.2 θ).card : ℝ≥0∞) *
      (Fintype.card (TValN n a) : ℝ≥0∞)⁻¹ ≤ kappaQN n := by
  unfold cellSrcN
  rw [Finset.sum_product]
  by_cases hz : IsExpandCell z
  · have hterm : ∀ (i : Fin n) (s : TPos), ((srcValsN z i s θ).card : ℝ≥0∞) *
        (Fintype.card (TVal s) : ℝ≥0∞)⁻¹ ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := fun i s ↦ by
      rw [srcValsN_of_isExpandCell hz]
      exact srcVals_frac_expand_le hz s _
    calc ∑ i : Fin n, ∑ s ∈ cellSrc z, ((srcValsN z i s θ).card : ℝ≥0∞) *
          (Fintype.card (TVal s) : ℝ≥0∞)⁻¹
        ≤ ∑ _i : Fin n, ∑ _s ∈ cellSrc z, (2 ^ 256 : ℝ≥0∞)⁻¹ :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun s _ ↦ hterm i s
      _ ≤ ∑ _i : Fin n, (2 ^ 256 : ℝ≥0∞)⁻¹ := Finset.sum_le_sum fun _ _ ↦ by
          rw [Finset.sum_const, nsmul_eq_mul]
          calc ((cellSrc z).card : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ ≤ 1 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
                gcongr
                exact_mod_cast card_cellSrc_le_one z
            _ = (2 ^ 256 : ℝ≥0∞)⁻¹ := one_mul _
      _ = n * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ kappaQN n := le_add_self
  · rw [Finset.sum_comm]
    have hs : ∀ s ∈ cellSrc z, ∑ i : Fin n, ((srcValsN z i s θ).card : ℝ≥0∞) *
        (Fintype.card (TVal s) : ℝ≥0∞)⁻¹ ≤ kappaQ := fun s _ ↦ by
      by_cases hex : ∃ i : Fin n, (srcValsN z i s θ).Nonempty
      · obtain ⟨i, hi⟩ := hex
        rw [Finset.sum_eq_single i (fun j _ hji ↦ by
          rw [srcValsN_eq_empty hz hi hji, Finset.card_empty, Nat.cast_zero, zero_mul])
          (fun h ↦ absurd (Finset.mem_univ i) h)]
        exact (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Finset.card_le_card
          (srcValsN_subset z i s θ))) zero_le).trans (srcVals_frac_le z s (userOf θ i))
      · simp only [not_exists, Finset.not_nonempty_iff_eq_empty] at hex
        rw [Finset.sum_eq_zero fun i _ ↦ by
          rw [hex i, Finset.card_empty, Nat.cast_zero, zero_mul]]
        exact zero_le
    calc ∑ s ∈ cellSrc z, ∑ i : Fin n, ((srcValsN z i s θ).card : ℝ≥0∞) *
          (Fintype.card (TVal s) : ℝ≥0∞)⁻¹
        ≤ ∑ _s ∈ cellSrc z, kappaQ := Finset.sum_le_sum hs
      _ = (cellSrc z).card * kappaQ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * kappaQ := by
          gcongr
          exact_mod_cast card_cellSrc_le_one z
      _ = kappaQ := one_mul _
      _ ≤ kappaQN n := by
          rw [kappaQN, kappaQ]
          exact le_self_add

/-- **The hidden cells on the good set**: all cells on `GoodSN`, none elsewhere. -/
def maskHidN (θ : TValsN n) : Set HashDomain :=
  {z | GoodSN θ ∧ z ∈ hidCellsN θ}

theorem maskHidN_of_goodSN {θ : TValsN n} (hG : GoodSN θ) : maskHidN θ = hidCellsN θ :=
  Set.ext fun _ ↦ and_iff_right hG

/-- **A masked hidden cell not hardwired has an undisclosed source** whose value is a source
value, on the states where every position with a disclosed source has its cell hardwired. -/
theorem hh_sourcesQSN {M : Type} (θ : TValsN n) (z : HashDomain)
    (r : HwReg PairOut HashDomain (Finset (TPosN n) × M))
    (hinv : SrcInvN θ r)
    (hz : z ∈ maskHidN θ) (hnone : r.2.1.1 z = none) :
    ∃ a ∈ cellSrcN z, a ∉ r.2.2.1 ∧ θ a ∈ srcValsN z a.1 a.2 θ := by
  obtain ⟨hG, i, p, rfl⟩ := hz
  refine ⟨(i, srcOf p), Finset.mem_product.2 ⟨Finset.mem_univ _,
    srcOf_mem_cellSrc (userOf θ i) p⟩, fun hp ↦ hinv i p hp hnone, ?_⟩
  change userOf θ i (srcOf p) ∈ srcValsN _ i (srcOf p) θ
  by_cases hz : IsExpandCell (cellOf (seedsOf θ i) p (tabOf (userOf θ i)))
  · rw [srcValsN_of_isExpandCell hz]
    exact self_mem_srcVals (userOf θ i) p
  · rw [srcValsN_of_not hz, ite_eq_left fun j hji ↦ srcVals_eq_empty_of_goodSN hG i j hji
      fun hp ↦ hz (isExpandCell_cellOf hp)]
    exact self_mem_srcVals (userOf θ i) p

/-- **The sources of the hidden cells on the good set**, on the states of the source invariant. -/
noncomputable def sourcesQSN :
    Sources PairOut HashDomain (TPosN n) (SelMemN n) (TPosN n) (TValN n) (fun r ↦ r.2.2.1)
      (fun θ ↦ SrcInvN θ) maskHidN (fun _ ↦ ∅) (fun _ ↦ ∅) (kappaQN n) where
  sh z _ := cellSrcN z
  sk _ _ := ∅
  sk' _ _ := ∅
  Fh z _ a θ := srcValsN z a.1 a.2 θ
  Fk _ _ _ _ := ∅
  Fk' _ _ _ _ := ∅
  hFh z _ a θ d := srcValsN_update z a.1 a.2 θ d
  hFk _ _ _ _ _ := rfl
  hFk' _ _ _ _ _ := rfl
  hh θ z r hinv hz hnone := hh_sourcesQSN θ z r hinv hz hnone
  hk _ _ _ _ hy := absurd hy (Set.notMem_empty _)
  hk' _ _ _ _ hy := absurd hy (Set.notMem_empty _)
  hκh z _ θ := sum_cellSrcN_le z θ
  hκk _ _ _ := by rw [Finset.sum_empty]; exact zero_le
  hκk' _ _ _ := by rw [Finset.sum_empty]; exact zero_le

end sources

/-! ## The masses of the game -/

section masses

/-- The initial state of the game and the register. -/
noncomputable def initSN :
    Matrix (QReg.of Unit × QReg.of (RRegSN n (SelMemN n)))
      (QReg.of Unit × QReg.of (RRegSN n (SelMemN n))) ℂ :=
  (SubState.basis ()).matrix ⊗ₖ
    (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).init.matrix

theorem initSN_posSemidef : (initSN (n := n)).PosSemidef :=
  ((SubState.basis ()).prod
    (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).init).posSemidef

theorem ofReal_trace_initSN_le_one : ENNReal.ofReal (initSN (n := n)).trace.re ≤ 1 :=
  ENNReal.ofReal_le_one.mpr
    ((SubState.basis ()).prod
      (runtimeR (X := PairOut) (Z := HashDomain) (m0SN (n := n))).init).trace_re_le_one

/-- The masked masses are those of the masked hidden sets. -/
theorem ite_totalWeight_le_maskHidSN {θ : TValsN n}
    (w : Set HashDomain → (i : (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).Port) →
      Matrix ((recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).In i ×
        QReg.of (RRegSN n (SelMemN n)))
        ((recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).In i ×
        QReg.of (RRegSN n (SelMemN n))) ℂ → ℝ≥0∞) (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n) :
    (if GoodSN θ then (runtimeR m0SN).totalWeight .instruments (w (hidCellsN θ))
      (muGameQSN pols valid A θ) initSN else 0) ≤
      (runtimeR m0SN).totalWeight .instruments (w (maskHidN θ)) (muGameQSN pols valid A θ)
        initSN := by
  split_ifs with hG
  · rw [maskHidN_of_goodSN hG]
  · exact zero_le

/-- **R2: the reads of encoding cells carry no hidden mass**: on hidden sets without encoding
cells, the read mass is that of the reads at cells other than encoding cells. -/
theorem readMass_le_readQSN {H : Set HashDomain} (hH : ∀ z ∈ H, isEncCell z = false)
    (i : (recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).Port)
    (σ : Matrix ((recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).In i ×
      QReg.of (RRegSN n (SelMemN n)))
      ((recHwSpec PairOut HashDomain (TPosN n) (SelMemN n)).In i ×
      QReg.of (RRegSN n (SelMemN n))) ℂ) :
    readMass H ∅ ∅ i σ ≤
      portMass (fun i ↦ readQSN (SelMemN n) (n := n) i = true) H ∅ ∅ i σ := by
  rcases i with (((_ | _ | _) | (⟨z, u⟩ | ⟨y, u⟩ | ⟨y, u⟩)) | c) | T
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · by_cases hz : isEncCell z = true
    · have hz' : z ∉ H := fun h ↦ by
        rw [hH z h] at hz
        exact Bool.false_ne_true hz
      simp [readMass, portMass, readQSN, encRead, hz, Quantum.Xmss.Assembly.extWeight,
        Quantum.Xmss.Assembly.sumWeight, hiddenMass, diagMass, hz']
    · simp only [Bool.not_eq_true] at hz
      simp only [readMass, portMass, readQSN, encRead, hz, Bool.not_false]
      split <;> simp
  · simp only [readMass, portMass, readQSN, encRead, Bool.not_false]
    split <;> simp
  · simp only [readMass, portMass, readQSN, encRead, Bool.not_false]
    split <;> simp
  · simp [readMass, portMass, Quantum.Xmss.Assembly.extWeight, Quantum.Xmss.Assembly.sumWeight,
      hiddenMass]
  · simp [readMass, portMass, Quantum.Xmss.Assembly.extWeight, Quantum.Xmss.Assembly.sumWeight]

variable (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
  {q total : ℕ}
  (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
  (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
include hhash hsign

/-- **The sponge-port masses on the good set**: at most `q · kappaQN n`, averaged over the hidden
values. -/
theorem uavg_mask_spongeMass_leSN :
    uavg (fun θ : TValsN n ↦ if GoodSN θ then (runtimeR m0SN).totalWeight .instruments
      (spongeMass (hidCellsN θ) ∅ ∅) (muGameQSN (msgPolN n) valid A θ) initSN else 0) ≤
      q * kappaQN n := by
  have hc : (fun i ↦ if (extCls PairOut HashDomain (Finset (TPosN n) × SelMemN n)
      (recSpec (TPosN n) (SelMemN n)) i = false) then 1 else 0) =
      fun i ↦ if extCls PairOut HashDomain (Finset (TPosN n) × SelMemN n)
        (recSpec (TPosN n) (SelMemN n)) i then 0 else 1 := by
    funext i
    rcases Bool.eq_false_or_eq_true (extCls PairOut HashDomain (Finset (TPosN n) × SelMemN n)
      (recSpec (TPosN n) (SelMemN n)) i) with h | h <;> simp [h]
  refine (uavg_mono fun θ ↦ ite_totalWeight_le_maskHidSN (fun H ↦ spongeMass H ∅ ∅)
    (msgPolN n) valid A).trans ?_
  refine Quantum.Qrom.Xmss.uavg_le_of_sum_le _ _ ((sum_totalWeight_portMass_runtimeR_le_inv
    .instruments
    (fun i ↦ extCls PairOut HashDomain (Finset (TPosN n) × SelMemN n)
      (recSpec (TPosN n) (SelMemN n)) i = false)
    m0SN (fun r ↦ r.2.2.1) (fun θ ↦ muGameQSN (msgPolN n) valid A θ) (fun _ ↦ initSN)
    (fun _ ↦ initSN_posSemidef)
    (fun j ↦ viewByOn_muGameT (SelMemN n) cwUpdN (msgPolN n) valid A m0SN initSN j)
    (fun θ ↦ SrcInvN θ)
    (fun θ ↦ forallQueries_muGameQSN cwUpdN (fun _ h ↦ Bool.noConfusion h)
      (fun _ h ↦ Bool.noConfusion h) (fun _ ↦ noVal_msgPol) m0SN valid A θ initSN
      (querySupportedOn_initQSN m0SN rfl _)) maskHidN (fun _ ↦ ∅) (fun _ ↦ ∅) (kappaQN n)
    sourcesQSN
    (fun θ ↦ by rw [hc]; exact advCalls_muGameQS cwUpdN (msgPolN n) valid A hhash hsign θ)).trans
    ?_)
  exact Quantum.Qrom.Xmss.sum_mul_trace_le (kappaQN n) _ ofReal_trace_initSN_le_one q

/-- **The read-port masses on the good set**: the verification's reads (the encoding reads carry
none), at most `verifyCalls · kappaQN n`, averaged over the hidden values. -/
theorem uavg_mask_readMass_leSN :
    uavg (fun θ : TValsN n ↦ if GoodSN θ then (runtimeR m0SN).totalWeight .instruments
      (readMass (hidCellsN θ) ∅ ∅) (muGameQSN (msgPolN n) valid A θ) initSN else 0) ≤
      verifyCalls * kappaQN n := by
  refine (uavg_mono fun θ ↦ (ite_totalWeight_le_maskHidSN (fun H ↦ readMass H ∅ ∅) (msgPolN n)
    valid A).trans (totalWeight_le_totalWeight (runtimeR m0SN) .instruments
      (fun i σ _ ↦ readMass_le_readQSN (fun z hz ↦ isEncCell_of_mem_hidCellsN hz.2) i σ)
      (muGameQSN (msgPolN n) valid A θ) initSN_posSemidef)).trans ?_
  refine Quantum.Qrom.Xmss.uavg_le_of_sum_le _ _ ((sum_totalWeight_portMass_runtimeR_le_inv
    .instruments (fun i ↦ readQSN (SelMemN n) (n := n) i = true) m0SN (fun r ↦ r.2.2.1)
    (fun θ ↦ muGameQSN (msgPolN n) valid A θ) (fun _ ↦ initSN) (fun _ ↦ initSN_posSemidef)
    (fun j ↦ viewByOn_muGameT (SelMemN n) cwUpdN (msgPolN n) valid A m0SN initSN j)
    (fun θ ↦ SrcInvN θ)
    (fun θ ↦ forallQueries_muGameQSN cwUpdN (fun _ h ↦ Bool.noConfusion h)
      (fun _ h ↦ Bool.noConfusion h) (fun _ ↦ noVal_msgPol) m0SN valid A θ initSN
      (querySupportedOn_initQSN m0SN rfl _)) maskHidN (fun _ ↦ ∅) (fun _ ↦ ∅) (kappaQN n)
    sourcesQSN (fun θ ↦ readQCalls_muGameQS cwUpdN (msgPolN n) valid A hhash hsign θ)).trans ?_)
  exact Quantum.Qrom.Xmss.sum_mul_trace_le (kappaQN n) _ ofReal_trace_initSN_le_one verifyCalls

end masses

/-! ## Runtime 2 off the mask -/

section mask

/-- A program relabelled to `false` never wins. -/
theorem evalDistMap_map_false {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec)
    {α : Type} (y : QComp spec (QReg.of Unit) (QReg.of Unit) α) (ρ : SubState (QReg.of Unit)) :
    R.evalDistMap .instruments (y.map fun _ ↦ false) ρ winObsQ {true} = 0 := by
  refine (QuantumRuntime.evalDistMap_apply R _ _ ρ winObsQ (measurableSet_singleton true)).trans
    (ENNReal.tsum_eq_zero.2 fun p ↦ ?_)
  obtain ⟨u, hu, b⟩ := p
  cases hu
  cases b
  · simp [winObsQ]
  · have he : IsEmpty ((fun _ : α ↦ false) ⁻¹' {true}) := ⟨fun a ↦ absurd a.2 (by simp)⟩
    have h0 : (R.run₂ .instruments (y.map fun _ ↦ false)).branch true
        (ρ.matrix ⊗ₖ R.init.matrix) = 0 := by
      rw [QuantumRuntime.run₂_map, SubInstrument.branch_map_apply, tsum_empty]
    have h1 : (R.jointPost .instruments (y.map fun _ ↦ false) ρ
        ⟨QReg.of Unit, rfl, true⟩).matrix = 0 := h0
    rw [h1]
    simp

/-- Realizing keeps the relabelling of the value. -/
theorem realizeT_mapSN {M : Type} [Fintype M] [DecidableEq M] (θ : TValsN n) {A B : QReg}
    {α β : Type} (x : QComp (XSpecSN M n) A B α) (g : α → β) :
    realizeT θ (x.map g) = QuantumComp₂.map g (realizeT θ x) :=
  (congrArg (realizeT θ) (QuantumComp₂.map_eq_bind_pure g x)).trans
    ((realizeT_bind₂ θ x _).trans (QuantumComp₂.map_eq_bind_pure g _).symm)

/-- **Realized reveals agree** when their continuations agree at the revealed values. -/
theorem realizeT_revealThen_congrSN {M : Type} [Fintype M] [DecidableEq M] (θ : TValsN n)
    {B C : QReg} {α : Type} (T : Finset (TPosN n))
    {k k' : RevealVals (TValN n) T × (Finset (TPosN n) × M) → QComp (XSpecSN M n) B C α}
    (hk : ∀ m, k (restrictTo T θ, m) = k' (restrictTo T θ, m)) :
    realizeT θ (revealThen goodQN T k) = realizeT θ (revealThen goodQN T k') := by
  have h : ∀ k₀ : RevealVals (TValN n) T × (Finset (TPosN n) × M) → QComp (XSpecSN M n) B C α,
      realizeT θ (revealThen goodQN T k₀) =
        QuantumComp₂.queryBind (L := LocalSig.instruments)
          (spec := recHwSpec PairOut HashDomain (TPosN n) M) (.inr T) B
          (Equiv.uniqueProd B Unit).symm fun mem ↦
            (QComp.act (A := QReg.of ((recHwSpec PairOut HashDomain (TPosN n) M).Out (.inr T) × B))
              (B := B) (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
                realizeT θ (k₀ (restrictTo T θ, mem)) := fun _ ↦ rfl
  rw [h, h]
  congr 1
  funext mem
  congr 1
  funext _
  exact congrArg (realizeT θ) (hk mem)

/-- A read program whose result is always `false` is its relabelling to `false`. -/
theorem readsThenTN_eq_map_false (M : Type) [Fintype M] [DecidableEq M] {α : Type}
    (oa : OracleComp RomOracles α) (f : α → Bool) (hf : ∀ a, f a = false) :
    readsThenTN (n := n) M oa f = (readsThenTN M oa f).map fun _ ↦ false := by
  rw [readsThenTN_eq, QuantumComp₂.map_eq_bind_pure (fun _ ↦ false), QuantumComp₂.bind_assoc]
  refine congrArg (QuantumComp₂.bind _) (funext fun a ↦ ?_)
  rw [QuantumComp₂.pure_bind, hf a]

/-- A run followed by the verification at keys with equal `PK.seed`s returns `false`. -/
theorem bind_verifyTN_eq_map_false {M : Type} [Fintype M] [DecidableEq M]
    (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (x : QComp (XSpecSN M n) (QReg.of Unit) (QReg.of Unit) (MuRunS n))
    {pks : Fin n → PublicKey} (hpd : pdOK pks = false) :
    x.bind (fun run ↦ verifyTN M valid (pks, run)) =
      (x.bind fun run ↦ verifyTN M valid (pks, run)).map fun _ ↦ false := by
  rw [QuantumComp₂.map_eq_bind_pure, QuantumComp₂.bind_assoc]
  refine congrArg (QuantumComp₂.bind x) (funext fun run ↦ ?_)
  rw [← QuantumComp₂.map_eq_bind_pure]
  unfold verifyTN
  exact readsThenTN_eq_map_false M _ _ fun b ↦ by simp only [hpd, Bool.false_and]

/-- Off `GoodSN` the revealed public keys fail `pdOK`. -/
theorem pdOK_pksT_eq_false {θ : TValsN n} (h : ¬GoodSN θ) :
    pdOK (pksT (restrictTo (pkRevealN (n := n)) θ)) = false := by
  refine @decide_eq_false _ (Classical.propDecidable _) fun hi ↦ h fun a b hab ↦ hi ?_
  have hs : ∀ i, (pksT (restrictTo (pkRevealN (n := n)) θ) i).publicSeed =
      (tabOf (userOf θ i)).publicSeed := fun i ↦
    publicSeed_tabOf_congr (pairRN_restrictTo (Finset.mem_product.2
      ⟨Finset.mem_univ _, Finset.mem_insert_self _ _⟩) θ)
  exact (hs a).trans (hab.trans (hs b).symm)

/-- **Off `GoodSN` the realized game returns `false`**: it is its relabelling to `false`. -/
theorem muGameQSN_eq_map_false {θ : TValsN n} (h : ¬GoodSN θ) (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n) :
    muGameQSN pols valid A θ = (muGameQSN pols valid A θ).map fun _ ↦ false := by
  unfold muGameQSN
  rw [← realizeT_mapSN, muGameT, QuantumComp₂.map_eq_bind_pure, revealThen_bind]
  refine realizeT_revealThen_congrSN θ _ fun m ↦ ?_
  dsimp only
  rw [← QuantumComp₂.map_eq_bind_pure]
  exact bind_verifyTN_eq_map_false valid _ (pdOK_pksT_eq_false h)

end mask

/-! ## The hybrid -/

section hybrid

/-- **The hybrid term**: `√(4 q · q κ) + √(verifyCalls · κ)` at `κ = kappaQN n`. -/
noncomputable def hybTermSN (n q : ℕ) : ℝ≥0∞ :=
  (4 * (q * (q * kappaQN n))) ^ (2⁻¹ : ℝ) + (verifyCalls * kappaQN n) ^ (2⁻¹ : ℝ)

/-- **Runtime 1's win at the hidden values `θ`**: all users' table cells hardwired at the start. -/
noncomputable def p1SN (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (A : MuAdversaryS n) (θ : TValsN n) : ℝ≥0∞ :=
  (runtime1R PairOut HashDomain (hwTN θ) m0SN).evalDistMap .instruments
    (muGameQSN (msgPolN n) valid A θ) (SubState.basis ()) winObsQ {true}

/-- **Runtime 2's win at the digest policies `pols` and the hidden values `θ`.** -/
noncomputable def p2SN (pols : Fin n → DigestPolicy)
    (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
    (θ : TValsN n) : ℝ≥0∞ :=
  (runtimeR m0SN).evalDistMap .instruments (muGameQSN pols valid A θ) (SubState.basis ())
    winObsQ {true}

/-- **Runtime 2 never wins off `GoodSN`** (`pdOK` fails). -/
theorem p2SN_eq_zero_of_not {pols : Fin n → DigestPolicy}
    {valid : SufCma.SignLog Message (Option Signature) → Bool} {A : MuAdversaryS n}
    {θ : TValsN n} (h : ¬GoodSN θ) : p2SN pols valid A θ = 0 := by
  unfold p2SN
  rw [muGameQSN_eq_map_false h]
  exact evalDistMap_map_false _ _ _

/-- **The stream reindexing**: runtime 2's averaged win at `msgPolN` is that at `strPolN`. -/
theorem uavg_p2SN_msgPol_eq (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (A : MuAdversaryS n) : uavg (p2SN (msgPolN n) valid A) = uavg (p2SN (strPolN n) valid A) :=
  uavg_muGameT_msgPolN_eq_strPolN cwUpdN valid A (fun _ _ ↦ none) (SubState.basis ()) winObsQ
    (measurableSet_singleton true)

/-- **The mask moves to `GoodSN`**: the multi-user QROM game is at most the collision term plus
runtime 1 on `GoodSN`, averaged over the hidden values. -/
theorem muWinProb_le_uavg_maskSN (valid : SufCma.SignLog Message (Option Signature) → Bool)
    (A : MuAdversaryS n) :
    muWinProb sphincsRom valid n A ≤
      collTermSN n + uavg (fun θ ↦ if GoodSN θ then p1SN valid A θ else 0) := by
  refine (muWinProb_le_uavg_goodSN cwUpdN valid A m0SN).trans ?_
  rw [uavg_add]
  refine add_le_add uavg_not_goodTabN_le (uavg_mono fun θ ↦ ?_)
  by_cases hg : (tableN (seedsOf θ)).good (tabOfN θ)
  · have hG : GoodSN θ := (show goodN (seedsOf θ) (tabOfN θ) from hg).2
    rw [ite_eq_left hg, ite_eq_left hG]
    exact le_rfl
  · rw [ite_eq_right hg]
    exact zero_le

variable (valid : SufCma.SignLog Message (Option Signature) → Bool) (A : MuAdversaryS n)
  {q total : ℕ}
  (hhash : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge hashCharge) q)
  (hsign : ∀ pks, IFreeM.IsChargeBound (A pks) (cmdCharge signCharge) total)
include hhash hsign

/-- **The masked graded hybrid, averaged**: runtime 1 against runtime 2 at `msgPolN` on
`GoodSN`. -/
theorem uavg_mask_p1SN_le :
    uavg (fun θ ↦ if GoodSN θ then p1SN valid A θ else 0) ≤
      (uavg (fun θ ↦ if GoodSN θ then p2SN (msgPolN n) valid A θ else 0) ^ (2⁻¹ : ℝ) +
        hybTermSN n q) ^ 2 := by
  have h := Quantum.Qrom.Xmss.Multi.uavg_mask_win_runtime1R_le_graded .instruments hwTN
    hidCellsN (fun _ ↦ ∅) (fun _ ↦ ∅) covers_hwTN m0SN (fun θ ↦ muGameQSN (msgPolN n) valid A θ)
    (fun _ ↦ SubState.basis ()) (fun _ ↦ winObsQ) (measurableSet_singleton true) q
    (fun θ ↦ advCalls_muGameQS cwUpdN (msgPolN n) valid A hhash hsign θ) GoodSN
    (q * kappaQN n) (verifyCalls * kappaQN n) (uavg_mask_spongeMass_leSN valid A hhash hsign)
    (uavg_mask_readMass_leSN valid A hhash hsign)
  rw [add_assoc] at h
  exact h

/-- **The hidden-value hybrid of multi-user leanSPHINCS in the QROM**: `muWinProb ≤
C(n,2) (2^-128 + 2^-256) + (√(E p2SN strPolN) + hybTermSN n q)²`. -/
theorem muWinProb_le_hybridSN :
    muWinProb sphincsRom valid n A ≤
      collTermSN n + (uavg (p2SN (strPolN n) valid A) ^ (2⁻¹ : ℝ) + hybTermSN n q) ^ 2 := by
  refine (muWinProb_le_uavg_maskSN valid A).trans (add_le_add le_rfl
    ((uavg_mask_p1SN_le valid A hhash hsign).trans ?_))
  rw [← uavg_p2SN_msgPol_eq]
  refine pow_le_pow_left₀ zero_le (add_le_add (ENNReal.rpow_le_rpow (uavg_mono fun θ ↦ ?_)
    (by norm_num)) le_rfl) 2
  split_ifs
  · exact le_rfl
  · exact zero_le

end hybrid

end Quantum.Qrom.Sphincs.Multi

end
