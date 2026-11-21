module

public import Quantum.Xmss.Assembly.GameCongr
public import Quantum.Xmss.Assembly.SrcBad
public import Quantum.Xmss.Hybrid.SeedStage

@[expose] public section

/-!
# The composed reparametrization with the randomizer bases

MassesR0's `uavg_spongeMass_le_xmssR0` and `uavg_readMass_le_xmssR0` take the reparametrization `e`
of the padded table into public data, hidden values `HPos → Digest` and a never-revealed part
`RK × W`, its good set `G`, `hinj`, `hcard`, `hgame`, `hpath`, `hr0`, the seed families (`hseed`,
`hA`, `hA'`) and the bad fraction. Here they are all built.

* **The reparametrization** (`r0Phi`, `r0E`): SeedStage's `seedKSplit` (SchemeSplit's staged swap,
  R0Stage's randomizer-base `k`, `k'` and partial `h` stages, the seed paths' `k`, `k'` stages),
  then MassSources' chain-start exchange (`shufR`) and Reparam's `fwd`. The public data `RP` is
  Reparam's `(h'', w)` with SchemeSplit's public slot bits and the exchanged chain-start slots;
  the hidden values are `fwd`'s at `.inl` and the first `128` bits of the randomizer-base
  `h`-slots (`r0Coord`) at `.inr`; the never-revealed part is `RK = (S, S₀, κ, κ')` (the scheme
  seed and the master seed moved out of MassSources' `Rest`) with `RW` (the seed slots `SeedKS`
  and the other `960` bits of the `h`-slots). `r0Psi` is the bijection of the coordinates, so
  `r0E` is injective where Reparam's table is good (`r0E_injOn`) and `hcard` holds
  (`card_r0E_le`).
* **The good set** (`r0G Q G`): SeedStage's `seedKGood` (with R0Stage's `r0Good`) for the
  computations `Q`, `PermGood π G`, Reparam's `XGood` and `SrcGood` at the coordinates.
* **The paths' cells** (`hpath`, `r0E_hpath`): the public keys `k`, `k'`, `h` differ from the
  table's only at the seed paths' cells (`seedKSplit_spec`), the randomizer-base cells
  (`r0Split_keys_eq`) and SchemeSplit's hidden capacities; when the computations `Q` hash every
  in-table slot's input (`HashesSlots`), `SeedReadGood`, `ReadGood` and `GoodPS` keep these cells
  off the honest paths, so the keys agree on the paths (`KeysAt`, `r0G_keys`). The template is
  congruent in keys agreeing on a path (`stateAt_congr_keys`, `xVal_congr_keys`), which
  generalizes MassSources' transfer to public keys other than the table's (`cells_transfer_keys`,
  `hsub_keys`).
* **The never-revealed families** (`r0E_hr0`, `r0E_hseed`): MassesR0's `r0Good_subsets` and
  SeedStage's `seedKGood_subsets` at the coordinates (`permR_r0E`, `parR_r0E`, `rk_r0E`,
  `sk_r0E`). The hidden values agree with the table's at the in-table positions, the chain starts
  and the first labels' randomizer bases (`r0E_inl_eq`, `r0E_start_eq`, `r0E_inr_eq`).
* **`hgame`** (`hgame_r0E`): GameCongr's `hgame_xmssR0` assumes the public keys `k`, `k'` are the
  table's, which fails here; its slot-port agreement and game congruence are redone for keys
  agreeing on the paths (`slotPortsAgree_keys`, `realizeT_gameT_keys`), through GameCongr's
  `realizeT_gameT_congr`.
* **One computation per tree** (`treeQ`, indexed by `TIdx = Layer × Fin 2^16`): the value of a
  subtree root at level `16` by hash queries, hashing every in-table slot below it
  (`hashesSlots_treeQ`), at most `posReads` reads each (`length_honestEval_treeQ`). Over the
  `2^17` roots the per-computation read terms are about `2^23` times smaller than over MassSources'
  `posM` (one computation per position).
* **The bad fraction** (`r0G_frac_le_parts`): SeedStage's (`seedKGood`, with R0Stage's and
  SchemeSplit's), the bad permutations, Reparam's (`xGood_bad_frac_le`, with PathBad's) and
  SrcBad's. At Keccak's sizes with the tree computations and `G = 18`: `r0G_frac_le_keccak`, at
  most `2^-174`.
* `uavg_spongeMass_le_r0E`, `uavg_readMass_le_r0E`: MassesR0's bounds with every hypothesis
  discharged.
-/

open IPFunctor Matrix
open scoped ENNReal ComplexOrder

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss

/-! ## The composed reparametrization -/

section reparam

/-- The pads of the table: SchemeSplit's extra slots with R0Stage's randomizer-base slots, the
seed paths' `k`- and `k'`-slots (SeedStage), and Reparam's pad. -/
abbrev RE : Type := ((SeedSlots × CoinSlots R0.RLabel) × SeedKS) × (ValPos → Digest)

/-- SchemeSplit's public slot bits beyond the parameter, and the exchanged chain-start slots. -/
abbrev RS : Type := (Fin 832 → ZMod 2) × (Fin 960 → ZMod 2) × (CsIdx → X)

/-- The public slot bits are finite. -/
noncomputable instance instFintypeRS : Fintype RS :=
  inferInstanceAs (Fintype ((Fin 832 → ZMod 2) × (Fin 960 → ZMod 2) × (CsIdx → X)))

/-- **The public data**: Reparam's public coordinates `(h'', w)`, SchemeSplit's public slot bits
beyond the parameter, and the exchanged chain-start slots. -/
abbrev RP : Type :=
  ((Z → X) × XW) × RS

/-- The randomizer-base `h`-slots beyond their first `128` bits. -/
abbrev RPad : Type := RLabel → (Fin 960 → ZMod 2)

/-- The never-revealed pads (MassesR0's `W`): the seed paths' slots and the randomizer-base
`h`-slots beyond their first `128` bits. -/
abbrev RW : Type := SeedKS × RPad

/-- The never-revealed pads are finite. -/
noncomputable instance instFintypeRW : Fintype RW :=
  inferInstanceAs (Fintype (((SeedIdx → Z) × (SeedIdx → Z)) × (RLabel → (Fin 960 → ZMod 2))))

open scoped Classical in
/-- The public data are finite. -/
noncomputable instance instFintypeRP : Fintype RP :=
  inferInstanceAs (Fintype (((Z → X) × XW) × RS))

/-- R0Stage's table of a padded table. -/
def thetaOf (t : HonestTable × RE) : CTab R0.RLabel :=
  ((t.1, t.2.1.1.1), t.2.1.1.2)

/-- SeedStage's table of a padded table. -/
def xOf (t : HonestTable × RE) : CTab R0.RLabel × SeedKS :=
  (thetaOf t, t.2.1.2)

/-- The padded tables as SeedStage's tables with Reparam's pad. -/
def splitR0 : HonestTable × RE ≃ (CTab R0.RLabel × SeedKS) × (ValPos → Digest) where
  toFun t := (xOf t, t.2.2)
  invFun x := (x.1.1.1.1, (((x.1.1.1.2, x.1.1.2), x.1.2), x.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- SeedStage's coordinates with the pad, reordered for `shufR`. -/
def reorderR : ((CPub R0.RLabel × MasterSeed) × SeedKS) × (ValPos → Digest) ≃
    ((Hybrid.Pub × MasterSeed) × (ValPos → Digest)) × (CoinSlots R0.RLabel × SeedKS) where
  toFun x := (((x.1.1.1.1, x.1.1.2), x.2), (x.1.1.1.2, x.1.2))
  invFun y := ((((y.1.1.1, y.2.1), y.1.1.2), y.2.2), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The table as Reparam's table, the rest, the randomizer-base and the seed slots**: SeedStage's
`seedKSplit` (R0Stage's `r0Split`, then the seed paths' `k`, `k'` stages), then MassSources'
chain-start exchange `shufR`. -/
noncomputable def r0Phi : HonestTable × RE ≃ (RTab × Rest) × (CoinSlots R0.RLabel × SeedKS) :=
  ((splitR0.trans ((seedKSplit R0.rCell R0.rOrd).prodCongr (Equiv.refl _))).trans
    reorderR).trans (shufR.prodCongr (Equiv.refl _))

theorem r0Phi_apply (t : HonestTable × RE) :
    r0Phi t = (shufR (((seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1,
      (seedKSplit R0.rCell R0.rOrd (xOf t)).1.2), t.2.2),
      ((seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.2, (seedKSplit R0.rCell R0.rOrd (xOf t)).2)) :=
  rfl

/-- **The coordinates**: Reparam's public data `((h'', w), v)` and the rest with the
randomizer-base and seed slots as the public data `RP`, the hidden values (`v` at `.inl`, the
first `128` bits of the `h`-slots at `.inr`), and the never-revealed part (`S`, `S₀`, the `k`- and
`k'`-slots of the labels, the seed slots, the other bits of the `h`-slots). -/
def r0Psi : ((((Z → X) × XW) × (ValPos → Digest)) × Rest) × (CoinSlots R0.RLabel × SeedKS) ≃
    RP × ((HPos → Digest) × (RK × RW)) where
  toFun x := ((x.1.1.1, (x.1.2.2.1, x.1.2.2.2.1, x.1.2.2.2.2.1)),
    (Sum.elim x.1.1.2 fun a ↦ (r0SlotEquiv (x.2.1.2.2 a)).1,
      ((x.1.2.2.2.2.2, x.1.2.1, x.2.1.1, x.2.1.2.1),
        (x.2.2, fun a ↦ (r0SlotEquiv (x.2.1.2.2 a)).2))))
  invFun y := (((y.1.1, fun q ↦ y.2.1 (.inl q)),
      (y.2.2.1.2.1, y.1.2.1, y.1.2.2.1, y.1.2.2.2, y.2.2.1.1)),
    ((y.2.2.1.2.2.1, y.2.2.1.2.2.2, fun a ↦ r0SlotEquiv.symm (y.2.1 (.inr a), y.2.2.2.2 a)),
      y.2.2.2.1))
  left_inv x := by
    obtain ⟨⟨⟨hw, v⟩, rest⟩, ⟨κ, κ', hc⟩, sk⟩ := x
    exact Prod.ext rfl (Prod.ext (Prod.ext rfl (Prod.ext rfl (funext fun a ↦
      r0SlotEquiv.symm_apply_apply (hc a)))) rfl)
  right_inv y := by
    obtain ⟨p, V, k, sk, pad⟩ := y
    refine Prod.ext rfl (Prod.ext (funext fun s ↦ ?_) (Prod.ext rfl (Prod.ext rfl
      (funext fun a ↦ ?_))))
    · cases s with
      | inl q => rfl
      | inr a => exact congrArg Prod.fst (r0SlotEquiv.apply_symm_apply (V (.inr a), pad a))
    · exact congrArg Prod.snd (r0SlotEquiv.apply_symm_apply (V (.inr a), pad a))

/-- **The reparametrization** (MassesR0's `e`): `r0Phi`, Reparam's `fwd` on Reparam's table, then
`r0Psi`. -/
noncomputable def r0E (t : HonestTable × RE) : RP × ((HPos → Digest) × (RK × RW)) :=
  r0Psi ((fwd xmssFix xO (r0Phi t).1.1, (r0Phi t).1.2), (r0Phi t).2)

/-- The template's public datum of the public data. -/
def pubR (p : RP) : Pub :=
  xPub p.1.2 p.1.1

/-- The public parameter of the public data. -/
def parR (p : RP) : PublicParameter :=
  p.1.2.1

/-- The permutation of the public data. -/
def permR (p : RP) : Equiv.Perm (X × Z) :=
  p.1.2.2.1

variable {ι : Type} {β : ι → Type}

/-- **The good set** (MassesR0's `G`): SeedStage's good set (with R0Stage's) for the
computations `Q`, a good permutation, Reparam's good set, and source goodness of the public data
and hidden values. -/
def r0G (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (G : ℕ)
    (t : HonestTable × RE) : Prop :=
  xOf t ∈ seedKGood R0.rCell R0.rOrd Q ∧ PermGood t.1.perm G ∧ XGood (r0Phi t).1.1 ∧
    SrcGood (pubX ((fwd xmssFix xO (r0Phi t).1.1).1, (r0Phi t).1.2))
      (fwd xmssFix xO (r0Phi t).1.1).2

/-- The good set is decidable (classically). -/
noncomputable instance instDecidablePredR0G
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (G : ℕ) :
    DecidablePred (r0G Q G) :=
  Classical.decPred _

/-- The reparametrization is injective where Reparam's table is good. -/
theorem r0E_injOn_xGood : Set.InjOn r0E {t | XGood (r0Phi t).1.1} := by
  intro t₁ h₁ t₂ h₂ he
  have h := r0Psi.injective he
  have hf : fwd xmssFix xO (r0Phi t₁).1.1 = fwd xmssFix xO (r0Phi t₂).1.1 :=
    (congrArg (fun y ↦ y.1.1) h :)
  have hθ := injOn_fwd xO_consistent (good_of_xGood h₁) (good_of_xGood h₂) hf
  exact r0Phi.injective (Prod.ext (Prod.ext hθ (congrArg (fun y ↦ y.1.2) h :))
    (congrArg (fun y ↦ y.2) h :))

/-- **`hinj`**: the reparametrization is injective on the good set. -/
theorem r0E_injOn (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (G : ℕ) : Set.InjOn r0E {t | r0G Q G t} :=
  r0E_injOn_xGood.mono fun _ h ↦ h.2.2.1

/-- Reparam's public data and hidden values as Reparam's tables. -/
def rtabEquiv : ((Z → X) × XW) × (ValPos → Digest) ≃ RTab where
  toFun y := ((y.1.1, y.2), y.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`hcard`**: the coordinates are as many as the padded tables. -/
theorem card_r0E_le :
    Fintype.card RP * Fintype.card ((HPos → Digest) × (RK × RW)) ≤
      Fintype.card (HonestTable × RE) := by
  rw [← Fintype.card_prod]
  exact (Fintype.card_congr (r0Psi.symm.trans
    (((rtabEquiv.prodCongr (Equiv.refl Rest)).prodCongr (Equiv.refl _)).trans r0Phi.symm))).le

end reparam

/-! ## The template is congruent in keys agreeing on a path -/

section keys

/-- **The keys of `pub₂` agree with `pub`'s at round `i`** of slot `s`'s path at the values `f`
(at its `k`-, `k'`- and `h`-cells). -/
def KeysAt (pub pub₂ : Pub) (s : Slot) (f : ValPos → Digest) (i : ℕ) : Prop :=
  pub₂.keys.2.1 (srcCellK pub s f i) = pub.keys.2.1 (srcCellK pub s f i) ∧
    pub₂.keys.2.2 (srcCellK' pub s f i) = pub.keys.2.2 (srcCellK' pub s f i) ∧
    pub₂.keys.1 (srcCellH pub s f i) = pub.keys.1 (srcCellH pub s f i)

theorem keysAt_congr (pub pub₂ : Pub) {s : Slot} {f f' : ValPos → Digest}
    (h : ∀ q, IsInput q s → f q = f' q) (i : ℕ) :
    KeysAt pub pub₂ s f i ↔ KeysAt pub pub₂ s f' i := by
  unfold KeysAt
  rw [cellK_congr pub h, cellK'_congr pub h, cellH_congr pub h]

theorem slotInput_eq_of_param {pub pub₂ : Pub} (hP : pub₂.param = pub.param) :
    slotInput pub₂ = slotInput pub := by
  funext s f
  unfold slotInput
  rw [hP]

theorem midAt_congr {pub pub₂ : Pub} (hπ : pub₂.perm = pub.perm) {s : X × Z} {b : X}
    (hk : pub₂.keys.2.1 (s.1 + b) = pub.keys.2.1 (s.1 + b)) : midAt pub₂ s b = midAt pub s b := by
  unfold midAt
  rw [hπ, hk]

/-- **Keys agreeing on a path's first `j` rounds keep its first `j` states.** -/
theorem stateAt_congr_keys {pub pub₂ : Pub} (hπ : pub₂.perm = pub.perm) (s : Slot)
    (f : ValPos → Digest) :
    ∀ j, j ≤ nBlocks pub s → (∀ i < j, KeysAt pub pub₂ s f i) →
      stateAt pub₂ (blocks (slotInput pub s f)) j = stateAt pub (blocks (slotInput pub s f)) j
  | 0, _, _ => rfl
  | j + 1, hj, hk => by
    have hlen : j < (blocks (slotInput pub s f)).length := by
      rw [length_blocks_slotInput]
      omega
    obtain ⟨h1, h2, h3⟩ := hk j (Nat.lt_succ_self j)
    have ih := stateAt_congr_keys hπ s f j (by omega) fun i hi ↦ hk i (by omega)
    have hm : midAt pub₂ (stateAt pub₂ (blocks (slotInput pub s f)) j)
        ((blocks (slotInput pub s f)).getD j 0) =
        midAt pub (stateAt pub (blocks (slotInput pub s f)) j)
          ((blocks (slotInput pub s f)).getD j 0) := by
      rw [ih]
      exact midAt_congr hπ h1
    change pub₂.keys.2.2 (midAt pub (stateAt pub (blocks (slotInput pub s f)) j)
      ((blocks (slotInput pub s f)).getD j 0)).1 =
      pub.keys.2.2 (midAt pub (stateAt pub (blocks (slotInput pub s f)) j)
        ((blocks (slotInput pub s f)).getD j 0)).1 at h2
    rw [srcCellH, roundH_fst] at h3
    rw [stateAt_succ _ _ hlen, stateAt_succ _ _ hlen, hm, h2, h3]

/-- **The cells of a path are congruent in keys agreeing on it** (same parameter and
permutation). -/
theorem cells_congr_keys {pub pub₂ : Pub} (hP : pub₂.param = pub.param)
    (hπ : pub₂.perm = pub.perm) {s : Slot} {f : ValPos → Digest}
    (hk : ∀ i < nBlocks pub s, KeysAt pub pub₂ s f i) {j : ℕ} (hj : j < nBlocks pub s) :
    srcCellK pub₂ s f j = srcCellK pub s f j ∧ srcCellK' pub₂ s f j = srcCellK' pub s f j ∧
      srcCellH pub₂ s f j = srcCellH pub s f j := by
  have hst := stateAt_congr_keys hπ s f j hj.le fun i hi ↦ hk i (by omega)
  have hsl := slotInput_eq_of_param hP
  obtain ⟨h1, h2, -⟩ := hk j hj
  have hm : midAt pub₂ (stateAt pub₂ (blocks (slotInput pub₂ s f)) j)
      ((blocks (slotInput pub₂ s f)).getD j 0) =
      midAt pub (stateAt pub (blocks (slotInput pub s f)) j)
        ((blocks (slotInput pub s f)).getD j 0) := by
    rw [hsl, hst]
    exact midAt_congr hπ h1
  refine ⟨?_, ?_, ?_⟩
  · show (stateAt pub₂ (blocks (slotInput pub₂ s f)) j).1 +
        (blocks (slotInput pub₂ s f)).getD j 0 =
      (stateAt pub (blocks (slotInput pub s f)) j).1 + (blocks (slotInput pub s f)).getD j 0
    rw [hsl, hst]
  · show (midAt pub₂ (stateAt pub₂ (blocks (slotInput pub₂ s f)) j)
        ((blocks (slotInput pub₂ s f)).getD j 0)).1 =
      (midAt pub (stateAt pub (blocks (slotInput pub s f)) j)
        ((blocks (slotInput pub s f)).getD j 0)).1
    rw [hm]
  · change pub₂.keys.2.2 (midAt pub (stateAt pub (blocks (slotInput pub s f)) j)
      ((blocks (slotInput pub s f)).getD j 0)).1 =
      pub.keys.2.2 (midAt pub (stateAt pub (blocks (slotInput pub s f)) j)
        ((blocks (slotInput pub s f)).getD j 0)).1 at h2
    rw [srcCellH, srcCellH, roundH_fst, roundH_fst, hm, h2]

/-- **A path's hash is congruent in keys agreeing on it.** -/
theorem spongeHash_congr_keys {pub pub₂ : Pub} (hP : pub₂.param = pub.param)
    (hπ : pub₂.perm = pub.perm) {s : Slot} {f : ValPos → Digest}
    (hk : ∀ i < nBlocks pub s, KeysAt pub pub₂ s f i) :
    spongeHash (spongePerm pub₂.keys pub₂.perm) (blocks (slotInput pub₂ s f)) =
      spongeHash (spongePerm pub.keys pub.perm) (blocks (slotInput pub s f)) := by
  rw [spongeHash_eq_stateAt, spongeHash_eq_stateAt, slotInput_eq_of_param hP,
    length_blocks_slotInput, stateAt_congr_keys hπ s f _ le_rfl hk]

/-- **The table's values are congruent in keys agreeing on the in-table outputs' paths** (by
rank). -/
theorem xVal_congr_keys {w w₂ : XW} {h h₂ : Z → X} {u : ValPos → Digest}
    (hP : w₂.1 = w.1) (hπ : w₂.2.1 = w.2.1)
    (hk : ∀ p, InPos p → ∀ i < nBlocks (xPub w h) (outSlot p),
      KeysAt (xPub w h) (xPub w₂ h₂) (outSlot p) (xVal w h u) i) :
    ∀ p, InPos p → xVal w₂ h₂ u p = xVal w h u p := by
  suffices H : ∀ n p, xRank p = n → InPos p → xVal w₂ h₂ u p = xVal w h u p from
    fun p hp ↦ H _ p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hn hp
  have hlow : ∀ t, xRank t < xRank p → xVal w₂ h₂ u t = xVal w h u t := fun t ht ↦ by
    by_cases htp : InPos t
    · exact ih _ (hn ▸ ht) t rfl htp
    · rw [xVal, xVal, ite_eq_right htp, ite_eq_right htp]
  have hx : ∀ (w₀ : XW) (h₀ : Z → X), xVal w₀ h₀ u p =
      xDig w₀ h₀ (slotInput (xPub w₀ h₀) (outSlot p) (xVal w₀ h₀ u)) := fun w₀ h₀ ↦ by
    rw [show xVal w₀ h₀ u p = recVal w₀ h₀ u p from ite_eq_left hp, recVal_eq_xDig w₀ h₀ u hp]
  rw [hx w₂ h₂, hx w h, slotInput_congr (xPub w₂ h₂) hp hlow]
  exact congrArg trunc128
    (spongeHash_congr_keys (pub := xPub w h) (pub₂ := xPub w₂ h₂) hP hπ (hk p hp))

/-- **The table's values at public keys agreeing with the table's on its paths** are the table's
(`valuePos`) at the in-table outputs. -/
theorem xVal_eq_valuePos_keys (L : HonestTable) {h : Z → X} {u : ValPos → Digest} {w : XW}
    (hP : w.1 = L.param) (hπ : w.2.1 = L.perm)
    (hu : ∀ l e i, u (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      KeysAt (pubOf L) (xPub w h) s (valuePos L) j)
    {p : ValPos} (hp : InPos p) : xVal w h u p = valuePos L p := by
  have hLk : ∀ s, InTable s → ∀ q, IsInput q s → xVal (wOf L) L.keys.1 u q = valuePos L q :=
    fun s hs q hin ↦ by
      by_cases hq : InPos q
      · exact xVal_wOf L u (fun l e i _ ↦ hu l e i) hq
      · rcases inPos_or_start hs hin with hp' | ⟨l, e, i, rfl⟩
        · exact absurd hp' hq
        · rw [xVal, ite_eq_right hq, hu]
          rfl
  rw [xVal_congr_keys (w := wOf L) (h := L.keys.1) hP hπ (fun p hp i hi ↦
    (keysAt_congr _ _ (hLk _ (inTable_outSlot hp)) i).mpr (hav _ (inTable_outSlot hp) i hi)) p hp]
  exact xVal_wOf L u (fun l e i _ ↦ hu l e i) hp

/-- **The transfer at public keys agreeing with the table's on its paths** (MassSources'
`cells_transfer` with `w` other than `wOf L`): the honest paths' cells of `L` are the template's
cells at the public data and the hidden values. -/
theorem cells_transfer_keys (L : HonestTable) {h : Z → X} {u : ValPos → Digest} {w : XW}
    (hθ : XGood ((h, u), w)) (hP : w.1 = L.param) (hπ : w.2.1 = L.perm)
    (hu : ∀ l e i, u (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      KeysAt (pubOf L) (xPub w h) s (valuePos L) j)
    {s : Slot} (hs : InTable s) {j : ℕ} (hj : j < nBlocks (pubOf L) s) :
    srcCellK (xPub w (fwd xmssFix xO ((h, u), w)).1.1) s (xVal w h u) j =
        srcCellK (pubOf L) s (valuePos L) j ∧
      srcCellK' (xPub w (fwd xmssFix xO ((h, u), w)).1.1) s (xVal w h u) j =
        srcCellK' (pubOf L) s (valuePos L) j ∧
      srcCellH (xPub w (fwd xmssFix xO ((h, u), w)).1.1) s (xVal w h u) j =
        srcCellH (pubOf L) s (valuePos L) j := by
  have hvals : ∀ q, IsInput q s → xVal w h u q = valuePos L q := fun q hin ↦ by
    by_cases hq : InPos q
    · exact xVal_eq_valuePos_keys L hP hπ hu hav hq
    · rcases inPos_or_start hs hin with hp' | ⟨l, e, i, rfl⟩
      · exact absurd hp' hq
      · rw [xVal, ite_eq_right hq, hu]
        rfl
  have hnb : nBlocks (xPub w h) s = nBlocks (pubOf L) s :=
    congrFun (nBlocks_eq_of_param (pub := xPub w h) (pub' := pubOf L) hP) s
  obtain ⟨e1, e2, e3⟩ := cells_fwd hθ hs (j := j) (by rw [hnb]; exact hj)
  rw [e1, e2, e3, cellK_congr _ hvals, cellK'_congr _ hvals, cellH_congr _ hvals]
  exact cells_congr_keys (pub := pubOf L) (pub₂ := xPub w h) hP hπ (fun i hi ↦ hav s hs i hi) hj

/-- **`hsub` at public keys agreeing with the table's on its paths**: over Reparam's table `θ`,
the table's hidden cells lie in the template's hidden sets at `fwd θ`. -/
theorem hsub_keys (L : HonestTable) (θ : RTab) (hθ : XGood θ) (hP : θ.2.1 = L.param)
    (hπ : θ.2.2.1 = L.perm)
    (hu : ∀ l e i, θ.1.2 (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      KeysAt (pubOf L) (xPub θ.2 θ.1.1) s (valuePos L) j)
    (hgood : SrcGood (xPub (fwd xmssFix xO θ).1.2 (fwd xmssFix xO θ).1.1) (fwd xmssFix xO θ).2) :
    pathH L ⊆ hidH (xPub (fwd xmssFix xO θ).1.2 (fwd xmssFix xO θ).1.1) (fwd xmssFix xO θ).2 ∧
      pathK L ⊆ hidK (xPub (fwd xmssFix xO θ).1.2 (fwd xmssFix xO θ).1.1)
        (fwd xmssFix xO θ).2 ∧
      pathK' L ⊆ hidK' (xPub (fwd xmssFix xO θ).1.2 (fwd xmssFix xO θ).1.1)
        (fwd xmssFix xO θ).2 := by
  obtain ⟨⟨h, u⟩, w⟩ := θ
  have hnb : ∀ s, nBlocks (xPub (fwd xmssFix xO ((h, u), w)).1.2 (fwd xmssFix xO ((h, u), w)).1.1)
      s = nBlocks (pubOf L) s :=
    congrFun (nBlocks_eq_of_param
      (pub := xPub (fwd xmssFix xO ((h, u), w)).1.2 (fwd xmssFix xO ((h, u), w)).1.1)
      (pub' := pubOf L) hP)
  refine ⟨fun z hz ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨s, hs, j, hj, rfl⟩ := mem_pathH hz
    exact ⟨hgood, s, hs, j, by rw [hnb]; exact hj,
      (cells_transfer_keys L hθ hP hπ hu hav hs hj).2.2⟩
  · obtain ⟨s, hs, j, hj, rfl⟩ := mem_pathK hx
    exact ⟨hgood, s, hs, j, by rw [hnb]; exact hj, (cells_transfer_keys L hθ hP hπ hu hav hs hj).1⟩
  · obtain ⟨s, hs, j, hj, rfl⟩ := mem_pathK' hx
    exact ⟨hgood, s, hs, j, by rw [hnb]; exact hj,
      (cells_transfer_keys L hθ hP hπ hu hav hs hj).2.1⟩

end keys

/-! ## Computations hashing the in-table slots -/

section hashes

variable {ι : Type} {β : ι → Type}

/-- **The computations `Q` hash every in-table slot's honest input** (evaluated honestly at the
table). -/
def HashesSlots (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) :
    Prop :=
  ∀ L : HonestTable, ∀ s, InTable s → ∃ i,
    slotInput (pubOf L) s (valuePos L) ∈
      queries (spongeOut (spongePerm L.keys L.perm)) (Q i L.param (csHash L))

/-- **A hashed slot's cells are read**: its `k`-, `k'`- and `h`-cells are among the reads of the
computation hashing it. -/
theorem cells_mem_schemeData
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
    {L : HonestTable} {s : Slot} {i : ι}
    (hi : slotInput (pubOf L) s (valuePos L) ∈
      queries (spongeOut (spongePerm L.keys L.perm)) (Q i L.param (csHash L)))
    {j : ℕ} (hj : j < nBlocks (pubOf L) s) :
    srcCellK (pubOf L) s (valuePos L) j ∈ kCells (schemeData Q L i).2 ∧
      srcCellK' (pubOf L) s (valuePos L) j ∈ k'Cells (schemeData Q L i).2 ∧
      srcCellH (pubOf L) s (valuePos L) j ∈ hCells (schemeData Q L i).2 := by
  have hr : (schemeData Q L i).2 =
      (queries (spongeOut (spongePerm L.keys L.perm)) (Q i L.param (csHash L))).flatMap
        (inputReads L.keys L.perm) :=
    snd_honestEval L.keys L.perm _
  rw [hr]
  obtain ⟨a, ha⟩ := cellK_mem_inputReads L s (valuePos L) hj
  obtain ⟨b, hb⟩ := cellK'_mem_inputReads L s (valuePos L) hj
  obtain ⟨c, hc⟩ := mem_hCells.mp (cellH_mem_hCells_inputReads L s (valuePos L) hj)
  exact ⟨mem_kCells.mpr ⟨a, List.mem_flatMap.mpr ⟨_, hi, ha⟩⟩,
    mem_k'Cells.mpr ⟨b, List.mem_flatMap.mpr ⟨_, hi, hb⟩⟩,
    mem_hCells.mpr ⟨c, List.mem_flatMap.mpr ⟨_, hi, hc⟩⟩⟩

/-! ### One computation per tree -/

section tree

variable (f : QueryImpl HashSpec Id)

theorem mem_queries_chainM_succ (P : PublicParameter) (Cs : CsIdx → HashOutput) (l : Layer)
    (e : KeyIndex) (i : ChainIndex) {j : ℕ} (hj : j < chainLength - 1) {q : HashInput}
    (h : q ∈ queries f (chainM P Cs l e i j)) : q ∈ queries f (chainM P Cs l e i (j + 1)) := by
  simp only [chainM, hj, ↓reduceDIte]
  exact mem_queries_bind_left f _ _ h

theorem mem_queries_chainM_le (P : PublicParameter) (Cs : CsIdx → HashOutput) (l : Layer)
    (e : KeyIndex) (i : ChainIndex) {j : ℕ} {q : HashInput}
    (h : q ∈ queries f (chainM P Cs l e i j)) :
    ∀ d, j + d ≤ chainLength - 1 → q ∈ queries f (chainM P Cs l e i (j + d))
  | 0, _ => h
  | d + 1, hd => mem_queries_chainM_succ f P Cs l e i (j := j + d) (by omega)
      (mem_queries_chainM_le P Cs l e i h d (by omega))

/-- **A subtree's queries are its ancestors'.** -/
theorem mem_queries_treeM_up (P : PublicParameter) (Cs : CsIdx → HashOutput) (l : Layer) :
    ∀ d lev index {q : HashInput}, q ∈ queries f (treeM P Cs l lev index) →
      q ∈ queries f (treeM P Cs l (lev + d) (index / 2 ^ d))
  | 0, lev, index, q, h => by simpa using h
  | d + 1, lev, index, q, h => by
    have ih := mem_queries_treeM_up P Cs l d lev index h
    have hdiv : index / 2 ^ d = 2 * (index / 2 ^ (d + 1)) + index / 2 ^ d % 2 := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul]
      omega
    show q ∈ queries f (treeM P Cs l (lev + d + 1) (index / 2 ^ (d + 1)))
    simp only [treeM]
    rcases Nat.mod_two_eq_zero_or_one (index / 2 ^ d) with h0 | h1
    · rw [h0, add_zero] at hdiv
      rw [hdiv] at ih
      exact mem_queries_bind_left f _ _ ih
    · rw [h1] at hdiv
      rw [hdiv] at ih
      exact mem_queries_bind_right f _ _ (mem_queries_bind_left f _ _ ih)

end tree

/-- The trees: a layer and a subtree root at level `16`. -/
abbrev TIdx : Type := Layer × Fin (2 ^ 16)

/-- **One computation per tree**: the value of a subtree root at level `16` by hash queries. -/
def treeQ (i : TIdx) (P : PublicParameter) (Cs : CsIdx → HashOutput) :
    OracleComp HashSpec Digest :=
  treeM P Cs i.1 16 i.2.val

/-- **The tree computations hash every in-table slot's input.** -/
theorem hashesSlots_treeQ : HashesSlots treeQ := by
  intro L s hs
  have hq := slotInput_mem_queries L hs
  cases s with
  | chain l e step i =>
    have hst := step.isLt
    have he : e.val < 2 ^ 16 * 2 ^ 16 := e.isLt
    refine ⟨(l, ⟨e.val / 2 ^ 16, (Nat.div_lt_iff_lt_mul (by positivity)).mpr he⟩), ?_⟩
    have hmod : (step.val + 1) % chainLength = step.val + 1 :=
      Nat.mod_eq_of_lt (by simp only [chainLength, winternitzBits] at hst ⊢; omega)
    change _ ∈ queries _ (chainM L.param (csHash L) l e i ((step.val + 1) % chainLength)) at hq
    rw [hmod] at hq
    have h3 := mem_queries_chainM_le _ L.param (csHash L) l e i hq
      (chainLength - 1 - (step.val + 1)) (by simp only [chainLength, winternitzBits] at hst ⊢; omega)
    rw [show step.val + 1 + (chainLength - 1 - (step.val + 1)) = chainLength - 1 by
      simp only [chainLength, winternitzBits] at hst ⊢; omega] at h3
    have h0 : slotInput (pubOf L) (.chain l e step i) (valuePos L) ∈
        queries (spongeOut (spongePerm L.keys L.perm)) (treeM L.param (csHash L) l 0 e.val) := by
      simp only [treeM]
      refine mem_queries_bind_left _ _ _ (mem_queries_sequenceFin _ _ i ?_)
      rw [leafKey_val]
      exact h3
    exact mem_queries_treeM_up _ L.param (csHash L) l 16 0 e.val h0
  | leaf l e =>
    have he : e.val < 2 ^ 16 * 2 ^ 16 := e.isLt
    refine ⟨(l, ⟨e.val / 2 ^ 16, (Nat.div_lt_iff_lt_mul (by positivity)).mpr he⟩), ?_⟩
    change _ ∈ queries _ (treeM L.param (csHash L) l (0 % (layerHeight + 1)) (e.val % 2 ^ 32)) at hq
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (show e.val < 2 ^ 32 from e.isLt)] at hq
    exact mem_queries_treeM_up _ L.param (csHash L) l 16 0 e.val hq
  | node l level index =>
    obtain ⟨h1, h2, h3⟩ := hs
    have hkb := keyBits_le l
    simp only [layerHeight] at h2
    have hidx : index < 2 ^ 16 * 2 ^ (16 - level) :=
      calc index < 2 ^ (keyBits l - level) := h3
        _ ≤ 2 ^ (16 + (16 - level)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ 16 * 2 ^ (16 - level) := pow_add _ _ _
    have h32 : index < 2 ^ 32 :=
      lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by norm_num) (by omega))
    refine ⟨(l, ⟨index / 2 ^ (16 - level), (Nat.div_lt_iff_lt_mul (by positivity)).mpr hidx⟩), ?_⟩
    change _ ∈ queries _ (treeM L.param (csHash L) l (level % (layerHeight + 1))
      (index % 2 ^ 32)) at hq
    rw [Nat.mod_eq_of_lt (show level < layerHeight + 1 by simp only [layerHeight]; omega),
      Nat.mod_eq_of_lt h32] at hq
    have h := mem_queries_treeM_up _ L.param (csHash L) l (16 - level) level index hq
    rw [show level + (16 - level) = 16 by omega] at h
    exact h
  | _ => exact absurd hs id

/-- **The reads of a tree computation**: at most `24 · 176 · 2^16` (at most `176 · 2^16` queries
of at most `8` blocks, `3` reads per block). -/
theorem length_honestEval_treeQ (i : TIdx) (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z))
    (P : PublicParameter) (Cs : CsIdx → HashOutput) :
    (honestEval t π (treeQ i P Cs)).2.length ≤ 24 * (176 * 2 ^ 16) := by
  rw [snd_honestEval]
  have hsat := queriesSatisfy_treeM (spongeOut (spongePerm t π)) P Cs i.1 16 i.2.val
  refine (length_flatMap_le _ 24 _ fun q hq ↦ ?_).trans (Nat.mul_le_mul_left 24 ?_)
  · rw [inputReads, length_spongeReads]
    have := hsat q hq
    omega
  · exact Nat.le_of_succ_le
      (length_queries_treeM (spongeOut (spongePerm t π)) P Cs i.1 16 i.2.val)

end hashes

/-! ## The good set's facts: `hpath`, `hr0`, and the hidden values -/

section good

variable {ι : Type} {β : ι → Type}
  {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)} {G : ℕ}
  {t : HonestTable × RE}

/-- Reparam's table of the coordinates, from SeedStage's. -/
theorem r0Phi_fst_fst (t : HonestTable × RE) : (r0Phi t).1.1 =
    (((seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1.1.keys.1,
      csxU (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1.2.2.2 t.2.2),
    ((paramEquiv (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1.2.2.1).1,
      (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1.1.perm,
      (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1.1.keys.2.1,
      (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1.1.keys.2.2)) :=
  rfl

/-- The permutation of Reparam's table is the table's. -/
theorem r0Phi_perm (t : HonestTable × RE) : (r0Phi t).1.1.2.2.1 = t.1.perm :=
  seedKSplit_perm R0.rCell R0.rOrd (xOf t)

/-- On the good set, the parameter of Reparam's table is the table's. -/
theorem r0G_param (ht : r0G Q G t) : (r0Phi t).1.1.2.1 = t.1.param := by
  rw [r0Phi_fst_fst]
  show (paramEquiv _).1 = _
  rw [seedKSplit_slots, paramEquiv_fst]
  exact (r0Split_coords R0.rCell_injective (mem_seedKGood.mp ht.1).1).1

/-- On the good set, Reparam's pad carries the table's chain starts. -/
theorem r0G_start (ht : r0G Q G t) (l : Layer) (e : KeyIndex) (i : ChainIndex) :
    (r0Phi t).1.1.1.2 (.chain l e i ⟨0, by decide⟩) = t.1.chainStart l e i := by
  obtain ⟨hgood, -, -⟩ := mem_r0Good.mp (mem_seedKGood.mp ht.1).1
  have hsl := (seedKSplit_slots R0.rCell R0.rOrd (xOf t)).trans
    (r0Split_slots R0.rCell R0.rOrd (xOf t).1)
  have hC : pubCs (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1 = csHash t.1 :=
    (congrArg (fun (s : PubSlots) (j : CsIdx) ↦ out256 (s.2.2 j)) hsl).trans
      (schemeSplit_transfer (xOf t).1.1 hgood.1).2.1
  rw [chainStart_eq_csHash, ← congrFun hC]
  show csxU (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1.2.2.2 t.2.2
    (.chain l e i ⟨0, by decide⟩) = _
  exact ite_eq_left rfl

/-- **On the good set, the public keys agree with the table's on its paths**: the seed paths'
cells, the randomizer-base cells and SchemeSplit's hidden capacities, where they differ, are not
read by the computations, which read the paths. -/
theorem r0G_keys (hQ : HashesSlots Q) (ht : r0G Q G t) :
    ∀ s, InTable s → ∀ j < nBlocks (pubOf t.1) s,
      KeysAt (pubOf t.1) (xPub (r0Phi t).1.1.2 (r0Phi t).1.1.1.1) s (valuePos t.1) j := by
  obtain ⟨hr0, -, hsread⟩ := mem_seedKGood.mp ht.1
  obtain ⟨hgood, hcoll, hread⟩ := mem_r0Good.mp hr0
  have hsd := schemeData_eq_pubData_r0Split R0.rCell_injective hr0
  have hsd' := schemeData_eq_of_mem (mem_schemeGood.mpr hgood)
  have hsd₂ := schemeData_eq_pubData_seedKSplit R0.rCell_injective R0.hidCell_ne_rCell ht.1
  obtain ⟨-, -, -, -, hguard⟩ := seedKGood_paths R0.rCell_injective R0.hidCell_ne_rCell ht.1
  obtain ⟨k₂, k'₂, sk₂, hE, f1, f2, f3⟩ := seedKSplit_spec R0.rCell R0.rOrd (xOf t)
  obtain ⟨-, f5⟩ := f3 hguard
  have hk₂ : (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1.1.keys.2.1 = k₂ := by rw [hE]
  have hk'₂ : (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1.1.keys.2.2 = k'₂ := by rw [hE]
  have hsc : ∀ b, seedCellK (seedKSplit R0.rCell R0.rOrd (xOf t)) b =
      hidCellOf (r0Split R0.rCell R0.rOrd (xOf t).1) b := fun b ↦ by
    rw [hE]
    rfl
  have hsc' : ∀ b, seedCellK' (seedKSplit R0.rCell R0.rOrd (xOf t)) b = rateOf
      (r0Split R0.rCell R0.rOrd (xOf t).1).1.1.1.keys.2.1
      (r0Split R0.rCell R0.rOrd (xOf t).1).1.1.1.perm
      (hidCellOf (r0Split R0.rCell R0.rOrd (xOf t).1) b) := fun b ↦ by
    rw [hE]
    unfold seedCellK' rateOf
    rw [f1 b]
    rfl
  obtain ⟨g4, g5, g6⟩ :=
    r0Split_keys_eq R0.rCell R0.rOrd (xOf t).1 R0.rCell_injective hcoll.1
  obtain ⟨-, -, hh⟩ := schemeSplit_transfer (xOf t).1.1 hgood.1
  have hks := schemeSplit_keys_snd (xOf t).1.1
  intro s hs j hj
  obtain ⟨i, hi⟩ := hQ t.1 s hs
  obtain ⟨mk, mk', mh⟩ := cells_mem_schemeData hi hj
  refine ⟨?_, ?_, ?_⟩
  · show (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1.1.keys.2.1 _ = t.1.keys.2.1 _
    rw [hk₂, f2 _ fun b hb ↦ (hsread i b).1 (by rw [hsc, hb, ← hsd₂]; exact mk),
      g4 _ fun a ha ↦ (hread i a).1 (by rw [ha, ← hsd]; exact mk)]
    exact congrFun (congrArg Prod.fst hks) _
  · show (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1.1.keys.2.2 _ = t.1.keys.2.2 _
    rw [hk'₂, f5 _ fun b hb ↦ (hsread i b).2 (by rw [hsc', hb, ← hsd₂]; exact mk'),
      g5 _ fun a ha ↦ (hread i a).2.1 (by rw [ha, ← hsd]; exact mk')]
    exact congrFun (congrArg Prod.snd hks) _
  · show (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1.1.keys.1 _ = t.1.keys.1 _
    rw [seedKSplit_h, g6 _ fun a ha ↦ (hread i a).2.2 (by rw [ha, ← hsd]; exact mh)]
    exact hh _ fun a ha ↦ hgood.2 i a (by rw [ha, ← hsd']; exact mh)

/-- **`hpath`**: on the good set, the table's honest paths' cells are the template's hidden cells
at the public data and the hidden values. -/
theorem r0E_hpath (hQ : HashesSlots Q) (ht : r0G Q G t) :
    pathH t.1 ⊆ hidH (pubR (r0E t).1) (fun q ↦ (r0E t).2.1 (.inl q)) ∧
      pathK t.1 ⊆ hidK (pubR (r0E t).1) (fun q ↦ (r0E t).2.1 (.inl q)) ∧
      pathK' t.1 ⊆ hidK' (pubR (r0E t).1) (fun q ↦ (r0E t).2.1 (.inl q)) :=
  hsub_keys t.1 (r0Phi t).1.1 ht.2.2.1 (r0G_param ht) (r0Phi_perm t) (r0G_start ht)
    (r0G_keys hQ ht) ht.2.2.2

theorem permR_r0E (t : HonestTable × RE) : permR (r0E t).1 = t.1.perm :=
  r0Phi_perm t

theorem parR_r0E (ht : r0G Q G t) : parR (r0E t).1 = t.1.param :=
  r0G_param ht

/-- **The never-revealed part is R0Stage's coordinates** (`rkOf`). -/
theorem rk_r0E (t : HonestTable × RE) : (r0E t).2.2.1 = rkOf (thetaOf t) := by
  show ((seedKSplit R0.rCell R0.rOrd (xOf t)).1.2,
      (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.1.1.masterSeed,
      (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.2.1,
      (seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.2.2.1) =
    ((r0Split R0.rCell R0.rOrd (thetaOf t)).2, (thetaOf t).1.1.masterSeed,
      (r0Split R0.rCell R0.rOrd (thetaOf t)).1.2.1, (r0Split R0.rCell R0.rOrd (thetaOf t)).1.2.2.1)
  rw [seedKSplit_coins, seedKSplit_seed, seedKSplit_masterSeed, r0Split_snd]
  rfl

/-- The seed slots of the never-revealed part are SeedStage's. -/
theorem sk_r0E (t : HonestTable × RE) :
    (r0E t).2.2.2.1 = (seedKSplit R0.rCell R0.rOrd (xOf t)).2 :=
  rfl

/-- **`hr0`**: on the good set, the table's randomizer-base and seed `k`-cells are the
never-revealed families at the coordinates. -/
theorem r0E_hr0 (ht : r0G Q G t) :
    r0H t.1 ⊆ r0Hk (permR (r0E t).1) (parR (r0E t).1) (r0E t).2.2.1 ∧
      r0K t.1 ⊆ r0Kk (parR (r0E t).1) (r0E t).2.2.1 ∧
      r0K' t.1 ⊆ r0K'k G (permR (r0E t).1) (parR (r0E t).1) (r0E t).2.2.1 ∧
      seedK t.1 ⊆ seedKk (parR (r0E t).1) (r0E t).2.2.1 := by
  rw [permR_r0E, parR_r0E ht, rk_r0E]
  exact r0Good_subsets G (mem_seedKGood.mp ht.1).1 ht.2.1

/-- **`hseed`**: on the good set, the table's seed paths' capacities and rates are SeedStage's
families at the coordinates. -/
theorem r0E_hseed (ht : r0G Q G t) :
    seedH t.1 ⊆ seedHSlots (permR (r0E t).1) (parR (r0E t).1) (r0E t).2.2.1 (r0E t).2.2.2.1 ∧
      seedK' t.1 ⊆ seedK'Slots G (permR (r0E t).1) (parR (r0E t).1) (r0E t).2.2.1
        (r0E t).2.2.2.1 := by
  rw [permR_r0E, parR_r0E ht, rk_r0E, sk_r0E]
  exact seedKGood_subsets G ht.1 ht.2.1

/-- **On the good set, the hidden values are the table's at the in-table outputs.** -/
theorem r0E_inl_eq (hQ : HashesSlots Q) (ht : r0G Q G t) {p : ValPos} (hp : InPos p) :
    (r0E t).2.1 (.inl p) = valuePos t.1 p :=
  xVal_eq_valuePos_keys t.1 (r0G_param ht) (r0Phi_perm t) (r0G_start ht) (r0G_keys hQ ht) hp

/-- **On the good set, the hidden values are the table's at the chain starts.** -/
theorem r0E_start_eq (ht : r0G Q G t) (l : Layer) (e : KeyIndex) (i : ChainIndex) :
    (r0E t).2.1 (.inl (.chain l e i ⟨0, by decide⟩)) =
      valuePos t.1 (.chain l e i ⟨0, by decide⟩) := by
  show xVal (r0Phi t).1.1.2 (r0Phi t).1.1.1.1 (r0Phi t).1.1.1.2 (.chain l e i ⟨0, by decide⟩) = _
  rw [xVal, ite_eq_right fun h ↦ Nat.not_succ_le_zero 0 h.1]
  exact r0G_start ht l e i

/-- **On the good set, the hidden values are the table's at the first labels' randomizer
bases.** -/
theorem r0E_inr_eq (ht : r0G Q G t) (a : RLabel)
    (ha : (Sum.inr a : HPos) ∉ r0Bk (permR (r0E t).1) (parR (r0E t).1) (r0E t).2.2.1) :
    (r0E t).2.1 (.inr a) = valueAt t.1 (.inr a) := by
  rw [permR_r0E, parR_r0E ht, rk_r0E] at ha
  have h1 : (r0E t).2.1 (.inr a) = r0Coord (r0Split R0.rCell R0.rOrd (thetaOf t)).1 a := by
    show (r0SlotEquiv ((seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.2.2.2 a)).1 = _
    rw [r0SlotEquiv_fst, seedKSplit_coins]
    rfl
  exact h1.trans (valueAt_inr_eq_r0Coord (mem_seedKGood.mp ht.1).1 a ha).symm

end good

/-! ## `hgame`: the game at the reparametrized datum -/

section game

open LeanXmss.RandomPermutationModel Common Common.SufCma HashSig.OverPermutation

/-- Reparam's values at public keys agreeing with the table's on its paths are the table's at the
in-table positions and the chain starts. -/
theorem xVal_eq_valuePos_keys' (L : HonestTable) {h : Z → X} {u : ValPos → Digest} {w : XW}
    (hP : w.1 = L.param) (hπ : w.2.1 = L.perm)
    (hu : ∀ l e i, u (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      KeysAt (pubOf L) (xPub w h) s (valuePos L) j)
    (q : ValPos) (hq : InPos q ∨ ∃ l e i, q = .chain l e i ⟨0, by decide⟩) :
    xVal w h u q = valuePos L q := by
  rcases hq with hp | ⟨l, e, i, rfl⟩
  · exact xVal_eq_valuePos_keys L hP hπ hu hav hp
  · rw [xVal, ite_eq_right fun hp ↦ Nat.not_succ_le_zero 0 hp.1, hu]
    rfl

/-- **The slot ports agree at the reparametrized datum**, for public keys agreeing with the
table's on its paths (GameCongr's `slotPortsAgree_pubOf` with `w` other than `wOf L`). -/
theorem slotPortsAgree_keys (L : HonestTable) {h : Z → X} {u : ValPos → Digest} {w : XW}
    (hθ : XGood ((h, u), w)) (hP : w.1 = L.param) (hπ : w.2.1 = L.perm)
    (hu : ∀ l e i, u (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      KeysAt (pubOf L) (xPub w h) s (valuePos L) j)
    {l : Layer} {e : KeyIndex} {x : Encoding} {s : Slot} (he : e.val < keyCount l)
    (hs : s ∈ layerSlots l e x) :
    SlotPortsAgree (pubOf L) (xPub w (fwd xmssFix xO ((h, u), w)).1.1) (valueAt L) s := by
  intro j hj
  have hsIn : InTable s := inTable_of_mem_layerSlots he hs
  have hFv : ∀ q ∈ slotNeed s,
      extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L)) q = valuePos L q :=
    fun q hq ↦ extendVals_restrictTo (inl_mem_inlSet.mpr hq) (valueAt L)
  have hFx : ∀ q ∈ slotNeed s,
      extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L)) q = xVal w h u q :=
    fun q hq ↦ (hFv q hq).trans (xVal_eq_valuePos_keys' L hP hπ hu hav q ((mem_slotNeed hq).elim
      (inPos_or_start hsIn) fun hout ↦ Or.inl (hout ▸ inPos_slotOutPos hsIn))).symm
  have hinv : ∀ q, IsInput q s →
      extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L)) q = valuePos L q :=
    fun q hq ↦ hFv q (isInput_mem_slotNeed hq)
  have hinx : ∀ q, IsInput q s →
      extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L)) q = xVal w h u q :=
    fun q hq ↦ hFx q (isInput_mem_slotNeed hq)
  obtain ⟨c1, c2, c3⟩ := cells_transfer_keys L hθ hP hπ hu hav hsIn hj
  obtain ⟨k1, k2, k3⟩ := hav s hsIn j hj
  refine ⟨?_, ?_, ?_⟩
  · show (srcCellK (pubOf L) s (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j,
        L.keys.2.1 (srcCellK (pubOf L) s
          (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j)) =
      (srcCellK (xPub w (fwd xmssFix xO ((h, u), w)).1.1) s
          (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j,
        w.2.2.1 (srcCellK (xPub w (fwd xmssFix xO ((h, u), w)).1.1) s
          (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j))
    rw [cellK_congr (pubOf L) hinv, cellK_congr _ hinx, c1]
    exact Prod.ext rfl k1.symm
  · show (srcCellK' (pubOf L) s (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j,
        L.keys.2.2 (srcCellK' (pubOf L) s
          (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j)) =
      (srcCellK' (xPub w (fwd xmssFix xO ((h, u), w)).1.1) s
          (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j,
        w.2.2.2 (srcCellK' (xPub w (fwd xmssFix xO ((h, u), w)).1.1) s
          (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j))
    rw [cellK'_congr (pubOf L) hinv, cellK'_congr _ hinx, c2]
    exact Prod.ext rfl k2.symm
  · have hj' : j < nBlocks (xPub w h) (outSlot (slotOutPos s)) := by
      rw [outSlot_slotOutPos hsIn, congrFun (nBlocks_eq_of_param (pub := xPub w h)
        (pub' := pubOf L) hP) s]
      exact hj
    obtain ⟨-, -, e3⟩ := rounds_fwd hθ (mem_xI.mpr (inPos_slotOutPos hsIn)) hj'
    have e4 := roundH_table w h u (inPos_slotOutPos hsIn) hj'
    rw [outSlot_slotOutPos hsIn] at e3 e4
    have hc : (roundH (xPub w h) s (xVal w h u) j).1 = srcCellH (pubOf L) s (valuePos L) j := by
      rw [← e3]
      exact c3
    have hh : h (srcCellH (pubOf L) s (valuePos L) j) =
        L.keys.1 (srcCellH (pubOf L) s (valuePos L) j) := k3
    calc roundH (pubOf L) s (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j
        = (srcCellH (pubOf L) s (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j,
            L.keys.1 (srcCellH (pubOf L) s
              (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j)) :=
          Prod.ext rfl (roundH_snd L hs j)
      _ = (srcCellH (pubOf L) s (valuePos L) j,
            L.keys.1 (srcCellH (pubOf L) s (valuePos L) j)) := by
          rw [cellH_congr (pubOf L) hinv]
      _ = (srcCellH (pubOf L) s (valuePos L) j, h (srcCellH (pubOf L) s (valuePos L) j)) := by
          rw [hh]
      _ = roundH (xPub w h) s (xVal w h u) j := by
          rw [e4, hc]
      _ = roundH (xPub w (fwd xmssFix xO ((h, u), w)).1.1) s (xVal w h u) j := e3.symm
      _ = roundH (xPub w (fwd xmssFix xO ((h, u), w)).1.1) s
            (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j :=
          roundH_congr_of_need _ (fun q hq ↦ (hFx q hq).symm) (slotOutPos_mem hs) j

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **The game at the reparametrized datum**, for public keys agreeing with the table's on its
paths (GameCongr's `realizeT_gameT_pubOf` with `θ.2` other than `wOf L`). -/
theorem realizeT_gameT_keys (A : Adversary (X × Z)) (L : HonestTable) (θ : RTab) (hθ : XGood θ)
    (hP : θ.2.1 = L.param) (hπ : θ.2.2.1 = L.perm)
    (hu : ∀ l e i, θ.1.2 (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      KeysAt (pubOf L) (xPub θ.2 θ.1.1) s (valuePos L) j)
    (v : HPos → Digest) (hinl : ∀ q, v (.inl q) = xVal θ.2 θ.1.1 θ.1.2 q)
    (hinr : ∀ lab, v (.inr lab) = valueAt L (.inr lab)) :
    realizeT (valueAt L) (gameT M upd (pubOf L) A) =
      realizeT v (gameT M upd (xPub θ.2 (fwd xmssFix xO θ).1.1) A) := by
  obtain ⟨⟨h, u⟩, w⟩ := θ
  refine realizeT_gameT_congr upd A hP.symm hπ.symm ?_ (fun lab ↦ (hinr lab).symm) ?_
    fun l e x s he hs ↦ slotPortsAgree_keys L hθ hP hπ hu hav he hs
  · rw [hinl]
    exact (xVal_eq_valuePos_keys' L hP hπ hu hav _ (Or.inl inPos_rootPos)).symm
  · intro l e x he q hq
    rw [hinl]
    exact (xVal_eq_valuePos_keys' L hP hπ hu hav q (layerNeed_good he hq)).symm

variable {ι : Type} {β : ι → Type}
  {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)} {G : ℕ}

/-- **`hgame`** (MassesR0's, for `r0E`): on the good set, the game at the table is the template
game at the public datum, realized at the hidden values of `r0E` on the positions and the table's
on the labels, which agree with `r0E`'s off the non-first labels. -/
theorem hgame_r0E (A : Adversary (X × Z)) (hQ : HashesSlots Q) {t : HonestTable × RE}
    (ht : r0G Q G t) :
    ∃ v : HPos → Digest,
      Agree (Finset.univ \ r0Bk (permR (r0E t).1) (parR (r0E t).1) (r0E t).2.2.1) v (r0E t).2.1 ∧
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) =
        realizeT v (gameT M upd (pubR (r0E t).1) A) :=
  ⟨Sum.elim (fun q ↦ (r0E t).2.1 (.inl q)) fun lab ↦ valueAt t.1 (.inr lab),
    agree_univ_sdiff fun s hs ↦ by
      rcases s with q | lab
      · rfl
      · exact (r0E_inr_eq ht lab hs).symm,
    realizeT_gameT_keys upd A t.1 (r0Phi t).1.1 ht.2.2.1 (r0G_param ht) (r0Phi_perm t)
      (r0G_start ht) (r0G_keys hQ ht) _ (fun _ ↦ rfl) fun _ ↦ rfl⟩

end game

/-! ## The bad fraction -/

section bad

variable {ι : Type} {β : ι → Type}

/-- A union bound for a complement covered by four events. -/
theorem card_filter_not_le_four {Y : Type*} [Fintype Y] (GP P₁ P₂ P₃ P₄ : Y → Prop)
    [DecidablePred GP] [DecidablePred P₁] [DecidablePred P₂] [DecidablePred P₃]
    [DecidablePred P₄] (h : ∀ y, ¬GP y → P₁ y ∨ P₂ y ∨ P₃ y ∨ P₄ y) :
    (Finset.univ.filter fun y ↦ ¬GP y).card ≤
      (Finset.univ.filter P₁).card + (Finset.univ.filter P₂).card +
        (Finset.univ.filter P₃).card + (Finset.univ.filter P₄).card := by
  classical
  refine (Finset.card_le_card fun y hy ↦ ?_).trans
    ((Finset.card_union_le _ _).trans (add_le_add ((Finset.card_union_le _ _).trans
      (add_le_add (Finset.card_union_le _ _) le_rfl)) le_rfl))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy ⊢
  rcases h y hy with h1 | h2 | h3 | h4
  · exact Or.inl (Or.inl (Or.inl h1))
  · exact Or.inl (Or.inl (Or.inr h2))
  · exact Or.inl (Or.inr h3)
  · exact Or.inr h4

/-- A count bound by four parts, as fractions. -/
theorem inv_mul_le_four {N g a b c d : ℕ} (h : g ≤ a + b + c + d) :
    (N : ℝ≥0∞)⁻¹ * g ≤ (N : ℝ≥0∞)⁻¹ * a + (N : ℝ≥0∞)⁻¹ * b + (N : ℝ≥0∞)⁻¹ * c +
      (N : ℝ≥0∞)⁻¹ * d := by
  rw [← mul_add, ← mul_add, ← mul_add]
  gcongr
  exact_mod_cast h

/-- The padded tables as the permutation and the rest. -/
def permSplitR : HonestTable × RE ≃ Equiv.Perm (X × Z) × ((SpongeKeys X Z × MasterSeed) × RE) where
  toFun t := (t.1.perm, ((t.1.keys, t.1.masterSeed), t.2))
  invFun x := (⟨x.2.1.1, x.1, x.2.1.2⟩, x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Classical in
/-- **The source-goodness part**: the tables whose coordinates are Reparam-good but not
source-good are at most SrcBad's fraction (the coordinates of Reparam-good tables are distinct). -/
theorem frac_srcBad_r0E_le :
    (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦
      XGood (r0Phi t).1.1 ∧ ¬SrcGood (pubX ((fwd xmssFix xO (r0Phi t).1.1).1, (r0Phi t).1.2))
        (fwd xmssFix xO (r0Phi t).1.1).2).card ≤
      (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ ¬SrcGood (pubX y.1) y.2).card := by
  have hC := card_filter_le_of_injOn
    (fun t ↦ ((((fwd xmssFix xO (r0Phi t).1.1).1, (r0Phi t).1.2), (fwd xmssFix xO (r0Phi t).1.1).2),
      (r0Phi t).2) :
        HonestTable × RE → (PX × (ValPos → Digest)) × (CoinSlots R0.RLabel × SeedKS))
    (fun t ↦ XGood (r0Phi t).1.1 ∧ ¬SrcGood (pubX ((fwd xmssFix xO (r0Phi t).1.1).1,
      (r0Phi t).1.2)) (fwd xmssFix xO (r0Phi t).1.1).2)
    (fun z : (PX × (ValPos → Digest)) × (CoinSlots R0.RLabel × SeedKS) ↦
      ¬SrcGood (pubX z.1.1) z.1.2)
    (fun _ h ↦ h.2) fun t₁ t₂ h₁ h₂ e ↦ by
      have hf : fwd xmssFix xO (r0Phi t₁).1.1 = fwd xmssFix xO (r0Phi t₂).1.1 :=
        Prod.ext (congrArg (fun z ↦ z.1.1.1) e :) (congrArg (fun z ↦ z.1.2) e :)
      have hθ := injOn_fwd xO_consistent (good_of_xGood h₁.1) (good_of_xGood h₂.1) hf
      exact r0Phi.injective (Prod.ext (Prod.ext hθ (congrArg (fun z ↦ z.1.1.2) e :))
        (congrArg (fun z ↦ z.2) e :))
  have hP := card_filter_pad (W := CoinSlots R0.RLabel × SeedKS)
    (fun y : PX × (ValPos → Digest) ↦ ¬SrcGood (pubX y.1) y.2)
  have hN : Fintype.card (HonestTable × RE) =
      Fintype.card (PX × (ValPos → Digest)) * Fintype.card (CoinSlots R0.RLabel × SeedKS) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr (r0Phi.trans (pxEquiv.symm.prodCongr (Equiv.refl _)))
  calc (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦
        XGood (r0Phi t).1.1 ∧ ¬SrcGood (pubX ((fwd xmssFix xO (r0Phi t).1.1).1, (r0Phi t).1.2))
          (fwd xmssFix xO (r0Phi t).1.1).2).card
      ≤ (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun z : (PX × (ValPos → Digest)) × (CoinSlots R0.RLabel × SeedKS) ↦
            ¬SrcGood (pubX z.1.1) z.1.2).card := by
        gcongr
    _ = (((Fintype.card (PX × (ValPos → Digest)) * Fintype.card (CoinSlots R0.RLabel × SeedKS) :
          ℕ) : ℝ≥0∞))⁻¹ * (((Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
            ¬SrcGood (pubX y.1) y.2).card * Fintype.card (CoinSlots R0.RLabel × SeedKS) : ℕ) :
              ℝ≥0∞) := by
        rw [hP, hN, Nat.cast_mul, Nat.cast_mul]
    _ = _ := natCast_mul_inv_mul_cancel _ _ _ Fintype.card_ne_zero

open scoped Classical in
/-- **The bad fraction of the good set**: SeedStage's (`seedKGood`, with R0Stage's and
SchemeSplit's inside), the bad permutations, Reparam's, and the source-goodness fraction. -/
theorem r0G_frac_le_parts
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (G : ℕ) :
    (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬r0G Q G t).card ≤
      (Fintype.card (CTab R0.RLabel × SeedKS) : ℝ≥0∞)⁻¹ *
          ((Fintype.card (CTab R0.RLabel × SeedKS) - (seedKGood R0.rCell R0.rOrd Q).card : ℕ) :
            ℝ≥0∞) +
        ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        (Fintype.card RTab : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun θ : RTab ↦ ¬XGood θ).card +
        (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ ¬SrcGood (pubX y.1) y.2).card := by
  have h4 := card_filter_not_le_four (r0G Q G)
    (fun t ↦ (splitR0 t).1 ∉ seedKGood R0.rCell R0.rOrd Q)
    (fun t ↦ ¬PermGood (permSplitR t).1 G)
    (fun t ↦ ¬XGood ((r0Phi.trans (Equiv.prodAssoc RTab Rest (CoinSlots R0.RLabel × SeedKS))) t).1)
    (fun t ↦ XGood (r0Phi t).1.1 ∧ ¬SrcGood (pubX ((fwd xmssFix xO (r0Phi t).1.1).1,
      (r0Phi t).1.2)) (fwd xmssFix xO (r0Phi t).1.1).2) fun t ht ↦ by
      by_cases h1 : xOf t ∈ seedKGood R0.rCell R0.rOrd Q
      · by_cases h2 : PermGood t.1.perm G
        · by_cases h3 : XGood (r0Phi t).1.1
          · exact Or.inr (Or.inr (Or.inr ⟨h3, fun h4 ↦ ht ⟨h1, h2, h3, h4⟩⟩))
          · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inr (Or.inl h2)
      · exact Or.inl h1
  have e1 := inv_card_mul_card_filter_comp_fst splitR0
    (fun x ↦ x ∉ seedKGood R0.rCell R0.rOrd Q)
  have hc : (Finset.univ.filter fun x ↦ x ∉ seedKGood R0.rCell R0.rOrd Q).card =
      Fintype.card (CTab R0.RLabel × SeedKS) - (seedKGood R0.rCell R0.rOrd Q).card := by
    convert card_filter_notMem_eq (seedKGood R0.rCell R0.rOrd Q)
  rw [hc, ENNReal.div_eq_inv_mul] at e1
  have e2 := inv_card_mul_card_filter_comp_fst permSplitR (fun π ↦ ¬PermGood π G)
  have e3 := inv_card_mul_card_filter_comp_fst
    (r0Phi.trans (Equiv.prodAssoc RTab Rest (CoinSlots R0.RLabel × SeedKS))) (fun θ ↦ ¬XGood θ)
  rw [ENNReal.div_eq_inv_mul] at e3
  refine (inv_mul_le_four h4).trans ?_
  rw [e1, e2, e3]
  exact add_le_add le_rfl frac_srcBad_r0E_le

end bad

/-! ## At Keccak's sizes, with the tree computations -/

section keccak

theorem card_tIdx : Fintype.card TIdx = 2 ^ 17 := by
  simp only [TIdx, Fintype.card_prod, Fintype.card_fin]
  norm_num [layerCount]

theorem card_optCs : Fintype.card (Option CsIdx) = 1 + 2 * 2 ^ 32 * 29 := by
  simp only [Fintype.card_option, CsIdx, Fintype.card_prod, Fintype.card_fin]
  norm_num [layerCount, lifetime, chainCount, layerHeight]

theorem natCast_div_le_ofReal {a b : ℕ} (hb : 0 < b) {r : ℝ} (h : (a : ℝ) / b ≤ r) :
    (a : ℝ≥0∞) / b ≤ ENNReal.ofReal r := by
  rw [R0.natCast_div_eq_ofReal a b hb]
  exact ENNReal.ofReal_le_ofReal h

theorem add_le_ofReal {x y : ℝ≥0∞} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hx : x ≤ ENNReal.ofReal r) (hy : y ≤ ENNReal.ofReal s) : x + y ≤ ENNReal.ofReal (r + s) :=
  (add_le_add hx hy).trans_eq (ENNReal.ofReal_add hr hs).symm

theorem natCast_mul_le_ofReal (n : ℕ) {x : ℝ≥0∞} {r : ℝ} (hx : x ≤ ENNReal.ofReal r) :
    (n : ℝ≥0∞) * x ≤ ENNReal.ofReal (n * r) := by
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  gcongr

theorem pow256_eq : (2 : ℝ≥0∞) ^ 256 = ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
  norm_cast

theorem posReads_div_le : (posReads : ℝ≥0∞) / 2 ^ 256 ≤ ENNReal.ofReal (posReads / 2 ^ 256) := by
  rw [pow256_eq]
  exact natCast_div_le_ofReal (by positivity) (by norm_num [posReads])

/-- The seed paths' `k`-cell read term of a computation (`(qs₀ + qs₁) / 2^256`). -/
theorem seedReadTerm_le :
    ((posReads + posReads : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ENNReal.ofReal (2 * posReads / 2 ^ 256) := by
  rw [pow256_eq]
  exact natCast_div_le_ofReal (by positivity) (by norm_num [posReads])

set_option exponentiation.threshold 4096 in
/-- The randomizer-base read term of a computation (`|J| 19 q / |Z|`). -/
theorem r0ReadTerm_le :
    (Fintype.card R0.RLabel : ℝ≥0∞) * ((18 : ℕ) + 1) * posReads / Fintype.card Z ≤
      ENNReal.ofReal ((2 ^ 288 + 2 ^ 160) * 19 * posReads / 2 ^ 512) := by
  have h : (Fintype.card R0.RLabel : ℝ≥0∞) * ((18 : ℕ) + 1) * posReads =
      (((2 ^ 288 + 2 ^ 160) * 19 * posReads : ℕ) : ℝ≥0∞) := by
    rw [R0.card_rLabel]
    push_cast
    ring
  rw [h, R0.card_cap]
  exact natCast_div_le_ofReal (by positivity) (by norm_num [posReads])

set_option exponentiation.threshold 4096 in
/-- SchemeSplit's read term of a computation (`19 q / |Z|`). -/
theorem schemeReadTerm_le :
    (((18 : ℕ) : ℝ≥0∞) + 1) * posReads / Fintype.card Z ≤
      ENNReal.ofReal (19 * posReads / 2 ^ 512) := by
  have h : (((18 : ℕ) : ℝ≥0∞) + 1) * posReads = ((19 * posReads : ℕ) : ℝ≥0∞) := by
    push_cast
    ring
  rw [h, R0.card_cap]
  exact natCast_div_le_ofReal (by positivity) (by norm_num [posReads])

set_option exponentiation.threshold 4096 in
/-- SchemeSplit's chain-start read term of a computation (`|CsIdx| 19 q / |Z|`). -/
theorem schemeCsReadTerm_le :
    (Fintype.card (Option CsIdx) : ℝ≥0∞) * ((18 : ℕ) + 1) * posReads / Fintype.card Z ≤
      ENNReal.ofReal ((1 + 2 * 2 ^ 32 * 29) * 19 * posReads / 2 ^ 512) := by
  have h : (Fintype.card (Option CsIdx) : ℝ≥0∞) * ((18 : ℕ) + 1) * posReads =
      (((1 + 2 * 2 ^ 32 * 29) * 19 * posReads : ℕ) : ℝ≥0∞) := by
    rw [card_optCs]
    push_cast
    ring
  rw [h, R0.card_cap]
  exact natCast_div_le_ofReal (by positivity) (by norm_num [posReads])

set_option exponentiation.threshold 4096 in
/-- SchemeSplit's static collision term (`|A|² 19 / |Z|`). -/
theorem schemeCollTerm_le :
    ((Fintype.card (Option (Option CsIdx)) * Fintype.card (Option (Option CsIdx)) * (18 + 1) : ℕ) :
      ℝ≥0∞) / Fintype.card Z ≤ ENNReal.ofReal (1 / 2 ^ 430) := by
  rw [R0.card_hidIdx, R0.card_cap]
  exact natCast_div_le_ofReal (by positivity) (by push_cast; norm_num)

set_option exponentiation.threshold 4096 in
/-- Reparam's one-block output collision term (`|xI₁|² 19 / |Z|`). -/
theorem xI₁Term_le :
    ((xI₁.card * xI₁.card * (18 + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z ≤
      ENNReal.ofReal (1 / 2 ^ 420) := by
  have h1 : xI₁.card ≤ 498 * 2 ^ 32 :=
    (Finset.card_le_card fun _ hp ↦ mem_xI.mpr (mem_xI₁.mp hp).1).trans card_xI_le
  have h2 : xI₁.card * xI₁.card * (18 + 1) ≤ 498 * 2 ^ 32 * (498 * 2 ^ 32) * 19 :=
    Nat.mul_le_mul (Nat.mul_le_mul h1 h1) le_rfl
  refine (ENNReal.div_le_div_right (Nat.cast_le.mpr h2) _).trans ?_
  rw [R0.card_cap]
  exact natCast_div_le_ofReal (by positivity) (by push_cast; norm_num)

theorem sum_tIdx_const (c : ℝ≥0∞) : ∑ _i : TIdx, c = ((2 ^ 17 : ℕ) : ℝ≥0∞) * c := by
  rw [Finset.sum_const, Finset.card_univ, card_tIdx, nsmul_eq_mul]

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The bad fraction at Keccak's sizes** (tree computations, `G = 18`): at most `2^-174`. The
randomizer-base read term `2^17 · posReads · 19 |J| / |Z| ≈ 2^-174.7` dominates; R0Stage's static
collisions are `2^-181`, the rest is below `2^-200`. -/
theorem r0G_frac_le_keccak :
    (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ ¬r0G treeQ 18 t).card ≤ ENNReal.ofReal (1 / 2 ^ 174) := by
  have hq : ∀ (i : TIdx) (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (treeQ i P Cs)).2.length ≤ posReads :=
    length_honestEval_treeQ
  have hS := schemeGood_frac_le 18 treeQ (fun _ ↦ posReads) (fun _ ↦ posReads)
    (fun _ ↦ posReads) hq
    (fun i t π P Cs ↦ (Finset.card_filter_le _ _).trans ((card_kCells_le _).trans (hq i t π P Cs)))
    (fun i t π P Cs ↦ (Finset.card_filter_le _ _).trans ((card_kCells_le _).trans (hq i t π P Cs)))
  have hR := R0.r0Good_frac_le_rLabel 18 treeQ (fun _ ↦ posReads) (fun _ ↦ posReads) hq
    (fun i t π P Cs ↦ (Finset.card_filter_le _ _).trans ((card_kCells_le _).trans (hq i t π P Cs)))
  have hSK := seedKGood_frac_le_keccak treeQ (fun _ ↦ posReads) (fun _ ↦ posReads)
    (fun _ ↦ posReads) hq
    (fun i t π P Cs ↦ (Finset.card_filter_le _ _).trans ((card_kCells_le _).trans (hq i t π P Cs)))
    (fun i t π P Cs ↦ (Finset.card_filter_le _ _).trans ((card_kCells_le _).trans (hq i t π P Cs)))
  have hπ := permTerm_le_keccak
  have hsumS := (sum_tIdx_const _).trans_le (natCast_mul_le_ofReal (2 ^ 17)
    (add_le_ofReal (by positivity) (by positivity)
      (add_le_ofReal (by positivity) (by positivity) posReads_div_le schemeReadTerm_le)
      (add_le_ofReal (by positivity) (by positivity) posReads_div_le schemeCsReadTerm_le)))
  have hsumR := (sum_tIdx_const _).trans_le (natCast_mul_le_ofReal (2 ^ 17)
    (add_le_ofReal (by positivity) (by positivity) posReads_div_le r0ReadTerm_le))
  have hsumSK := (sum_tIdx_const _).trans_le (natCast_mul_le_ofReal (2 ^ 17)
    (add_le_ofReal (by positivity) (by positivity) seedReadTerm_le
      (le_refl (ENNReal.ofReal ((posReads : ℝ) / 2 ^ 469)))))
  have hSb := hS.trans (add_le_ofReal (by positivity) (by positivity)
    (add_le_ofReal (by positivity) (by positivity) hπ schemeCollTerm_le) hsumS)
  have hRb := hR.trans (add_le_ofReal (by positivity) (by positivity)
    (add_le_ofReal (by positivity) (by positivity)
      (add_le_ofReal (by positivity) (by positivity) hSb hπ) R0.r0CollTerms_le_keccak) hsumR)
  have hSKb := hSK.trans (add_le_ofReal (by positivity) (by positivity)
    (add_le_ofReal (by positivity) (by positivity)
      (add_le_ofReal (by positivity) (by positivity) hRb hπ) le_rfl) hsumSK)
  have hXb := (xGood_bad_frac_le 18).trans (add_le_ofReal (by positivity) (by positivity)
    (add_le_ofReal (by positivity) (by positivity) hπ xI₁Term_le) pathBad_frac_le_keccak)
  have hA : (Fintype.card (CTab R0.RLabel × SeedKS) : ℝ≥0∞)⁻¹ *
      ((Fintype.card (CTab R0.RLabel × SeedKS) - (seedKGood R0.rCell R0.rOrd treeQ).card : ℕ) :
        ℝ≥0∞) ≤ ENNReal.ofReal _ := hSKb
  have hB : ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π 18).card : ℝ≥0∞) /
      Fintype.card (Equiv.Perm (X × Z)) ≤ ENNReal.ofReal _ := hπ
  have hC : (Fintype.card RTab : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun θ : RTab ↦ ¬XGood θ).card ≤
      ENNReal.ofReal _ := hXb
  have hD : (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
      (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ ¬SrcGood (pubX y.1) y.2).card ≤
      ENNReal.ofReal _ := srcBad_frac_le_keccak
  have hE := add_le_ofReal (by positivity) (by positivity)
    (add_le_ofReal (by positivity) (by positivity)
      (add_le_ofReal (by positivity) (by positivity) hA hB) hC) hD
  refine (r0G_frac_le_parts treeQ 18).trans (hE.trans (ENNReal.ofReal_le_ofReal ?_))
  norm_num [posReads]

end keccak

/-! ## The bounds -/

section bounds

open LeanXmss.RandomPermutationModel Common Common.SufCma HashSig.OverPermutation

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

/-- **`hybSponge` for leanXMSS's full table, discharged but for the constants**: MassesR0's
`uavg_spongeMass_le_xmssR0` at `r0E`, `r0G treeQ 18`, with SeedStage's seed families
(`εA = seedEps 18`) and the bad fraction `2^-174`. -/
theorem uavg_spongeMass_le_r0E (A : Adversary (X × Z)) {q : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ) :
    uavg (fun L : HonestTable ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (spongeMass (pathH L ∪ seedH L ∪ r0H L) (pathK L ∪ seedK L ∪ r0K L)
        (pathK' L ∪ seedK' L ∪ r0K' L)) (realizeT (valueAt L) (gameT M upd (pubOf L) A)) ρ) ≤
      ((6 * q : ℕ) : ℝ≥0∞) * ((2 ^ 128 : ℝ≥0∞)⁻¹ + (seedEps 18 + r0Eps 18) +
          ((2 * lifetime : ℕ) : ℝ≥0∞) * ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)) +
        ((6 * q : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 2 ^ 174) :=
  (uavg_spongeMass_le_xmssR0 upd A hperm hsign m₀ ρ hρ hρ1 hs r0E (r0G treeQ 18)
    (r0E_injOn treeQ 18) card_r0E_le pubR parR permR 18
    (fun _ ht ↦ hgame_r0E upd A hashesSlots_treeQ ht) (fun _ ht ↦ r0E_hpath hashesSlots_treeQ ht)
    (fun _ ht ↦ r0E_hr0 ht) (fun p k ↦ seedHSlots (permR p) (parR p) k.1 k.2.1)
    (fun p k ↦ seedK'Slots 18 (permR p) (parR p) k.1 k.2.1) (seedEps 18)
    (fun _ ht ↦ r0E_hseed ht) (fun p z ↦ sum_indicator_seedHSlots_le 18 (permR p) (parR p) z)
    (fun p y ↦ sum_indicator_seedK'Slots_le 18 (permR p) (parR p) y)).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left r0G_frac_le_keccak zero_le))

/-- **`hybRead` for leanXMSS's full table, discharged but for the constants**: MassesR0's
`uavg_readMass_le_xmssR0` at `r0E`, `r0G treeQ 18`, with SeedStage's seed families and the bad
fraction `2^-174`. -/
theorem uavg_readMass_le_r0E (A : Adversary (X × Z)) {q : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)) ↦
      p.2.2.2.1) {∅} ρ) :
    uavg (fun L : HonestTable ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (readMass (pathH L ∪ seedH L ∪ r0H L) (pathK L ∪ seedK L ∪ r0K L)
        (pathK' L ∪ seedK' L ∪ r0K' L)) (realizeT (valueAt L) (gameT M upd (pubOf L) A)) ρ) ≤
      ((3 * (signBlocks * lifetime + verifyBlocks) + 2 * progCap : ℕ) : ℝ≥0∞) *
          ((2 ^ 128 : ℝ≥0∞)⁻¹ + (seedEps 18 + r0Eps 18) +
            ((2 * lifetime : ℕ) : ℝ≥0∞) * ((Fintype.card RLabel : ℝ≥0∞) / Fintype.card Z)) +
        ((3 * (signBlocks * lifetime + verifyBlocks) + 2 * progCap : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (1 / 2 ^ 174) :=
  (uavg_readMass_le_xmssR0 upd A hperm hsign m₀ ρ hρ hρ1 hs r0E (r0G treeQ 18)
    (r0E_injOn treeQ 18) card_r0E_le pubR parR permR 18
    (fun _ ht ↦ hgame_r0E upd A hashesSlots_treeQ ht) (fun _ ht ↦ r0E_hpath hashesSlots_treeQ ht)
    (fun _ ht ↦ r0E_hr0 ht) (fun p k ↦ seedHSlots (permR p) (parR p) k.1 k.2.1)
    (fun p k ↦ seedK'Slots 18 (permR p) (parR p) k.1 k.2.1) (seedEps 18)
    (fun _ ht ↦ r0E_hseed ht) (fun p z ↦ sum_indicator_seedHSlots_le 18 (permR p) (parR p) z)
    (fun p y ↦ sum_indicator_seedK'Slots_le 18 (permR p) (parR p) y)).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left r0G_frac_le_keccak zero_le))

end bounds

end Quantum.Xmss.Assembly

end
