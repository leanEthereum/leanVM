module

public import Quantum.Sphincs.Assembly.ReparamFull

@[expose] public section

/-!
# The charged coordinates at the reparametrized data, and the first-meeting record mass

MassSources pays the mismatch between the game at a table and the game at the reparametrized
data (`hgame_fullE`, agreement off `chgB t`) with a record mass. Here both are put in the shape
the averaging needs (`Quantum.Sphincs.Assembly.ChgRevBound`).

* **The first-meeting mismatch lemma** (`totalWeight_portMass_le_mismatch_first`): Mismatch's
  `totalWeight_le_mismatch` with the record mass replaced by the mass of the record calls meeting
  `B` from a label avoiding `B` (`revFirst`, Mismatch's `revSet`), which is what its proof gives.
  A record of a coordinate already in the label is never charged.
* **The charged coordinates read off the coordinates** `x = (p, (v, k))` (`chgBK x`): a message
  `M` is charged (`MsgChg`) if its randomizer label is non-first at the randomizer stage's
  capacities (`RChg`, `rCapK`: the never-revealed coins of `k`), or one of its digest labels
  `(M, i)` is charged at the capacities of the public keys at the `H_msg` blocks under the hidden
  root and randomizers (`DChg`, `capD`): a label of smaller rank at the same capacity, or a
  randomizer-stage or `SK.seed`-keyed capacity (`ExtK`). Both `.rnd M` and `.dig M i` of a
  charged message are charged, so a digest record of `M` (after its randomizer's record) is never
  a first meeting.
* `chgB_subset_chgBK`: on `FullD t`, `chgB t ⊆ chgBK (fullE t)` (`rCellH_eq_rCapK`: the table's
  randomizer capacities are `rCapK`; `dChg_of_mem_dBX`: DigestStage's charged labels are `DChg`).
-/

open Matrix IPFunctor
open scoped ENNReal ComplexOrder Kronecker

universe u v w

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer MasterSeed)
open Quantum.Xmss (X Z out256 trunc128)
open Quantum.Xmss.Hybrid (IsFirst capOf rateOf Agree CoinSlots diagMass revSet badW portMass
  KeepsLab)
open Quantum.Xmss.Assembly (XW recHwSpec runtimeR realizeT tmplSpec Disc)
open Quantum.Sphincs.Hybrid (DLab dLabCell dLabOrd rCell rOrd skCell SkIdx rB rCellH rCellK
  rCellK' pCellH pB Secret SeedKS)

namespace Quantum.Sphincs.Assembly

/-! ## The first-meeting mismatch lemma -/

section mismatch

variable {L : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- **The first-meeting record mass**: the trace of the inputs, labelled off `B`, of the record
calls of `x` whose recorded set meets `B`. -/
noncomputable def revFirst (m₀ : Finset HPos × Selections) (I : L.Interp) (B : Finset HPos)
    {A : QReg} (x : QuantumComp L (recHwSpec X Z HPos Selections) Ω A)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset HPos × Selections)))
      (A × QReg.of (HwReg X Z (Finset HPos × Selections))) ℂ) : ℝ≥0∞ :=
  (runtimeR m₀).totalWeight I (fun i ↦ diagMass (revSet X Z Selections B i)) x ρ

/-- **The mismatch lemma with the first-meeting record mass** (Mismatch's
`totalWeight_le_mismatch`, without its last weakening). -/
theorem totalWeight_le_mismatch_first (m₀ : Finset HPos × Selections) (I : L.Interp) {A : QReg}
    (y : QuantumComp L (tmplSpec X Z HPos XD Selections goodAll) Ω A) (hdisc : Disc y ∅)
    (hy : KeepsLab y)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset HPos × Selections)))
      (A × QReg.of (HwReg X Z (Finset HPos × Selections))) ℂ) (hρ : ρ.PosSemidef)
    {t₀ : Finset HPos}
    (hs : QuerySupportedOn (fun p : A × QReg.of (HwReg X Z (Finset HPos × Selections)) ↦
      p.2.2.2.1) {t₀} ρ)
    (B : Finset HPos) (ht₀ : Disjoint t₀ B)
    (Q : (recHwSpec X Z HPos Selections).Port → Prop) [DecidablePred Q]
    (C : ∀ i, Set ((recHwSpec X Z HPos Selections).In i ×
      QReg.of (HwReg X Z (Finset HPos × Selections))))
    (hCQ : ∀ i, ¬ Q i → C i = ∅) {v v' : (s : HPos) → XD s} (hv : Agree (Finset.univ \ B) v v')
    {N : ℕ}
    (hN : IFreeM.IsChargeBound (realizeT v y) (portCharge fun i ↦ if Q i then 1 else 0) N) :
    (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i)) (realizeT v y) ρ ≤
      (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i)) (realizeT v' y) ρ +
        N * revFirst m₀ I B (realizeT v' y) ρ := by
  have heq : ∀ C' : ∀ i, Set ((recHwSpec X Z HPos Selections).In i ×
      QReg.of (HwReg X Z (Finset HPos × Selections))),
      (∀ i p, p ∈ C' i → Disjoint p.2.2.2.1 B) →
      (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C' i)) (realizeT v y) ρ =
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C' i)) (realizeT v' y) ρ := fun C' hC' ↦
    tsum_congr fun j ↦ Quantum.Xmss.Hybrid.queryWeight_eq_of_viewBy_off (runtimeR m₀) I
      (fun r ↦ r.2.2.1) (fun u ↦ realizeT u y) (fun _ ↦ ρ) j
      (Quantum.Xmss.Assembly.viewBy_runtimeR_of_disc I m₀ y ∅ hdisc (fun _ ↦ ρ)
        (Quantum.Xmss.Hybrid.lazy_const _ ρ)
        (fun _ ↦ Quantum.Xmss.Hybrid.suppAt_empty _ ρ) j) B hv C' hC'
  have hsplit : ∀ u : (s : HPos) → XD s,
      (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i)) (realizeT u y) ρ =
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i ∩ {p | Disjoint p.2.2.2.1 B}))
          (realizeT u y) ρ +
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i \ {p | Disjoint p.2.2.2.1 B}))
          (realizeT u y) ρ := fun u ↦
    (congrArg (fun w ↦ (runtimeR m₀).totalWeight I w (realizeT u y) ρ)
      (funext fun i ↦ funext fun σ ↦
        Quantum.Xmss.Hybrid.diagMass_eq_inter_add_diff (C i) {p | Disjoint p.2.2.2.1 B} σ)).trans
      (Quantum.Xmss.Hybrid.totalWeight_add_weight (runtimeR m₀) I _ _ (realizeT u y) ρ)
  have hbad : (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i \ {p | Disjoint p.2.2.2.1 B}))
      (realizeT v y) ρ ≤ (runtimeR m₀).totalWeight I (badW B Q) (realizeT v y) ρ :=
    Quantum.Xmss.Hybrid.totalWeight_le_totalWeight _ I (fun i σ _ ↦ by
      show _ ≤ (if Q i then diagMass {p | ¬ Disjoint p.2.2.2.1 B} σ else 0)
      by_cases hQ : Q i
      · simp only [hQ, ↓reduceIte]
        exact Quantum.Xmss.Hybrid.diagMass_mono (fun p hp ↦ hp.2) σ
      · simp only [hQ, ↓reduceIte]
        exact le_of_eq (Finset.sum_eq_zero fun p _ ↦ Set.indicator_of_notMem
          (fun hp ↦ Set.notMem_empty p (hCQ i hQ ▸ hp.1)) _)) _ hρ
  have hrevSet : ∀ i p, p ∈ revSet X Z Selections B i → Disjoint p.2.2.2.1 B := fun i p hp ↦ by
    unfold revSet at hp
    split_ifs at hp
    · exact hp
    · exact hp.elim
  have hb : (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i \ {p | Disjoint p.2.2.2.1 B}))
      (realizeT v y) ρ ≤ N * revFirst m₀ I B (realizeT v' y) ρ :=
    hbad.trans ((Quantum.Xmss.Hybrid.totalWeight_badW_le m₀ I B Q v y hy N t₀ ht₀ ρ hρ hs
      hN).trans (mul_le_mul_of_nonneg_left (heq (revSet X Z Selections B) hrevSet).le zero_le))
  calc (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i)) (realizeT v y) ρ
      = (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i ∩ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v y) ρ +
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i \ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v y) ρ := hsplit v
    _ = (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i ∩ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v' y) ρ +
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i \ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v y) ρ :=
        congrArg (· + _) (heq (fun i ↦ C i ∩ {p | Disjoint p.2.2.2.1 B}) fun i p hp ↦ hp.2)
    _ ≤ (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i ∩ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v' y) ρ + N * revFirst m₀ I B (realizeT v' y) ρ := add_le_add le_rfl hb
    _ ≤ ((runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i ∩ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v' y) ρ +
        (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i \ {p | Disjoint p.2.2.2.1 B}))
          (realizeT v' y) ρ) + N * revFirst m₀ I B (realizeT v' y) ρ :=
        add_le_add le_self_add le_rfl
    _ = (runtimeR m₀).totalWeight I (fun i ↦ diagMass (C i)) (realizeT v' y) ρ +
        N * revFirst m₀ I B (realizeT v' y) ρ := congrArg (· + _) (hsplit v').symm

/-- **The first-meeting mismatch lemma for Graded's port masses.** -/
theorem totalWeight_portMass_le_mismatch_first (m₀ : Finset HPos × Selections) (I : L.Interp)
    {A : QReg} (y : QuantumComp L (tmplSpec X Z HPos XD Selections goodAll) Ω A)
    (hdisc : Disc y ∅) (hy : KeepsLab y)
    (ρ : Matrix (A × QReg.of (HwReg X Z (Finset HPos × Selections)))
      (A × QReg.of (HwReg X Z (Finset HPos × Selections))) ℂ) (hρ : ρ.PosSemidef)
    {t₀ : Finset HPos}
    (hs : QuerySupportedOn (fun p : A × QReg.of (HwReg X Z (Finset HPos × Selections)) ↦
      p.2.2.2.1) {t₀} ρ)
    (B : Finset HPos) (ht₀ : Disjoint t₀ B)
    (Q : (recHwSpec X Z HPos Selections).Port → Prop) [DecidablePred Q] (Hh : Set Z)
    (Hk Hk' : Set X) {v v' : (s : HPos) → XD s} (hv : Agree (Finset.univ \ B) v v') {N : ℕ}
    (hN : IFreeM.IsChargeBound (realizeT v y) (portCharge fun i ↦ if Q i then 1 else 0) N) :
    (runtimeR m₀).totalWeight I (portMass Q Hh Hk Hk') (realizeT v y) ρ ≤
      (runtimeR m₀).totalWeight I (portMass Q Hh Hk Hk') (realizeT v' y) ρ +
        N * revFirst m₀ I B (realizeT v' y) ρ := by
  rw [Quantum.Xmss.Hybrid.portMass_eq_diagMass]
  exact totalWeight_le_mismatch_first m₀ I y hdisc hy ρ hρ hs B ht₀ Q _
    (fun i hQ ↦ by simp only [hQ, ↓reduceIte]) hv hN

end mismatch

/-! ## The charged coordinates read off the coordinates -/

section charges

/-- The coordinates of the reparametrization. -/
abbrev CX : Type := PP × (((s : HPos) → XD s) × KK)

/-- **A digest label's capacity** at the public keys of `p`, under the root `root` and the
randomizer `R`. -/
def capD (p : PP) (root : Digest) (a : DLab) (R : Randomizer) : Z :=
  capOf p.1.2.2.2.1 p.1.2.2.2.2 p.1.2.2.1 (dLabCell a p.1.2.1 root R)

/-- **A randomizer label's capacity** at the coordinates: `π` and `PK.seed` of `p`, `SK.prf` and
the randomizer stage's coins of `k`. -/
def rCapK (p : PP) (k : KK) (M : Message) : Z :=
  (p.1.2.2.1 (rCell M p.1.2.1 k.1.2, k.2.2.1 M)).2 + k.2.2.2.1 M

/-- **An `SK.seed`-keyed capacity** at the coordinates: `SK.seed` and SeedStage's slots of `k`. -/
def sCapK (p : PP) (k : KK) (b : SkIdx) : Z :=
  (p.1.2.2.1 (skCell p.1.2.1 k.1.1 b, k.2.1.1 b)).2 + k.2.1.2 b

/-- The capacities the digest labels must avoid: the randomizer and `SK.seed`-keyed ones. -/
def ExtK (p : PP) (k : KK) (z : Z) : Prop :=
  (∃ M, rCapK p k M = z) ∨ ∃ b, sCapK p k b = z

/-- **A charged digest label** at the coordinates: a label of smaller rank at the same capacity,
or an extra capacity, at the hidden root and randomizers. -/
def DChg (x : CX) (a : DLab) : Prop :=
  (∃ b, dLabOrd b < dLabOrd a ∧ capD x.1 (rootV x.2.1) b (x.2.1 (.rnd b.1)) =
      capD x.1 (rootV x.2.1) a (x.2.1 (.rnd a.1))) ∨
    ExtK x.1 x.2.2 (capD x.1 (rootV x.2.1) a (x.2.1 (.rnd a.1)))

/-- **A non-first randomizer label** at the coordinates. -/
def RChg (p : PP) (k : KK) (M : Message) : Prop :=
  ∃ M', rOrd M' < rOrd M ∧ rCapK p k M' = rCapK p k M

/-- **A charged message**: its randomizer label or one of its digest labels is charged. -/
def MsgChg (x : CX) (M : Message) : Prop :=
  RChg x.1 x.2.2 M ∨ ∃ i, DChg x (M, i)

/-- The charged coordinates: the randomizer and both digests of a charged message. -/
def IsChgK (x : CX) : HPos → Prop
  | .rnd M => MsgChg x M
  | .dig M _ => MsgChg x M
  | _ => False

open scoped Classical in
/-- **The charged coordinates** as a finite set. Irreducible: membership does not unfold the
enumeration of the coordinates. -/
@[irreducible]
noncomputable def chgBK (x : CX) : Finset HPos :=
  Finset.univ.filter (IsChgK x)

theorem mem_chgBK {x : CX} {s : HPos} : s ∈ chgBK x ↔ IsChgK x s := by
  unfold chgBK
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The randomizer coordinate of a randomizer or `H_msg` coordinate's message. -/
def toRnd : HPos → HPos
  | .rnd M => .rnd M
  | .dig M _ => .rnd M
  | s => s

/-- The coordinates of the messages with a non-first randomizer label. -/
def IsRK (p : PP) (k : KK) : HPos → Prop
  | .rnd M => RChg p k M
  | .dig M _ => RChg p k M
  | _ => False

/-- The coordinates of the messages with a charged digest label. -/
def IsDK (x : CX) : HPos → Prop
  | .rnd M => ∃ i, DChg x (M, i)
  | .dig M _ => ∃ i, DChg x (M, i)
  | _ => False

open scoped Classical in
/-- **The randomizer part** of the charged coordinates (a function of `p` and the never-revealed
part only). Irreducible like `chgBK`. -/
@[irreducible]
noncomputable def rPartK (p : PP) (k : KK) : Finset HPos :=
  Finset.univ.filter (IsRK p k)

open scoped Classical in
/-- **The digest part** of the charged coordinates. Irreducible like `chgBK`. -/
@[irreducible]
noncomputable def dPartK (x : CX) : Finset HPos :=
  Finset.univ.filter (IsDK x)

theorem mem_rPartK {p : PP} {k : KK} {s : HPos} : s ∈ rPartK p k ↔ IsRK p k s := by
  unfold rPartK
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_dPartK {x : CX} {s : HPos} : s ∈ dPartK x ↔ IsDK x s := by
  unfold dPartK
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The charged coordinates are the two parts'. -/
theorem chgBK_subset_parts (x : CX) : chgBK x ⊆ rPartK x.1 x.2.2 ∪ dPartK x := by
  intro s hs
  have h := mem_chgBK.mp hs
  rw [Finset.mem_union, mem_rPartK, mem_dPartK]
  cases s with
  | rnd M => exact h
  | dig M i => exact h
  | val q => exact h.elim
  | str j i => exact h.elim
  | asg M j => exact h.elim

/-- The digest part is charged. -/
theorem dPartK_subset_chgBK (x : CX) : dPartK x ⊆ chgBK x := by
  intro s hs
  have h := mem_dPartK.mp hs
  refine mem_chgBK.mpr ?_
  cases s with
  | rnd M => exact Or.inr h
  | dig M i => exact Or.inr h
  | val q => exact h.elim
  | str j i => exact h.elim
  | asg M j => exact h.elim

/-- **A randomizer hitting a charge** of a digest label of `M`: at one of its calls the capacity
is an extra capacity, another message's label's capacity (at its hidden randomizer), or the two
calls' capacities agree. It does not read the hidden randomizer of `M`. -/
def Hit (x : CX) (M : Message) (R : Randomizer) : Prop :=
  ∃ i : DigestCall, ExtK x.1 x.2.2 (capD x.1 (rootV x.2.1) (M, i) R) ∨
    (∃ b : DLab, b.1 ≠ M ∧
      capD x.1 (rootV x.2.1) b (x.2.1 (.rnd b.1)) = capD x.1 (rootV x.2.1) (M, i) R) ∨
    capD x.1 (rootV x.2.1) (M, 0) R = capD x.1 (rootV x.2.1) (M, 1) R

open scoped Classical in
/-- **The randomizers hitting a charge** of `M`. Irreducible: membership does not unfold the
enumeration of the randomizers. -/
@[irreducible]
noncomputable def badR (x : CX) (M : Message) : Finset Randomizer :=
  Finset.univ.filter (Hit x M)

theorem mem_badR {x : CX} {M : Message} {R : Randomizer} : R ∈ badR x M ↔ Hit x M R := by
  unfold badR
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Typical coordinates**: every message has at most three randomizers hitting a charge. -/
def Typ (x : CX) : Prop :=
  ∀ M, (badR x M).card ≤ 3

/-- Two distinct calls are the two calls. -/
theorem digestCall_pair {a b : DigestCall} (h : a ≠ b) : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  revert a b
  decide

/-- **A charged digest label's randomizer hits a charge.** -/
theorem hit_of_dChg {x : CX} {M : Message} {i : DigestCall} (h : DChg x (M, i)) :
    Hit x M (x.2.1 (.rnd M)) := by
  rcases h with ⟨⟨M', j⟩, hb, he⟩ | he
  · by_cases hbM : M' = M
    · subst hbM
      have hji : j ≠ i := fun e ↦ by
        subst e
        exact lt_irrefl _ hb
      refine ⟨i, Or.inr (Or.inr ?_)⟩
      rcases digestCall_pair hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact he
      · exact he.symm
    · exact ⟨i, Or.inr (Or.inl ⟨(M', j), hbM, he⟩)⟩
  · exact ⟨i, Or.inl he⟩

/-- `Hit` does not read the hidden randomizer of `M`. -/
theorem hit_update {x : CX} {M : Message} {R : Randomizer} (d : XD (.rnd M)) :
    Hit (x.1, (Function.update x.2.1 (.rnd M) d, x.2.2)) M R ↔ Hit x M R := by
  have hroot : rootV (Function.update x.2.1 (.rnd M) d) = rootV x.2.1 :=
    Function.update_of_ne (by simp) _ _
  have hb : ∀ b : DLab, b.1 ≠ M →
      Function.update x.2.1 (.rnd M) d (.rnd b.1) = x.2.1 (.rnd b.1) := fun b hb ↦
    Function.update_of_ne (by simpa using hb) _ _
  unfold Hit
  simp only [hroot]
  constructor
  · rintro ⟨i, h | ⟨b, hbM, he⟩ | h⟩
    · exact ⟨i, Or.inl h⟩
    · exact ⟨i, Or.inr (Or.inl ⟨b, hbM, (hb b hbM).symm ▸ he⟩)⟩
    · exact ⟨i, Or.inr (Or.inr h)⟩
  · rintro ⟨i, h | ⟨b, hbM, he⟩ | h⟩
    · exact ⟨i, Or.inl h⟩
    · exact ⟨i, Or.inr (Or.inl ⟨b, hbM, (hb b hbM) ▸ he⟩)⟩
    · exact ⟨i, Or.inr (Or.inr h)⟩

theorem badR_update {x : CX} {M : Message} (d : XD (.rnd M)) :
    badR (x.1, (Function.update x.2.1 (.rnd M) d, x.2.2)) M = badR x M := by
  ext R
  rw [mem_badR, mem_badR, hit_update]

end charges

/-! ## The coordinates of the digest stage's output -/

section psi

variable (y : (((Z → X) × XW) × (ValPos → Digest)) × RestF)

theorem psiE_dLast_xw : (psiE (dLast y)).1.1.2 = y.1.1.2 := by
  obtain ⟨h₃, hc₃, e⟩ := dLast_eq y
  rw [e]
  rfl

theorem psiE_dLast_rnd (M : Message) :
    (psiE (dLast y)).2.1 (.rnd M) = trunc128 (y.2.2.2.1.2.2 M) := by
  obtain ⟨h₃, hc₃, e⟩ := dLast_eq y
  rw [e]
  rfl

theorem psiE_dLast_root : rootV (psiE (dLast y)).2.1 = y.1.2 rootPos := by
  obtain ⟨h₃, hc₃, e⟩ := dLast_eq y
  rw [e]
  rfl

theorem psiE_dLast_secret : (psiE (dLast y)).2.2.1 = y.2.2.2.2.1 := by
  obtain ⟨h₃, hc₃, e⟩ := dLast_eq y
  rw [e]
  rfl

theorem psiE_dLast_seedKS : (psiE (dLast y)).2.2.2.1 = y.2.2.2.2.2.1 := by
  obtain ⟨h₃, hc₃, e⟩ := dLast_eq y
  rw [e]
  rfl

theorem psiE_dLast_rk : (psiE (dLast y)).2.2.2.2.1 = y.2.2.2.1.1 := by
  obtain ⟨h₃, hc₃, e⟩ := dLast_eq y
  rw [e]
  rfl

theorem psiE_dLast_rk' : (psiE (dLast y)).2.2.2.2.2.1 = y.2.2.2.1.2.1 := by
  obtain ⟨h₃, hc₃, e⟩ := dLast_eq y
  rw [e]
  rfl

/-- The digest labels' capacities at the coordinates are the path stages'. -/
theorem capD_psiE (a : DLab) :
    capD (psiE (dLast y)).1 (rootV (psiE (dLast y)).2.1) a ((psiE (dLast y)).2.1 (.rnd a.1)) =
      capOf y.1.1.2.2.2.1 y.1.1.2.2.2.2 y.1.1.2.2.1 (dcYy y a) := by
  unfold capD
  rw [psiE_dLast_xw, psiE_dLast_root, psiE_dLast_rnd]
  rfl

theorem rCapK_psiE (M : Message) :
    rCapK (psiE (dLast y)).1 (psiE (dLast y)).2.2 M =
      (y.1.1.2.2.1 (rCell M y.1.1.2.1 y.2.2.2.2.1.2, y.2.2.2.1.1 M)).2 + y.2.2.2.1.2.1 M := by
  unfold rCapK
  rw [psiE_dLast_xw, psiE_dLast_secret, psiE_dLast_rk, psiE_dLast_rk']

theorem sCapK_psiE (b : SkIdx) :
    sCapK (psiE (dLast y)).1 (psiE (dLast y)).2.2 b =
      (y.1.1.2.2.1 (skCell y.1.1.2.1 y.2.2.2.2.1.1 b, y.2.2.2.2.2.1.1 b)).2 +
        y.2.2.2.2.2.1.2 b := by
  unfold sCapK
  rw [psiE_dLast_xw, psiE_dLast_secret, psiE_dLast_seedKS]

/-- Membership in two families' cells. -/
theorem mem_famCells_iff {A B : Type} [Fintype A] [Fintype B] (r : A → Z) (s : B → Z) (z : Z) :
    z ∈ famCells r s ↔ (∃ a, r a = z) ∨ ∃ b, s b = z := by
  unfold famCells
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]

/-- **DigestStage's charged labels are charged at the coordinates.** -/
theorem dChg_of_mem_dBX (hrate : RateInjY (yView y)) {a : DLab} (ha : a ∈ dBX (zOf y)) :
    DChg (psiE (dLast y)) a := by
  have hcap : ∀ b, capD (psiE (dLast y)).1 (rootV (psiE (dLast y)).2.1) b
      ((psiE (dLast y)).2.1 (.rnd b.1)) = pCellH dcY (zOf y) b := fun b ↦
    (capD_psiE y b).trans ((zOf_spec y hrate).1 b).symm
  rcases ha with ⟨b, hb, he⟩ | hx
  · exact Or.inl ⟨b, hb, by rw [hcap, hcap]; exact he⟩
  · refine Or.inr ?_
    rw [hcap]
    rcases (mem_famCells_iff _ _ _).mp hx with ⟨M, hM⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨M, (rCapK_psiE y M).trans ((rCapY_zOf y M).symm.trans hM)⟩
    · exact Or.inr ⟨b, (sCapK_psiE y b).trans ((sCapY_zOf y b).symm.trans hb)⟩

end psi

/-! ## The table's charged coordinates are charged at the coordinates -/

section table

variable {t : FT}

/-- **The table's randomizer capacities are `rCapK`** at the coordinates. -/
theorem rCellH_eq_rCapK (ht : StageGood t) (M : Message) :
    rCellH rCell (tabOf t) M = rCapK (fullE t).1 (fullE t).2.2 M := by
  rw [fullE_eq, rCapK_psiE, yOf_xw, yOf_snd]
  obtain ⟨k₂, k'₂, sk₂, -, he2, -⟩ := phiE_spec t
  have hR := rGood_of_dGood ht.1
  obtain ⟨-, c1, c2, -, -⟩ := Quantum.Sphincs.Hybrid.rSplit_coords
    Quantum.Sphincs.Hybrid.rCell_injective hR
  obtain ⟨-, -, d3, d4⟩ := dFull_coins (θ := t.1.1.1)
  have hsec := dFull_secret (θ := t.1.1.1)
  have hP := wPub_seed ht
  have hπ : (phiE t).1.2.2.1 = (tabOf t).perm := wPub_perm
  have e1 : (phiE t).2.2.2.1.1 M = (tabOf t).keys.2.1 (rCellK rCell (tabOf t) M) := by
    rw [he2]
    exact (congrFun d3 M).trans (c1 M)
  have e2 : (phiE t).2.2.2.1.2.1 M = (tabOf t).keys.2.2 (rCellK' rCell (tabOf t) M) := by
    rw [he2]
    exact (congrFun d4 M).trans (c2 M)
  have e3 : (phiE t).2.2.2.2.1.2 = (tabOf t).prfKey := by
    rw [he2]
    show (dFull t.1.1.1).2.2.2 = _
    rw [hsec]
  rw [e1, e2, e3, hP, hπ]
  rfl

/-- The table's non-first randomizer labels are non-first at the coordinates. -/
theorem rChg_of_mem_rB (ht : StageGood t) {M : Message} (hM : M ∈ rB rCell rOrd (tabOf t)) :
    RChg (fullE t).1 (fullE t).2.2 M := by
  obtain ⟨M', h1, h2⟩ := hM
  exact ⟨M', h1, (rCellH_eq_rCapK ht M').symm.trans (h2.trans (rCellH_eq_rCapK ht M))⟩

/-- **The charged coordinates of a table are charged at its coordinates.** -/
theorem chgB_subset_chgBK (ht : FullD t) : chgB t ⊆ chgBK (fullE t) := by
  intro s hs
  have hs' := mem_chgB.mp hs
  refine mem_chgBK.mpr ?_
  cases s with
  | rnd M => exact Or.inl (rChg_of_mem_rB ht.1 hs')
  | dig M i =>
    rcases hs' with h | h
    · exact Or.inl (rChg_of_mem_rB ht.1 h)
    · refine Or.inr ⟨i, ?_⟩
      rw [fullE_eq]
      exact dChg_of_mem_dBX (yOf t) ht.2.2.2.1 h
  | val q => exact hs'.elim
  | str j i => exact hs'.elim
  | asg M j => exact hs'.elim

end table

end Quantum.Sphincs.Assembly

end
