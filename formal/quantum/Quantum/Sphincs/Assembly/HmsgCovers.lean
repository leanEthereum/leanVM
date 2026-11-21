module

public import Quantum.Sphincs.Assembly.ReparamFull

@[expose] public section

/-!
# The `H_msg` cells of the full table at the reparametrized data

The full table (`fullHw`) hardwires both `H_msg` calls of every message at the table's randomizer.
Their cells are functions of the public data, the root and the randomizer (`hmCellK`, `hmCellR`,
`hmCellZ`; no stage moved `k`, `k'` at them). On the core good set of the composed
reparametrization:

* the randomizer stage's cells are read off the never-revealed part (`rcK`, `rRateK`, `rCapKK`:
  `SK.prf` and the coin slots, `rCells_fullE`), so the non-first messages are `rBK` of the public
  data and the never-revealed part (`rB_eq_rBK`);
* the table's `H_msg` cells are the template's at `(pubP p, root)` for every randomizer
  (`hmCells_fullE`); a first message's randomizer is the hidden `.rnd M` (`rnd_fullE`), so its cells
  are in `tmCellsH` (and `K`, `K'`); a non-first message's cells are in `rbCellsH` (any randomizer
  of a message in `rBK`), a set of the public data, the hidden values and the never-revealed part
  (`hmCells_subset`).

The sets are restricted to the static condition `HStatic` on the public data and the root: the
`H_msg` rates are injective over all randomizers and calls (`HmsgRateInj`), no six `H_msg` inputs
share a capacity (`HmsgCapLoad`).
-/

open scoped ENNReal

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (capOf rateOf)
open Quantum.Sphincs.Hybrid (DLab dLabCell rCell rOrd rB rCellK rCellK' rCellH rCell_injective
  rSplit_coords)

namespace Quantum.Sphincs.Assembly

/-! ## The randomizer stage's cells at the coordinates -/

section rstage

/-- A message's `PRF_msg` first block at the coordinates: `PK.seed` and `SK.prf`. -/
def rcK (p : PP) (k : KK) (M : Message) : X :=
  rCell M (pubP p).seed k.1.2

/-- A message's `PRF_msg` rate at the coordinates: the `k`-coin. -/
def rRateK (p : PP) (k : KK) (M : Message) : X :=
  ((pubP p).perm (rcK p k M, k.2.2.1 M)).1

/-- A message's `PRF_msg` capacity at the coordinates: the `k`- and `k'`-coins. -/
def rCapKK (p : PP) (k : KK) (M : Message) : Z :=
  ((pubP p).perm (rcK p k M, k.2.2.1 M)).2 + k.2.2.2.1 M

/-- **The non-first messages at the coordinates**: a message of smaller rank has the same
`PRF_msg` capacity. -/
def rBK (p : PP) (k : KK) : Set Message :=
  {M | ∃ M', rOrd M' < rOrd M ∧ rCapKK p k M' = rCapKK p k M}

/-- The never-revealed part's `(SK.seed, SK.prf)` and randomizer coins are those of the rest of
Reparam's coordinates. -/
theorem fullE_kk (t : FT) :
    (fullE t).2.2.1 = (phiE t).2.2.2.2.1 ∧ (fullE t).2.2.2.2.1 = (phiE t).2.2.2.1.1 ∧
      (fullE t).2.2.2.2.2.1 = (phiE t).2.2.2.1.2.1 := by
  obtain ⟨h₃, hc₃, e⟩ := dLast_eq (yOf t)
  refine ⟨?_, ?_, ?_⟩
  · show (psiE (dLast (yOf t))).2.2.1 = _
    rw [e]
    rfl
  · show (psiE (dLast (yOf t))).2.2.2.2.1 = _
    rw [e]
    rfl
  · show (psiE (dLast (yOf t))).2.2.2.2.2.1 = _
    rw [e]
    rfl

variable {t : FT}

/-- **The table's randomizer cells are read off the coordinates.** -/
theorem rCells_fullE (ht : FullGCore t) (M : Message) :
    rCellK rCell (tabOf t) M = rcK (fullE t).1 (fullE t).2.2 M ∧
      rCellK' rCell (tabOf t) M = rRateK (fullE t).1 (fullE t).2.2 M ∧
      rCellH rCell (tabOf t) M = rCapKK (fullE t).1 (fullE t).2.2 M := by
  have hst := ht.1.1
  have hR := rGood_of_dGood hst.1
  have hc := rSplit_coords rCell_injective hR
  obtain ⟨e1, e2, e3⟩ := fullE_kk t
  obtain ⟨r1, r2⟩ := phiE_rest t
  obtain ⟨-, -, c3, c4⟩ := dFull_coins (θ := t.1.1.1)
  have h1 : rCellK rCell (tabOf t) M = rcK (fullE t).1 (fullE t).2.2 M := by
    show rCell M (tabOf t).publicSeed (tabOf t).prfKey =
      rCell M (pubP (fullE t).1).seed (fullE t).2.2.1.2
    rw [pubP_seed hst, e1, r2, dFull_secret]
  have hk : (fullE t).2.2.2.2.1 M = (tabOf t).keys.2.1 (rCellK rCell (tabOf t) M) := by
    rw [e2, r1, c3]
    exact hc.2.1 M
  have hk' : (fullE t).2.2.2.2.2.1 M = (tabOf t).keys.2.2 (rCellK' rCell (tabOf t) M) := by
    rw [e3, r1, c4]
    exact hc.2.2.1 M
  refine ⟨h1, ?_, ?_⟩
  · unfold rRateK
    rw [← h1, hk, pubP_perm]
    rfl
  · unfold rCapKK
    rw [← h1, hk, hk', pubP_perm]
    rfl

/-- **The non-first messages are read off the coordinates.** -/
theorem rB_eq_rBK (ht : FullGCore t) :
    rB rCell rOrd (tabOf t) = rBK (fullE t).1 (fullE t).2.2 := by
  refine Set.ext fun M ↦ ⟨fun ⟨M', h1, h2⟩ ↦ ⟨M', h1, ?_⟩, fun ⟨M', h1, h2⟩ ↦ ⟨M', h1, ?_⟩⟩
  · rw [← (rCells_fullE ht M').2.2, ← (rCells_fullE ht M).2.2]
    exact h2
  · rw [(rCells_fullE ht M').2.2, (rCells_fullE ht M).2.2]
    exact h2

end rstage

/-! ## The `H_msg` cells -/

section hmsg

/-- The `k`-cell of `H_msg` call `a = (M, i)` at the public data, the root and the randomizer. -/
def hmCellK (pub : Pub) (root : Digest) (R : Randomizer) (a : DLab) : X :=
  dLabCell a pub.seed root R

/-- Its `k'`-cell. -/
def hmCellR (pub : Pub) (root : Digest) (R : Randomizer) (a : DLab) : X :=
  rateOf pub.keys.2.1 pub.perm (hmCellK pub root R a)

/-- Its `h`-cell. -/
def hmCellZ (pub : Pub) (root : Digest) (R : Randomizer) (a : DLab) : Z :=
  capOf pub.keys.2.1 pub.keys.2.2 pub.perm (hmCellK pub root R a)

/-- **The `H_msg` rates are injective** over all randomizers and calls. -/
def HmsgRateInj (pub : Pub) (root : Digest) : Prop :=
  Function.Injective fun c : Randomizer × DLab ↦ hmCellR pub root c.1 c.2

/-- **At most five `H_msg` inputs share a capacity.** -/
def HmsgCapLoad (pub : Pub) (root : Digest) : Prop :=
  ∀ z : Z, ∃ T : Finset (Randomizer × DLab), T.card ≤ 5 ∧
    ∀ (R : Randomizer) (a : DLab), hmCellZ pub root R a = z → (R, a) ∈ T

/-- **The static condition of the `H_msg` cells** at the public data and the root. -/
def HStatic (pub : Pub) (root : Digest) : Prop :=
  HmsgRateInj pub root ∧ HmsgCapLoad pub root

/-- One-block rates and capacities at agreeing keys. -/
theorem rate_cap_congr {k₁ k₂ k'₁ k'₂ : X → Z} {π₁ π₂ : Equiv.Perm (X × Z)} {b : X}
    (hπ : π₁ = π₂) (hk : k₁ b = k₂ b) (hk' : k'₁ (rateOf k₁ π₁ b) = k'₂ (rateOf k₁ π₁ b)) :
    rateOf k₁ π₁ b = rateOf k₂ π₂ b ∧ capOf k₁ k'₁ π₁ b = capOf k₂ k'₂ π₂ b := by
  subst hπ
  have hr : rateOf k₁ π₁ b = rateOf k₂ π₁ b := by
    unfold rateOf
    rw [hk]
  refine ⟨hr, ?_⟩
  unfold capOf
  rw [← hk]
  exact congrArg _ hk'

variable {t : FT}

/-- **The table's `H_msg` cells are the template's** at the reparametrized public data and the
hidden root, at every randomizer. -/
theorem hmCells_fullE (ht : FullGCore t) (R : Randomizer) (a : DLab) :
    hmCellK (pubOf (tabOf t)) (tabOf t).root R a =
        hmCellK (pubP (fullE t).1) (rootV (fullE t).2.1) R a ∧
      hmCellR (pubOf (tabOf t)) (tabOf t).root R a =
        hmCellR (pubP (fullE t).1) (rootV (fullE t).2.1) R a ∧
      hmCellZ (pubOf (tabOf t)) (tabOf t).root R a =
        hmCellZ (pubP (fullE t).1) (rootV (fullE t).2.1) R a := by
  have hst := ht.1.1
  have hK : hmCellK (pubOf (tabOf t)) (tabOf t).root R a =
      hmCellK (pubP (fullE t).1) (rootV (fullE t).2.1) R a := by
    unfold hmCellK rootV
    rw [root_fullE hst, pubP_seed hst]
    rfl
  have hkk := pubP_kk (t := t)
  have hk : (pubP (fullE t).1).keys.2.1 (hmCellK (pubOf (tabOf t)) (tabOf t).root R a) =
      (tabOf t).keys.2.1 (hmCellK (pubOf (tabOf t)) (tabOf t).root R a) := by
    rw [hkk]
    exact kPub_hmsg hst a (tabOf t).root R
  have hk' : (pubP (fullE t).1).keys.2.2 (rateOf (tabOf t).keys.2.1 (tabOf t).perm
        (hmCellK (pubOf (tabOf t)) (tabOf t).root R a)) =
      (tabOf t).keys.2.2 (rateOf (tabOf t).keys.2.1 (tabOf t).perm
        (hmCellK (pubOf (tabOf t)) (tabOf t).root R a)) := by
    rw [hkk]
    exact k'Pub_hmsg hst ht.2.2.1 a (tabOf t).root R
  have hrc := rate_cap_congr (b := hmCellK (pubOf (tabOf t)) (tabOf t).root R a)
    (k₁ := (tabOf t).keys.2.1) (k'₁ := (tabOf t).keys.2.2) pubP_perm.symm hk.symm hk'.symm
  refine ⟨hK, ?_, ?_⟩
  · unfold hmCellR
    rw [← hK]
    exact hrc.1
  · unfold hmCellZ
    rw [← hK]
    exact hrc.2

/-- The template's `H_msg` `h`-cells at the hidden randomizers, on the static condition. -/
def tmCellsH (p : PP) (v : (s : HPos) → XD s) : Set Z :=
  {z | HStatic (pubP p) (rootV v) ∧
    ∃ (M : Message) (i : DigestCall), hmCellZ (pubP p) (rootV v) (v (.rnd M)) (M, i) = z}

/-- The template's `H_msg` `k`-cells at the hidden randomizers, on the static condition. -/
def tmCellsK (p : PP) (v : (s : HPos) → XD s) : Set X :=
  {x | HStatic (pubP p) (rootV v) ∧
    ∃ (M : Message) (i : DigestCall), hmCellK (pubP p) (rootV v) (v (.rnd M)) (M, i) = x}

/-- The template's `H_msg` `k'`-cells at the hidden randomizers, on the static condition. -/
def tmCellsK' (p : PP) (v : (s : HPos) → XD s) : Set X :=
  {x | HStatic (pubP p) (rootV v) ∧
    ∃ (M : Message) (i : DigestCall), hmCellR (pubP p) (rootV v) (v (.rnd M)) (M, i) = x}

/-- The `H_msg` `h`-cells of the non-first messages at any randomizer, on the static condition. -/
def rbCellsH (p : PP) (w : ((s : HPos) → XD s) × KK) : Set Z :=
  {z | HStatic (pubP p) (rootV w.1) ∧ ∃ M ∈ rBK p w.2, ∃ (i : DigestCall) (R : Randomizer),
    hmCellZ (pubP p) (rootV w.1) R (M, i) = z}

/-- The `H_msg` `k`-cells of the non-first messages at any randomizer, on the static condition. -/
def rbCellsK (p : PP) (w : ((s : HPos) → XD s) × KK) : Set X :=
  {x | HStatic (pubP p) (rootV w.1) ∧ ∃ M ∈ rBK p w.2, ∃ (i : DigestCall) (R : Randomizer),
    hmCellK (pubP p) (rootV w.1) R (M, i) = x}

/-- The `H_msg` `k'`-cells of the non-first messages at any randomizer, on the static condition. -/
def rbCellsK' (p : PP) (w : ((s : HPos) → XD s) × KK) : Set X :=
  {x | HStatic (pubP p) (rootV w.1) ∧ ∃ M ∈ rBK p w.2, ∃ (i : DigestCall) (R : Randomizer),
    hmCellR (pubP p) (rootV w.1) R (M, i) = x}

/-- **The table's `H_msg` cells are covered**, on the static condition: by the template's at the
hidden randomizers (first messages) or by the non-first messages' cells. -/
theorem hmCells_subset (ht : FullGCore t)
    (hS : HStatic (pubP (fullE t).1) (rootV (fullE t).2.1)) (M : Message) (i : DigestCall) :
    hmCellZ (pubOf (tabOf t)) (tabOf t).root ((tabOf t).randomizer M) (M, i) ∈
        tmCellsH (fullE t).1 (fullE t).2.1 ∪ rbCellsH (fullE t).1 (fullE t).2 ∧
      hmCellK (pubOf (tabOf t)) (tabOf t).root ((tabOf t).randomizer M) (M, i) ∈
        tmCellsK (fullE t).1 (fullE t).2.1 ∪ rbCellsK (fullE t).1 (fullE t).2 ∧
      hmCellR (pubOf (tabOf t)) (tabOf t).root ((tabOf t).randomizer M) (M, i) ∈
        tmCellsK' (fullE t).1 (fullE t).2.1 ∪ rbCellsK' (fullE t).1 (fullE t).2 := by
  obtain ⟨h1, h2, h3⟩ := hmCells_fullE ht ((tabOf t).randomizer M) (M, i)
  by_cases hM : M ∈ rB rCell rOrd (tabOf t)
  · have hM' : M ∈ rBK (fullE t).1 (fullE t).2.2 := (rB_eq_rBK ht) ▸ hM
    exact ⟨Or.inr ⟨hS, M, hM', i, _, h3.symm⟩, Or.inr ⟨hS, M, hM', i, _, h1.symm⟩,
      Or.inr ⟨hS, M, hM', i, _, h2.symm⟩⟩
  · have hr := rnd_fullE ht.1.1 M hM
    refine ⟨Or.inl ⟨hS, M, i, ?_⟩, Or.inl ⟨hS, M, i, ?_⟩, Or.inl ⟨hS, M, i, ?_⟩⟩
    · rw [hr]
      exact h3.symm
    · rw [hr]
      exact h1.symm
    · rw [hr]
      exact h2.symm

end hmsg

end Quantum.Sphincs.Assembly

end
