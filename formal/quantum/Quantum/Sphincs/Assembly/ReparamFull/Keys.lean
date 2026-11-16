module

public import Quantum.Sphincs.Assembly.Reparam
public import Quantum.Sphincs.Assembly.PathsDisjoint
public import Quantum.Sphincs.Assembly.FullTable

@[expose] public section

/-!
# leanSPHINCS's values at public keys agreeing with a table's on its paths

`Quantum.Sphincs.Assembly.Reparam`'s `sVal_tabW` at public data `w` and a key `h` other than the
table's own (`tabW L`, `L.keys.1`) that agree with the table's keys only on the cells of its
in-table paths (`PathKeys`; the leanSPHINCS analog of leanXMSS's `ReparamR0` keys section).

* `cells_eq_of_slotBlk`: blocks equal to the table's give the table's cells (`rnK_congr`,
  `rnR_congr`, `rnZ_congr` of PathBad's rounds).
* `sVal_eq_valuePos_keys`: with the chain starts and FORS secrets in the pad, the values are
  `valuePos L` at every live position (by rank).
* `slotBlk_sVal_keys`, `cells_eq_keys`, `cellVals_eq_keys`: an in-table slot's blocks, cells and
  key values at the values `sVal w h u` are the table's.
* `live_of_fullPos`: the tabulated positions of `FullTable` are live.
-/

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Assembly (RnAgree rnK_congr rnR_congr rnZ_congr XW)

namespace Quantum.Sphincs.Assembly

/-- Keys agreeing with the table's on its in-table paths (cells at the table's keys and values). -/
def PathKeys (L : HonestTable) (w : XW) (h : Z → X) : Prop :=
  w.1 = L.publicSeed ∧ w.2.1 = L.perm ∧ ∀ s, InTable s → ∀ j < nBlk L.publicSeed s,
    w.2.2.1 (sCellK (tabW L) L.keys.1 s (valuePos L) j) =
        L.keys.2.1 (sCellK (tabW L) L.keys.1 s (valuePos L) j) ∧
      w.2.2.2 (sCellR (tabW L) L.keys.1 s (valuePos L) j) =
        L.keys.2.2 (sCellR (tabW L) L.keys.1 s (valuePos L) j) ∧
      h (sCellZ (tabW L) L.keys.1 s (valuePos L) j) =
        L.keys.1 (sCellZ (tabW L) L.keys.1 s (valuePos L) j)

/-- **Blocks equal to the table's give the table's cells** at keys agreeing on its paths. -/
theorem cells_eq_of_slotBlk {L : HonestTable} {w : XW} {h : Z → X} (hk : PathKeys L w h)
    {s : Slot} (hs : InTable s) {g : ValPos → Digest}
    (hb : slotBlk w.1 s g = slotBlk L.publicSeed s (valuePos L)) {j : ℕ}
    (hj : j < nBlk L.publicSeed s) :
    sCellK w h s g j = sCellK (tabW L) L.keys.1 s (valuePos L) j ∧
    sCellR w h s g j = sCellR (tabW L) L.keys.1 s (valuePos L) j ∧
    sCellZ w h s g j = sCellZ (tabW L) L.keys.1 s (valuePos L) j := by
  obtain ⟨-, hπ, hag⟩ := hk
  have hR : RnAgree L.perm L.keys.1 L.keys.2.1 L.keys.2.2 h w.2.2.1 w.2.2.2
      (slotBlk L.publicSeed s (valuePos L)) (j + 1) := fun i hi ↦ hag s hs i (by omega)
  have hRj : RnAgree L.perm L.keys.1 L.keys.2.1 L.keys.2.2 h w.2.2.1 w.2.2.2
      (slotBlk L.publicSeed s (valuePos L)) j := fun i hi ↦ hR i (by omega)
  obtain ⟨e1, e2, -⟩ := hR j (Nat.lt_succ_self j)
  unfold sCellK sCellR sCellZ
  rw [hb, hπ]
  exact ⟨rnK_congr hRj, rnR_congr hRj e1, rnZ_congr hRj e1 e2⟩

/-- **The values at keys agreeing with the table's on its paths**: with its chain starts and FORS
secrets in the pad, the values are `valuePos L` at every live position. -/
theorem sVal_eq_valuePos_keys {L : HonestTable} {w : XW} {h : Z → X} {u : ValPos → Digest}
    (hk : PathKeys L w h) (hu : ∀ q, SecretPos q → u q = valuePos L q) :
    ∀ q, Live q → sVal w h u q = valuePos L q := by
  intro q
  induction hn : sRank q using Nat.strong_induction_on generalizing q with
  | _ n ih =>
    intro hq
    by_cases hp : InPos q
    · rw [sVal_of_inPos _ _ _ hp]
      have hb : slotBlk w.1 (outSlot q) (sVal w h u) =
          slotBlk L.publicSeed (outSlot q) (valuePos L) := by
        rw [hk.1]
        exact slotBlk_congr_inPos _ hp fun r hr hrq ↦ ih (sRank r) (hn ▸ hrq) r rfl hr
      have hlt : nBlk L.publicSeed (outSlot q) - 1 < nBlk L.publicSeed (outSlot q) := by
        have := nBlk_pos L.publicSeed (outSlot q)
        omega
      obtain ⟨-, e2, e3⟩ := cells_eq_of_slotBlk hk hp.1 hb hlt
      have hn' : nBlk w.1 (outSlot q) = nBlk L.publicSeed (outSlot q) := by rw [hk.1]
      have hR : sOutRate w h (outSlot q) (sVal w h u) =
          sOutRate (tabW L) L.keys.1 (outSlot q) (valuePos L) := by
        unfold sOutRate
        rw [hn']
        exact e2
      have hC : sOutCap w h (outSlot q) (sVal w h u) =
          sOutCap (tabW L) L.keys.1 (outSlot q) (valuePos L) := by
        unfold sOutCap
        rw [hn']
        exact e3
      have hZ : h (sOutCap (tabW L) L.keys.1 (outSlot q) (valuePos L)) =
          L.keys.1 (sOutCap (tabW L) L.keys.1 (outSlot q) (valuePos L)) :=
        (hk.2.2 _ hp.1 _ hlt).2.2
      rw [hR, hC, hZ, ← trunc128_spongeHash_slot (tabW L) L.keys.1 (outSlot q) (valuePos L)]
      have ht := L.target_eq_some hp.1
      rw [HonestTable.target, L.honestInput_eq_slotInput hp.1, Option.map_some, hp.2] at ht
      exact Option.some.inj ht
    · rw [sVal_of_not_inPos _ _ _ hp]
      exact hu q (hq.resolve_left hp)

/-- At keys agreeing with the table's on its paths, an in-table slot's blocks at the values are
those at `valuePos L`. -/
theorem slotBlk_sVal_keys {L : HonestTable} {w : XW} {h : Z → X} {u : ValPos → Digest}
    (hk : PathKeys L w h) (hu : ∀ q, SecretPos q → u q = valuePos L q) {s : Slot}
    (hs : InTable s) :
    slotBlk w.1 s (sVal w h u) = slotBlk L.publicSeed s (valuePos L) := by
  rw [hk.1]
  exact slotBlk_congr_live _ hs fun q hq _ ↦ sVal_eq_valuePos_keys hk hu q hq

/-- **The cells of an in-table path** at keys agreeing with the table's on its paths and the
values `sVal w h u` are the table's. -/
theorem cells_eq_keys {L : HonestTable} {w : XW} {h : Z → X} {u : ValPos → Digest}
    (hk : PathKeys L w h) (hu : ∀ q, SecretPos q → u q = valuePos L q)
    {s : Slot} (hs : InTable s) {j : ℕ} (hj : j < nBlk L.publicSeed s) :
    sCellK w h s (sVal w h u) j = sCellK (tabW L) L.keys.1 s (valuePos L) j ∧
    sCellR w h s (sVal w h u) j = sCellR (tabW L) L.keys.1 s (valuePos L) j ∧
    sCellZ w h s (sVal w h u) j = sCellZ (tabW L) L.keys.1 s (valuePos L) j :=
  cells_eq_of_slotBlk hk hs (slotBlk_sVal_keys hk hu hs) hj

/-- **The key values at an in-table path's cells** at keys agreeing with the table's on its paths
and the values `sVal w h u` are the table's. -/
theorem cellVals_eq_keys {L : HonestTable} {w : XW} {h : Z → X} {u : ValPos → Digest}
    (hk : PathKeys L w h) (hu : ∀ q, SecretPos q → u q = valuePos L q)
    {s : Slot} (hs : InTable s) {j : ℕ} (hj : j < nBlk L.publicSeed s) :
    w.2.2.1 (sCellK w h s (sVal w h u) j) =
        L.keys.2.1 (sCellK (tabW L) L.keys.1 s (valuePos L) j) ∧
    w.2.2.2 (sCellR w h s (sVal w h u) j) =
        L.keys.2.2 (sCellR (tabW L) L.keys.1 s (valuePos L) j) ∧
    h (sCellZ w h s (sVal w h u) j) = L.keys.1 (sCellZ (tabW L) L.keys.1 s (valuePos L) j) := by
  obtain ⟨e1, e2, e3⟩ := cells_eq_keys hk hu hs hj
  rw [e1, e2, e3]
  exact hk.2.2 s hs j hj

/-- **The tabulated positions are live.** -/
theorem live_of_fullPos {q : ValPos} (hq : FullPos q) : Live q := by
  cases q with
  | chain l τ e i j =>
    obtain ⟨hτ, he⟩ := hq
    have hc : cpos l τ e i j.val = .chain l τ e i j :=
      congrArg _ (Fin.ext (Nat.mod_eq_of_lt j.isLt))
    rw [← hc]
    exact live_cpos i hτ he j.isLt
  | tree l τ level index =>
    obtain ⟨hτ, hl, hi⟩ := hq
    have hc : tpos l τ level.val index.val = .tree l τ level index :=
      congrArg₂ (ValPos.tree l τ) (Fin.ext (Nat.mod_eq_of_lt level.isLt))
        (Fin.ext (Nat.mod_eq_of_lt index.isLt))
    rw [← hc]
    exact live_tpos hτ hl hi
  | forsSecret => exact Or.inr trivial
  | forsTree idx κ height node =>
    have hc : fpos idx κ height.val node.val = .forsTree idx κ height node :=
      congrArg₂ (ValPos.forsTree idx κ) (Fin.ext (Nat.mod_eq_of_lt height.isLt))
        (Fin.ext (Nat.mod_eq_of_lt node.isLt))
    rw [← hc]
    exact live_fpos idx κ (Nat.lt_succ_iff.mp height.isLt) hq
  | forsKey idx => exact Or.inl (inPos_slotOutPos (s := .forsRoots idx) trivial)

end Quantum.Sphincs.Assembly

end
