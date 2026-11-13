/-
  LeanVM.Guest.B1.Main.MainGoalsG

  `main`'s raw-signature loops on an honest run, and its direct DA claim: `MainGoalL3`,
  `MainGoalL4`, `checked_da`.

  The DA witness and `Da.MatrixWitness.Opens` are Benedikt Wagner's LeanDA formalization, as ported here.
-/

module

public import LeanVM.Guest.B1.Main.MainCoverLemmas
public import LeanVM.Guest.B1.Main.RawAt
public import LeanVM.Guest.B1.Main.KidCoverAt
public import LeanVM.Guest.B1.Da.Witness
public import LeanVM.Guest.AcceptableChild

/-!
# `main`'s raw signatures and checked DA claim, honestly

For a statement `s` held by `w` (`NodeRelation`) within the deployed limits (`Limits`), on `main`'s
honest words `hLmain`:

* `rawXD`, `rawSD`: the raw signatures' data (`RawXData`, `RawSData`): raw signature `i` takes
  slot `(slotsOf p)[i]` of its region (`plan_raw`), whose coverage word is `g` to its mark
  (`hMarkX_raw`, `hMarkS_raw`) and whose table entry is its claim;
* `mainGoalL3`, `mainGoalL4`: `main_loop2`, `main_loop3` from the counter `1 = g^0`
  (`rawX_completeAt`, `rawS_completeAt`), the regions below `2^16` by `Limits.coverage`;
* `checked_da`: the checked DA claim's witness opens it, `da_verify`'s returns its cells;
  `wLog_lt`: its padded count's log is below `34` (`da_verify` reads `exponent_tables`' second
  table there; its completeness is `MainGoalsDvTB.mainGoalDvTB`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Coverage (coveragePlan)
open LeanVM.Guest.B1 (CompleteAtD Returns)
open LeanVM.Guest.B1.Da (reads_of_memL exists_of_length_succ wLog)

@[expose] public section

variable {bytecode : List K} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

/-! ## Bounds -/

/-- The coverage table is below `2^23`. -/
theorem regions_lt (hl : GuestLimits s w) : rX s w + rY s w < 2 ^ 23 := by
  have := hl.planSlotsBelow2Pow23
  rw [coverage_eq] at this
  simp only [List.length_append] at this
  simp only [rX, rY]
  omega

/-- The padded count's log is below `34`: at most `LeanDa.maxRows` rows. -/
theorem wLog_lt {x : LeanVM.Da.MatrixWitness} {r : Digest} {v : E} (hw : x.Opens r v) : wLog x < 34 := by
  obtain ⟨h1, h2, -⟩ := hw
  have hb := (Da.nPad_bounds h1).2
  rw [Da.maxRows_eq] at h2
  by_contra hc
  have : 2 ^ 34 ≤ LeanDa.paddedRowCount x.rows.length := by
    unfold LeanDa.paddedRowCount
    exact Nat.pow_le_pow_right (by norm_num) (by unfold wLog at hc; omega)
  omega

/-! ## The raw claims' slots -/

theorem xslot {i : ℕ} (hi : i < (hRawX s w).length) :
    ∃ hk : i < (slotsOf (xPlan s w)).length,
      (s.claims.xmss ++ (xPlan s w).duplicates)[(slotsOf (xPlan s w))[i]]? = some ((hRawX s w)[i]).1 := by
  obtain ⟨hk', hs, e, hc⟩ := plan_raw s.claims.xmss ((hRawX s w).map (·.1))
    (w.children.map (·.statement.claims.xmss)) (k := i) (by simpa using hi)
  rw [← e, List.getElem_map] at hc
  exact ⟨hs, hc⟩

theorem sslot {i : ℕ} (hi : i < (hRawS s w).length) :
    ∃ hk : i < (slotsOf (sPlan s w)).length,
      (s.claims.sphincs ++ (sPlan s w).duplicates)[(slotsOf (sPlan s w))[i]]? = some ((hRawS s w)[i]).1 := by
  obtain ⟨hk', hs, e, hc⟩ := plan_raw s.claims.sphincs ((hRawS s w).map (·.1))
    (w.children.map (·.statement.claims.sphincs)) (k := i) (by simpa using hi)
  rw [← e, List.getElem_map] at hc
  exact ⟨hs, hc⟩

/-! ## The raw leanXMSS signatures -/

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ)

section
variable {fs fp}

theorem xs_lt {i : ℕ} (hi : i < (hRawX s w).length) : (slotsOf (xPlan s w)).getD i 0 < rX s w := by
  obtain ⟨hk, -⟩ := xslot hi
  rw [List.getD_eq_getElem _ _ hk]
  exact slotX_lt s w hk

theorem xs_verify (hn : NodeRelation bytecode seed s w) (d0 : LeanXmssClaim × LeanXmss.Signature) {i : ℕ}
    (hi : i < (hRawX s w).length) :
    LeanXmss.verifyWithKeccak ((hRawX s w).getD i d0).1.1 ((hRawX s w).getD i d0).1.2 ((hRawX s w).getD i d0).2 =
      true := by
  rw [List.getD_eq_getElem _ _ hi]
  exact hn.1.1 _ (List.getElem_mem hi)

theorem xs_cover {rd : Reader} (hL : MemL rd (hLmain fs fp seed s w)) {i : ℕ}
    (hi : i < (hRawX s w).length) :
    LoadHolds rd (gen ^ hPos seed s w fs fp 2) ((slotsOf (xPlan s w)).getD i 0) (gen ^ i) := by
  obtain ⟨hk, -⟩ := xslot hi
  have := coverX_load hL hk
  rw [hMarkX_raw s w hi] at this
  rw [List.getD_eq_getElem _ _ hk]
  exact this

theorem xs_claim {rd : Reader} (hL : MemL rd (hLmain fs fp seed s w))
    (d0 : LeanXmssClaim × LeanXmss.Signature) {i : ℕ} (hi : i < (hRawX s w).length) :
    Sig.ClaimAt rd (gen ^ (hPos seed s w fs fp 0 + 4 * (slotsOf (xPlan s w)).getD i 0))
      (Sig.cellOf128 ((hRawX s w).getD i d0).1.1.root)
      (Sig.cellOf128 ((hRawX s w).getD i d0).1.1.parameter)
      (Sig.cellOf128 (((hRawX s w).getD i d0).1.2.extractLsb' 0 128))
      (Sig.cellOf128 (((hRawX s w).getD i d0).1.2.extractLsb' 128 128)) := by
  obtain ⟨hk, hc⟩ := xslot hi
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hi]
  exact tableX_claim hL hc

theorem xs_regCover {i : ℕ} (hi : i < (hRawX s w).length) :
    RegionL (hLmain fs fp seed s w) (hPos seed s w fs fp 2 + (slotsOf (xPlan s w)).getD i 0) :=
  cover_region (by have := xs_lt hi; omega)

theorem xs_regClaim {i : ℕ} (hi : i < (hRawX s w).length) {k : ℕ} (hk : k < 4) :
    RegionL (hLmain fs fp seed s w) (hPos seed s w fs fp 0 + 4 * (slotsOf (xPlan s w)).getD i 0 + k) :=
  tableX_region (xs_lt hi) hk

end

/-- **The raw leanXMSS signatures' honest data.** -/
def rawXD (hn : NodeRelation bytecode seed s w) (d0 : LeanXmssClaim × LeanXmss.Signature) :
    RawXData (hRawX s w).length (rX s w) (hPos seed s w fs fp 2) (hPos seed s w fs fp 0)
      (hLmain fs fp seed s w) where
  slot i := (slotsOf (xPlan s w)).getD i 0
  pk i := ((hRawX s w).getD i d0).1.1
  msg i := ((hRawX s w).getD i d0).1.2
  sig i := ((hRawX s w).getD i d0).2
  slot_lt _ hi := xs_lt hi
  verify _ hi := xs_verify hn d0 hi
  cover _ _ hL _ hi := xs_cover hL hi
  claim _ _ hL _ hi := xs_claim hL d0 hi
  regCover _ hi := xs_regCover hi
  regClaim _ hi _ hk := xs_regClaim hi hk

/-- **`main_loop2` on an honest run.** -/
theorem mainGoalL3 (hn : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    (hc : Sig.verify_lean_xmss_complete_Spec) : MainGoalL3 fs cert fp seed s w := by
  intro h0
  have hpos : 0 < (hRawX s w).length := Nat.pos_of_ne_zero h0
  have hb := regions_lt hl
  have hnl : (hRawX s w).length ≤ rX s w := xRaw_le hl.toDeployedLimits
  have hX : s.claims.xmss.length ≤ rX s w := Nat.le_add_right _ _
  have h := rawX_completeAt fs cert hc (rawXD fs fp hn (hRawX s w)[0]) (by omega) (by omega) 0 hpos
  rw [pow_zero] at h
  exact h

/-! ## The raw leanSPHINCS signatures -/

section
variable {fs fp}

theorem ss_lt {j : ℕ} (hj : j < (hRawS s w).length) : (slotsOf (sPlan s w)).getD j 0 < rY s w := by
  obtain ⟨hk, -⟩ := sslot hj
  rw [List.getD_eq_getElem _ _ hk]
  exact slotS_lt s w hk

theorem ss_verify (hn : NodeRelation bytecode seed s w) (d0 : LeanSphincsClaim × Sphincs.Signature) {j : ℕ}
    (hj : j < (hRawS s w).length) :
    Sphincs.verifyWithKeccak ((hRawS s w).getD j d0).1.1 ((hRawS s w).getD j d0).1.2 ((hRawS s w).getD j d0).2 =
      true := by
  rw [List.getD_eq_getElem _ _ hj]
  exact hn.1.2.1 _ (List.getElem_mem hj)

theorem ss_cover {rd : Reader} (hL : MemL rd (hLmain fs fp seed s w)) {j : ℕ}
    (hj : j < (hRawS s w).length) :
    LoadHolds rd (gen ^ hPos seed s w fs fp 2) (rX s w + (slotsOf (sPlan s w)).getD j 0)
      (gen ^ ((hRawX s w).length + j)) := by
  obtain ⟨hk, -⟩ := sslot hj
  have := coverS_load hL hk
  rw [hMarkS_raw s w hj] at this
  rw [List.getD_eq_getElem _ _ hk]
  exact this

theorem ss_claim {rd : Reader} (hL : MemL rd (hLmain fs fp seed s w))
    (d0 : LeanSphincsClaim × Sphincs.Signature) {j : ℕ} (hj : j < (hRawS s w).length) :
    Sig.ClaimAt rd (gen ^ (hPos seed s w fs fp 1 + 4 * (slotsOf (sPlan s w)).getD j 0))
      (Sig.cellOf128 ((hRawS s w).getD j d0).1.1.publicSeed)
      (Sig.cellOf128 ((hRawS s w).getD j d0).1.1.root)
      (Sig.cellOf128 (((hRawS s w).getD j d0).1.2.extractLsb' 0 128))
      (Sig.cellOf128 (((hRawS s w).getD j d0).1.2.extractLsb' 128 128)) := by
  obtain ⟨hk, hc⟩ := sslot hj
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hj]
  exact tableS_claim hL hc

theorem ss_regCover {j : ℕ} (hj : j < (hRawS s w).length) :
    RegionL (hLmain fs fp seed s w)
      (hPos seed s w fs fp 2 + (rX s w + (slotsOf (sPlan s w)).getD j 0)) :=
  cover_region (by have := ss_lt hj; omega)

theorem ss_regClaim {j : ℕ} (hj : j < (hRawS s w).length) {k : ℕ} (hk : k < 4) :
    RegionL (hLmain fs fp seed s w) (hPos seed s w fs fp 1 + 4 * (slotsOf (sPlan s w)).getD j 0 + k) :=
  tableS_region (ss_lt hj) hk

end

/-- **The raw leanSPHINCS signatures' honest data.** -/
def rawSD (hn : NodeRelation bytecode seed s w) (d0 : LeanSphincsClaim × Sphincs.Signature) :
    RawSData (hRawS s w).length (rY s w) (rX s w) (hRawX s w).length (hPos seed s w fs fp 2)
      (hPos seed s w fs fp 1) (hPos seed s w fs fp 3) (hLmain fs fp seed s w) where
  slot j := (slotsOf (sPlan s w)).getD j 0
  pk j := ((hRawS s w).getD j d0).1.1
  msg j := ((hRawS s w).getD j d0).1.2
  sig j := ((hRawS s w).getD j d0).2
  slot_lt _ hj := ss_lt hj
  verify _ hj := ss_verify hn d0 hj
  cover _ _ hL _ hj := ss_cover hL hj
  claim _ _ hL _ hj := ss_claim hL d0 hj
  bytes _ _ hL := bytes_hold hL
  regCover _ hj := ss_regCover hj
  regClaim _ hj _ hk := ss_regClaim hj hk
  regBytes _ hv := bytes_region hv

/-- **`main_loop3` on an honest run.** -/
theorem mainGoalL4 (hn : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    (hc : Sig.SphincsCompleteSpecs) : MainGoalL4 fs cert fp seed s w := by
  intro h0
  have hpos : 0 < (hRawS s w).length := Nat.pos_of_ne_zero h0
  have hb := regions_lt hl
  have hnl : (hRawS s w).length ≤ rY s w := sRaw_le hl.toDeployedLimits
  have hY : s.claims.sphincs.length ≤ rY s w := Nat.le_add_right _ _
  have h := rawS_completeAt fs cert hc (rawSD fs fp hn (hRawS s w)[0]) (by omega) (by omega) 0 hpos
  rw [pow_zero, pow_add (a := gen) (hPos seed s w fs fp 2)] at h
  exact h

/-! ## The direct DA claim -/

/-- **The checked DA claim**, when `main` checks one: its witness opens its root and vector
challenge, `da_verify`'s returns its cells. -/
theorem checked_da (hn : NodeRelation bytecode seed s w) (h1 : (hm fs fp seed s w).nd = 1) :
    ∃ p, w.daMatrix = some p ∧ (hm fs fp seed s w).daR = daCells p.1 ∧
      p.2.Opens p.1.daRoot p.1.membershipChallenge := by
  obtain ⟨-, hda, -, -⟩ := hn
  obtain ⟨p, hw⟩ : ∃ p, w.daMatrix = some p := by
    cases hw : w.daMatrix with
    | none => simp [hm, hData, MainData.toIn, hw] at h1
    | some p => exact ⟨p, rfl⟩
  rw [DaDigestHeld, hw] at hda
  exact ⟨p, hw, by simp [hm, hData, MainData.toIn, hw], hda.2⟩

end
end LeanVM.Guest.B1.Main
