/-
  LeanVM.Guest.B1.Place.OsKidsOT

  `os_levels_kidsO` and `os_kids_blockO` with, within each bound, the calls by trees of predicates of the memory.
-/

module

public import LeanVM.Guest.B1.Place.OsKidsO
public import LeanVM.Guest.B1.Place.OsKidsBT

/-!
# The levels' callees at an optional bound, with tree predicates

* `bdT Bd T rd`: `T rd` within every bound of `Bd` (no constraint without one); `lvTB Bd TB l` so for level `l`;
* `OsLvKOkOT`: `OsLvKOkO`, and within each bound `Bk` the calls before the positions by trees of `TA rd`, the
  positions' by one of `TS rd`, the calls after them by trees of `TB rd` (`OsLvKOkBT`);
* `os_levels_kidsOT`: `os_levels_kidsO` by trees of `lvTs (bdT Bd TA) (bdT Bd TS) (lvTB Bd TB)`;
* `os_kids_blockOT`: `os_kids_blockO` by trees of `bdT Bd T`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- `OsLvKOkO`, and within each bound the calls before the positions by trees of `TA rd`, the positions' by one of
`TS rd`, the calls after them by trees of `TB rd`. -/
structure OsLvKOkOT (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (σ : Val) (Lk : Layout)
    (W S : ℕ → Layout) (Bd : Option (String → ℕ)) (TA TS TB : Reader → Tree → Prop) (k : OsLvK) : Prop
    extends OsLvKOkO fs cert κ σ Lk W S Bd k where
  AT : ∀ Bk ∈ Bd, ∀ c ∈ k.A, c.taken = true →
    CompleteAtDTBR fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) TA (Bk c.f)
  sqT : ∀ Bk ∈ Bd, OsCompleteAtPBT fs cert κ k.sq.f (fun p => Lk ++ W p) (k.sq.args.map σ) (k.sq.rets.map σ) S TS
    (Bk k.sq.f)
  BT : ∀ Bk ∈ Bd, ∀ p, ∀ c ∈ k.B, c.taken = true →
    CompleteAtDTBR fs cert κ c.f (Lk ++ W p ++ S p) (c.args.map σ) (Returns (c.rets.map σ)) TB (Bk c.f)

/-- A predicate within every bound of `Bd`. -/
def bdT (Bd : Option (String → ℕ)) (T : Reader → Tree → Prop) (rd : Reader) (t : Tree) : Prop :=
  ∀ Bk ∈ Bd, T rd t

/-- Level `l`'s predicate within every bound of `Bd`. -/
def lvTB (Bd : Option (String → ℕ)) (TB : ℕ → Reader → Tree → Prop) (l : ℕ) (rd : Reader) (t : Tree) : Prop :=
  ∀ Bk ∈ Bd, TB l rd t

theorem lvTs_all {TA TS : Reader → Tree → Prop} {TB : ℕ → Reader → Tree → Prop} {rd : Reader}
    (hA : ∀ t, TA rd t) (hS : ∀ t, TS rd t) (h : ∀ l t, TB l rd t) :
    ∀ (l : ℕ) (ks : List OsLvK), ∀ T ∈ lvTs TA TS TB rd l ks, ∀ t, T t
  | _, [] => fun _ h' => by simp [lvTs] at h'
  | l, k :: ks => fun T hT t => by
    simp only [lvTs, List.mem_append, List.mem_map, List.mem_cons] at hT
    rcases hT with (⟨_, -, rfl⟩ | rfl | ⟨_, -, rfl⟩) | hT
    · exact hA t
    · exact hS t
    · exact h l t
    · exact lvTs_all hA hS h (l + 1) ks T hT t

/-- **The levels' callees at an optional bound, by trees of `lvTs (bdT Bd TA) (bdT Bd TS) (lvTB Bd TB)`.** -/
theorem os_levels_kidsOT (σ : Val) (Lk : Layout) (W S : ℕ → ℕ → Layout) (Bd : Option (String → ℕ))
    (TA TS : Reader → Tree → Prop) (TB : ℕ → Reader → Tree → Prop) (ks : List OsLvK) (l0 : ℕ)
    (hok : ∀ i (h : i < ks.length), OsLvKOkOT fs cert κ σ Lk (W (l0 + i)) (S (l0 + i)) Bd TA TS (TB (l0 + i)) ks[i])
    (b : ℕ) :
    ∃ (N : ℕ) (L : Layout) (ps : List ℕ), ps.length = ks.length ∧ Within L b N ∧ DisjL L ∧
      (∀ Bk ∈ Bd, N ≤ ((ks.flatMap OsLvK.calls).map fun c => max (fs c.f) (Bk c.f)).sum) ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd L → MemL rd Lk →
        (∀ i (h : i < ps.length), MemL rd (W (l0 + i) ps[i])) → (∀ i, RegionL Lk i → R i) →
        (∀ l, l0 ≤ l → l < l0 + ks.length → ∀ p i, RegionL (W l p) i → R i) →
        KidsFromInT coreProgram fs cert rd σ R Dacc (ks.flatMap OsLvK.calls)
          (lvTs (bdT Bd TA) (bdT Bd TS) (lvTB Bd TB) rd l0 ks) b N (fun _ => False) := by
  cases Bd with
  | none =>
    obtain ⟨N, L, ps, hps, hW, hD, hN, hK⟩ := os_levels_kidsO (fs := fs) (cert := cert) (κ := κ) σ Lk W S none ks l0
      (fun i h ↦ (hok i h).toOsLvKOkO) b
    exact ⟨N, L, ps, hps, hW, hD, hN, fun rd R Dacc hlow hL hLk hWm hR hRW ↦ kidsFromIn_toT _
      (lvTs_all (fun _ Bk h ↦ absurd h (by simp)) (fun _ Bk h ↦ absurd h (by simp))
        (fun _ _ Bk h ↦ absurd h (by simp)) l0 ks) (hK rd R Dacc hlow hL hLk hWm hR hRW)⟩
  | some Bk =>
    obtain ⟨N, L, ps, hps, hW, hD, hN, hK⟩ := os_levels_kidsBT (fs := fs) (cert := cert) κ σ Lk W S Bk
      (bdT (some Bk) TA) (bdT (some Bk) TS) (lvTB (some Bk) TB) ks l0 (fun i h ↦ let o := hok i h
        ⟨fun c hc ht ↦ (o.AT Bk rfl c hc ht).mono le_rfl fun _ _ h' _ _ ↦ h', o.taken,
          (o.sqT Bk rfl).mono le_rfl fun _ _ h' _ _ ↦ h',
          fun p c hc ht ↦ (o.BT Bk rfl p c hc ht).mono le_rfl fun _ _ h' _ _ ↦ h'⟩) b
    exact ⟨N, L, ps, hps, hW, hD, fun B h ↦ by simp only [Option.mem_def, Option.some.injEq] at h; subst h; exact hN,
      hK⟩

/-- **Calls complete on fixed words at an optional bound, within each bound by trees of `T rd`**, placed from `b`. -/
theorem os_kids_blockOT (Lk : Layout) (σ : Val) (cs : List Call) (Bd : Option (String → ℕ))
    (T : Reader → Tree → Prop)
    (hc : ∀ c ∈ cs, c.taken = true →
      CompleteAtO fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) (Bd.map (· c.f)))
    (hcT : ∀ Bk ∈ Bd, ∀ c ∈ cs, c.taken = true →
      CompleteAtDTBR fs cert κ c.f Lk (c.args.map σ) (Returns (c.rets.map σ)) T (Bk c.f))
    (b : ℕ) :
    ∃ (N : ℕ) (L : Layout), Within L b N ∧ DisjL L ∧
      (∀ Bk ∈ Bd, N ≤ (cs.map fun c => max (fs c.f) (Bk c.f)).sum) ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd →
      MemL rd L → MemL rd Lk → (∀ i, RegionL Lk i → R i ∨ Dacc i) →
      KidsFromInT coreProgram fs cert rd σ R Dacc cs (cs.map fun _ => bdT Bd T rd) b N (fun _ => False) := by
  cases Bd with
  | none =>
    obtain ⟨N, L, hW, hD, hN, hK⟩ := os_kids_blockO (fs := fs) (cert := cert) (κ := κ) Lk σ cs none hc b
    exact ⟨N, L, hW, hD, hN, fun rd R Dacc hlow hL hLk hR ↦ kidsFromIn_toT _
      (fun _ hT _ ↦ by obtain ⟨_, -, rfl⟩ := List.mem_map.mp hT; exact fun _ h ↦ absurd h (by simp))
      (hK rd R Dacc hlow hL hLk hR)⟩
  | some Bk =>
    obtain ⟨N, L, hW, hD, hN, hK⟩ := os_kids_blockBT (fs := fs) (cert := cert) κ Lk σ cs Bk (bdT (some Bk) T)
      (fun c hc' ht ↦ (hcT Bk rfl c hc' ht).mono le_rfl fun _ _ h' _ _ ↦ h') b
    exact ⟨N, L, hW, hD, fun B h ↦ by simp only [Option.mem_def, Option.some.injEq] at h; subst h; exact hN, hK⟩

end
end LeanVM.Guest.B1
