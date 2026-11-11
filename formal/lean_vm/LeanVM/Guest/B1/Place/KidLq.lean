/-
  LeanVM.Guest.B1.Place.KidLq

  open_stacked's `level_queries` calls placed, from their placed statement.
-/

module

public import LeanVM.Guest.B1.Place.KidLp
public import LeanVM.Guest.B1.Bits.QueryWindowsHonest

/-!
# `level_queries`' calls, placed

`os_lq_kid`: level `l`'s `level_queries` call, at its honest arguments (`osLqArgs`), on the
callees' words, the level's window pointers and its decoders' runs (`level_positions` entered at
`p`), returns the root, the enforced sum and `λ^q`: `CompleteAtO`, from `LqAtO` and the level's
honest data (`LvHelperFacts.queries`). Query `k`'s windows are in decoder `k / (192/d)`'s run, at
position `k % (192/d)`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {c : OsCfg} {tr : OsTr} {b0 : ℕ}
  {Lin : Layout}

/-- Query `k`'s windows' cell, its `level_positions` entered at `p`. -/
def osEb (cert : String → V → ℕ) (c : OsCfg) (D : ℕ → ℕ → ℕ → ℕ) (l p k : ℕ) : ℕ :=
  D l p (k / (192 / (lvAt c l).depth)) + cert (osDecName c l) (.n 5) +
    k % (192 / (lvAt c l).depth) * qwN (lvAt c l).depth (lvAt c l).capDepth

theorem mod_mul_add_lt {k per N i : ℕ} (hper : 0 < per) (hi : i < N) :
    k % per * N + i < per * N := by
  have h1 : (k % per + 1) * N ≤ per * N := Nat.mul_le_mul_right _ (Nat.mod_lt _ hper)
  rw [Nat.add_mul, Nat.one_mul] at h1; omega

/-- **Level `l`'s `level_queries` call, placed**, its `level_positions` entered at `p`. -/
theorem os_lq_kid (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap)
    (htl : tr.Lf.ml ≤ yrLogCap) {l : ℕ} (hl : l < c.levels.length)
    (hper : 0 < 192 / (lvAt c l).depth)
    (hqs : (lvAt c l).queries ≤ (lvAt c l).squeezes * (192 / (lvAt c l).depth))
    (hcd : (lvAt c l).capDepth ≤ (lvAt c l).depth)
    (hil : rowLo (lvAt c l).interleave + (lvAt c l).interleave / rowLo (lvAt c l).interleave ≤
      c.maxIl)
    (hH : LvHelperFacts c tr l) {name : String} {Bd : Option ℕ} {D : ℕ → ℕ → ℕ → ℕ} {leaf : ℕ}
    (hlq : LqAtO fs cert κ name (lvAt c l).queries (lvBase l) (lvAt c l).interleave leaf
      (lvAt c l).depth (lvAt c l).capDepth Bd) (hB : BoundsAt fs name Bd) (p : ℕ) :
    CompleteAtO fs cert κ name (osLk c tr b0 Lin ++ osW cert c D b0 l p ++ osS cert c tr D l p)
      (osLqArgs c tr (osAtOf c b0) l) (Returns (osLqRets c tr l)) Bd := by
  obtain ⟨capW, flW, qs, rows, sibs, hcaps, hqd, hen⟩ := hH.queries
  set per := 192 / (lvAt c l).depth
  set d := (lvAt c l).depth
  set cd := (lvAt c l).capDepth
  set s := lqShape (lvBase l) (lvAt c l).interleave d cd
  have hs1 : s.pd + s.cd = d := by simp only [s, lqShape]; omega
  have hlo : s.lo + s.I / s.lo ≤ c.maxIl := hil
  set eqp := osBase c b0 6 + (lvAt c l).posOff
  set ewp := osBase c b0 (osIxWp l)
  have hargs : osLqArgs c tr (osAtOf c b0) l =
      [(tr.L l).lam, ofK (addressOfIndex eqp), ofK (addressOfIndex ewp)] := by
    simp only [osLqArgs, eqp, ewp]
    rw [show (osAtOf c b0).P.qbp = ofK (addressOfIndex (osBase c b0 6)) from rfl, ofK_addr_mul_gen]
    rfl
  have hrets : osLqRets c tr l = [(digestHalves (tr.L l).root).1, (digestHalves (tr.L l).root).2,
      oqChain ((lvAt c l).queries % 2 * lvBase l) (lvBase l) (tr.L l).lam⁻¹
        (fun k ↦ rowDot (lvBase l) (lvAt c l).interleave (rows k) fun i ↦ (wpC c tr l).getD i 0)
        (lqIters (lvAt c l).queries (lvBase l)) * (tr.L l).lam ^ (lvAt c l).queries,
      (tr.L l).lam ^ (lvAt c l).queries] := by
    simp only [osLqRets]; rw [hen]
  rw [hargs, hrets]
  -- the entries
  have hwpE := osLk_entry (b0 := b0) (Lin := Lin) (j := osIxWp l) (by unfold osIxWp; omega)
    (by unfold osIxWp; omega) hpt htl
  rw [osOwnL_getD_lv c tr _ hl] at hwpE
  have hWE : (eqp, (List.range ((lvAt c l).squeezes * per)).map fun k ↦
      osBp cert c D (fun _ ↦ p) l (k / per) * gen ^ ((k % per) * qwN d cd)) ∈
        osLk c tr b0 Lin ++ osW cert c D b0 l p ++ osS cert c tr D l p :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  have hSE : ∀ k < (lvAt c l).queries,
      (D l p (k / per) + cert (osDecName c l) (.n 5), qwRunList d cd (sqChal (tr.L l).F2.cap (k / per))) ∈
        osLk c tr b0 Lin ++ osW cert c D b0 l p ++ osS cert c tr D l p := fun k hk ↦ by
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨k / per, ?_, List.mem_singleton_self _⟩)
    rw [List.mem_range]
    exact (Nat.div_lt_iff_lt_mul hper).mpr (by omega)
  have hrunlen : ∀ w, (qwRunList d cd w).length = per * qwN d cd := fun w ↦ by
    simp only [qwRunList, List.length_map, List.length_range]; rfl
  refine hlq _ eqp ewp (tr.L l).lam (fun i ↦ (wpC c tr l).getD i 0) (osEb cert c D l p) qs rows sibs
    capW flW _ _ hH.lam hcaps ⟨fun i hi ↦ ?_, fun k hk ↦ ⟨?_, fun i hi ↦ ?_⟩⟩
    (fun rd hl' hm ↦ ⟨fun i hi ↦ ?_, fun k hk ↦ ⟨?_, fun i hi ↦ ?_⟩⟩) hB
  · have hwl : (wpC c tr l).length = c.maxIl := by simp [wpC]
    exact regionL_entry (List.mem_append_left _ (List.mem_append_left _ hwpE))
      (by rw [hwl]; exact lt_of_lt_of_le hi hlo)
  · exact regionL_entry hWE (by simp only [List.length_map, List.length_range]; omega)
  · rw [hs1] at hi
    have h := regionL_entry (hSE k hk) (k := k % per * qwN d cd + i)
      (by rw [hrunlen]; exact mod_mul_add_lt hper hi)
    have e : osEb cert c D l p k + i =
        D l p (k / per) + cert (osDecName c l) (.n 5) + (k % per * qwN d cd + i) :=
      Nat.add_assoc _ _ _
    rw [e]; exact h
  · have hwl : (wpC c tr l).length = c.maxIl := by simp [wpC]
    exact readsAt_getD (hm _ (List.mem_append_left _ (List.mem_append_left _ hwpE)))
      (by rw [hwl]; exact lt_of_lt_of_le hi hlo)
  · have h := hm _ hWE
    have h2 := readsAt_map_range h (k := k) (by omega)
    rw [show osBp cert c D (fun _ ↦ p) l (k / per) * gen ^ (k % per * qwN d cd) =
      ofK (addressOfIndex (osEb cert c D l p k)) by unfold osBp osEb; rw [ofK_addr_mul_gen]] at h2
    exact h2
  · rw [hs1] at hi
    have hs2 : (lqShape (lvBase l) (lvAt c l).interleave d cd).pd +
        (lqShape (lvBase l) (lvAt c l).interleave d cd).cd = d := hs1
    rw [hs2]
    change LoadHolds rd _ i (gen ^ qwVal d cd (qs k) i)
    have h := hm _ (hSE k hk)
    have h2 := h (k % per * qwN d cd + i) (by rw [hrunlen]; exact mod_mul_add_lt hper hi)
    simp only [qwRunList, List.getElem_map, List.getElem_range] at h2
    rw [qwRunW_at (cd := cd) _ (show i < qwN d cd from hi), ← hqd k hk] at h2
    change LoadHolds rd (ofK (addressOfIndex ((D l p (k / per) + cert (osDecName c l) (.n 5)) +
      k % per * qwN d cd))) i _
    rw [← ofK_addr_mul_gen, loadHolds_mul_gen_pow]
    exact h2

end
end LeanVM.Guest.B1
