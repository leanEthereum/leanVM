/-
  LeanVM.Guest.B1.Place.OsFinalKB

  open_stacked's callees, placed in sequence after its buffers, within their bounds.
-/

module

public import LeanVM.Guest.B1.Place.OsBos
public import LeanVM.Guest.B1.Place.OsMeanB
public import LeanVM.Guest.B1.Place.OsKidsB

/-!
# The callees, placed within their bounds

`OsSpecialsB … Bk`: `OsSpecials` with each special callee within `Bk` of its name.
`os_kids_atB`: `os_kids_at` with the named callees within `Bk` (`OsLeafBounds fs Bk`), the total
at most `osKidsB fs Bk c`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **The callees placed apart, within `Bk` of their names**, at their honest arguments. -/
structure OsSpecialsB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Bk : String → ℕ)
    (c : OsCfg) (tr : OsTr) (b0 : ℕ) (Lin : Layout) : Prop where
  sq : ∀ l < c.levels.length, OsCompleteAtPB fs cert κ (c.sqLoop l)
    (fun p ↦ osLk c tr b0 Lin ++ osW fs cert c b0 l p) (osSqArgs c (osAtOf c b0) l) [] (osS fs cert c tr l)
    (Bk (c.sqLoop l))
  q : ∀ l < c.levels.length, ∀ p, CompleteAtB fs cert κ (osQueriesName l (lvAt c l))
    (osLk c tr b0 Lin ++ osW fs cert c b0 l p ++ osS fs cert c tr l p) (osQArgs c tr (osAtOf c b0) l)
    (Returns [(tr.L l).enforced]) (Bk (osQueriesName l (lvAt c l)))
  res : ∀ l < c.levels.length, CompleteAtB fs cert κ (c.resLoop l) (osLk c tr b0 Lin)
    (osResArgs c tr (osAtOf c b0) l) (Returns []) (Bk (c.resLoop l))

/-- **The callees, placed within their bounds.** -/
theorem os_kids_atB {Bk : String → ℕ} (hT : OsLeafBounds fs Bk) {c : OsCfg} (hN : OsNames c) {tr : OsTr}
    (hlen : tr.Ls.length = c.levels.length) (hfit : TrFit c tr)
    (hpos : ∀ x ∈ osSizesL c, 0 < x) (htot : (osSizesL c).sum < 2 ^ 64 - 1)
    {σ0 : Val} {c0 c2 : E} {b0 : ℕ} {Lin : Layout} (hsp : OsSpecialsB fs cert κ Bk c tr b0 Lin)
    (hall : ∀ rd, LowDef κ rd → MemL rd (osLk c tr b0 Lin) →
      AllOk (osCR rd (osSp c tr (osAtOf c b0)) (OsXOk κ (osLk c tr b0 Lin))) rd
        (osSigma c tr σ0 c0 c2 b0) (osBodyA c))
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 (osLk c tr b0 Lin)) (bk : ℕ) :
    ∃ (N : ℕ) (L : Layout) (ps : List ℕ), ps.length = c.levels.length ∧ Within L bk N ∧ DisjL L ∧ N ≤ osKidsB fs Bk c ∧
      OsKidsOk fs cert κ c tr σ0 c0 c2 b0 Lin L ps bk N := by
  set σ := osSigma c tr σ0 c0 c2 b0 with hσ
  set A := osAtOf c b0 with hA
  set Lk := osLk c tr b0 Lin with hLk
  have hcs := osBodyA_calls σ c
  obtain ⟨cs2, hcs2⟩ : ∃ cs2, cs2 = ((osTail c (osLevels c 0 c.levels (osHead c).2).2).1.filterMap Main.Stmt.callS).map
      (Main.mkCall σ) ++
    ((osFinishA c (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.1
      (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.2).filterMap Main.Stmt.callS).map
      (Main.mkCall σ) := ⟨_, rfl⟩
  rw [← hcs2] at hcs
  have hmem : ∀ c', c' ∈ (osLvKOf σ c 0 c.levels (osHead c).2).flatMap OsLvK.calls ∨ c' ∈ cs2 →
      c' ∈ ((osBodyA c).filterMap Main.Stmt.callS).map (Main.mkCall σ) := fun c' h ↦ by
    rw [hcs, List.mem_append]; exact h
  have hksl : (osLvKOf σ c 0 c.levels (osHead c).2).length = c.levels.length := osLvKOf_length σ c 0 c.levels (osHead c).2
  have hlenS : (osSizesL c).length = 18 + 3 * c.levels.length := osSizesL_length c
  -- the special callees' arguments, by their kinds
  have hspecial : ∀ c' ∈ ((osBodyA c).filterMap Main.Stmt.callS).map (Main.mkCall σ),
      c'.taken = true → osKindOf c'.f = none →
      osSp c tr A c'.f (c'.args.map σ) (c'.rets.map σ) := fun c' hc' ht hK ↦
    os_kid_special hall hex hc' ht hK
  -- the levels
  have hok : ∀ i (h : i < (osLvKOf σ c 0 c.levels (osHead c).2).length), OsLvKOkB fs cert κ σ Lk (osW fs cert c b0 (0 + i))
      (osS fs cert c tr (0 + i)) Bk (osLvKOf σ c 0 c.levels (osHead c).2)[i] := by
    intro i h
    have hi : i < c.levels.length := by rw [← hksl]; exact h
    have hb := hfit.lvb i hi
    have e := osLvKOf_get σ c 0 c.levels (osHead c).2 i hi
    rw [e]
    simp only [Nat.zero_add, lvAt_eq hi]
    have hkA : (osLevelA c i (lvAt c i) (osLevels c 0 (c.levels.take i) (osHead c).2).2).2.1 = osAj c i :=
      rfl
    have hinK : ∀ c' ∈ (osLvKOf σ c 0 c.levels (osHead c).2)[i].calls, c' ∈ ((osBodyA c).filterMap Main.Stmt.callS).map (Main.mkCall σ) :=
      fun c' hc' ↦ hmem c' (Or.inl (List.mem_flatMap.mpr ⟨(osLvKOf σ c 0 c.levels (osHead c).2)[i], List.getElem_mem h, hc'⟩))
    rw [e] at hinK
    simp only [Nat.zero_add, lvAt_eq hi, OsLvK.calls, List.mem_append, List.mem_cons] at hinK
    refine ⟨fun c' hc' ht ↦ ?_, ?_, ?_, fun p c' hc' ht ↦ ?_⟩
    · -- before the squeezes: named callees
      have hf := mem_cnames hc'
      rw [lvA_cnames] at hf
      obtain ⟨K, hK⟩ := lvA_named hN hi hf
      exact os_kid_namedB hT hall hex (hinK c' (Or.inl hc')) ht hK
    · -- the squeeze loop is entered
      simp only [Main.mkCall, sqCallS, decide_eq_true_eq, hkA]
      rw [hσ, osVal_guard hlen hi (t := 2) (by omega)]
      simp only [sqGuardVals, List.getD_cons_succ, List.getD_cons_zero, word_one,
        Whir.gw_eq (show (lvAt c i).squeezes < u128Bound by have := hb.sq5; omega)]
      exact one_add_gen_pow_ne_zero hb.sq0 hb.sqOrd
    · -- the squeeze loop, placed
      have hargs : (Main.mkCall σ (sqCallS c i (osAj c i).k)).args.map σ = osSqArgs c A i := by
        simp only [Main.mkCall, sqCallS, List.map_cons, List.map_nil]
        rw [hσ, osVal_guard hlen hi (t := 3) (by omega), osVal_guard hlen hi (t := 4) (by omega),
          osVal_sqz hlen hi, osVal_qpos, osVal_qbp, osVal_win]
        simp only [sqGuardVals, List.getD_cons_succ, List.getD_cons_zero, word_one,
          Whir.gw_eq (show (lvAt c i).squeezes < u128Bound by have := hb.sq5; omega), osSqArgs]
        rfl
      rw [hkA, hargs]
      exact hsp.sq i hi
    · -- after the squeezes
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc'
      have hin := hinK _ (Or.inr (Or.inr hc'))
      have hfx : (Main.mkCall σ x).f = x.2.1 := by obtain ⟨cv, f, a, r⟩ := x; cases cv <;> rfl
      have hax : (Main.mkCall σ x).args = x.2.2.1 := by obtain ⟨cv, f, a, r⟩ := x; cases cv <;> rfl
      cases hK : osKindOf (Main.mkCall σ x).f with
      | some K =>
        rw [List.append_assoc]
        exact completeAtB_lin_mono (os_kid_namedB hT hall hex hin ht hK)
          fun q hq ↦ List.mem_append_left _ hq
      | none =>
        rw [hfx] at hK
        obtain ⟨hq1, hq5, hq7⟩ := lvB_qcall hN hi hx hK
        obtain ⟨l, hl, hsp'⟩ := hspecial _ hin ht (by rw [hfx]; exact hK)
        have hlen7 : ((Main.mkCall σ x).args.map σ).length = 7 := by rw [List.length_map, hax, hq7]
        rcases hsp' with ⟨-, ha, -⟩ | ⟨hf, ha, hr⟩ | ⟨-, ha, -⟩
        · rw [ha] at hlen7; simp [osSqArgs] at hlen7
        · -- the queries of level `l` are level `i`'s
          have h5 : ((Main.mkCall σ x).args.map σ).getD 5 0 = A.wp i := by
            rw [hax]
            have : (x.2.2.1.map σ).getD 5 0 = σ (x.2.2.1.getD 5 (.n 0)) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
              rcases h5' : x.2.2.1[5]? with _ | v
              · rw [List.getElem?_eq_none_iff] at h5'; omega
              · rfl
            rw [this, hq5, hσ]
            exact osVal_wp hlen hi
          rw [ha] at h5
          simp only [osQArgs, List.getD_cons_succ, List.getD_cons_zero] at h5
          have hil : l = i := by
            have := osPtrAt_inj (c := c) (b := b0) (j := osIxWp l) (j' := osIxWp i)
              (by rw [hlenS]; unfold osIxWp; omega) (by rw [hlenS]; unfold osIxWp; omega) hpos htot h5
            unfold osIxWp at this; omega
          subst hil
          rw [hf, ha, hr]
          exact hsp.q l hl p
        · rw [ha] at hlen7; simp [osResArgs] at hlen7
  obtain ⟨N1, L1, ps, hps, hW1, hD1, hN1, hK1⟩ := os_levels_kidsB κ σ Lk (osW fs cert c b0)
    (osS fs cert c tr) Bk (osLvKOf σ c 0 c.levels (osHead c).2) 0 hok bk
  -- the tail and the finish
  have hc2 : ∀ c' ∈ cs2, c'.taken = true →
      CompleteAtB fs cert κ c'.f Lk (c'.args.map σ) (Returns (c'.rets.map σ)) (Bk c'.f) := by
    intro c' hc' ht
    have hin := hmem c' (Or.inr hc')
    rw [hcs2] at hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · obtain ⟨K, hK⟩ := tail_named (mem_cnames hc')
      exact os_kid_namedB hT hall hex hin ht hK
    · cases hK : osKindOf c'.f with
      | some K => exact os_kid_namedB hT hall hex hin ht hK
      | none =>
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc'
        have hfx : (Main.mkCall σ x).f = x.2.1 := by obtain ⟨cv, f, a, r⟩ := x; cases cv <;> rfl
        have hax : (Main.mkCall σ x).args = x.2.2.1 := by obtain ⟨cv, f, a, r⟩ := x; cases cv <;> rfl
        obtain ⟨⟨j, hj, hnm⟩, h6⟩ := finish_rescall hN hx (by rw [← hfx]; exact hK)
        obtain ⟨l, hl, hsp'⟩ := hspecial _ hin ht hK
        have hlen6 : ((Main.mkCall σ x).args.map σ).length = 6 := by rw [List.length_map, hax, h6]
        rcases hsp' with ⟨hf, -, -⟩ | ⟨-, ha, -⟩ | ⟨hf, ha, hr⟩
        · rw [hfx, hnm] at hf; exact absurd hf.symm (hN.sqres l hl j hj)
        · rw [ha] at hlen6; simp [osQArgs] at hlen6
        · rw [hf, ha, hr]; exact hsp.res l hl
  obtain ⟨N2, L2, hW2, hD2, hN2, hK2⟩ := os_kids_blockB κ Lk σ cs2 Bk hc2 (bk + N1)
  refine ⟨N1 + N2, L1 ++ L2, ps, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hps, hksl]
  · rw [within_append]
    exact ⟨hW1.mono le_rfl (by omega), hW2.mono (by omega) (by omega)⟩
  · exact disj_append hD1 hD2 hW1 hW2 le_rfl
  · have e := osBodyCalls_sumB fs Bk σ c
    rw [osBodyCalls_eq, hcs, List.map_append, List.sum_append] at e
    unfold osCallB at e
    omega
  · intro rd R Dacc hl hL hLk hWm hR hRW
    have hL12 : MemL rd L1 ∧ MemL rd L2 := Main.memL_append.mp hL
    rw [osBodyCalls_eq, hcs]
    refine kidsFromIn_append _ _ Dacc bk N1 N2 (fun _ ↦ False) (fun _ ↦ False) ?_ fun Dacc' _ ↦ ?_
    · exact hK1 rd R Dacc hl hL12.1 hLk (fun i h ↦ by simpa using hWm i (by rw [hps] at h ⊢; exact h)) hR
        (fun l h1 h2 p i hi ↦ hRW l (by rw [hksl] at h2; omega) p i hi)
    · exact hK2 rd R Dacc' hl hL12.2 hLk fun i hi ↦ Or.inl (hR i hi)


end
end LeanVM.Guest.B1
