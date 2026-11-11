/-
  LeanVM.Guest.WalkOs

  `open_stacked`'s cut obligations (`CutsKnown`): at each level's dispatch into `level_queries`,
  at each rate's arm, the callee's windows (`lqTag`) on its window pointers, from the level's
  dispatch into `level_positions` at that arm.
-/

module

public import LeanVM.Guest.WalkLq
public import LeanVM.Guest.WalkOsPre
public import LeanVM.Guest.B1.Bits.QueryWindowsAll

/-!
# `open_stacked`'s walk obligations

Checker K cuts `open_stacked__L{m}` before each level's dispatch into `level_queries`; the cut hands
on, for each rate's arm `r`, `selTag (lqTag n odd base d cd) r` on the cells of the window pointers
and of the rate's selector: `level_queries`' windows at `g^n`, if the selector is `g^r`. `osOk`
(`WalkOsDefs`) checks each tuple against a witness: the level's dispatch into `level_positions`
before the cut, whose arm `r` (the same selector) is a specialization of `lpTab` covering the walk,
on window pointers in the tuple's cell, and the window table the body writes before it.
`os_cutsKnown`: `CutsKnown j` from that check (`lp_sound`). The instances are `WalkOsN.lean`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir LeanVM.Guest.Value

@[expose] public section

/-- A tag below `2^31` is its plain relation. -/
theorem semRel_lt31 {t : ℕ} (ht : t < 2 ^ 31) (rd : Reader) (ws : List E) :
    SemRel glob t rd ws ↔ SemRel0 glob t rd ws := by
  unfold SemRel
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- A tag conditional on a dispatch's arm `r`: the relation of its tag on the words but the last,
if the last is `g^r`'s. -/
theorem semRel_sel {t r : ℕ} (ht : t < 2 ^ 26) (hr : r < 32) (rd : Reader) (ws : List E) :
    SemRel glob (selTag t r) rd ws ↔
      (ws.getLast? = some (ofK (addressOfIndex r)) → SemRel0 glob t rd ws.dropLast) := by
  obtain ⟨h1, h2, hb, ha⟩ := selTag_decode ht hr
  unfold SemRel
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2), hb, ha]

theorem getD_mapV {σ : Val} {l : List V} {i : ℕ} (h : i < l.length) :
    (l.map σ).getD i 0 = σ (l.getD i (.n 0)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

/-- **A tuple `osTupOk` accepts holds**: at arm `r`, the windows `level_positions`' arm `r`
decodes on the dispatch's window pointers, in the tuple's cell. -/
theorem os_tup {κ : ℕ} {L : MemoryImage κ} (hκ : κ ≤ 32) {fp : K} {C : Cert} {body : List Stmt}
    {start : ℕ} {lp : List (String × ℕ × ℕ × ℕ × String)} (hlp : ∀ e ∈ lp, LpOk e)
    (hall : ∀ s ∈ body.take start, StmtOkD (coreProgram.Rel L.read) L.read (valG L fp C) s)
    (hwt : WinTabs L.read (valG L fp C (.n osWin))) {w : ℕ × ℕ} {t : ℕ × List ℕ}
    (hw' : osTupOk lp C body start w t = true) : SemRel glob t.1 L.read (t.2.map (wd L fp)) := by
  obtain ⟨pP, wv⟩ := w
  obtain ⟨tg, cells⟩ := t
  unfold osTupOk at hw'
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, Nat.ble_eq, Bool.or_eq_true, and_assoc] at hw'
  obtain ⟨ht1, hr4, hk2, ho2, hcd, hd, hn, hob, rfl, hpP, hdisp⟩ := hw'
  generalize lqN (selBase tg) = n at ht1 hn hdisp
  generalize walkOdd (lqWalk (selBase tg)) = odd at ht1 ho2 hob hdisp
  generalize walkD (lqWalk (selBase tg)) = d at ht1 hd hdisp
  generalize walkCd (lqWalk (selBase tg)) = cd at ht1 hcd hdisp
  have hk4 : walkKind (lqWalk (selBase tg)) < 4 := by unfold walkKind; omega
  generalize hbase : walkKind (lqWalk (selBase tg)) - 2 = base at ht1 hob hdisp
  generalize selArm tg = r at ht1 hr4 hdisp
  have hb2 : base < 2 := by omega
  have hodd : odd = 1 → base = 1 := fun h1 ↦ by rcases hob with h | h <;> omega
  subst ht1
  have hlq : lqTag n odd base d cd < 2 ^ 26 := by
    have := walkTag_lt (kind := 2 + base) (by omega) ho2 hcd hd
    unfold lqTag; omega
  rw [semRel_sel hlq (by omega)]
  intro hsel
  simp only [List.map_cons, List.map_nil, List.getLast?_cons_cons, List.getLast?_singleton,
    Option.some.injEq, List.dropLast_cons_cons, List.dropLast_singleton] at hsel ⊢
  rw [(semRel_lt31 (by omega) _ _).symm, semRel_lq ho2 hb2 hcd hd hn]
  simp only [List.getD_cons_zero]
  rw [← valG_n L fp C 0] at hsel
  rw [← valG_n L fp C wv]
  split at hdisp
  · next x names args rets heq =>
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, List.any_eq_true, and_assoc] at hdisp
    obtain ⟨rfl, hnl, hal, h7, h6, e, he, he1, he2, he3, hcov⟩ := hdisp
    have hd0 := okAt hall hpP
    rw [heq] at hd0
    obtain ⟨e', he', hx, hrel⟩ := hd0
    have hrr : e' = r := by
      rw [hx, ← Value.gen_pow_eq_ofK, ← Value.gen_pow_eq_ofK] at hsel
      exact gen_pow_inj (by omega) (by omega) hsel
    subst hrr
    have hname : names[e']'he' = e.1 := by rw [he1, List.getD_eq_getElem _ _ he']
    rw [hname] at hrel
    have hlen : (args.map (valG L fp C)).length = 8 := by simpa using hal
    have hwt' : WinTabs L.read ((args.map (valG L fp C)).getD 7 0) := by
      rw [getD_mapV (by omega), h7]; exact hwt
    have := lp_sound hκ L (hlp e he) hodd (by rw [he2, he3]; exact hcov) hlen hwt' hrel
    rw [getD_mapV (by omega), h6, he2, he3] at this
    exact this
  · simp at hdisp

/-- **`open_stacked`'s cut obligations**, from its certificate's check against the core IR and
the table of `level_positions`' specializations. -/
theorem os_cutsKnown {j : ℕ} {lp : List (String × ℕ × ℕ × ℕ × String)}
    {W : List (ℕ × ℕ)} {hw : ℕ} (hlp : ∀ e ∈ lp, LpOk e)
    (hok : osOk lp j W hw = true) : CutsKnown j := by
  intro κ L _ h32 fp _ _ i hi h0 hl
  have hc := List.all_eq_true.mp hok _ (cutAt_mem hi h0)
  simp only [osCutOk, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, Bool.or_eq_true,
    Nat.ble_eq] at hc
  obtain ⟨⟨⟨⟨hkn, hki⟩, hflat⟩, htab⟩, hsm⟩ := hc
  refine ⟨by rw [hkn]; intro _ h; simp at h, by rw [hki]; intro _ h; simp at h, fun t ht ↦ ?_⟩
  have hall := (holdsList_flatD _ (List.all_eq_true.mpr hflat) _ _ hl).1
  have htab' : hw + osWinTabs.length ≤ ((certOf j).cutAt i).start ∧
      stmtsEqb (((coreOf j).body.drop hw).take osWinTabs.length) osWinTabs = true := by
    rcases htab with h | h
    · rw [h] at ht; simp at ht
    · exact h
  obtain ⟨w, -, hw'⟩ := List.any_eq_true.mp (hsm t ht)
  exact os_tup (by unfold maxLogMem at h32; omega) hlp hall (winTabs_of_body hall htab'.1 htab'.2) hw'

end
end LeanVM.Guest.End
