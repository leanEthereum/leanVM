/-
  LeanVM.Guest.B1.Opening.QueriesPlacedP

  `walk_path`, a level-0 iteration of `opening_queries`' loop and the loop, placed with their pops (`RelAtInP`): the honest rows and children, query by query.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced6
public import LeanVM.Guest.B1.Opening.QueriesPops
public import LeanVM.Guest.B1.Main.RelAtInP

/-!
# The opening's walks and level-0 loop, placed with their pops

The proofs are `QueriesPlaced4`'s and `QueriesPlaced6`'s with `relAtInP_of_walk`, `relAtInP_of_walk_loop` and `KidsFromInP`, the bodies' pops from `WalkPops` and `QueriesPops` (`splice_of_body`).

* `QD.rowPop_vals`: at the honest values a query's row entry is its row's cells (`QD.rowVals`);
* `wp_relAtInP`: an honest `walk_path` frame pops its children (`WD.wpPops`);
* `oqIt1Pops`, `oqIter1_relAtInP`: a level-0 iteration pops its two queries' rows and walks' children, then its tail's entries;
* `oqLoop1_relAtInP`: the level-0 loop pops its iterations', in order.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **At the honest values a query's row entry is its row's cells.** -/
theorem QD.rowPop_vals (d : QD) {σ : Val} (hv : d.Hv σ) : rowPop σ d.b d.s.I = ("merkle_leaf_rows", d.rowVals) := by
  have he := d.ch_lt_e
  have hI : d.b + d.s.I ≤ d.ch := by simp only [QD.ch, oqCh, oqKL, oqK1]; split_ifs <;> omega
  rw [rowPop, QD.rowVals]
  congr 1
  exact List.map_congr_left fun j hj => by
    have := List.mem_range.mp hj
    rw [hv _ (by omega) (by omega), d.val_row this]

/-- **An honest `walk_path` frame, placed, with its pops**: its path's children. -/
theorem wp_relAtInP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ) {w : WD}
    (hpd : 1 ≤ w.pd) (hcd : 1 ≤ w.cd) (hsl : w.sibs.length = w.pd) (hq : w.q < 2 ^ (w.pd + w.cd))
    {rd : Reader} (hm : w.MemOk rd) {wlk : String} (hW : WalkFn coreProgram wlk w.pd w.cd) {R : ℕ → Prop}
    (hreg : OqWReg R w.pd w.cd w.capv w.flagsv w.bpv w.q) (fp : ℕ) :
    RelAtInP coreProgram fs cert rd R (fun _ => False) fp (fs wlk) wlk
      [(digestHalves w.leaf).1, (digestHalves w.leaf).2, w.bpv, w.capv, w.flagsv] [] w.wpPops := by
  obtain ⟨fn, hf, hp, hb⟩ := hW
  set σ : Val := fun v ↦ w.val v.idx with hσ
  have hv : w.Hv σ := fun _ ↦ rfl
  set pre := oqPathT w.s (.n 2) (wpPr w.s) 0 wpCh ++ oqCapT w.s (.n 2) (.n 3) (.n 4) 0 wpCh with hpre
  have hok := wp_atoms_ok w.s
  have hA : BlockOkC anyCall rd σ pre :=
    blockOkC_of_blockOk (w.walk_block hpd hcd hsl hq hv hm)
  have hfm : pre.all Stmt.flatM = true := hok.flatM
  have hbody : fn.body = pre ++ [.ret []] := by rw [hb, hpre]; exact wpBodyT_eq w.s
  set es := pre.flatMap (fmEvs σ) with hes
  have hw : walk σ fn.body = .ret es [] := by rw [hbody]; exact walk_flatM σ [] pre hfm (hok.matchOk hA)
  obtain ⟨i1, i2, i3, i4⟩ := flatM_parts σ pre hfm
  have hal : pre.filterMap Stmt.allocSz = [] := hok.allocSz
  have hallocs : allocs σ es = [] := by rw [i2, hal]; rfl
  have hcalls : calls es = [] := by
    rw [i4, callS_flat (flat_append (oqPathT_flat _ _ _ _ _) (flat_of_atoms (oqCapT_atoms _ _ _ _ _ _)))]
    rfl
  have hps : splice rd σ es [] = w.wpPops := by
    rw [splice_of_body hbody (SplicePops.of_fallPops (w.wp_fallPops hv))
      (show walk σ [.ret []] = .ret [] [] by simp [walk, walk1, Out.seq]) rfl hw]
    simp [evPops]
  have h := relAtInP_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) hP
    (R := R) (D := fun _ => False) (Dk := fun _ => False) (fp := fp) (N := 0)
    (args := [(digestHalves w.leaf).1, (digestHalves w.leaf).2, w.bpv, w.capv, w.flagsv]) (rets := [])
    hf (Or.inr hcalls) (by rw [hp]; rfl) hw rfl (hok.evs_holds hA)
    (by rw [i1, hal, hallocs]; rfl) (fun q hq ↦ ?_)
    (by rw [hcalls, KidsFromInP]; exact ⟨rfl, fun _ h ↦ h⟩) (fun A hAl ↦ ?_) (fun _ h ↦ h.elim) hps
  · rw [hallocs, List.sum_nil, Nat.add_zero, Nat.add_zero] at h; exact h
  · rw [i3, hok.addrS] at hq
    simp at hq
  · rw [loadAddrs_flatM σ pre hfm] at hAl
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hAl
    obtain ⟨i, hi, hr⟩ := oqWLoad_in hv hreg (hok.load hq)
    exact ⟨i, hi, Or.inr (Or.inl hr)⟩

/-- **A level-0 iteration's entries**: its two queries' rows and walks' children. -/
def oqIt1Pops (s : Oq) (cap flags : E) (rounds : List FoldRound) (hsv : List E) (w1 w2 : QW) (bp1 bp2 : E) :
    List Pop :=
  ("merkle_leaf_rows", (oqQD s 16 true 0 cap flags rounds hsv w1).rowVals) ::
    ((oqQD s 16 true 0 cap flags rounds hsv w1).wd bp1).wpPops ++
  ("merkle_leaf_rows", (oqQD s (oqE1 s + 2) false (oqK1 s 16) cap flags rounds hsv w2).rowVals) ::
    ((oqQD s (oqE1 s + 2) false (oqK1 s 16) cap flags rounds hsv w2).wd bp2).wpPops

/-- **A level-0 iteration, placed, with its pops**: its queries' (`oqIt1Pops`), then its tail's `kn` (`[]` after
the last). -/
theorem oqIter1_relAtInP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) {odd : ℕ}
    {wlk loop : String} (hW : WalkFn coreProgram wlk s.pd s.cd) {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd wlk loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp c Bt m j : ℕ} {N positions qptrs cap flags coefs hsp ch mu : E}
    {rounds : List FoldRound} {hsv : List E} {w1 w2 : QW} {bp1 bp2 v : E} {kn : List Pop}
    (hok1 : (oqQD s 16 true 0 cap flags rounds hsv w1).Ok rd coefs hsp bp1)
    (hok2 : (oqQD s (oqE1 s + 2) false (oqK1 s 16) cap flags rounds hsv w2).Ok rd coefs hsp bp2)
    (hx1 : LoadHolds rd positions (2 * j + odd) (eOfNat w1.1))
    (hx2 : LoadHolds rd positions (2 * j + odd + 1) (eOfNat w2.1))
    (hb1 : LoadHolds rd qptrs (2 * j + odd) bp1) (hb2 : LoadHolds rd qptrs (2 * j + odd + 1) bp2)
    (hv : s.final ≠ 1 → LoadHolds rd ch j v ∧
      LoadHolds rd ch (j + 1) (((v + oqResV s rounds w1) * mu + oqResV s rounds w2) * mu))
    (hK : IsInK (gen ^ j * gen + N))
    (htail : if gen ^ j * gen + N ≠ 0 then
      RelAtInCP coreProgram fs cert rd R (fun _ => False) (fp + fs loop) (c + 2 * fs wlk) Bt m loop
        [gen ^ j * gen, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] [] kn
      else Bt = fs loop ∧ m = 0 ∧ kn = [])
    (hRp : ∀ e < 2, OqIn R ((positions * gen ^ j * gen ^ j).limb 0 * Parameters.addressOfIndex
        (odd + e)))
    (hRq : ∀ e < 2, OqIn R ((qptrs * gen ^ j * gen ^ j).limb 0 * Parameters.addressOfIndex
        (odd + e)))
    (hR1 : OqQReg R s cap flags coefs hsp bp1 w1.1) (hR2 : OqQReg R s cap flags coefs hsp bp2 w2.1)
    (hRc : s.final ≠ 1 → ∀ e < 2, OqIn R ((ch * gen ^ j).limb 0 * Parameters.addressOfIndex e)) :
    RelAtInCP coreProgram fs cert rd R (fun _ => False) fp c (fs loop + Bt) (2 * fs wlk + m) loop
      [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] []
      (oqIt1Pops s cap flags rounds hsv w1 w2 bp1 bp2 ++ kn) := by
  set D1 := oqQD s 16 true 0 cap flags rounds hsv w1 with hD1
  set D2 := oqQD s (oqE1 s + 2) false (oqK1 s 16) cap flags rounds hsv w2 with hD2
  set args : List E := [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] with hargs
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ w : V, σ w = oqIter1F s args D1 D2 bp1 bp2 v w.idx :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hpar, hA, hv1, hv2, e11, e13, e15, eB2, eCh, eG2, eG4, hl1, hl2⟩ :=
    oqIter1_at (σ := σ) (walk := wlk) hs hfin hok1 hok2 hx1 hx2 hb1 hb2 hv (fun _ ↦ hσ _)
  have eP : ∀ i < 10, σ (.n i) = args.getD i 0 := by
    intro i hi
    have := congrArg (·.getD i 0) hpar
    simp only [oqLoopParams] at this
    interval_cases i <;> simpa [hargs] using this
  -- the body
  set ca : Stmt := .callIf (.n (oqG1 s + 2)) loop
    [.n (oqG1 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] with hca
  set pre := oqLoop1A s odd wlk ++ [ca] with hpre
  have hok := oqLoop1A_ok s odd wlk
  have hfm : pre.all Stmt.flatM = true := by
    rw [hpre, List.all_append, hok.flatM]; rfl
  have hmo : ∀ x ∈ pre, MatchOk σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hok.matchOk hA x hx
    · simp only [List.mem_singleton] at hx
      subst hx; trivial
  have hbody : fl.body = pre ++ [.ret []] := by
    rw [hbl, hpre, oqLoop1T, oqNextT, List.append_assoc]; rfl
  set es := pre.flatMap (fmEvs σ) with hes
  have hw : walk σ fl.body = .ret es [] := by rw [hbody]; exact walk_flatM σ [] pre hfm hmo
  obtain ⟨i1, i2, i3, i4⟩ := flatM_parts σ pre hfm
  have hal : pre.filterMap Stmt.allocSz = [] := by
    rw [hpre, List.filterMap_append, hok.allocSz]; rfl
  have hallocs : allocs σ es = [] := by rw [i2, hal]; rfl
  set a1 : List V := [.n (oqOut s (oqKL s 16 true) (s.B - 1) 0), .n (oqOut s (oqKL s 16 true) (s.B - 1) 1),
    .n 15, .n 4, .n 5] with ha1
  set a2 : List V := [.n (oqOut s (oqKL s (oqE1 s + 2) false) (s.B - 1) 0),
    .n (oqOut s (oqKL s (oqE1 s + 2) false) (s.B - 1) 1), .n (oqE1 s + 1), .n 4, .n 5] with ha2
  have hcalls : calls es = [⟨wlk, a1, [], true⟩, ⟨wlk, a2, [], true⟩] ++
      [⟨loop, [.n (oqG1 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9],
      [], decide (σ (.n (oqG1 s + 2)) ≠ 0)⟩] := by
    rw [i4, hpre, List.filterMap_append, oqLoop1A_callS]; rfl
  -- the events hold
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    rw [hes, hpre, List.flatMap_append] at he
    rcases List.mem_append.mp he with he | he
    · exact hok.evs_holds hA e he
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at he
      change e ∈ slEvs σ ca at he
      simp only [hca, slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | he
      · show IsInK (σ (.n (oqG1 s + 2)))
        rw [eG2]; exact hK
      · rw [he]; split <;> trivial
  -- the walks
  have hW1 := wp_relAtInP (w := D1.wd bp1) hP fs cert hpd1 (show 1 ≤ s.cd by omega) hok1.hsibs
    hok1.hq hok1.hmem hW hR1.toW
  have hW2 := wp_relAtInP (w := D2.wd bp2) hP fs cert hpd1 (show 1 ≤ s.cd by omega) hok2.hsibs
    hok2.hq hok2.hmem hW hR2.toW
  have hm1 : a1.map σ = [(digestHalves D1.leaf).1, (digestHalves D1.leaf).2, bp1, cap, flags] := by
    have e0 := congrArg Prod.fst hl1
    have e1 := congrArg Prod.snd hl1
    simp only at e0 e1
    simp only [ha1, List.map_cons, List.map_nil, e0, e1, e15, eP 4 (by omega), eP 5 (by omega)]
    rfl
  have hm2 : a2.map σ = [(digestHalves D2.leaf).1, (digestHalves D2.leaf).2, bp2, cap, flags] := by
    have e0 := congrArg Prod.fst hl2
    have e1 := congrArg Prod.snd hl2
    simp only at e0 e1
    simp only [ha2, List.map_cons, List.map_nil, e0, e1, eB2, eP 4 (by omega), eP 5 (by omega)]
    rfl
  -- the pops
  have hps : splice rd σ es ([(D1.wd bp1).wpPops, (D2.wd bp2).wpPops] ++ [kn]) =
      oqIt1Pops s cap flags rounds hsv w1 w2 bp1 bp2 ++ kn := by
    have hx : SplicePops rd σ pre [(D1.wd bp1).wpPops, (D2.wd bp2).wpPops, kn]
        (rowPop σ 16 s.I :: (D1.wd bp1).wpPops ++ rowPop σ (oqE1 s + 2) s.I :: (D2.wd bp2).wpPops ++ kn) :=
      (oqLoop1A_splicePops s odd wlk _ _).append (SplicePops.callIf _ _ _ kn)
    rw [List.cons_append, List.cons_append, List.nil_append,
      splice_of_body hbody hx (show walk σ [.ret []] = .ret [] [] by simp [walk, walk1, Out.seq]) rfl hw,
      show rowPop σ 16 s.I = rowPop σ D1.b D1.s.I from rfl, D1.rowPop_vals hv1,
      show rowPop σ (oqE1 s + 2) s.I = rowPop σ D2.b D2.s.I from rfl, D2.rowPop_vals hv2]
    simp [oqIt1Pops, evPops, hD1, hD2]
  have inR : ∀ A, OqIn R A → ∃ i, A = Parameters.addressOfIndex i ∧
      (ownData cert fp c loop (allocs σ es) es i ∨ R i ∨ False ∨
        ((⟨loop, [.n (oqG1 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9], [],
          decide (σ (.n (oqG1 s + 2)) ≠ 0)⟩ : Call).taken = true ∧ False)) :=
    fun A ⟨i, hi, hr⟩ ↦ ⟨i, hi, Or.inr (Or.inl hr)⟩
  have h := relAtInP_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    hP (R := R) (D := fun _ => False) (Dk := fun _ => False) (Rt := R) (Dt := fun _ => False)
    (fp := fp) (c := c) (Bt := Bt) (m := m) (N := fs wlk + (fs wlk + 0)) (args := args) (rets := [])
    hfl hlp (hpl ▸ hpar) hw rfl hev hcalls ?_
    (by rw [i1, hal, hallocs]; rfl)
    (fun q hq ↦ ?_) ?_ (fun i hi ↦ Or.inl hi)
    (fun A hAl ↦ ?_) (fun _ h ↦ h.elim) hps
  · rw [hallocs, List.sum_nil, show 0 + (fs wlk + (fs wlk + 0)) + m = 2 * fs wlk + m by ring] at h
    exact h
  · -- the tail
    rw [hallocs, List.sum_nil, show c + 0 + (fs wlk + (fs wlk + 0)) = c + 2 * fs wlk by ring]
    have hargs' : ([.n (oqG1 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] :
        List V).map σ = [gen ^ j * gen, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] := by
      simp only [List.map_cons, List.map_nil, eG4, eP 1 (by omega), eP 2 (by omega),
        eP 3 (by omega), eP 4 (by omega), eP 5 (by omega), eP 6 (by omega), eP 7 (by omega),
        eP 8 (by omega), eP 9 (by omega)]
      rfl
    by_cases ht : gen ^ j * gen + N ≠ 0
    · simp only [ht, ne_eq, not_false_eq_true, ↓reduceIte] at htail
      have htk : decide (σ (.n (oqG1 s + 2)) ≠ 0) = true := by rw [eG2]; exact decide_eq_true ht
      simp only [htk, ↓reduceIte, List.map_nil]
      rw [hargs']; exact htail
    · simp only [ht, ↓reduceIte] at htail
      have htk : decide (σ (.n (oqG1 s + 2)) ≠ 0) = false := by rw [eG2]; exact decide_eq_false ht
      simp only [htk, Bool.false_eq_true, ↓reduceIte]
      exact htail
  · -- no frame address
    rw [i3, hpre, List.filterMap_append, hok.addrS] at hq
    simp [hca, Stmt.addrS] at hq
  · -- the walks
    rw [hallocs, List.sum_nil, Nat.add_zero]
    refine ⟨fs wlk, fs wlk + 0, R, fun _ => False, rfl, fun i hi ↦ Or.inl (Or.inl hi), ?_,
      fs wlk, 0, R, fun _ => False, rfl, fun i hi ↦ Or.inl (Or.inl hi), ?_, rfl, fun _ h ↦ h.elim⟩
    · rw [ite_eq_left rfl, hm1]; exact hW1 _
    · rw [ite_eq_left rfl, hm2]; exact hW2 _
  · -- the loads
    rw [loadAddrs_flatM σ pre hfm] at hAl
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hAl
    rw [hpre, List.filterMap_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok.load hq with hl | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
      · exact inR _ (oqQLoad_in (σ := σ) (coefs := .n 6) (hs := .n 7)
          (by rw [eP 6 (by omega), eP 7 (by omega)]; exact hR1) hl)
      · rw [e11]
        rcases ho with rfl | rfl
        · exact inR _ (by simpa using hRp 0 (by omega))
        · exact inR _ (hRp 1 (by omega))
      · rw [e13]
        rcases ho with rfl | rfl
        · exact inR _ (by simpa using hRq 0 (by omega))
        · exact inR _ (hRq 1 (by omega))
      · rw [(eCh hf).1]; exact inR _ (hRc hf 0 (by omega))
      · rw [(eCh hf).2]; exact inR _ (hRc hf 1 (by omega))
    · simp [hca, stmtLoad?] at hq

/-- **The level-0 loop, placed, with its pops**: its iterations' entries in order (`oqLoop1_relAtIn`). -/
theorem oqLoop1_relAtInP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) {odd : ℕ}
    {wlk loop : String}
    (hW : WalkFn coreProgram wlk s.pd s.cd) {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd wlk loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N : ℕ} (hN : N < ordG)
    {positions qptrs cap flags coefs hsp ch mu : E} {rounds : List FoldRound} {hsv : List E}
    {w1 w2 : ℕ → QW} {bp1 bp2 v : ℕ → E}
    (hit : ∀ j < N, OqIt1Ok rd R s odd j positions qptrs cap flags coefs hsp ch mu rounds hsv
      (w1 j) (w2 j) (bp1 j) (bp2 j) (v j)) (hN0 : 0 < N) :
    RelAtInP coreProgram fs cert rd R (fun _ => False) fp ((N + 1) * fs loop + N * (2 * fs wlk)) loop
      [gen ^ 0, gen ^ N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] []
      ((List.range N).flatMap fun j => oqIt1Pops s cap flags rounds hsv (w1 j) (w2 j) (bp1 j) (bp2 j)) := by
  set it : ℕ → List Pop := fun j => oqIt1Pops s cap flags rounds hsv (w1 j) (w2 j) (bp1 j) (bp2 j) with hit'
  suffices h : ∀ n j, j + n + 1 = N → RelAtInCP coreProgram fs cert rd R (fun _ => False)
      (fp + j * fs loop) (fp + (N + 1) * fs loop + j * (2 * fs wlk)) ((N - j + 1) * fs loop)
      ((N - j) * (2 * fs wlk)) loop [gen ^ j, gen ^ N, positions, qptrs, cap, flags, coefs, hsp, ch, mu]
      [] ((List.range' j (n + 1)).flatMap it) by
    have := h (N - 1) 0 (by omega)
    simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero, show N - 1 + 1 = N by omega,
      ← List.range_eq_range'] at this
    exact this.relAtInP
  intro n
  induction n with
  | zero =>
    intro j hj
    have H := hit j (by omega)
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have := oqIter1_relAtInP (fp := fp + j * fs loop)
      (c := fp + (N + 1) * fs loop + j * (2 * fs wlk)) (Bt := fs loop) (m := 0) (kn := []) hP fs cert hs hfin
      hpd1 hcd hW hfl hpl hbl hlp H.ok1 H.ok2 H.x1 H.x2 H.b1 H.b2 H.chv hK
      (by
        split
        · next h => exact absurd (hne.mp h) (by omega)
        · exact ⟨rfl, rfl, rfl⟩) H.rp H.rq H.reg1 H.reg2 H.rc
    rw [show (N - j + 1) * fs loop = fs loop + fs loop by rw [show N - j = 1 by omega]; ring,
      show (N - j) * (2 * fs wlk) = 2 * fs wlk + 0 by rw [show N - j = 1 by omega]; ring,
      show (List.range' j (0 + 1)).flatMap it = it j ++ [] by simp]
    exact this
  | succ n ih =>
    intro j hj
    have H := hit j (by omega)
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have ht := ih (j + 1) (by omega)
    rw [show fp + (j + 1) * fs loop = fp + j * fs loop + fs loop by ring,
      show fp + (N + 1) * fs loop + (j + 1) * (2 * fs wlk) =
        fp + (N + 1) * fs loop + j * (2 * fs wlk) + 2 * fs wlk by ring, pow_succ] at ht
    have := oqIter1_relAtInP (fp := fp + j * fs loop)
      (c := fp + (N + 1) * fs loop + j * (2 * fs wlk)) (Bt := (N - (j + 1) + 1) * fs loop)
      (m := (N - (j + 1)) * (2 * fs wlk)) hP fs cert hs hfin hpd1 hcd hW hfl
      hpl hbl hlp H.ok1 H.ok2 H.x1 H.x2 H.b1 H.b2 H.chv hK
      (by
        split
        · exact ht
        · next h => exact absurd (hne.mpr (by omega)) h) H.rp H.rq H.reg1 H.reg2 H.rc
    rw [show (N - j + 1) * fs loop = fs loop + (N - (j + 1) + 1) * fs loop by
        rw [show N - j = N - (j + 1) + 1 by omega]; ring,
      show (N - j) * (2 * fs wlk) = 2 * fs wlk + (N - (j + 1)) * (2 * fs wlk) by
        rw [show N - j = N - (j + 1) + 1 by omega]; ring,
      List.range'_succ, List.flatMap_cons]
    exact this

end
end LeanVM.Guest.B1
