/-
  LeanVM.Guest.B1.Opening.QueriesPlacedP

  A level-0 iteration of `opening_queries`' loop and the loop, placed with their pops (`RelAtInP`):
  the honest rows and siblings, query by query.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedL
public import LeanVM.Guest.B1.Opening.QueriesPops
public import LeanVM.Guest.B1.Main.RelAtInP

/-!
# The level-0 loop, placed with its pops

An iteration's body is flat and calls nothing but its next iteration (the walks inline), so it is
placed by `relAtInP_of_walk_loop` with no other callee, its pops from `QueriesPops`
(`oqLoop1A_fallPops`, `splice_of_body`).

* `QD.queryPops_vals`: at the honest values a query's entries are its row's cells and its
  siblings' (`oqQE`, which reads only the shape and the witness);
* `QD.winSel`: at the honest values its windows' words are arms of their matches;
* `oqIter1_relAtInP`: a level-0 iteration pops its two queries' entries, then its tail's;
* `oqLoop1_relAtInP`: the level-0 loop, its `N` frames from `fp` and its last call's tail frame,
  pops its iterations' entries in order.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A query's entries**: its row's cells, its siblings' cells. -/
def oqQE (s : Oq) (w : QW) : List Pop :=
  ("merkle_leaf_rows", (oqQD s 0 0 true 0 0 0 0 [] [] w).rowVals) :: (oqQD s 0 0 true 0 0 0 0 [] [] w).wd.wpPops

theorem oqQE_eq (s : Oq) (cd b : ℕ) (emit : Bool) (pr : ℕ) (bp cap flags : E) (rounds : List FoldRound)
    (hsv : List E) (w : QW) :
    ("merkle_leaf_rows", (oqQD s cd b emit pr bp cap flags rounds hsv w).rowVals) ::
      (oqQD s cd b emit pr bp cap flags rounds hsv w).wd.wpPops = oqQE s w := rfl

namespace QD

variable (d : QD) {σ : Val}

theorem fo_lt_e : d.fo < d.e := lt_of_le_of_lt d.fo_le_v d.v_lt_e

/-- **At the honest values a query's entries** are its row's cells and its siblings'. -/
theorem queryPops_vals (hv : d.Hv σ) :
    queryPops σ d.s d.b d.emit = ("merkle_leaf_rows", d.rowVals) :: d.wd.wpPops := by
  have he := d.ch_lt_e
  have hfe := d.fo_lt_e
  have hfo := d.fo_eq
  have hl := d.wd.vals_length
  have hI : d.b + d.s.I ≤ d.ch := by simp only [QD.ch, oqCh, oqKL, oqK1]; split_ifs <;> omega
  have hb := d.b_le_ch
  simp only [queryPops, rowPop, WD.wpPops, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
  refine ⟨?_, ?_⟩
  · rw [QD.rowVals]
    exact List.map_congr_left fun j hj => by
      have := List.mem_range.mp hj
      rw [hv _ (by omega) (by omega), d.val_row this]
  · exact List.map_congr_left fun j hj => by
      have := List.mem_range.mp hj
      have hl' : d.wd.vals.length = 2 * d.s.pd + winOff d.s (oqNpw d.s) + 9 := hl
      rw [show oqCh d.s d.b d.emit = d.ch from rfl, hv _ (by omega) (by omega), d.val_sib this]

/-- **At the honest values a query's windows' words** are arms of their matches. -/
theorem winSel (hv : d.Hv σ) : WinSel σ d.s d.ch := by
  intro i hi
  have h1 := winOff_succ_le (s := d.s) hi
  have hfe := d.fo_lt_e
  have hb := d.b_le_ch
  have h5 : d.fo = oqCq d.s d.ch + 9 := rfl
  have h6 : oqCq d.s d.ch = d.ch + 2 * d.s.pd + winOff d.s (oqNpw d.s) := by rw [oqCq, oqWk_eq]
  have h7 : oqWk d.s d.ch i = d.ch + 2 * d.s.pd + winOff d.s i := oqWk_eq _ _ _
  have hsz : 0 < winSz d.s i := by unfold winSz; omega
  refine ⟨d.wd.wv i, (qwVal_path hi d.q).1, ?_⟩
  rw [show oqWk d.s d.ch i = oqWk d.s d.ch i + 0 from rfl, hv _ (by omega) (by omega),
    d.val_win hi hsz, WD.winV, ite_eq_left rfl, gen_pow_eq_ofK]

end QD

/-- **A level-0 iteration, placed, with its pops**: its queries' (`oqQE`), then its tail's `kn`
(`[]` after the last). -/
theorem oqIter1_relAtInP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp c Bt m cd j : ℕ} {N positions qptrs cap flags coefs hsp ch mu : E}
    {rounds : List FoldRound} {hsv : List E} {w1 w2 : QW} {bp1 bp2 v : E} {kn : List Pop}
    (H : OqIt1Ok rd R s cd j positions qptrs cap flags coefs hsp ch mu rounds hsv w1 w2 bp1 bp2 v)
    (hK : IsInK (gen ^ j * gen + N))
    (htail : if gen ^ j * gen + N ≠ 0 then
      RelAtInCP coreProgram fs cert rd R (fun _ => False) (fp + fs loop) c Bt m loop
        [gen ^ j * gen, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] [] kn
      else Bt = fs (tailKey loop) ∧ m = 0 ∧ kn = []) :
    RelAtInCP coreProgram fs cert rd R (fun _ => False) fp c (fs loop + Bt) m loop
      [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] []
      (oqQE s w1 ++ oqQE s w2 ++ kn) := by
  set D1 := oqQD s cd 15 true 0 bp1 cap flags rounds hsv w1 with hD1
  set D2 := oqQD s cd (oqE1 s + 2) false (oqK1 s 15) bp2 cap flags rounds hsv w2 with hD2
  set args : List E := [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] with hargs
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ w : V, σ w = oqIter1F s args D1 D2 v w.idx :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hpar, hA, hv1, hv2, e11, e12, e14, eB2, eCh, eG2, eG4⟩ :=
    oqIter1_at (σ := σ) hs hfin H.ok1 H.ok2 H.x1 H.x2 H.b1 H.b2 H.chv (fun _ ↦ hσ _)
  have eP : ∀ i < 10, σ (.n i) = args.getD i 0 := by
    intro i hi
    have := congrArg (·.getD i 0) hpar
    simp only [oqLoopParams] at this
    interval_cases i <;> simpa [hargs] using this
  -- the body
  set ca : Stmt := .callIf (.n (oqG1 s + 2)) loop (oqNextArgs (oqG1 s)) with hca
  set pre := oqLoop1A s ++ [ca] with hpre
  have hok := oqLoop1A_ok s
  have hfm : pre.all Stmt.flatM = true := by
    rw [hpre, List.all_append, hok.flatM]; rfl
  have hmo : ∀ x ∈ pre, MatchOk σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hok.matchOk hA x hx
    · simp only [List.mem_singleton] at hx
      subst hx; trivial
  have hbody : fl.body = pre ++ [.ret []] := by
    rw [hbl, hpre, oqLoop1T, oqNextT_eq, List.append_assoc]; rfl
  set es := pre.flatMap (fmEvs σ) with hes
  have hw : walk σ fl.body = .ret es [] := by rw [hbody]; exact walk_flatM σ [] pre hfm hmo
  obtain ⟨i1, i2, i3, i4⟩ := flatM_parts σ pre hfm
  have hal : pre.filterMap Stmt.allocSz = [] := by
    rw [hpre, List.filterMap_append, hok.allocSz]; rfl
  have hallocs : allocs σ es = [] := by rw [i2, hal]; rfl
  have hcalls : calls es = [] ++ [⟨loop, oqNextArgs (oqG1 s), [], decide (σ (.n (oqG1 s + 2)) ≠ 0)⟩] := by
    rw [i4, hpre, List.filterMap_append, callS_flat (oqLoop1A_flat s)]; rfl
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
  -- the pops
  have hps : splice rd σ es ([] ++ [kn]) = oqQE s w1 ++ oqQE s w2 ++ kn := by
    have hx : SplicePops rd σ pre ([] ++ [kn])
        (queryPops σ s 15 true ++ queryPops σ s (oqE1 s + 2) false ++ kn) :=
      (SplicePops.of_fallPops (oqLoop1A_fallPops s (D1.winSel hv1) (D2.winSel hv2))).append
        (SplicePops.callIf _ _ _ kn)
    rw [splice_of_body hbody hx (show walk σ [.ret []] = .ret [] [] by simp [walk, walk1, Out.seq]) rfl hw,
      show queryPops σ s 15 true = queryPops σ D1.s D1.b D1.emit from rfl, D1.queryPops_vals hv1,
      show queryPops σ s (oqE1 s + 2) false = queryPops σ D2.s D2.b D2.emit from rfl,
      D2.queryPops_vals hv2, oqQE_eq, oqQE_eq]
    simp [evPops]
  have inR : ∀ A, OqIn R A → ∃ i, A = Parameters.addressOfIndex i ∧
      (ownData cert fp c loop (allocs σ es) es i ∨ R i ∨ False ∨
        ((⟨loop, oqNextArgs (oqG1 s), [], decide (σ (.n (oqG1 s + 2)) ≠ 0)⟩ : Call).taken = true ∧
          False)) :=
    fun A ⟨i, hi, hr⟩ ↦ ⟨i, hi, Or.inr (Or.inl hr)⟩
  have h := relAtInP_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    hP (R := R) (D := fun _ => False) (Dk := fun _ => False) (Rt := R) (Dt := fun _ => False)
    (fp := fp) (c := c) (Bt := Bt) (m := m) (N := 0) (args := args) (rets := []) (pss := [])
    hfl hlp (hpl ▸ hpar) hw rfl hev hcalls ?_
    (by rw [i1, hal, hallocs]; rfl)
    (fun q hq ↦ ?_) ⟨rfl, fun _ h ↦ h⟩ (fun i hi ↦ Or.inl hi)
    (fun A hAl ↦ ?_) (fun _ h ↦ h.elim) hps
  · simpa [hallocs] using h
  · -- the tail
    rw [hallocs, List.sum_nil, Nat.add_zero, Nat.add_zero]
    have hargs' : (oqNextArgs (oqG1 s)).map σ =
        [gen ^ j * gen, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] := by
      simp only [oqNextArgs, List.map_cons, List.map_nil, eG4, eP 1 (by omega), eP 2 (by omega),
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
  · -- the loads
    rw [loadAddrs_flatM σ pre hfm] at hAl
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hAl
    rw [hpre, List.filterMap_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok.load hq with hl | hl | ⟨rfl, ho⟩ | ⟨rfl, ho⟩ | ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
      · exact inR _ (oqQLoad_in (d := D1) hv1 (coefs := .n oqCoefs) (hs := .n oqHs) (bp := .n 14)
          (by rw [eP 6 (by omega), eP 7 (by omega), e14]; exact H.reg1) hl)
      · exact inR _ (oqQLoad_in (d := D2) hv2 (coefs := .n oqCoefs) (hs := .n oqHs) (bp := .n (oqE1 s + 1))
          (by rw [eP 6 (by omega), eP 7 (by omega), eB2]; exact H.reg2) hl)
      · rw [e11]; exact inR _ (H.rp off ho)
      · rw [e12]; exact inR _ (H.rq off ho)
      · rw [(eCh hf).1]; exact inR _ (H.rc hf 0 (by omega))
      · rw [(eCh hf).2]; exact inR _ (H.rc hf 1 (by omega))
    · simp [hca, stmtLoad?] at hq

/-- **The level-0 loop, placed, with its pops**: entered at `g^0`, its frames at `fp` and its last
call's tail frame after them, it pops its iterations' entries in order. -/
theorem oqLoop1_relAtInP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N cd : ℕ} (hN : N < ordG)
    {positions qptrs cap flags coefs hsp ch mu : E} {rounds : List FoldRound} {hsv : List E}
    {w1 w2 : ℕ → QW} {bp1 bp2 v : ℕ → E}
    (hit : ∀ j < N, OqIt1Ok rd R s cd j positions qptrs cap flags coefs hsp ch mu rounds hsv
      (w1 j) (w2 j) (bp1 j) (bp2 j) (v j)) (hN0 : 0 < N) :
    RelAtInP coreProgram fs cert rd R (fun _ => False) fp (N * fs loop + fs (tailKey loop)) loop
      [gen ^ 0, gen ^ N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] []
      ((List.range N).flatMap fun j => oqQE s (w1 j) ++ oqQE s (w2 j)) := by
  set it : ℕ → List Pop := fun j => oqQE s (w1 j) ++ oqQE s (w2 j) with hit'
  set B := N * fs loop + fs (tailKey loop) with hB
  suffices h : ∀ n j, j + n + 1 = N → RelAtInCP coreProgram fs cert rd R (fun _ => False)
      (fp + j * fs loop) (fp + B) ((N - j) * fs loop + fs (tailKey loop)) 0 loop
      [gen ^ j, gen ^ N, positions, qptrs, cap, flags, coefs, hsp, ch, mu]
      [] ((List.range' j (n + 1)).flatMap it) by
    have := h (N - 1) 0 (by omega)
    simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero, show N - 1 + 1 = N by omega,
      ← List.range_eq_range'] at this
    exact this.relAtInP
  intro n
  induction n with
  | zero =>
    intro j hj
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have := oqIter1_relAtInP (fp := fp + j * fs loop) (c := fp + B) (Bt := fs (tailKey loop))
      (m := 0) (kn := []) hP fs cert hs hfin hfl hpl hbl hlp (hit j (by omega)) hK
      (by
        split
        · next h => exact absurd (hne.mp h) (by omega)
        · exact ⟨rfl, rfl, rfl⟩)
    rw [show (N - j) * fs loop + fs (tailKey loop) = fs loop + fs (tailKey loop) by
        rw [show N - j = 1 by omega, Nat.one_mul],
      show (List.range' j (0 + 1)).flatMap it = oqQE s (w1 j) ++ oqQE s (w2 j) ++ [] by simp [hit']]
    exact this
  | succ n ih =>
    intro j hj
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have ht := ih (j + 1) (by omega)
    rw [show fp + (j + 1) * fs loop = fp + j * fs loop + fs loop by ring, pow_succ] at ht
    have := oqIter1_relAtInP (fp := fp + j * fs loop) (c := fp + B)
      (Bt := (N - (j + 1)) * fs loop + fs (tailKey loop)) (m := 0) hP fs cert hs hfin hfl hpl hbl hlp
      (hit j (by omega)) hK
      (by
        split
        · exact ht
        · next h => exact absurd (hne.mpr (by omega)) h)
    rw [show (N - j) * fs loop + fs (tailKey loop) =
        fs loop + ((N - (j + 1)) * fs loop + fs (tailKey loop)) by
        rw [show N - j = N - (j + 1) + 1 by omega]; ring,
      List.range'_succ, List.flatMap_cons]
    exact this

end
end LeanVM.Guest.B1
