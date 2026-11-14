/-
  LeanVM.Guest.B1.Opening.QueriesPlacedP2

  A deeper iteration of `opening_queries`' loop and the loop, placed with their pops (`RelAtInP`).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedP

/-!
# The deeper loop, placed with its pops

`QueriesPlaced5`'s and `QueriesPlaced6`'s deeper proofs with `relAtInP_of_walk_loop` and `KidsFromInP`, as `QueriesPlacedP` at level 0.

* `oqIt0Pops`, `oqIter0_relAtInP`: a deeper iteration pops its query's row and walk's children, then its tail's entries;
* `oqLoop0_relAtInP`: the deeper loop pops its iterations', in order.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A deeper iteration's entries**: its query's row and walk's children. -/
def oqIt0Pops (s : Oq) (cap flags : E) (rounds : List FoldRound) (hsv : List E) (w : QW) (bp : E) : List Pop :=
  ("merkle_leaf_rows", (oqQD s 14 true 0 cap flags rounds hsv w).rowVals) ::
    ((oqQD s 14 true 0 cap flags rounds hsv w).wd bp).wpPops

/-- **A deeper iteration, placed, with its pops**: its query's (`oqIt0Pops`), then its tail's `kn` (`[]` after the
last). -/
theorem oqIter0_relAtInP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd)
    {wlk loop : String} (hW : WalkFn coreProgram wlk s.pd s.cd) {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s wlk loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp c Bt m j : ℕ} {N positions qptrs cap flags coefs hsp ch mu : E}
    {rounds : List FoldRound} {hsv : List E} {w : QW} {bp v : E} {kn : List Pop}
    (hok : (oqQD s 14 true 0 cap flags rounds hsv w).Ok rd coefs hsp bp)
    (hx : LoadHolds rd positions j (eOfNat w.1)) (hb : LoadHolds rd qptrs j bp)
    (hv : s.final ≠ 1 → LoadHolds rd ch j v ∧ LoadHolds rd ch (j + 1) ((v + oqResV s rounds w) * mu))
    (hK : IsInK (gen ^ j * gen + N))
    (htail : if gen ^ j * gen + N ≠ 0 then
      RelAtInCP coreProgram fs cert rd R (fun _ => False) (fp + fs loop) (c + fs wlk) Bt m loop
        [gen ^ j * gen, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] [] kn
      else Bt = fs loop ∧ m = 0 ∧ kn = [])
    (hRp : OqIn R ((positions * gen ^ j).limb 0 * Parameters.addressOfIndex 0))
    (hRq : OqIn R ((qptrs * gen ^ j).limb 0 * Parameters.addressOfIndex 0))
    (hR1 : OqQReg R s cap flags coefs hsp bp w.1)
    (hRc : s.final ≠ 1 → ∀ e < 2, OqIn R ((ch * gen ^ j).limb 0 * Parameters.addressOfIndex e)) :
    RelAtInCP coreProgram fs cert rd R (fun _ => False) fp c (fs loop + Bt) (fs wlk + m) loop
      [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] []
      (oqIt0Pops s cap flags rounds hsv w bp ++ kn) := by
  set D1 := oqQD s 14 true 0 cap flags rounds hsv w with hD1
  set args : List E := [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] with hargs
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ w : V, σ w = oqIter0F s args D1 bp v w.idx := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hpar, hA, hv1, e10, e12, e13, eCh, eG2, eG4, hl1⟩ :=
    oqIter0_at (σ := σ) (walk := wlk) hs hfin hok hx hb hv (fun _ ↦ hσ _)
  have eP : ∀ i < 10, σ (.n i) = args.getD i 0 := by
    intro i hi
    have := congrArg (·.getD i 0) hpar
    simp only [oqLoopParams] at this
    interval_cases i <;> simpa [hargs] using this
  set ca : Stmt := .callIf (.n (oqG0 s + 2)) loop
    [.n (oqG0 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] with hca
  set pre := oqLoop0A s wlk ++ [ca] with hpre
  have hok' := oqLoop0A_ok s wlk
  have hfm : pre.all Stmt.flatM = true := by
    rw [hpre, List.all_append, hok'.flatM]; rfl
  have hmo : ∀ x ∈ pre, MatchOk σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hok'.matchOk hA x hx
    · simp only [List.mem_singleton] at hx
      subst hx; trivial
  have hbody : fl.body = pre ++ [.ret []] := by
    rw [hbl, hpre, oqLoop0T, oqNextT, List.append_assoc]; rfl
  set es := pre.flatMap (fmEvs σ) with hes
  have hw : walk σ fl.body = .ret es [] := by rw [hbody]; exact walk_flatM σ [] pre hfm hmo
  obtain ⟨i1, i2, i3, i4⟩ := flatM_parts σ pre hfm
  have hal : pre.filterMap Stmt.allocSz = [] := by
    rw [hpre, List.filterMap_append, hok'.allocSz]; rfl
  have hallocs : allocs σ es = [] := by rw [i2, hal]; rfl
  set a1 : List V := [.n (oqOut s (oqKL s 14 true) (s.B - 1) 0), .n (oqOut s (oqKL s 14 true) (s.B - 1) 1),
    .n 13, .n 4, .n 5] with ha1
  have hcalls : calls es = [⟨wlk, a1, [], true⟩] ++
      [⟨loop, [.n (oqG0 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9],
      [], decide (σ (.n (oqG0 s + 2)) ≠ 0)⟩] := by
    rw [i4, hpre, List.filterMap_append, oqLoop0A_callS]; rfl
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    rw [hes, hpre, List.flatMap_append] at he
    rcases List.mem_append.mp he with he | he
    · exact hok'.evs_holds hA e he
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at he
      change e ∈ slEvs σ ca at he
      simp only [hca, slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | he
      · show IsInK (σ (.n (oqG0 s + 2)))
        rw [eG2]; exact hK
      · rw [he]; split <;> trivial
  have hW1 := wp_relAtInP (w := D1.wd bp) hP fs cert hpd1 (show 1 ≤ s.cd by omega) hok.hsibs hok.hq
    hok.hmem hW hR1.toW
  have hm1 : a1.map σ = [(digestHalves D1.leaf).1, (digestHalves D1.leaf).2, bp, cap, flags] := by
    have e0 := congrArg Prod.fst hl1
    have e1 := congrArg Prod.snd hl1
    simp only at e0 e1
    simp only [ha1, List.map_cons, List.map_nil, e0, e1, e13, eP 4 (by omega), eP 5 (by omega)]
    rfl
  -- the pops
  have hps : splice rd σ es ([(D1.wd bp).wpPops] ++ [kn]) = oqIt0Pops s cap flags rounds hsv w bp ++ kn := by
    have hx : SplicePops rd σ pre [(D1.wd bp).wpPops, kn] (rowPop σ 14 s.I :: (D1.wd bp).wpPops ++ kn) :=
      (oqLoop0A_splicePops s wlk _).append (SplicePops.callIf _ _ _ kn)
    rw [List.singleton_append,
      splice_of_body hbody hx (show walk σ [.ret []] = .ret [] [] by simp [walk, walk1, Out.seq]) rfl hw,
      show rowPop σ 14 s.I = rowPop σ D1.b D1.s.I from rfl, D1.rowPop_vals hv1]
    simp [oqIt0Pops, evPops, hD1]
  have inR : ∀ A, OqIn R A → ∃ i, A = Parameters.addressOfIndex i ∧
      (ownData cert fp c loop (allocs σ es) es i ∨ R i ∨ False ∨
        ((⟨loop, [.n (oqG0 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9], [],
          decide (σ (.n (oqG0 s + 2)) ≠ 0)⟩ : Call).taken = true ∧ False)) :=
    fun A ⟨i, hi, hr⟩ ↦ ⟨i, hi, Or.inr (Or.inl hr)⟩
  have h := relAtInP_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    hP (R := R) (D := fun _ => False) (Dk := fun _ => False) (Rt := R) (Dt := fun _ => False)
    (fp := fp) (c := c) (Bt := Bt) (m := m) (N := fs wlk + 0) (args := args) (rets := [])
    hfl hlp (hpl ▸ hpar) hw rfl hev hcalls ?_
    (by rw [i1, hal, hallocs]; rfl)
    (fun q hq ↦ ?_) ?_ (fun i hi ↦ Or.inl hi)
    (fun A hAl ↦ ?_) (fun _ h ↦ h.elim) hps
  · rw [hallocs, List.sum_nil, show 0 + (fs wlk + 0) + m = fs wlk + m by ring] at h; exact h
  · rw [hallocs, List.sum_nil, show c + 0 + (fs wlk + 0) = c + fs wlk by ring]
    have hargs' : ([.n (oqG0 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] :
        List V).map σ = [gen ^ j * gen, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] := by
      simp only [List.map_cons, List.map_nil, eG4, eP 1 (by omega), eP 2 (by omega),
        eP 3 (by omega), eP 4 (by omega), eP 5 (by omega), eP 6 (by omega), eP 7 (by omega),
        eP 8 (by omega), eP 9 (by omega)]
      rfl
    by_cases ht : gen ^ j * gen + N ≠ 0
    · simp only [ht, ne_eq, not_false_eq_true, ↓reduceIte] at htail
      have htk : decide (σ (.n (oqG0 s + 2)) ≠ 0) = true := by rw [eG2]; exact decide_eq_true ht
      simp only [htk, ↓reduceIte, List.map_nil]
      rw [hargs']; exact htail
    · simp only [ht, ↓reduceIte] at htail
      have htk : decide (σ (.n (oqG0 s + 2)) ≠ 0) = false := by rw [eG2]; exact decide_eq_false ht
      simp only [htk, Bool.false_eq_true, ↓reduceIte]
      exact htail
  · rw [i3, hpre, List.filterMap_append, hok'.addrS] at hq
    simp [hca, Stmt.addrS] at hq
  · rw [hallocs, List.sum_nil, Nat.add_zero]
    refine ⟨fs wlk, 0, R, fun _ => False, rfl, fun i hi ↦ Or.inl (Or.inl hi), ?_, rfl, fun _ h ↦ h.elim⟩
    rw [ite_eq_left rfl, hm1]; exact hW1 _
  · rw [loadAddrs_flatM σ pre hfm] at hAl
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hAl
    rw [hpre, List.filterMap_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok'.load hq with hl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
      · exact inR _ (oqQLoad_in (σ := σ) (coefs := .n 6) (hs := .n 7)
          (by rw [eP 6 (by omega), eP 7 (by omega)]; exact hR1) hl)
      · rw [e10]; exact inR _ hRp
      · rw [e12]; exact inR _ hRq
      · rw [(eCh hf).1]; exact inR _ (hRc hf 0 (by omega))
      · rw [(eCh hf).2]; exact inR _ (hRc hf 1 (by omega))
    · simp [hca, stmtLoad?] at hq

/-- **The deeper loop, placed, with its pops**: its iterations' entries in order (`oqLoop0_relAtIn`). -/
theorem oqLoop0_relAtInP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd)
    {wlk loop : String}
    (hW : WalkFn coreProgram wlk s.pd s.cd) {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s wlk loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N : ℕ} (hN : N < ordG)
    {positions qptrs cap flags coefs hsp ch mu : E} {rounds : List FoldRound} {hsv : List E}
    {w : ℕ → QW} {bp v : ℕ → E}
    (hit : ∀ j < N, OqIt0Ok rd R s j positions qptrs cap flags coefs hsp ch mu rounds hsv
      (w j) (bp j) (v j)) (hN0 : 0 < N) :
    RelAtInP coreProgram fs cert rd R (fun _ => False) fp ((N + 1) * fs loop + N * fs wlk) loop
      [gen ^ 0, gen ^ N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] []
      ((List.range N).flatMap fun j => oqIt0Pops s cap flags rounds hsv (w j) (bp j)) := by
  set it : ℕ → List Pop := fun j => oqIt0Pops s cap flags rounds hsv (w j) (bp j) with hit'
  suffices h : ∀ n j, j + n + 1 = N → RelAtInCP coreProgram fs cert rd R (fun _ => False)
      (fp + j * fs loop) (fp + (N + 1) * fs loop + j * fs wlk) ((N - j + 1) * fs loop)
      ((N - j) * fs wlk) loop [gen ^ j, gen ^ N, positions, qptrs, cap, flags, coefs, hsp, ch, mu]
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
    have := oqIter0_relAtInP (fp := fp + j * fs loop) (c := fp + (N + 1) * fs loop + j * fs wlk)
      (Bt := fs loop) (m := 0) (kn := []) hP fs cert hs hfin hpd1 hcd hW hfl hpl hbl hlp
      H.ok H.x H.b H.chv hK (by
        split
        · next h => exact absurd (hne.mp h) (by omega)
        · exact ⟨rfl, rfl, rfl⟩) H.rp H.rq H.reg H.rc
    rw [show (N - j + 1) * fs loop = fs loop + fs loop by rw [show N - j = 1 by omega]; ring,
      show (N - j) * fs wlk = fs wlk + 0 by rw [show N - j = 1 by omega]; ring,
      show (List.range' j (0 + 1)).flatMap it = it j ++ [] by simp]
    exact this
  | succ n ih =>
    intro j hj
    have H := hit j (by omega)
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have ht := ih (j + 1) (by omega)
    rw [show fp + (j + 1) * fs loop = fp + j * fs loop + fs loop by ring,
      show fp + (N + 1) * fs loop + (j + 1) * fs wlk =
        fp + (N + 1) * fs loop + j * fs wlk + fs wlk by ring, pow_succ] at ht
    have := oqIter0_relAtInP (fp := fp + j * fs loop) (c := fp + (N + 1) * fs loop + j * fs wlk)
      (Bt := (N - (j + 1) + 1) * fs loop) (m := (N - (j + 1)) * fs wlk) hP fs cert hs hfin hpd1
      hcd hW hfl hpl hbl hlp H.ok H.x H.b H.chv hK
      (by
        split
        · exact ht
        · next h => exact absurd (hne.mpr (by omega)) h) H.rp H.rq H.reg H.rc
    rw [show (N - j + 1) * fs loop = fs loop + (N - (j + 1) + 1) * fs loop by
        rw [show N - j = N - (j + 1) + 1 by omega]; ring,
      show (N - j) * fs wlk = fs wlk + (N - (j + 1)) * fs wlk by
        rw [show N - j = N - (j + 1) + 1 by omega]; ring,
      List.range'_succ, List.flatMap_cons]
    exact this

end
end LeanVM.Guest.B1
