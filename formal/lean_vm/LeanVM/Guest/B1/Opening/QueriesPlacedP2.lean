/-
  LeanVM.Guest.B1.Opening.QueriesPlacedP2

  A deeper iteration of `opening_queries`' loop and the loop, placed with their pops.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedP

/-!
# The deeper loop, placed with its pops

`QueriesPlacedP`'s proofs at a deeper level (one query an iteration).

* `oqIter0_relAtInP`: a deeper iteration pops its query's entries, then its tail's;
* `oqLoop0_relAtInP`: the deeper loop pops its iterations', in order.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A deeper iteration, placed, with its pops**: its query's (`oqQE`), then its tail's `kn`
(`[]` after the last). -/
theorem oqIter0_relAtInP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp c Bt m cd j : ℕ} {N positions qptrs cap flags coefs hsp ch mu : E}
    {rounds : List FoldRound} {hsv : List E} {w : QW} {bp v : E} {kn : List Pop}
    (H : OqIt0Ok rd R s cd j positions qptrs cap flags coefs hsp ch mu rounds hsv w bp v)
    (hK : IsInK (gen ^ j * gen + N))
    (htail : if gen ^ j * gen + N ≠ 0 then
      RelAtInCP coreProgram fs cert rd R (fun _ => False) (fp + fs loop) c Bt m loop
        [gen ^ j * gen, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] [] kn
      else Bt = fs (tailKey loop) ∧ m = 0 ∧ kn = []) :
    RelAtInCP coreProgram fs cert rd R (fun _ => False) fp c (fs loop + Bt) m loop
      [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] []
      (oqQE s w ++ kn) := by
  set D := oqQD s cd 14 true 0 bp cap flags rounds hsv w with hD
  set args : List E := [gen ^ j, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] with hargs
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ w : V, σ w = oqIter0F s args D v w.idx :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hpar, hA, hv1, e10, e12, e13, eCh, eG2, eG4⟩ :=
    oqIter0_at (σ := σ) hs hfin H.ok H.x H.b H.chv (fun _ ↦ hσ _)
  have eP : ∀ i < 10, σ (.n i) = args.getD i 0 := by
    intro i hi
    have := congrArg (·.getD i 0) hpar
    simp only [oqLoopParams] at this
    interval_cases i <;> simpa [hargs] using this
  -- the body
  set ca : Stmt := .callIf (.n (oqG0 s + 2)) loop (oqNextArgs (oqG0 s)) with hca
  set pre := oqLoop0A s ++ [ca] with hpre
  have hok := oqLoop0A_ok s
  have hfm : pre.all Stmt.flatM = true := by
    rw [hpre, List.all_append, hok.flatM]; rfl
  have hmo : ∀ x ∈ pre, MatchOk σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hok.matchOk hA x hx
    · simp only [List.mem_singleton] at hx
      subst hx; trivial
  have hbody : fl.body = pre ++ [.ret []] := by
    rw [hbl, hpre, oqLoop0T, oqNextT_eq, List.append_assoc]; rfl
  set es := pre.flatMap (fmEvs σ) with hes
  have hw : walk σ fl.body = .ret es [] := by rw [hbody]; exact walk_flatM σ [] pre hfm hmo
  obtain ⟨i1, i2, i3, i4⟩ := flatM_parts σ pre hfm
  have hal : pre.filterMap Stmt.allocSz = [] := by
    rw [hpre, List.filterMap_append, hok.allocSz]; rfl
  have hallocs : allocs σ es = [] := by rw [i2, hal]; rfl
  have hcalls : calls es = [] ++ [⟨loop, oqNextArgs (oqG0 s), [], decide (σ (.n (oqG0 s + 2)) ≠ 0)⟩] := by
    rw [i4, hpre, List.filterMap_append, callS_flat (oqLoop0A_flat s)]; rfl
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
      · show IsInK (σ (.n (oqG0 s + 2)))
        rw [eG2]; exact hK
      · rw [he]; split <;> trivial
  -- the pops
  have hps : splice rd σ es ([] ++ [kn]) = oqQE s w ++ kn := by
    have hx : SplicePops rd σ pre ([] ++ [kn]) (queryPops σ s 14 true ++ kn) :=
      (SplicePops.of_fallPops (oqLoop0A_fallPops s (D.winSel hv1))).append
        (SplicePops.callIf _ _ _ kn)
    rw [splice_of_body hbody hx (show walk σ [.ret []] = .ret [] [] by simp [walk, walk1, Out.seq]) rfl hw,
      show queryPops σ s 14 true = queryPops σ D.s D.b D.emit from rfl, D.queryPops_vals hv1, oqQE_eq]
    simp [evPops]
  have inR : ∀ A, OqIn R A → ∃ i, A = Parameters.addressOfIndex i ∧
      (ownData cert fp c loop (allocs σ es) es i ∨ R i ∨ False ∨
        ((⟨loop, oqNextArgs (oqG0 s), [], decide (σ (.n (oqG0 s + 2)) ≠ 0)⟩ : Call).taken = true ∧
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
    have hargs' : (oqNextArgs (oqG0 s)).map σ =
        [gen ^ j * gen, N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] := by
      simp only [oqNextArgs, List.map_cons, List.map_nil, eG4, eP 1 (by omega), eP 2 (by omega),
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
  · -- no frame address
    rw [i3, hpre, List.filterMap_append, hok.addrS] at hq
    simp [hca, Stmt.addrS] at hq
  · -- the loads
    rw [loadAddrs_flatM σ pre hfm] at hAl
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hAl
    rw [hpre, List.filterMap_append] at hq
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok.load hq with hl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hf, rfl, rfl⟩ | ⟨hf, rfl, rfl⟩
      · exact inR _ (oqQLoad_in (d := D) hv1 (coefs := .n oqCoefs) (hs := .n oqHs) (bp := .n 13)
          (by rw [eP 6 (by omega), eP 7 (by omega), e13]; exact H.reg) hl)
      · rw [e10]; exact inR _ H.rp
      · rw [e12]; exact inR _ H.rq
      · rw [(eCh hf).1]; exact inR _ (H.rc hf 0 (by omega))
      · rw [(eCh hf).2]; exact inR _ (H.rc hf 1 (by omega))
    · simp [hca, stmtLoad?] at hq

/-- **The deeper loop, placed, with its pops**: entered at `g^0`, its frames at `fp` and its last
call's tail frame after them, it pops its iterations' entries in order. -/
theorem oqLoop0_relAtInP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N cd : ℕ} (hN : N < ordG)
    {positions qptrs cap flags coefs hsp ch mu : E} {rounds : List FoldRound} {hsv : List E}
    {w : ℕ → QW} {bp v : ℕ → E}
    (hit : ∀ j < N, OqIt0Ok rd R s cd j positions qptrs cap flags coefs hsp ch mu rounds hsv
      (w j) (bp j) (v j)) (hN0 : 0 < N) :
    RelAtInP coreProgram fs cert rd R (fun _ => False) fp (N * fs loop + fs (tailKey loop)) loop
      [gen ^ 0, gen ^ N, positions, qptrs, cap, flags, coefs, hsp, ch, mu] []
      ((List.range N).flatMap fun j => oqQE s (w j)) := by
  set it : ℕ → List Pop := fun j => oqQE s (w j) with hit'
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
    have := oqIter0_relAtInP (fp := fp + j * fs loop) (c := fp + B) (Bt := fs (tailKey loop))
      (m := 0) (kn := []) hP fs cert hs hfin hfl hpl hbl hlp (hit j (by omega)) hK
      (by
        split
        · next h => exact absurd (hne.mp h) (by omega)
        · exact ⟨rfl, rfl, rfl⟩)
    rw [show (N - j) * fs loop + fs (tailKey loop) = fs loop + fs (tailKey loop) by
        rw [show N - j = 1 by omega, Nat.one_mul],
      show (List.range' j (0 + 1)).flatMap it = oqQE s (w j) ++ [] by simp [hit']]
    exact this
  | succ n ih =>
    intro j hj
    obtain ⟨hK, hne⟩ := gen_pow_guard (j := j) hN (by omega)
    have ht := ih (j + 1) (by omega)
    rw [show fp + (j + 1) * fs loop = fp + j * fs loop + fs loop by ring, pow_succ] at ht
    have := oqIter0_relAtInP (fp := fp + j * fs loop) (c := fp + B)
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
