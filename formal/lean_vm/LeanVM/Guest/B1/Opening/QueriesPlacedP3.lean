/-
  LeanVM.Guest.B1.Opening.QueriesPlacedP3

  `opening_queries` placed with its pops (`RelAtInP`): its odd first query's, then its loop's.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedP2

/-!
# `opening_queries`, placed with its pops

The body is flat but for level 0's branch on `odd_g + 1` (`walk_ite_flatM`, `ite_parts`): its
parts are those of the start with the branch taken (`oqStartFlat`), the loop's call and the end.

* `oqMainPops`: the odd first query's entries, or nothing;
* `oqMain_relAtInP`: the function pops those, then its loop's;
* `oqMain1_placedP`, `oqMain0_placedP`: assembled, the loop's iterations' entries in order, by a
  tree of `fs name + (N + 1) + N·fs loop + fs (tailKey loop)` words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The odd first query's entries** (none when `odd ≠ 1`). -/
def oqMainPops (s : Oq) (odd : ℕ) (w : QW) : List Pop := if odd = 1 then oqQE s w else []

/-- The tail after the loop's call walks to its return, calling and popping nothing. -/
theorem oqMainEnd_walk (σ : Val) (rd : Reader) (s : Oq) (k : ℕ) :
    ∃ es vs, walk σ (oqMainEnd s k ++ [.ret [.n (oqMainRet s k)]]) = .ret es vs ∧ calls es = [] ∧
      evPops rd σ es = [] := by
  unfold oqMainEnd oqMainRet
  split
  · exact ⟨[.atom (.const (.n (k + 3)) (word 0 0))], [.n (k + 3)], by simp [walk, walk1, Out.seq, Out.pre], rfl, rfl⟩
  · exact ⟨[.atom (.mul (.n (k + 3)) (.n 11) (.n oqMN)), .atom (.load (.n (k + 4)) (.n (k + 3)) 0),
      .atom (.copy (.n (k + 5)) (.n (k + 4)))], [.n (k + 5)], by simp [walk, walk1, Out.seq, Out.pre], rfl, rfl⟩

/-- **`opening_queries`, placed, with its pops**: its odd first query's (`oqMainPops`), then its
loop's `kl` (`[]` when the loop is skipped). -/
theorem oqMain_relAtInP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) {cd odd : ℕ} (hodd : odd ≤ s.base) {name loop : String}
    {fm : Fn} (hfm : coreProgram.find? name = some fm) (hpm : fm.params = oqMainParams)
    (hbm : fm.body = oqMainT s loop)
    {rd : Reader} {R : ℕ → Prop} {fp N m : ℕ} (hN : N + 1 < ordG)
    {cap flags lamInv coefs hsp positions qptrs : E} {rounds : List FoldRound} {hsv : List E}
    {w : QW} {bp hNv : E} {kl : List Pop}
    (h1 : odd = 1 → LoadHolds rd positions 0 (eOfNat w.1) ∧ LoadHolds rd qptrs 0 bp ∧
      (oqQD s cd 17 true 0 bp cap flags rounds hsv w).Ok rd coefs hsp ∧
      LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 (oqResV s rounds w * lamInv) ∧
      OqIn R (positions.limb 0 * Parameters.addressOfIndex 0) ∧
      OqIn R (qptrs.limb 0 * Parameters.addressOfIndex 0) ∧ OqQReg R s cap flags coefs hsp bp w.1)
    (h0 : odd ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 0)
    (hNl : s.final ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) N hNv)
    (hloop : if 1 + gen ^ N ≠ 0 then
      RelAtInP coreProgram fs cert rd (fun i ↦ R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (N + 1)))
        (fun _ ↦ False) (fp + fs name + (N + 1)) m loop
        [1, gen ^ N, if s.base = 1 then positions * gen ^ odd else positions,
          if s.base = 1 then qptrs * gen ^ odd else qptrs, cap, flags, coefs, hsp,
          ofK (Parameters.addressOfIndex (fp + fs name)), lamInv] [] kl
      else m = fs (tailKey loop) ∧ kl = []) :
    RelAtInP coreProgram fs cert rd R (fun _ ↦ False) fp (fs name + (N + 1) + m) name
      [cap, flags, lamInv, coefs, hsp, positions, qptrs, gen ^ N, gen ^ odd]
      [if s.final = 1 then 0 else hNv] (oqMainPops s odd w ++ kl) := by
  set ch0 : E := ofK (Parameters.addressOfIndex (fp + fs name)) with hch0
  set D := oqQD s cd 17 true 0 bp cap flags rounds hsv w with hD
  set args : List E := [cap, flags, lamInv, coefs, hsp, positions, qptrs, gen ^ N, gen ^ odd] with hargs
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ v : V, σ v = oqMainF s args ch0 D
      (oqMainRest s ch0 (gen ^ N) hNv) v.idx := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hpar, e10, e11, eT, eb1, eodd, hA⟩ := oqMain_at (σ := σ) hs hfin hodd
    (fun h ↦ ⟨(h1 h).1, (h1 h).2.1, (h1 h).2.2.1, (h1 h).2.2.2.1⟩) h0
    (oqMainRest s ch0 (gen ^ N) hNv) (fun _ ↦ hσ _)
  set k := oqMK s with hk
  have hb01 : s.base = 0 ∨ s.base = 1 := by rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have t : ∀ o, σ (.n (k + o)) =
      (oqMainTl (gen ^ N) (oqMainRest s ch0 (gen ^ N) hNv)).getD o 0 := eT
  have t1 : σ (.n (k + 1)) = 1 + gen ^ N := by rw [t 1]; simp [oqMainTl, word_one]
  have t2 : σ (.n (k + 2)) = 1 := by rw [t 2]; simp [oqMainTl, word_one]
  have t3 : σ (.n (k + 3)) = (oqMainRest s ch0 (gen ^ N) hNv).getD 0 0 := by rw [t 3]; rfl
  have t4 : σ (.n (k + 4)) = (oqMainRest s ch0 (gen ^ N) hNv).getD 1 0 := by rw [t 4]; rfl
  have t5 : σ (.n (k + 5)) = (oqMainRest s ch0 (gen ^ N) hNv).getD 2 0 := by rw [t 5]; rfl
  have eP : ∀ i < 9, σ (.n i) = args.getD i 0 := by
    intro i hi
    have := congrArg (·.getD i 0) hpar
    simp only [oqMainParams] at this
    interval_cases i <;> simpa [hargs] using this
  have hret : σ (.n (oqMainRet s k)) = if s.final = 1 then 0 else hNv := by
    unfold oqMainRet
    split
    · rename_i hf
      rw [t3]; simp [oqMainRest, hf, word_zero]
    · rename_i hf
      rw [t5]; simp [oqMainRest, hf]
  -- the odd query is taken exactly at `odd = 1`
  have hodd1 : odd ≤ 1 := by omega
  have h13 : s.base = 1 → (σ (.n 13) = 0 ↔ odd ≠ 1) := fun hb ↦ by
    rw [(eb1 hb).1, gen_pow_add_one hodd1]; omega
  set even : Bool := decide (σ (.n 13) = 0) with heven
  have hodd_even : s.base = 1 → even = false → odd = 1 := fun hb he ↦ by
    by_contra hne
    have := (h13 hb).mpr hne
    simp [heven, this] at he
  -- the body's flat parts
  set ca : Stmt := .callIf (.n (k + 1)) loop (oqCallArgs s) with hca
  set en : List Stmt := oqMainEnd s k with hen
  have hpA : AllAtoms en := oqMainEnd_atoms s k
  set fl := oqStartFlat s even ++ ca :: en with hfl
  have hok := oqStart_ok s even
  have hst : BlockOkC anyCall rd σ (oqStartFlat s even) := by
    unfold OqStartOk at hA
    unfold oqStartFlat
    split
    · rename_i hb
      simp only [hb, ↓reduceIte] at hA
      obtain ⟨hpp, -, hz, hn⟩ := hA
      obtain ⟨hpre, hpost⟩ := blockOkC_append.mp hpp
      refine blockOkC_append.mpr ⟨blockOkC_append.mpr ⟨hpre, ?_⟩, hpost⟩
      by_cases h0 : σ (.n 13) = 0
      · simp only [heven, h0, decide_true, ↓reduceIte]; exact hz h0
      · simp only [heven, h0, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hn h0
    · rename_i hb
      simp only [hb, ↓reduceIte] at hA
      exact hA
  have hflF : fl.all Stmt.flatM = true := by
    rw [hfl, List.all_append, hok.flatM, List.all_cons, hen, oqMainEnd_flatM]; rfl
  have hmoF : ∀ x ∈ fl, MatchOk σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hok.matchOk hst x hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · trivial
      · obtain ⟨a, rfl⟩ := hpA _ hx
        trivial
  -- the end's atoms
  have hpostH : ∀ a, Stmt.atom a ∈ en → a.Holds rd σ := by
    intro a ha
    rw [hen, oqMainEnd] at ha
    split at ha
    · rename_i hf
      simp only [List.mem_singleton, Stmt.atom.injEq] at ha
      subst ha
      show σ (.n (k + 3)) = word 0 0
      rw [t3]; simp [oqMainRest, hf]
    · rename_i hf
      simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      have u3 : σ (.n (k + 3)) = ch0 * gen ^ N := by rw [t3]; simp [oqMainRest, hf]
      have u4 : σ (.n (k + 4)) = hNv := by rw [t4]; simp [oqMainRest, hf]
      have u5 : σ (.n (k + 5)) = hNv := by rw [t5]; simp [oqMainRest, hf]
      rcases ha with rfl | rfl | rfl
      · show σ (.n (k + 3)) = σ (.n 11) * σ (.n oqMN)
        rw [u3, e11, eP 7 (by omega)]; rfl
      · show LoadHolds rd (σ (.n (k + 3))) 0 (σ (.n (k + 4)))
        rw [u3, u4, loadHolds_mul_gen_pow, Nat.add_zero]; exact hNl hf
      · show σ (.n (k + 5)) = σ (.n (k + 4))
        rw [u5, u4]
  have hFev : ∀ e ∈ fl.flatMap (fmEvs σ), e.Holds rd σ := by
    intro e he
    obtain ⟨x, hx, he⟩ := List.mem_flatMap.mp he
    rcases List.mem_append.mp hx with hx | hx
    · exact hok.evs_holds hst e (List.mem_flatMap.mpr ⟨x, hx, he⟩)
    · rcases List.mem_cons.mp hx with rfl | hx
      · change e ∈ slEvs σ ca at he
        simp only [hca, slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | he
        · show IsInK (σ (.n (k + 1)))
          rw [t1, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
        · rw [he]; split <;> trivial
      · obtain ⟨a, rfl⟩ := hpA _ hx
        simp only [fmEvs, slEvs, List.mem_singleton] at he
        subst he
        exact hpostH a hx
  -- the walk
  have hwalk : ∃ es, walk σ fm.body = .ret es [.n (oqMainRet s k)] ∧
      allocDsts es = allocDsts (fl.flatMap (fmEvs σ)) ∧ allocs σ es = allocs σ (fl.flatMap (fmEvs σ)) ∧
      addrs es = addrs (fl.flatMap (fmEvs σ)) ∧ calls es = calls (fl.flatMap (fmEvs σ)) ∧
      loadAddrs σ es = loadAddrs σ (fl.flatMap (fmEvs σ)) ∧ ∀ e ∈ es, e.Holds rd σ := by
    by_cases hb : s.base = 1
    · have hsf : oqStartFlat s even = oqMainPre ++ (if σ (.n 13) = 0 then oqEvenT else oqOddT s) ++
          oqMainPost s := by
        unfold oqStartFlat
        rw [ite_eq_left hb]
        by_cases h0 : σ (.n 13) = 0
        · rw [show even = true by rw [heven]; exact decide_eq_true h0, ite_eq_left rfl, ite_eq_left h0]
        · rw [show even = false by rw [heven]; exact decide_eq_false h0, ite_eq_right (by decide), ite_eq_right h0]
      have hbody : fm.body = oqMainPre ++ .ite (.n 13) oqEvenT (oqOddT s) ::
          ((oqMainPost s ++ ca :: en) ++ [.ret [.n (oqMainRet s k)]]) := by
        rw [hbm, oqMainT_eq, oqMainA_one hb]
        simp only [List.append_assoc, List.cons_append, ← hk, hca, hen]
      have hsub : ∀ x, x ∈ oqMainPre ∨ x ∈ (if σ (.n 13) = 0 then oqEvenT else oqOddT s) ∨
          x ∈ oqMainPost s ++ ca :: en → x ∈ fl := by
        intro x hx
        rw [hfl, hsf]
        rcases hx with hx | hx | hx
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx))
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx))
        · rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append_left _ (List.mem_append_right _ hx)
          · exact List.mem_append_right _ hx
      have hal : ∀ l : List Stmt, (∀ x ∈ l, x ∈ fl) → l.all Stmt.flatM = true ∧ ∀ x ∈ l, MatchOk σ x :=
        fun l hl ↦ ⟨List.all_eq_true.mpr fun x hx ↦ List.all_eq_true.mp hflF x (hl x hx),
          fun x hx ↦ hmoF x (hl x hx)⟩
      obtain ⟨b1, b2⟩ := hal _ fun x hx ↦ hsub x (Or.inr (Or.inl hx))
      obtain ⟨p1, p2⟩ := hal _ fun x hx ↦ hsub x (Or.inr (Or.inr hx))
      obtain ⟨q1, q2⟩ := hal _ fun x hx ↦ hsub x (Or.inl hx)
      have hw := walk_ite_flatM σ (.n 13) oqEvenT (oqOddT s) (oqMainPost s ++ ca :: en)
        [.n (oqMainRet s k)] b1 b2 p1 p2 oqMainPre q1 q2
      obtain ⟨i1, i2, i3, i4, i5⟩ := ite_parts σ (.n 13) oqMainPre
        (if σ (.n 13) = 0 then oqEvenT else oqOddT s) (oqMainPost s ++ ca :: en)
      have hfl' : fl = oqMainPre ++ (if σ (.n 13) = 0 then oqEvenT else oqOddT s) ++
          (oqMainPost s ++ ca :: en) := by rw [hfl, hsf, List.append_assoc]
      refine ⟨_, by rw [hbody]; exact hw, ?_, ?_, ?_, ?_, ?_, fun e he ↦ ?_⟩
      · rw [i1, hfl']
      · rw [i2, hfl']
      · rw [i3, hfl']
      · rw [i4, hfl']
      · rw [i5, hfl']
      · have hsubE : ∀ e, e ∈ oqMainPre.flatMap (fmEvs σ) ∨
            e ∈ (if σ (.n 13) = 0 then oqEvenT else oqOddT s).flatMap (fmEvs σ) ∨
            e ∈ (oqMainPost s ++ ca :: en).flatMap (fmEvs σ) → e ∈ fl.flatMap (fmEvs σ) := by
          intro e h
          rw [hfl', List.flatMap_append, List.flatMap_append]
          rcases h with h | h | h
          · exact List.mem_append_left _ (List.mem_append_left _ h)
          · exact List.mem_append_left _ (List.mem_append_right _ h)
          · exact List.mem_append_right _ h
        rcases List.mem_append.mp he with he | he
        · exact hFev e (hsubE e (Or.inl he))
        · rcases List.mem_cons.mp he with rfl | he
          · show IsInK (σ (.n 13))
            rw [(eb1 hb).1, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
          · rcases List.mem_append.mp he with he | he
            · exact hFev e (hsubE e (Or.inr (Or.inl he)))
            · exact hFev e (hsubE e (Or.inr (Or.inr he)))
    · have hbody : fm.body = fl ++ [.ret [.n (oqMainRet s k)]] := by
        rw [hbm, oqMainT_eq, hfl, oqStartFlat, ite_eq_right hb]
        simp only [List.append_assoc, List.cons_append, ← hk, hca, hen]
      exact ⟨_, by rw [hbody]; exact walk_flatM σ _ fl hflF hmoF, rfl, rfl, rfl, rfl, rfl, hFev⟩
  obtain ⟨es, hw, i1, i2, i3, i4, i5, hev⟩ := hwalk
  obtain ⟨j1, j2, j3, j4⟩ := flatM_parts σ fl hflF
  have hal : fl.filterMap Stmt.allocSz = [(.n 11, .inr (.n 10))] := by
    rw [hfl, List.filterMap_append, oqStart_allocSz, List.filterMap_cons, hen, oqMainEnd_allocSz]
    rfl
  have hlogN : logG (σ (.n 10)) = N + 1 := by
    rw [e10, ← pow_succ, gen_pow_eq_ofK, logG_spec hN]
  have hallocs : allocs σ es = [N + 1] := by
    rw [i2, j2, hal]; simp [hlogN]
  have hcalls : calls es = [⟨loop, oqCallArgs s, [], decide (σ (.n (k + 1)) ≠ 0)⟩] := by
    rw [i4, j4, hfl, List.filterMap_append, oqStart_callS, List.filterMap_cons, callS_atoms hpA]
    rfl
  -- the own data: the chain buffer
  have hbufd : ∀ i, fp + fs name ≤ i → i < fp + fs name + (N + 1) →
      ownData cert fp (fp + fs name) name (allocs σ es) es i := by
    intro i h1' h2'
    refine Or.inl ⟨(N + 1, fp + fs name), ?_, h1', by omega⟩
    rw [hallocs]; simp [bases]
  -- the pops
  have hps : splice rd σ es [kl] = oqMainPops s odd w ++ kl := by
    have hsel : s.base = 1 → σ (.n 13) ≠ 0 → WinSel σ s (oqCh s 17 true) := fun hb h ↦ by
      have ho : odd = 1 := by by_contra hne; exact h ((h13 hb).mpr hne)
      exact D.winSel (eodd ho).2
    have hx : SplicePops rd σ (oqMainA s ++ [ca]) ([] ++ [kl]) (startPops σ s ++ kl) :=
      (SplicePops.of_fallPops (oqMainA_fallPops s hsel)).append (SplicePops.callIf _ _ _ kl)
    obtain ⟨es', vs', hy, hc', hp'⟩ := oqMainEnd_walk σ rd s k
    rw [show [kl] = [] ++ [kl] from rfl, splice_of_body (by rw [hbm, oqMainT_eq]; simp only [List.append_assoc, List.cons_append, List.nil_append, ← hk, hca])
      hx hy hc' hw, hp', List.append_nil]
    unfold startPops oqMainPops
    by_cases ho : odd = 1
    · have hb : s.base = 1 := by omega
      have h13' : σ (.n 13) ≠ 0 := fun h ↦ ((h13 hb).mp h) ho
      rw [ite_eq_left ⟨hb, h13'⟩, ite_eq_left ho, show queryPops σ s 17 true = queryPops σ D.s D.b D.emit from rfl,
        D.queryPops_vals (eodd ho).2, oqQE_eq]
    · rw [ite_eq_right ho, ite_eq_right]
      rintro ⟨hb, h⟩
      exact h ((h13 hb).mpr ho)
  have h := relAtInP_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) hP
    (R := R) (D := fun _ ↦ False) (Dk := fun _ ↦ False) (fp := fp) (N := m + 0)
    (args := args) (rets := [if s.final = 1 then 0 else hNv]) (pss := [kl])
    hfm (Or.inl (fn_loop_main hfm hbm)) (by rw [hpm]; exact hpar) hw (by simp [hret]) hev
    (by rw [i1, j1, hal, hallocs]; simp [bases, e11, hch0])
    (fun q hq ↦ ?_) ?_ (fun A hAl ↦ ?_) (fun _ h ↦ h.elim) hps
  · rw [hallocs] at h; simpa [Nat.add_assoc] using h
  · -- no frame address
    have hb : ∀ p run, oqAlloc ≠ .frameAddr p run := fun p run h ↦ by cases h
    rw [i3, j3, hfl, List.filterMap_append, hok.addrS' hb, List.filterMap_cons, hen,
      oqMainEnd_addrS] at hq
    simp [hca, Stmt.addrS] at hq
  · -- the loop
    rw [hcalls]
    have hsum : (allocs σ es).sum = N + 1 := by rw [hallocs]; simp
    rw [hsum]
    refine ⟨m, 0, (fun i ↦ R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (N + 1))), fun _ ↦ False,
      by omega, fun i hi ↦ ?_, ?_, ⟨rfl, fun _ h ↦ h.elim⟩⟩
    · rcases hi with hi | hi
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr (hbufd i hi.1 hi.2))
    · have hargs' : (oqCallArgs s).map σ = [1, gen ^ N, if s.base = 1 then positions * gen ^ odd else positions,
          if s.base = 1 then qptrs * gen ^ odd else qptrs, cap, flags, coefs, hsp, ch0, lamInv] := by
        by_cases hb : s.base = 1
        · simp only [oqCallArgs, hb, ↓reduceIte, List.map_cons, List.map_nil, ← hk, t2, (eb1 hb).2.1,
            (eb1 hb).2.2, eP 7 (by omega), eP 0 (by omega), eP 1 (by omega), eP 3 (by omega),
            eP 4 (by omega), e11, eP 2 (by omega)]
          rfl
        · simp only [oqCallArgs, hb, ↓reduceIte, List.map_cons, List.map_nil, ← hk, t2,
            eP 7 (by omega), eP 5 (by omega), eP 6 (by omega), eP 0 (by omega), eP 1 (by omega),
            eP 3 (by omega), eP 4 (by omega), e11, eP 2 (by omega)]
          rfl
      by_cases ht : 1 + gen ^ N ≠ 0
      · have htk : decide (σ (.n (k + 1)) ≠ 0) = true := by rw [t1]; exact decide_eq_true ht
        simp only [htk, ↓reduceIte, List.map_nil]
        rw [hargs']
        split at hloop
        · exact hloop
        · next h' => exact absurd ht h'
      · have htk : decide (σ (.n (k + 1)) ≠ 0) = false := by rw [t1]; exact decide_eq_false ht
        simp only [htk, Bool.false_eq_true, ↓reduceIte]
        split at hloop
        · next h' => exact absurd h' ht
        · exact hloop
  · -- the loads
    rw [i5, loadAddrs_flatM σ fl hflF] at hAl
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hAl
    rw [hfl, List.filterMap_append] at hq
    have hb : ∀ d p off, oqAlloc ≠ .load d p off := fun d p off h ↦ by cases h
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok.load' hb hq with ⟨hb1, he, hl⟩ | ⟨hb1, he, rfl, rfl⟩ | ⟨hb1, he, rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have ho := hodd_even hb1 he
        obtain ⟨-, -, -, -, -, -, hreg⟩ := h1 ho
        obtain ⟨e16, hvD⟩ := eodd ho
        obtain ⟨i, hi, hr⟩ := oqQLoad_in (R := R) (d := D) hvD (coefs := .n oqMCoefs) (hs := .n oqMHs)
          (bp := .n 16) (by rw [eP 3 (by omega), eP 4 (by omega), e16]; exact hreg) hl
        exact ⟨i, hi, Or.inr (Or.inl hr)⟩
      · obtain ⟨i, hi, hr⟩ := (h1 (hodd_even hb1 he)).2.2.2.2.1
        rw [eP 5 (by omega)]
        exact ⟨i, hi, Or.inr (Or.inl hr)⟩
      · obtain ⟨i, hi, hr⟩ := (h1 (hodd_even hb1 he)).2.2.2.2.2.1
        rw [eP 6 (by omega)]
        exact ⟨i, hi, Or.inr (Or.inl hr)⟩
      · rw [e11, hch0, limb_ofK]
        exact ⟨fp + fs name, by simp, Or.inl (hbufd _ le_rfl (by omega))⟩
    · rw [List.filterMap_cons] at hq
      simp only [hca, stmtLoad?] at hq
      rw [hen, oqMainEnd] at hq
      split at hq
      · simp [stmtLoad?] at hq
      · rename_i hf
        simp only [stmtLoad?, List.filterMap_cons, List.filterMap_nil, List.mem_singleton,
          Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        have u3 : σ (.n (k + 3)) = ch0 * gen ^ N := by rw [t3]; simp [oqMainRest, hf]
        rw [u3, hch0, addr_gpow]
        exact ⟨_, rfl, Or.inl (hbufd _ (by omega) (by omega))⟩

/-- **`opening_queries` at level 0, placed, with its pops**: its odd first query's, then its
iterations'. -/
theorem oqMain1_placedP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hb1 : s.base = 1) {cd odd : ℕ} (hodd : odd ≤ 1)
    {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm) (hpm : fm.params = oqMainParams)
    (hbm : fm.body = oqMainT s loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N : ℕ} (hN : N + 1 < ordG)
    {cap flags lamInv coefs hsp positions qptrs : E} {rounds : List FoldRound} {hsv : List E}
    {w : QW} {bp hNv : E}
    (h1 : odd = 1 → LoadHolds rd positions 0 (eOfNat w.1) ∧ LoadHolds rd qptrs 0 bp ∧
      (oqQD s cd 17 true 0 bp cap flags rounds hsv w).Ok rd coefs hsp ∧
      LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 (oqResV s rounds w * lamInv) ∧
      OqIn R (positions.limb 0 * Parameters.addressOfIndex 0) ∧
      OqIn R (qptrs.limb 0 * Parameters.addressOfIndex 0) ∧ OqQReg R s cap flags coefs hsp bp w.1)
    (h0 : odd ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 0)
    (hNl : s.final ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) N hNv)
    {w1 w2 : ℕ → QW} {bp1 bp2 v : ℕ → E}
    (hit : ∀ j < N, OqIt1Ok rd (oqLoopR R (fp + fs name) (N + 1)) s cd j (positions * gen ^ odd)
      (qptrs * gen ^ odd) cap flags coefs hsp (ofK (Parameters.addressOfIndex (fp + fs name))) lamInv
      rounds hsv (w1 j) (w2 j) (bp1 j) (bp2 j) (v j)) :
    RelAtInP coreProgram fs cert rd R (fun _ ↦ False) fp
      (fs name + (N + 1) + (N * fs loop + fs (tailKey loop)))
      name [cap, flags, lamInv, coefs, hsp, positions, qptrs, gen ^ N, gen ^ odd]
      [if s.final = 1 then 0 else hNv]
      (oqMainPops s odd w ++ (List.range N).flatMap fun j => oqQE s (w1 j) ++ oqQE s (w2 j)) := by
  refine oqMain_relAtInP hP fs cert hs hfin (cd := cd) (by omega) hfm hpm hbm hN h1 h0 hNl ?_
  by_cases hN0 : N = 0
  · subst hN0
    have : ¬ (1 + gen ^ 0 ≠ 0) := fun h ↦ (one_add_gen_pow hN).mp h rfl
    split
    · next h => exact absurd h this
    · exact ⟨by ring, by simp⟩
  · have hne : 1 + gen ^ N ≠ 0 := (one_add_gen_pow hN).mpr hN0
    split
    · have := oqLoop1_relAtInP (fp := fp + fs name + (N + 1)) hP fs cert hs hfin hfl hpl hbl hlp
        (by omega : N < ordG) hit (by omega)
      simp only [pow_zero] at this
      exact this
    · next h => exact absurd hne h

/-- **`opening_queries` deeper, placed, with its pops**: its iterations'. -/
theorem oqMain0_placedP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hb0 : s.base = 0) {cd : ℕ}
    {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm) (hpm : fm.params = oqMainParams)
    (hbm : fm.body = oqMainT s loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N : ℕ} (hN : N + 1 < ordG)
    {cap flags lamInv coefs hsp positions qptrs : E} {rounds : List FoldRound} {hsv : List E}
    {hNv : E}
    (h0 : LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 0)
    (hNl : s.final ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) N hNv)
    {w : ℕ → QW} {bp v : ℕ → E}
    (hit : ∀ j < N, OqIt0Ok rd (oqLoopR R (fp + fs name) (N + 1)) s cd j positions qptrs cap flags
      coefs hsp (ofK (Parameters.addressOfIndex (fp + fs name))) lamInv rounds hsv (w j) (bp j)
      (v j)) :
    RelAtInP coreProgram fs cert rd R (fun _ ↦ False) fp
      (fs name + (N + 1) + (N * fs loop + fs (tailKey loop)))
      name [cap, flags, lamInv, coefs, hsp, positions, qptrs, gen ^ N, gen ^ 0]
      [if s.final = 1 then 0 else hNv]
      ((List.range N).flatMap fun j => oqQE s (w j)) := by
  have h := oqMain_relAtInP (R := R) (m := N * fs loop + fs (tailKey loop)) (cap := cap) (flags := flags)
    (lamInv := lamInv) (coefs := coefs) (hsp := hsp) (positions := positions) (qptrs := qptrs)
    (rounds := rounds) (hsv := hsv) (w := (0, [], [])) (bp := 0) (cd := cd) (odd := 0)
    (kl := (List.range N).flatMap fun j => oqQE s (w j)) hP fs cert hs
    hfin (by omega) hfm hpm hbm hN (fun h ↦ absurd h (by decide)) (fun _ ↦ h0) hNl ?_
  · rw [show oqMainPops s 0 (0, [], []) = [] from rfl, List.nil_append] at h
    exact h
  by_cases hN0 : N = 0
  · subst hN0
    have : ¬ (1 + gen ^ 0 ≠ 0) := fun h ↦ (one_add_gen_pow hN).mp h rfl
    split
    · next h => exact absurd h this
    · exact ⟨by ring, by simp⟩
  · have hne : 1 + gen ^ N ≠ 0 := (one_add_gen_pow hN).mpr hN0
    split
    · have := oqLoop0_relAtInP (fp := fp + fs name + (N + 1)) hP fs cert hs hfin hfl hpl hbl hlp
        (by omega : N < ordG) hit (by omega)
      simp only [pow_zero] at this
      have e1 : (if s.base = 1 then positions * gen ^ 0 else positions) = positions := by simp [hb0]
      have e2 : (if s.base = 1 then qptrs * gen ^ 0 else qptrs) = qptrs := by simp [hb0]
      rw [e1, e2]
      exact this
    · next h => exact absurd hne h

end
end LeanVM.Guest.B1
