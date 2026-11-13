/-
  LeanVM.Guest.B1.Opening.QueriesPlacedP3

  `opening_queries` placed with its pops (`RelAtInP`): its odd first query's, then its loop's.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedP2
public import LeanVM.Guest.B1.Opening.QueriesPlaced10

/-!
# `opening_queries`, placed with its pops

`QueriesPlaced9`'s and `QueriesPlaced10`'s proofs with `relAtInP_of_walk` and `KidsFromInP`, the body's pops from `QueriesPops` (`oqMainA_splicePops`, `splice_of_body`).

* `oqMainPops`: the odd first query's row and walk's children, or nothing;
* `oqMain_relAtInP`: the function pops those, then its loop's;
* `oqMain1_placedP`, `oqMain0_placedP`: assembled, the loop's iterations' entries in order.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The odd first query's entries**: its row and walk's children (none when `odd ≠ 1`). -/
def oqMainPops (s : Oq) (odd : ℕ) (cap flags : E) (rounds : List FoldRound) (hsv : List E) (w : QW) (bp : E) :
    List Pop :=
  if odd = 1 then ("merkle_leaf_rows", (oqQD s 13 true 0 cap flags rounds hsv w).rowVals) ::
    ((oqQD s 13 true 0 cap flags rounds hsv w).wd bp).wpPops else []

/-- The tail after the loop's call walks to its return, calling and popping nothing. -/
theorem oqMainPost_walk (σ : Val) (rd : Reader) (s : Oq) (k : ℕ) :
    ∃ es vs, walk σ (oqMainPost s k ++ [.ret [.n (oqMainRet s k)]]) = .ret es vs ∧ calls es = [] ∧
      evPops rd σ es = [] := by
  unfold oqMainPost oqMainRet
  split
  · exact ⟨[.atom (.const (.n (k + 3)) (word 0 0))], [.n (k + 3)], by simp [walk, walk1, Out.seq, Out.pre], rfl, rfl⟩
  · exact ⟨[.atom (.mul (.n (k + 3)) (.n 10) (.n 7)), .atom (.load (.n (k + 4)) (.n (k + 3)) 0),
      .atom (.copy (.n (k + 5)) (.n (k + 4)))], [.n (k + 5)], by simp [walk, walk1, Out.seq, Out.pre], rfl, rfl⟩

/-- **`opening_queries`, placed, with its pops**: its odd first query's (`oqMainPops`), then its loop's `kl` (`[]`
when the loop is skipped). -/
theorem oqMain_relAtInP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) {odd : ℕ}
    (hodd : odd ≤ 1) {name wlk loop : String} (hW : WalkFn coreProgram wlk s.pd s.cd) {fm : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hbm : fm.body = oqMainT s odd wlk loop)
    {rd : Reader} {R : ℕ → Prop} {fp N m : ℕ} (hN : N + 1 < ordG)
    {cap flags lamInv coefs hsp positions qptrs : E} {rounds : List FoldRound} {hsv : List E}
    {w : QW} {bp hNv : E} {kl : List Pop}
    (h1 : odd = 1 → LoadHolds rd positions 0 (eOfNat w.1) ∧ LoadHolds rd qptrs 0 bp ∧
      (oqQD s 13 true 0 cap flags rounds hsv w).Ok rd coefs hsp bp ∧
      LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 (oqResV s rounds w * lamInv) ∧
      OqIn R (positions.limb 0 * Parameters.addressOfIndex 0) ∧
      OqIn R (qptrs.limb 0 * Parameters.addressOfIndex 0) ∧ OqQReg R s cap flags coefs hsp bp w.1)
    (h0 : odd ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 0)
    (hNl : s.final ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) N hNv)
    (hloop : if 1 + gen ^ N ≠ 0 then
      RelAtInP coreProgram fs cert rd (fun i ↦ R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (N + 1)))
        (fun _ ↦ False) (fp + fs name + (N + 1) + odd * fs wlk) m loop
        [1, gen ^ N, positions, qptrs, cap, flags, coefs, hsp,
          ofK (Parameters.addressOfIndex (fp + fs name)), lamInv] [] kl
      else m = fs loop ∧ kl = []) :
    RelAtInP coreProgram fs cert rd R (fun _ ↦ False) fp (fs name + (N + 1) + odd * fs wlk + m) name
      [cap, flags, lamInv, coefs, hsp, positions, qptrs, gen ^ N]
      [if s.final = 1 then 0 else hNv] (oqMainPops s odd cap flags rounds hsv w bp ++ kl) := by
  set ch0 : E := ofK (Parameters.addressOfIndex (fp + fs name)) with hch0
  set D := oqQD s 13 true 0 cap flags rounds hsv w with hD
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ v : V, σ v = oqMainF s odd
      [cap, flags, lamInv, coefs, hsp, positions, qptrs, gen ^ N] ch0 bp D
      (oqMainRest s ch0 (gen ^ N) hNv) v.idx := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hpar, e9, e10, eT, eodd, hA⟩ := oqMain_at (σ := σ) (walk := wlk) hs hfin hodd
    (fun h ↦ ⟨(h1 h).1, (h1 h).2.1, (h1 h).2.2.1, (h1 h).2.2.2.1⟩) h0
    (oqMainRest s ch0 (gen ^ N) hNv) (fun _ ↦ hσ _)
  set k := oqMK s odd with hk
  have t : ∀ o, σ (.n (k + o)) =
      (oqMainTl (gen ^ N) (oqMainRest s ch0 (gen ^ N) hNv)).getD o 0 := eT
  have t1 : σ (.n (k + 1)) = 1 + gen ^ N := by rw [t 1]; simp [oqMainTl, word_one]
  have t2 : σ (.n (k + 2)) = 1 := by rw [t 2]; simp [oqMainTl, word_one]
  have t3 : σ (.n (k + 3)) = (oqMainRest s ch0 (gen ^ N) hNv).getD 0 0 := by rw [t 3]; rfl
  have t4 : σ (.n (k + 4)) = (oqMainRest s ch0 (gen ^ N) hNv).getD 1 0 := by rw [t 4]; rfl
  have t5 : σ (.n (k + 5)) = (oqMainRest s ch0 (gen ^ N) hNv).getD 2 0 := by rw [t 5]; rfl
  have eP : ∀ i < 8, σ (.n i) = [cap, flags, lamInv, coefs, hsp, positions, qptrs, gen ^ N].getD i 0 := by
    intro i hi
    have := congrArg (·.getD i 0) hpar
    interval_cases i <;> simpa using this
  have hret : σ (.n (oqMainRet s k)) = if s.final = 1 then 0 else hNv := by
    unfold oqMainRet
    split
    · rename_i hf
      rw [t3]; simp [oqMainRest, hf, word_zero]
    · rename_i hf
      rw [t5]; simp [oqMainRest, hf]
  -- the body
  set ca : Stmt := .callIf (.n (k + 1)) loop
    [.n (k + 2), .n 7, .n 5, .n 6, .n 0, .n 1, .n 3, .n 4, .n 10, .n 2] with hca
  set post : List Stmt := oqMainPost s k with hpost
  have hpA : AllAtoms post := oqMainPost_atoms s k
  set pre := oqMainA s odd wlk ++ (ca :: post) with hpre
  have hok := oqMainA_ok s odd wlk
  have hflat : pre.all Stmt.flatM = true := by
    rw [hpre, List.all_append, hok.flatM, List.all_cons, hpost, oqMainPost_flatM]
    rfl
  have hmo : ∀ x ∈ pre, MatchOk σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hok.matchOk hA x hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · trivial
      · obtain ⟨a, rfl⟩ := hpA _ hx
        trivial
  have hbody : fm.body = pre ++ [.ret [.n (oqMainRet s k)]] := by
    rw [hbm, oqMainT_eq]
  set es := pre.flatMap (fmEvs σ) with hes
  have hw : walk σ fm.body = .ret es [.n (oqMainRet s k)] := by
    rw [hbody]; exact walk_flatM σ _ pre hflat hmo
  obtain ⟨i1, i2, i3, i4⟩ := flatM_parts σ pre hflat
  have hal : pre.filterMap Stmt.allocSz = [(.n 10, .inr (.n 9))] := by
    rw [hpre, List.filterMap_append, oqMainA_allocSz, List.filterMap_cons, hpost,
      oqMainPost_allocSz]
    rfl
  set a1 : List V := [.n (oqOut s (oqKL s 13 true) (s.B - 1) 0), .n (oqOut s (oqKL s 13 true) (s.B - 1) 1),
    .n 12, .n 0, .n 1] with ha1
  have hlogN : logG (σ (.n 9)) = N + 1 := by
    rw [e9, ← pow_succ, gen_pow_eq_ofK, logG_spec hN]
  have hallocs : allocs σ es = [N + 1] := by
    rw [i2, hal]; simp [hlogN]
  have hcalls : calls es = (if odd = 1 then [⟨wlk, a1, [], true⟩] else []) ++
      [⟨loop, [.n (k + 2), .n 7, .n 5, .n 6, .n 0, .n 1, .n 3, .n 4, .n 10, .n 2], [],
      decide (σ (.n (k + 1)) ≠ 0)⟩] := by
    rw [i4, hpre, List.filterMap_append, oqMainA_callS, List.filterMap_cons, callS_atoms hpA]
    split_ifs <;> rfl
  -- the chain's end
  have hpostH : ∀ a, Stmt.atom a ∈ post → a.Holds rd σ := by
    intro a ha
    rw [hpost, oqMainPost] at ha
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
      · show σ (.n (k + 3)) = σ (.n 10) * σ (.n 7)
        rw [u3, e10, eP 7 (by omega)]; rfl
      · show LoadHolds rd (σ (.n (k + 3))) 0 (σ (.n (k + 4)))
        rw [u3, u4, loadHolds_mul_gen_pow, Nat.add_zero]; exact hNl hf
      · show σ (.n (k + 5)) = σ (.n (k + 4))
        rw [u5, u4]
  -- the events hold
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    obtain ⟨x, hx, he⟩ := List.mem_flatMap.mp he
    rcases List.mem_append.mp hx with hx | hx
    · exact hok.evs_holds hA e (List.mem_flatMap.mpr ⟨x, hx, he⟩)
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
  -- the own data: the chain buffer
  have hbufd : ∀ i, fp + fs name ≤ i → i < fp + fs name + (N + 1) →
      ownData cert fp (fp + fs name) name (allocs σ es) es i := by
    intro i h1' h2'
    refine Or.inl ⟨(N + 1, fp + fs name), ?_, h1', by omega⟩
    rw [hallocs]; simp [bases]
  -- the pops
  set pss : List (List Pop) := (if odd = 1 then [(D.wd bp).wpPops] else []) ++ [kl] with hpss
  have hps : splice rd σ es pss = oqMainPops s odd cap flags rounds hsv w bp ++ kl := by
    have hx : SplicePops rd σ (oqMainA s odd wlk ++ [ca]) pss
        ((if odd = 1 then rowPop σ 13 s.I :: (D.wd bp).wpPops else []) ++ kl) :=
      (oqMainA_splicePops s odd wlk _ _ (by split_ifs; exacts [⟨_, rfl, rfl⟩, ⟨rfl, rfl⟩])).append
        (SplicePops.callIf _ _ _ kl)
    obtain ⟨es', vs', hy, hc', hp'⟩ := oqMainPost_walk σ rd s k
    rw [splice_of_body (by rw [hbody, hpre]; simp [hpost]) hx hy hc' hw, hp', List.append_nil]
    unfold oqMainPops
    split_ifs with ho
    · rw [show rowPop σ 13 s.I = rowPop σ D.b D.s.I from rfl, D.rowPop_vals (eodd ho).2.1]
    · rfl
  have h := relAtInP_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) hP
    (R := R) (D := fun _ ↦ False) (Dk := fun _ ↦ False) (fp := fp) (N := odd * fs wlk + (m + 0))
    (args := [cap, flags, lamInv, coefs, hsp, positions, qptrs, gen ^ N])
    (rets := [if s.final = 1 then 0 else hNv])
    hfm (Or.inl (fn_loop_main hfm hbm)) (by rw [hpm]; exact hpar) hw (by simp [hret]) hev
    (by rw [i1, hal, hallocs]; simp [bases, e10, hch0])
    (fun q hq ↦ ?_) ?_ (fun A hAl ↦ ?_) (fun _ h ↦ h.elim) hps
  · rw [hallocs] at h; simpa [Nat.add_assoc] using h
  · -- no frame address
    have hb : ∀ p run, oqAlloc ≠ .frameAddr p run := fun p run h ↦ by cases h
    rw [i3, hpre, List.filterMap_append, hok.addrS' hb, List.filterMap_cons, hpost,
      oqMainPost_addrS] at hq
    simp [hca, Stmt.addrS] at hq
  · -- the odd query's walk, the loop
    rw [hcalls]
    have hsum : (allocs σ es).sum = N + 1 := by rw [hallocs]; simp
    rw [hsum]
    have hloopK : ∀ Dacc : ℕ → Prop, KidsFromInP coreProgram fs cert rd σ
        (fun i ↦ R i ∨ ownData cert fp (fp + fs name) name (allocs σ es) es i) Dacc
        [⟨loop, [.n (k + 2), .n 7, .n 5, .n 6, .n 0, .n 1, .n 3, .n 4, .n 10, .n 2], [],
          decide (σ (.n (k + 1)) ≠ 0)⟩] [kl] (fp + fs name + (N + 1) + odd * fs wlk) (m + 0)
        (fun _ ↦ False) := by
      intro Dacc
      refine ⟨m, 0, (fun i ↦ R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (N + 1))), fun _ ↦ False,
        by omega, fun i hi ↦ ?_, ?_, ⟨rfl, fun _ h ↦ h.elim⟩⟩
      · rcases hi with hi | hi
        · exact Or.inl (Or.inl hi)
        · exact Or.inl (Or.inr (hbufd i hi.1 hi.2))
      · have hargs : ([.n (k + 2), .n 7, .n 5, .n 6, .n 0, .n 1, .n 3, .n 4, .n 10, .n 2] :
            List V).map σ = [1, gen ^ N, positions, qptrs, cap, flags, coefs, hsp, ch0, lamInv] := by
          simp only [List.map_cons, List.map_nil, t2, eP 7 (by omega), eP 5 (by omega),
            eP 6 (by omega), eP 0 (by omega), eP 1 (by omega), eP 3 (by omega), eP 4 (by omega),
            e10, eP 2 (by omega)]
          rfl
        by_cases ht : 1 + gen ^ N ≠ 0
        · have htk : decide (σ (.n (k + 1)) ≠ 0) = true := by rw [t1]; exact decide_eq_true ht
          simp only [htk, ↓reduceIte, List.map_nil]
          rw [hargs]
          split at hloop
          · exact hloop
          · next h' => exact absurd ht h'
        · have htk : decide (σ (.n (k + 1)) ≠ 0) = false := by rw [t1]; exact decide_eq_false ht
          simp only [htk, Bool.false_eq_true, ↓reduceIte]
          split at hloop
          · next h' => exact absurd h' ht
          · exact hloop
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hodd with rfl | rfl
    · simp only [hpss, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, List.nil_append, Nat.zero_mul,
        Nat.zero_add, Nat.add_zero] at hloopK ⊢
      exact hloopK _
    · obtain ⟨-, -, hokD, -, -, -, hreg⟩ := h1 rfl
      obtain ⟨e12, -, hl⟩ := eodd rfl
      have hW1 := wp_relAtInP (w := D.wd bp) hP fs cert hpd1 (show 1 ≤ s.cd by omega) hokD.hsibs
        hokD.hq hokD.hmem hW hreg.toW (fp + fs name + (N + 1))
      have hm1 : a1.map σ = [(digestHalves D.leaf).1, (digestHalves D.leaf).2, bp, cap, flags] := by
        have e0 := congrArg Prod.fst hl
        have e1 := congrArg Prod.snd hl
        simp only at e0 e1
        simp only [ha1, List.map_cons, List.map_nil, e0, e1, e12, eP 0 (by omega), eP 1 (by omega)]
        rfl
      simp only [hpss, ↓reduceIte, List.singleton_append, Nat.one_mul] at hloopK ⊢
      refine ⟨fs wlk, m + 0, R, fun _ ↦ False, rfl, fun i hi ↦ Or.inl (Or.inl hi), ?_, hloopK _⟩
      rw [ite_eq_left rfl, hm1]; exact hW1
  · -- the loads
    rw [loadAddrs_flatM σ pre hflat] at hAl
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hAl
    rw [hpre, List.filterMap_append] at hq
    have hb : ∀ d p off, oqAlloc ≠ .load d p off := fun d p off h ↦ by cases h
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok.load' hb hq with ⟨ho, hl⟩ | ⟨ho, rfl, rfl⟩ | ⟨ho, rfl, rfl⟩ | ⟨rfl, rfl⟩
      · subst ho
        obtain ⟨-, -, -, -, -, -, hreg⟩ := h1 rfl
        obtain ⟨i, hi, hr⟩ := oqQLoad_in (R := R) (σ := σ) (coefs := .n 3) (hs := .n 4)
          (by rw [eP 3 (by omega), eP 4 (by omega)]; exact hreg) hl
        exact ⟨i, hi, Or.inr (Or.inl hr)⟩
      · obtain ⟨i, hi, hr⟩ := (h1 ho).2.2.2.2.1
        rw [eP 5 (by omega)]
        exact ⟨i, hi, Or.inr (Or.inl hr)⟩
      · obtain ⟨i, hi, hr⟩ := (h1 ho).2.2.2.2.2.1
        rw [eP 6 (by omega)]
        exact ⟨i, hi, Or.inr (Or.inl hr)⟩
      · rw [e10, hch0, limb_ofK]
        exact ⟨fp + fs name, by simp, Or.inl (hbufd _ le_rfl (by omega))⟩
    · rw [List.filterMap_cons] at hq
      simp only [hca, stmtLoad?] at hq
      rw [hpost, oqMainPost] at hq
      split at hq
      · simp [stmtLoad?] at hq
      · rename_i hf
        simp only [stmtLoad?, List.filterMap_cons, List.filterMap_nil, List.mem_singleton,
          Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        have u3 : σ (.n (k + 3)) = ch0 * gen ^ N := by rw [t3]; simp [oqMainRest, hf]
        rw [u3, hch0, addr_gpow]
        exact ⟨_, rfl, Or.inl (hbufd _ (by omega) (by omega))⟩

/-- **`opening_queries` at level 0, placed, with its pops**: its odd first query's, then its iterations'. -/
theorem oqMain1_placedP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) {odd : ℕ}
    (hodd : odd ≤ 1) {name wlk loop : String} (hW : WalkFn coreProgram wlk s.pd s.cd) {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hbm : fm.body = oqMainT s odd wlk loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd wlk loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N : ℕ} (hN : N + 1 < ordG)
    {cap flags lamInv coefs hsp positions qptrs : E} {rounds : List FoldRound} {hsv : List E}
    {w : QW} {bp hNv : E}
    (h1 : odd = 1 → LoadHolds rd positions 0 (eOfNat w.1) ∧ LoadHolds rd qptrs 0 bp ∧
      (oqQD s 13 true 0 cap flags rounds hsv w).Ok rd coefs hsp bp ∧
      LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 (oqResV s rounds w * lamInv) ∧
      OqIn R (positions.limb 0 * Parameters.addressOfIndex 0) ∧
      OqIn R (qptrs.limb 0 * Parameters.addressOfIndex 0) ∧ OqQReg R s cap flags coefs hsp bp w.1)
    (h0 : odd ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 0)
    (hNl : s.final ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) N hNv)
    {w1 w2 : ℕ → QW} {bp1 bp2 v : ℕ → E}
    (hit : ∀ j < N, OqIt1Ok rd (oqLoopR R (fp + fs name) (N + 1)) s odd j positions qptrs cap flags
      coefs hsp (ofK (Parameters.addressOfIndex (fp + fs name))) lamInv rounds hsv
      (w1 j) (w2 j) (bp1 j) (bp2 j) (v j)) :
    RelAtInP coreProgram fs cert rd R (fun _ ↦ False) fp
      (fs name + (N + 1) + odd * fs wlk + ((N + 1) * fs loop + N * (2 * fs wlk)))
      name [cap, flags, lamInv, coefs, hsp, positions, qptrs, gen ^ N]
      [if s.final = 1 then 0 else hNv]
      (oqMainPops s odd cap flags rounds hsv w bp ++
        (List.range N).flatMap fun j => oqIt1Pops s cap flags rounds hsv (w1 j) (w2 j) (bp1 j) (bp2 j)) := by
  refine oqMain_relAtInP hP fs cert hs hfin hpd1 hcd hodd hW hfm hpm hbm hN h1 h0 hNl ?_
  by_cases hN0 : N = 0
  · subst hN0
    have : ¬ (1 + gen ^ 0 ≠ 0) := fun h ↦ (one_add_gen_pow hN).mp h rfl
    split
    · next h => exact absurd h this
    · exact ⟨by ring, by simp⟩
  · have hne : 1 + gen ^ N ≠ 0 := (one_add_gen_pow hN).mpr hN0
    split
    · have := oqLoop1_relAtInP (fp := fp + fs name + (N + 1) + odd * fs wlk) hP fs cert hs hfin hpd1
        hcd hW hfl hpl hbl hlp (by omega : N < ordG) hit (by omega)
      simp only [pow_zero] at this
      exact this
    · next h => exact absurd hne h

/-- **`opening_queries` deeper, placed, with its pops**: its iterations'. -/
theorem oqMain0_placedP (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd)
    {name wlk loop : String} (hW : WalkFn coreProgram wlk s.pd s.cd) {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hbm : fm.body = oqMainT s 0 wlk loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s wlk loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N : ℕ} (hN : N + 1 < ordG)
    {cap flags lamInv coefs hsp positions qptrs : E} {rounds : List FoldRound} {hsv : List E}
    {hNv : E}
    (h0 : LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 0)
    (hNl : s.final ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) N hNv)
    {w : ℕ → QW} {bp v : ℕ → E}
    (hit : ∀ j < N, OqIt0Ok rd (oqLoopR R (fp + fs name) (N + 1)) s j positions qptrs cap flags
      coefs hsp (ofK (Parameters.addressOfIndex (fp + fs name))) lamInv rounds hsv (w j) (bp j)
      (v j)) :
    RelAtInP coreProgram fs cert rd R (fun _ ↦ False) fp
      (fs name + (N + 1) + 0 * fs wlk + ((N + 1) * fs loop + N * fs wlk))
      name [cap, flags, lamInv, coefs, hsp, positions, qptrs, gen ^ N]
      [if s.final = 1 then 0 else hNv]
      ((List.range N).flatMap fun j => oqIt0Pops s cap flags rounds hsv (w j) (bp j)) := by
  have h := oqMain_relAtInP (R := R) (m := (N + 1) * fs loop + N * fs wlk) (cap := cap) (flags := flags)
    (lamInv := lamInv) (coefs := coefs) (hsp := hsp) (positions := positions) (qptrs := qptrs)
    (rounds := rounds) (hsv := hsv) (w := (0, [], [])) (bp := 0)
    (kl := (List.range N).flatMap fun j => oqIt0Pops s cap flags rounds hsv (w j) (bp j)) hP fs cert hs
    hfin hpd1 hcd (by omega) hW hfm hpm hbm hN (fun h ↦ absurd h (by decide)) (fun _ ↦ h0) hNl ?_
  · rw [show oqMainPops s 0 cap flags rounds hsv (0, [], []) 0 = [] from rfl, List.nil_append] at h
    exact h
  by_cases hN0 : N = 0
  · subst hN0
    have : ¬ (1 + gen ^ 0 ≠ 0) := fun h ↦ (one_add_gen_pow hN).mp h rfl
    split
    · next h => exact absurd h this
    · exact ⟨by ring, by simp⟩
  · have hne : 1 + gen ^ N ≠ 0 := (one_add_gen_pow hN).mpr hN0
    split
    · have := oqLoop0_relAtInP (fp := fp + fs name + (N + 1)) hP fs cert hs hfin hpd1 hcd hW
        hfl hpl hbl hlp (by omega : N < ordG) hit (by omega)
      simp only [pow_zero] at this
      rw [Nat.zero_mul, Nat.add_zero]
      exact this
    · next h => exact absurd hne h

end
end LeanVM.Guest.B1
