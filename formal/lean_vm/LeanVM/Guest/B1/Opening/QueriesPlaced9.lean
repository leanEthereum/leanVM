/-
  LeanVM.Guest.B1.Opening.QueriesPlaced9

  `opening_queries` placed (`RelAtIn`): the function's own frame, its chain buffer, its loop.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced8

/-!
# The function, placed

`oqMain_relAtIn`: `opening_queries` on `(cap, flags, λ, λ_n, qptrs, wp, g^N)` at its honest values
(`oqMainF`), placed at `fp`: its chain buffer of `N + 1` words at `fp + fs name` (its `HeapBuf`),
its loop right after the buffer (`relAtIn_of_walk`, the body flat: `walk_flatM`), the loop given
placed and loading from `R` and the buffer; it returns the chain's end times `λ_n`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem fn_loop_main {s : Oq} {odd : ℕ} {name wlk loop : String} {fm : Fn}
    (hfm : coreProgram.find? name = some fm) (hbm : fm.body = oqMainT s odd wlk loop) :
    coreProgram.loop name = false := by
  rw [Program.loop_of_find? hfm, Fn.loop, hbm]
  simp [oqMainT]

/-- **`opening_queries`, placed**: its chain buffer after its frame, its odd first query's walk
after it, then its loop's tree (`m` words). -/
theorem oqMain_relAtIn (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) {odd : ℕ} (hodd : odd ≤ 1)
    {name wlk loop : String} (hW : WalkFn wlk s.pd s.cd) {fm : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s odd wlk loop)
    {rd : Reader} {R : ℕ → Prop} {fp N m : ℕ} (hN : N + 1 < ordG)
    {cap flags lam lamN qptrs wp : E} (hlam : lam ≠ 0)
    {r : List K} {w : ℕ → E} {q : ℕ} {sb : List Digest} {bp hNv : E}
    (h1 : odd = 1 → LoadHolds rd qptrs 0 bp ∧
      (⟨s, 13, true, 0, r, w, q, sb, cap, flags⟩ : QD).Ok rd wp bp ∧
      LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 (rowDot s.base s.I r w *
          lam⁻¹) ∧
      OqIn R (qptrs.limb 0 * Parameters.addressOfIndex 0) ∧ OqQReg R s cap flags wp bp q)
    (h0 : odd ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 0)
    (hNl : LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) N hNv)
    (hloop : if 1 + gen ^ N ≠ 0 then
      RelAtIn coreProgram fs cert rd (fun i ↦ R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (N + 1)))
        (fun _ ↦ False) (fp + fs name + (N + 1) + odd * fs wlk) m loop
        [1, gen ^ N, qptrs, cap, flags, wp, ofK (Parameters.addressOfIndex (fp + fs name)),
            lam⁻¹] []
      else m = fs loop) :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp (fs name + (N + 1) + odd * fs wlk + m) name
      [cap, flags, lam, lamN, qptrs, wp, gen ^ N] [hNv * lamN] := by
  set ch0 : E := ofK (Parameters.addressOfIndex (fp + fs name)) with hch0
  set D : QD := ⟨s, 13, true, 0, r, w, q, sb, cap, flags⟩ with hD
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, ∀ v : V, σ v = oqMainF s odd [cap, flags, lam, lamN, qptrs, wp, gen ^ N]
      ch0 bp D [ch0 * gen ^ N, hNv, hNv * lamN] v.idx := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨hpar, e8, e10, e11, eT, eodd, hA⟩ := oqMain_at (σ := σ) (walk := wlk) hs hodd hlam
    (fun h ↦ ⟨(h1 h).1, (h1 h).2.1, (h1 h).2.2.1⟩) h0
    [ch0 * gen ^ N, hNv, hNv * lamN] (fun _ ↦ hσ _)
  set k := oqMK s odd with hk
  have t : ∀ o, σ (.n (k + o)) = (oqMainTl (gen ^ N) [ch0 * gen ^ N, hNv, hNv * lamN]).getD o 0 := eT
  have t1 : σ (.n (k + 1)) = 1 + gen ^ N := by rw [t 1]; simp [oqMainTl, word_one]
  have t2 : σ (.n (k + 2)) = 1 := by rw [t 2]; simp [oqMainTl, word_one]
  have t3 : σ (.n (k + 3)) = ch0 * gen ^ N := by rw [t 3]; rfl
  have t4 : σ (.n (k + 4)) = hNv := by rw [t 4]; rfl
  have t5 : σ (.n (k + 5)) = hNv * lamN := by rw [t 5]; rfl
  have eP : ∀ i < 7, σ (.n i) = [cap, flags, lam, lamN, qptrs, wp, gen ^ N].getD i 0 := by
    intro i hi
    have := congrArg (·.getD i 0) hpar
    interval_cases i <;> simpa using this
  -- the body
  set ca : Stmt := .callIf (.n (k + 1)) loop [.n (k + 2), .n 6, .n 4, .n 0, .n 1, .n 5, .n 11, .n 8]
    with hca
  set post : List Stmt := [.atom (.mul (.n (k + 3)) (.n 11) (.n 6)),
    .atom (.load (.n (k + 4)) (.n (k + 3)) 0), .atom (.mul (.n (k + 5)) (.n (k + 4)) (.n 3))]
    with hpost
  set pre := oqMainA s odd wlk ++ (ca :: post) with hpre
  have hok := oqMainA_ok s odd wlk
  have hflat : pre.all Stmt.flatM = true := by
    rw [hpre, List.all_append, hok.flatM]; rfl
  have hmo : ∀ x ∈ pre, MatchOk σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hok.matchOk hA x hx
    · simp only [hpost, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> trivial
  have hbody : fm.body = pre ++ [.ret [.n (k + 5)]] := by
    rw [hbm, hpre, oqMainT]; simp [hca, hpost, hk]
  set es := pre.flatMap (fmEvs σ) with hes
  have hw : walk σ fm.body = .ret es [.n (k + 5)] := by
    rw [hbody]; exact walk_flatM σ _ pre hflat hmo
  obtain ⟨i1, i2, i3, i4⟩ := flatM_parts σ pre hflat
  have hal : pre.filterMap Stmt.allocSz = [(.n 11, .inr (.n 10))] := by
    rw [hpre, List.filterMap_append, oqMainA_allocSz]; rfl
  set a1 : List V := [.n (oqOut s (oqKL s 13 true) (s.B - 1) 0), .n (oqOut s (oqKL s 13 true) (s.B - 1) 1),
    .n 12, .n 0, .n 1] with ha1
  have hlogN : logG (σ (.n 10)) = N + 1 := by
    rw [e10, ← pow_succ, gen_pow_eq_ofK, logG_spec hN]
  have hallocs : allocs σ es = [N + 1] := by
    rw [i2, hal]; simp [hlogN]
  have hcalls : calls es = (if odd = 1 then [⟨wlk, a1, [], true⟩] else []) ++
      [⟨loop, [.n (k + 2), .n 6, .n 4, .n 0, .n 1, .n 5, .n 11, .n 8], [],
      decide (σ (.n (k + 1)) ≠ 0)⟩] := by
    rw [i4, hpre, List.filterMap_append, oqMainA_callS]
    split_ifs <;> rfl
  -- the events hold
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    obtain ⟨x, hx, he⟩ := List.mem_flatMap.mp he
    rcases List.mem_append.mp hx with hx | hx
    · exact hok.evs_holds hA e (List.mem_flatMap.mpr ⟨x, hx, he⟩)
    · simp only [hpost, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · change e ∈ slEvs σ ca at he
        simp only [hca, slEvs, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | he
        · show IsInK (σ (.n (k + 1)))
          rw [t1, gen_pow_eq_ofK, ← ofK_one, ← ofK_add]; exact ofK_isInK _
        · rw [he]; split <;> trivial
      · simp only [fmEvs, slEvs, List.mem_singleton] at he
        subst he
        show σ (.n (k + 3)) = σ (.n 11) * σ (.n 6)
        rw [t3, e11, eP 6 (by omega)]; rfl
      · simp only [fmEvs, slEvs, List.mem_singleton] at he
        subst he
        show LoadHolds rd (σ (.n (k + 3))) 0 (σ (.n (k + 4)))
        rw [t3, t4, loadHolds_mul_gen_pow, Nat.add_zero]; exact hNl
      · simp only [fmEvs, slEvs, List.mem_singleton] at he
        subst he
        show σ (.n (k + 5)) = σ (.n (k + 4)) * σ (.n 3)
        rw [t5, t4, eP 3 (by omega)]; rfl
  -- the own data: the chain buffer
  have hbufd : ∀ i, fp + fs name ≤ i → i < fp + fs name + (N + 1) →
      ownData cert fp (fp + fs name) name (allocs σ es) es i := by
    intro i h1' h2'
    refine Or.inl ⟨(N + 1, fp + fs name), ?_, h1', by omega⟩
    rw [hallocs]; simp [bases]
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) hP
    (R := R) (D := fun _ ↦ False) (Dk := fun _ ↦ False) (fp := fp) (N := odd * fs wlk + (m + 0))
    (args := [cap, flags, lam, lamN, qptrs, wp, gen ^ N]) (rets := [hNv * lamN])
    hfm (Or.inl (fn_loop_main hfm hbm)) (by rw [hpm]; exact hpar) hw (by simp [t5]) hev
    (by rw [i1, hal, hallocs]; simp [bases, e11, hch0])
    (fun q hq ↦ ?_) ?_ (fun A hAl ↦ ?_) (fun _ h ↦ h.elim)
  · rw [hallocs] at h; simpa [Nat.add_assoc] using h
  · -- no frame address
    have hb : ∀ p run, oqAlloc ≠ .frameAddr p run := fun p run h ↦ by cases h
    rw [i3, hpre, List.filterMap_append, hok.addrS' hb] at hq
    simp [hca, hpost, Stmt.addrS] at hq
  · -- the odd query's walk, the loop
    rw [hcalls]
    have hsum : (allocs σ es).sum = N + 1 := by rw [hallocs]; simp
    rw [hsum]
    have hloopK : KidsFromIn coreProgram fs cert rd σ
        (fun i ↦ R i ∨ ownData cert fp (fp + fs name) name (allocs σ es) es i)
        (fun i ↦ False ∨ (odd = 1 ∧ False))
        [⟨loop, [.n (k + 2), .n 6, .n 4, .n 0, .n 1, .n 5, .n 11, .n 8], [],
          decide (σ (.n (k + 1)) ≠ 0)⟩] (fp + fs name + (N + 1) + odd * fs wlk) (m + 0)
        (fun _ ↦ False) := by
      refine ⟨m, 0, (fun i ↦ R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (N + 1))), fun _ ↦ False,
        by omega, fun i hi ↦ ?_, ?_, ⟨rfl, fun _ h ↦ h.elim⟩⟩
      · rcases hi with hi | hi
        · exact Or.inl (Or.inl hi)
        · exact Or.inl (Or.inr (hbufd i hi.1 hi.2))
      · have hargs : ([.n (k + 2), .n 6, .n 4, .n 0, .n 1, .n 5, .n 11, .n 8] : List V).map σ =
            [1, gen ^ N, qptrs, cap, flags, wp, ch0, lam⁻¹] := by
          simp only [List.map_cons, List.map_nil, t2, eP 6 (by omega), eP 4 (by omega),
            eP 0 (by omega), eP 1 (by omega), eP 5 (by omega), e11, e8]
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
    · simp only [show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, List.nil_append, Nat.zero_mul,
        Nat.zero_add, Nat.add_zero] at hloopK ⊢
      exact kidsFromIn_dacc _ (fun i hi ↦ by simp at hi) hloopK
    · obtain ⟨-, hokD, -, -, hreg⟩ := h1 rfl
      obtain ⟨e12, -, hl⟩ := eodd rfl
      have hW1 := wp_relAtIn (w := D.wd bp) hP fs cert hpd1 (show 1 ≤ s.cd by omega) hokD.hsibs hokD.hq
        hokD.hmem hW hreg.toW (fp + fs name + (N + 1))
      have hm1 : a1.map σ = [(digestHalves D.leaf).1, (digestHalves D.leaf).2, bp, cap, flags] := by
        have e0 := congrArg Prod.fst hl
        have e1 := congrArg Prod.snd hl
        simp only at e0 e1
        simp only [ha1, List.map_cons, List.map_nil, e0, e1, e12, eP 0 (by omega), eP 1 (by omega)]
        rfl
      simp only [↓reduceIte, List.singleton_append, Nat.one_mul] at hloopK ⊢
      refine kidsFromIn_walk (R0 := R) (by rw [hm1]; exact hW1) (fun i hi ↦ Or.inl (Or.inl hi)) ?_
      exact kidsFromIn_dacc _ (fun i hi ↦ by simp at hi) hloopK
  · -- the loads
    rw [loadAddrs_flatM σ pre hflat] at hAl
    obtain ⟨⟨p, off⟩, hq, rfl⟩ := List.mem_map.mp hAl
    rw [hpre, List.filterMap_append] at hq
    have hb : ∀ d p off, oqAlloc ≠ .load d p off := fun d p off h ↦ by cases h
    rcases List.mem_append.mp hq with hq | hq
    · rcases hok.load' hb hq with ⟨ho, hl⟩ | ⟨ho, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · subst ho
        obtain ⟨-, -, -, -, hreg⟩ := h1 rfl
        obtain ⟨i, hi, hr⟩ := oqQLoad_in (R := R) (σ := σ) (wp := .n 5)
          (by rw [eP 5 (by omega)]; exact hreg) hl
        exact ⟨i, hi, Or.inr (Or.inl hr)⟩
      · obtain ⟨i, hi, hr⟩ := (h1 ho).2.2.2.1
        rw [eP 4 (by omega)]
        exact ⟨i, hi, Or.inr (Or.inl hr)⟩
      · rw [e11, hch0, limb_ofK]
        exact ⟨fp + fs name, by simp, Or.inl (hbufd _ le_rfl (by omega))⟩
      · rw [t3, hch0, addr_gpow]
        exact ⟨_, rfl, Or.inl (hbufd _ (by omega) (by omega))⟩
    · simp only [hca, hpost, stmtLoad?, List.filterMap_cons, List.filterMap_nil,
        List.mem_singleton, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      rw [t3, hch0, addr_gpow]
      exact ⟨_, rfl, Or.inl (hbufd _ (by omega) (by omega))⟩

end
end LeanVM.Guest.B1
