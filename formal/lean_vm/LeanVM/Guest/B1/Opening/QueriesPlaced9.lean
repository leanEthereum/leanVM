/-
  LeanVM.Guest.B1.Opening.QueriesPlaced9

  `opening_queries` placed (`RelAtIn`): the function's own frame, its chain buffer, its loop.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced8

/-!
# The function, placed

`oqMain_relAtIn`: `opening_queries` on `(cap, flags, λ⁻¹, coefs, hs, positions, qptrs, g^N)` at
its honest values (`oqMainF`), placed at `fp`: its chain buffer of `N + 1` words at `fp + fs name`
(its `HeapBuf`), its loop right after the buffer (`relAtIn_of_walk`, the body flat:
`walk_flatM`), the loop given placed and loading from `R` and the buffer; it returns the chain's
end, or `0` at the final level (`oqMainPost`, `oqMainRet`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem fn_loop_main {s : Oq} {odd : ℕ} {name wlk loop : String} {fm : Fn}
    (hfm : coreProgram.find? name = some fm) (hbm : fm.body = oqMainT s odd wlk loop) :
    coreProgram.loop name = false := by
  rw [Program.loop_of_find? hfm, Fn.loop, hbm]
  unfold oqMainT
  by_cases hf : s.final = 1 <;> simp [hf]

/-- The function's tail after its loop: the chain's end read and returned, or (final level) `0`. -/
def oqMainPost (s : Oq) (k : ℕ) : List Stmt :=
  if s.final = 1 then [.atom (.const (.n (k + 3)) (word 0 0))]
  else [.atom (.mul (.n (k + 3)) (.n 10) (.n 7)), .atom (.load (.n (k + 4)) (.n (k + 3)) 0),
    .atom (.copy (.n (k + 5)) (.n (k + 4)))]

/-- The function's returned value. -/
def oqMainRet (s : Oq) (k : ℕ) : ℕ := if s.final = 1 then k + 3 else k + 5

/-- The function's values after `1, 1 + nG, 1`: `0`, or the chain's end's pointer and value. -/
def oqMainRest (s : Oq) (ch nG hN : E) : List E :=
  if s.final = 1 then [word 0 0] else [ch * nG, hN, hN]

theorem oqMainT_eq (s : Oq) (odd : ℕ) (wlk loop : String) :
    oqMainT s odd wlk loop = (oqMainA s odd wlk ++
      (.callIf (.n (oqMK s odd + 1)) loop [.n (oqMK s odd + 2), .n 7, .n 5, .n 6, .n 0, .n 1, .n 3,
        .n 4, .n 10, .n 2] :: oqMainPost s (oqMK s odd))) ++ [.ret [.n (oqMainRet s (oqMK s odd))]] := by
  unfold oqMainT oqMainPost oqMainRet
  by_cases hf : s.final = 1 <;> simp [hf]

theorem oqMainPost_atoms (s : Oq) (k : ℕ) : AllAtoms (oqMainPost s k) := by
  unfold oqMainPost
  split
  · exact allAtoms_cons allAtoms_nil
  · exact allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil))

theorem oqMainPost_flatM (s : Oq) (k : ℕ) : (oqMainPost s k).all Stmt.flatM = true := by
  unfold oqMainPost; split <;> rfl

theorem oqMainPost_allocSz (s : Oq) (k : ℕ) : (oqMainPost s k).filterMap Stmt.allocSz = [] := by
  unfold oqMainPost; split <;> rfl

theorem oqMainPost_addrS (s : Oq) (k : ℕ) : (oqMainPost s k).filterMap Stmt.addrS = [] := by
  unfold oqMainPost; split <;> rfl

/-- **`opening_queries`, placed**: its chain buffer after its frame, its odd first query's walk
after it, then its loop's tree (`m` words). -/
theorem oqMain_relAtIn (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) {odd : ℕ}
    (hodd : odd ≤ 1) {name wlk loop : String} (hW : WalkFn wlk s.pd s.cd) {fm : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hbm : fm.body = oqMainT s odd wlk loop)
    {rd : Reader} {R : ℕ → Prop} {fp N m : ℕ} (hN : N + 1 < ordG)
    {cap flags lamInv coefs hsp positions qptrs : E} {rounds : List FoldRound} {hsv : List E}
    {w : QW} {bp hNv : E}
    (h1 : odd = 1 → LoadHolds rd positions 0 (eOfNat w.1) ∧ LoadHolds rd qptrs 0 bp ∧
      (oqQD s 13 true 0 cap flags rounds hsv w).Ok rd coefs hsp bp ∧
      LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 (oqResV s rounds w * lamInv) ∧
      OqIn R (positions.limb 0 * Parameters.addressOfIndex 0) ∧
      OqIn R (qptrs.limb 0 * Parameters.addressOfIndex 0) ∧ OqQReg R s cap flags coefs hsp bp w.1)
    (h0 : odd ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 0)
    (hNl : s.final ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) N hNv)
    (hloop : if 1 + gen ^ N ≠ 0 then
      RelAtIn coreProgram fs cert rd (fun i ↦ R i ∨ (fp + fs name ≤ i ∧ i < fp + fs name + (N + 1)))
        (fun _ ↦ False) (fp + fs name + (N + 1) + odd * fs wlk) m loop
        [1, gen ^ N, positions, qptrs, cap, flags, coefs, hsp,
          ofK (Parameters.addressOfIndex (fp + fs name)), lamInv] []
      else m = fs loop) :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp (fs name + (N + 1) + odd * fs wlk + m) name
      [cap, flags, lamInv, coefs, hsp, positions, qptrs, gen ^ N]
      [if s.final = 1 then 0 else hNv] := by
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
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) hP
    (R := R) (D := fun _ ↦ False) (Dk := fun _ ↦ False) (fp := fp) (N := odd * fs wlk + (m + 0))
    (args := [cap, flags, lamInv, coefs, hsp, positions, qptrs, gen ^ N])
    (rets := [if s.final = 1 then 0 else hNv])
    hfm (Or.inl (fn_loop_main hfm hbm)) (by rw [hpm]; exact hpar) hw (by simp [hret]) hev
    (by rw [i1, hal, hallocs]; simp [bases, e10, hch0])
    (fun q hq ↦ ?_) ?_ (fun A hAl ↦ ?_) (fun _ h ↦ h.elim)
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
    have hloopK : KidsFromIn coreProgram fs cert rd σ
        (fun i ↦ R i ∨ ownData cert fp (fp + fs name) name (allocs σ es) es i)
        (fun i ↦ False ∨ (odd = 1 ∧ False))
        [⟨loop, [.n (k + 2), .n 7, .n 5, .n 6, .n 0, .n 1, .n 3, .n 4, .n 10, .n 2], [],
          decide (σ (.n (k + 1)) ≠ 0)⟩] (fp + fs name + (N + 1) + odd * fs wlk) (m + 0)
        (fun _ ↦ False) := by
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
    · simp only [show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, List.nil_append, Nat.zero_mul,
        Nat.zero_add, Nat.add_zero] at hloopK ⊢
      exact kidsFromIn_dacc _ (fun i hi ↦ by simp at hi) hloopK
    · obtain ⟨-, -, hokD, -, -, -, hreg⟩ := h1 rfl
      obtain ⟨e12, -, hl⟩ := eodd rfl
      have hW1 := wp_relAtIn (w := D.wd bp) hP fs cert hpd1 (show 1 ≤ s.cd by omega) hokD.hsibs
        hokD.hq hokD.hmem hW hreg.toW (fp + fs name + (N + 1))
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

end
end LeanVM.Guest.B1
