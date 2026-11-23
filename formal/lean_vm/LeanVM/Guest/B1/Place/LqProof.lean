/-
  LeanVM.Guest.B1.Place.LqProof

  `level_queries` complete placed at every specialization: `level_queries_completeAt`.
-/

module

public import LeanVM.Guest.B1.Place.Lq
public import LeanVM.Guest.B1.Place.LpProof
public import LeanVM.Guest.B1.Place.OsMean
public import LeanVM.Guest.B1.Place.SqAt
public import LeanVM.Guest.B1.Opening.QueriesPlacedAll
public import LeanVM.Guest.B1.Whir.OqKey
public import LeanVM.Guest.B1.Whir.DataSpec
public import LeanVM.Guest.B1.Whir.HelperAll

/-!
# `level_queries`, placed

`lq_placed`: at every frame pointer, the specialization's walk is straight-line (the cap's and
the flags' `HeapBuf`s, their hints, `verify_merkle_cap`, `opening_queries`, `λ^q` by square and
multiply); on every memory holding its two buffers (the honest cap and flags) and the caller's
words, it relates its arguments to the root, the queries' sum and `λ^q`, its two callees placed
from their own placed statements (`kindD_holds`, `opening_queries_completeAtB`) by
`kidsFromIn_of_kidsD`. `level_queries_completeAt`: every entry of `lqTable`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-! ## The body -/

/-- The body before its `ret`. -/
abbrev lqPreB (q base folds leaf d cd mu nhs hbits fin : ℕ) : List Stmt :=
  lqBodyA q base folds leaf d cd mu nhs hbits fin

theorem lqBody_pre (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    lqBody q base folds leaf d cd mu nhs hbits fin =
      lqPreB q base folds leaf d cd mu nhs hbits fin ++
        [.ret [.n 19, .n 20, .n 21, .n (22 + osPowLen q)]] :=
  lqBody_split ..

theorem lqPreB_straight (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (lqPreB q base folds leaf d cd mu nhs hbits fin).all Main.Stmt.straight = true := by
  simp [lqBodyA, osHeap, os_powSteps_straight, Main.Stmt.straight]

theorem lqPreB_flat (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (lqPreB q base folds leaf d cd mu nhs hbits fin).all Whir.Stmt.flat = true :=
  lqBodyA_flat ..

theorem lq_pow_filterMap {β : Type} (f : Stmt → Option β) (hf : ∀ d a b, f (osMul d a b) = none)
    (ds : List Bool) (acc k : ℕ) : (osPowSteps 0 ds acc k).1.filterMap f = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro s hs
  obtain ⟨d, a, b, rfl⟩ := osPowSteps_mem_mul 0 ds acc k s hs
  exact hf d a b

theorem lqPreB_allocs (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (lqPreB q base folds leaf d cd mu nhs hbits fin).filterMap Main.Stmt.allocSz =
      [(.n 7, .inr (.n 6)), (.n 9, .inr (.n 8))] := by
  rw [lqPreB, lqBodyA, List.filterMap_append, List.filterMap_append,
    lq_pow_filterMap Main.Stmt.allocSz (fun _ _ _ ↦ rfl)]
  rfl

theorem lqPreB_addrs (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (lqPreB q base folds leaf d cd mu nhs hbits fin).filterMap Main.Stmt.addrS = [] := by
  rw [lqPreB, lqBodyA, List.filterMap_append, List.filterMap_append,
    lq_pow_filterMap Main.Stmt.addrS (fun _ _ _ ↦ rfl)]
  rfl

theorem lqPreB_calls (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (lqPreB q base folds leaf d cd mu nhs hbits fin).filterMap Main.Stmt.callS =
      [(none, "verify_merkle_cap__L" ++ natStr cd, [.n 7, .n 9], [.n 10, .n 11]),
        (none, oqName base folds leaf (d - cd) mu nhs hbits fin,
          [.n 13, .n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 16, .n 17], [.n 18])] := by
  rw [lqPreB, lqBodyA, List.filterMap_append, List.filterMap_append,
    lq_pow_filterMap Main.Stmt.callS (fun _ _ _ ↦ rfl)]
  rfl

theorem lqPreB_loads (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (lqPreB q base folds leaf d cd mu nhs hbits fin).filterMap Stmt.loadS = [] := by
  rw [lqPreB, lqBodyA, List.filterMap_append, List.filterMap_append,
    lq_pow_filterMap Stmt.loadS (fun _ _ _ ↦ rfl)]
  rfl

/-- **`level_queries` ends with its returns**: it is no loop helper. -/
theorem lq_notLoop {q base folds leaf d cd mu nhs hbits fin : ℕ} {name : String} {fn : Fn}
    (hf : coreProgram.find? name = some fn)
    (hb : fn.body = lqBody q base folds leaf d cd mu nhs hbits fin) :
    coreProgram.loop name = false := by
  rw [Program.loop_of_find? hf, Fn.loop, hb, lqBody_pre]
  simp

/-! ## Placed -/

theorem lq_cap_lt {pd cd x e : ℕ} (hx : x < 2 ^ (pd + cd)) (he : e < 2) :
    2 * (2 ^ cd + x / 2 ^ pd) + e < 4 * 2 ^ cd := by
  have : x / 2 ^ pd < 2 ^ cd := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm]; exact hx
  omega

theorem lq_flag_lt {pd cd x : ℕ} (hcd : 1 ≤ cd) (hx : x < 2 ^ (pd + cd)) :
    2 ^ (cd - 1) + x / 2 ^ (pd + 1) < 2 ^ cd := by
  have h2 : 2 ^ cd = 2 * 2 ^ (cd - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : x / 2 ^ (pd + 1) < 2 ^ (cd - 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    calc x < 2 ^ (pd + cd) := hx
      _ = 2 ^ (cd - 1 + (pd + 1)) := by congr 1; omega
  omega

/-- **`level_queries` at one specialization, placed.** -/
theorem lq_placed (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {name : String}
    {q base folds leaf d cd mu nhs hbits fin : ℕ}
    (hlq : FnIs name (osParams 6) (lqBody q base folds leaf d cd mu nhs hbits fin))
    (hoq : (lqOqN base folds leaf d cd mu nhs hbits fin,
      oqLoopOf (lqOqN base folds leaf d cd mu nhs hbits fin),
      oqShapeOf (lqOqN base folds leaf d cd mu nhs hbits fin)) ∈ openingQueriesLoops)
    (hQ : oqCount (Whir.lqOdd q base) (lqOqS base folds leaf d cd mu nhs hbits fin).base
      (lqIters q base) = q)
    (hN : lqIters q base + 1 < ordG)
    (hodd : Whir.lqOdd q base ≤ (lqOqS base folds leaf d cd mu nhs hbits fin).base)
    (hcd1 : 1 ≤ cd) (hcd8 : cd ≤ 8)
    (hK : osKindOf ("verify_merkle_cap__L" ++ natStr cd) = some (.cap cd))
    (hpw : digitsVal (osPowDigits q) 1 = q) :
    LqAtD fs cert κ name q base folds leaf d cd mu nhs hbits fin := by
  unfold LqAtD
  simp only [lqOqS, lqOqN] at hoq hQ hodd ⊢
  generalize hsh : oqShapeOf (oqName base folds leaf (d - cd) mu nhs hbits fin) = sh at hoq hQ hodd ⊢
  generalize hlp : oqLoopOf (oqName base folds leaf (d - cd) mu nhs hbits fin) = loop at hoq
  intro Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 hrl hhs hst
    hcaps hreg hmem fp
  obtain ⟨fn, hf, hps, hb⟩ := hlq
  have hnl : coreProgram.loop name = false := lq_notLoop hf hb
  obtain ⟨hcapL, hflL, hvmc, hcells⟩ := hcaps
  set N := lqIters q base with hNdef
  set odd := Whir.lqOdd q base with hodddef
  set oqn := oqName base folds leaf (d - cd) mu nhs hbits fin with hoqn
  set vmcN := "verify_merkle_cap__L" ++ natStr cd with hvmcN
  set sum := lqSum sh.oq odd N lamInv rounds qs rows with hsum
  set capE := fp + fs name with hcapE
  set flE := capE + 4 * 2 ^ cd with hflE
  set b := flE + 2 ^ cd with hbdef
  set ecap := capE + 2 ^ (cd + 1) with hecap
  set eflags := flE + 2 ^ (cd - 1) with heflags
  set CAP : E := ofK (addressOfIndex capE) with hCAP
  set FL : E := ofK (addressOfIndex flE) with hFL
  set cP : E := ofK (addressOfIndex ecoefs) with hcP
  set hP : E := ofK (addressOfIndex ehs) with hhP
  set pP : E := ofK (addressOfIndex epos) with hpP
  set qP : E := ofK (addressOfIndex eqp) with hqP
  set capsL : Layout := [(capE, capW), (flE, flW)] with hcapsL
  have h4 : 4 * 2 ^ cd ≤ 1024 := by
    have : 2 ^ cd ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) hcd8
    omega
  have hc1 : 2 ^ (cd + 1) = 2 * 2 ^ cd := by rw [pow_succ]; ring
  have hc2 : 2 ^ cd = 2 * 2 ^ (cd - 1) := by
    have e : cd = cd - 1 + 1 := by omega
    conv_lhs => rw [e]
    rw [pow_succ]; ring
  have hO : ordG = 2 ^ 64 - 1 := rfl
  have hU : u128Bound = 2 ^ 128 := rfl
  have hCAPm : ofK (addressOfIndex ecap) = CAP * gen ^ (2 ^ (cd + 1)) := by
    rw [hCAP, ofK_addr_mul_gen_pow]
  have hFLm : ofK (addressOfIndex eflags) = FL * gen ^ (2 ^ (cd - 1)) := by rw [hFL, ofK_addr_mul_gen_pow]
  have hCAPo' : CAP * gw (2 ^ (cd + 1)) = ofK (addressOfIndex ecap) := by
    rw [hCAPm, Whir.gw_eq (by rw [hU]; omega)]
  have hFLo' : FL * gw (2 ^ (cd - 1)) = ofK (addressOfIndex eflags) := by
    rw [hFLm, Whir.gw_eq (by rw [hU]; omega)]
  -- the kids
  set kv : Kid := ⟨vmcN, true, [CAP, FL], capsL, Returns [r0, r1]⟩ with hkv
  set ko : Kid := ⟨oqn, true, [ofK (addressOfIndex ecap), ofK (addressOfIndex eflags), lamInv, cP, hP,
    pP, qP, gen ^ N, gen ^ odd], Lin ++ capsL,
    Returns [sum]⟩ with hko
  have hkvD : CompleteAtD fs cert κ vmcN capsL [CAP, FL] (Returns [r0, r1]) := by
    have := kindD_holds (fs := fs) (cert := cert) (κ := κ) hK [CAP, FL] [r0, r1] capsL ?_ ?_
    · exact this
    · intro p hp t ht
      simp only [OsKind.spec, merkleCapSpec, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · refine ⟨capE + t, Main.addr_ofK _ _, (capE, capW), List.mem_cons_self, by omega, ?_⟩
        simp only at ht ⊢; rw [hcapL]; rw [pow_add] at ht; omega
      · refine ⟨flE + t, Main.addr_ofK _ _, (flE, flW), by simp [hcapsL], by omega, ?_⟩
        simp only at ht ⊢; rw [hflL]; omega
    · intro rd _ hm
      have h1 : ReadsAt rd CAP capW := hm (capE, capW) List.mem_cons_self
      have h2 : ReadsAt rd FL flW := hm (flE, flW) (List.mem_cons_of_mem _ List.mem_cons_self)
      exact hvmc rd CAP FL h1 h2
  have hkoD : CompleteAtD fs cert κ oqn (Lin ++ capsL)
      [ofK (addressOfIndex ecap), ofK (addressOfIndex eflags), lamInv, cP, hP, pP, qP, gen ^ N,
        gen ^ odd] (Returns [sum]) := by
    have hD := (opening_queries_completeAtB fs cert (oqn, loop, sh) hoq).toD trivial κ (Lin ++ capsL)
      N cd odd ecap eflags ecoefs ehs epos eqp lamInv rounds hsv eb qs rows sibs hcd1 hodd hN hrl hhs
      (by rw [hQ]; exact hst) ?_ ?_
    · have hs : (if sh.oq.final = 1 then 0 else oqChain odd sh.oq.base lamInv
          (fun k ↦ foldRow (lanesOf sh.oq.base (rows k)) (K.ofBits (qs k)) rounds) N) = sum := rfl
      rw [hs] at hD
      exact hD
    · rw [hQ]
      obtain ⟨hr1, hr2, hr3⟩ := hreg
      have hL : ∀ i, RegionL Lin i → RegionL (Lin ++ capsL) i := fun i ⟨q', hq, h1, h2⟩ ↦
        ⟨q', List.mem_append_left _ hq, h1, h2⟩
      refine ⟨fun l hl ↦ hL _ (hr1 l hl), fun hf l hl ↦ hL _ (hr2 hf l hl), fun k hk ↦ ?_⟩
      obtain ⟨p1, p2, p3⟩ := hr3 k hk
      have hqk := (hst k hk).1
      refine ⟨hL _ p1, hL _ p2, fun i hi ↦ hL _ (p3 i hi), ?_, fun e he ↦ ?_⟩
      · refine ⟨(flE, flW), List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self),
          Nat.le_add_right_of_le (Nat.le_add_right flE _), ?_⟩
        have := lq_flag_lt (pd := sh.oq.pd) (cd := cd) hcd1 hqk
        simp only [heflags]; rw [hflL]; omega
      · refine ⟨(capE, capW), List.mem_append_right _ List.mem_cons_self, Nat.le_add_right_of_le (Nat.le_add_right capE _), ?_⟩
        have := lq_cap_lt (pd := sh.oq.pd) (cd := cd) hqk he
        simp only [hecap]; rw [hcapL]; omega
    · intro rd hl hm
      obtain ⟨hmL, hmC⟩ := Main.memL_append.mp hm
      have hC : ReadsAt rd CAP capW := hmC (capE, capW) List.mem_cons_self
      have hF : ReadsAt rd FL flW := hmC (flE, flW) (List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨m1, m2, m3⟩ := hmem rd hl hmL
      rw [hQ]
      refine ⟨m1, m2, fun k hk ↦ ?_⟩
      obtain ⟨n1, n2, n3⟩ := m3 k hk
      obtain ⟨c1, c2, c3⟩ := hcells k hk
      have hqk := (hst k hk).1
      have hx0 := lq_cap_lt (pd := sh.oq.pd) (cd := cd) hqk (e := 0) (by omega)
      have hx1 := lq_cap_lt (pd := sh.oq.pd) (cd := cd) hqk (e := 1) (by omega)
      have hxf := lq_flag_lt (pd := sh.oq.pd) (cd := cd) hcd1 hqk
      refine ⟨n1, n2, n3, ?_, ?_, ?_⟩
      · rw [hCAPm, loadHolds_mul_gen_pow, ← c1,
          show 2 ^ (cd + 1) + 2 * (qs k / 2 ^ sh.oq.pd) = 2 * (2 ^ cd + qs k / 2 ^ sh.oq.pd) by omega,
          List.getD_eq_getElem _ _ (by rw [hcapL]; omega)]
        exact hC _ _
      · rw [hCAPm, loadHolds_mul_gen_pow, ← c2,
          show 2 ^ (cd + 1) + (2 * (qs k / 2 ^ sh.oq.pd) + 1) =
            2 * (2 ^ cd + qs k / 2 ^ sh.oq.pd) + 1 by omega,
          List.getD_eq_getElem _ _ (by rw [hcapL]; omega)]
        exact hC _ _
      · rw [hFLm, loadHolds_mul_gen_pow]
        have := hF (2 ^ (cd - 1) + qs k / 2 ^ (sh.oq.pd + 1)) (by rw [hflL]; exact hxf)
        rw [List.getElem_eq_getD 0, c3] at this
        exact this
  -- the kids placed
  obtain ⟨NK, LK, outs, hOk, hWK, hDK, -, hKK⟩ := kidsFromIn_of_kidsD (fs := fs) (cert := cert) κ
    [kv, ko] (fun k hk _ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact hkvD
      · exact hkoD) b
  obtain ⟨o1, o2, rfl⟩ : ∃ o1 o2, outs = [o1, o2] := by
    match outs, hOk with
    | [o1, o2], _ => exact ⟨o1, o2, rfl⟩
  obtain ⟨ho1, ho2, -⟩ := hOk
  obtain ⟨e11, e12⟩ := ho1 rfl
  obtain ⟨e21, e22⟩ := ho2 rfl
  -- the honest values
  set L := osPowLen q with hL
  set A : List E := [lam, lamInv, cP, hP, pP, qP, gw (4 * 2 ^ cd), CAP, gw (2 ^ cd), FL, r0, r1,
    gw (2 ^ (cd + 1)), CAP * gw (2 ^ (cd + 1)), gw (2 ^ (cd - 1)), FL * gw (2 ^ (cd - 1)), gw N,
    gw odd, sum, r0, r1, sum] with hA
  set PV := lqPowVals lam (osPowDigits q) 1 with hPV
  set vals : List E := A ++ (PV ++ [lam ^ q]) with hvals
  set σ : Val := fun v ↦ if v.path = [] ∧ v.tag = 0 then vals.getD v.idx 0 else 0 with hσ
  have hv : ∀ i, σ (.n i) = vals.getD i 0 := fun i ↦ by simp [hσ]
  have hAl : A.length = 22 := rfl
  have hpl : PV.length = L := by rw [hPV, lqPowVals_length, hL, osPowLen]
  have hvA : ∀ i < 22, σ (.n i) = A.getD i 0 := fun i hi ↦ by
    rw [hv, hvals, List.getD_append _ _ _ _ (by rw [hAl]; exact hi)]
  have hv22 : ∀ j < L, σ (.n (22 + j)) = PV.getD j 0 := by
    intro j hj
    rw [hv, hvals, List.getD_append_right _ _ _ _ (by rw [hAl]; omega), hAl,
      show 22 + j - 22 = j by omega, List.getD_append _ _ _ _ (by rw [hpl]; exact hj)]
  have hvk : σ (.n (22 + L)) = lam ^ q := by
    rw [hv, hvals, List.getD_append_right _ _ _ _ (by rw [hAl]; omega), hAl,
      show 22 + L - 22 = L by omega, List.getD_append_right _ _ _ _ (by rw [hpl]), hpl,
      Nat.sub_self]
    rfl
  have hv0 : σ (.n 0) = lam := hvA 0 (by omega)
  have hpow : ∀ rd : Reader, AllOk (fun _ _ _ ↦ True) rd σ (osPowSteps 0 (osPowDigits q) 0 22).1 ∧
      σ (.n (osPowSteps 0 (osPowDigits q) 0 22).2) = lam ^ q := fun rd ↦ by
    have h := lq_powSteps_complete (C := fun _ _ _ ↦ True) (rd := rd) (σ := σ) 0
      (osPowDigits q) 0 22 1 (by rw [pow_one]) (fun j hj ↦ by
        rw [hv0] at hj ⊢; exact hv22 j (by rw [← hpl]; exact hj))
    rw [hv0, hpw] at h
    exact h
  have hgi : gw N = gen ^ N := Whir.gw_eq (by rw [hU]; rw [hO] at hN; omega)
  have hgo : gw odd = gen ^ odd := Whir.gw_eq (by
    rw [hU, hodddef, Whir.lqOdd]; split_ifs <;> omega)
  -- the walk
  have hst' := lqPreB_straight q base folds leaf d cd mu nhs hbits fin
  have hwalk : walk σ fn.body = .ret ((lqPreB q base folds leaf d cd mu nhs hbits fin).flatMap
      (Main.slEvs σ)) [.n 19, .n 20, .n 21, .n (22 + osPowLen q)] := by
    rw [hb, lqBody_pre]; exact Main.walk_straight σ _ _ hst'
  set es := (lqPreB q base folds leaf d cd mu nhs hbits fin).flatMap (Main.slEvs σ) with hes_def
  obtain ⟨i1, i2, i3, i4⟩ := Main.straight_parts σ _ hst'
  have h6 : σ (.n 6) = gw (4 * 2 ^ cd) := hvA 6 (by omega)
  have h7 : σ (.n 7) = CAP := hvA 7 (by omega)
  have h8 : σ (.n 8) = gw (2 ^ cd) := hvA 8 (by omega)
  have h9 : σ (.n 9) = FL := hvA 9 (by omega)
  have hal : allocs σ es = [4 * 2 ^ cd, 2 ^ cd] := by
    rw [i2, lqPreB_allocs]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, h6, h8]
    rw [lp_logG_gw (by omega), lp_logG_gw (by omega)]
  have hcalls : calls es =
      [⟨vmcN, [.n 7, .n 9], [.n 10, .n 11], true⟩,
        ⟨oqn, [.n 13, .n 15, .n 1, .n 2, .n 3, .n 4, .n 5, .n 16, .n 17], [.n 18], true⟩] := by
    rw [i4, lqPreB_calls]
    rfl
  refine ⟨fs name + (4 * 2 ^ cd + 2 ^ cd) + NK, capsL ++ LK, [r0, r1, sum, lam ^ q], [],
    ⟨rfl, rfl⟩, ?_, ?_, fun rd hlow hLm ↦ ?_⟩
  · intro q' hq'
    simp only [List.nil_append, List.mem_append, hcapsL, List.mem_cons, List.not_mem_nil,
      or_false] at hq'
    rcases hq' with (rfl | rfl) | hq'
    · simp only; omega
    · simp only; omega
    · have := hWK q' hq'; omega
  · have hc : DisjL (capsL ++ LK) := by
      unfold DisjL
      refine List.pairwise_append.mpr ⟨?_, hDK, fun x hx y hy ↦ Or.inl ?_⟩
      · refine List.pairwise_cons.mpr ⟨fun y hy ↦ ?_, List.pairwise_singleton _ _⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        subst hy
        left; simp only; omega
      · have := hWK y hy
        simp only [hcapsL, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp only <;> omega
    simpa using hc
  have hLm' : MemL rd (capsL ++ LK ++ Lin) := by simpa using hLm
  have hLin : MemL rd Lin := fun q' hq' ↦ hLm' q' (List.mem_append_right _ hq')
  have hCaps : MemL rd capsL := fun q' hq' ↦ hLm' q' (List.mem_append_left _
    (List.mem_append_left _ hq'))
  have hLK : MemL rd LK := fun q' hq' ↦ hLm' q' (List.mem_append_left _ (List.mem_append_right _ hq'))
  have hholds : Stmt.HoldsList (fun _ _ _ ↦ True) rd σ fn.body False
      (fun r ↦ r = [r0, r1, sum, lam ^ q]) := by
    rw [hb, lqBody_pre, holdsList_flat_ret _ (lqPreB_flat _ _ _ _ _ _ _ _ _ _)]
    refine ⟨?_, ?_⟩
    · rw [lqPreB, lqBodyA, allOk_append, allOk_append]
      refine ⟨⟨?_, (hpow rd).1⟩, ?_⟩
      · simp only [osHeap, allOk_append, allOk_cons, allOk_nil, and_true, Whir.StmtOk, Atom.Holds,
          osCst, osCp, osMul]
        simp [hvA, hA, hNdef, hodddef]
      · simp only [allOk_cons, allOk_nil, and_true, Whir.StmtOk, Atom.Holds, osCp]
        rw [(hpow rd).2, hvk]
    · simp only [List.map_cons, List.map_nil]
      rw [hvA 19 (by omega), hvA 20 (by omega), hvA 21 (by omega), hvk]
      rfl
  have hes : ∀ e ∈ es, e.Holds rd σ := by
    have := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf))
      hholds
    rw [hwalk] at this
    exact fun e he => (this.1 e he).1
  have hown : ∀ i, RegionL capsL i → ownData cert fp (fp + fs name) name (allocs σ es) es i := by
    intro i ⟨q', hq', h1, h2⟩
    rw [hal]
    simp only [hcapsL, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl
    · exact Or.inl ⟨(4 * 2 ^ cd, fp + fs name), by simp [bases], by simp only at h1; omega,
        by simp only at h2 ⊢; omega⟩
    · exact Or.inl ⟨(2 ^ cd, fp + fs name + 4 * 2 ^ cd), by simp [bases], by simp only at h1; omega,
        by simp only at h2 ⊢; omega⟩
  have hK := hKK rd σ (calls es) (fun i ↦ RegionL Lin i ∨ ownData cert fp (fp + fs name) name
      (allocs σ es) es i) (fun _ ↦ False) (by
      rw [hcalls]
      refine ⟨rfl, rfl, fun _ ↦ ⟨?_, ?_⟩, rfl, rfl, fun _ ↦ ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n 7), σ (.n 9)] = [CAP, FL]
        rw [h7, h9]
      · show [σ (.n 10), σ (.n 11)] = o1.1
        rw [e11, hvA 10 (by omega), hvA 11 (by omega)]
        rfl
      · show [σ (.n 13), σ (.n 15), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 16),
          σ (.n 17)] = [ofK (addressOfIndex ecap), ofK (addressOfIndex eflags), lamInv, cP, hP, pP, qP,
            gen ^ N, gen ^ odd]
        rw [hvA 13 (by omega), hvA 15 (by omega), hvA 1 (by omega), hvA 2 (by omega),
          hvA 3 (by omega), hvA 4 (by omega), hvA 5 (by omega), hvA 16 (by omega),
          hvA 17 (by omega), ← hgi, ← hgo, ← hCAPo', ← hFLo']
        rfl
      · show [σ (.n 18)] = o2.1
        rw [e21, hvA 18 (by omega)]
        rfl) hlow hLK (by
      simp only [Kid.lins, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact Main.memL_append.mpr ⟨hCaps, Main.memL_append.mpr ⟨hLin, hCaps⟩⟩) (by
      refine ⟨fun _ i hi ↦ Or.inl (Or.inr (hown i hi)), fun _ i hi ↦ ?_, trivial⟩
      obtain ⟨q', hq', h1, h2⟩ := hi
      rcases List.mem_append.mp hq' with hq' | hq'
      · exact Or.inl (Or.inl ⟨q', hq', h1, h2⟩)
      · exact Or.inl (Or.inr (hown i ⟨q', hq', h1, h2⟩)))
  have hrel := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (Dk := fun i ↦ False ∨ outRegion [kv, ko] [o1, o2] i)
    (N := NK) (fp := fp)
    (args := [lam, lamInv, cP, hP, pP, qP]) (rets := [r0, r1, sum, lam ^ q])
    coreProgram_wf hf (Or.inl hnl)
    (by rw [hps]; simp only [osParams, List.range_succ, List.range_zero, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append]
        rw [hvA 0 (by omega), hvA 1 (by omega), hvA 2 (by omega), hvA 3 (by omega),
          hvA 4 (by omega), hvA 5 (by omega)]
        rfl) hwalk
    (by simp only [List.map_cons, List.map_nil]
        rw [hvA 19 (by omega), hvA 20 (by omega), hvA 21 (by omega), hvk]
        rfl) hes
    (by rw [hal, i1, lqPreB_allocs]; simp [bases, h7, h9, hCAP, hFL, hcapE, hflE])
    (fun q' hq' => by rw [i3, lqPreB_addrs] at hq'; simp at hq')
    (by
      have hb' : fp + fs name + (allocs σ es).sum = b := by
        rw [hal]; simp [hbdef, hflE, hcapE]; omega
      rw [hb']
      exact hK)
    (fun A' hA' => by
      rw [loadAddrs_straight σ _ hst', lqPreB_loads] at hA'
      simp at hA')
    (fun i hi => absurd hi (by simp [RegionL]))
  rw [hal] at hrel
  simpa [Nat.add_assoc] using hrel

/-! ## Every specialization -/

/-- The facts an entry of `lqTable` gives `lq_placed`. -/
def LqFacts (q base folds leaf d cd mu nhs hbits fin : ℕ) : Prop :=
  (oqEntry (lqOqN base folds leaf d cd mu nhs hbits fin)).map (·.1) =
      some (lqOqN base folds leaf d cd mu nhs hbits fin) ∧
    oqCount (Whir.lqOdd q base) (lqOqS base folds leaf d cd mu nhs hbits fin).base (lqIters q base) = q ∧
    lqIters q base + 1 < ordG ∧ Whir.lqOdd q base ≤ (lqOqS base folds leaf d cd mu nhs hbits fin).base ∧
    1 ≤ cd ∧ cd ≤ 8 ∧ osKindOf ("verify_merkle_cap__L" ++ natStr cd) = some (.cap cd) ∧
    digitsVal (osPowDigits q) 1 = q

/-- `LqFacts` by numbers: the entry and shape of the numbers `k` (`Whir/OqKey`). -/
def LqFactsK (k : List ℕ) (q base cd : ℕ) : Prop :=
  (oqEntryK k).isSome ∧ oqCount (Whir.lqOdd q base) (oqShapeK k).oq.base (lqIters q base) = q ∧
    lqIters q base + 1 < ordG ∧ Whir.lqOdd q base ≤ (oqShapeK k).oq.base ∧
    1 ≤ cd ∧ cd ≤ 8 ∧ osKindOf ("verify_merkle_cap__L" ++ natStr cd) = some (.cap cd) ∧
    digitsVal (osPowDigits q) 1 = q

instance (k : List ℕ) (q base cd : ℕ) : Decidable (LqFactsK k q base cd) := by
  unfold LqFactsK; infer_instance

instance (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    Decidable (LqFacts q base folds leaf d cd mu nhs hbits fin) :=
  decidable_of_iff (LqFactsK (oqKey base folds leaf (d - cd) mu nhs hbits fin) q base cd) <| by
    unfold LqFacts LqFactsK lqOqS lqOqN
    rw [oqEntry_name_iff', oqShapeOf_oqName]

set_option maxRecDepth 100000 in
/-- **Every entry of `lqTable` has its facts**, by the kernel. -/
theorem lqTable_facts : ∀ e ∈ lqTable,
    LqFacts e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2 := by
  decide +kernel

theorem oq_mem_of_entry {name : String} (h : (oqEntry name).map (·.1) = some name) :
    (name, oqLoopOf name, oqShapeOf name) ∈ openingQueriesLoops := by
  obtain ⟨e, hE, he1⟩ : ∃ e, oqEntry name = some e ∧ e.1 = name := by
    rcases hE : oqEntry name with _ | e
    · rw [hE] at h; simp at h
    · rw [hE] at h; simp at h; exact ⟨e, rfl, h⟩
  have heq : e = (name, oqLoopOf name, oqShapeOf name) := by
    obtain ⟨a, b, c⟩ := e
    simp only at he1
    simp [oqLoopOf, oqShapeOf, hE, he1]
  rw [← heq]
  exact List.mem_of_find?_eq_some hE

/-- **`level_queries` is complete placed at every specialization.** -/
theorem level_queries_completeAt : level_queries_completeAt_Spec := by
  intro fs cert κ _ _ _ e he
  obtain ⟨hoq, hQ, hN, hodd, hcd1, hcd8, hK, hpw⟩ := lqTable_facts e he
  exact lq_placed fs cert (κ := κ) (lqTable_ok e he) (oq_mem_of_entry hoq) hQ hN hodd hcd1 hcd8 hK hpw

end
end LeanVM.Guest.B1
