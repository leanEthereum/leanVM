/-
  LeanVM.Guest.B1.Place.LqProofP

  `level_queries` complete placed at every specialization, with its pops: the cap's and the flags' words, then its queries' rows and walks' children.
-/

module

public import LeanVM.Guest.B1.Place.LqProof
public import LeanVM.Guest.B1.Merkle.CapPops
public import LeanVM.Guest.B1.Merkle.CapAll
public import LeanVM.Guest.B1.Opening.QueriesPlacedDPAll
public import LeanVM.Guest.B1.Place.LqBound
public import LeanVM.Guest.B1.Opening.CapPlacedE

/-!
# `level_queries`, placed with its pops

`LqProof`'s proof with `kidsFromInP_of_kidsD` and `relAtInP_of_walk`: `verify_merkle_cap` pops nothing (`mc_node_pops`, at its body `mcBody`: `mc_body_of_kind`), `opening_queries` its queries' entries (`opening_queries_completeAtDP`), and the body the cap's and the flags' heap words (`lq_splice`, `words_heap_of_reads`).

* `lqCapE`: the cap's and the flags' entries, the honest words;
* `LqAtDP`: `LqAtD` popping `lqCapE` then `oqPops` of its `q` queries;
* `LqAtEP`: `LqAtDP` by a tree of exactly `lqN` words (`toDP`, `toE`);
* `lq_placedEP`, `level_queries_completeAtEP`, `level_queries_completeAtP`: every entry of `lqTable`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- **The cap's and the flags' entries**: the honest words. -/
def lqCapE (capW flW : List E) : List Pop := [("merkle_caps", capW), ("merkle_cap_active", flW)]

/-- **`level_queries` at an entry of `lqTable`, placed, with its pops**: `LqAtD`, its tree popping the honest cap
and flags (`lqCapE`), then its `q` queries' rows and walks' children (`oqPops`). -/
def LqAtDP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name : String)
    (q base folds leaf d cd mu nhs hbits fin : ℕ) : Prop :=
  let s := lqOqS q base folds leaf d cd mu nhs hbits fin
  ∀ (Lin : Layout) (lam lamInv : E) (ecoefs ehs epos eqp : ℕ) (rounds : List FoldRound)
    (hsv : List E) (eb qs : ℕ → ℕ) (rows : ℕ → List K) (sibs : ℕ → List Digest)
    (capW flW : List E) (r0 r1 : E),
    rounds.length = s.folds → (s.final = 1 → hsv.length = s.nHs) →
    OqStatic s rounds hsv qs rows sibs q →
    LqCaps s q capW flW r0 r1 qs rows sibs →
    LqReg (RegionL Lin) s q ecoefs ehs epos eqp eb →
    (∀ rd, LowDef κ rd → MemL rd Lin → LqMem rd s q ecoefs ehs epos eqp rounds hsv eb qs) →
    CompleteAtDP fs cert κ name Lin
      [lam, lamInv, ofK (addressOfIndex ecoefs), ofK (addressOfIndex ehs),
        ofK (addressOfIndex epos), ofK (addressOfIndex eqp)]
      (Returns [r0, r1, lqSum s (lqOdd q base folds leaf d cd mu nhs hbits fin) (lqIters q base)
        lamInv rounds qs rows, lam ^ q])
      (fun _ => lqCapE capW flW ++ oqPops s (oqW qs rows sibs) q)

/-- **`LqAtDP` by a tree of exactly `lqN` words.** -/
def LqAtEP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name : String)
    (q base folds leaf d cd mu nhs hbits fin : ℕ) : Prop :=
  let s := lqOqS q base folds leaf d cd mu nhs hbits fin
  ∀ (Lin : Layout) (lam lamInv : E) (ecoefs ehs epos eqp : ℕ) (rounds : List FoldRound)
    (hsv : List E) (eb qs : ℕ → ℕ) (rows : ℕ → List K) (sibs : ℕ → List Digest)
    (capW flW : List E) (r0 r1 : E),
    rounds.length = s.folds → (s.final = 1 → hsv.length = s.nHs) →
    OqStatic s rounds hsv qs rows sibs q →
    LqCaps s q capW flW r0 r1 qs rows sibs →
    LqReg (RegionL Lin) s q ecoefs ehs epos eqp eb →
    (∀ rd, LowDef κ rd → MemL rd Lin → LqMem rd s q ecoefs ehs epos eqp rounds hsv eb qs) →
    CompleteAtEP fs cert κ name Lin
      [lam, lamInv, ofK (addressOfIndex ecoefs), ofK (addressOfIndex ehs),
        ofK (addressOfIndex epos), ofK (addressOfIndex eqp)]
      (Returns [r0, r1, lqSum s (lqOdd q base folds leaf d cd mu nhs hbits fin) (lqIters q base)
        lamInv rounds qs rows, lam ^ q]) (lqN fs name q base folds leaf d cd mu nhs hbits fin)
      (fun _ => lqCapE capW flW ++ oqPops s (oqW qs rows sibs) q)

section
variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {name : String}
  {q base folds leaf d cd mu nhs hbits fin : ℕ}

theorem LqAtEP.toDP (h : LqAtEP fs cert κ name q base folds leaf d cd mu nhs hbits fin) :
    LqAtDP fs cert κ name q base folds leaf d cd mu nhs hbits fin :=
  fun Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 hrl hhs hst hcaps hreg hmem ↦
    (h Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 hrl hhs hst hcaps hreg
      hmem).toDP

theorem LqAtEP.toE (h : LqAtEP fs cert κ name q base folds leaf d cd mu nhs hbits fin) :
    LqAtE fs cert κ name q base folds leaf d cd mu nhs hbits fin :=
  fun Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 hrl hhs hst hcaps hreg hmem ↦
    (h Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 hrl hhs hst hcaps hreg
      hmem).toE

end

/-- A named `verify_merkle_cap` has the body `mcBody`. -/
theorem mc_body_of_kind {f : String} {d : ℕ} (hK : osKindOf f = some (.cap d)) :
    ∃ fn L, coreProgram.find? f = some fn ∧ fn.body = mcBody L := by
  have he := osKindEntry_ok hK
  simp only [osKindEntryOk, decide_eq_true_eq, merkleCapNames, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
    or_false] at he
  rcases he with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact ⟨_, _, find_verify_merkle_cap_L2, verify_merkle_cap_L2_body⟩
  · exact ⟨_, _, find_verify_merkle_cap_L3, verify_merkle_cap_L3_body⟩
  · exact ⟨_, _, find_verify_merkle_cap_L4, verify_merkle_cap_L4_body⟩
  · exact ⟨_, _, find_verify_merkle_cap_L5, verify_merkle_cap_L5_body⟩
  · exact ⟨_, _, find_verify_merkle_cap_L6, verify_merkle_cap_L6_body⟩
  · exact ⟨_, _, find_verify_merkle_cap_L7, verify_merkle_cap_L7_body⟩
  · exact ⟨_, _, find_verify_merkle_cap_L8, verify_merkle_cap_L8_body⟩

/-- **A heap hint's words are the memory's** at its pointer. -/
theorem words_heap_of_reads {rd : Reader} {σ : Val} {p : V} {P : E} {ws : List E} (hp : σ p = P)
    (hr : ReadsAt rd P ws) : Dest.words rd σ (.heap p 0 ws.length) = ws :=
  List.ext_getElem (by simp [Dest.words]) fun k _ h2 => by simp [Dest.words, hp, (hr k h2).2]

/-- **`level_queries`' events pop the cap and its flags, then its callees' entries.** -/
theorem lq_splice {rd : Reader} {σ : Val} {q base folds leaf d cd mu nhs hbits fin : ℕ} {fn : Fn}
    (hb : fn.body = lqBody q base folds leaf d cd mu nhs hbits fin) {es : List Ev} {vs : List V}
    (hw : walk σ fn.body = .ret es vs) (kc ko : List Pop) :
    splice rd σ es [kc, ko] = capPops rd σ cd ++ kc ++ ko := by
  have h : SplicePops rd σ (((((((osHeap (4 * 2 ^ cd) 6 ++
      [.atom (.hint (.witness "merkle_caps" (.heap (.n 7) 0 (4 * 2 ^ cd))))]) ++
      osHeap (2 ^ cd) 8) ++ [.atom (.hint (.witness "merkle_cap_active" (.heap (.n 9) 0 (2 ^ cd))))]) ++
      [.call ("verify_merkle_cap__L" ++ natStr cd) [.n 7, .n 9] [.n 10, .n 11]]) ++
      [osCst 12 (gw (if base = 1 then q / 2 else q))]) ++
      [.call (oqName q base folds leaf d cd mu nhs hbits fin) [.n 7, .n 9, .n 1, .n 2, .n 3, .n 4, .n 5, .n 12]
        [.n 13]]) ++
      ([osCp 14 10, osCp 15 11, osCp 16 13] ++ (osPowSteps 0 (osPowDigits q) 0 17).1 ++
        [osCp (17 + osPowLen q) (osPowSteps 0 (osPowDigits q) 0 17).2]))
      ([] ++ [] ++ [] ++ [] ++ [kc] ++ [] ++ [ko] ++ [])
      ([] ++ [("merkle_caps", Dest.words rd σ (.heap (.n 7) 0 (4 * 2 ^ cd)))] ++ [] ++
        [("merkle_cap_active", Dest.words rd σ (.heap (.n 9) 0 (2 ^ cd)))] ++ kc ++ [] ++ ko ++ []) :=
    (((((((SplicePops.of_fallPops (fallPops_noWit σ rfl)).append (SplicePops.of_fallPops (FallPops.atom _))).append
      (SplicePops.of_fallPops (fallPops_noWit σ rfl))).append (SplicePops.of_fallPops (FallPops.atom _))).append
      (SplicePops.call _ _ _ kc)).append (SplicePops.of_fallPops (fallPops_noWit σ rfl))).append
      (SplicePops.call _ _ _ ko)).append (SplicePops.of_fallPops (fallPops_noWit σ (by
        rw [noWit_append, noWit_append, osPowSteps_noWit]; rfl)))
  have h' := SplicePops.congr_pops (SplicePops.congr_ks h (ks' := [kc, ko]) (by simp))
    (q := capPops rd σ cd ++ kc ++ ko) (by simp [capPops])
  rw [splice_of_body (ys := [.ret [.n 14, .n 15, .n 16, .n (17 + osPowLen q)]]) (es' := [])
    (vs' := [.n 14, .n 15, .n 16, .n (17 + osPowLen q)])
    (by rw [hb, lqBody]; simp [List.append_assoc]) h' (by simp [walk, walk1, Out.seq]) rfl hw]
  exact List.append_nil _

/-- **`level_queries` at one specialization, placed, with its pops, by exactly `lqN` words.** -/
theorem lq_placedEP (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {name : String}
    {q base folds leaf d cd mu nhs hbits fin : ℕ}
    (hlq : FnIs name (osParams 6) (lqBody q base folds leaf d cd mu nhs hbits fin))
    (hoq : (lqOqN q base folds leaf d cd mu nhs hbits fin,
      oqLoopOf (lqOqN q base folds leaf d cd mu nhs hbits fin),
      oqShapeOf (lqOqN q base folds leaf d cd mu nhs hbits fin)) ∈ openingQueriesLoops)
    (hQ : oqCount (lqOdd q base folds leaf d cd mu nhs hbits fin)
      (lqOqS q base folds leaf d cd mu nhs hbits fin).base (lqIters q base) = q)
    (hN : lqIters q base + 1 < ordG)
    (hcd : (lqOqS q base folds leaf d cd mu nhs hbits fin).cd = cd) (hcd1 : 1 ≤ cd) (hcd8 : cd ≤ 8)
    (hK : osKindOf ("verify_merkle_cap__L" ++ natStr cd) = some (.cap cd))
    (hpw : digitsVal (osPowDigits q) 1 = q) :
    LqAtEP fs cert κ name q base folds leaf d cd mu nhs hbits fin := by
  unfold LqAtEP
  simp only [lqOqS, lqOdd, lqOqN] at hoq hQ hcd ⊢
  generalize hsh : oqShapeOf (oqName q base folds leaf d cd mu nhs hbits fin) = sh at hoq hQ hcd ⊢
  generalize hlp : oqLoopOf (oqName q base folds leaf d cd mu nhs hbits fin) = loop at hoq
  have hlp' := hlp
  intro Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 hrl hhs hst
    hcaps hreg hmem
  refine CompleteAtEP.of_eq fun fp ↦ ?_
  obtain ⟨fn, hf, hps, hb⟩ := hlq
  have hnl : coreProgram.loop name = false := lq_notLoop hf hb
  obtain ⟨hcapL, hflL, hvmc, hcells⟩ := hcaps
  rw [hcd] at hcapL hflL hvmc
  set N := lqIters q base with hNdef
  set oqn := oqName q base folds leaf d cd mu nhs hbits fin with hoqn
  set vmcN := "verify_merkle_cap__L" ++ natStr cd with hvmcN
  obtain ⟨fmc, Lmc, hfmc, hbmc⟩ := mc_body_of_kind hK
  set sum := lqSum sh.oq sh.odd N lamInv rounds qs rows with hsum
  set capE := fp + fs name with hcapE
  set flE := capE + 4 * 2 ^ cd with hflE
  set b := flE + 2 ^ cd with hbdef
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
  have hO : ordG = 2 ^ 64 - 1 := rfl
  have hU : u128Bound = 2 ^ 128 := rfl
  -- the kids
  set kv : Kid := ⟨vmcN, true, [CAP, FL], capsL, Returns [r0, r1]⟩ with hkv
  set ko : Kid := ⟨oqn, true, [CAP, FL, lamInv, cP, hP, pP, qP, gen ^ N], Lin ++ capsL,
    Returns [sum]⟩ with hko
  have hkvD : CompleteAtE fs cert κ vmcN capsL [CAP, FL] (Returns [r0, r1]) (fs vmcN) := by
    have := verify_merkle_cap_completeAtE_of_kind (fs := fs) (cert := cert) hK κ [CAP, FL] [r0, r1]
      capsL ?_ ?_
    · exact this
    · intro p hp t ht
      simp only [merkleCapSpec, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · refine ⟨capE + t, Main.addr_ofK _ _, (capE, capW), List.mem_cons_self, by omega, ?_⟩
        simp only at ht ⊢; rw [hcapL]; rw [pow_add] at ht; omega
      · refine ⟨flE + t, Main.addr_ofK _ _, (flE, flW), by simp [hcapsL], by omega, ?_⟩
        simp only at ht ⊢; rw [hflL]; omega
    · intro rd _ hm
      have h1 : ReadsAt rd CAP capW := hm (capE, capW) List.mem_cons_self
      have h2 : ReadsAt rd FL flW := hm (flE, flW) (List.mem_cons_of_mem _ List.mem_cons_self)
      have h3 := hvmc rd CAP FL h1 h2
      exact h3
  have hkvDP : CompleteAtEP fs cert κ vmcN capsL [CAP, FL] (Returns [r0, r1]) (fs vmcN) (fun _ => []) :=
    completeAtEP_of_node hkvD fun _ τ bufs kids => mc_node_pops hfmc hbmc τ bufs kids
  have hkoDP : CompleteAtEP fs cert κ oqn (Lin ++ capsL) [CAP, FL, lamInv, cP, hP, pP, qP, gen ^ N]
      (Returns [sum]) (oqBound fs oqn loop N) (fun _ => oqPops sh.oq (oqW qs rows sibs) q) := by
    have hD := opening_queries_completeAtEP fs cert (oqn, loop, sh) hoq κ (Lin ++ capsL)
      N capE flE
      ecoefs ehs epos eqp lamInv rounds hsv eb qs rows sibs hN hrl hhs (by rw [hQ]; exact hst)
      ?_ ?_
    · rw [hQ] at hD; exact hD
    · rw [hQ]
      obtain ⟨hr1, hr2, hr3⟩ := hreg
      have hL : ∀ i, RegionL Lin i → RegionL (Lin ++ capsL) i := fun i ⟨q', hq, h1, h2⟩ ↦
        ⟨q', List.mem_append_left _ hq, h1, h2⟩
      refine ⟨fun l hl ↦ hL _ (hr1 l hl), fun hf l hl ↦ hL _ (hr2 hf l hl), fun k hk ↦ ?_⟩
      obtain ⟨p1, p2, p3⟩ := hr3 k hk
      have hqk := (hst k hk).1
      refine ⟨hL _ p1, hL _ p2, fun i hi ↦ hL _ (p3 i hi), ?_, fun e he ↦ ?_⟩
      · refine ⟨(flE, flW), List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self),
          Nat.le_add_right _ _, ?_⟩
        have := lq_flag_lt (pd := sh.oq.pd) (cd := cd) hcd1 (by rw [← hcd]; exact hqk)
        simp only; rw [hcd, hflL]; omega
      · refine ⟨(capE, capW), List.mem_append_right _ List.mem_cons_self, Nat.le_add_right _ _, ?_⟩
        have := lq_cap_lt (pd := sh.oq.pd) (cd := cd) (by rw [← hcd]; exact hqk) he
        simp only; rw [hcd, hcapL]; omega
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
      rw [hcd] at hqk c1 c2 c3
      have hx0 := lq_cap_lt (pd := sh.oq.pd) (cd := cd) hqk (e := 0) (by omega)
      have hx1 := lq_cap_lt (pd := sh.oq.pd) (cd := cd) hqk (e := 1) (by omega)
      have hxf := lq_flag_lt (pd := sh.oq.pd) (cd := cd) hcd1 hqk
      refine ⟨n1, n2, n3, ?_, ?_, ?_⟩
      · rw [hcd, ← c1, List.getD_eq_getElem _ _ (by rw [hcapL]; omega)]
        exact hC _ _
      · rw [hcd, ← c2, List.getD_eq_getElem _ _ (by rw [hcapL]; omega)]
        exact hC _ _
      · rw [hcd]
        have := hF (2 ^ (cd - 1) + qs k / 2 ^ (sh.oq.pd + 1)) (by rw [hflL]; exact hxf)
        rw [List.getElem_eq_getD 0, c3] at this
        exact this
  -- the kids placed
  obtain ⟨LK, outs, hOk, hWK, hDK, -, hKK⟩ := kidsFromInP_of_kidsEP (fs := fs) (cert := cert) κ
    (fun k ↦ if k.args.length = 2 then fs vmcN else oqBound fs oqn loop N)
    [kv, ko] [fun _ => [], fun _ => oqPops sh.oq (oqW qs rows sibs) q]
    ⟨fun _ ↦ hkvDP, fun _ _ ↦ rfl, fun _ ↦ hkoDP, fun h ↦ by simp at h, trivial⟩ b
  obtain ⟨NK, hNKd⟩ : ∃ n, n = kidsN fs
      (fun k ↦ if k.args.length = 2 then fs vmcN else oqBound fs oqn loop N) [kv, ko] := ⟨_, rfl⟩
  rw [← hNKd] at hWK hKK
  have hNK : NK = fs vmcN + oqBound fs oqn loop N := by
    rw [hNKd]; simp [kidsN, hkv, hko]
  have hn : lqN fs name q base folds leaf d cd mu nhs hbits fin =
      fs name + (4 * 2 ^ cd + 2 ^ cd) + NK := by
    rw [hNK, hvmcN]
    unfold lqN
    simp only [lqOqN]
    rw [← hoqn, hlp', ← hNdef]
    ring
  obtain ⟨o1, o2, rfl⟩ : ∃ o1 o2, outs = [o1, o2] := by
    match outs, hOk with
    | [o1, o2], _ => exact ⟨o1, o2, rfl⟩
  obtain ⟨ho1, ho2, -⟩ := hOk
  obtain ⟨e11, e12⟩ := ho1 rfl
  obtain ⟨e21, e22⟩ := ho2 rfl
  -- the honest values
  set L := osPowLen q with hL
  set A : List E := [lam, lamInv, cP, hP, pP, qP, gw (4 * 2 ^ cd), CAP, gw (2 ^ cd), FL, r0, r1,
    gw (if base = 1 then q / 2 else q), sum, r0, r1, sum] with hA
  set PV := lqPowVals lam (osPowDigits q) 1 with hPV
  set vals : List E := A ++ (PV ++ [lam ^ q]) with hvals
  set σ : Val := fun v ↦ if v.path = [] ∧ v.tag = 0 then vals.getD v.idx 0 else 0 with hσ
  have hv : ∀ i, σ (.n i) = vals.getD i 0 := fun i ↦ by simp [hσ]
  have hAl : A.length = 17 := rfl
  have hpl : PV.length = L := by rw [hPV, lqPowVals_length, hL, osPowLen]
  have hvA : ∀ i < 17, σ (.n i) = A.getD i 0 := fun i hi ↦ by
    rw [hv, hvals, List.getD_append _ _ _ _ (by rw [hAl]; exact hi)]
  have hv17 : ∀ j < L, σ (.n (17 + j)) = PV.getD j 0 := by
    intro j hj
    rw [hv, hvals, List.getD_append_right _ _ _ _ (by rw [hAl]; omega), hAl,
      show 17 + j - 17 = j by omega, List.getD_append _ _ _ _ (by rw [hpl]; exact hj)]
  have hvk : σ (.n (17 + L)) = lam ^ q := by
    rw [hv, hvals, List.getD_append_right _ _ _ _ (by rw [hAl]; omega), hAl,
      show 17 + L - 17 = L by omega, List.getD_append_right _ _ _ _ (by rw [hpl]), hpl,
      Nat.sub_self]
    rfl
  have hv0 : σ (.n 0) = lam := hvA 0 (by omega)
  have hpow : ∀ rd : Reader, AllOk (fun _ _ _ ↦ True) rd σ (osPowSteps 0 (osPowDigits q) 0 17).1 ∧
      σ (.n (osPowSteps 0 (osPowDigits q) 0 17).2) = lam ^ q := fun rd ↦ by
    have h := lq_powSteps_complete (C := fun _ _ _ ↦ True) (rd := rd) (σ := σ) 0
      (osPowDigits q) 0 17 1 (by rw [pow_one]) (fun j hj ↦ by
        rw [hv0] at hj ⊢; exact hv17 j (by rw [← hpl]; exact hj))
    rw [hv0, hpw] at h
    exact h
  have hit : (if base = 1 then q / 2 else q) = N := rfl
  have hgi : gw (if base = 1 then q / 2 else q) = gen ^ N := by
    rw [hit, Whir.gw_eq (by rw [hU]; rw [hO] at hN; omega)]
  have hcLen : capW.length = 4 * 2 ^ cd := hcapL
  have hfLen : flW.length = 2 ^ cd := hflL
  -- the walk
  have hst' := lqPreB_straight q base folds leaf d cd mu nhs hbits fin
  have hwalk : walk σ fn.body = .ret ((lqPreB q base folds leaf d cd mu nhs hbits fin).flatMap
      (Main.slEvs σ)) [.n 14, .n 15, .n 16, .n (17 + osPowLen q)] := by
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
        ⟨oqn, [.n 7, .n 9, .n 1, .n 2, .n 3, .n 4, .n 5, .n 12], [.n 13], true⟩] := by
    rw [i4, lqPreB_calls]
    rfl
  refine ⟨fs name + (4 * 2 ^ cd + 2 ^ cd) + NK, capsL ++ LK, [r0, r1, sum, lam ^ q], [],
    ⟨rfl, rfl⟩, ?_, ?_, hn.symm, fun rd hlow hLm ↦ ?_⟩
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
    · rw [lqPreB, allOk_append, allOk_append]
      refine ⟨⟨?_, (hpow rd).1⟩, ?_⟩
      · simp only [osHeap, allOk_append, allOk_cons, allOk_nil, and_true, Whir.StmtOk, Atom.Holds,
          osCst, osCp]
        simp [hvA, hA]
      · simp only [allOk_cons, allOk_nil, and_true, Whir.StmtOk, Atom.Holds, osCp]
        rw [(hpow rd).2, hvk]
    · simp only [List.map_cons, List.map_nil]
      rw [hvA 14 (by omega), hvA 15 (by omega), hvA 16 (by omega), hvk]
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
      · show [σ (.n 7), σ (.n 9), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 12)] =
          [CAP, FL, lamInv, cP, hP, pP, qP, gen ^ N]
        rw [h7, h9, hvA 1 (by omega), hvA 2 (by omega), hvA 3 (by omega), hvA 4 (by omega),
          hvA 5 (by omega), hvA 12 (by omega), ← hgi]
        rfl
      · show [σ (.n 13)] = o2.1
        rw [e21, hvA 13 (by omega)]
        rfl) hlow hLK (by
      simp only [Kid.lins, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact Main.memL_append.mpr ⟨hCaps, Main.memL_append.mpr ⟨hLin, hCaps⟩⟩) (by
      refine ⟨fun _ i hi ↦ Or.inl (Or.inr (hown i hi)), fun _ i hi ↦ ?_, trivial⟩
      obtain ⟨q', hq', h1, h2⟩ := hi
      rcases List.mem_append.mp hq' with hq' | hq'
      · exact Or.inl (Or.inl ⟨q', hq', h1, h2⟩)
      · exact Or.inl (Or.inr (hown i ⟨q', hq', h1, h2⟩)))
  have hC : ReadsAt rd CAP capW := hCaps (capE, capW) List.mem_cons_self
  have hF : ReadsAt rd FL flW := hCaps (flE, flW) (List.mem_cons_of_mem _ List.mem_cons_self)
  have hpops : splice rd σ es [[], oqPops sh.oq (oqW qs rows sibs) q] =
      lqCapE capW flW ++ oqPops sh.oq (oqW qs rows sibs) q := by
    rw [lq_splice hb hwalk, List.append_nil, capPops, ← hcLen, ← hfLen, words_heap_of_reads h7 hC,
      words_heap_of_reads h9 hF]
    rfl
  have hrel := relAtInP_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
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
        rw [hvA 14 (by omega), hvA 15 (by omega), hvA 16 (by omega), hvk]
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
    (fun i hi => absurd hi (by simp [RegionL])) hpops
  rw [hal, List.sum_cons, List.sum_cons, List.sum_nil, Nat.add_zero] at hrel
  exact hrel

/-- **`level_queries` is complete placed with its pops at every specialization, by exactly `lqN` words.** -/
theorem level_queries_completeAtEP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) :
    ∀ e ∈ lqTable,
      LqAtEP fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
        e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2 := by
  intro e he
  obtain ⟨hoq, hQ, hN, hcd, hcd1, hcd8, hK, hpw⟩ := lqTable_facts e he
  exact lq_placedEP fs cert (lqTable_ok e he) (oq_mem_of_entry hoq) hQ hN hcd hcd1 hcd8 hK hpw

/-- **`level_queries` is complete placed with its pops at every specialization.** -/
theorem level_queries_completeAtP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) :
    ∀ e ∈ lqTable,
      LqAtDP fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
        e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2 :=
  fun e he ↦ (level_queries_completeAtEP fs cert κ e he).toDP

end
end LeanVM.Guest.B1
