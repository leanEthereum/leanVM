/-
  LeanVM.Guest.Complete.CycOwn

  The cycle hand facts whose values come from the pops: `main`'s own (its meta counts), `da_verify`'s (its blob
  count), and the two claim-list digests' (a list's split, or the empty list's arm).
-/

module

public import LeanVM.Guest.Complete.HandKids
public import LeanVM.Guest.Complete.CycHands

/-!
# Cycle hand facts from the pops

The values are `hand2`'s (`main_meta`, `honest_blobs`, `list_split_in`, `honest_split`); each coordinate's inequality
is linear arithmetic at each opcode. A digest's empty-list arm reads its split's two values at a valuation running its
path with both `1` (`ThenSame`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

/-! ## A hand fact at another valuation -/

/-- **A hand function's cycle hand fact at a valuation `σ'` running its path** (`handFact_ch_of` with `σ'`). -/
theorem handFact_ch_of' (op : Opcode) (C₁ C₂ : ℕ) {f : String} {j : ℕ} {hv : HandV} {b : AffV} {σ σ' : Val}
    (hj : coreIdx f = j) (hm : j ≠ Data.chidxMain) (hd : j ≠ Data.chidxDa) (hl : f ≠ "__loop4_main")
    (hh : Data.chhandJ j = some hv) (hc : Data.chcertJ j = .stat [] b []) (hsame : SameOnPath coreProgram f σ σ')
    (hfact : ∀ fn, coreProgram.find? f = some fn → ArgsPre hv.pre (fn.params.map σ ++ hv.vps.map σ') ∧
      (hv.b.proj (B2C.opIdx op)).eval (fn.params.map σ ++ hv.vps.map σ') ≤
        (b.proj (B2C.opIdx op)).eval (fn.params.map σ)) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) f σ := by
  refine ⟨not_chOut op hl, fun h hH fn hfn => ?_⟩
  have hjl : j ≠ Data.chidxLoop := fun e => hl (coreIdx_eq_loop (hj.trans e))
  unfold chHandAt handAt handP at hH
  rw [hj, ite_eq_right hm, hh, Option.map_some, Option.some.injEq] at hH
  subst hH
  refine ⟨σ', hsame, ?_⟩
  unfold chCertAt certAt certP
  rw [hj, ite_eq_right hd, ite_eq_right hjl, hc]
  intro _
  have := hfact fn hfn
  simpa [HandV.proj, CertV.proj, List.map_append] using this

/-! ## `main`'s own -/

variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {rd : Reader} {σ : Val} {bufs : List ℕ}
  {kids : List Tree}

/-- `main`'s cycle inner bound at its values' exponents. -/
theorem chmain_eval (op : Opcode) (args : List E) :
    (Data.chmainHand.b.proj (B2C.opIdx op)).eval args = mainV op + declV op * (argExp args 0 + argExp args 1) +
      dupV op * (argExp args 2 + argExp args 3) + xmssV op * argExp args 4 + sphincsV op * argExp args 5 +
      childV op * argExp args 6 := by
  cases op <;> simp [AffV.proj, Aff.eval, Data.chmainHand, B2C.opIdx, mainV, declV, dupV, xmssV, sphincsV, childV,
    v6] <;> ring

/-- **`main`'s own cycle hand fact**: its preconditions at its values and its inner bound there within
`mainCntC op` of the node's items. -/
theorem main_cyc_own (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (h : MainHonest al s w rd (.node "main" σ bufs kids)) (op : Opcode) :
    ArgsPre Data.chmainHand.pre ([] ++ Data.chmainHand.vps.map σ) ∧
      (Data.chmainHand.b.proj (B2C.opIdx op)).eval ([] ++ Data.chmainHand.vps.map σ) ≤ mainCntC op (itemsOf s w) := by
  have hm := main_meta h
  simp only [metaCells, List.cons.injEq, and_true] at hm
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, -⟩ := hm
  have hb := hlim.withinMemoryBudget
  simp only [NodeWitness.memoryBudget, NodeWitness.childClaimCount] at hb
  have hps := slots_eq hrel
  have L : ∀ n, n ≤ 3 * 2 ^ 24 → n < 2 ^ 64 - 1 := fun n hn => by omega
  have g0 := count_gpow (n := s.claims.xmss.length) (L _ (by omega))
  have g1 := count_gpow (n := (xPlan s w).duplicates.length) (L _ (by omega))
  have g2 := count_gpow (n := w.xmssSignatures.length) (L _ (by omega))
  have g3 := count_gpow (n := s.claims.sphincs.length) (L _ (by omega))
  have g4 := count_gpow (n := (sPlan s w).duplicates.length) (L _ (by omega))
  have g5 := count_gpow (n := w.sphincsSignatures.length) (L _ (by omega))
  have g6 := count_gpow (n := w.children.length) (L _ (by omega))
  rw [← h0] at g0; rw [← h1] at g1; rw [← h2] at g2; rw [← h3] at g3; rw [← h4] at g4; rw [← h5] at g5
  rw [← h6] at g6
  have hvps : Data.chmainHand.vps = [.n 0, .n 3, .n 1, .n 4, .n 2, .n 5, .n 6] := rfl
  have hpre : Data.chmainHand.pre = [(2, 2 ^ 64), (3, 2 ^ 64), (4, 2 ^ 64), (5, 2 ^ 64), (6, 2 ^ 64)] := rfl
  rw [hvps, hpre]
  simp only [List.nil_append, List.map_cons, List.map_nil]
  refine ⟨argsPre_of (by simp) ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl | rfl | rfl | rfl)
    exacts [⟨_, g1⟩, ⟨_, g4⟩, ⟨_, g2⟩, ⟨_, g5⟩, ⟨_, g6⟩]
  · set vs : List E := [σ (.n 0), σ (.n 3), σ (.n 1), σ (.n 4), σ (.n 2), σ (.n 5), σ (.n 6)] with hvs
    have a0 : argExp vs 0 = _ := g0.logG
    have a1 : argExp vs 1 = _ := g3.logG
    have a2 : argExp vs 2 = _ := g1.logG
    have a3 : argExp vs 3 = _ := g4.logG
    have a4 : argExp vs 4 = _ := g2.logG
    have a5 : argExp vs 5 = _ := g5.logG
    have a6 : argExp vs 6 = _ := g6.logG
    have hdup : (itemsOf s w).holders - (itemsOf s w).declaredXmss - (itemsOf s w).declaredSphincs =
        (xPlan s w).duplicates.length + (sPlan s w).duplicates.length := by
      simp only [NodeItems.holders, NodeItems.childClaims, itemsOf, NodeItems.ofWitness, List.map_map,
        Function.comp_def]
      omega
    rw [chmain_eval, a0, a1, a2, a3, a4, a5, a6]
    unfold mainCntC
    rw [hdup]
    simp only [itemsOf, NodeItems.ofWitness, List.length_map]
    cases op <;> simp only [mainV, declV, dupV, xmssV, sphincsV, childV, v6] <;> omega

/-! ## `da_verify` -/

theorem chhand_da : (Data.chhandJ 26).map (fun h : HandV => (h.vps, h.pre, h.b)) =
    some ([.n 1, .n 2], [(1, 18446744073709551616), (2, 18446744073709551616)],
      ⟨[34082, 34729, 1686, 23708, 605, 32], [(1, [33159, 18365, 2893, 19643, 780, 2175]), (2, [1, 6, 6, 7, 2, 0])]⟩) :=
  rfl

/-- **`da_verify`'s cycle hand fact** at the node's rows, from the pops. -/
theorem da_verify_cyc (hlim : DeployedLimits s w) (op : Opcode) {C₂ : ℕ}
    (hp : PathIn coreProgram rd (Prover.honestPushes guestBytecode guestSeed s w) "da_verify" σ) :
    HandFact coreProgram (chCertAt op (daCntC op (itemsOf s w).rows) C₂)
      (chHandAt op (daCntC op (itemsOf s w).rows) C₂) (chOut op) "da_verify" σ := by
  have hj : coreIdx "da_verify" = Data.chidxDa := coreIdx_of_name ch_nodeIdx.nd
  obtain ⟨fn, hf, hh, es, vs, hw, -, hpops⟩ := hp
  rw [coreProgram_find?_at (j := idx% «da_verify») rfl] at hf
  obtain rfl := Option.some.inj hf
  obtain ⟨rest, hbody⟩ : ∃ rest, (fn% «da_verify»).body =
      .atom (.hint (.witness "da_n_blobs" (.stack [.n 1]))) :: .call "da_padding" [.n 1] [.n 2] :: rest := ⟨_, rfl⟩
  rw [hbody] at hw hh
  have hmem := hpops _ (hint_stack_mem (σ := σ) (rd := rd) (atom_head_mem hw))
  obtain ⟨c, mw, hm, hv1⟩ := honest_blobs (honest_mem s w _ hmem)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hv1
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, List.map_cons, List.map_nil] at hh
  obtain ⟨nb, x, hnb, hx, hmul⟩ := da_padding_mul _ _ (RelIn.rel hh.1)
  simp only [List.cons.injEq, and_true] at hnb hx
  subst hnb hx
  have hn32 : mw.rows.length ≤ 32 := hlim.atMostMaxRows (c, mw) (by rw [hm]; rfl)
  have g1 : GPow (σ (.n 1)) mw.rows.length := hv1 ▸ count_gpow (by omega)
  have g2 : GPow (σ (.n 2)) (32 - mw.rows.length) := by
    refine ⟨mul_right_cancel₀ (gen_pow_ne_zero mw.rows.length) ?_, by omega⟩
    calc σ (.n 2) * gen ^ mw.rows.length = σ (.n 2) * σ (.n 1) := by rw [g1.1]
      _ = gen ^ 32 := hmul.symm
      _ = gen ^ (32 - mw.rows.length) * gen ^ mw.rows.length := by rw [← pow_add]; congr 1; omega
  refine ⟨not_chOut op (by decide), fun h hh' fn hfn => ⟨σ, SameOnPath.refl, ?_⟩⟩
  have e1 : chHandAt op (daCntC op (itemsOf s w).rows) C₂ "da_verify" =
      (Data.chhandJ 26).map (HandV.proj (B2C.opIdx op)) := by
    simp only [chHandAt, handAt, handP, hj]; rfl
  rw [e1] at hh'
  obtain ⟨hv, hhv, hdat⟩ : ∃ hv : HandV, Data.chhandJ 26 = some hv ∧ (hv.vps, hv.pre, hv.b) =
      ([.n 1, .n 2], [(1, 18446744073709551616), (2, 18446744073709551616)],
        ⟨[34082, 34729, 1686, 23708, 605, 32], [(1, [33159, 18365, 2893, 19643, 780, 2175]), (2, [1, 6, 6, 7, 2, 0])]⟩) := by
    have hd := chhand_da
    rcases e : Data.chhandJ 26 with _ | hv
    · rw [e] at hd; cases hd
    · rw [e] at hd; exact ⟨hv, rfl, Option.some.inj hd⟩
  rw [hhv, Option.map_some, Option.some.injEq] at hh'
  subst hh'
  simp only [Prod.mk.injEq] at hdat
  obtain ⟨hvps, hpre, hb⟩ := hdat
  have e2 : chCertAt op (daCntC op (itemsOf s w).rows) C₂ "da_verify" =
      .stat [] ⟨daCntC op (itemsOf s w).rows, []⟩ [] := by
    simp only [chCertAt, certAt, hj, ↓reduceIte]
  rw [e2]
  rw [coreProgram_find?_at (j := idx% «da_verify») rfl] at hfn
  obtain rfl := Option.some.inj hfn
  intro _
  simp only [HandV.proj, hvps, hpre, hb, Aff.eval_mk_nil]
  have hrows : (itemsOf s w).rows = some mw.rows.length := by
    simp [itemsOf, NodeItems.ofWitness, hm]
  set ps : List E := (fn% «da_verify»).params.map σ with hps
  set as : List E := ps ++ [V.n 1, .n 2].map σ with has
  have a1 : argExp as 1 = mw.rows.length := g1.logG
  have a2 : argExp as 2 = 32 - mw.rows.length := g2.logG
  refine ⟨argsPre_of (by simp) ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl)
    exacts [⟨_, g1⟩, ⟨_, g2⟩]
  · rw [hrows]
    cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, a1, a2, daCntC, daV, rowV, padV, v6, Option.map_some,
      Option.getD_some] <;> omega

/-! ## The claim-list digests -/

/-- **A digest's empty-list arm runs at a valuation with its split's two values `1`**: on `f`'s path with `σ z = 0`,
some `σ'` runs it (`SameOnPath`) with `σ' a = σ' b = 1` (`hand3`'s lemma, for the words alike). -/
def ThenSame (f : String) (z a b : V) : Prop :=
  ∀ rd σ, PathHolds coreProgram rd f σ → σ z = 0 → ∃ σ', SameOnPath coreProgram f σ σ' ∧ σ' a = 1 ∧ σ' b = 1

theorem gpow_unit : GPow (1 : E) 0 := ⟨(pow_zero gen).symm, by norm_num⟩

theorem chhand_cl : Data.chhandJ (idx% «claim_list_digest») = some ⟨[.n 12, .n 13],
    [(2, 18446744073709551616), (3, 18446744073709551616)],
    ⟨[73, 69, 26, 145, 12, 9], [(2, [577, 18, 4, 575, 2, 64]), (3, [73, 15, 4, 99, 2, 8])]⟩, []⟩ := rfl

theorem chcert_cl : Data.chcertJ (idx% «claim_list_digest») =
    .stat [] ⟨[584, 174, 54, 838, 26, 65], [(1, [5, 1, 1, 5, 1, 1])]⟩ [] := rfl

theorem chhand_ccl : Data.chhandJ (idx% «child_claim_list_digest») = some ⟨[.n 15, .n 16],
    [(5, 18446744073709551616), (6, 18446744073709551616)],
    ⟨[74, 157, 26, 194, 12, 9], [(5, [577, 555, 6, 851, 2, 64]), (6, [73, 79, 6, 137, 2, 8]),
      (5, [577, 831, 4, 986, 2, 64]), (6, [73, 114, 4, 153, 2, 8])]⟩, []⟩ := rfl

theorem chcert_ccl : Data.chcertJ (idx% «child_claim_list_digest») =
    .stat [] ⟨[1096, 1508, 96, 2224, 40, 121], [(4, [9, 11, 1, 14, 1, 1])]⟩ [] := rfl

/-- `claim_list_digest`'s cycle fact at its list's exponent `n` and split exponents `a`, `b` with
`136 a + 17 b ≤ n`, `b < 8`. -/
theorem claim_cyc_of (op : Opcode) (C₁ C₂ : ℕ) {σ σ' : Val} (hsame : SameOnPath coreProgram "claim_list_digest" σ σ')
    {n a b : ℕ} (hn : logG (σ (.n 1)) = n) (ga : GPow (σ' (.n 12)) a) (gb : GPow (σ' (.n 13)) b)
    (hab : 136 * a + 17 * b ≤ n) (hb : b < 8) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "claim_list_digest" σ := by
  refine handFact_ch_of' op C₁ C₂ (coreIdx_of_name (j := idx% «claim_list_digest») rfl) (by decide) (by decide)
    (by decide) chhand_cl chcert_cl hsame fun fn hfn => ?_
  rw [Digest.find_claim_list_digest] at hfn
  obtain rfl := Option.some.inj hfn
  have hp : (fn% «claim_list_digest»).params = [.n 0, .n 1] := rfl
  rw [hp]
  dsimp only
  set ps : List E := [V.n 0, .n 1].map σ with hps
  set vs : List E := ps ++ [V.n 12, .n 13].map σ' with hvs
  have a2 : argExp vs 2 = a := argExp_gpow rfl ga
  have a3 : argExp vs 3 = b := argExp_gpow rfl gb
  have a1 : argExp ps 1 = n := hn
  refine ⟨argsPre_of (by simp) ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl)
    exacts [⟨_, ga⟩, ⟨_, gb⟩]
  · cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, a1, a2, a3] <;> omega

/-- `child_claim_list_digest`'s cycle fact at its list's exponent `n` and split exponents `a`, `b` with
`136 a + 17 b ≤ n`, `b < 8`. -/
theorem child_claim_cyc_of (op : Opcode) (C₁ C₂ : ℕ) {σ σ' : Val}
    (hsame : SameOnPath coreProgram "child_claim_list_digest" σ σ')
    {n a b : ℕ} (hn : logG (σ (.n 4)) = n) (ga : GPow (σ' (.n 15)) a) (gb : GPow (σ' (.n 16)) b)
    (hab : 136 * a + 17 * b ≤ n) (hb : b < 8) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "child_claim_list_digest" σ := by
  refine handFact_ch_of' op C₁ C₂ (coreIdx_of_name (j := idx% «child_claim_list_digest») rfl) (by decide)
    (by decide) (by decide) chhand_ccl chcert_ccl hsame fun fn hfn => ?_
  rw [Digest.find_child_claim_list_digest] at hfn
  obtain rfl := Option.some.inj hfn
  have hp : (fn% «child_claim_list_digest»).params = [.n 0, .n 1, .n 2, .n 3, .n 4] := rfl
  rw [hp]
  dsimp only
  set ps : List E := [V.n 0, .n 1, .n 2, .n 3, .n 4].map σ with hps
  set vs : List E := ps ++ [V.n 15, .n 16].map σ' with hvs
  have a5 : argExp vs 5 = a := argExp_gpow rfl ga
  have a6 : argExp vs 6 = b := argExp_gpow rfl gb
  have a4 : argExp ps 4 = n := hn
  refine ⟨argsPre_of (by simp) ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl)
    exacts [⟨_, ga⟩, ⟨_, gb⟩]
  · cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, a4, a5, a6] <;> omega

/-- A list's split from the pops: `list_split`'s returns an honest split of a list's length `n`, its argument `g^n`. -/
theorem split_vals (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w) {ng x y z : E}
    (h : RelIn coreProgram rd (Prover.honestPushes guestBytecode guestSeed s w) "list_split" [ng] [x, y, z]) :
    ∃ n, GPow ng n ∧ GPow x (n / 136) ∧ GPow y (n % 136 / 17) ∧ n ≤ 2 ^ 24 := by
  obtain ⟨hmem, a, b, c, habc, hng⟩ := list_split_in h
  obtain ⟨n, hsplit, hn⟩ := honest_split (honest_mem s w _ hmem)
  have hnb := listLen_le hrel hlim hn
  simp only [List.cons.injEq, and_true] at habc
  obtain ⟨rfl, rfl, rfl⟩ := habc
  simp only [Prover.listSplit, List.cons.injEq, and_true] at hsplit
  obtain ⟨h12, h13, h14⟩ := hsplit
  have hcb : Prover.claimBig = 136 := rfl
  have hcg : Prover.claimGroup = 17 := rfl
  rw [hcb] at h12 h13 h14
  rw [hcg] at h13 h14
  have g12 := count_gpow (n := n / 136) (by omega)
  have g13 := count_gpow (n := n % 136 / 17) (by omega)
  have g14 := count_gpow (n := n % 136 % 17) (by omega)
  rw [← h12] at g12; rw [← h13] at g13; rw [← h14] at g14
  refine ⟨n, ⟨?_, by omega⟩, g12, g13, hnb⟩
  rw [hng, g12.1, g13.1, g14.1, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  omega

/-- **`claim_list_digest`'s cycle hand fact**, from the pops (a nonempty list) or the empty arm (`ThenSame`). -/
theorem claim_cyc (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hT : ThenSame "claim_list_digest" (.n 3) (.n 12) (.n 13)) (op : Opcode) (C₁ C₂ : ℕ)
    (hp : PathIn coreProgram rd (Prover.honestPushes guestBytecode guestSeed s w) "claim_list_digest" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "claim_list_digest" σ := by
  by_cases h3 : σ (.n 3) = 0
  · obtain ⟨σ', hs, h12, h13⟩ := hT rd σ hp.pathHolds h3
    exact claim_cyc_of op C₁ C₂ hs rfl (h12 ▸ gpow_unit) (h13 ▸ gpow_unit) (by omega) (by omega)
  obtain ⟨fn, hf, hh, -⟩ := hp
  rw [Digest.find_claim_list_digest] at hf
  obtain rfl := Option.some.inj hf
  rw [Digest.claim_list_digest_shape] at hh
  simp only [Stmt.HoldsList, Stmt.Holds] at hh
  obtain ⟨-, -, -, -, helse⟩ := hh
  have he := helse h3
  obtain ⟨rest, hel⟩ : ∃ rest, Digest.cl23Else = .call "list_split" [.n 1] [.n 12, .n 13, .n 14] :: rest :=
    ⟨_, rfl⟩
  rw [hel] at he
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at he
  obtain ⟨n, g1, g12, g13, -⟩ := split_vals hrel hlim he.1
  exact claim_cyc_of op C₁ C₂ SameOnPath.refl g1.logG g12 g13 (by omega) (by omega)

/-- **`child_claim_list_digest`'s cycle hand fact**, from the pops (a nonempty list) or the empty arm
(`ThenSame`). -/
theorem child_claim_cyc (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hT : ThenSame "child_claim_list_digest" (.n 6) (.n 15) (.n 16)) (op : Opcode) (C₁ C₂ : ℕ)
    (hp : PathIn coreProgram rd (Prover.honestPushes guestBytecode guestSeed s w) "child_claim_list_digest" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "child_claim_list_digest" σ := by
  by_cases h6 : σ (.n 6) = 0
  · obtain ⟨σ', hs, h15, h16⟩ := hT rd σ hp.pathHolds h6
    exact child_claim_cyc_of op C₁ C₂ hs rfl (h15 ▸ gpow_unit) (h16 ▸ gpow_unit) (by omega) (by omega)
  obtain ⟨fn, hf, hh, -⟩ := hp
  rw [Digest.find_child_claim_list_digest] at hf
  obtain rfl := Option.some.inj hf
  rw [Digest.child_claim_list_digest_shape] at hh
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hh
  obtain ⟨-, -, -, -, helse⟩ := hh
  obtain ⟨hsplit, -⟩ := helse h6
  obtain ⟨n, g4, g15, g16, -⟩ := split_vals hrel hlim hsplit
  exact child_claim_cyc_of op C₁ C₂ SameOnPath.refl g4.logG g15 g16 (by omega) (by omega)

end
end LeanVM.Guest.Complete
