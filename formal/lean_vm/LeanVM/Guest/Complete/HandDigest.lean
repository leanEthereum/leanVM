/-
  LeanVM.Guest.Complete.HandDigest

  The hand facts whose values come from the pops: `da_verify`'s blob count (`da_n_blobs`) and
  padding, and a nonempty claim list's split (`signers_split`) in `claim_list_digest`.
-/

module

public import LeanVM.Guest.Complete.HandFacts
public import LeanVM.Guest.B1.Digest.ClaimList
public import LeanVM.Guest.B1.Da.Padding

/-!
# Hand facts from the pops

On `main`'s honest tree every node's path is within the honest pushes (`every_pathIn_of_streams`):

* `da_verify` hints its blob count `v1`, an honest `da_n_blobs` entry, so the checked matrix's
  rows `g^n`, `n ≤ 32` (`honest_blobs`); `da_padding` returns `v2 = g^(32 - n)`
  (`da_padding_mul`). Its inner bound there is `daWordsC` of the node's rows (`da_verify_hand`).
* On a nonempty list (`n_g ≠ 1`), `claim_list_digest` calls `list_split`, whose tree pops its
  three returns as one `signers_split` entry, an honest list's split, and whose product is `n_g`
  (`list_split_in`). So `n_g = g^n` with `n` a list's length, within the memory budget, and the
  inner bound `5071 + 2028 (n / 136) + 316 (n % 136 / 17)` is within `7283 + 15 n`
  (`claim_else_hand`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

/-! ## The honest entries of the two streams -/

variable {s : NodeStatement} {w : NodeWitness}

theorem honest_blobs {ws : List E} (h : HonestEntry s w ("da_n_blobs", ws)) :
    ∃ c mw, w.daMatrix = some (c, mw) ∧ ws = [Prover.count mw.rows.length] := by
  generalize hp : (("da_n_blobs" : String), ws) = p at h
  cases h with
  | other ho => subst hp; exact (ho.2.1 rfl).elim
  | split n _ => simp at hp
  | blobs c mw hm =>
      simp only [Prod.mk.injEq, true_and] at hp
      exact ⟨c, mw, hm, hp⟩
  | childMeta c _ => simp at hp

/-- A list's length: one of the node's two declared lists or one of a child's. -/
def ListLen (s : NodeStatement) (w : NodeWitness) (n : ℕ) : Prop :=
  n = s.claims.xmss.length ∨ n = s.claims.sphincs.length ∨
    ∃ c ∈ w.children, n = c.statement.claims.xmss.length ∨ n = c.statement.claims.sphincs.length

theorem honest_split {ws : List E} (h : HonestEntry s w ("signers_split", ws)) :
    ∃ n, ws = Prover.listSplit n ∧ ListLen s w n := by
  generalize hp : (("signers_split" : String), ws) = p at h
  cases h with
  | other ho => subst hp; exact (ho.1 rfl).elim
  | split n hn =>
      simp only [Prod.mk.injEq, true_and] at hp
      exact ⟨n, hp, hn⟩
  | blobs c mw _ => simp at hp
  | childMeta c _ => simp at hp

/-- The coverage table's slots: the declared claims and their duplicates, one a holder. -/
theorem slots_eq (hrel : NodeRelation guestBytecode guestSeed s w) :
    s.claims.xmss.length + (xPlan s w).duplicates.length + s.claims.sphincs.length +
      (sPlan s w).duplicates.length = w.xmssSignatures.length + w.sphincsSignatures.length +
        (w.children.map fun c => c.statement.claims.xmss.length + c.statement.claims.sphincs.length).sum := by
  have := Main.planSlots_eq hrel.1
  simp only [Coverage.planSlots, coverageSlots] at this
  rw [← (coveragePlan_eq _ _ _).1, ← (coveragePlan_eq _ _ _).1] at this
  exact this

/-- **A list's length is within the memory budget.** -/
theorem listLen_le (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w) {n : ℕ}
    (hn : ListLen s w n) : n ≤ 2 ^ 24 := by
  have hb := hlim.withinMemoryBudget
  simp only [NodeWitness.memoryBudget, NodeWitness.childClaimCount] at hb
  have hs := slots_eq hrel
  rcases hn with rfl | rfl | ⟨c, hc, hn⟩
  · omega
  · omega
  · have hle : c.statement.claims.xmss.length + c.statement.claims.sphincs.length ≤
        (w.children.map fun c => c.statement.claims.xmss.length + c.statement.claims.sphincs.length).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hc)
    omega

/-! ## Walks -/

theorem atom_head_mem {σ : Val} {a : Atom} {ss : List Stmt} {es : List Ev} {vs : List V}
    (h : walk σ (.atom a :: ss) = .ret es vs) : Ev.atom a ∈ es := by
  have e : walk σ (.atom a :: ss) = (walk σ ss).pre [.atom a] := by simp [walk, walk1, Out.seq]
  rw [e] at h
  cases hw : walk σ ss with
  | fall _ => rw [hw] at h; simp [Out.pre] at h
  | ret es' vs' =>
      rw [hw] at h
      simp only [Out.pre, Out.ret.injEq] at h
      rw [← h.1]
      exact List.mem_cons_self
  | stuck => rw [hw] at h; simp [Out.pre] at h

/-! ## `da_verify` -/

theorem da_padding_mul {rd : Reader} : ∀ args rets : List E, coreProgram.Rel rd "da_padding" args rets →
    ∃ nb x, args = [nb] ∧ rets = [x] ∧ gen ^ 32 = x * nb := by
  intro args rets
  rw [rel_iff_fnSem Da.find_da_padding]
  vc
  rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, word_two_pow (a := 32) (by decide)]
  rintro ⟨nb, rfl, inv, hinv, y, t1, l1, hk, t2, l2, x, hx, rfl⟩
  exact ⟨nb, x, rfl, rfl, hx⟩

variable {rd : Reader} {σ : Val}

/-- **`da_verify`'s hand fact** at the node's rows, from the pops. -/
theorem da_verify_hand (hlim : DeployedLimits s w) {C₂ : ℕ}
    (hp : PathIn coreProgram rd (Prover.honestPushes guestBytecode guestSeed s w) "da_verify" σ) :
    HandFact coreProgram (whCertAt (daWordsC (itemsOf s w).rows) C₂) (whHandAt (daWordsC (itemsOf s w).rows) C₂)
      whOut "da_verify" σ := by
  have hj : coreIdx "da_verify" = Data.whidxDa := coreIdx_of_name wh_nodeIdx.nd
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
  refine ⟨whOut_not (by rw [hj]; decide), fun h hh' fn hfn => ⟨σ, SameOnPath.refl, ?_⟩⟩
  have e1 : whHandAt (daWordsC (itemsOf s w).rows) C₂ "da_verify" = Data.whhandJ 26 := by
    simp only [whHandAt, handAt, hj]; rfl
  rw [e1] at hh'
  have hv : h.vps = [.n 1, .n 2] := by
    have h0 : (Data.whhandJ 26).map Hand.vps = some [.n 1, .n 2] := rfl
    rw [hh'] at h0; exact Option.some.inj h0
  have hpre : h.pre = [(1, 2 ^ 64), (2, 2 ^ 64)] := by
    have h0 : (Data.whhandJ 26).map Hand.pre = some [(1, 2 ^ 64), (2, 2 ^ 64)] := rfl
    rw [hh'] at h0; exact Option.some.inj h0
  have hb : affEqB 3 h.b ⟨96198, [(1, 120893), (2, 18)]⟩ = true := by
    have h0 : (Data.whhandJ 26).map (fun h => affEqB 3 h.b ⟨96198, [(1, 120893), (2, 18)]⟩) = some true := by
      decide +kernel
    rw [hh'] at h0; exact Option.some.inj h0
  have e2 : whCertAt (daWordsC (itemsOf s w).rows) C₂ "da_verify" =
      .stat [] ⟨daWordsC (itemsOf s w).rows, []⟩ [] := by
    simp only [whCertAt, certAt, hj, ↓reduceIte]
  rw [e2]
  rw [coreProgram_find?_at (j := idx% «da_verify») rfl] at hfn
  obtain rfl := Option.some.inj hfn
  intro _
  rw [hv, hpre, aff_eq hb, Aff.eval_mk_nil]
  have hrows : (itemsOf s w).rows = some mw.rows.length := by
    simp [itemsOf, NodeItems.ofWitness, hm]
  simp only [List.map_cons, List.map_nil]
  have a1 : argExp ((fn% «da_verify»).params.map σ ++ [σ (.n 1), σ (.n 2)]) 1 = mw.rows.length := g1.logG
  have a2 : argExp ((fn% «da_verify»).params.map σ ++ [σ (.n 1), σ (.n 2)]) 2 = 32 - mw.rows.length := g2.logG
  refine ⟨argsPre_of (by simp) ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl)
    exacts [⟨_, g1⟩, ⟨_, g2⟩]
  · simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, a1, a2, hrows, daWordsC,
      Option.map_some, Option.getD_some]
    omega

/-! ## `claim_list_digest` on a nonempty list -/

/-- **`list_split`'s tree within `H`**: its three returns are one of `H`'s `signers_split` entries, and
their product is its argument. -/
theorem list_split_in {H : List Pop} {ng : E} {rets : List E}
    (h : RelIn coreProgram rd H "list_split" [ng] rets) :
    ("signers_split", rets) ∈ H ∧ ∃ a b c, rets = [a, b, c] ∧ ng = a ^ 136 * b ^ 17 * c := by
  obtain ⟨t, htn, htv, htp⟩ := h
  cases t with
  | phantom => exact htv.elim
  | node f σ' bufs kids =>
  simp only [Memory.Tree.name] at htn
  subst htn
  obtain ⟨fn, hf, hp, es, vs, hw, hr, hes, -⟩ := htv
  rw [Digest.find_list_split] at hf
  obtain rfl := Option.some.inj hf
  have hb : (fn% «list_split»).body = (fn% «list_split»).body.dropLast ++ [.ret [.n 28, .n 29, .n 30]] :=
    stmtsEqb_sound (by decide +kernel)
  have hst : (fn% «list_split»).body.dropLast.all Stmt.straight = true := by decide +kernel
  have hw' := hw
  rw [hb, walk_straight σ' _ _ hst] at hw'
  obtain ⟨rfl, rfl⟩ := Out.ret.inj hw'
  have hin : ∀ a, a ∈ VsC.atomsOf (fn% «list_split»).body.dropLast →
      Ev.atom a ∈ (fn% «list_split»).body.dropLast.flatMap (slEvs σ') := fun a ha =>
    List.mem_flatMap.mpr ⟨_, atom_mem_of_atomsOf ha, by simp [slEvs]⟩
  have hm : Atom.hint (.witness "signers_split" (.stack [.n 1, .n 2, .n 3])) ∈
        VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.copy (.n 28) (.n 1) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.copy (.n 29) (.n 2) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.copy (.n 30) (.n 3) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.assertEq (.n 27) (.n 0) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 13) (.n 1) (.n 1) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 14) (.n 13) (.n 13) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 15) (.n 14) (.n 14) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 16) (.n 15) (.n 15) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 17) (.n 16) (.n 1) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 18) (.n 17) (.n 17) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 19) (.n 18) (.n 18) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 20) (.n 19) (.n 19) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 21) (.n 2) (.n 2) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 22) (.n 21) (.n 21) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 23) (.n 22) (.n 22) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 24) (.n 23) (.n 23) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 25) (.n 24) (.n 2) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 26) (.n 20) (.n 25) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast ∧
      Atom.mul (.n 27) (.n 26) (.n 3) ∈ VsC.atomsOf (fn% «list_split»).body.dropLast := by
    decide +kernel
  obtain ⟨mh, m28, m29, m30, m0, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27⟩ := hm
  have c28 : σ' (.n 28) = σ' (.n 1) := hes _ (hin _ m28)
  have c29 : σ' (.n 29) = σ' (.n 2) := hes _ (hin _ m29)
  have c30 : σ' (.n 30) = σ' (.n 3) := hes _ (hin _ m30)
  simp only [List.map_cons, List.map_nil, c28, c29, c30] at hr
  subst hr
  refine ⟨htp _ ?_, _, _, _, rfl, ?_⟩
  · rw [pops_node (bufs := bufs) (kids := kids) Digest.find_list_split hw]
    exact mem_splice_of_evPops (hint_stack_mem (hin _ mh))
  · have e0 : σ' (.n 27) + σ' (.n 0) = 0 := hes _ (hin _ m0)
    have e13 : σ' (.n 13) = _ := hes _ (hin _ m13)
    have e14 : σ' (.n 14) = _ := hes _ (hin _ m14)
    have e15 : σ' (.n 15) = _ := hes _ (hin _ m15)
    have e16 : σ' (.n 16) = _ := hes _ (hin _ m16)
    have e17 : σ' (.n 17) = _ := hes _ (hin _ m17)
    have e18 : σ' (.n 18) = _ := hes _ (hin _ m18)
    have e19 : σ' (.n 19) = _ := hes _ (hin _ m19)
    have e20 : σ' (.n 20) = _ := hes _ (hin _ m20)
    have e21 : σ' (.n 21) = _ := hes _ (hin _ m21)
    have e22 : σ' (.n 22) = _ := hes _ (hin _ m22)
    have e23 : σ' (.n 23) = _ := hes _ (hin _ m23)
    have e24 : σ' (.n 24) = _ := hes _ (hin _ m24)
    have e25 : σ' (.n 25) = _ := hes _ (hin _ m25)
    have e26 : σ' (.n 26) = _ := hes _ (hin _ m26)
    have e27 : σ' (.n 27) = _ := hes _ (hin _ m27)
    have hng : ng = σ' (.n 0) := by
      have hpar : (fn% «list_split»).params = [.n 0] := rfl
      rw [hpar] at hp
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
      exact hp.symm
    rw [hng, ← e_add_eq_zero_iff.mp e0, e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13]
    ring

/-- **`claim_list_digest`'s hand fact on a nonempty list**, from the pops. -/
theorem claim_else_hand (hrel : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    {C₁ C₂ : ℕ} (hp : PathIn coreProgram rd (Prover.honestPushes guestBytecode guestSeed s w) "claim_list_digest" σ)
    (h3 : σ (.n 3) ≠ 0) :
    HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut "claim_list_digest" σ := by
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
  obtain ⟨hmem, a, b, c, habc, hng⟩ := list_split_in he.1
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
  have g1 : GPow (σ (.n 1)) n := by
    refine ⟨?_, by omega⟩
    rw [hng, g12.1, g13.1, g14.1, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  refine handFact_of (j := 20) (n := 4) (bS := ⟨5071, [(2, 2028), (3, 316)]⟩) (bOS := ⟨7283, [(1, 15)]⟩)
    (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide)
    (by decide) rfl rfl (by decide +kernel) (by decide +kernel) SameOnPath.refl ?_
  intro fn hfn _
  rw [Digest.find_claim_list_digest] at hfn
  obtain rfl := Option.some.inj hfn
  have a1 : argExp ((fn% «claim_list_digest»).params.map σ) 1 = n := g1.logG
  have a2 : argExp ((fn% «claim_list_digest»).params.map σ ++ [σ (.n 12), σ (.n 13)]) 2 = n / 136 := g12.logG
  have a3 : argExp ((fn% «claim_list_digest»).params.map σ ++ [σ (.n 12), σ (.n 13)]) 3 = n % 136 / 17 :=
    g13.logG
  refine ⟨argsPre_of (by decide) ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro q (rfl | rfl)
    exacts [⟨_, g12⟩, ⟨_, g13⟩]
  · simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, a1, a2, a3]
    omega

end
end LeanVM.Guest.Complete
