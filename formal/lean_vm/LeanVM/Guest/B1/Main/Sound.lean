/-
  LeanVM.Guest.B1.Main.Sound

  B1 for `main` (G:3119-3316; TRIAGE #76), soundness: a run of the guest's core IR whose public
  input is a digest `D` gives a seed, a statement of digest `D` and a witness of `NodeRel`.
-/

module

public import LeanVM.Guest.B1.Main.Template
public import LeanVM.Guest.B1.Main.Cover
public import LeanVM.Guest.B1.Main.AggSound

/-!
# `main`, soundly

The statement `main` proves is its public input's: its seed `fs_seed`, its declared claim lists
(the prefixes of the tables `claim_list_digest` hashes, and the DA roots `da_list_digest` hashes),
and the deferred claim it hashes at `defer_stmt`, the leaf's zeros or `aggregate_claims`'s
batching. The witness holds every declared claim: every slot of the coverage table is written
(`cover_all`), and its writer certifies it (`SlotGood`): a raw signature or a direct blob
matrix, or a child whose statement makes the claim. The children are `__loop5`'s
(`ChildAt`): their statements under the same seed, verified by `verify_sub`.

`main_sound` assumes the callees' soundness (`Callees`) and that the memory is a valid execution's
(`MemOk`); `aggregate_claims`' is `aggregate_claims_sound`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

variable {bytecode : List K} {rd : Reader}

/-! ## What a slot's writer certifies -/

/-- leanXMSS slot `s`: a signature on its claim, or a child making it. -/
abbrev XGood (rd : Reader) (lxT : E) (chs : List Child) (s : ℕ) : Prop :=
  (∃ σ, xmssVerify (entryX rd lxT s).1 (entryX rd lxT s).2 σ = true) ∨
    ∃ (i : ℕ) (ch : Child), chs[i]? = some ch ∧ entryX rd lxT s ∈ ch.statement.claims.xmss

/-- leanSPHINCS slot `s`: a signature on its claim, or a child making it. -/
abbrev SGood (rd : Reader) (spT : E) (chs : List Child) (s : ℕ) : Prop :=
  (∃ σ, sphincsVerify (entryS rd spT s).1 (entryS rd spT s).2 σ = true) ∨
    ∃ (i : ℕ) (ch : Child), chs[i]? = some ch ∧ entryS rd spT s ∈ ch.statement.claims.sphincs

/-- DA slot `i`: its claim opened by a blob matrix, or made by a child. -/
abbrev DGood (rd : Reader) (daR : E) (chs : List Child) (i : ℕ) : Prop :=
  ∀ cl, DaAt rd daR i cl → (∃ w : Da.Witness, w.Opens cl.1 cl.2) ∨
    ∃ (j : ℕ) (ch : Child), chs[j]? = some ch ∧ cl ∈ ch.statement.claims.da

/-- Slot `s` of the coverage table, in its region, is certified. -/
def SlotGood (rd : Reader) (lxT spT daR : E) (chs : List Child) (Lx Ls s : ℕ) : Prop :=
  (s < Lx → XGood rd lxT chs s) ∧ (Lx ≤ s → s < Lx + Ls → SGood rd spT chs (s - Lx)) ∧
    (Lx + Ls ≤ s → DGood rd daR chs (s - (Lx + Ls)))

theorem slotGood_x {lxT spT daR : E} {chs : List Child} {Lx Ls s : ℕ} (hs : s < Lx)
    (h : XGood rd lxT chs s) : SlotGood rd lxT spT daR chs Lx Ls s :=
  ⟨fun _ => h, fun h1 _ => absurd h1 (by omega), fun h1 => absurd h1 (by omega)⟩

theorem slotGood_s {lxT spT daR : E} {chs : List Child} {Lx Ls s : ℕ} (hs : s < Ls)
    (h : SGood rd spT chs s) : SlotGood rd lxT spT daR chs Lx Ls (Lx + s) :=
  ⟨fun h1 => absurd h1 (by omega), fun _ _ => by rwa [Nat.add_sub_cancel_left],
    fun h1 => absurd h1 (by omega)⟩

theorem slotGood_d {lxT spT daR : E} {chs : List Child} {Lx Ls i : ℕ} (h : DGood rd daR chs i) :
    SlotGood rd lxT spT daR chs Lx Ls (Lx + Ls + i) :=
  ⟨fun h1 => absurd h1 (by omega), fun _ h2 => absurd h2 (by omega),
    fun _ => by rwa [Nat.add_sub_cancel_left]⟩

/-- The number of claims a child makes. -/
def nOf (ch : Child) : ℕ :=
  ch.statement.claims.xmss.length + ch.statement.claims.sphincs.length +
    ch.statement.claims.da.length

/-- The running counts: `b0`, then each child's claims added. -/
def counts (b0 : ℕ) (chs : List Child) (c : ℕ) : ℕ :=
  b0 + ∑ i ∈ Finset.range c, (chs[i]?.map nOf).getD 0

theorem counts_succ (b0 : ℕ) (chs : List Child) (c : ℕ) (hc : c < chs.length) :
    counts b0 chs (c + 1) = counts b0 chs c + nOf chs[c] := by
  rw [counts, counts, Finset.sum_range_succ, List.getElem?_eq_getElem hc]
  simp only [Option.map_some, Option.getD_some]
  ring

theorem counts_mono (b0 : ℕ) (chs : List Child) (c : ℕ) :
    counts b0 chs c ≤ counts b0 chs (c + 1) := by
  rw [counts, counts, Finset.sum_range_succ]; omega

theorem counts_le (b0 : ℕ) (chs : List Child) (hn : ∀ c (hc : c < chs.length), nOf chs[c] ≤ 2 ^ 18) :
    ∀ c ≤ chs.length, counts b0 chs c ≤ b0 + c * 2 ^ 18
  | 0, _ => by simp [counts]
  | c + 1, h => by
    rw [counts_succ b0 chs c (by omega)]
    have := counts_le b0 chs hn c (by omega)
    have := hn c (by omega)
    rw [Nat.succ_mul]; omega

/-! ## The writers -/

/-- **Every mark certifies its slot**: the raw signatures' (`__loop3`, `__loop4`), the direct
DA's, and each child's claims', the marks of child `c` from its count `counts c`. -/
theorem writers_good {F : Frame} {seed : Digest} {chs : List Child} {a2 a5 a7 : ℕ}
    (hdaC : F.daC = F.cover * gen ^ (F.Lx + F.Ls))
    (h3 : ∀ i < a2, ∃ s < F.Lx, LoadHolds rd F.cover s (gen ^ i) ∧
      XmssSigned rd (F.lxT * gen ^ (4 * s)))
    (h4 : ∀ j < a5, ∃ s < F.Ls, LoadHolds rd F.cover (F.Lx + s) (gen ^ (a2 + j)) ∧
      SphincsSigned rd (F.spT * gen ^ (4 * s)))
    (ha7 : a7 ≤ 1)
    (hd : a7 = 1 → ∃ i < F.Md, LoadHolds rd F.daC i (gen ^ (a2 + a5)) ∧
      ∀ cl, DaAt rd F.daR i cl → ∃ w : Da.Witness, w.Opens cl.1 cl.2)
    (hch : ∀ c (hc : c < chs.length), ChildAt bytecode rd F seed c chs[c])
    (hbase : ∀ c ≤ chs.length, LoadHolds rd F.written c (gen ^ counts (a2 + a5 + a7) chs c)) :
    ∀ e < counts (a2 + a5 + a7) chs chs.length, ∃ s < F.Lx + F.Ls + F.Md,
      LoadHolds rd F.cover s (gen ^ e) ∧ SlotGood rd F.lxT F.spT F.daR chs F.Lx F.Ls s := by
  intro e he
  rcases Nat.lt_or_ge e a2 with h1 | h1
  · obtain ⟨s, hs, hl, a, b, c, d, hr, σ', hv⟩ := h3 e h1
    refine ⟨s, by omega, hl, slotGood_x hs ?_⟩
    exact Or.inl ⟨σ', by rwa [entryX_of_reads hr]⟩
  rcases Nat.lt_or_ge e (a2 + a5) with h2 | h2
  · obtain ⟨s, hs, hl, a, b, c, d, hr, σ', hv⟩ := h4 (e - a2) (by omega)
    rw [show a2 + (e - a2) = e by omega] at hl
    refine ⟨F.Lx + s, by omega, hl, slotGood_s hs ?_⟩
    exact Or.inl ⟨σ', by rwa [entryS_of_reads hr]⟩
  rcases Nat.lt_or_ge e (a2 + a5 + a7) with h5 | h5
  · obtain ⟨i, hi, hl, hw⟩ := hd (by omega)
    rw [hdaC, loadHolds_mul_gen_pow, show a2 + a5 = e by omega] at hl
    exact ⟨F.Lx + F.Ls + i, by omega, hl, slotGood_d fun cl hcl => Or.inl (hw cl hcl)⟩
  obtain ⟨c, hc, hc1, hc2⟩ := exists_segment (counts (a2 + a5 + a7) chs)
    (counts_mono (a2 + a5 + a7) chs) (show counts (a2 + a5 + a7) chs 0 ≤ e by simpa [counts])
    chs.length he
  rw [counts_succ _ _ _ hc, nOf] at hc2
  obtain ⟨base, hw0, -, -, -, -, hX, hS, hD, -⟩ := hch c hc
  have hb := loadHolds_unique hw0 (hbase c (by omega))
  subst hb
  set b := counts (a2 + a5 + a7) chs c
  have hget : chs[c]? = some chs[c] := List.getElem?_eq_getElem hc
  rcases Nat.lt_or_ge e (b + chs[c].statement.claims.xmss.length) with g1 | g1
  · obtain ⟨s, hs, hl, he'⟩ := hX (e - b) (by omega)
    rw [← pow_add, show b + (e - b) = e by omega] at hl
    exact ⟨s, by omega, hl, slotGood_x hs (Or.inr ⟨c, chs[c], hget, List.mem_of_getElem? he'⟩)⟩
  rcases Nat.lt_or_ge e (b + chs[c].statement.claims.xmss.length +
    chs[c].statement.claims.sphincs.length) with g2 | g2
  · obtain ⟨s, hs, hl, he'⟩ := hS (e - b - chs[c].statement.claims.xmss.length) (by omega)
    rw [← pow_add, show b + (chs[c].statement.claims.xmss.length +
      (e - b - chs[c].statement.claims.xmss.length)) = e by omega] at hl
    exact ⟨F.Lx + s, by omega, hl,
      slotGood_s hs (Or.inr ⟨c, chs[c], hget, List.mem_of_getElem? he'⟩)⟩
  · obtain ⟨i, hi, hl, hcl⟩ := hD (e - b - chs[c].statement.claims.xmss.length -
      chs[c].statement.claims.sphincs.length) (by omega)
    rw [← pow_add, show b + (chs[c].statement.claims.xmss.length +
      chs[c].statement.claims.sphincs.length + (e - b - chs[c].statement.claims.xmss.length -
      chs[c].statement.claims.sphincs.length)) = e by omega, hdaC, loadHolds_mul_gen_pow] at hl
    refine ⟨F.Lx + F.Ls + i, by omega, hl, slotGood_d fun cl hcl' => Or.inr ?_⟩
    have hcl'' := List.getElem?_eq_getElem (l := chs[c].statement.claims.da)
      (i := e - b - chs[c].statement.claims.xmss.length - chs[c].statement.claims.sphincs.length)
      (by omega)
    have := daAt_unique hcl' (hcl _ hcl'')
    subst this
    exact ⟨c, chs[c], hget, List.mem_of_getElem? hcl''⟩

end
end LeanVM.Guest.B1.Main

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

variable {bytecode : List K} {rd : Reader}

/-! ## `main` -/

theorem find_main : coreProgram.find? "main" = some Data.core0 :=
  Program.find?_of_indexOf? (j := 0) (by decide +kernel) rfl

theorem cellAt_of_readsAt {p : E} {cs : List E} (h : ReadsAt rd p cs) {k : ℕ} (hk : k < cs.length) :
    cellAt rd p k = cs.getD k 0 := by
  rw [List.getD_eq_getElem _ _ hk]; exact cellAt_of_load (h k hk)

theorem load_one {v : E} (h : LoadHolds rd 1 0 v) : rd 1 = some v := by
  have h2 := h.2
  rw [← ofK_one, limb_ofK] at h2
  simpa [Parameters.gpow] using h2

theorem load_gen {v : E} (h : LoadHolds rd gen 0 v) : rd g = some v := by
  have h2 := h.2
  rw [gen_eq_ofK, limb_ofK] at h2
  simpa [Parameters.gpow] using h2

theorem deferredShaped_iff {bytecode : List K} (hlen : bytecode.length = 2 ^ 22) (c : DeferredClaim) :
    c.Shaped bytecode ↔ c.bytecodePoint.length = 22 ∧ c.matrixPoint.length = 28 := by
  rw [DeferredClaim.Shaped, hlen, Nat.log2_two_pow]
  rfl

/-- **`main`, soundly** (G:3119-3316; TRIAGE #76): on a memory of a valid execution whose public
input (cells `g^0`, `g^1`) is the digest `D`, a run of `main` gives a seed and a statement of
digest `D` that a witness holds (`NodeRel`) for the guest `bytecode` of `2^22` words, given the
callees' soundness. -/
theorem main_sound (hlen : bytecode.length = 2 ^ 22) (hm : MemOk rd) (H : Callees bytecode rd)
    {D : Digest} (hpub0 : rd 1 = some (digestScalars D).1) (hpub1 : rd g = some (digestScalars D).2)
    (h : coreProgram.Rel rd "main" [] []) :
    ∃ seed s w, statementDigest seed s = D ∧ NodeRel bytecode seed s w := by
  rw [rel_iff_sem find_main] at h
  obtain ⟨σ, -, h⟩ := h
  rw [core0_body, mainBody, holdsList_append, holdsList_noRet mainPre rfl] at h
  obtain ⟨hpre, h⟩ := h
  rw [Stmt.HoldsList, holds_ite_noRet (.n 112) daBranch [] rfl rfl, holdsList_append,
    holdsList_noRet mainMid rfl] at h
  obtain ⟨hite1, hmid, h⟩ := h
  rw [Stmt.HoldsList, holds_ite_noRet (.n 155) leafT aggT rfl rfl] at h
  obtain ⟨hite2, hpost⟩ := h
  simp only [mainPre, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    word_gmax, word_g16, word_g257, word_gen, word_one, word_iv0, word_iv1, word_md64] at hpre
  obtain ⟨-, c8, rc0, c12, rc1, c16, rc2, c20, rc3, c24, rc4, c28, rc5, c32, rc6, c36, rc7, -,
    c42, rc40, c46, rc41, h50, -, -, h55, h56, h57, h58, c59, rc58, -, het, -, -, -, -, -, -, -, -,
    hdl, -, -, -, -, -, -, hcx, hcs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c97, c98, c99, hbl, -, l100, l101, -, h104, h105, h106, h107, -, hl3, h108, h109, h110, -, hl4,
    h111, h112, -⟩ := hpre
  simp only [mainMid, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    word_gen, word_one] at hmid
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h146, h147, l147,
    h148, h149, h150, -, hl5, h151, l152, he152, -, h154, h155, -⟩ := hmid
  simp only [mainPost, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    word_gen, word_one] at hpost
  obtain ⟨hsd, h211, l212, he212, h213, h214, h215, l216, he216, -⟩ := hpost
  -- the counts
  obtain ⟨a0, ha0, e0⟩ := rc_const hm (by norm_num) c8 rc0
  obtain ⟨a1, ha1, e1⟩ := rc_const hm (by norm_num) c12 rc1
  obtain ⟨a2, ha2, e2⟩ := rc_const hm (by norm_num) c16 rc2
  obtain ⟨a3, ha3, e3⟩ := rc_const hm (by norm_num) c20 rc3
  obtain ⟨a4, ha4, e4⟩ := rc_const hm (by norm_num) c24 rc4
  obtain ⟨a5, ha5, e5⟩ := rc_const hm (by norm_num) c28 rc5
  obtain ⟨a6, ha6, e6⟩ := rc_const hm (by norm_num) c32 rc6
  obtain ⟨a7, ha7, e7⟩ := rc_const hm (c := 1) (by norm_num) (by rw [c36, pow_one]) rc7
  obtain ⟨a40, ha40, e40⟩ := rc_const hm (by norm_num) c42 rc40
  obtain ⟨a41, ha41, e41⟩ := rc_const hm (by norm_num) c46 rc41
  obtain ⟨t, ht, et⟩ := rc_const hm (by norm_num) c59 rc58
  have e55 : σ (.n 55) = gen ^ (a0 + a1) := by rw [h55, e0, e1, ← pow_add]
  have e56 : σ (.n 56) = gen ^ (a3 + a4) := by rw [h56, e3, e4, ← pow_add]
  have e50 : σ (.n 50) = gen ^ (a40 + a41) := by rw [h50, e40, e41, ← pow_add]
  have e57 : σ (.n 57) = gen ^ (a0 + a1 + (a3 + a4)) := by rw [h57, e55, e56, ← pow_add]
  have hT : t = a0 + a1 + (a3 + a4) + (a40 + a41) :=
    gen_pow_inj' (by omega) (by omega) (et.symm.trans (by rw [h58, e57, e50, ← pow_add]))
  -- the tables
  have htab : ExpTables rd (σ (.n 65)) (σ (.n 66)) := (exponent_tables_iff rd [] _).mp het
  have hsq := squaresTable_of_expTables htab
  -- the declared lists
  obtain ⟨dcl, hdl16, hn40, hDCA, hdd⟩ := H.da_list_digest _ _ _ _ hdl
  have hdlen : dcl.length = a40 := gen_pow_inj' (by omega) (by omega) (hn40.symm.trans e40)
  obtain ⟨nx, hnx, hn0, csX, hlX, hRX, hdX⟩ := H.claim_list_digest _ _ _ _ _ hsq hcx
  have hnx' : a0 = nx := gen_pow_inj' (by omega) (by omega) (e0.symm.trans hn0)
  obtain ⟨ns, hns, hn3, csS, hlS, hRS, hdS⟩ := H.claim_list_digest _ _ _ _ _ hsq hcs
  have hns' : a3 = ns := gen_pow_inj' (by omega) (by omega) (e3.symm.trans hn3)
  subst hnx' hns'
  rw [← xmssListDigest_claims hlX] at hdX
  rw [← sphincsListDigest_claims hlS] at hdS
  -- the signer set
  rw [c97, c98, c99, show σ (.n 81) = _ from congrArg Prod.fst hdX,
    show σ (.n 82) = _ from congrArg Prod.snd hdX, show σ (.n 83) = _ from congrArg Prod.fst hdS,
    show σ (.n 84) = _ from congrArg Prod.snd hdS] at hbl
  have hsig := signers_compress hbl
  -- the own statement's digest
  obtain ⟨seed, sig, da, cells, hcl, hseed, hs0, hs1, hda, hcells, hown⟩ :=
    H.statement_digest _ _ _ _ _ _ _ _ hsd
  have hsg : sig = signersDigest (xmssClaims csX) (sphincsClaims csS) := by
    apply digestScalars_injective
    rw [signersDigest, ← hsig, ← loadHolds_unique hs0 l100, ← loadHolds_unique hs1 l101]
  have hdg : da = daListDigest dcl := digestScalars_injective (hda.symm.trans hdd)
  subst hsg hdg
  have hD : stmtDigestOf seed (signersDigest (xmssClaims csX) (sphincsClaims csS))
      (daListDigest dcl) cells = D := by
    apply digestScalars_injective
    rw [← hown]
    rw [h211] at l212
    rw [h215, h213, h214, one_mul] at l216
    have q0 := Option.some.inj ((load_one l212).symm.trans hpub0)
    have q1 := Option.some.inj ((load_gen l216).symm.trans hpub1)
    rw [← e_add_eq_zero_iff.mp he212, ← e_add_eq_zero_iff.mp he216, q0, q1]
  -- the raw signatures
  have raw3 := loop_sound (rd := rd) (f := "__loop3")
    (ps := [σ (.n 2), σ (.n 55), σ (.n 103), σ (.n 77)]) (m := a2) (N := σ (.n 2))
    (by unfold ordG; omega) e2 (fun x hx => loop3_step hm H (M := a0 + a1) (by omega) e55 x hx)
    (by rw [h106, h105, h107] at hl3; exact hl3)
  have raw4 := loop_sound (rd := rd) (f := "__loop4")
    (ps := [σ (.n 5), σ (.n 56), σ (.n 103), σ (.n 55), σ (.n 2), σ (.n 80)]) (m := a5)
    (N := σ (.n 5)) (by unfold ordG; omega) e5
    (fun x hx => loop4_step hm H (M := a3 + a4) (Lx := a0 + a1) (by omega) e56 e55 x hx)
    (by rw [h109, h108, h110] at hl4; exact hl4)
  -- the direct DA
  have hdirect : a7 = 1 → ∃ i < a40 + a41, LoadHolds rd (σ (.n 104)) i (gen ^ (a2 + a5)) ∧
      ∀ cl, DaAt rd (σ (.n 69)) i cl → ∃ w : Da.Witness, w.Opens cl.1 cl.2 := by
    intro h7
    have h0 : σ (.n 112) = 0 := by rw [h112, h111, e7, h7, pow_one]; exact e_add_self gen
    have hb := hite1.2.1 h0
    simp only [daBranch, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
      List.map_nil] at hb
    obtain ⟨hdv, h117, hcov, q0, q1, q2, q3, -⟩ := hb
    obtain ⟨root, vd, w, hr, hv, hw⟩ := H.da_verify _ _ _ _ _ hsq hdv
    obtain ⟨i, M, hM, hi, hsl, hmk, hrd⟩ := H.cover_da_root _ _ _ _ _ _ _ _ hcov
    have hMM : M = a40 + a41 := gen_pow_inj' (by omega) (by omega) (hsl.symm.trans e50)
    subst hMM
    refine ⟨i, hi, ?_, fun cl hcl => ⟨w, ?_⟩⟩
    · rw [h117, e2, e5, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero] at hmk
      exact hmk
    · have hroot : DaAt rd (σ (.n 69)) i (root, vd) := by
        unfold DaAt
        rw [← e_add_eq_zero_iff.mp q0, ← e_add_eq_zero_iff.mp q1, ← e_add_eq_zero_iff.mp q2,
          ← e_add_eq_zero_iff.mp q3, show σ (.n 113) = _ from congrArg Prod.fst hr,
          show σ (.n 114) = _ from congrArg Prod.snd hr, show σ (.n 115) = _ from congrArg Prod.fst hv,
          show σ (.n 116) = _ from congrArg Prod.snd hv] at hrd
        exact hrd
      rw [daAt_unique hcl hroot]
      exact hw
  -- the children
  let F : Frame := ⟨σ (.n 145), σ (.n 77), σ (.n 80), σ (.n 103), σ (.n 69), σ (.n 104),
    σ (.n 142), σ (.n 123), σ (.n 133), a0 + a1, a3 + a4, a40 + a41⟩
  have hkids := loop_sound (rd := rd) (f := "__loop5")
    (ps := [σ (.n 6), F.written, F.lxT, F.cover, σ (.n 55), σ (.n 66), F.spT, σ (.n 56), F.carried,
      F.daR, F.daC, σ (.n 50), σ (.n 63), σ (.n 64), F.cpi, σ (.n 65), F.cfresh]) (m := a6)
    (N := σ (.n 6)) (by unfold ordG; omega) e6
    (fun x hx => loop5_step (F := F) H e55 e56 e50 (by show a0 + a1 < 2 ^ 33; omega)
      (by show a3 + a4 < 2 ^ 33; omega) (by show a40 + a41 < 2 ^ 33; omega) hseed htab x hx)
    (by rw [h149, h148, h150] at hl5; exact hl5)
  obtain ⟨chs, hchl, hch⟩ := exists_list (P := fun c ch => ChildAt bytecode rd F seed c ch)
    (m := a6) (fun j hj => hkids j hj j rfl)
  have hb0 : LoadHolds rd F.written 0 (gen ^ (a2 + a5 + a7)) := by
    rw [h147, h146, e2, e5, e7, ← pow_add, ← pow_add] at l147
    exact l147
  have hbase : ∀ c ≤ chs.length, LoadHolds rd F.written c (gen ^ counts (a2 + a5 + a7) chs c) := by
    intro c hc
    induction c with
    | zero => simpa [counts] using hb0
    | succ c ih =>
      obtain ⟨base, hw0, hw1, -⟩ := hch c (by omega)
      have := loadHolds_unique hw0 (ih (by omega))
      rw [this, ← pow_add] at hw1
      rw [counts_succ _ _ _ (by omega), nOf]
      exact hw1
  have hnOf : ∀ c (hc : c < chs.length), nOf chs[c] ≤ 2 ^ 18 := by
    intro c hc
    obtain ⟨-, -, -, h1, h2, h3, -⟩ := hch c hc
    rw [nOf]; omega
  have hfin : counts (a2 + a5 + a7) chs chs.length = t := by
    rw [h151, e6, loadHolds_mul_gen_pow, Nat.add_zero, e_add_eq_zero_iff.mp he152, et,
      ← hchl] at l152
    have := counts_le (a2 + a5 + a7) chs hnOf chs.length le_rfl
    exact gen_pow_inj' (by omega) (by omega) (loadHolds_unique (hbase chs.length le_rfl) l152)
  -- the coverage
  have hdaC : F.daC = F.cover * gen ^ (F.Lx + F.Ls) := by
    show σ (.n 104) = σ (.n 103) * gen ^ (a0 + a1 + (a3 + a4))
    rw [h104, e57]
  have hgood := cover_all (rd := rd) (cover := F.cover) (T := t) (by omega)
    (Good := SlotGood rd F.lxT F.spT F.daR chs F.Lx F.Ls) fun e he => by
      obtain ⟨s, hs, hl, hg⟩ := writers_good (F := F) (seed := seed) (chs := chs) (a2 := a2)
        (a5 := a5) (a7 := a7) hdaC raw3
        (fun j hj => by
          obtain ⟨s, hs, hl, hsg⟩ := raw4 j hj
          rw [e2, ← pow_add] at hl
          exact ⟨s, hs, hl, hsg⟩)
        ha7 hdirect hch hbase e (by rw [hfin]; exact he)
      have hFt : F.Lx + F.Ls + F.Md = t := by
        show a0 + a1 + (a3 + a4) + (a40 + a41) = t; omega
      exact ⟨s, by omega, hl, hg⟩
  -- the holders
  have hX : ∃ hs, List.Forall₂ (XmssHeld chs) (xmssClaims csX) hs := by
    apply exists_forall₂
    intro cl hcl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hcl
    have hk' : k < a0 := by rwa [(xmssClaims_spec a0 csX hlX).1] at hk
    have hent : (xmssClaims csX)[k] = entryX rd F.lxT k := by
      rw [(xmssClaims_spec a0 csX hlX).2.1 k hk, entryX, cellAt_of_readsAt hRX (by omega),
        cellAt_of_readsAt hRX (by omega), cellAt_of_readsAt hRX (by omega),
        cellAt_of_readsAt hRX (by omega)]
    rcases (hgood k (by omega)).1 (by show k < a0 + a1; omega) with ⟨σ', hv⟩ | ⟨i, ch, hi, hmem⟩
    · exact ⟨.direct σ', by rw [hent]; exact hv⟩
    · exact ⟨.child i, ch, hi, by rw [hent]; exact hmem⟩
  have hS : ∃ hs, List.Forall₂ (SphincsHeld chs) (sphincsClaims csS) hs := by
    apply exists_forall₂
    intro cl hcl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hcl
    have hk' : k < a3 := by rwa [(sphincsClaims_spec a3 csS hlS).1] at hk
    have hent : (sphincsClaims csS)[k] = entryS rd F.spT k := by
      rw [(sphincsClaims_spec a3 csS hlS).2.1 k hk, entryS, cellAt_of_readsAt hRS (by omega),
        cellAt_of_readsAt hRS (by omega), cellAt_of_readsAt hRS (by omega),
        cellAt_of_readsAt hRS (by omega)]
    have := (hgood (F.Lx + k) (by show a0 + a1 + k < t; omega)).2.1 (by omega)
      (by show a0 + a1 + k < a0 + a1 + (a3 + a4); omega)
    rw [Nat.add_sub_cancel_left] at this
    rcases this with ⟨σ', hv⟩ | ⟨i, ch, hi, hmem⟩
    · exact ⟨.direct σ', by rw [hent]; exact hv⟩
    · exact ⟨.child i, ch, hi, by rw [hent]; exact hmem⟩
  have hDa : ∃ hs, List.Forall₂ (DaHeld chs) dcl hs := by
    apply exists_forall₂
    intro cl hcl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hcl
    have := (hgood (F.Lx + F.Ls + k) (by show a0 + a1 + (a3 + a4) + k < t; omega)).2.2
      (by omega)
    rw [Nat.add_sub_cancel_left] at this
    rcases this dcl[k] (daAt_of_claimsAt hDCA k hk) with ⟨w, hw⟩ | ⟨i, ch, hi, hmem⟩
    · exact ⟨.direct w, hw⟩
    · exact ⟨.child i, ch, hi, hmem⟩
  obtain ⟨hsX, hhX⟩ := hX
  obtain ⟨hsS, hhS⟩ := hS
  obtain ⟨hsD, hhD⟩ := hDa
  have hkidsOk : ∀ c ∈ chs, c.statement.defer.Shaped bytecode ∧
      verifyDeferred bytecode seed (statementDigest seed c.statement) c.fresh c.proof = true := by
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨-, -, -, -, -, -, -, -, -, h22, h28, -, -, -, -, -, hv⟩ := hch k hk
    exact ⟨(deferredShaped_iff hlen _).mpr ⟨h22, h28⟩, hv⟩
  have hdig : statementDigest seed ⟨⟨xmssClaims csX, sphincsClaims csS, dcl⟩, deferOfCells cells⟩ =
      D := by
    rw [statementDigest_eq, cells_deferOfCells hcl]; exact hD
  -- the deferred claim
  by_cases ha60 : a6 = 0
  · -- a leaf
    have hnil : chs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h0 : σ (.n 155) = 0 := by
      rw [h155, h154, e6, ha60, pow_zero]; exact e_add_self 1
    have hl := hite2.2.1 h0
    rw [leafT, Stmt.HoldsList, Stmt.Holds, holdsList_append, holdsList_append, holdsList_append,
      holdsList_range_flatten 22 (zeroStores 159 0) (fun _ => rfl),
      holdsList_range_flatten 28 (zeroStores 181 23) (fun _ => rfl)] at hl
    simp only [zeroStores, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_zero] at hl
    obtain ⟨-, hz1, -, hz2, -⟩ := hl
    have hz : ∀ k (h : k < cells.length), k < 22 → cells[k] = 0 := fun k h hk => by
      obtain ⟨hc, hl, -⟩ := hz1 k hk
      rw [hc, Nat.zero_add] at hl
      exact loadHolds_unique (hcells k h) hl
    have hz' : ∀ k (h : 23 + k < cells.length), k < 28 → cells[23 + k] = 0 := fun k h hk => by
      obtain ⟨hc, hl, -⟩ := hz2 k hk
      rw [hc] at hl
      exact loadHolds_unique (hcells (23 + k) h) hl
    refine ⟨seed, ⟨⟨xmssClaims csX, sphincsClaims csS, dcl⟩, deferOfCells cells⟩,
      ⟨chs, hsX, hsS, hsD, ⟨[], [], 0, 0, 0⟩⟩, hdig, ?_⟩
    refine ⟨(deferredShaped_iff hlen _).mpr (length_deferOfCells hcl), hkidsOk, hhX, hhS, hhD, ?_⟩
    simp only [hnil, ↓reduceIte]
    rw [DeferredClaim.AtZero, hlen, Nat.log2_two_pow, show 2 * blake2sR1csLogSize = 28 from rfl]
    refine ⟨List.ext_getElem (by simp [deferOfCells, hcl]) fun k h1 h2 => ?_,
      List.ext_getElem (by simp [deferOfCells, hcl]) fun k h1 h2 => ?_⟩
    · simp only [deferOfCells, List.getElem_take, List.getElem_replicate]
      exact hz k _ (by simpa [deferOfCells, hcl] using h1)
    · simp only [deferOfCells, List.getElem_take, List.getElem_drop, List.getElem_replicate]
      exact hz' k _ (by simpa [deferOfCells, hcl] using h1)
  · -- the batching
    have hne : σ (.n 155) ≠ 0 := by
      rw [h155, h154, e6]
      intro h0
      have := (gen_pow_eq_one_iff (by omega)).mp (e_add_eq_zero_iff.mp h0)
      omega
    have ha := hite2.2.2 hne
    simp only [aggT, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at ha
    obtain ⟨n_g, pis, fresh, carried, dp, hargs, -, hbat⟩ := aggregate_claims_sound _ _ ha.1
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
    let cs : List ChildClaims := chs.map fun c => ⟨statementDigest seed c.statement, c.fresh,
      c.statement.defer⟩
    have hchs : chs ≠ [] := fun hc => ha60 (by rw [← hchl, hc, List.length_nil])
    obtain ⟨hh, d, hbd, hd22, hd28, hdc⟩ := hbat cs (by simpa [cs] using hchs)
      (by simp [cs, hchl]; omega) (by simp [cs, hchl, e6])
      (fun c hc => by
        simp only [cs, List.length_map] at hc
        obtain ⟨-, -, -, -, -, -, -, -, -, h22, h28, hcar, hp0, hp1, hfs, hfr, -⟩ := hch c hc
        simp only [cs, List.getElem_map]
        exact ⟨hp0, hp1, hfs, hfr, h22, h28, hcar⟩)
    have hcd : cells = d.cells := readsAt_unique hcells hdc (by
      simp [hcl, DeferredClaim.cells, hd22, hd28])
    refine ⟨seed, ⟨⟨xmssClaims csX, sphincsClaims csS, dcl⟩, deferOfCells cells⟩,
      ⟨chs, hsX, hsS, hsD, hh⟩, hdig, ?_⟩
    refine ⟨(deferredShaped_iff hlen _).mpr (length_deferOfCells hcl), hkidsOk, hhX, hhS, hhD, ?_⟩
    simp only [hchs, ↓reduceIte]
    rw [hcd, deferOfCells_cells hd22 hd28]
    exact hbd

end
end LeanVM.Guest.B1.Main
