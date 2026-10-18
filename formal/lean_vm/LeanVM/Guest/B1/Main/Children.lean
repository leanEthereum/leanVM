/-
  LeanVM.Guest.B1.Main.Children

  `main`'s loop over its children (`__loop5`, G:3248-3290), read forward: per child, its
  statement rebuilt from this node's tables, its digest, its proof verified, its coverage marks.
-/

module

public import LeanVM.Guest.B1.Main.Loops

/-!
# The children

Iteration `c` of `__loop5` (at `x = g^c`) reads the running count `base = written[c]`, then:

* the child's two claim lists, rebuilt from this node's tables by `child_claim_list_digest` at
  hinted indices, every claim marking its coverage slot (`base·g^j`, then `base·g^(n_x + j)`);
* the signer set's digest of the two list digests, stored at `sub_hash`;
* its 53 deferred cells, hinted at `carried·g^(53c)`;
* its DA roots (`__loop100`), each marking a DA slot and copied from it, and their list digest;
* its statement's digest, stored at `child_pi·g^(2c)`, and `verify_sub` on that public input;
* the next count `written[c + 1] = base·g^(n_x + n_s + n_da)`.

`ChildAt bytecode rd F seed c ch` says all of it of a `Node.Child`, with the statement's claims
decoded from the table entries they read (`entryX`, `entryS`, `DaAt`) and the deferred claim from
its cells (`deferOfCells`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

variable {bytecode : List K} {rd : Reader}

/-- The pointers and region sizes `main` hands its children's loop. -/
structure Frame where
  /-- The running counts `written`. -/
  written : E
  /-- The leanXMSS table. -/
  lxT : E
  /-- The leanSPHINCS table. -/
  spT : E
  /-- The coverage table. -/
  cover : E
  /-- The DA roots. -/
  daR : E
  /-- The DA region of the coverage table. -/
  daC : E
  /-- The children's deferred cells. -/
  carried : E
  /-- The children's public inputs. -/
  cpi : E
  /-- The children's fresh claims. -/
  cfresh : E
  /-- The leanXMSS region's size. -/
  Lx : ℕ
  /-- The leanSPHINCS region's size. -/
  Ls : ℕ
  /-- The DA region's size. -/
  Md : ℕ

/-- **What iteration `c` of the children's loop establishes of the child `ch`**: the running
count `base` at `written[c]` and `base·g^n` at `written[c + 1]`, `n` its claims; each leanXMSS
claim `j` the table entry of a slot `s` of the leanXMSS region, which holds the mark `base·g^j`;
the same of its leanSPHINCS claims and DA claims, the marks continuing; its deferred claim of the
guest's shape at `carried·g^(53c)`; its statement's digest under `seed` at `child_pi·g^(2c)`; its
fresh claims at `child_fresh·g^(106c)`; and the deferring verifier accepting its proof. -/
def ChildAt (bytecode : List K) (rd : Reader) (F : Frame) (seed : Digest) (c : ℕ) (ch : Child) :
    Prop :=
  ∃ base : E, LoadHolds rd F.written c base ∧
    LoadHolds rd F.written (c + 1) (base * gen ^ (ch.statement.claims.xmss.length +
      ch.statement.claims.sphincs.length + ch.statement.claims.da.length)) ∧
    ch.statement.claims.xmss.length < 2 ^ 16 ∧ ch.statement.claims.sphincs.length < 2 ^ 16 ∧
    ch.statement.claims.da.length ≤ 16 ∧
    (∀ j < ch.statement.claims.xmss.length, ∃ s < F.Lx, LoadHolds rd F.cover s (base * gen ^ j) ∧
      ch.statement.claims.xmss[j]? = some (entryX rd F.lxT s)) ∧
    (∀ j < ch.statement.claims.sphincs.length, ∃ s < F.Ls,
      LoadHolds rd F.cover (F.Lx + s) (base * gen ^ (ch.statement.claims.xmss.length + j)) ∧
      ch.statement.claims.sphincs[j]? = some (entryS rd F.spT s)) ∧
    (∀ j < ch.statement.claims.da.length, ∃ i < F.Md,
      LoadHolds rd F.daC i (base * gen ^ (ch.statement.claims.xmss.length +
        ch.statement.claims.sphincs.length + j)) ∧
      ∀ cl, ch.statement.claims.da[j]? = some cl → DaAt rd F.daR i cl) ∧
    ch.statement.defer.bytecodePoint.length = 22 ∧ ch.statement.defer.matrixPoint.length = 28 ∧
    ReadsAt rd (F.carried * gen ^ (53 * c)) ch.statement.defer.cells ∧
    LoadHolds rd F.cpi (2 * c) (digestScalars (statementDigest seed ch.statement)).1 ∧
    LoadHolds rd F.cpi (2 * c + 1) (digestScalars (statementDigest seed ch.statement)).2 ∧
    FreshShaped ch.fresh ∧ ReadsAt rd (F.cfresh * gen ^ (106 * c)) (fixedCells ch.fresh) ∧
    verifyDeferred bytecode seed (statementDigest seed ch.statement) ch.fresh ch.proof = true

theorem find_loop5 : coreProgram.find? "__loop5" = some Data.core35 :=
  Program.find?_of_indexOf? (j := 35) (by decide +kernel) rfl

theorem gen_pow_pow (c k : ℕ) : (gen ^ c) ^ k = gen ^ (k * c) := by
  rw [← pow_mul, mul_comm]

/-- **Iteration `c` of `__loop5`**: the child it reads (`ChildAt`), then the next iteration while
`x·g ≠ N`. The regions are `g^Lx`, `g^Ls`, `g^Md`, the exponent tables at `glp`, `gsq`, the seed's
cells `seed0`, `seed1`. -/
theorem loop5_step (H : Callees bytecode rd) {F : Frame}
    {N gsq glp lxS spS daS seed0 seed1 : E} {seed : Digest} (hLx : lxS = gen ^ F.Lx)
    (hLs : spS = gen ^ F.Ls) (hMd : daS = gen ^ F.Md) (hLx' : F.Lx < 2 ^ 33)
    (hLs' : F.Ls < 2 ^ 33) (hMd' : F.Md < 2 ^ 33) (hseed : (seed0, seed1) = digestScalars seed)
    (ht : ExpTables rd glp gsq) (x : E)
    (h : coreProgram.Rel rd "__loop5" [x, N, F.written, F.lxT, F.cover, lxS, gsq, F.spT, spS,
      F.carried, F.daR, F.daC, daS, seed0, seed1, F.cpi, glp, F.cfresh] []) :
    (∀ c, x = gen ^ c → ∃ ch, ChildAt bytecode rd F seed c ch) ∧
      (x * gen + N ≠ 0 → coreProgram.Rel rd "__loop5" [x * gen, N, F.written, F.lxT, F.cover,
        lxS, gsq, F.spT, spS, F.carried, F.daR, F.daC, daS, seed0, seed1, F.cpi, glp,
        F.cfresh] []) := by
  rw [rel_iff_sem find_loop5] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [show Fn.params Data.core35 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8,
    .n 9, .n 10, .n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17] from rfl, List.map_cons,
    List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17⟩ := hp
  simp only [show Fn.body Data.core35 = Data.core35.body from rfl, Data.core35.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen, word_one,
    word_iv0, word_iv1, word_md64] at h
  obtain ⟨h18, l19, -, -, -, -, -, h30, h31, hcx, h34, hcs, h37, h38, h39, hbl, -, l40, l41,
    h43, h44, h45, h46, h47, h48, h49, h50, h51, -, -, -, -, h57, h58, -, h60, h61, h62, -, hl100,
    hdl, hsd, h67, h68, l65, h69, l66, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, hvs, h80,
    h81, h82, l81, h83, h84, h85, h86, h87, -, hcall, -⟩ := h
  refine ⟨fun c hx => ?_, fun hne => ?_⟩
  swap
  · have := hcall (by rw [h85, h84, h83, p0, p1]; exact hne)
    rwa [h87, h86, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16,
      p17] at this
  have hsq : SquaresTable rd (σ (.n 6)) := by rw [p6]; exact squaresTable_of_expTables ht
  -- the two claim lists
  obtain ⟨nx, hnx, hn20, offx, csx, hcsx, hRx, hdx⟩ :=
    H.child_claim_list_digest _ _ _ _ _ _ _ _ _ hsq hcx
  obtain ⟨ns, hns, hn21, offs, css, hcss, hRs, hds⟩ :=
    H.child_claim_list_digest _ _ _ _ _ _ _ _ _ hsq hcs
  obtain ⟨hlx, hgx, -⟩ := xmssClaims_spec nx csx hcsx
  obtain ⟨hls, hgs, -⟩ := sphincsClaims_spec ns css hcss
  rw [← xmssListDigest_claims hcsx] at hdx
  rw [← sphincsListDigest_claims hcss] at hds
  -- the signer set
  rw [h37, h38, h39, show σ (.n 32) = _ from congrArg Prod.fst hdx,
    show σ (.n 33) = _ from congrArg Prod.snd hdx, show σ (.n 35) = _ from congrArg Prod.fst hds,
    show σ (.n 36) = _ from congrArg Prod.snd hds] at hbl
  have hsig := signers_compress hbl
  -- the DA roots
  obtain ⟨dcl, hdlen, hn52, hDCA, hdd⟩ := H.da_list_digest _ _ _ _ hdl
  have h100 := loop_sound (rd := rd) (f := "__loop100")
    (ps := [σ (.n 52), σ (.n 59), σ (.n 10), σ (.n 11), σ (.n 12), σ (.n 19), σ (.n 30)])
    (m := dcl.length) (by unfold ordG; omega) hn52
    (fun x h => loop100_step H hMd' (by rw [p12]; exact hMd) x h)
    (by rw [h61, h60, h62] at hl100; exact hl100)
  -- the statement and its digest
  obtain ⟨seed', sig, da, cells, hcl, hseed', hsig0, hsig1, hda, hcells, hpi⟩ :=
    H.statement_digest _ _ _ _ _ _ _ _ hsd
  rw [p13, p14, hseed] at hseed'
  have hss : seed' = seed := (digestScalars_injective hseed').symm
  subst hss
  have hsg : sig = signersDigest (xmssClaims csx) (sphincsClaims css) := by
    apply digestScalars_injective
    rw [signersDigest, ← hsig, ← loadHolds_unique hsig0 l40, ← loadHolds_unique hsig1 l41]
  have hdg : da = daListDigest dcl := digestScalars_injective (hda.symm.trans hdd)
  subst hsg hdg
  let st : NodeStatement := ⟨⟨xmssClaims csx, sphincsClaims css, dcl⟩, deferOfCells cells⟩
  have hst : (σ (.n 65), σ (.n 66)) = digestScalars (statementDigest seed' st) := by
    rw [statementDigest_eq, cells_deferOfCells hcl]
    exact hpi
  -- the child's proof
  obtain ⟨pi, iv, fresh, π, hpi', hiv, hfs, hfr, hver⟩ := H.verify_sub _ _ _ _ _ _ _
    (by rw [p16, p6]; exact ht) hvs
  rw [hst] at hpi'
  rw [p13, p14, hseed] at hiv
  have hpe : pi = statementDigest seed' st := (digestScalars_injective hpi').symm
  have hie : iv = seed' := (digestScalars_injective hiv).symm
  subst hpe hie
  refine ⟨⟨st, fresh, π⟩, σ (.n 19), ?_, ?_, by simpa [st, hlx] using hnx,
    by simpa [st, hls] using hns, by simpa [st] using hdlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfs,
    ?_, hver⟩
  · rw [h18, p2, p0, hx, loadHolds_mul_gen_pow, Nat.add_zero] at l19
    exact l19
  · rw [h82, p2, p0, hx, loadHolds_mul_gen_pow, h81, h80, h30, hn20, hn21, hn52] at l81
    simp only [st, hlx, hls]
    simp only [mul_assoc, ← pow_add] at l81
    exact l81
  · intro j hj
    simp only [st, hlx] at hj
    obtain ⟨⟨L, hL, hLe, hoff⟩, hmk, hrd⟩ := hRx j hj
    rw [p5, hLx] at hLe
    have := gen_pow_inj' (by omega) (by omega) hLe
    subst this
    refine ⟨offx j, hoff, ?_, ?_⟩
    · rw [h31, one_mul, p4, loadHolds_mul_gen_pow, Nat.add_zero] at hmk
      exact hmk
    · rw [p3] at hrd
      simp only [st]
      rw [List.getElem?_eq_getElem (by rw [hlx]; exact hj), hgx j (by rw [hlx]; exact hj),
        entryX_of_reads hrd]
  · intro j hj
    simp only [st, hls] at hj
    obtain ⟨⟨L, hL, hLe, hoff⟩, hmk, hrd⟩ := hRs j hj
    rw [p8, hLs] at hLe
    have := gen_pow_inj' (by omega) (by omega) hLe
    subst this
    refine ⟨offs j, hoff, ?_, ?_⟩
    · rw [h34, p4, p5, hLx, hn20, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero, mul_assoc,
        ← pow_add] at hmk
      simp only [st, hlx]
      exact hmk
    · rw [p7] at hrd
      simp only [st]
      rw [List.getElem?_eq_getElem (by rw [hls]; exact hj), hgs j (by rw [hls]; exact hj),
        entryS_of_reads hrd]
  · intro j hj
    simp only [st] at hj
    obtain ⟨i, hi, hmk, r0, r1, r2, r3, hroot, hcda⟩ := h100 j hj
    refine ⟨i, hi, ?_, fun cl hcl' => ?_⟩
    · rw [p11, h30, hn20, hn21] at hmk
      simp only [mul_assoc, ← pow_add] at hmk
      simp only [st, hlx, hls]
      exact hmk
    · simp only [st] at hcl'
      rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hcl'
      subst hcl'
      have hD := daAt_of_claimsAt hDCA j hj
      rw [gen_pow_four] at hcda
      have := readsAt_unique hcda hD (by simp only [List.length_cons, List.length_nil])
      rw [p10, this] at hroot
      exact hroot
  · simp only [st]; exact (length_deferOfCells hcl).1
  · simp only [st]; exact (length_deferOfCells hcl).2
  · simp only [st]
    rw [cells_deferOfCells hcl]
    have e50 : σ (.n 50) = σ (.n 0) ^ 53 := by
      rw [h50, h49, h48, h47, h46, h45, h44, h43]; ring
    rw [h51, e50, p9, p0, hx, gen_pow_pow] at hcells
    exact hcells
  · rw [h68, h67, p15, p0, hx, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero,
      show c + c = 2 * c by ring, show σ (.n 65) = _ from congrArg Prod.fst hst] at l65
    exact l65
  · rw [h69, h67, p15, p0, hx, ← pow_add, loadHolds_mul_gen_pow,
      show c + c = 2 * c by ring, show σ (.n 66) = _ from congrArg Prod.snd hst] at l66
    exact l66
  · have e78 : σ (.n 78) = σ (.n 0) ^ 106 := by
      rw [h78, h77, h76, h75, h74, h73, h72, h71, h70]; ring
    rw [h79, e78, p17, p0, hx, gen_pow_pow] at hfr
    exact hfr

end
end LeanVM.Guest.B1.Main
