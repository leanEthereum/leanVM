/-
  LeanVM.Guest.B1.Main.Callees

  What `main` assumes of the functions it calls that other groups prove (TRIAGE #44, #52, #57,
  #58, #62, #65, #66, #73, #75): each one's relation implies its meaning, in Spec terms.
-/

module

public import LeanVM.Guest.B1.Main.Basic

/-!
# The callees of `main`

`main` calls the signature verifiers (group 2), the digests, claim lists and LeanDA (group 3),
and `verify_sub` (group 6). `Callees bytecode rd` collects the soundness half of each one's B1
lemma, `coreProgram.Rel rd f args rets → Meaning_f`, on the memory `rd`, as the hypothesis
`main`'s theorem takes; each field is shaped as the owning group's lemma states it or implies it
(group 3's `Meaning_*` with their scratch tables dropped):

* `verify_lean_xmss(p)`, `verify_sig_lean_sphincs(p)`: some signature verifies, with BLAKE2s
  (`xmssVerify`, `sphincsVerify`), for the claim of the four cells at `p` (`xmssOf`, `sphincsOf`);
* `statement_digest`: the digest of the statement whose seed, signer-set digest (read at
  `signers_hash`), DA list digest and 53 deferred cells (read at `defer`) are its arguments
  (`stmtDigestOf`);
* `claim_list_digest(p, g^n, g_squares)`: `n < 2^16`, and the BLAKE2s of the `4n` cells at `p`;
* `child_claim_list_digest`: the same of `n` claims read at hinted table indices, each marking its
  coverage slot (`ChildReads`);
* `da_list_digest(roots, g^n)`: the list digest of `n ≤ 16` DA claims at `roots`;
* `cover_da_root`: the mark in slot `i` of the coverage table and the claim of DA slot `i`;
* `da_verify(g_squares)`: a blob matrix opens to the returned root and vector digest;
* `verify_sub`: the deferring verifier accepts some proof for the child's public input under the
  IV `seed`, with fixed claims of the guest's shape written at `defer_out`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## Spec vocabulary -/

/-- `statementDigest` on its parts: the seed, the signer-set digest, the DA list digest and the
deferred cells. -/
def stmtDigestOf (seed sig da : Digest) (defer : List E) : Digest :=
  let cells := defer ++ if defer.length % 2 = 1 then [0] else []
  let bytes := digestBytes seed ++ digestBytes sig ++ digestBytes da ++ cells.flatMap eBytes
  blake2sBytes (bytes ++ List.replicate ((64 - bytes.length % 64) % 64) 0)

theorem statementDigest_eq (seed : Digest) (s : NodeStatement) :
    statementDigest seed s = stmtDigestOf seed (signersDigest s.claims.xmss s.claims.sphincs)
      (daListDigest s.claims.da) s.defer.cells := rfl

/-- The table `g^(2^j)`, `j < 34`, at `q` (`exponent_tables`' second). -/
def SquaresTable (rd : Reader) (q : E) : Prop := ∀ j < sizeBits, LoadHolds rd q j (gen ^ 2 ^ j)

theorem squaresTable_of_expTables {rd : Reader} {p q : E} (h : ExpTables rd p q) :
    SquaresTable rd q := fun j hj => (h j hj).2

/-- A leanXMSS signature verifies, with BLAKE2s, for the claim of the four cells at `p`. -/
def XmssSigned (rd : Reader) (p : E) : Prop :=
  ∃ a b c d, ReadsAt rd p [a, b, c, d] ∧ ∃ σ, xmssVerify (xmssOf a b c d).1 (xmssOf a b c d).2 σ = true

/-- A leanSPHINCS signature verifies, with BLAKE2s, for the claim of the four cells at `p`. -/
def SphincsSigned (rd : Reader) (p : E) : Prop :=
  ∃ a b c d, ReadsAt rd p [a, b, c, d] ∧
    ∃ σ, sphincsVerify (sphincsOf a b c d).1 (sphincsOf a b c d).2 σ = true

/-- The DA claims at `p`, four cells a claim: the root's two cells, the vector digest's two. -/
def DaClaimsAt (rd : Reader) (p : E) (claims : List DaClaim) : Prop :=
  ∀ i (h : i < claims.length), LoadHolds rd p (4 * i) (digestScalars claims[i].1).1 ∧
    LoadHolds rd p (4 * i + 1) (digestScalars claims[i].1).2 ∧
    LoadHolds rd p (4 * i + 2) (digestScalars claims[i].2).1 ∧
    LoadHolds rd p (4 * i + 3) (digestScalars claims[i].2).2

/-- **What a child's claim blocks read and mark**: block `j < k` takes its claim at the table
index `off j`, below `log limit`: the coverage slot `cover·(origin·g^(off j))` holds `marks·g^j`
and the table entry `entries·g^(4·off j)` holds the block's four cells. -/
def ChildReads (rd : Reader) (entries cover marks origin limit : E) (off : ℕ → ℕ) (cs : List E)
    (k : ℕ) : Prop :=
  ∀ j < k, (∃ L ≤ 2 ^ 33, limit = gen ^ L ∧ off j < L) ∧
    LoadHolds rd (cover * (origin * gen ^ off j)) 0 (marks * gen ^ j) ∧
    ReadsAt rd (entries * gen ^ (4 * off j))
      [cs.getD (4 * j) 0, cs.getD (4 * j + 1) 0, cs.getD (4 * j + 2) 0, cs.getD (4 * j + 3) 0]

/-- The shape of the fixed claims a child's proof makes, as `verify_sub` exports them
(`DEFER_SIZE = 106` cells). -/
def FreshShaped (c : FixedClaims) : Prop :=
  c.bytecodePoint.length = 22 ∧ c.rowPoint.length = 8 ∧ c.columnPoint.length = 8 ∧
    c.slices.length = 64

/-! ## The hypotheses -/

/-- **The callees of `main`, soundly**: for each function another group proves, its relation on
the memory `rd` implies its meaning; `verify_sub` for the guest `bytecode`. -/
structure Callees (bytecode : List K) (rd : Reader) : Prop where
  verify_lean_xmss : ∀ p, coreProgram.Rel rd "verify_lean_xmss" [p] [] → XmssSigned rd p
  verify_sig_lean_sphincs :
    ∀ p, coreProgram.Rel rd "verify_sig_lean_sphincs" [p] [] → SphincsSigned rd p
  statement_digest : ∀ seed0 seed1 sigp da0 da1 dp d0 d1,
    coreProgram.Rel rd "statement_digest" [seed0, seed1, sigp, da0, da1, dp] [d0, d1] →
      ∃ (seed sig da : Digest) (cells : List E), cells.length = 53 ∧
        (seed0, seed1) = digestScalars seed ∧ LoadHolds rd sigp 0 (digestScalars sig).1 ∧
        LoadHolds rd sigp 1 (digestScalars sig).2 ∧ (da0, da1) = digestScalars da ∧
        ReadsAt rd dp cells ∧ (d0, d1) = digestScalars (stmtDigestOf seed sig da cells)
  claim_list_digest : ∀ p n_g gsq d0 d1, SquaresTable rd gsq →
    coreProgram.Rel rd "claim_list_digest" [p, n_g, gsq] [d0, d1] →
      ∃ n < 2 ^ 16, n_g = gen ^ n ∧ ∃ cs : List E, cs.length = 4 * n ∧ ReadsAt rd p cs ∧
        (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes))
  child_claim_list_digest : ∀ entries cover base origin limit n_g gsq d0 d1, SquaresTable rd gsq →
    coreProgram.Rel rd "child_claim_list_digest" [entries, cover, base, origin, limit, n_g, gsq]
      [d0, d1] →
      ∃ n < 2 ^ 16, n_g = gen ^ n ∧ ∃ (off : ℕ → ℕ) (cs : List E), cs.length = 4 * n ∧
        ChildReads rd entries cover base origin limit off cs n ∧
        (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes))
  da_list_digest : ∀ roots n_g d0 d1,
    coreProgram.Rel rd "da_list_digest" [roots, n_g] [d0, d1] →
      ∃ claims : List DaClaim, claims.length ≤ 16 ∧ n_g = gen ^ claims.length ∧
        DaClaimsAt rd roots claims ∧ (d0, d1) = digestScalars (daListDigest claims)
  cover_da_root : ∀ roots cover nslots mark r0 r1 r2 r3,
    coreProgram.Rel rd "cover_da_root" [roots, cover, nslots, mark] [r0, r1, r2, r3] →
      ∃ i M, M < 2 ^ 33 ∧ i < M ∧ nslots = gen ^ M ∧ LoadHolds rd (cover * gen ^ i) 0 mark ∧
        ReadsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3]
  da_verify : ∀ gsq r0 r1 v0 v1, SquaresTable rd gsq →
    coreProgram.Rel rd "da_verify" [gsq] [r0, r1, v0, v1] →
      ∃ (root vd : Digest) (w : Da.Witness), (r0, r1) = digestScalars root ∧
        (v0, v1) = digestScalars vd ∧ w.Opens root vd
  verify_sub : ∀ pi0 pi1 s0 s1 glp gsq out, ExpTables rd glp gsq →
    coreProgram.Rel rd "verify_sub" [pi0, pi1, s0, s1, glp, gsq, out] [] →
      ∃ (pi iv : Digest) (fresh : FixedClaims) (π : Proof), (pi0, pi1) = digestScalars pi ∧
        (s0, s1) = digestScalars iv ∧ FreshShaped fresh ∧ ReadsAt rd out (fixedCells fresh) ∧
        verifyDeferred bytecode iv pi fresh π = true

end
end LeanVM.Guest.B1.Main

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## Memory cells and table entries -/

/-- The word at `p·g^k`, zero where there is none. -/
def cellAt (rd : Reader) (p : E) (k : ℕ) : E := (rd (p.limb 0 * Parameters.gpow k)).getD 0

theorem cellAt_of_load {rd : Reader} {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) :
    cellAt rd p k = v := by
  rw [cellAt, h.2]; rfl

theorem readsAt_four {rd : Reader} {p a b c d : E} :
    ReadsAt rd p [a, b, c, d] ↔
      LoadHolds rd p 0 a ∧ LoadHolds rd p 1 b ∧ LoadHolds rd p 2 c ∧ LoadHolds rd p 3 d := by
  constructor
  · intro h
    exact ⟨h 0 (by simp), h 1 (by simp), h 2 (by simp), h 3 (by simp)⟩
  · rintro ⟨h0, h1, h2, h3⟩ k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    exacts [h0, h1, h2, h3]

theorem readsAt_mul_gen_pow {rd : Reader} {p : E} {j : ℕ} {xs : List E} :
    ReadsAt rd (p * gen ^ j) xs ↔ ∀ k (hk : k < xs.length), LoadHolds rd p (j + k) xs[k] := by
  simp only [ReadsAt, loadHolds_mul_gen_pow]

theorem readsAt_unique {rd : Reader} {p : E} {xs ys : List E} (hx : ReadsAt rd p xs)
    (hy : ReadsAt rd p ys) (hl : xs.length = ys.length) : xs = ys :=
  List.ext_getElem hl fun k h1 h2 => loadHolds_unique (hx k h1) (hy k h2)

/-- The leanXMSS claim of table entry `s` at `T`: the four cells from `T·g^(4s)`. -/
def entryX (rd : Reader) (T : E) (s : ℕ) : XmssClaim :=
  xmssOf (cellAt rd T (4 * s)) (cellAt rd T (4 * s + 1)) (cellAt rd T (4 * s + 2))
    (cellAt rd T (4 * s + 3))

/-- The leanSPHINCS claim of table entry `s` at `T`. -/
def entryS (rd : Reader) (T : E) (s : ℕ) : SphincsClaim :=
  sphincsOf (cellAt rd T (4 * s)) (cellAt rd T (4 * s + 1)) (cellAt rd T (4 * s + 2))
    (cellAt rd T (4 * s + 3))

theorem cells_of_reads {rd : Reader} {T a b c d : E} {s : ℕ}
    (h : ReadsAt rd (T * gen ^ (4 * s)) [a, b, c, d]) :
    cellAt rd T (4 * s) = a ∧ cellAt rd T (4 * s + 1) = b ∧ cellAt rd T (4 * s + 2) = c ∧
      cellAt rd T (4 * s + 3) = d := by
  rw [readsAt_four] at h
  simp only [loadHolds_mul_gen_pow] at h
  exact ⟨cellAt_of_load h.1, cellAt_of_load h.2.1, cellAt_of_load h.2.2.1,
    cellAt_of_load h.2.2.2⟩

theorem entryX_of_reads {rd : Reader} {T a b c d : E} {s : ℕ}
    (h : ReadsAt rd (T * gen ^ (4 * s)) [a, b, c, d]) : entryX rd T s = xmssOf a b c d := by
  obtain ⟨h0, h1, h2, h3⟩ := cells_of_reads h
  rw [entryX, h0, h1, h2, h3]

theorem entryS_of_reads {rd : Reader} {T a b c d : E} {s : ℕ}
    (h : ReadsAt rd (T * gen ^ (4 * s)) [a, b, c, d]) : entryS rd T s = sphincsOf a b c d := by
  obtain ⟨h0, h1, h2, h3⟩ := cells_of_reads h
  rw [entryS, h0, h1, h2, h3]

/-- The DA claim `c` is DA slot `i`'s at `p`: its four cells from `p·g^(4i)`. -/
def DaAt (rd : Reader) (p : E) (i : ℕ) (c : DaClaim) : Prop :=
  ReadsAt rd (p * gen ^ (4 * i)) [(digestScalars c.1).1, (digestScalars c.1).2,
    (digestScalars c.2).1, (digestScalars c.2).2]

theorem daAt_unique {rd : Reader} {p : E} {i : ℕ} {c c' : DaClaim} (h : DaAt rd p i c)
    (h' : DaAt rd p i c') : c = c' := by
  unfold DaAt at h h'
  have := readsAt_unique h h' (by simp only [List.length_cons, List.length_nil])
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨h0, h1, h2, h3⟩ := this
  exact Prod.ext (digestScalars_injective (Prod.ext h0 h1))
    (digestScalars_injective (Prod.ext h2 h3))

theorem daAt_of_claimsAt {rd : Reader} {p : E} {claims : List DaClaim} (h : DaClaimsAt rd p claims)
    (i : ℕ) (hi : i < claims.length) : DaAt rd p i claims[i] := by
  obtain ⟨h0, h1, h2, h3⟩ := h i hi
  rw [DaAt, readsAt_four]
  simp only [loadHolds_mul_gen_pow, Nat.add_zero]
  exact ⟨h0, h1, h2, h3⟩

/-- **The signer set's block**: one compression of two digests' cells under the IV, the final
64-byte block, is the BLAKE2s of their bytes. -/
theorem signers_compress {a b : Digest} {o0 o1 : E}
    (hc : CompressCells ![(digestScalars a).1, (digestScalars a).2, (digestScalars b).1,
      (digestScalars b).2] ivCells.1 ivCells.2 o0 o1 (metadataCell 64 true)) :
    (o0, o1) = digestScalars (blake2sBytes (digestBytes a ++ digestBytes b)) := by
  rw [blake2s_default hc, digestBytes_eq, digestBytes_eq]
  simp [blockBytes, List.append_assoc]

end
end LeanVM.Guest.B1.Main
