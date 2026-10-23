/-
  LeanVM.Guest.B1.Main.MainWords

  The words of an honest run of `main` placed at `fp`: its counts, the contents of its ten
  `HeapBuf`s, the digests its callees return, the children's iterations, and what each callee
  needs of them (`MainWordsOk`).
-/

module

public import LeanVM.Guest.B1.Main.ChildrenAt
public import LeanVM.Guest.B1.Main.TablesAt
public import LeanVM.Guest.B1.Main.MainWalk

/-!
# `main`'s words, placed

`MainWords`: the counts of `MainRun`, the contents of `main`'s `HeapBuf`s (the DA claims table,
the two signature claim tables, the signer pair, the coverage table, the children's public
inputs, fresh and carried claims, the running counts, `defer_stmt`), the digests and the
children's iterations. At `fp` the buffers lie from `fp + fs "main"` (`mainLb`), the exponent
tables' after them, where `exponent_tables`, `main`'s first callee, puts them (`mainLexp`);
`mainRunAt` is the `MainRun` with these pointers. `MainWordsOk`: the bounds, and for each callee
the words of its precondition on every memory holding `mainIn = mainLb ++ mainLexp`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef bufL Meaning_statement_digest Meaning_da_list_digest
  Meaning_verify_lean_xmss Meaning_verify_sig_lean_sphincs)

@[expose] public section

/-- **The words of an honest run of `main`.** -/
structure MainWords where
  /-- The counts, as `MainRun`'s. -/
  dx : ℕ
  ux : ℕ
  rx : ℕ
  ds : ℕ
  us : ℕ
  rs : ℕ
  nc : ℕ
  rd : ℕ
  da : ℕ
  ud : ℕ
  /-- The direct DA matrix's rows. -/
  drows : ℕ
  /-- The seed. -/
  seed : Digest
  /-- The `HeapBuf`s' contents: DA claims, leanXMSS and leanSPHINCS claims, coverage marks, the
  children's public inputs, fresh and carried claims, running counts, `defer_stmt`. -/
  daTab : List E
  xTab : List E
  sTab : List E
  cov : List E
  cpiTab : List E
  frTab : List E
  carTab : List E
  wTab : List E
  dTab : List E
  /-- The digests the callees return. -/
  daDig : Digest
  xDig : Digest
  sDig : Digest
  sigDig : Digest
  stDig : Digest
  /-- The direct DA claim's cells. -/
  dr : E × E × E × E
  /-- The leaf's deferred values. -/
  lbv : E
  lmA : E
  lmB : E
  /-- The children's iterations. -/
  child : ℕ → ChildWords
  /-- The raw signatures' slots. -/
  slX : ℕ → ℕ
  slS : ℕ → ℕ

namespace MainWords

variable (W : MainWords)

/-- The coverage table's size. -/
def total : ℕ := W.dx + W.ux + (W.ds + W.us) + (W.da + W.ud)

/-- The sizes of `main`'s `HeapBuf`s, in allocation order. -/
def sizes : List ℕ :=
  [4 * (W.da + W.ud), 4 * (W.dx + W.ux), 4 * (W.ds + W.us), 2, W.total, 2 * W.nc, 106 * W.nc,
    53 * W.nc, W.nc + 1, 53]

/-- Their contents. -/
def bufs : List (List E) :=
  [W.daTab, W.xTab, W.sTab, [(digestScalars W.sigDig).1, (digestScalars W.sigDig).2], W.cov,
    W.cpiTab, W.frTab, W.carTab, W.wTab, W.dTab]

end MainWords

variable (fs : String → ℕ)

/-- Buffer `i`'s first word at `fp`. -/
def mainBase (fp : ℕ) (W : MainWords) (i : ℕ) : ℕ := (bases (fp + fs "main") W.sizes).getD i 0

/-- `main`'s `HeapBuf`s at `fp`. -/
def mainLb (fp : ℕ) (W : MainWords) : Layout := bufL (fp + fs "main") W.sizes W.bufs

/-- The exponent tables' first word: `exponent_tables`' buffers, after its frame, the first callee
after `main`'s buffers. -/
def mainExpBase (fp : ℕ) (W : MainWords) : ℕ := fp + fs "main" + W.sizes.sum + fs "exponent_tables"

/-- The exponent tables at `fp`. -/
noncomputable def mainLexp (fp : ℕ) (W : MainWords) : Layout :=
  [(mainExpBase fs fp W, expTbl1), (mainExpBase fs fp W + 34, expTbl2)]

/-- The words `main`'s callees read. -/
noncomputable def mainIn (fp : ℕ) (W : MainWords) : Layout := mainLb fs fp W ++ mainLexp fs fp W

/-- A pointer to `main`'s buffer `i`. -/
def mainPtr (fp : ℕ) (W : MainWords) (i : ℕ) : E := ofK (gpow (mainBase fs fp W i))

/-- **`main`'s run at `fp`**, its pointers the allocator's. -/
noncomputable def mainRunAt (fp : ℕ) (W : MainWords) : MainRun :=
  ⟨W.dx, W.ux, W.rx, W.ds, W.us, W.rs, W.nc, W.rd, W.da, W.ud, W.seed,
    ofK (gpow (mainExpBase fs fp W)), ofK (gpow (mainExpBase fs fp W + 34)),
    mainPtr fs fp W 0, mainPtr fs fp W 1, mainPtr fs fp W 2, mainPtr fs fp W 3, mainPtr fs fp W 4,
    mainPtr fs fp W 5, mainPtr fs fp W 6, mainPtr fs fp W 7, mainPtr fs fp W 8, mainPtr fs fp W 9,
    W.daDig, W.xDig, W.sDig, W.sigDig, W.stDig, W.dr.1, W.dr.2.1, W.dr.2.2.1, W.dr.2.2.2, W.lbv,
    W.lmA, W.lmB⟩

/-- **What `main`'s callees need of its words at `fp`**, on every memory holding `mainIn` and
defined below `2^κ`, the children's runs of the deferring verifier in `VsGood`. -/
structure MainWordsOk (κ : ℕ) (VsGood : VerifySub.VsData → Prop) (fp : ℕ) (W : MainWords) :
    Prop where
  total : W.total ≤ 65535
  nc : W.nc ≤ 16
  rd1 : W.rd ≤ 1
  da : W.da ≤ 16
  ud : W.ud ≤ 257
  dau : W.da + W.ud ≤ 257
  rx : W.rx ≤ 65535
  rs : W.rs ≤ 65535
  decl : 0 < W.dx + W.ds + W.da
  lens : W.bufs.map List.length = W.sizes
  daList : ∃ claims : List DaClaim, claims.length = W.da ∧ ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    DaListPreAt claims rd [mainPtr fs fp W 0, gen ^ W.da]
      [(digestScalars W.daDig).1, (digestScalars W.daDig).2]
  xList : ∃ cs : List E, cs.length = 4 * W.dx ∧ ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    ClPreAt cs rd [mainPtr fs fp W 1, gen ^ W.dx, ofK (gpow (mainExpBase fs fp W + 34))]
      [(digestScalars W.xDig).1, (digestScalars W.xDig).2]
  sList : ∃ cs : List E, cs.length = 4 * W.ds ∧ ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    ClPreAt cs rd [mainPtr fs fp W 2, gen ^ W.ds, ofK (gpow (mainExpBase fs fp W + 34))]
      [(digestScalars W.sDig).1, (digestScalars W.sDig).2]
  sig : CompressCells ![(digestScalars W.xDig).1, (digestScalars W.xDig).2, (digestScalars W.sDig).1,
    (digestScalars W.sDig).2] ivCells.1 ivCells.2 (digestScalars W.sigDig).1
    (digestScalars W.sigDig).2 (metadataCell 64 true)
  xSlot : ∀ c < W.rx, W.slX c < W.dx + W.ux
  xMark : ∀ c < W.rx, CellL (mainIn fs fp W) (mainBase fs fp W 4 + W.slX c) (gen ^ c)
  xSig : ∀ c < W.rx, ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    Meaning_verify_lean_xmss rd [mainPtr fs fp W 1 * gen ^ (4 * W.slX c)] []
  sSlot : ∀ c < W.rs, W.slS c < W.ds + W.us
  sMark : ∀ c < W.rs, CellL (mainIn fs fp W) (mainBase fs fp W 4 + (W.dx + W.ux + W.slS c))
    (gen ^ W.rx * gen ^ c)
  sSig : ∀ c < W.rs, ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    Meaning_verify_sig_lean_sphincs rd [mainPtr fs fp W 2 * gen ^ (4 * W.slS c)] []
  daVerify : W.rd = 1 → ∃ (wt : Da.Witness) (root vd : Digest), wt.Opens root vd ∧ wt.rows.length = W.drows ∧
    ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) → DaVerifyPreAt root vd rd [ofK (gpow (mainExpBase fs fp W + 34))] [W.dr.1, W.dr.2.1, W.dr.2.2.1, W.dr.2.2.2]
  daCover : W.rd = 1 → ∃ i, ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    CoverPreAt i rd [mainPtr fs fp W 0, mainPtr fs fp W 4 * (gen ^ W.dx * gen ^ W.ux *
      (gen ^ W.ds * gen ^ W.us)), gen ^ W.da * gen ^ W.ud, gen ^ W.rx * gen ^ W.rs]
      [W.dr.1, W.dr.2.1, W.dr.2.2.1, W.dr.2.2.2]
  written0 : CellL (mainIn fs fp W) (mainBase fs fp W 8 + 0) (gen ^ W.rx * gen ^ W.rs * gen ^ W.rd)
  writtenN : CellL (mainIn fs fp W) (mainBase fs fp W 8 + W.nc)
    (gen ^ W.dx * gen ^ W.ux * (gen ^ W.ds * gen ^ W.us) * (gen ^ W.da * gen ^ W.ud))
  children : ∀ c < W.nc, ChildWordsOk κ VsGood (mainIn fs fp W) (mainBase fs fp W 8)
    (mainBase fs fp W 5) (mainPtr fs fp W 1) (mainPtr fs fp W 4) (gen ^ W.dx * gen ^ W.ux)
    (ofK (gpow (mainExpBase fs fp W + 34))) (mainPtr fs fp W 2) (gen ^ W.ds * gen ^ W.us)
    (mainPtr fs fp W 7) (mainPtr fs fp W 0)
    (mainPtr fs fp W 4 * (gen ^ W.dx * gen ^ W.ux * (gen ^ W.ds * gen ^ W.us)))
    (gen ^ W.da * gen ^ W.ud) (digestScalars W.seed).1 (digestScalars W.seed).2
    (ofK (gpow (mainExpBase fs fp W))) (mainPtr fs fp W 6) W.seed c (W.child c)
  leaf : W.nc = 0 → W.dTab = List.replicate 22 0 ++ [W.lbv] ++ List.replicate 28 0 ++ [W.lmA, W.lmB]
  agg : W.nc ≠ 0 → ∃ (cs : List ChildClaims) (h : BatchHints) (d : DeferredClaim),
    cs.length = W.nc ∧ batch cs h = some d ∧ h.bytecodeRounds.length = 22 ∧
    h.matrixRounds.length = 28 ∧ (∀ c ∈ cs, FreshShaped c.fresh ∧
      c.carried.bytecodePoint.length = 22 ∧ c.carried.matrixPoint.length = 28) ∧
    W.cpiTab = cs.flatMap (fun c => [(digestScalars c.publicInput).1, (digestScalars c.publicInput).2]) ∧
    W.frTab = cs.flatMap (fun c => fixedCells c.fresh) ∧ W.carTab = cs.flatMap (fun c => c.carried.cells) ∧
    W.dTab = d.cells
  stmt : ∃ sig cells, ∀ rd, LowDef κ rd → MemL rd (mainIn fs fp W) →
    SdPreAt sig cells rd [(digestScalars W.seed).1, (digestScalars W.seed).2,
      mainPtr fs fp W 3, (digestScalars W.daDig).1, (digestScalars W.daDig).2, mainPtr fs fp W 9]
      [(digestScalars W.stDig).1, (digestScalars W.stDig).2]

end
end LeanVM.Guest.B1.Main
