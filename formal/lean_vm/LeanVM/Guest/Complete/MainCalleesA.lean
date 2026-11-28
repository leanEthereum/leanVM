module

public import LeanVM.Guest.Complete.KidsA
public import LeanVM.Guest.Complete.LeafA
public import LeanVM.Guest.B1.Main.Body

/-!
# `main`'s callees, placed, at its honest valuation

`main`'s node is placed at the root (frame `0`, cursor `B2C.fs "main"`). Its `HeapBuf`s are, in
allocation order, the leanXMSS table (`4·sx` words, `sx` its declared and duplicate slots), the
leanSPHINCS table (`4·ss`), the coverage table (`sx + ss`), the byte table (`256`), `da_digests`
(`2(n + 1)`, `n` the children's count), `child_pi` (`2n`), `child_fresh` (`55n`), `child_carried`
(`26n`), `written` (`n + 1`) and `defer_stmt` (`26`), from the cursor one after another (`mBase`).
Its callees follow from their end (`mTop`): `exponent_tables` first, its tables at `mGS`, then the
others, each at a frame past the tables (`mLo`).

`mainWords`: the buffers' honest words (the coverage table's marks are the loops' choice, a
parameter). `MainPreA`: a memory holding them, the exponent tables, and the statement's digest at
the header. `mainR`: the buffers and the tables, the region every callee loads in.

`MainCalleesAt al k s w cover`: every callee of `main` not proved yet, at the arguments `main`'s
honest valuation gives, at every frame past the tables and every cursor past its block, ending within
`2^40` of its cursor below `2^60` (`AtEveryB`), its pops the honest pushes' share (`PopsPost`), every
node exact. `MainCalleesA al k`: on every node `MainCompleteA` covers, some coverage table of `sx + ss`
marks with them.
The target: `MainCalleesA al k → MainFromVsA al k` (`hotwire-port.md`, `b1c`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

noncomputable section

/-! ## The honest counts -/

/-- The leanXMSS region of the coverage plan. -/
def xPlan (s : NodeStatement) (w : NodeWitness) : Prover.CoverageRegion LeanXmssClaim :=
  Prover.coveragePlan s.claims.xmss (w.xmssSignatures.map (·.1)) (w.children.map (·.statement.claims.xmss))

/-- The leanSPHINCS region of the coverage plan. -/
def sPlan (s : NodeStatement) (w : NodeWitness) : Prover.CoverageRegion LeanSphincsClaim :=
  Prover.coveragePlan s.claims.sphincs (w.sphincsSignatures.map (·.1))
    (w.children.map (·.statement.claims.sphincs))

/-- A leanXMSS claim's cells. -/
def xCells (c : LeanXmssClaim) : List E := Prover.cellsOfBytes (claimBytes xmssPublicKeyBytes c)

/-- A leanSPHINCS claim's cells. -/
def sCells (c : LeanSphincsClaim) : List E := Prover.cellsOfBytes (claimBytes Sphincs.PublicKey.toBytes c)

/-- `main`'s counts, `meta`'s exponents. -/
structure MainCounts where
  nlx : ℕ
  nxd : ℕ
  nrx : ℕ
  nls : ℕ
  nsd : ℕ
  nrs : ℕ
  nc : ℕ
  nd : ℕ

/-- **The honest counts** (`honestPushes`' `meta`). -/
def mainCounts (s : NodeStatement) (w : NodeWitness) : MainCounts :=
  ⟨s.claims.xmss.length, (xPlan s w).duplicates.length, w.xmssSignatures.length, s.claims.sphincs.length,
    (sPlan s w).duplicates.length, w.sphincsSignatures.length, w.children.length,
    (w.daMatrix.map fun _ => 1).getD 0⟩

namespace MainCounts

/-- The leanXMSS slots. -/
abbrev sx (m : MainCounts) : ℕ := m.nlx + m.nxd

/-- The leanSPHINCS slots. -/
abbrev ss (m : MainCounts) : ℕ := m.nls + m.nsd

/-- `main`'s `HeapBuf` sizes, in allocation order. -/
def bufs (m : MainCounts) : List ℕ :=
  [4 * m.sx, 4 * m.ss, m.sx + m.ss, 256, 2 * (m.nc + 1), 2 * m.nc, 55 * m.nc, 26 * m.nc, m.nc + 1, 26]

end MainCounts

/-! ## The layout -/

/-- The base of `main`'s `j`-th `HeapBuf`: `0` the leanXMSS table, `1` the leanSPHINCS table, `2`
the coverage table, `3` the byte table, `4` `da_digests`, `5` `child_pi`, `6` `child_fresh`, `7`
`child_carried`, `8` `written`, `9` `defer_stmt`. -/
def mBase (m : MainCounts) (j : ℕ) : ℕ := (bases (B2C.fs "main") m.bufs).getD j 0

/-- The end of `main`'s `HeapBuf`s, where its callees start. -/
def mTop (m : MainCounts) : ℕ := B2C.fs "main" + m.bufs.sum

/-- The exponent tables' index: `exponent_tables`' cursor, after its frame. -/
def mGS (al : String → Bool) (m : MainCounts) : ℕ :=
  allocBase (al "exponent_tables") (mTop m) + B2C.fs "exponent_tables"

/-- Past the exponent tables: where the later callees' frames lie. -/
def mLo (al : String → Bool) (m : MainCounts) : ℕ := mGS al m + expTabLen

/-- **The region `main`'s callees load in**: its `HeapBuf`s and the exponent tables. -/
def mainR (al : String → Bool) (m : MainCounts) (i : ℕ) : Prop :=
  (B2C.fs "main" ≤ i ∧ i < mTop m) ∨ (mGS al m ≤ i ∧ i < mGS al m + expTabLen)

/-! ## The honest words -/

/-- The write count before child `c`: the raw signatures and the earlier children's claims. -/
def kidBase (w : NodeWitness) (c : ℕ) : ℕ :=
  w.xmssSignatures.length + w.sphincsSignatures.length +
    ((w.children.take c).map fun ch => ch.statement.claims.xmss.length + ch.statement.claims.sphincs.length).sum

/-- The own DA digest's cells: the checked claim's digest, or zeros. -/
def ownDaCells (w : NodeWitness) : List E :=
  match w.daMatrix with
  | some (c, _) => Prover.digestCells (daClaimDigest c)
  | none => [0, 0]

/-- **`main`'s words**: each `HeapBuf`'s honest contents from its base, the coverage table's marks
`cover`. -/
def mainWords (s : NodeStatement) (w : NodeWitness) (cover : List E) : Words :=
  let m := mainCounts s w
  [(mBase m 0, (s.claims.xmss ++ (xPlan s w).duplicates).flatMap xCells),
    (mBase m 1, (s.claims.sphincs ++ (sPlan s w).duplicates).flatMap sCells),
    (mBase m 2, cover),
    (mBase m 3, (List.range 256).map fun v => word v 0),
    (mBase m 4, w.children.flatMap (fun ch => Prover.digestCells ch.statement.claims.daDigest) ++ ownDaCells w),
    (mBase m 5, w.children.flatMap fun ch => Prover.digestCells (statementDigest guestSeed ch.statement)),
    (mBase m 6, w.children.flatMap (·.freshClaim.cells)),
    (mBase m 7, w.children.flatMap (·.statement.deferredClaim.cells)),
    (mBase m 8, (List.range (m.nc + 1)).map fun c => gen ^ kidBase w c),
    (mBase m 9, s.deferredClaim.cells)]

/-- **What `main`'s callees may assume of the memory**: `main`'s words, the exponent tables at
`mGS`, the statement's digest at the header. -/
def MainPreA (al : String → Bool) (s : NodeStatement) (w : NodeWitness) (cover : List E) (rd : Reader) : Prop :=
  HoldsWords rd (mainWords s w cover) ∧ ExpTables rd (ptrAt (mGS al (mainCounts s w))) ∧
    ExpWinTab rd (ptrAt (mGS al (mainCounts s w))) ∧
    ReadsAt rd 1 (Prover.digestCells (statementDigest guestSeed s))

/-- A callee's tree pops `P` stream by stream, every node exact. -/
def PopsPost (P : List Pop) (rd : Reader) (t : Tree) : Prop :=
  SameStreams (t.pops coreProgram rd) P ∧ t.Every (ExactAt coreProgram rd)

/-- **A callee completes placed at every position past `lo`**: at every frame `fp ≥ lo` and every
cursor past its block `B`, claiming no data and giving its caller nothing. -/
def AtEvery (al : String → Bool) (k : ℕ) (f : String) (args rets : List E) (R : ℕ → Prop)
    (Pre : Reader → Prop) (Post : Reader → Tree → Prop) (B lo : ℕ) : Prop :=
  ∀ fp cur, lo ≤ fp → fp + B ≤ cur → ∃ e,
    CallAtA B2C.fs al B2C.cert k f args rets R (fun _ => False) (fun _ => True) Pre Post B fp cur e

/-- **`AtEvery`, its end within `β` of its cursor below `T`.** A `CallAtA` alone does not bound its end:
own words `2^64 - 1` apart share an address, so a `CallAtA` whose words no memory holds is true at any
end (`callAtA_wrap`). Below `T` the end is within `β` of the cursor, so the words lie below `T + β` and,
for `T + β < 2^64 - 1`, some memory holds them; a caller's cursor then stays bounded too. -/
def AtEveryB (al : String → Bool) (k : ℕ) (f : String) (args rets : List E) (R : ℕ → Prop)
    (Pre : Reader → Prop) (Post : Reader → Tree → Prop) (B lo T β : ℕ) : Prop :=
  ∀ fp cur, lo ≤ fp → fp + B ≤ cur → ∃ e, (cur < T → e ≤ cur + β) ∧
    CallAtA B2C.fs al B2C.cert k f args rets R (fun _ => False) (fun _ => True) Pre Post B fp cur e

theorem AtEveryB.toAtEvery {al : String → Bool} {k : ℕ} {f : String} {args rets : List E} {R : ℕ → Prop}
    {Pre : Reader → Prop} {Post : Reader → Tree → Prop} {B lo T β : ℕ}
    (h : AtEveryB al k f args rets R Pre Post B lo T β) : AtEvery al k f args rets R Pre Post B lo :=
  fun fp cur h1 h2 => let ⟨e, _, he⟩ := h fp cur h1 h2; ⟨e, he⟩

theorem AtEveryB.mono {al : String → Bool} {k : ℕ} {f : String} {args rets : List E} {R : ℕ → Prop}
    {Pre : Reader → Prop} {Post : Reader → Tree → Prop} {B lo T β T' β' : ℕ}
    (h : AtEveryB al k f args rets R Pre Post B lo T β) (hT : T' ≤ T) (hβ : β ≤ β') :
    AtEveryB al k f args rets R Pre Post B lo T' β' :=
  fun fp cur h1 h2 => let ⟨e, hb, he⟩ := h fp cur h1 h2; ⟨e, fun hc => (hb (by omega)).trans (by omega), he⟩

/-- **A callee ending at its cursor**, at every position past `lo`, is `AtEveryB` at every `T`, `β`. -/
theorem atEveryB_of_le {al : String → Bool} {k : ℕ} {f : String} {args rets : List E} {R : ℕ → Prop}
    {Pre : Reader → Prop} {Post : Reader → Tree → Prop} {B lo T β : ℕ}
    (h : ∀ fp cur, lo ≤ fp → fp + B ≤ cur → ∃ e, e ≤ cur ∧
      CallAtA B2C.fs al B2C.cert k f args rets R (fun _ => False) (fun _ => True) Pre Post B fp cur e) :
    AtEveryB al k f args rets R Pre Post B lo T β :=
  fun fp cur h1 h2 => let ⟨e, hb, he⟩ := h fp cur h1 h2; ⟨e, fun _ => hb.trans (Nat.le_add_right _ _), he⟩

/-- A loop helper's block over its `m` iterations and its skipped tail. -/
def loopBlock (L : String) (m : ℕ) : ℕ := m * B2C.fs L + B2C.fs (tailKey L)

/-- The pointer to `main`'s `j`-th `HeapBuf`, offset by `o`. -/
abbrev mPtr (m : MainCounts) (j o : ℕ) : E := ptrAt (mBase m j + o)

/-- **`main`'s callees not proved yet**, at the node `(s, w)` with the coverage marks `cover`, each
at the arguments and returns `main`'s honest valuation gives them, at every frame past the exponent
tables, loading in `main`'s buffers and the tables, on memories with `MainPreA`, its pops its share
of `honestPushes`, every node exact, ending within `2^40` of its cursor below `2^60`. The loops'
fields hold when their guard is taken. -/
structure MainCalleesAt (al : String → Bool) (k : ℕ) (s : NodeStatement) (w : NodeWitness) (cover : List E) :
    Prop where
  /-- `claim_list_digest(lx_table, n_lx)`. -/
  clx : AtEveryB al k "claim_list_digest" [mPtr (mainCounts s w) 0 0, gen ^ (mainCounts s w).nlx]
    (Prover.digestCells (claimListDigest xmssPublicKeyBytes s.claims.xmss)) (mainR al (mainCounts s w))
    (MainPreA al s w cover) (PopsPost (Prover.listPushes "claims" (s.claims.xmss.map xCells)))
    (B2C.fs "claim_list_digest") (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  /-- `claim_list_digest(lean_sphincs_table, n_lean_sphincs)`. -/
  csp : AtEveryB al k "claim_list_digest" [mPtr (mainCounts s w) 1 0, gen ^ (mainCounts s w).nls]
    (Prover.digestCells (claimListDigest Sphincs.PublicKey.toBytes s.claims.sphincs))
    (mainR al (mainCounts s w)) (MainPreA al s w cover)
    (PopsPost (Prover.listPushes "claims" (s.claims.sphincs.map sCells)))
    (B2C.fs "claim_list_digest") (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  /-- The leanXMSS duplicates' loop (`__loop0_main`). -/
  dupx : (mainCounts s w).nxd ≠ 0 → AtEveryB al k "__loop0_main"
    [1, gen ^ (mainCounts s w).nxd, mPtr (mainCounts s w) 0 0, gen ^ (mainCounts s w).nlx] []
    (mainR al (mainCounts s w)) (MainPreA al s w cover)
    (PopsPost ((xPlan s w).duplicates.map fun c => ("dup_claims", xCells c)))
    (loopBlock "__loop0_main" (mainCounts s w).nxd) (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  /-- The leanSPHINCS duplicates' loop (`__loop1_main`). -/
  dups : (mainCounts s w).nsd ≠ 0 → AtEveryB al k "__loop1_main"
    [1, gen ^ (mainCounts s w).nsd, mPtr (mainCounts s w) 1 0, gen ^ (mainCounts s w).nls] []
    (mainR al (mainCounts s w)) (MainPreA al s w cover)
    (PopsPost ((sPlan s w).duplicates.map fun c => ("dup_claims", sCells c)))
    (loopBlock "__loop1_main" (mainCounts s w).nsd) (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  /-- The raw leanXMSS signatures' loop (`__loop2_main`), the carried chain indices `lx_tags` last. -/
  rawx : (mainCounts s w).nrx ≠ 0 → AtEveryB al k "__loop2_main"
    ([1, gen ^ (mainCounts s w).nrx, gen ^ (mainCounts s w).sx, mPtr (mainCounts s w) 2 0,
      mPtr (mainCounts s w) 0 0] ++ Main.lxTagWords) []
    (mainR al (mainCounts s w)) (MainPreA al s w cover)
    (PopsPost ((w.xmssSignatures.zip (xPlan s w).directSlots).flatMap fun cs =>
      ("raw_index", [Prover.count cs.2]) :: Prover.xmssHints cs.1.1.1 cs.1.1.2 cs.1.2))
    (loopBlock "__loop2_main" (mainCounts s w).nrx) (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  /-- The raw leanSPHINCS signatures' loop (`__loop3_main`). -/
  raws : (mainCounts s w).nrs ≠ 0 → AtEveryB al k "__loop3_main"
    [1, gen ^ (mainCounts s w).nrs, gen ^ (mainCounts s w).ss, mPtr (mainCounts s w) 2 (mainCounts s w).sx,
      gen ^ (mainCounts s w).nrx, mPtr (mainCounts s w) 1 0, mPtr (mainCounts s w) 3 0] []
    (mainR al (mainCounts s w)) (MainPreA al s w cover)
    (PopsPost ((w.sphincsSignatures.zip (sPlan s w).directSlots).flatMap fun cs =>
      ("sp_raw_index", [Prover.count cs.2]) :: Prover.sphincsHints cs.1.1.1 cs.1.1.2 cs.1.2))
    (loopBlock "__loop3_main" (mainCounts s w).nrs) (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  /-- `da_verify(byte_bits)`, on the node's blob matrix: the root's halves and the challenge. -/
  da : ∀ c mw, w.daMatrix = some (c, mw) → AtEveryB al k "da_verify" [mPtr (mainCounts s w) 3 0]
    (Prover.digestCells c.daRoot ++ [c.membershipChallenge]) (mainR al (mainCounts s w))
    (MainPreA al s w cover) (PopsPost (Prover.daHints c mw)) (B2C.fs "da_verify") (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  /-- Child `c`'s leanXMSS list (`child_claim_list_digest` over `lx_table` and its coverage). -/
  kidx : ∀ c (hc : c < w.children.length), AtEveryB al k "child_claim_list_digest"
    [mPtr (mainCounts s w) 0 0, mPtr (mainCounts s w) 2 0, gen ^ kidBase w c, gen ^ (mainCounts s w).sx,
      gen ^ w.children[c].statement.claims.xmss.length]
    (Prover.digestCells (claimListDigest xmssPublicKeyBytes w.children[c].statement.claims.xmss))
    (mainR al (mainCounts s w)) (MainPreA al s w cover)
    (PopsPost (Prover.childSlotPushes ((xPlan s w).childSlots.getD c [])))
    (B2C.fs "child_claim_list_digest") (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  /-- Child `c`'s leanSPHINCS list. -/
  kids : ∀ c (hc : c < w.children.length), AtEveryB al k "child_claim_list_digest"
    [mPtr (mainCounts s w) 1 0, mPtr (mainCounts s w) 2 (mainCounts s w).sx,
      gen ^ kidBase w c * gen ^ w.children[c].statement.claims.xmss.length, gen ^ (mainCounts s w).ss,
      gen ^ w.children[c].statement.claims.sphincs.length]
    (Prover.digestCells (claimListDigest Sphincs.PublicKey.toBytes w.children[c].statement.claims.sphincs))
    (mainR al (mainCounts s w)) (MainPreA al s w cover)
    (PopsPost (Prover.childSlotPushes ((sPlan s w).childSlots.getD c [])))
    (B2C.fs "child_claim_list_digest") (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)
  /-- `aggregate_claims(n_children, child_pi, child_fresh, child_carried, defer_stmt, tables)` on
  an inner node. -/
  agg : w.children ≠ [] → AtEveryB al k "aggregate_claims"
    [gen ^ (mainCounts s w).nc, mPtr (mainCounts s w) 5 0, mPtr (mainCounts s w) 6 0, mPtr (mainCounts s w) 7 0,
      mPtr (mainCounts s w) 9 0, ptrAt (mGS al (mainCounts s w) + winTabAt)] []
    (mainR al (mainCounts s w)) (MainPreA al s w cover) (PopsPost (Prover.batchPushes w.batchingHints))
    (B2C.fs "aggregate_claims") (mLo al (mainCounts s w))
    (2 ^ 60) (2 ^ 40)

/-- **`main`'s callees not proved yet, on every node**: some coverage table of `sx + ss` marks with
`MainCalleesAt`. -/
structure MainCalleesA (al : String → Bool) (k : ℕ) : Prop where
  callees : ∀ (s : NodeStatement) (w : NodeWitness), NodeRelation guestBytecode guestSeed s w →
    DeployedLimits s w → ChildrenOk guestBytecode guestSeed w → ∃ cover : List E,
      cover.length = (mainCounts s w).sx + (mainCounts s w).ss ∧ MainCalleesAt al k s w cover

end
end
end LeanVM.Guest.Complete
