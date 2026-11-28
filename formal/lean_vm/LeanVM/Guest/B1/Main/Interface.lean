/-
  LeanVM.Guest.B1.Main.Interface

  The interface of B1 for `main` and `aggregate_claims`: what the batching of the children
  computes, what `main` asks of its callees, the decoders of the seed, the statement and the
  witness, and the statement that `main`'s run establishes `NodeRelation` of what they decode.
-/

module

public import LeanVM.Guest.B1.Da.Interface
public import LeanVM.Guest.B1.Sig.InterfaceP
public import LeanVM.Guest.Batch.Def
import LeanVM.Guest.B1.Bits.Meaning
import LeanVM.Guest.B1.Sig.Interface
import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main»
import LeanVM.Guest.Data.ValNames.«main_loop2»

/-!
# `main` and `aggregate_claims`: meanings (TRIAGE G #96, #97)

**`aggregate_claims`**: from the batching seed (`AGG_SEED_*`), the duplex sponge
absorbs the children's count and every child's words, checks the proof of work on the hinted
nonce, squeezes the challenge `λ` and the `SPLIT_LOG` column challenges, which fold each fresh
claim's values, and one sumcheck (`batch_sumcheck`) reduces the children's claims on the split
program to the claim written at `defer_stmt`: `Node.batch` of the children whose
words the memory holds (`ChildWordsAt`) returns that claim, for the hints `bc_sumcheck_msgs` (the
nonce first) and `bc_star_hint` (`Aggregate.lean`'s `MeaningAggregateClaimsW`), given the grind's window tables at
its last argument (`WinTabs`).

**`main`**. Its callees with a witness, each through a witness function of
the call's words (`CalleesWC`, `LoopsC.lean`): a leanXMSS signature `wX args` for the raw iteration of
`main_loop2` at `args` (the leanXMSS check is inline there at 40f877dc: `Loop2Out`, its segment read
as `Sig.XmssOut` at its signer), a leanSPHINCS signature `wS p` (`verify_sig_lean_sphincs`,
`Sig.SphincsOut`, with the byte table), a matrix `wD args rets` (`da_verify`, `Da.MatrixWitness.Opens`),
a child's proof `wV args` (`verify_sub`: `verifyDeferred` of the child's public input under the
seed, its fresh claim at the call's pointer, `VerifySubOut`), and the batching's hints
`wA args` (`aggregate_claims`). The function's other callees are the deterministic functions
whose `…_Spec`s are stated in `Digest/Interface`, `Da/Interface`, `Bits/Meaning` (B1-a's
`exponent_tables`) and here.

**The decoders** read `main`'s valuation and the memory:
* `decSeed σ`: the seed `fs_seed`;
* `decStmt σ rd`: the claims of the declared prefixes of the leanXMSS and leanSPHINCS tables
  (`Sig.xmssClaimOf`, `Sig.sphincsClaimOf`), the DA digest at the slot `da_pick` of `da_digests`,
  the deferred claim at `defer_stmt`;
* `decWit σ rd wX wS wD wV wA`: the children (child `c`'s statement read off the coverage table:
  its claims are the slots whose marks lie in its segment from its base `written[c]`, by slot
  for a gap-walked list, else by mark, `kidStmt`; its fresh
  claim at `child_fresh · g^(55c)`; its proof `wV` at its `verify_sub` call's words); the raw
  signatures, the `j`-th leanXMSS one at the slot holding the mark `j` (`slotOf`), its signature
  `wX` of `main_loop2`'s iteration `j` (`l2Args`), the `j`-th
  leanSPHINCS one at the slot holding `n_raw_x + j`, each with its slot's claim (`rawXmss`,
  `rawSphincs`); the matrix `da_verify` checks, with the claim it returns, when `n_direct_da = g`;
  and the batching's hints `wA`.

**The statement** (`Final.lean`'s `main_sound_C`): on a memory image, given the callees' contracts, a
run of `main`'s body whose public input cells hold the digest `D` gives `statementDigest (decSeed σ)
(decStmt σ rd) = D` and `NodeRelation bytecode (decSeed σ) (decStmt σ rd) (decWit …)`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-! ## Reading the memory -/

/-- The index of `a` among the powers `g^i`, `i < 2^κ`, by a search: the first `i` with `a = g^i`
(`addressIndex?` on at most `2^63` words, `indexSearch_eq`), decided by evaluation. -/
def indexSearch (κ : ℕ) (a : K) : Option (Fin (2 ^ κ)) :=
  (List.finRange (2 ^ κ)).find? fun i ↦ decide (a = Parameters.addressOfIndex i)

/-- The exponent `i < 2^34` with `g^i` the word's low limb, `0` if there is none. Only the low limb
is read: a word whose `y` limb is nonzero gets the exponent of its low limb. -/
@[irreducible] noncomputable def gLog (x : E) : ℕ := ((indexSearch 34 (x.limb 0)).map Fin.val).getD 0

/-- The digest of two cells, their limbs its four words (`digestFromHalves`). -/
def digestOfCells (a b : E) : Digest :=
  #v[(a.limb 0).lane, (a.limb 1).lane, (b.limb 0).lane, (b.limb 1).lane]

/-- The word at `p · g^k`, or `0`. -/
noncomputable def cellAt (rd : Reader) (p : E) (k : ℕ) : E :=
  (rd (p.limb 0 * Parameters.addressOfIndex k)).getD 0

/-- The `n` words from `p`. -/
noncomputable def readCells (rd : Reader) (p : E) (n : ℕ) : List E := (List.range n).map (cellAt rd p)

/-- `BYTECODE_VARS = BYTECODE_LOG + SPLIT_LOG`: a deferred claim's coordinates, the instructions'
then the split columns'. -/
abbrev bytecodeVars : ℕ := guest_const% BYTECODE_VARS

/-- `BYTECODE_LOG`: a fresh claim's coordinates, the instructions'. -/
abbrev bytecodeLog : ℕ := guest_const% BYTECODE_LOG

/-- `N_SPLIT`: a fresh claim's values, one per split column. -/
abbrev nSplit : ℕ := guest_const% N_SPLIT

/-- A deferred claim of its `26` cells: the point, then the value. -/
def deferOfCells (cs : List E) : DeferredBytecodeClaim := ⟨cs.take bytecodeVars, cs.getD bytecodeVars 0⟩

/-- A fresh claim of its `55` cells (`defer_out`): the point, then the values. -/
def freshOfCells (cs : List E) : FreshClaim := ⟨cs.take bytecodeLog, (cs.drop bytecodeLog).take nSplit⟩

/-! ## `aggregate_claims` (TRIAGE #97) -/

/-- **Child `c`'s words in memory**: its public input's two cells at `child_pi · g^(2c)`, its
fresh claim at `child_fresh · g^(55c)` (`19` coordinates, `36` values), its statement's deferred
claim at `child_carried · g^(26c)` (`25` coordinates). -/
def ChildWordsAt (rd : Reader) (cpi cfresh ccarried : E) (c : ℕ) (cc : ChildClaims) : Prop :=
  (cc.freshClaim.point.length = bytecodeLog ∧ cc.freshClaim.values.length = nSplit) ∧
    cc.carriedClaim.bytecodePoint.length = bytecodeVars ∧
    LoadHolds rd cpi (2 * c) (digestHalves cc.publicInput).1 ∧
    LoadHolds rd cpi (2 * c + 1) (digestHalves cc.publicInput).2 ∧
    ReadsAt rd (cfresh * gen ^ (55 * c)) cc.freshClaim.cells ∧
    ReadsAt rd (ccarried * gen ^ (26 * c)) cc.carriedClaim.cells

/-! ## What `main` asks of its callees with a witness -/

/-- **What a `verify_sub` call establishes for the proof `π`** (`VerifySub.MeaningVerifySub`): its
first four cells hold a public input and a seed, its sixth argument the cells of the fresh claim
the child's verification raises, of the shape `ChildHasBytecodeShape` asks (a point over the
instructions, one value per split column), and the deferring verifier accepts `π` for the public
input under the seed with that fresh claim. -/
def VerifySubOut (bytecode : List K) (rd : Reader) (args : List E) (π : Proof) : Prop :=
  ∃ pi0 pi1 s0 s1 gsq out, args = [pi0, pi1, s0, s1, gsq, out] ∧
    ∃ (seed pi : Digest) (fresh : FreshClaim), (s0, s1) = digestHalves seed ∧
      (pi0, pi1) = digestHalves pi ∧ fresh.point.length = instructionVariableCount bytecode ∧
      fresh.values.length = (splitColumns tables).length ∧
      ReadsAt rd out fresh.cells ∧ verifyDeferred bytecode seed pi fresh π = true

/-- **A run of `main_loop2` at `args`, its leanXMSS segment read as its meaning**: a valuation of
its parameters at which its body without the segment holds (`l2Pre ++ l2Post`, `Sig.loop2_split`),
and, when the tag parameters hold the chain indices, `sig` verifies the claim at the signer
`.n 65`. -/
def Loop2Out (C : CallRel) (rd : Reader) (args : List E) (sig : LeanXmss.Signature) : Prop :=
  ∃ σ : Val, (fn% «main_loop2»).params.map σ = args ∧
    Stmt.HoldsList C rd σ (Sig.l2Pre ++ Sig.l2Post) False (fun rs => rs = []) ∧
    (Sig.LxTagsHold (fun j => σ (.n (5 + j))) → Sig.XmssOut rd (σ (.n (val% «main_loop2» "s3#2"))) sig)

/-! ## The decoders

`main`'s values, cited by name (`val%`): the counts `meta[0]` to `meta[7]` (`n_lx`, `n_xdup`,
`n_raw_x`, `n_ls`, `n_sdup`, `n_raw_s`, `n_children`, `n_direct_da`, each `g^count`, the first eight
values), the region sizes, the seed `fs_seed`, the exponent table `g_squares`, the tables and
pointers (`lx_table`, `lean_sphincs_table`, `cover`, `da_digests`, `child_pi`, `child_fresh`,
`child_carried`, `written`, `defer_stmt`), the direct DA check's words, `da_pick`, and the window
tables `g_squares·g^178`. -/

/-- The four cells of slot `s` of a table at `p`. -/
noncomputable def slotCells (rd : Reader) (p : E) (s : ℕ) : List E := readCells rd (p * gen ^ (4 * s)) 4

/-- The leanXMSS claim of slot `s` of the table at `p`. -/
noncomputable def xmssAt (rd : Reader) (p : E) (s : ℕ) : LeanXmssClaim :=
  let c := slotCells rd p s
  Sig.xmssClaimOf (c.getD 0 0) (c.getD 1 0) (c.getD 2 0) (c.getD 3 0)

/-- The leanSPHINCS claim of slot `s` of the table at `p`. -/
noncomputable def sphincsAt (rd : Reader) (p : E) (s : ℕ) : LeanSphincsClaim :=
  let c := slotCells rd p s
  Sig.sphincsClaimOf (c.getD 0 0) (c.getD 1 0) (c.getD 2 0) (c.getD 3 0)

/-- The mark in coverage slot `s`, as a log. -/
noncomputable def markOf (rd : Reader) (σ : Val) (s : ℕ) : ℕ := gLog (cellAt rd (σ (.n (val% «main» "cover"))) s)

/-- The running count `written[c]`, as a log. -/
noncomputable def countOf (rd : Reader) (σ : Val) (c : ℕ) : ℕ := gLog (cellAt rd (σ (.n (val% «main» "written"))) c)

/-- The number of children. -/
noncomputable def nKids (σ : Val) : ℕ := gLog (σ (.n (val% «main» "meta[6]")))

/-- The slot of the region `[lo, lo + len)` holding the mark `e` (relative to `lo`). -/
noncomputable def slotOf (rd : Reader) (σ : Val) (lo len e : ℕ) : ℕ :=
  ((List.range len).find? fun s => decide (markOf rd σ (lo + s) = e)).getD 0

/-- The number of slots of the region `[lo, lo + len)` whose marks lie in `[a, b)`. -/
noncomputable def segCount (rd : Reader) (σ : Val) (lo len a b : ℕ) : ℕ :=
  ((List.range len).filter fun s => decide (a ≤ markOf rd σ (lo + s) ∧ markOf rd σ (lo + s) < b)).length

/-- The region sizes, as logs: leanXMSS slots, leanSPHINCS slots. -/
noncomputable def lxSlots (σ : Val) : ℕ := gLog (σ (.n (val% «main» "lx_slots_g")))
noncomputable def lsSlots (σ : Val) : ℕ := gLog (σ (.n (val% «main» "lean_sphincs_slots_g")))

/-- The DA digest of slot `k` of `da_digests`: its two cells at `g^(2k)` (child `c`'s at `k = c`,
the node's own at `k = n_children`). -/
noncomputable def daDigestAt (rd : Reader) (σ : Val) (k : ℕ) : Digest :=
  digestOfCells (cellAt rd (σ (.n (val% «main» "da_digests"))) (2 * k)) (cellAt rd (σ (.n (val% «main» "da_digests"))) (2 * k + 1))

/-- **A child's list's slots** in the region `[lo, lo + len)` of the coverage table, its marks in
`[a, b)`: when as many of the region's slots hold the list's first mark `a` as hold a mark of
`[a, b)` (a gap-walked list, `child_claim_list_mono`, marks every claim with `a`; or a list of at
most one claim), the slots in slot order (the gap walk's slots strictly increase); else the slot
of each mark `a + j` in turn (`child_claim_list_any` marks claim `j` with `a + j`). -/
noncomputable def kidSlots (rd : Reader) (σ : Val) (lo len a b : ℕ) : List ℕ :=
  if segCount rd σ lo len a (a + 1) = segCount rd σ lo len a b then
    (List.range len).filter fun s => decide (a ≤ markOf rd σ (lo + s) ∧ markOf rd σ (lo + s) < b)
  else (List.range (segCount rd σ lo len a b)).map fun j => slotOf rd σ lo len (a + j)

/-- **Child `c`'s statement**, read off the coverage table: of the marks in its segment
`[written[c], written[c + 1])`, the leanXMSS region's list, then the leanSPHINCS region's from
the mark after the leanXMSS ones (`kidSlots`), each the claim of its slot; its DA digest at
`da_digests · g^(2c)`; its deferred claim at `child_carried · g^(26c)`. -/
noncomputable def kidStmt (rd : Reader) (σ : Val) (c : ℕ) : NodeStatement :=
  let a := countOf rd σ c
  let b := countOf rd σ (c + 1)
  let nx := segCount rd σ 0 (lxSlots σ) a b
  ⟨⟨(kidSlots rd σ 0 (lxSlots σ) a b).map (xmssAt rd (σ (.n (val% «main» "lx_table")))),
    (kidSlots rd σ (lxSlots σ) (lsSlots σ) (a + nx) b).map (sphincsAt rd (σ (.n (val% «main» "lean_sphincs_table")))),
    daDigestAt rd σ c⟩,
   deferOfCells (readCells rd (σ (.n (val% «main» "child_carried")) * gen ^ (26 * c)) 26)⟩

/-- The words of child `c`'s `verify_sub` call. -/
noncomputable def subArgs (rd : Reader) (σ : Val) (c : ℕ) : List E :=
  [cellAt rd (σ (.n (val% «main» "child_pi"))) (2 * c), cellAt rd (σ (.n (val% «main» "child_pi"))) (2 * c + 1), σ (.n (val% «main» "fs_seed[0]")), σ (.n (val% «main» "fs_seed[1]")),
    σ (.n (val% «main» "g_squares")), σ (.n (val% «main» "child_fresh")) * gen ^ (55 * c)]

/-- **Child `c`**: its statement (`kidStmt`), its fresh claim at `child_fresh · g^(55c)`, its
proof `wV` at its `verify_sub` call's words. -/
noncomputable def decKid (rd : Reader) (σ : Val) (wV : List E → Proof) (c : ℕ) : Child :=
  ⟨kidStmt rd σ c, freshOfCells (readCells rd (σ (.n (val% «main» "child_fresh")) * gen ^ (55 * c)) 55),
    wV (subArgs rd σ c)⟩

/-- **The seed**: the cells `fs_seed`. -/
def decSeed (σ : Val) : Digest := digestOfCells (σ (.n (val% «main» "fs_seed[0]"))) (σ (.n (val% «main» "fs_seed[1]")))

/-- **The statement**: the declared claims at the leanXMSS and leanSPHINCS tables, the DA digest
at the slot `da_pick` of `da_digests`, the deferred claim at `defer_stmt`. -/
noncomputable def decStmt (σ : Val) (rd : Reader) : NodeStatement :=
  ⟨⟨(List.range (gLog (σ (.n (val% «main» "meta[0]"))))).map (xmssAt rd (σ (.n (val% «main» "lx_table")))),
    (List.range (gLog (σ (.n (val% «main» "meta[3]"))))).map (sphincsAt rd (σ (.n (val% «main» "lean_sphincs_table")))),
    daDigestAt rd σ (gLog (σ (.n (val% «main» "da_pick"))))⟩,
   deferOfCells (readCells rd (σ (.n (val% «main» "defer_stmt"))) 26)⟩

/-- The number of raw leanXMSS signatures, raw leanSPHINCS signatures, direct DA checks. -/
noncomputable def nRawX (σ : Val) : ℕ := gLog (σ (.n (val% «main» "meta[2]")))
noncomputable def nRawS (σ : Val) : ℕ := gLog (σ (.n (val% «main» "meta[5]")))
noncomputable def nDirect (σ : Val) : ℕ := gLog (σ (.n (val% «main» "meta[7]")))

/-- The DA claim `da_verify` returns: its root and its challenge. -/
noncomputable def dvClaim (σ : Val) : DaClaim :=
  ⟨digestOfCells (σ (.n (val% «main» "root_0"))) (σ (.n (val% «main» "root_1"))), σ (.n (val% «main» "z"))⟩

/-- `main_loop2`'s arguments after its counter: `n_raw_x`, `lx_slots`, `cover`, `lx_table`, then
the `51` carried tags `lx_tags` (`lean_ethereum.py`). -/
def l2Args (σ : Val) : List E :=
  [σ (.n (val% «main» "meta[2]")), σ (.n (val% «main» "lx_slots_g")), σ (.n (val% «main» "cover")), σ (.n (val% «main» "lx_table"))] ++ (List.range 51).map fun j => σ (.n ((val% «main» "lx_tags[0]") + j))

/-- The raw leanXMSS signature of mark `j`: the claim of the slot holding the mark, with the
signature `wX` of `main_loop2`'s iteration `j` (its arguments `g^j :: l2Args σ`). -/
noncomputable def rawXmss (rd : Reader) (σ : Val) (wX : List E → LeanXmss.Signature) (j : ℕ) :
    LeanXmssClaim × LeanXmss.Signature :=
  let s := slotOf rd σ 0 (lxSlots σ) j
  (xmssAt rd (σ (.n (val% «main» "lx_table"))) s, wX (gen ^ j :: l2Args σ))

/-- The raw leanSPHINCS signature of mark `n_raw_x + j`, in the leanSPHINCS region (`rawXmss`). -/
noncomputable def rawSphincs (rd : Reader) (σ : Val) (wS : E → Sphincs.Signature) (j : ℕ) :
    LeanSphincsClaim × Sphincs.Signature :=
  let s := slotOf rd σ (lxSlots σ) (lsSlots σ) (nRawX σ + j)
  (sphincsAt rd (σ (.n (val% «main» "lean_sphincs_table"))) s, wS (σ (.n (val% «main» "lean_sphincs_table")) * gen ^ (4 * s)))

/-- **The witness**: the children, the raw signatures by their marks (`rawXmss`, `rawSphincs`),
the matrix `da_verify` checks with the claim it returns, the batching's hints. -/
noncomputable def decWit (σ : Val) (rd : Reader) (wX : List E → LeanXmss.Signature)
    (wS : E → Sphincs.Signature) (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → Proof) (wA : List E → BatchingHints) : NodeWitness :=
  ⟨(List.range (nKids σ)).map (decKid rd σ wV),
    (List.range (nRawX σ)).map (rawXmss rd σ wX),
    (List.range (nRawS σ)).map (rawSphincs rd σ wS),
    if nDirect σ = 1 then
      some (dvClaim σ, wD [σ (.n (val% «main» "byte_bits"))] [σ (.n (val% «main» "root_0")), σ (.n (val% «main» "root_1")), σ (.n (val% «main» "z"))])
    else none,
    wA [σ (.n (val% «main» "meta[6]")), σ (.n (val% «main» "child_pi")), σ (.n (val% «main» "child_fresh")), σ (.n (val% «main» "child_carried")), σ (.n (val% «main» "defer_stmt")), σ (.n (val% «main» "s63.e.s0#1"))]⟩

/-! ## The functions, found -/

theorem find_main : coreProgram.find? "main" = some fn% «main» :=
  coreProgram_find?_at (j := idx% «main») rfl

theorem find_aggregate_claims : coreProgram.find? "aggregate_claims" = some fn% «aggregate_claims»
    :=
  coreProgram_find?_at (j := idx% «aggregate_claims») rfl

end
end LeanVM.Guest.B1.Main
