/-
  LeanVM.Guest.B1.Main.Interface

  The interface of B1 for `main` and `aggregate_claims`: what the batching of the children
  computes, what `main` asks of its callees, the decoders of the seed, the statement and the
  witness, and the statement that `main`'s run establishes `NodeRelation` of what they decode.
-/

module

public import LeanVM.Guest.B1.Da.Interface
public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Sig.Interface

/-!
# `main` and `aggregate_claims`: meanings (TRIAGE G #96, #97)

**`aggregate_claims`** (`core33`): from the batching seed (`AGG_SEED_*`), the duplex sponge
absorbs the children's count and every child's words, checks the proof of work on the hinted
nonce, squeezes the challenge `λ`, and one sumcheck (`batch_sumcheck`) reduces the children's
claims on the bytecode to the claim written at `defer_stmt`: `Node.batch` of the children whose
words the memory holds (`ChildWordsAt`) returns that claim, for the hints `bc_sumcheck_msgs` (the
nonce first) and `bc_star_hint` (`MeaningAggregateClaims`), given the grind's window tables at
its last argument (`WinTabs`).

**`main`** (G:4491-4667, `core0`). Its callees with a witness, each through a witness function of
the call's words (`CalleesW`): a leanXMSS signature `wX args` for the raw iteration of
`__loop2` at `args` (the leanXMSS check is inline there at 40f877dc: `Loop2Out`, its segment read
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
  claim at `child_fresh · g^(24c)`; its proof `wV` at its `verify_sub` call's words); the raw
  signatures, the `j`-th leanXMSS one at the slot holding the mark `j` (`slotOf`), its signature
  `wX` of `__loop2`'s iteration `j` (`l2Args`), the `j`-th
  leanSPHINCS one at the slot holding `n_raw_x + j`, each with its slot's claim (`rawXmss`,
  `rawSphincs`); the matrix `da_verify` checks, with the claim it returns, when `n_direct_da = g`;
  and the batching's hints `wA`.

**The statement** (`main_sound_Spec`): on a memory image, given the callees' contracts, a run of
`main`'s body whose public input cells hold the digest `D` gives `statementDigest (decSeed σ)
(decStmt σ rd) = D` and `NodeRelation bytecode (decSeed σ) (decStmt σ rd) (decWit …)`. Its proof,
`main_sound_w`, composes the `…_Spec`s of every family.
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

/-- `BYTECODE_VARS`. -/
abbrev bytecodeVars : ℕ := 23

/-- A deferred claim of its `24` cells: the point, then the value. -/
def deferOfCells (cs : List E) : DeferredClaim := ⟨cs.take bytecodeVars, cs.getD bytecodeVars 0⟩

/-- A proof's claim on the bytecode of its `24` cells (`defer_out`). -/
def fixedOfCells (cs : List E) : BytecodeClaim := ⟨cs.take bytecodeVars, cs.getD bytecodeVars 0⟩

/-! ## `aggregate_claims` (G:4670-4773, TRIAGE #97) -/

/-- **Child `c`'s words in memory**: its public input's two cells at `child_pi · g^(2c)`, its
proof's claim at `child_fresh · g^(24c)`, its statement's deferred claim at
`child_carried · g^(24c)`, both claims at `23` coordinates. -/
def ChildWordsAt (rd : Reader) (cpi cfresh ccarried : E) (c : ℕ) (cc : ChildClaims) : Prop :=
  cc.freshClaim.bytecodePoint.length = bytecodeVars ∧ cc.carriedClaim.bytecodePoint.length = bytecodeVars ∧
    LoadHolds rd cpi (2 * c) (digestHalves cc.publicInput).1 ∧
    LoadHolds rd cpi (2 * c + 1) (digestHalves cc.publicInput).2 ∧
    ReadsAt rd (cfresh * gen ^ (24 * c)) (DeferredClaim.cells cc.freshClaim) ∧
    ReadsAt rd (ccarried * gen ^ (24 * c)) cc.carriedClaim.cells

/-- **`aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt, tabs)`**,
for `n_children_g = g^m`, `1 ≤ m ≤ 16`, with the window tables at `tabs`: it returns nothing, and
for some hints the claim written at `defer_stmt` (`23` coordinates, then the value) is the
batching (`Node.batch`) of every list of `m` children whose words the memory holds. -/
def MeaningAggregateClaims (rd : Reader) : List E → List E → Prop
  | [ncg, cpi, cfresh, ccarried, dst, tabs], rets => WinTabs rd tabs →
      ∀ m, 1 ≤ m → m ≤ 16 → ncg = gen ^ m →
      rets = [] ∧ ∃ (h : BatchingHints) (out : DeferredClaim),
        out.bytecodePoint.length = bytecodeVars ∧ ReadsAt rd dst out.cells ∧
        ∀ cs : List ChildClaims, cs.length = m →
          (∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) →
          batch cs h = some out
  | _, _ => False

/-- `aggregate_claims`' core IR gives its meaning. -/
def aggregate_claims_sound_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "aggregate_claims" args rets → MeaningAggregateClaims rd args rets

/-! ## What `main` asks of its callees with a witness -/

/-- **What a `verify_sub` call establishes for the proof `π`** (B1-d's `verify_sub`, G:3321;
`VerifySub.MeaningVerifySub`): its first four cells hold a public input and a seed, its sixth
argument the child proof's claim on the bytecode (`23` coordinates, then the value), and the
deferring verifier accepts `π` for the public input under the seed. -/
def VerifySubOut (bytecode : List K) (rd : Reader) (args : List E) (π : Proof) : Prop :=
  ∃ pi0 pi1 s0 s1 gsq out, args = [pi0, pi1, s0, s1, gsq, out] ∧
    ∃ (seed pi : Digest) (fresh : BytecodeClaim), (s0, s1) = digestHalves seed ∧
      (pi0, pi1) = digestHalves pi ∧ fresh.bytecodePoint.length = bytecodeVars ∧
      ReadsAt rd out (DeferredClaim.cells fresh) ∧ verifyDeferred bytecode seed pi fresh π = true

/-- **A run of `__loop2` at `args`, its leanXMSS segment read as its meaning**: a valuation of its
parameters at which its body without the segment holds (`l2Pre ++ l2Post`, `Sig.loop2_split`),
and, when the tag parameters hold the chain indices, `sig` verifies the claim at the signer
`.n 65`. -/
def Loop2Out (C : CallRel) (rd : Reader) (args : List E) (sig : LeanXmss.Signature) : Prop :=
  ∃ σ : Val, Data.core36.params.map σ = args ∧
    Stmt.HoldsList C rd σ (Sig.l2Pre ++ Sig.l2Post) False (fun rs => rs = []) ∧
    (Sig.LxTagsHold (fun j => σ (.n (5 + j))) → Sig.XmssOut rd (σ (.n 65)) sig)

/-- **The callees' contracts with witness functions**, on the call relation `coreProgram.Rel`. -/
structure CalleesW (bytecode : List K) (rd : Reader) (wX : List E → LeanXmss.Signature)
    (wS : E → Sphincs.Signature) (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → Proof) (wA : List E → BatchingHints) : Prop where
  /-- A raw leanXMSS iteration (`__loop2`, the leanXMSS check inline): its body around the
  segment, and the signature `wX args` verifying the claim at its signer (`Loop2Out`). -/
  xmss : ∀ args, coreProgram.Rel rd "__loop2" args [] → Loop2Out (coreProgram.Rel rd) rd args (wX args)
  /-- A leanSPHINCS check with the byte table: the signature `wS p` verifies the claim at `p`. -/
  sphincs : ∀ p bb, coreProgram.Rel rd "verify_sig_lean_sphincs" [p, bb] [] →
    Sig.ByteBits rd bb → Sig.SphincsOut rd p (wS p)
  /-- The DA check with the exponent table: the matrix `wD args rets` opens the returned claim,
  the root's cells and the challenge (`Da.MeaningDaVerify`). -/
  da : ∀ gsq rets, coreProgram.Rel rd "da_verify" [gsq] rets → Da.SquaresAt rd gsq →
    ∃ (root : Digest) (z : E), (wD [gsq] rets).Opens root z ∧ rets = digestCells root ++ [z]
  /-- A child proof's check with the exponent table: the proof `wV args`. -/
  sub : ∀ pi0 pi1 s0 s1 gsq out,
    coreProgram.Rel rd "verify_sub" [pi0, pi1, s0, s1, gsq, out] [] → ExpTables rd gsq →
    VerifySubOut bytecode rd [pi0, pi1, s0, s1, gsq, out] (wV [pi0, pi1, s0, s1, gsq, out])
  /-- The batching, for `n_children_g = g^m`, `1 ≤ m ≤ 16`, with the window tables at `tabs`,
  with the hints `wA args`. -/
  agg : ∀ ncg cpi cfresh ccarried dst tabs, coreProgram.Rel rd "aggregate_claims"
    [ncg, cpi, cfresh, ccarried, dst, tabs] [] → WinTabs rd tabs → ∀ m, 1 ≤ m → m ≤ 16 →
      ncg = gen ^ m →
      ∃ out : DeferredClaim, out.bytecodePoint.length = bytecodeVars ∧ ReadsAt rd dst out.cells ∧
        ∀ cs : List ChildClaims, cs.length = m →
          (∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c]) →
          batch cs (wA [ncg, cpi, cfresh, ccarried, dst, tabs]) = some out

/-! ## The decoders

`main`'s values (`core0`): the counts `n_lx = .n 0`, `n_xdup = .n 1`, `n_raw_x = .n 2`,
`n_ls = .n 3`, `n_sdup = .n 4`, `n_raw_s = .n 5`, `n_children = .n 6`, `n_direct_da = .n 7`
(each `g^count`); the region sizes `lx_slots = .n 40`, `ls_slots = .n 41`, `n_total = .n 42`;
`fs_seed = .n 47, .n 48`; the exponent table `.n 49`; the pointers
`lx_table = .n 52`, `ls_table = .n 55`, `cover = .n 66`, `da_digests = .n 385`,
`child_pi = .n 404`, `child_fresh = .n 410`, `child_carried = .n 416`, `written = .n 419`,
`defer_stmt = .n 437`; the direct DA check's words `.n 390 … .n 392`; `da_pick = .n 426`; the
window tables `.n 465`. -/

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
noncomputable def markOf (rd : Reader) (σ : Val) (s : ℕ) : ℕ := gLog (cellAt rd (σ (.n 66)) s)

/-- The running count `written[c]`, as a log. -/
noncomputable def countOf (rd : Reader) (σ : Val) (c : ℕ) : ℕ := gLog (cellAt rd (σ (.n 419)) c)

/-- The number of children. -/
noncomputable def nKids (σ : Val) : ℕ := gLog (σ (.n 6))

/-- The slot of the region `[lo, lo + len)` holding the mark `e` (relative to `lo`). -/
noncomputable def slotOf (rd : Reader) (σ : Val) (lo len e : ℕ) : ℕ :=
  ((List.range len).find? fun s => decide (markOf rd σ (lo + s) = e)).getD 0

/-- The number of slots of the region `[lo, lo + len)` whose marks lie in `[a, b)`. -/
noncomputable def segCount (rd : Reader) (σ : Val) (lo len a b : ℕ) : ℕ :=
  ((List.range len).filter fun s => decide (a ≤ markOf rd σ (lo + s) ∧ markOf rd σ (lo + s) < b)).length

/-- The region sizes, as logs: leanXMSS slots, leanSPHINCS slots. -/
noncomputable def lxSlots (σ : Val) : ℕ := gLog (σ (.n 40))
noncomputable def lsSlots (σ : Val) : ℕ := gLog (σ (.n 41))

/-- The DA digest of slot `k` of `da_digests`: its two cells at `g^(2k)` (child `c`'s at `k = c`,
the node's own at `k = n_children`). -/
noncomputable def daDigestAt (rd : Reader) (σ : Val) (k : ℕ) : Digest :=
  digestOfCells (cellAt rd (σ (.n 385)) (2 * k)) (cellAt rd (σ (.n 385)) (2 * k + 1))

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
`da_digests · g^(2c)`; its deferred claim at `child_carried · g^(24c)`. -/
noncomputable def kidStmt (rd : Reader) (σ : Val) (c : ℕ) : NodeStatement :=
  let a := countOf rd σ c
  let b := countOf rd σ (c + 1)
  let nx := segCount rd σ 0 (lxSlots σ) a b
  ⟨⟨(kidSlots rd σ 0 (lxSlots σ) a b).map (xmssAt rd (σ (.n 52))),
    (kidSlots rd σ (lxSlots σ) (lsSlots σ) (a + nx) b).map (sphincsAt rd (σ (.n 55))),
    daDigestAt rd σ c⟩,
   deferOfCells (readCells rd (σ (.n 416) * gen ^ (24 * c)) 24)⟩

/-- The words of child `c`'s `verify_sub` call. -/
noncomputable def subArgs (rd : Reader) (σ : Val) (c : ℕ) : List E :=
  [cellAt rd (σ (.n 404)) (2 * c), cellAt rd (σ (.n 404)) (2 * c + 1), σ (.n 47), σ (.n 48),
    σ (.n 49), σ (.n 410) * gen ^ (24 * c)]

/-- **Child `c`**: its statement (`kidStmt`), its fresh claim at `child_fresh · g^(24c)`, its
proof `wV` at its `verify_sub` call's words. -/
noncomputable def decKid (rd : Reader) (σ : Val) (wV : List E → Proof) (c : ℕ) : Child :=
  ⟨kidStmt rd σ c, fixedOfCells (readCells rd (σ (.n 410) * gen ^ (24 * c)) 24),
    wV (subArgs rd σ c)⟩

/-- **The seed**: the cells `fs_seed`. -/
def decSeed (σ : Val) : Digest := digestOfCells (σ (.n 47)) (σ (.n 48))

/-- **The statement**: the declared claims at the leanXMSS and leanSPHINCS tables, the DA digest
at the slot `da_pick` of `da_digests`, the deferred claim at `defer_stmt`. -/
noncomputable def decStmt (σ : Val) (rd : Reader) : NodeStatement :=
  ⟨⟨(List.range (gLog (σ (.n 0)))).map (xmssAt rd (σ (.n 52))),
    (List.range (gLog (σ (.n 3)))).map (sphincsAt rd (σ (.n 55))),
    daDigestAt rd σ (gLog (σ (.n 426)))⟩,
   deferOfCells (readCells rd (σ (.n 437)) 24)⟩

/-- The number of raw leanXMSS signatures, raw leanSPHINCS signatures, direct DA checks. -/
noncomputable def nRawX (σ : Val) : ℕ := gLog (σ (.n 2))
noncomputable def nRawS (σ : Val) : ℕ := gLog (σ (.n 5))
noncomputable def nDirect (σ : Val) : ℕ := gLog (σ (.n 7))

/-- The DA claim `da_verify` returns: its root and its challenge. -/
noncomputable def dvClaim (σ : Val) : DaClaim :=
  ⟨digestOfCells (σ (.n 390)) (σ (.n 391)), σ (.n 392)⟩

/-- `__loop2`'s arguments after its counter: `n_raw_x`, `lx_slots`, `cover`, `lx_table`, then
the `51` carried tags `lx_tags` (`.n 325 ..< .n 376`; lean_ethereum.py:4578-4591). -/
def l2Args (σ : Val) : List E :=
  [σ (.n 2), σ (.n 40), σ (.n 66), σ (.n 52)] ++ (List.range 51).map fun j => σ (.n (325 + j))

/-- The raw leanXMSS signature of mark `j`: the claim of the slot holding the mark, with the
signature `wX` of `__loop2`'s iteration `j` (its arguments `g^j :: l2Args σ`). -/
noncomputable def rawXmss (rd : Reader) (σ : Val) (wX : List E → LeanXmss.Signature) (j : ℕ) :
    LeanXmssClaim × LeanXmss.Signature :=
  let s := slotOf rd σ 0 (lxSlots σ) j
  (xmssAt rd (σ (.n 52)) s, wX (gen ^ j :: l2Args σ))

/-- The raw leanSPHINCS signature of mark `n_raw_x + j`, in the leanSPHINCS region (`rawXmss`). -/
noncomputable def rawSphincs (rd : Reader) (σ : Val) (wS : E → Sphincs.Signature) (j : ℕ) :
    LeanSphincsClaim × Sphincs.Signature :=
  let s := slotOf rd σ (lxSlots σ) (lsSlots σ) (nRawX σ + j)
  (sphincsAt rd (σ (.n 55)) s, wS (σ (.n 55) * gen ^ (4 * s)))

/-- **The witness**: the children, the raw signatures by their marks (`rawXmss`, `rawSphincs`),
the matrix `da_verify` checks with the claim it returns, the batching's hints. -/
noncomputable def decWit (σ : Val) (rd : Reader) (wX : List E → LeanXmss.Signature)
    (wS : E → Sphincs.Signature) (wD : List E → List E → LeanVM.Da.MatrixWitness)
    (wV : List E → Proof) (wA : List E → BatchingHints) : NodeWitness :=
  ⟨(List.range (nKids σ)).map (decKid rd σ wV),
    (List.range (nRawX σ)).map (rawXmss rd σ wX),
    (List.range (nRawS σ)).map (rawSphincs rd σ wS),
    if nDirect σ = 1 then
      some (dvClaim σ, wD [σ (.n 49)] [σ (.n 390), σ (.n 391), σ (.n 392)])
    else none,
    wA [σ (.n 6), σ (.n 404), σ (.n 410), σ (.n 416), σ (.n 437), σ (.n 465)]⟩

/-! ## The statement -/

/-- **`main`, soundly, its witness decoded** (G:4491-4667, TRIAGE #96): on a memory image whose
public input cells (`[1]`, `[g]`) hold the digest `D`, given the callees' contracts with the
witness functions, every run of `main`'s body (under `coreProgram.Rel`) gives the seed
`decSeed σ` and the statement `decStmt σ rd` of digest `D`, which the witness
`decWit σ rd wX wS wD wV wA` holds (`NodeRelation`) for the guest's bytecode of `2^23` words. -/
def main_sound_Spec (bytecode : List K) : Prop :=
  bytecode.length = 2 ^ bytecodeVars →
  ∀ (rd : Reader), MemOk rd →
  ∀ (wX : List E → LeanXmss.Signature) (wS : E → Sphincs.Signature)
    (wD : List E → List E → LeanVM.Da.MatrixWitness) (wV : List E → Proof) (wA : List E → BatchingHints),
    CalleesW bytecode rd wX wS wD wV wA →
  ∀ (D : Digest) (σ : Val), LoadHolds rd 1 0 (digestHalves D).1 →
    LoadHolds rd 1 1 (digestHalves D).2 →
    Stmt.HoldsList (coreProgram.Rel rd) rd σ Data.core0.body False (fun rs => rs = []) →
      statementDigest (decSeed σ) (decStmt σ rd) = D ∧
        NodeRelation bytecode (decSeed σ) (decStmt σ rd) (decWit σ rd wX wS wD wV wA)

/-! ## The functions, found -/

theorem find_main : coreProgram.find? "main" = some Data.core0 :=
  Program.find?_of_indexOf? (j := 0) (by decide +kernel) rfl

theorem find_aggregate_claims : coreProgram.find? "aggregate_claims" = some Data.core33 :=
  Program.find?_of_indexOf? (j := 33) (by decide +kernel) rfl

end
end LeanVM.Guest.B1.Main
