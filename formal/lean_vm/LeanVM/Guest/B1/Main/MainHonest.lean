/-
  LeanVM.Guest.B1.Main.MainHonest

  `main`'s honest run on a node's statement and witness: its oracle (`hData`) and the words it
  leaves in its buffers (`hOwn`), as the honest prover plans them (`Hints.honestPushes`).
-/

module

public import LeanVM.Guest.B1.Main.MainAtDefs
public import LeanVM.Guest.B1.Main.Plan
public import LeanVM.Guest.Hints
public import LeanVM.Guest.AcceptableChild

/-!
# `main`'s honest run

For a statement `s` held by a witness `w` under the seed `seed`:

* the counts of `meta` are the declared lists' lengths, their regions' duplicates (`xPlan`,
  `sPlan`), the raw signatures, the children, whether a DA matrix is checked; `da_pick` the slot
  of `da_digests` the node publishes (`daPick`);
* `hW c`: the running count before child `c`, the raw claims first, then each child's claims
  (its leanXMSS, leanSPHINCS claims);
* the coverage table's word at each slot is `g` to the global index of the claim that takes it
  (`hMarkX`, `hMarkS`): the claims are numbered the raw leanXMSS ones, the raw leanSPHINCS ones,
  then child by child;
* the tables hold the declared claims then the duplicates (`claimCells`), `da_digests` the
  children's DA digests then the own one (`hOwnDa`), the children's buffers their statements'
  digests, fresh claims and deferred claims.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (claimCells daPick)


@[expose] public section

variable (seed : Digest) (s : NodeStatement) (w : NodeWitness)

/-! ## Counts -/

/-- The raw signatures with their claims (the statement a parameter, as every name of an honest
run has one). -/
def hRawX (_ : NodeStatement) (w : NodeWitness) : List (LeanXmssClaim × LeanXmss.Signature) :=
  w.xmssSignatures
def hRawS (_ : NodeStatement) (w : NodeWitness) : List (LeanSphincsClaim × Sphincs.Signature) :=
  w.sphincsSignatures

/-- Child `c`'s claims' counts. -/
def hEx (c : ℕ) : ℕ := (w.children.map (·.statement.claims.xmss.length)).getD c 0
def hEs (c : ℕ) : ℕ := (w.children.map (·.statement.claims.sphincs.length)).getD c 0

/-- **The running count before child `c`.** -/
def hW : ℕ → ℕ
  | 0 => (hRawX s w).length + (hRawS s w).length
  | c + 1 => hW c + (hEx w c + hEs w c)

/-! ## Marks -/

/-- The child and the index within it of claim `k` of the children's claims, child by child. -/
def segOf : List ℕ → ℕ → ℕ × ℕ
  | [], k => (0, k)
  | l :: ls, k => if k < l then (0, k) else ((segOf ls (k - l)).1 + 1, (segOf ls (k - l)).2)

/-- The global index of the leanXMSS region's taker `k` (raw first, then the children's). -/
def hMarkX (k : ℕ) : ℕ :=
  if k < (hRawX s w).length then k
  else let p := segOf (w.children.map (·.statement.claims.xmss.length)) (k - (hRawX s w).length)
    hW s w p.1 + p.2

/-- The leanSPHINCS region's. -/
def hMarkS (k : ℕ) : ℕ :=
  if k < (hRawS s w).length then (hRawX s w).length + k
  else let p := segOf (w.children.map (·.statement.claims.sphincs.length)) (k - (hRawS s w).length)
    hW s w p.1 + hEx w p.1 + p.2

/-- **The coverage table's words**: each slot's taker's mark, region by region. -/
def hCover : List E :=
  ((List.range (s.claims.xmss ++ (xPlan s w).duplicates).length).map fun t =>
      gen ^ hMarkX s w ((slotsOf (xPlan s w)).idxOf t)) ++
    ((List.range (s.claims.sphincs ++ (sPlan s w).duplicates).length).map fun t =>
      gen ^ hMarkS s w ((slotsOf (sPlan s w)).idxOf t))

/-! ## The oracle and the buffers -/

/-- A DA claim's four cells: its root's, then its challenge's rate cells with the tag `0`
(`fs_pack(z_cells, 0, z, 0)`, `lean_ethereum.py:4325`). -/
def daCells (c : DaClaim) : List E := B1.Digest.digestCells c.daRoot ++ [c.membershipChallenge]

/-- The own DA digest: the checked claim's, or zeros. -/
def hOwnDa : Digest := match w.daMatrix with
  | some p => daClaimDigest p.1
  | none => zeroDigest

/-- **`main`'s honest oracle** (besides pointers). -/
def hData : MainData where
  nlx := s.claims.xmss.length
  nxd := (xPlan s w).duplicates.length
  nrx := (hRawX s w).length
  nls := s.claims.sphincs.length
  nsd := (sPlan s w).duplicates.length
  nrs := (hRawS s w).length
  nc := w.children.length
  nd := (w.daMatrix.map fun _ => 1).getD 0
  pick := daPick s w
  seed := seed
  xd := claimListDigest xmssPublicKeyBytes s.claims.xmss
  sd := claimListDigest Sphincs.PublicKey.toBytes s.claims.sphincs
  sdg := statementDigest seed s
  daR := (w.daMatrix.map fun p => daCells p.1).getD [0, 0, 0]
  dap := s.claims.daDigest
  leaf := s.deferredClaim.bytecodeValue

/-- **`main`'s honest buffers' words**, in allocation order. -/
def hOwn : List (List E) :=
  [(s.claims.xmss ++ (xPlan s w).duplicates).flatMap (fun c => claimCells c.1.root c.1.parameter c.2),
    (s.claims.sphincs ++ (sPlan s w).duplicates).flatMap (fun c => claimCells c.1.publicSeed c.1.root c.2),
    hCover s w,
    (List.range 256).map fun v => word v 0,
    (w.children.map (·.statement.claims.daDigest) ++ [hOwnDa w]).flatMap B1.Digest.digestCells,
    w.children.flatMap (fun c => B1.Digest.digestCells (statementDigest seed c.statement)),
    w.children.flatMap (fun c => DeferredClaim.cells c.freshClaim),
    w.children.flatMap (fun c => c.statement.deferredClaim.cells),
    (List.range (w.children.length + 1)).map (fun c => gen ^ hW s w c),
    s.deferredClaim.cells]

end
end LeanVM.Guest.B1.Main
