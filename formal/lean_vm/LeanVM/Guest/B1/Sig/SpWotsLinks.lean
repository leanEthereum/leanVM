/-
  LeanVM.Guest.B1.Sig.SpWotsLinks

  `sp_wots`'s link, in pieces: the map, the cuts and each piece's check.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsRef
public import LeanVM.Guest.Pack.sp_wots.Core
public import LeanVM.Guest.Fast.SpWotsTables
public import LeanVM.Guest.Fast.Numbers
meta import LeanVM.Guest.Ref.Elab
meta import LeanVM.Guest.B1.Sig.SpWotsRef

/-!
# `sp_wots`, linked in pieces

The link check (`LeanVM.Guest.Ref.Link`) of `sp_wots` against `spWotsRef`, too large for one kernel
evaluation, in pieces (`Map.Pieces`): the body cut before each digit group's hint (`spCuts`), the
commands before each group's range check (`spRefCuts`), all against one map, `spMap`. The map is
computed when this module is elaborated (`sp_wots_map%`: the inference `infer` run on the core
function read off its definition, `LeanVM.Guest.Ref.Elab`), unverified: a wrong entry can only make
a piece's check fail. Each piece but the first starts from the values every group reads known
(`spKc`: the parameters, `at`, `powers`, the first group's word, its range check, the padding run
and the constant set before the first `match`). A piece's check (`spPiece`, the last one's
`spPieceLast`) first reads the map in order up to where the piece starts (`Map.warm`), which only
keeps the kernel's recursion shallow.

`spPositions` are the values the decoder reads (each group's digit word at `spSel`, each arm's
chains' starts at `spTabOf`, as `Guest/Fast/` reads them), which own the names of the reference
function's hints there. `SpWotsLinks0` to `SpWotsLinks2` check the pieces, one declaration each,
and the owners; `SpWotsLinksAll` assembles them.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Ref
open LeanVM.Guest.Fast

meta section

deriving instance Lean.ToExpr for SpName

/-- `sp_wots_map%`: `infer` of `sp_wots`'s core function and `spWotsRef`, as a literal map. -/
syntax (name := spWotsMapStx) "sp_wots_map%" : term

open Lean Elab Term in
def elabSpWotsMap : TermElab := fun _ _ => do
  return Ref.Elab.mapE (infer (← Ref.Elab.decFn ``Fn.«sp_wots».core) spWotsRef)

end

attribute [local term_elab spWotsMapStx] elabSpWotsMap

@[expose] public section

/-- `sp_wots`'s map, computed at elaboration. -/
noncomputable def spMap : Map SpName := sp_wots_map%

/-- The body's pieces: the first group with what precedes it, each other group, the rest. -/
def spCuts : List ℕ := 22 :: List.replicate 21 5

/-- The commands' pieces, as the body's. -/
def spRefCuts : List ℕ := 12 :: List.replicate 21 2

/-- The values every group reads known: the first `27`. -/
def spKc : ℕ := 2 ^ 27 - 1

/-- The known values after the parameters. -/
noncomputable def spK0 : ℕ := (spMap.uses 0 Fn.«sp_wots».core.params).getD 0

/-- Piece `i` of the body. -/
noncomputable def spP (i : ℕ) : List Stmt := (cutAt spCuts Fn.«sp_wots».core.body).getD i []

/-- Piece `i` of the commands. -/
def spQ (i : ℕ) : List (Cmd SpName) := (cutAt spRefCuts spWotsRef.body).getD i []

/-- Piece `i`'s check, `i < 22`. -/
noncomputable def spPiece (i : ℕ) : Bool :=
  spMap.warm (spSel.getD i 0) && spMap.segOk (if i = 0 then spK0 else spKc) spKc (spP i) (spQ i)

/-- The last piece's check: the codeword's checks and the leaf. -/
noncomputable def spPieceLast : Bool :=
  spMap.warm (spSel.getD 21 0) && spMap.body spKc (spP 22) (spQ 22) spWotsRef.rets

/-- The values the signature's decoder reads and the names they own: group `p`'s digit word, and
in each arm `k` each chain's start. -/
def spPositions : List (ℕ × SpName) :=
  (List.range 22).flatMap fun p => (spSel.getD p 0, .group p) ::
    (List.range (4 ^ spN p)).flatMap fun k => (List.range (spN p)).map fun r =>
      (spSel.getD p 0 + offAt (spTabOf p) r k, spStartN (3 * p + r) k)

end
end LeanVM.Guest.B1.Sig
