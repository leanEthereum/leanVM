module

public import LeanVM.Guest.Complete.BridgeB1
public import LeanVM.Guest.ExpTables

/-!
# `verify_sub`'s completeness, placed, and `main`'s target from it

`VsCompleteHypA al k bytecode seed`: `verify_sub`'s completeness on the aligned allocator's layout (`CallAtA`).
`main` calls `verify_sub(pi_0, pi_1, seed_0, seed_1, g_squares, child_fresh * xc ** DEFER_SIZE)`
from its children's loop: the exponent tables (`exponent_tables`' returned buffer, at index `qt`) and
the fresh claim's cells (in `main`'s `child_fresh`, at index `qo`) are its caller's words, below the
call's frame. So, at every frame `fp` past them and every cursor `c` past the frame's block, on a
child the guest accepts, `verify_sub` completes placed at `(fp, c)`: its own words in its frame
or from `c`, its loads and heap hints in its subtree's data, the tables or the fresh claim's cells
(`vsRegion`), on memories holding the tables and the fresh claim at `out` (what `main`'s words give),
its tree popping `childHints` stream by stream, every node exact. It claims no data and its caller
reads none of its words (`D`, `Out` trivial); it returns nothing, the fresh claim's cells being
`main`'s words that it checks.

`MainFromVsA al k`: `MainCompleteA al k` from it, this part's target.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Guest.B1

@[expose] public section

/-- The pointer to the word of index `q`: `g^q`. -/
abbrev ptrAt (q : ℕ) : E := ofK (addressOfIndex q)

/-- The exponent tables' length: `ExpTables` and `ExpWinTab` read the cells `0 ..< WIN_TAB_AT + 2^WIN_TAB_BITS`. -/
abbrev expTabLen : ℕ := winTabAt + 2 ^ winTabBits

/-- The cells `verify_sub` reads of its caller's: the exponent tables from index `qt`, the `n`
cells of the fresh claim from index `qo`. -/
def vsRegion (qt qo n : ℕ) (i : ℕ) : Prop := (qt ≤ i ∧ i < qt + expTabLen) ∨ (qo ≤ i ∧ i < qo + n)

/-- **`verify_sub` is complete, placed** (the hypothesis of `main`'s placed completeness), on
memories defined on their first `2^k` words: on a child the guest accepts, the exponent tables at
index `qt` and the fresh claim's destination at index `qo`, both below the frame `fp`, at every
cursor `c` past the frame's block, `verify_sub` completes placed at `(fp, c)`, loading from its
data and `vsRegion`, on a memory holding the tables and the fresh claim's cells, its tree popping
`Prover.childHints` stream by stream, every node exact, ending within `2^40` of its cursor below
`2^60` (as `AtEveryB`: its words then have a memory, and `main`'s end a bound). -/
def VsCompleteHypA (al : String → Bool) (k : ℕ) (bytecode : List K) (seed : Digest) : Prop :=
  ∀ (c : Child) (qt qo fp cur : ℕ), VsChildOk bytecode seed c → qt + expTabLen ≤ fp →
    qo + c.freshClaim.cells.length ≤ fp → fp + B2C.fs "verify_sub" ≤ cur →
    ∃ e, (cur < 2 ^ 60 → e ≤ cur + 2 ^ 40) ∧ CallAtA B2C.fs al B2C.cert k "verify_sub" (vsArgs seed c (ptrAt qt) (ptrAt qo)) []
      (vsRegion qt qo c.freshClaim.cells.length) (fun _ => False) (fun _ => True)
      (fun rd => VerifySub.VerifySubPre rd (vsArgs seed c (ptrAt qt) (ptrAt qo)) ∧
        ReadsAt rd (ptrAt qo) c.freshClaim.cells)
      (fun rd t => SameStreams (t.pops coreProgram rd) (Prover.childHints bytecode seed c) ∧
        t.Every (ExactAt coreProgram rd))
      (B2C.fs "verify_sub") fp cur e

/-- **`main`'s placed completeness from `verify_sub`'s**: the statement this part proves. -/
def MainFromVsA (al : String → Bool) (k : ℕ) : Prop :=
  VsCompleteHypA al k guestBytecode guestSeed → MainCompleteA al k

/-- **`verify_sub` placed as a fresh callee** (`KidsAtF`'s entered call): at the aligned base of
the cursor `cur`, past the tables and the fresh claim, its cursor after its frame. -/
theorem VsCompleteHypA.at {al : String → Bool} {k : ℕ} {bytecode : List K} {seed : Digest}
    (h : VsCompleteHypA al k bytecode seed) {c : Child} (hc : VsChildOk bytecode seed c) {qt qo cur : ℕ}
    (ht : qt + expTabLen ≤ cur) (ho : qo + c.freshClaim.cells.length ≤ cur) :
    ∃ e, (Prover.Exec.allocBase (al "verify_sub") cur + B2C.fs "verify_sub" < 2 ^ 60 →
      e ≤ Prover.Exec.allocBase (al "verify_sub") cur + B2C.fs "verify_sub" + 2 ^ 40) ∧ CallAtA B2C.fs al B2C.cert k "verify_sub" (vsArgs seed c (ptrAt qt) (ptrAt qo)) []
      (vsRegion qt qo c.freshClaim.cells.length) (fun _ => False) (fun _ => True)
      (fun rd => VerifySub.VerifySubPre rd (vsArgs seed c (ptrAt qt) (ptrAt qo)) ∧
        ReadsAt rd (ptrAt qo) c.freshClaim.cells)
      (fun rd t => SameStreams (t.pops coreProgram rd) (Prover.childHints bytecode seed c) ∧
        t.Every (ExactAt coreProgram rd))
      (B2C.fs "verify_sub") (Prover.Exec.allocBase (al "verify_sub") cur)
      (Prover.Exec.allocBase (al "verify_sub") cur + B2C.fs "verify_sub") e :=
  have hb := Memory.le_allocBase (al "verify_sub") cur
  h c qt qo _ _ hc (ht.trans hb) (ho.trans hb) le_rfl

end
end LeanVM.Guest.Complete
