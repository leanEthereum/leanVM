module

public import LeanVM.Guest.Complete.AggFree
public import LeanVM.Guest.B1.Bits.Tables
public import LeanVM.Guest.B1.Da.PaddingComplete
public import LeanVM.Guest.B1.Da.LevelsComplete
import LeanVM.Guest.CoreRef
import LeanVM.Guest.Data.Consts

/-!
# `main`'s callees free of witness hints, complete

`exponent_tables`, `da_padding` and `da_levels` at its two depths have no witness hint in their
subtrees and every computed hint pinned (kernel evaluation), so each completes where its relation
holds (`callCompletes_free`): `exponent_tables` returning a pointer to the tables the memory holds
(`exponent_tables_holds`), `da_padding` on a row count within the cap (`da_padding_complete`),
`da_levels` on a tree of honest levels (`da_levels_complete`). A buffer a callee returns is the
caller's words: these take none of their own.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem et_free : NoWitG "exponent_tables" ∧ ExactFreeG "exponent_tables" :=
  free_of (by decide +kernel : freeAt "exponent_tables" idx% «exponent_tables» = true)

set_option maxRecDepth 100000 in
theorem da_padding_free : NoWitG "da_padding" ∧ ExactFreeG "da_padding" :=
  free_of (by decide +kernel : freeAt "da_padding" idx% «da_padding» = true)

set_option maxRecDepth 100000 in
theorem da_levels_free {d : ℕ} (hd : DlDepth d) :
    NoWitG (daLevelsName d) ∧ ExactFreeG (daLevelsName d) := by
  rcases hd with rfl | rfl
  · exact free_of (by decide +kernel : freeAt (daLevelsName (guest_const% DA_LOG_MAX_ROWS))
      idx% «da_levels__L32_L5» = true)
  · exact free_of (by decide +kernel : freeAt (daLevelsName (guest_const% DA_BLOCK_BITS))
      idx% «da_levels__L128_L7» = true)

/-- **`exponent_tables` completes** returning `q` where the memory holds the tables at `q`. -/
theorem exponent_tables_completes (hwf : coreProgram.Wf) (k : ℕ) (q : E) :
    CallCompletes k "exponent_tables" [] [q] (fun rd => ExpTables rd q ∧ ExpWinTab rd q) FreePost :=
  callCompletes_free hwf et_free.1 et_free.2 fun rd _ hp => (exponent_tables_holds rd [] [q]).mpr hp

/-- **`da_padding` completes** on `r` rows within the cap, on memories defined below `2^16`. -/
theorem da_padding_completes (hwf : coreProgram.Wf) {k : ℕ} (hk : 16 ≤ k) {r : ℕ} (h1 : 1 ≤ r)
    (h2 : r ≤ LeanDa.maxRows) :
    CallCompletes k "da_padding" [gen ^ r] [gen ^ (LeanDa.maxRows - r)] (fun _ => True) FreePost :=
  callCompletes_free hwf da_padding_free.1 da_padding_free.2 fun rd hl _ =>
    da_padding_complete rd (hl.mono hk) r h1 h2

/-- **`da_levels` completes** at its depths, on a tree of honest levels, returning the root. -/
theorem da_levels_completes (hwf : coreProgram.Wf) (k : ℕ) {d : ℕ} (hd : DlDepth d) (tree : E)
    (leaves : List (E × E)) (hl : leaves.length = 2 ^ d) :
    CallCompletes k (daLevelsName d) [tree] [(cellRoot d leaves).1, (cellRoot d leaves).2]
      (fun rd => TreeMem rd tree d leaves) FreePost :=
  callCompletes_free hwf (da_levels_free hd).1 (da_levels_free hd).2 fun rd _ hp =>
    da_levels_complete d hd rd tree leaves hl hp

end
end LeanVM.Guest.Complete
