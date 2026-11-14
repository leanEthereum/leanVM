/-
  LeanVM.Guest.Backend.Sound.Obl.GuestTab

  The guest's preconditions and postconditions for the analysis: the weakest the selectors need.
-/

module

public import LeanVM.Guest.Backend.Sound.Obl.Check

/-!
# The guest's table

What each guest function asks of its callers and promises them, in the analysis' terms
(`Obl.Sig`, indices into the arguments and, for `post`, into the arguments then the returns).
Every entry is what a selector of the function, or of a function it is passed to, needs and no
more; the existing certificates' `Sig.pre`, `Sig.mem`, `Sig.post` for the same functions are the
same bounds at frame offsets (`2 + i`).

* `verify_tables`: argument `9` below `g^34` (dispatched on), the word at argument `10` below
  `g^34` (`dims_g[0]`, dispatched on);
* `check_opening_terminal`: the eight words at argument `8` (`kappa_base`) below its arms;
* `child_claim_list_any`, `child_claim_list_mono`: argument `6` below `g^17`;
* `open_stacked__L0` to `__L10`: argument `0` below `g^4`;
* `walk_path__*`: the words at argument `2` (the path's bits) read by its `match`es below `g^64`;
* `list_split`: return `2` below `g^17`; `log2_ceil_in_the_exponent__L0_L34`: return `0` below
  `g^34`; `da_row_shape`: its argument `1` below `g^11` (it range-checks it);
* relation `0`, the exponent table (B1's `ExpTables`): `exponent_tables` returns one, `main_loop4`
  (compiled `__loop4`) takes it as argument `14` and `verify_sub` as argument `4`, where B1's
  bounds on `dims_g` and `kappa_base` (`vsDimsKnown0_holds`, `vsKnown_holds`) read it;
* `ext`: `verify_bus_gkr_loop0` (compiled `__loop6`), whose selector is a word its argument's GKR
  layer data bounds (B1's `GkrPar`), not a bound of the table's form.

`pows`: `g^255`, the bound of `main_loop2`'s (compiled `__loop2`) range checks.
-/

namespace LeanVM.Guest.Backend.Obl

@[expose] public section

/-- **The guest's table.** Every key is a literal: comparing strings is the costly step of
evaluating the analysis in the kernel. -/
def guestTab : Tab where
  sigs := [
    ("verify_tables", { pre := [(9, 34)], mem := [(10, 0, 34)] }),
    ("check_opening_terminal", { mem := [(8, 0, 1), (8, 1, 31), (8, 2, 31), (8, 3, 31),
      (8, 4, 31), (8, 5, 31), (8, 6, 31), (8, 7, 25)] }),
    ("child_claim_list_any", { pre := [(6, 17)] }),
    ("child_claim_list_mono", { pre := [(6, 17)] }),
    ("list_split", { post := [(3, 17)] }),
    ("log2_ceil_in_the_exponent__L0_L34", { post := [(2, 34)] }),
    ("da_row_shape", { post := [(1, 11)] }),
    ("__loop6", { ext := true }),
    ("exponent_tables", { xpost := [(0, 0)] }),
    ("__loop4", { xpre := [(14, 0)] }),
    ("verify_sub", { xpre := [(4, 0)] }),
    ("open_stacked__L0", { pre := [(0, 4)] }),
    ("open_stacked__L1", { pre := [(0, 4)] }),
    ("open_stacked__L2", { pre := [(0, 4)] }),
    ("open_stacked__L3", { pre := [(0, 4)] }),
    ("open_stacked__L4", { pre := [(0, 4)] }),
    ("open_stacked__L5", { pre := [(0, 4)] }),
    ("open_stacked__L6", { pre := [(0, 4)] }),
    ("open_stacked__L7", { pre := [(0, 4)] }),
    ("open_stacked__L8", { pre := [(0, 4)] }),
    ("open_stacked__L9", { pre := [(0, 4)] }),
    ("open_stacked__L10", { pre := [(0, 4)] }),
    ("walk_path__L6_L6", { mem := [(2, 0, 64)] }),
    ("walk_path__L6_L7", { mem := [(2, 0, 64)] }),
    ("walk_path__L12_L2", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L12_L3", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L12_L4", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L12_L5", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L12_L6", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L12_L7", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L12_L8", { mem := [(2, 0, 64), (2, 1, 64)] }),
    ("walk_path__L18_L2", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)] }),
    ("walk_path__L18_L3", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)] }),
    ("walk_path__L18_L4", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)] }),
    ("walk_path__L18_L5", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)] }),
    ("walk_path__L18_L6", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)] }),
    ("walk_path__L18_L7", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64)] }),
    ("walk_path__L24_L2", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64), (2, 3, 64)] }),
    ("walk_path__L24_L3", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64), (2, 3, 64)] }),
    ("walk_path__L24_L4", { mem := [(2, 0, 64), (2, 1, 64), (2, 2, 64), (2, 3, 64)] })]
  pows := [(9223372036854810629, 255)]

end
end LeanVM.Guest.Backend.Obl
