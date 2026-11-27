/-
  LeanVM.Guest.CoreMode.PairLit

  The pairing's context with its tries stated once, as values the kernel checks, for a long
  function's windows.
-/

module

public import LeanVM.Guest.CoreMode.PairDefs

/-!
# Contexts with stated tries

Each window of a long function's pairing (`winOkHS`) starts by building its context's tries from
lists: the cells, the fixed cells, the call sites, the table jumps, the callees (`AlignCtx.ofPacked`),
the heap certificate's reads (`HCert.readT`) and the oracle (`offsT`). The kernel shares nothing
between declarations, so every window builds them again. The function's `ALit` and `Lit` modules
(`scripts/core-mode/pair.py`) state each trie once as a value (`kernel_lit`) and the context with
them (`AlignCtx.withTries`, `PairCtx.ofH_eq`); a window rewrites its context to that one and reads
the tries without building them, and so does a long loop's code window (`core.py`'s `CLit`). Nothing
is proved of the values: the kernel checks each against the term it was computed from.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest.Exec (Trie)

@[expose] public section

/-- `X` with its tries `loc`, `stat`, `sites`, `arms` and `ents` replaced. -/
def AlignCtx.withTries (X : AlignCtx) (loc : Trie ℕ) (stat : Trie B2C.PC) (sites : Trie B2C.Site)
    (arms : Trie (ℕ × ℕ)) (ents : Trie String) : AlignCtx :=
  { X with loc, stat, sites, arms, ents }

end

public section

/-- **A context with its tries stated**: equal to `X` when each stated trie is `X`'s. -/
theorem AlignCtx.eq_withTries {X : AlignCtx} {loc : Trie ℕ} {stat : Trie B2C.PC} {sites : Trie B2C.Site}
    {arms : Trie (ℕ × ℕ)} {ents : Trie String} (h1 : X.loc = loc) (h2 : X.stat = stat) (h3 : X.sites = sites)
    (h4 : X.arms = arms) (h5 : X.ents = ents) : X = X.withTries loc stat sites arms ents := by
  subst h1 h2 h3 h4 h5; rfl

end

end LeanVM.Guest.Bridge

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest.Bridge
open LeanVM.Guest.Exec (Trie)

public section

/-- **The pairing's context with its tries stated**. -/
theorem PairCtx.ofH_eq {X X' : AlignCtx} {H : HCert} {O S O' S' : Trie Unit}
    {R : Trie (List (ℕ × ℕ × Wit))} (hX : X = X') (hR : H.readT = R) (hO : O = O') (hS : S = S') :
    PairCtx.ofH X H O S = ⟨X', R, O', S'⟩ := by
  subst hX hR hO hS; rfl

end

end LeanVM.Guest.CoreMode
