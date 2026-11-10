/-
  LeanVM.Guest.WalkTags

  The tags of the guest's semantic relations (`Glob.sem`), and the relations of the windowed
  Merkle walk's tags.
-/

module

public import LeanVM.Guest.WalkWindows

/-!
# The tags of the semantic relations

A function's precondition names tuples of its frame cells in relations by tag (`Check.Sig.sem`):

* `0`: the exponent table (`B1.ExpTables`) at the tuple's one word (`verify_sub`, `__loop4`);
* `1` (`Check.tagNe`): the two words differ, the checker's own (a loop's `x ≠ N`);
* `walkTag kind odd d cd`: the windows `opening_queries`' walk dispatches on, specialization
  `(odd, base, depth d, cap_depth cd)` (`lean_ethereum.py:1393-1415` at `40f877dc`): `kind` `0`
  `WinWalk` on `[t, x, N]` (a deeper loop, `odd = 0`), `1` `WinWalk2` on `[t, x, N]` (a level-0 loop),
  `2 + base` `OqMainWins` on `[t, N]` (the function's window pointers and iteration count);
  `winsTag d cd = walkTag 0 1 d cd`: `WinsAt` on `[wins]`, the windows `walk_path__L{pd}_L{cd}`
  dispatches on (`lean_ethereum.py:1308-1343` at `40f877dc`), which its callers hand it.

* `tagTabs = 2^21`: `WinTabs` on `[tabs]`, the window table `open_stacked__L{m}` takes as an
  argument (`lean_ethereum.py:1530`), which its decodes and grinds read.

* `tagGkr = 2^20`: `GkrPar` on `[layers, x, start_g, k_mod_next]`, `verify_bus_gkr`'s
  radix-four layer loop `__loop6` (`lean_ethereum.py:2006-2089`): the parity word
  `layer[g^LAYER_PARITY]` of layer `x` it dispatches on, and the table `k_mod_next` that steps it.

`walkSem t` is the relation of a walk tag `2 ≤ t < tagGkr`, decoded by `walkKind`, `walkOdd`, `walkD`,
`walkCd`. The certificates' generator (`cli/GuestCert.lean`) writes the tags.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The tag of a walk relation, `kind < 4`, `cd < 64`. -/
def walkTag (kind odd d cd : ℕ) : ℕ := 2 + kind + 4 * (odd + 2 * (cd + 64 * d))

/-- A walk tag's kind. -/
def walkKind (t : ℕ) : ℕ := (t - 2) % 4

/-- A walk tag's `odd`. -/
def walkOdd (t : ℕ) : ℕ := (t - 2) / 4 % 2

/-- A walk tag's `cap_depth`. -/
def walkCd (t : ℕ) : ℕ := (t - 2) / 8 % 64

/-- A walk tag's depth. -/
def walkD (t : ℕ) : ℕ := (t - 2) / 512

/-- **The relation of walk tag `t`** on the words `ws`. -/
def walkSem (t : ℕ) (rd : Reader) (ws : List E) : Prop :=
  match walkKind t with
  | 0 => if walkOdd t = 1 then B1.WinsAt rd (walkD t) (walkCd t) (ws.getD 0 0)
    else B1.WinWalk rd (walkD t) (walkCd t) (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0)
  | 1 => B1.WinWalk2 rd (walkD t) (walkCd t) (walkOdd t) (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0)
  | k => B1.OqMainWins rd (walkD t) (walkCd t) (walkOdd t) (k - 2) (ws.getD 0 0) (ws.getD 1 0)

/-- The tag of `walk_path__L{pd}_L{cd}`'s windows (`WinsAt` on its `wins`), `d = pd + cd`: kind `0`
with `odd = 1`, which no deeper loop has (a deeper loop's specialization has `odd = 0`). -/
def winsTag (d cd : ℕ) : ℕ := walkTag 0 1 d cd

/-- The tag of `GkrPar`, above every walk tag. -/
def tagGkr : ℕ := 2 ^ 20

/-- The tag of `WinTabs` (`ExpTables.lean`), above `tagGkr`: `open_stacked`'s window table `tabs`,
which `verify_sub` hands it. -/
def tagTabs : ℕ := 2 ^ 21

/-- **`__loop6`'s parity obligation** on `layers`, the iteration `x`, `start_g` and `k_mod_next`:
`k_mod_next[g^r]`, `r < 4`, if read, is `g^e`, `e < 4`; and the parity word `layer[g^12]` of
layer `x`, `layer = layers·(x²·start_g)^13` (`LAYER_SLOTS = 13`, `LAYER_PARITY = 12`), if read,
is `g^e`, `e < 4`. -/
def GkrPar (rd : Reader) (layers x startG kmn : E) : Prop :=
  (∀ r < 4, ∀ v, LoadHolds rd kmn r v → ∃ e < 4, v = ofK (addressOfIndex e)) ∧
    ∀ p, LoadHolds rd (layers * (x * x * startG) ^ 13) 12 p → ∃ e < 4, p = ofK (addressOfIndex e)

theorem walkTag_decode {kind odd d cd : ℕ} (hk : kind < 4) (ho : odd < 2) (hc : cd < 64) :
    walkKind (walkTag kind odd d cd) = kind ∧ walkOdd (walkTag kind odd d cd) = odd ∧
      walkD (walkTag kind odd d cd) = d ∧ walkCd (walkTag kind odd d cd) = cd := by
  unfold walkKind walkOdd walkD walkCd walkTag
  refine ⟨by omega, by omega, by omega, by omega⟩

end
end LeanVM.Guest
