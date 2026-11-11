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

* `tagGkr = 2^20`: `GkrPar` on `[layers, x, depth_shift, g_bus_mu, k_mod_next]`, `verify_bus_gkr`'s
  radix-four layer loop `__loop6` (`lean_ethereum.py:1868-1934` at `40f877dc`): the parity word
  `layer[g^LAYER_PARITY]` of layer `x` it dispatches on, and the table `k_mod_next` that steps it.
* `lqTag n odd base d cd`, from `2^21`: `OqMainWins` on `[win_ptrs]` at `n_iters_g = g^n`, the
  windows `level_queries` hands `opening_queries` (`lean_ethereum.py`, `level_queries`), which
  `open_stacked` assumes at the rate's arm of its dispatch (`Check.selTag`, below `2^26`).

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

/-- The tag of `level_queries`' windows: the walk `walkTag (2 + base) odd d cd` (`OqMainWins`) on
`[t]` at `N = g^n`; with `d < 64` the walk tag is below `2^16`, and with `n < 992` the tag below
`2^26`. -/
def lqTag (n odd base d cd : ℕ) : ℕ := 2 ^ 21 + walkTag (2 + base) odd d cd + 2 ^ 16 * n

/-- A `level_queries` tag's walk tag. -/
def lqWalk (t : ℕ) : ℕ := (t - 2 ^ 21) % 2 ^ 16

/-- A `level_queries` tag's iteration count. -/
def lqN (t : ℕ) : ℕ := (t - 2 ^ 21) / 2 ^ 16

/-- **The relation of a `level_queries` tag** `t ≥ 2^21` on the words `ws`: its walk's
`OqMainWins` at `g^n`. -/
def lqSem (t : ℕ) (rd : Reader) (ws : List E) : Prop :=
  B1.OqMainWins rd (walkD (lqWalk t)) (walkCd (lqWalk t)) (walkOdd (lqWalk t)) (walkKind (lqWalk t) - 2)
    (ws.getD 0 0) (gen ^ lqN t)

/-- **`__loop6`'s parity obligation** on `layers`, the iteration `x`, the depth shift table, `g_bus_mu`
and `k_mod_next`: `k_mod_next[g^r]`, `r < 4`, if read, is `g^e`, `e < 4`; and the parity word
`layer[g^12]` of layer `x`, `layer = layers·(x²·depth_shift[g_bus_mu])^17` (`LAYER_SLOTS = 17`,
`LAYER_PARITY = 12`), if read, is `g^e`, `e < 4`. -/
def GkrPar (rd : Reader) (layers x shift gbm kmn : E) : Prop :=
  (∀ r < 4, ∀ v, LoadHolds rd kmn r v → ∃ e < 4, v = ofK (addressOfIndex e)) ∧
    ∀ s, LoadHolds rd (shift * gbm) 0 s → ∀ p, LoadHolds rd (layers * (x * x * s) ^ 17) 12 p →
      ∃ e < 4, p = ofK (addressOfIndex e)

theorem walkTag_lt {kind odd d cd : ℕ} (hk : kind < 4) (ho : odd < 2) (hc : cd < 64) (hd : d < 64) :
    walkTag kind odd d cd < 2 ^ 16 := by
  unfold walkTag; omega

theorem lqTag_decode {n odd base d cd : ℕ} (hb : base < 2) (ho : odd < 2) (hc : cd < 64) (hd : d < 64) :
    lqWalk (lqTag n odd base d cd) = walkTag (2 + base) odd d cd ∧ lqN (lqTag n odd base d cd) = n := by
  have h := walkTag_lt (kind := 2 + base) (by omega) ho hc hd
  unfold lqWalk lqN lqTag
  refine ⟨by omega, by omega⟩

theorem walkTag_decode {kind odd d cd : ℕ} (hk : kind < 4) (ho : odd < 2) (hc : cd < 64) :
    walkKind (walkTag kind odd d cd) = kind ∧ walkOdd (walkTag kind odd d cd) = odd ∧
      walkD (walkTag kind odd d cd) = d ∧ walkCd (walkTag kind odd d cd) = cd := by
  unfold walkKind walkOdd walkD walkCd walkTag
  refine ⟨by omega, by omega, by omega, by omega⟩

end
end LeanVM.Guest
