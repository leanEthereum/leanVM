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

* `0`: the exponent table (`B1.ExpTables`) at the tuple's one word (`verify_sub`, `main_loop4`);
* `1` (`Check.tagNe`): the two words differ, the checker's own (a loop's `x ≠ N`);
* `oqTag kind odd pd = walkTag kind odd pd 0`: the windows `opening_queries`' inline walk
  dispatches on, at path depth `pd` (`lean_ethereum.py`): `kind` `0` `WinWalkP` on `[t, x, N]` (a
  deeper loop), `1` `WinWalk2P` on `[t, x, N]` (a level-0 loop), `2` `WinWalkP` from `1` on
  `[t, N]` (a deeper specialization's window pointers and iteration count), `3` `OqStartP` for
  `odd` on `[t, N, odd_g]` (a level-0 specialization, which assumes both `odd`'s);
  `tagOdd = walkTag 0 1 0 0`: `odd_g ∈ {1, g}` on `[odd_g]`.

* `tagTabs = 2^21`: `WinTabs` on `[tabs]`, the window table `open_stacked__L{m}` takes as an
  argument (`lean_ethereum.py`), which its decodes and grinds read.

* `lqTag n odd base d cd`, from `2^21`: `OqMainWins` on `[win_ptrs]` at `n_iters_g = g^n`, the
  windows `level_queries` hands `opening_queries` (`lean_ethereum.py`, `level_queries`), which
  `open_stacked` assumes at the rate's arm of its dispatch (`Check.selTag`, below `2^26`).

`walkSem t` is the relation of a walk tag `2 ≤ t < 2^21`, decoded by `walkKind`, `walkOdd`, `walkD`
(`walkCd` too for `lqSem`). The certificates' generator (`cli/GuestCert.lean`) writes the tags.
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
  | 0 => if walkOdd t = 1 then ws.getD 0 0 = 1 ∨ ws.getD 0 0 = gen
    else B1.WinWalkP rd (walkD t) (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0)
  | 1 => B1.WinWalk2P rd (walkD t) (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0)
  | 2 => B1.WinWalkP rd (walkD t) (ws.getD 0 0) 1 (ws.getD 1 0)
  | _ => B1.OqStartP rd (walkD t) (walkOdd t) (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0)

/-- The tag of an `opening_queries` walk relation at path depth `pd`. -/
def oqTag (kind odd pd : ℕ) : ℕ := walkTag kind odd pd 0

/-- The tag of `odd_g ∈ {1, g}`: kind `0` with `odd = 1`, which no loop's tag has. -/
def tagOdd : ℕ := walkTag 0 1 0 0

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

/-- The tag of `WinTabs` (`ExpTables.lean`), above every walk tag and below every `level_queries` tag:
`open_stacked`'s window table `tabs`, which `verify_sub` hands it. -/
def tagTabs : ℕ := 2 ^ 21

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
