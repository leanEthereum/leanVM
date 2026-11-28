/-
  LeanVM.Guest.B1.VsC.LinkCalleesA

  The placed completeness statements of `verify_sub`'s link callees left to prove.
-/

module

public import LeanVM.Guest.B1.VsC.LinkCallees
public import LeanVM.Guest.B1.VsC.Vsc8CalleesA

/-!
# `verify_sub`'s link callees, placed: the statements

`LinkCallees.lean`'s layout-free statements in the placed form of `Vsc8CalleesA.lean`: `CallAtA` at
the callee's cursor right after its frame (what `KidsAtF` hands an entered call), the caller's
arrays below the frame (`PtrsBelow`), loads in them (`ptrRegion`) or the callee's own data, popping
nothing, every node exact (`PostQuiet`). The stream words a chain of rounds reads from `cur` are
`nw` long, `nw` given by the cursor after the chain; the cursor is not `0` (at `0` the words a chain
reads all sit at the one word `0`, which no region names, while `nw = 0` makes the cursor's run empty).

* `SqueezePackedCompleteA`: `squeeze_packed` on the capacity and `g^p`, `p < 64`, the packed draw's
  cells at `out`, returns the capacity after it.
* `LinkRoundsCompleteA nt bits name`: `link_rounds__L{nt}_L{bits}` on the state `fs0..fs4, cursor,
  claim`, a chain of `l.length < 64` rounds, the challenges at `point`, returns the state after it.
* `LinkRowSideCompleteA d b1 b2 name`: `link_row_side__L{d}`, the rows' chain then the pointer
  columns' (`6` rounds), each reading its own run of stream words.
* `LinkTerminalCompleteA w name`: `link_terminal__L{w}` on the summand's inputs, the claim the
  summand plus `rest`, returns `0`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Protocol.Verifier

@[expose] public section

/-- **`squeeze_packed` completes placed.** -/
def SqueezePackedCompleteA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) : Prop :=
  ∀ (f0 f1 f2 f3 f4 out : E) (p fp : ℕ), p < 64 →
    PtrsBelow [(out, (pkSqueeze p [f0, f1, f2, f3, f4]).1.length)] fp →
    ∃ e, CallAtA fs al cert k "squeeze_packed" [f0, f1, f2, f3, f4, out, gen ^ p]
      (pkSqueeze p [f0, f1, f2, f3, f4]).2
      (ptrRegion [(out, (pkSqueeze p [f0, f1, f2, f3, f4]).1.length)]) (fun _ => False) (fun _ => True)
      (fun rd ↦ ReadsAt rd out (pkSqueeze p [f0, f1, f2, f3, f4]).1)
      PostQuiet (fs "squeeze_packed") fp (fp + fs "squeeze_packed") e

/-- The arrays a chain of `n` rounds reads of its caller's: `nw` stream words at `cur`, the `n`
challenges at `point`, the window tables at `tabs`. -/
def lrArrays (cur point tabs : E) (nw n : ℕ) : List (E × ℕ) :=
  [(cur, nw), (point, n), (tabs, 2 ^ winTabBits)]

/-- **`link_rounds__L{nt}_L{bits}` completes placed.** -/
def LinkRoundsCompleteA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k nt bits : ℕ)
    (name : String) : Prop :=
  ∀ (f0 f1 f2 f3 f4 cur cl point tabs : E) (l : List (E × RSt)) (nw fp : ℕ), l.length < 64 → cur ≠ 0 →
    (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l).cur = cur * gen ^ nw →
    PtrsBelow (lrArrays cur point tabs nw l.length) fp →
    ∃ e, CallAtA fs al cert k name [f0, f1, f2, f3, f4, cur, cl, point, gen ^ l.length, tabs]
      (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l).cells
      (ptrRegion (lrArrays cur point tabs nw l.length)) (fun _ => False) (fun _ => True)
      (fun rd ↦ (bits ≠ 0 → WinTabs rd tabs) ∧ RoundChain rd nt bits ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l ∧
        ReadsAt rd point (l.map Prod.fst))
      PostQuiet (fs name) fp (fp + fs name) e

/-- The arrays a row side reads of its caller's: `nw1` stream words at `cur` and `nw2` at `cur1`
(the rows' chain's and the columns'), the rows' `n` challenges at `chi`, the columns' `6` at `qp`,
the window tables at `tabs`. -/
def lrsArrays (cur cur1 chi qp tabs : E) (nw1 nw2 n : ℕ) : List (E × ℕ) :=
  [(cur, nw1), (cur1, nw2), (chi, n), (qp, 6), (tabs, 2 ^ winTabBits)]

/-- **`link_row_side__L{d}` completes placed.** -/
def LinkRowSideCompleteA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k d b1 b2 : ℕ)
    (name : String) : Prop :=
  ∀ (f0 f1 f2 f3 f4 cur cl chi qp tabs : E) (l1 l2 : List (E × RSt)) (nw1 nw2 fp : ℕ), l1.length < 64 →
    l2.length = 6 → cur ≠ 0 →
    (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cur = cur * gen ^ nw1 →
    (chainLast (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2).cur =
      (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cur * gen ^ nw2 →
    PtrsBelow (lrsArrays cur (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cur chi qp tabs nw1 nw2 l1.length) fp →
    ∃ e, CallAtA fs al cert k name [f0, f1, f2, f3, f4, cur, cl, chi, qp, gen ^ l1.length, tabs]
      (chainLast (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2).cells
      (ptrRegion (lrsArrays cur (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1).cur chi qp tabs nw1 nw2 l1.length))
      (fun _ => False) (fun _ => True)
      (fun rd ↦ WinTabs rd tabs ∧ RoundChain rd (d + 1) b1 ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1 ∧
        RoundChain rd d b2 (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2 ∧
        ReadsAt rd chi (l1.map Prod.fst) ∧ ReadsAt rd qp (l2.map Prod.fst))
      PostQuiet (fs name) fp (fp + fs name) e

/-- The arrays `link_terminal` reads of its caller's: the index point at `r`, the slices at
`sent·g^80`, the shift coefficients at `shifts`, the chunks' `ν` at `nu`. -/
def ltArrays (r sent shifts nu : E) (nr nnu : ℕ) : List (E × ℕ) :=
  [(r, nr), (sent * gen ^ 80, 64), (shifts, 12), (nu, nnu)]

/-- **`link_terminal__L{w}` completes placed** at the chunking `Chunks.new w = some c`. -/
def LinkTerminalCompleteA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k w : ℕ)
    (name : String) : Prop :=
  ∀ c, Chunks.new w = some c →
    ∀ (r sent coef shifts certW nu rest claim : E) (rs sl shs nus : List E) (fp : ℕ), rs.length = c.width →
      sl.length = 64 → shs.length = 12 → nus.length = c.d →
      claim = (Functionals.new c rs 12).summand coef shs ((Functionals.new c rs 12).values c sl)
        (nus.map (certW * ·)) + rest →
      PtrsBelow (ltArrays r sent shifts nu rs.length nus.length) fp →
      ∃ e, CallAtA fs al cert k name [r, sent, coef, shifts, certW, nu, rest, claim] [0]
        (ptrRegion (ltArrays r sent shifts nu rs.length nus.length)) (fun _ => False) (fun _ => True)
        (fun rd ↦ ReadsAt rd r rs ∧ (∀ k < 64, LoadHolds rd sent (80 + k) (sl.getD k 0)) ∧
          ReadsAt rd shifts shs ∧ ReadsAt rd nu nus)
        PostQuiet (fs name) fp (fp + fs name) e

/-- **The placed link callees `verify_sub` enters** (`vsLinkCalleesA_complete`): `link_rounds` at the index
side's `(1, 0)` and the row sides' five specializations, `squeeze_packed`, `link_terminal__L{w}`.
The row sides follow (`VsLinkCalleesA.row_side`, `RowSideA.lean`). -/
structure VsLinkCalleesA (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) : Prop where
  rounds_L1_L0 : LinkRoundsCompleteA fs al cert k 1 0 "link_rounds__L1_L0"
  rounds_L6_L0 : LinkRoundsCompleteA fs al cert k 6 0 "link_rounds__L6_L0"
  rounds_L7_L0 : LinkRoundsCompleteA fs al cert k 7 0 "link_rounds__L7_L0"
  rounds_L8_L1 : LinkRoundsCompleteA fs al cert k 8 1 "link_rounds__L8_L1"
  rounds_L9_L1 : LinkRoundsCompleteA fs al cert k 9 1 "link_rounds__L9_L1"
  rounds_L10_L1 : LinkRoundsCompleteA fs al cert k 10 1 "link_rounds__L10_L1"
  squeeze_packed : SqueezePackedCompleteA fs al cert k
  terminal : ∀ w, 19 ≤ w → w ≤ 24 → LinkTerminalCompleteA fs al cert k w (ltNames.getD (w - 19) "")

end
end LeanVM.Guest.B1.VsC
