/-
  LeanVM.Guest.B1.Main.MainAtDefs

  `main` placed at a frame pointer: its buffers as the bump allocator places them, its oracle at
  those positions, and its callees as `Kid`s.
-/

module

public import LeanVM.Guest.B1.Main.MainWalkChk
public import LeanVM.Guest.B1.Main.MainCore
public import LeanVM.Guest.B1.Main.ExpTablesAt
public import LeanVM.Guest.Data.NameStrings

/-!
# `main`, placed: the definitions

`MainData`: what `main`'s oracle supplies besides pointers. At `fp`, `main` allocates from
`b0 = fp + fs "main"` the two claim tables, the coverage table, the byte table, the DA digests, the
children's digests, fresh and carried claims, the running counts and the deferred claim
(`mSizes`); its first callee, `exponent_tables`, sits after them, its table
after its frame. `MainData.toIn` is the oracle with those pointers. `mKids`: `main`'s other callees
in call order, each reading `main`'s words `Lin`, the conditional blocks' only when they run.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1 (Kid Returns bufL)

@[expose] public section

/-- **What `main`'s oracle supplies besides pointers.** -/
structure MainData where
  nlx : ℕ
  nxd : ℕ
  nrx : ℕ
  nls : ℕ
  nsd : ℕ
  nrs : ℕ
  nc : ℕ
  nd : ℕ
  pick : ℕ
  seed : Digest
  xd : Digest
  sd : Digest
  sdg : Digest
  daR : List E
  dap : Digest
  leaf : E

variable (d : MainData)

/-- The leanXMSS region's and the leanSPHINCS region's slots. -/
def MainData.X : ℕ := d.nlx + d.nxd
def MainData.Y : ℕ := d.nls + d.nsd
def MainData.T : ℕ := d.X + d.Y

/-- `main`'s `HeapBuf` sizes, in allocation order. -/
def mSizes : List ℕ :=
  [4 * d.X, 4 * d.Y, d.T, 256, 2 * (d.nc + 1), 2 * d.nc, 24 * d.nc, 24 * d.nc, d.nc + 1, 24]

/-- The buffers' first words from `b0`. -/
def mPos (b0 : ℕ) : List ℕ := Memory.bases b0 (mSizes d)

/-- `main`'s first callee's frame. -/
def mK0 (fs : String → ℕ) (fp : ℕ) : ℕ := fp + fs "main" + (mSizes d).sum

/-- **`main`'s oracle at `fp`.** -/
def MainData.toIn (fs : String → ℕ) (fp : ℕ) : MainIn :=
  let p := mPos d (fp + fs "main")
  let e := etB fs (mK0 d fs fp)
  { nlx := d.nlx, nxd := d.nxd, nrx := d.nrx, nls := d.nls, nsd := d.nsd, nrs := d.nrs, nc := d.nc,
    nd := d.nd, pick := d.pick, seed := d.seed, et := gen ^ e,
    a77 := gen ^ p.getD 0 0, a80 := gen ^ p.getD 1 0, a117 := gen ^ p.getD 2 0,
    a119 := gen ^ p.getD 3 0, aDa := gen ^ p.getD 4 0,
    a394 := gen ^ p.getD 5 0, a400 := gen ^ p.getD 6 0, a406 := gen ^ p.getD 7 0,
    a409 := gen ^ p.getD 8 0, a417 := gen ^ p.getD 9 0, xd := d.xd, sd := d.sd,
    sdg := d.sdg, daR := d.daR, dap := d.dap, leaf := d.leaf }

/-- `exponent_tables`' table, placed. -/
def etL (fs : String → ℕ) (fp : ℕ) : B1.Main.Layout := [(etB fs (mK0 d fs fp), expTabAllWords)]

/-- **`main`'s callees after `exponent_tables`**, in call order, reading `Lin`. -/
def mKids (m : MainIn) (Lin : B1.Main.Layout) : List Kid :=
  let one : E := 1
  let X := m.nlx + m.nxd
  let Y := m.nls + m.nsd
  [⟨"claim_list_digest", true, [m.a77, gen ^ m.nlx], Lin, Returns (digestCells m.xd)⟩,
    ⟨"claim_list_digest", true, [m.a80, gen ^ m.nls], Lin, Returns (digestCells m.sd)⟩,
    ⟨name% «main_loop0», decide (m.nxd ≠ 0), [one, gen ^ m.nxd, m.a77, gen ^ m.nlx], Lin,
        Returns []⟩,
    ⟨name% «main_loop1», decide (m.nsd ≠ 0), [one, gen ^ m.nsd, m.a80, gen ^ m.nls], Lin,
        Returns []⟩,
    ⟨name% «main_loop2», decide (m.nrx ≠ 0), [one, gen ^ m.nrx, gen ^ X, m.a117,
        m.a77] ++ lxTagWords, Lin,
      Returns []⟩,
    ⟨name% «main_loop3», decide (m.nrs ≠ 0), [one, gen ^ m.nrs, gen ^ Y, m.a117 * gen ^ X,
        gen ^ m.nrx,
      m.a80, m.a119], Lin, Returns []⟩] ++
  (if m.nd = 1 then [⟨"da_verify", true, [m.et], Lin, Returns m.daR⟩] else []) ++
  [⟨name% «main_loop4», decide (m.nc ≠ 0), [one, gen ^ m.nc, m.a409, m.a77, m.a117, gen ^ X, m.a80,
    m.a117 * gen ^ X, gen ^ Y, m.a406, m.aDa, (digestHalves m.seed).1, (digestHalves m.seed).2,
    m.a394, m.et, m.a400], Lin, Returns []⟩] ++
  (if m.nc = 0 then [] else
    [⟨"aggregate_claims", true, [gen ^ m.nc, m.a394, m.a400, m.a406, m.a417,
      m.et * word 133823759239872512 0], Lin, Returns []⟩]) ++
  [⟨"statement_digest", true, [(digestHalves m.seed).1, (digestHalves m.seed).2,
    (digestHalves m.xd).1, (digestHalves m.xd).2, (digestHalves m.sd).1, (digestHalves m.sd).2,
    (digestHalves m.dap).1, (digestHalves m.dap).2, m.a417], Lin, Returns (digestCells m.sdg)⟩]

end
end LeanVM.Guest.B1.Main
