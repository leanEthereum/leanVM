/-
  LeanVM.Guest.B1.VsC.VsHonBw

  `verify_sub`'s honest buffers and return rule, from the child's native run.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatLay

/-!
# The honest buffers and returns

From one native run `N` of the accepted child (`natOpen`), **`VsCtx.honBw x N`** is the own buffers' words
(`vsAllocIdx` order, each of its `vsAllocSz` size) and **`VsCtx.honRetR x N bp bp1`** the callees' return rule, a
constant rule (`σ` unused) built from `x`'s placement and `N` only, never from `x.bw`, `x.ret`, `x.w`: `bp`, `bp1` are
`open_stacked`'s point buffers (`openCallEnd_nat`'s). **`VsCtx.honCtx x N ec bp bp1`** is `x` with them, `ex := []`
and the ends `ec`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Link LeanVM.Guest.B1.Stack
open LeanVM.Guest.B1.Link (pkSqueeze)
open LeanVM.Prover.Exec (allocBase)
open LeanVM.Guest.B1.VerifySub (qkeccakVarsCap keccakTauMin keccakTauMax)

@[expose] public section

attribute [local semireducible] VsCtx.lay

/-- The Keccak reduction's output claim's point (`N.outs`' one claim). -/
def NatOpen.op (N : NatOpen) : List E := (N.outs.headD ⟨0, [], 0⟩).point

/-- The Keccak reduction's output claim's value. -/
def NatOpen.kw (N : NatOpen) : E := (N.outs.headD ⟨0, [], 0⟩).value

/-- `table_size`'s honest returns, table `t`'s three from `tsRet t`. -/
def tsRuleV (h Rr : ℕ → ℕ) (i : ℕ) : E :=
  match (List.range 6).find? (fun t => decide (tsRet t ≤ i ∧ i < tsRet t + 3)) with
  | some t => [gen ^ Rr t, tsLeadW (Rr t) (h t), tsRestW (Rr t) (h t)].getD (i - tsRet t) 0
  | none => 0

namespace VsCtx

variable (x : VsCtx)

/-- The announced rate. -/
noncomputable def rate : ℕ := (announcedLayoutAndRate guestBytecode x.c.proof.stream |>.map Prod.snd).getD 0

/-- `.n 10`'s honest words: `opening_message`'s first return, `squeeze_packed`'s draws, zeros to `153`. -/
noncomputable def honB4 : List E :=
  padTo 153 (x.omN.getD 0 0 ::
    (pkSqueeze x.pk [x.omN.getD 2 0, x.omN.getD 3 0, x.omN.getD 4 0, x.omN.getD 5 0, x.omN.getD 6 0]).1)

/-- **The honest buffers**, `vsAllocIdx` order: `0` the heights' counts, `1` the tables' bits (`26` words each), `2`
the cycles' bits, `3` the link's shape, `4` `.n 10`, `5 … 12` the link's (`BwNat`), `8` the fresh claim's values,
`13` `.n 19` (the overlay's), `14` the Keccak claim's point then its input point, `15` the Keccak slices, `16` the
out-of-domain point, `17` the stream's word `11`, `18` the padded stream, `19` the rows, `20` the memory's and the
heights' powers, `21 … 23` the ring switch's map challenges, coefficients and merged slices. -/
noncomputable def honBw (N : NatOpen) : List (List E) :=
  [x.lay.tableLogHeights.map Prover.count,
   (List.range 6).flatMap (fun t => padTo 26 (tsBitsW (x.rows t) (x.hg t))),
   cbL (x.rows 0 + x.rows 1 + x.rows 2 + x.rows 3 + x.rows 4 + x.rows 5),
   vsLinkShape x.lay,
   x.honB4,
   eqLevels (ph7Rs x.honB4) 4,
   padTo 24 (N.L.r x.lay x.nF),
   padTo 25 ((List.range (x.wdS + 1)).map (Link.belowE (N.L.r x.lay x.nF))),
   x.c.freshClaim.values,
   padTo 24 (N.L.chi x.lay x.nF),
   N.L.qPoint x.lay x.nF,
   eqLevels ((N.L.qPoint x.lay x.nF).take 6) 6,
   padTo 25 ((List.range (x.nS + 1)).map (Link.belowE (N.L.chi x.lay x.nF))),
   List.replicate 12 0,
   padTo qkeccakVarsCap N.op ++ padTo qkeccakVarsCap N.kp,
   N.ks,
   padTo 30 (natOodZ x.seed x.c x.lay.stackLog),
   [(padStream x.c.proof.stream).getD 11 0],
   padStream x.c.proof.stream,
   rowsW x.rows,
   1 :: gen ^ x.lay.logMemory :: heightsW x.hg,
   ringF N.S ++ ringG N.S,
   ringCoefficients (ringF N.S) (ringG N.S),
   rsW N.ks N.L.msg (ringRho N.S)]

/-- `x` with the honest buffers (what `honRet`, `natBm` and the table points read). -/
noncomputable def withBw (N : NatOpen) : VsCtx := { x with bw := x.honBw N }

/-- The five later `table_point`s' honest returns, table `t + 1`'s three from `tpD (t + 1) + 5`. -/
noncomputable def tpRuleV (y : VsCtx) (i : ℕ) : E :=
  match (List.range 5).find? (fun t => decide (tpD (t + 1) + 5 ≤ i ∧ i < tpD (t + 1) + 8)) with
  | some t =>
    [(y.bw.getD 4 []).getD (t + 1) 0 * Link.tpTotalG (((y.bw.getD 4 []).drop 89).take (y.hgS (t + 1)))
        ((y.bw.getD 9 []).take (y.hgS (t + 1))) (((y.bw.getD 1 []).drop (26 * (t + 1))).take (y.hgS (t + 1)))
        ((y.bw.getD 1 []).getD (26 * (t + 1) + y.hgS (t + 1)) 0) (y.hgS (t + 1)),
      1 + (1 + (y.bw.getD 1 []).getD (26 * (t + 1) + y.hgS (t + 1)) 0) *
        Link.tpPad (((y.bw.getD 1 []).drop (26 * (t + 1))).take (y.hgS (t + 1)))
          ((y.bw.getD 9 []).take (y.hgS (t + 1))),
      Link.tpFullAt (((y.bw.getD 4 []).drop 89).take (y.hgS (t + 1))) ((y.bw.getD 9 []).take (y.hgS (t + 1)))
        (y.hgS (t + 1))].getD (i - (tpD (t + 1) + 5)) 0
  | none => 0

/-- `open_stacked`'s returns' stream cursor: past the packed message, the Keccak reduction's words, the ring grind's
nonce and the opening's words. -/
noncomputable def honIe (N : NatOpen) : ℕ := (x.withBw N).natBm N.L + 144 + N.xs.length + 1 + N.ws.length

/-- The honest returns off `honRet`'s indices. -/
noncomputable def honRetO (N : NatOpen) (bp bp1 i : ℕ) : E :=
  if i = 94 then gen ^ x.rate
  else if i = 101 then gen ^ x.lay.logMemory
  else if 145 ≤ i ∧ i < 227 then tsRuleV x.hg x.rows i
  else if i = 484 then gen ^ chunkCount (widthOf x.lay)
  else if i = 485 then gen ^ x.lay.stackLog
  else if i = 486 then ptrAt (csOffsAt (x.fpc + B2C.fs "certify_stack"))
  else if i = 487 then ptrAt (csOffsAt (x.fpc + B2C.fs "certify_stack") + 52)
  else if 566 ≤ i ∧ i < 571 then x.spfN.getD (i - 566) 0
  else if 573 ≤ i ∧ i < 581 then x.omN.getD (i - 573) 0
  else if 680 ≤ i ∧ i < 685 then
    (pkSqueeze x.pk [x.omN.getD 2 0, x.omN.getD 3 0, x.omN.getD 4 0, x.omN.getD 5 0, x.omN.getD 6 0]).2.getD (i - 680) 0
  else if 1400 ≤ i ∧ i < 1890 then tpRuleV (x.withBw N) i
  else if i = 2894 then 0
  else if 2915 ≤ i ∧ i < 2922 then
    (vkRets N.s' (ptrAt ((x.withBw N).natBm N.L + 144)) N.xs.length N.kw).getD (i - 2915) 0
  else if i = 3810 then ringTarget (rsW N.ks N.L.msg (ringRho N.S)) (ringF N.S) (ringG N.S)
  else if 3991 ≤ i ∧ i < 3997 then (osRets N.wE bp bp1 (x.honIe N)).getD (i - 3991) 0
  else 0

/-- **The honest return rule**: `honRet`'s link returns at the honest buffers, `honRetO` elsewhere. -/
noncomputable def honRetR (N : NatOpen) (bp bp1 : ℕ) (i : ℕ) (_ : ℕ → E) : E :=
  match honRet (x.withBw N) N.L i with
  | some v => v
  | none => x.honRetO N bp bp1 i

/-- **The honest context** at the native run `N`, the ends `ec` and `open_stacked`'s point buffers `bp`, `bp1`. -/
noncomputable def honCtx (N : NatOpen) (ec : ℕ → ℕ) (bp bp1 : ℕ) : VsCtx :=
  { x with ec := ec, bw := x.honBw N, ex := [], ret := x.honRetR N bp bp1 }

end VsCtx

end
end LeanVM.Guest.B1.VsC
