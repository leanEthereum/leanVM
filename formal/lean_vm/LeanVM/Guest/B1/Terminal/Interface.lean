/-
  LeanVM.Guest.B1.Terminal.Interface

  B1 of `check_opening_terminal`: the stacked opening's transparent weight, what `verify_sub`
  hands the terminal, and the statement of its soundness.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.Tables.Interface
public import LeanVM.Guest.B1.Placement.Interface
public import LeanVM.Guest.B1.KeccakGkr.Interface

/-!
# `check_opening_terminal` (TRIAGE G #70): the interface

`check_opening_terminal(g_squares, zeta, chi, rm, g_bus_mu, g_zc_n, g_log_mem, tau_keccak_g,
kappa_base, lam_cl, col_offsets, z_vals, c_table, point, point1, inner_total, yr_at_tail,
sumcheck_target, ood_z, gmv)` evaluates the stacked opening's transparent weight at the WHIR
terminal point and checks the terminal (`whirLevels`' last `require`):
`(inner + basis(point)) · residual = target`, `basis` the weight `verifyStackedOpening` hands WHIR
for the claims `verifyExecution` opens: the ring switch's, then every column claim but the `KECCAK`
output lanes' (which the Keccak reduction consumed, `keccakPhase`), then the reduction's claim on
its committed outputs, then the stack commitment's out-of-domain claim `eq(z, ·)` (`readOod`),
batched by the powers of one challenge `λ` (`lam_cl`, the guest multiplying its running power by
it after each claim).

Every low dimension is a `kappa_base` entry times a baked power of `g`: a committed column's `κ`
at `COL_KAPPA_SRC`, `COL_KAPPA_ADJ` (`Tables.colKappaSrc`, `Tables.colKappaAdj`), a claim's low
point's length at `CLAIM_KAPPA_SRC`, `CLAIM_KAPPA_ADJ` (`Tables.claimKappaSrc`,
`Tables.claimKappaAdj`), over `kappa_base = [1, g^log_mem, g^τ_0, …, g^τ_5]`.

* `openedClaims claims outs`: the column claims the opening batches;
* `stackWeight layout claims ringPoint coeffs oodPoint lam x`: `basis(x)`;
* `TermCtx`: what `verify_tables` hands the terminal (`Tables.TCtx`);
* `TermPre`: what `verify_sub` establishes before the call: `TermCtx`, `certify_placement`'s
  context (`PCtx`, `KappasBelow`), the layout's placement being `placementsOf`'s, the base
  `kappa_base`, the selector's nibble shares at `g_squares·g^34`, `lam_cl = λ`, the outputs'
  claim's point at `z_vals` and the ring switch's point at `z_vals·g^39`, the ring map's
  coefficients at `c_table`, the terminal point at `point` (zero-padded to
  `SIZE_BITS + QKECCAK_SLOT_LOG = 40` words) and `1 + point` at `point1`, the out-of-domain point
  at `ood_z` and `gmv = g^m` for the stack's `m` variables; the memory nonempty and the bus point
  at most `40` long (`eq_prefix_chain`'s range);
* `check_opening_terminal_Spec`: under `TermPre`, the relation gives the terminal check.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The opening's weight -/

/-- The column claims the stacked opening batches after the Keccak phase: every claim but the
output lanes', then the Keccak reduction's. -/
def openedClaims (claims outs : List ColumnClaim) : List ColumnClaim :=
  claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) ++ outs

/-- The stacked opening's transparent weight at `x`: the ring switch's claim (`ringSwitchClaim`,
its weight `ringWeight ringPoint · coeffs`), every column claim on the stack, then the
out-of-domain claim `eq(oodPoint, ·)`, batched by the powers of `lam`. -/
def stackWeight (layout : Layout) (claims : List ColumnClaim) (ringPoint coeffs oodPoint : List E)
    (lam : E) (x : List E) : E :=
  let all := ringSwitchClaim layout 0 (fun rPrime ↦ ringWeight ringPoint rPrime coeffs) ::
    claims.map (·.stackClaim layout) ++ [(fun y ↦ eqEval oodPoint y, 0)]
  dot (powers lam all.length) (all.map fun c ↦ c.1 x)

/-! ## The terminal's precondition -/

/-- `SIZE_BITS + QKECCAK_SLOT_LOG`: the terminal point's buffers' length. -/
abbrev termPointCap : ℕ := 40

/-- The number of pooled claims before claim `j` that the opening batches (not an output
lane's): claim `j`'s power of `λ` is `λ^(1 + poolRank j)`. -/
def poolRank (j : ℕ) : ℕ :=
  ((List.range j).filter fun i ↦ Tables.claimColumns.getD i 0 ∉ keccakOutputColumns).length

/-- The terminal point, zero-padded to `40` words. -/
def padPoint (x : List E) : List E := x ++ List.replicate (termPointCap - x.length) 0

/-- Claim `j`'s low point's length, as the guest reads it (`cplen_g`). -/
def claimLow (layout : Layout) (j : ℕ) : ℕ :=
  Tables.claimLowDim layout.logMemory layout.tableLogHeights j

/-- **What `verify_tables` hands `check_opening_terminal`**, over `[zeta, chi, rm, g_bus_mu,
g_zc_n]`: `Tables.TCtx`. -/
abbrev TermCtx (rd : Reader) (layout : Layout) (bus : BusResult) (claims : List ColumnClaim) :
    List E → Prop :=
  Tables.TCtx rd layout bus claims

/-- **What `verify_sub` establishes before `check_opening_terminal`**, for the layout, the bus
result and the pooled claims of `verify_tables`, the Keccak reduction's claim on its outputs
`out`, the batching challenge `lam`, the ring switch's point and coefficients, the out-of-domain
point and the WHIR terminal point `x`. The columns' sizes are `columnKappas` over the guest's
bytecode log size (`Tables.guestLogBytecode`), as `certify_placement` certifies them and the guest
bakes them (`COL_KAPPA_ADJ`). -/
def TermPre (rd : Reader) (layout : Layout) (bus : BusResult) (claims : List ColumnClaim)
    (out : ColumnClaim) (lam : E) (ringPoint coeffs oodPoint x : List E) : List E → Prop
  | [gsq, zeta, chi, rm, gmu, gzcn, glm, gtau, kb, lamCl, off, zv, ct, pt, pt1, _, _, _, oz, gm] =>
      let kappas := columnKappas layout.logMemory Tables.guestLogBytecode layout.tableLogHeights
      let τ := layout.tableLogHeights.getD opKeccak 0
      TermCtx rd layout bus claims [zeta, chi, rm, gmu, gzcn] ∧
      Tables.PCtx rd kappas off ∧ Tables.KappasBelow kappas ∧
      layout.placements = (placementsOf kappas).1 ∧ layout.stackLog = (placementsOf kappas).2 ∧
      layout.stackLog ≤ 30 ∧ 1 ≤ layout.logMemory ∧ layout.logMemory ≤ 32 ∧
      bus.point.length ≤ 40 ∧ layout.tableLogHeights.length = 6 ∧
      (∀ h ∈ layout.tableLogHeights, h < 33) ∧
      glm = gen ^ layout.logMemory ∧ gtau = gen ^ τ ∧
      Tables.TbReadsAt rd kb (1 :: gen ^ layout.logMemory :: layout.tableLogHeights.map (gen ^ ·)) ∧
      Tables.GTabsAt rd (gsq * gen ^ 34) ∧ lamCl = lam ∧
      out.column = qkeccak ∧ out.point.length = τ + qkeccakSlotBits ∧ ReadsAt rd zv out.point ∧
      ringPoint.length = τ + qkeccakSlotBits ∧ ReadsAt rd (zv * gen ^ qkeccakVarsCap) ringPoint ∧
      coeffs.length = kBits ∧ ReadsAt rd ct coeffs ∧
      x.length = layout.stackLog ∧ ReadsAt rd pt (padPoint x) ∧
      ReadsAt rd pt1 ((padPoint x).map (1 + ·)) ∧
      oodPoint.length = layout.stackLog ∧ ReadsAt rd oz oodPoint ∧ gm = gen ^ layout.stackLog
  | _ => False

/-- **`check_opening_terminal`'s outcome**: it returns nothing, and for every reading of its
arguments that `TermPre` allows, the WHIR terminal holds: `(inner + basis(x))·residual = target`,
the arguments `15`, `16`, `17` being `inner`, `residual` and `target`. -/
def MeaningTerminal (rd : Reader) (args rets : List E) : Prop :=
  rets = [] ∧ ∀ (layout : Layout) (bus : BusResult) (claims : List ColumnClaim) (out : ColumnClaim)
    (lam : E) (ringPoint coeffs oodPoint x : List E),
    TermPre rd layout bus claims out lam ringPoint coeffs oodPoint x args →
      (args.getD 15 0 +
          stackWeight layout (openedClaims claims [out]) ringPoint coeffs oodPoint lam x) *
        args.getD 16 0 = args.getD 17 0

/-- **`check_opening_terminal` is sound** (TRIAGE #70). -/
def check_opening_terminal_Spec (rd : Reader) : Prop :=
  ∀ args rets, coreProgram.Rel rd "check_opening_terminal" args rets → MeaningTerminal rd args rets

end
end LeanVM.Guest.B1.VerifySub
