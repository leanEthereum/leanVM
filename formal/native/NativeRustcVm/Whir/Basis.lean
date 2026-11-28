module

public import NativeRustcVm.Whir.Rep
public import NativeRustcVm.Layout.Rep
public import NativeRustcVm.Ring.Rep
public import NativeRustcVm.KeccakGkr.Rep

/-!
# The stacked opening's basis in memory

`BasisW<'a>` (`whir.rs`, `#[repr(C)]`, 56 bytes) is the model's `BasisW` (the batching scales and the
stack claims they weigh) by reference: the scales' slice (address, length), then the addresses of
the layout, the ring switch's output, phase 6's Keccak output, the column claims and the
out-of-domain claim. The stack claims are those `verifyExecution` hands `verifyStackedOpening`:
the ring-switched one, every column claim with a placement, the out-of-domain one
(`stackClaims`).

`BasisAddrs` names the six areas; `BasisWAt d p ba b`: the `BasisW` at `p` names them, and they
hold `b` (the stack's log-size at most `maxLogStack`, as `ladder` checks before WHIR runs).
-/

namespace NativeRustcVm.Whir

open NativeVm.Model LeanVM.Parameters
open NativeRustcVm.Transcript (off)
open NativeRustcVm.Layout NativeRustcVm.Ring NativeRustcVm.KeccakGkr

@[expose] public section

/-- `BasisW`'s bytes. -/
def basisBytes : Nat := 56

/-- The stack claims of the stacked opening (`verifyExecution`'s phase 7): the ring-switched one,
the column claims with a placement, the out-of-domain one. -/
def stackClaims (layout : LayoutW) (target : EW) (point coefficients : Array EW)
    (claims : Array ColumnClaimW) (z : Array EW) (value : EW) : Array StackClaimW :=
  #[ringSwitchClaim layout target point coefficients] ++ claims.filterMap (·.onStack layout) ++
    #[⟨.eq z, value⟩]

/-- The areas a `BasisW` refers to: the scales (and their count), the layout, the ring switch's
output, the Keccak output, the column claims, the out-of-domain claim. -/
structure BasisAddrs where
  scales : BitVec 64
  count : Nat
  layout : BitVec 64
  ring : BitVec 64
  keccak : BitVec 64
  claims : BitVec 64
  ood : BitVec 64

/-- The areas' regions. -/
def BasisAddrs.regions (ba : BasisAddrs) : List Region :=
  [⟨ba.scales, 16 * ba.count⟩, ⟨ba.layout, layoutBytes⟩, ⟨ba.ring, ringWBytes⟩,
    ⟨ba.keccak, outBytes⟩, ⟨ba.claims, claimsBytes⟩, ⟨ba.ood, eqClaimBytes⟩]

/-- The areas hold the stack claims' data: the layout `layout` (its stack's log-size at most
`maxLogStack`), the ring switch's target and coefficients, the Keccak output's point, the column
claims, the out-of-domain claim `⟨.eq z, value⟩`; `claims` are their `stackClaims`. -/
structure BasisData (d : Mem 64) (ba : BasisAddrs) (claims : Array StackClaimW) : Prop where
  holds : ∃ (layout : LayoutW) (target : EW) (coefficients point slices : Array EW)
      (cs : Array ColumnClaimW) (z : Array EW) (value : EW),
    layout.stackLog ≤ Whir.maxLogStack ∧ LayoutWAt d ba.layout layout ∧
      RingWAt d ba.ring target coefficients ∧ KeccakOutAt d ba.keccak point slices ∧
      ClaimsWAt d ba.claims cs ∧ EqClaimAt d ba.ood z value ∧
      claims = stackClaims layout target point coefficients cs z value

/-- **The `BasisW` at `p`** names the areas `ba`, which hold `b`: the scales' slice and the five
addresses, the scales, the stack claims' data. -/
structure BasisWAt (d : Mem 64) (p : BitVec 64) (ba : BasisAddrs) (b : BasisW) : Prop where
  count_lt : ba.count < 2 ^ 64
  words : WordsAt d p [UInt64.ofBitVec ba.scales, ba.count.toUInt64, UInt64.ofBitVec ba.layout,
    UInt64.ofBitVec ba.ring, UInt64.ofBitVec ba.keccak, UInt64.ofBitVec ba.claims,
    UInt64.ofBitVec ba.ood]
  scales_size : b.scales.size = ba.count
  scales : EWsAt d ba.scales b.scales.toList
  data : BasisData d ba b.claims

end

end NativeRustcVm.Whir
