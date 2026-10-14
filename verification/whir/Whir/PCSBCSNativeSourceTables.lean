import Whir.PCSBCSCapturedIdealNativeAcceptance

/-! Every typed atomic table has exactly the mixed seed/raw interpretation
used by the actual native driver. This is an inverse of existing partitions,
not an independence assumption or a distribution replacement. -/
set_option autoImplicit false
namespace Whir.PCSBCSNativeSourceTables
open Concrete FiatShamirGame DuplexModeGame TypedOracleCompiler RawOracleCoupling
open PCSBCSChallengeOracle TypedFiatShamirGame PCSStateRestoration.Latent

variable {p : ParameterBounds.Profile} {B : Nat} {iv : Digest32} {boundary : Nat}
local notation "part" => EnteredPacket.partition (p := p) (Q := B) (iv := iv) (boundary := boundary)
local notation "Keys" => PCSBCSSourceRootCapture.Key (p := p) (Q := B) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer (p := p) (Q := B) (iv := iv) (boundary := boundary)

theorem every_table (table : Table Keys Answers) :
    ∃ (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32),
      (part).split (PublicCompressionCouplingMixed.oracle seed ro) = table := by
  let pair := PublicCompressionCouplingMixed.tableEquiv B ((part).join table)
  refine ⟨pair.1,pair.2,?_⟩
  have joined : PublicCompressionCouplingMixed.oracle pair.1 pair.2 = (part).join table :=
    (PublicCompressionCouplingMixed.tableEquiv B).left_inv ((part).join table)
  rw [joined]
  exact (part).split_join table

section Driver
variable (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (saved : AnchoredHeaderCodec.Record)
    (proofs : Array MerkleTransport.PrunedMerklePaths) (B : Nat)
    (limit : WHIRPhysicalVerifier.sourceBudget ctx Q packet ≤ B)

theorem allocation_table
    (table : Table
      (PCSBCSSourceRootCapture.Key (p := packet.val.profile) (Q := B) (iv := ctx.iv)
        (boundary := (RawWHIRKeys.entry ctx packet.val).frames.length))
      (PCSBCSSourceRootCapture.Answer (p := packet.val.profile) (Q := B) (iv := ctx.iv)
        (boundary := (RawWHIRKeys.entry ctx packet.val).frames.length))) :
    ∃ (seed : DuplexPublicSimulator.Seed) (ro : RawKey B → Digest32),
      PCSBCSCapturedIdealNativeAcceptance.table ctx Q packet B seed ro = table ∧
      Sampling.eval table (PCSBCSCapturedIdealNativeAcceptance.allocationProgram
        cap model ctx stack Q packet saved proofs B limit) =
        AnchoredMixedIdealSourceAcceptance.mixedView cap .fresh model ctx stack Q packet saved proofs
          ctx.iv B limit seed ro := by
  obtain ⟨seed,ro,equal⟩ := every_table table
  refine ⟨seed,ro,equal,?_⟩
  rw [← equal]
  exact PCSBCSCapturedIdealNativeAcceptance.allocation_result
    cap model ctx stack Q packet saved proofs B limit seed ro
end Driver

#print axioms every_table
#print axioms allocation_table
end Whir.PCSBCSNativeSourceTables
