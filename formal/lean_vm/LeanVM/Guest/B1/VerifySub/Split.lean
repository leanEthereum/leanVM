/-
  LeanVM.Guest.B1.VerifySub.Split

  The deferring verifier's program (`deferringVerifierProgram`) regrouped along `verify_sub`'s
  callees.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Guest.B1.Gkr.InterfaceP

/-!
# The deferring verifier, regrouped

`deferredFlat c bytecode pi` is `deferringVerifierProgram c bytecode pi` (`deferred_eq`) with its
phases grouped as `verify_sub` runs them: the announced sizes (`readAnnouncedSizes`), the stack's
commitment and its out-of-domain sample (`readOod`: a grind, the point, the value), the bus's
depth check, grind, slot weights and `β`, the bus's GKR (`gkrPhase`, `verify_bus_gkr`), the bus's
rest, the table sumcheck and the public input (`tablesSeg`, `verify_tables`), the output lanes'
check and the Keccak reduction (`keccakPhaseClaims`, `verify_keccak`), the ring switch (a grind
and its sixteen challenges), and the stacked opening (the batching challenge, `whirOpen`, i.e.
`open_stacked`, and the terminal's check, `check_opening_terminal`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The push side's bus depth of a layout. -/
abbrev busDepth (layout : Layout) : ℕ :=
  (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth

/-- `verifyBusBalance` as the depth's check, the grind, the weights and `β`, `gkrPhase` and
`busRest`. -/
theorem verifyBusBalance_split (ev : List K → List E → E → VerifierProgram Unit) (layout : Layout) :
    verifyBusBalance ev layout =
      (VerifierProgram.require (busDepth layout < 64)).bind fun _ ↦
      (VerifierProgram.grindProofOfWork (busGrindingBits (busDepth layout))).bind fun _ ↦
      (VerifierProgram.sampleChallenges (2 ^ busBits)).bind fun weights ↦
      VerifierProgram.sampleChallenge.bind fun beta ↦
      (Tables.gkrPhase (busDepth layout)).bind fun r ↦
        Tables.busRest ev layout weights beta r.2.1 r.2.2 := by
  simp only [verifyBusBalance, Tables.gkrPhase, Tables.busRest, VerifierProgram.bind_eq,
    VerifierProgram.pure_eq, VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

/-- The output lanes' claims. -/
def lanesOf (claims : List ColumnClaim) : List ColumnClaim :=
  claims.filter fun c ↦ c.column ∈ keccakOutputColumns

/-- The claims the stacked opening batches: the ring switch's, the column claims with a
placement (the output lanes' replaced by the Keccak reduction's), the out-of-domain one. -/
def stackClaims (layout : Layout) (claims : List ColumnClaim) (target : E)
    (weight : List E → E) (ood : StackClaim) : List StackClaim :=
  ringSwitchClaim layout target weight :: claims.map (·.stackClaim layout) ++ [ood]

/-- The bus's grind, its slot weights and `β`. -/
def busChallenges (depth : ℕ) : VerifierProgram (List E × E) :=
  (VerifierProgram.grindProofOfWork (busGrindingBits depth)).bind fun _ ↦
  (VerifierProgram.sampleChallenges (2 ^ busBits)).bind fun weights ↦
  VerifierProgram.sampleChallenge.bind fun beta ↦ VerifierProgram.ret (weights, beta)

/-- **The deferring verifier's program, regrouped.** -/
def deferredFlat (c : BytecodeClaim) (bytecode : List K) (pi : Digest) : VerifierProgram Bool :=
  (readAnnouncedSizes bytecode).bind fun ls ↦
  (commitStack ls.1.stackLog ls.2).bind fun _ ↦
  (readOod ls.1.stackLog).bind fun ood ↦
  (VerifierProgram.require (busDepth ls.1 < 64)).bind fun _ ↦
  (busChallenges (busDepth ls.1)).bind fun wb ↦
  (Tables.gkrPhase (busDepth ls.1)).bind fun r ↦
  (Tables.tablesSeg (claimedBytecodeValue c) ls.1 pi wb.1 wb.2 r.2.1 r.2.2).bind fun bc ↦
  (keccakPhaseClaims ls.1 bc.2).bind fun kc ↦
  (ringSwitch kc.2.1 kc.2.2).bind fun rs ↦
  (verifyStackedOpening ls.1.stackLog ls.2 (stackClaims ls.1 kc.1 rs.1 rs.2 ood)).bind fun _ ↦
  VerifierProgram.ret true

theorem deferred_eq (c : BytecodeClaim) (bytecode : List K) (pi : Digest) :
    deferringVerifierProgram c bytecode pi = deferredFlat c bytecode pi := by
  rw [deferredProgram_eq]
  simp only [verifyExecutionClaims, deferredFlat, verifyBusBalance_split, busChallenges,
    Tables.tablesSeg, stackClaims, VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
    VerifierProgram.ret_bind]

end
end LeanVM.Guest.B1.VerifySub
