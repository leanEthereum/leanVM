/-
  LeanVM.Guest.B1.VerifySub.Split

  The deferring verifier's program (`deferringVerifierProgram`, V:2328) regrouped along
  `verify_sub`'s callees.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Guest.B1.Gkr.Interface

/-!
# The deferring verifier, regrouped

`deferredFlat c bytecode pi` is `deferringVerifierProgram c bytecode pi` (`deferred_eq`) with its
phases grouped as `verify_sub` runs them: the announced sizes (`readAnnouncedSizes`), the stack's
commitment, the four bus challenges and `β`, the bus's GKR (`gkrPhase`, `verify_bus_gkr`), the bus's
rest, the table sumcheck and the public input (`tablesSeg`, `verify_tables`), the output lanes'
check, the Keccak reduction and the ring map's first challenge (`keccakSeg`, `verify_keccak`), the
ring map's other five challenges, the batching challenge, the stacked opening up to its terminal
(`whirOpen`,
`open_stacked`) and the terminal's check (`check_opening_terminal`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verifyBusBalance` (V:1481) as the challenges, `gkrPhase` and `busRest`. -/
theorem verifyBusBalance_split (ev : (List K → List E → VerifierProgram E)) (layout : Layout) :
    verifyBusBalance ev layout =
      (VerifierProgram.sampleChallenges busBits).bind fun alphas ↦
          VerifierProgram.sampleChallenge.bind fun beta ↦
        (Tables.gkrPhase (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth).bind
          fun r ↦ Tables.busRest ev layout alphas beta r.2.1 r.2.2 := by
  simp only [verifyBusBalance, Tables.gkrPhase, Tables.busRest, VerifierProgram.bind_eq,
      VerifierProgram.pure_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

/-- The output lanes' claims (V:2215). -/
def lanesOf (claims : List ColumnClaim) : List ColumnClaim :=
  claims.filter fun c ↦ c.column ∈ keccakOutputColumns

/-- The claims the opening batches, as stack claims: the ring switch's first. -/
def stackClaims (layout : Layout) (claims : List ColumnClaim) (outs : List ColumnClaim)
    (ringPoint slices challenges : List E) : List StackClaim :=
  ringSwitchClaim layout (polyEval (slices.map (phiMap · challenges)) gen)
      (fun rPrime ↦ ringWeight ringPoint rPrime (ringCoefficients challenges)) ::
    (claims.filter (fun c ↦ c.column ∉ keccakOutputColumns) ++ outs).map (·.stackClaim layout)

/-- **The deferring verifier's program, regrouped.** -/
def deferredFlat (c : BytecodeClaim) (bytecode : List K) (pi : Digest) : VerifierProgram Bool :=
  (readAnnouncedSizes bytecode).bind fun ls ↦
  (commitStack ls.1.stackLog ls.2).bind fun _ ↦
  (VerifierProgram.sampleChallenges busBits).bind fun alphas ↦
  VerifierProgram.sampleChallenge.bind fun beta ↦
  (Tables.gkrPhase (busLayout [0, ls.1.logMemory, ls.1.logBytecode] ls.1.push).depth).bind fun r ↦
  (Tables.tablesSeg (claimedBytecodeValue c) ls.1 pi alphas beta r.2.1 r.2.2).bind fun bc ↦
  (VerifierProgram.require ((lanesOf bc.2).map (·.column) = keccakOutputColumns ∧
    ∀ c ∈ lanesOf bc.2, c.point = ((lanesOf bc.2).headD default).point)).bind fun _ ↦
  (keccakSeg (ls.1.tableLogHeights.getD opKeccak 0) ((lanesOf bc.2).headD default).point
    ((lanesOf bc.2).map (·.value))).bind fun km ↦
  (VerifierProgram.sampleChallenges 5).bind fun chs ↦
  VerifierProgram.sampleChallenge.bind fun lam ↦
  let all := stackClaims ls.1 bc.2 km.1.1 km.1.2.1 km.1.2.2 (km.2 :: chs)
  (B1.Whir.whirOpen ls.1.stackLog ls.2 (dot (powers lam all.length) (all.map (·.2)))).bind fun w ↦
  (VerifierProgram.require (w.Accepts fun point ↦ dot (powers lam all.length) (all.map fun c ↦ c.1 point))).bind
    fun _ ↦ VerifierProgram.ret true

theorem deferred_eq (c : BytecodeClaim) (bytecode : List K) (pi : Digest) :
    deferringVerifierProgram c bytecode pi = deferredFlat c bytecode pi := by
  simp only [deferredProgram_eq, verifyExecutionClaims, deferredFlat, VerifierProgram.bind_eq,
    VerifierProgram.bind_assoc]
  refine congrArg _ (funext fun ls ↦ congrArg _ (funext fun _ ↦ ?_))
  rw [verifyBusBalance_split]
  simp only [Tables.tablesSeg, VerifierProgram.bind_assoc, VerifierProgram.bind_eq,
      VerifierProgram.pure_eq, VerifierProgram.ret_bind]
  refine congrArg _ (funext fun alphas ↦ congrArg _ (funext fun beta ↦ congrArg _ (funext fun r ↦
    congrArg _ (funext fun bus ↦ congrArg _ (funext fun cl ↦ congrArg _ (funext fun pc ↦ ?_))))))
  simp only [keccakPhaseClaims, lanesOf, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  refine congrArg _ (funext fun _ ↦ ?_)
  simp only [keccakSeg, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  refine congrArg _ (funext fun kr ↦ ?_)
  simp only [ringSwitch, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
      VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  rw [show ringMapShifts.length = 5 + 1 from rfl, VerifierProgram.sampleChallenges]
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
      VerifierProgram.ret_bind]
  refine congrArg _ (funext fun m ↦ congrArg _ (funext fun chs ↦ ?_))
  simp only [verifyStackedOpening, verifyWhir_eq_target, B1.Whir.verifyWhir_split, stackClaims, VerifierProgram.bind_eq,
    VerifierProgram.bind_assoc]
  refine congrArg _ (funext fun lam ↦ congrArg _ (funext fun w ↦ ?_))
  rfl

end
end LeanVM.Guest.B1.VerifySub
