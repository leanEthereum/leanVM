module

public import Quantum.Sphincs.Assembly.PrefixFacts
public import Quantum.Sphincs.Assembly.GameR
public import Quantum.Sphincs.Assembly.GameTCalls
public import Quantum.Xmss.Assembly.WinDecomp

@[expose] public section

/-!
# The end of leanSPHINCS's event-side game: the verification's reads

The canonical runtime-2 game at template data `(pub, v)` (contract C4), split for the end of the
event bound (`WinDecomp`): the challenge prefix, the verification's read program with its reads
returned, the winning condition (`gameR_eq_verReads`). The generic part (the decompressed basis,
`noBot_runtimeR`, `readsRecorded`, `SuppTo`, `trace_le_of_off`) is leanXMSS's
`Quantum.Xmss.Assembly.{EndReads,WinDecomp}`; the classification is Classify's
`mem_bad_of_agrees`.

* **The verification's reads**: the verification of a prefix outcome through read ports, realized,
  returning the verdict and the reads (`realizeT_verifyT_eq`), written out in every statement.
* **Their counts** (`VerCounts`, `verCounts_honest`): the honest verification reads at most
  `verifyBlocks` cells of each function (one per Keccak-f block, `verify_hashBlocks`); the log of a
  run (`verLog`, empty past the counts) has at most `verifyBlocks` reads of each port
  (`readCount_verLog_le`).
* **The grade** (`grade_branch₂_sph`): a program on the trivial register with at most `progCap`
  program calls ends with at most `progCap` hardwired cells (Costs' `dbGrade_le_progCap`), the
  hypothesis `dbGrade W ≤ N` of PrefixFacts' `winFacts_of_preFacts` at `N = progCap`.
-/

open Matrix IPFunctor OracleSpec
open scoped Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Message)
open Quantum.Xmss (X Z extProgCharge hashBlocks_eq_length_blocks sum_map_queries_le)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT realizeT_bind₂ readLiftQ
  readLift_bind₂ initU recStep gradeSupp_recStep ofSpongeRead readCount_map_ofSpongeRead)

namespace Quantum.Sphincs.Assembly

/-! ## The verification's reads -/

section reads

/- The verification's read program at `(pub, v)` on a prefix outcome `pre`,
`realizeT v (readLiftQ goodAll (readsProgram Selections pub.perm (QReg.of Unit)
(schemeWithHash.verify pre.1 pre.2.1)))`, is written out in every statement, never wrapped in a
definition: with a wrapping definition, the kernel check of its runs against `SuppTo`'s statement
(`suppTo_readsProgram`) hit deep recursion. -/

set_option synthInstance.maxSize 2000 in
theorem realizeT_verifyT_eq (pub : Pub) (v : (s : HPos) → XD s)
    (pre : PublicKey × (Forgery × SignLog Message (Option Signature))) :
    realizeT v (verifyT Selections pub pre) =
      QuantumComp₂.bind (realizeT v (readLiftQ goodAll (readsProgram Selections pub.perm
        (QReg.of Unit) (schemeWithHash.verify pre.1 pre.2.1)))) fun a ↦
          QuantumComp₂.pure (winCondS pre && a.1) := by
  rw [verifyT, QuantumComp₂.map_eq_bind_pure, readLift_bind₂, QuantumComp₂.bind_assoc,
    realizeT_bind₂]
  rfl

set_option synthInstance.maxSize 2000 in
/-- **The canonical game is its prefix, the verification's reads, and the winning condition.** -/
theorem gameR_eq_verReads (pol : DigestPolicy) (A : SAdversary) (pub : Pub)
    (v : (s : HPos) → XD s) :
    gameR pol A pub v = (prefixR pol A pub v).bind fun pre ↦
      QuantumComp₂.bind (realizeT v (readLiftQ goodAll (readsProgram Selections pub.perm
        (QReg.of Unit) (schemeWithHash.verify pre.1 pre.2.1)))) fun a ↦
          QuantumComp₂.pure (winCondS pre && a.1) := by
  rw [gameR_eq]
  simp only [realizeT_verifyT_eq]

end reads

/-! ## The counts of the verification's reads -/

section counts

/-- The reads of each port number at most `verifyBlocks`. -/
def VerCounts (l : List (SpongeRead X Z)) : Prop :=
  ∀ p, readCount p (l.map ofSpongeRead) ≤ verifyBlocks

/-- **The honest verification makes at most `verifyBlocks` reads of each port**: one per
block. -/
theorem verCounts_honest (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (pk : PublicKey)
    (f : Forgery) : VerCounts (honestEval t π (schemeWithHash.verify pk f)).2 := by
  intro p
  rw [readCount_map_ofSpongeRead, snd_honestEval, List.countP_flatMap]
  refine le_of_eq_of_le (congrArg List.sum (List.map_congr_left fun inp _ ↦ ?_))
    (sum_map_queries_le (spongeOut (spongePerm t π)) Quantum.Xmss.hashBlocks
      (verify_hashBlocks pk f))
  simp only [Function.comp_apply, inputReads, countP_port_spongeReads, hashBlocks_eq_length_blocks]

open scoped Classical in
/-- The log of a run of the verification's reads (empty if it exceeds the read counts). -/
noncomputable def verLog
    (i : (PublicKey × (Forgery × SignLog Message (Option Signature))) ×
      (Bool × List (SpongeRead X Z))) :
    QueryLog (spongeOSpec X Z) :=
  if VerCounts i.2.2 then i.2.2.map ofSpongeRead else []

theorem verLog_of_counts
    {i : (PublicKey × (Forgery × SignLog Message (Option Signature))) ×
      (Bool × List (SpongeRead X Z))} (h : VerCounts i.2.2) :
    verLog i = i.2.2.map ofSpongeRead := by
  classical
  unfold verLog
  rw [ite_eq_left h]

theorem readCount_verLog_le
    (i : (PublicKey × (Forgery × SignLog Message (Option Signature))) ×
      (Bool × List (SpongeRead X Z))) (p : SpongePort) :
    readCount p (verLog i) ≤ verifyBlocks := by
  classical
  by_cases h : VerCounts i.2.2
  · rw [verLog_of_counts h]
    exact h p
  · unfold verLog
    rw [ite_eq_right h]
    exact Nat.zero_le _

end counts

/-! ## The grade at the end of a program -/

/-- **At most `progCap` hardwired cells** at the end of a program on the trivial register with at
most `progCap` program calls (Costs' `dbGrade_le_progCap`). -/
theorem grade_branch₂_sph {S M' : Type} [Fintype S] [DecidableEq S] [Fintype M']
    [DecidableEq M'] (m₀ : Finset S × M') {α : Type}
    {x : QComp (recHwSpec X Z S M') (QReg.of Unit) (QReg.of Unit) α}
    (hx : IFreeM.IsChargeBound x (portCharge (L := LocalSig.instruments.{0})
      (extProgCharge X Z (Finset S × M') (recSpec S M'))) progCap) (a : α) :
    QuerySupportedOn (fun p : Unit × HwReg X Z (Finset S × M') ↦ p.2)
      {s | dbGrade s.2.1 ≤ progCap}
      (((runtimeR m₀).run₂ .instruments x).branch a (initU m₀)) := by
  have h := dbGrade_le_progCap m₀ (recStep (X := X) (Z := Z) (S := S) (M := M'))
    (fun T r n σ hσ ↦ gradeSupp_recStep T r n σ hσ) .instruments hx le_rfl (SubState.basis ())
    ⟨QReg.of Unit, rfl, a⟩
  exact QuerySupportedOn.imp (q' := fun p : Unit × HwReg X Z (Finset S × M') ↦ p.2)
    (S' := {s | dbGrade s.2.1 ≤ progCap}) h fun _ h ↦ h

end Quantum.Sphincs.Assembly

end
