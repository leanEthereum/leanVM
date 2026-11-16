module

public import Quantum.Sphincs.Assembly.GameT

@[expose] public section

/-!
# Dropping the record ports of leanSPHINCS's game

The realized template game at `msgPol`, `realizeT v (gameT M upd msgPol pub A)`
(`Quantum.Sphincs.Assembly.Template`), runs over `recHwSpec`: memory `Finset HPos × M`, record
ports (the reveals), and counter trials whose `h`-reads update the inner memory with `upd`. Its
program `gameD pub v A` over `hwSpec` with memory `Unit` (`Quantum.Sphincs.Assembly.GameT`) drops
the record calls and keeps the memory on every read.

* `dropRec_gameT`: `DropRec HPos (realizeT v (gameT M upd msgPol pub A)) (gameD pub v A)`, by the
  structure of the two programs (leanXMSS's `ReadsRel` for the read programs: the counter
  searches `readsRel_grindK` and the verification's reads). At `msgPol` the coordinates a
  signature reveals do not depend on the memory label, so the dropped program does not either.
* With leanXMSS's `evalDistMap_runtime1R_eq` (the memory register forgotten), runtime 1 with record
  ports running the realized game has the law of runtime 1 running `gameD` (GameR's `p1K_eq_p1R`).
-/

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs Common Common.SufCma
open HashSig (Digest Message truncateHash)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (LazyProg restrictTo)
open Quantum.Xmss.Assembly (RevealVals revealThen progThen realizeT realizeT_bind₂ DropRec
  ReadsRel readsRel_pure readsRel_hashTrial readsRel_readsProgram progCall
  dropRec_realizeT_act_bind dropRec_realizeT_bind dropRec_realizeT_substitute
  dropRec_readLift_liftOrdinary)

namespace Quantum.Sphincs.Assembly

section records

variable {M : Type} (v : (s : HPos) → XD s)

theorem dropRec_revealThen {B C : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B C α)
    {y : QComp (hwSpec X Z Unit) B C α}
    (h : ∀ r, DropRec HPos (realizeT v (k (restrictTo T v, r))) y) :
    DropRec HPos (realizeT v (revealThen goodAll T k)) y :=
  DropRec.record T B _ _ (fun a ↦ Equiv.apply_symm_apply _ a) h

theorem dropRec_progThen {B C : QReg} {α : Type} (p : LazyProg X Z HPos XD)
    {k : QComp (SSpec M) B C α} {y : QComp (hwSpec X Z Unit) B C α}
    (h : DropRec HPos (realizeT v k) y) :
    DropRec HPos (realizeT v (progThen p trivial k))
      ((progCall (p.realize v) B).bind fun _ ↦ y) :=
  DropRec.prog (p.realize v) B (Equiv.uniqueProd B Unit).symm
    (k := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ realizeT v k)
    (k' := fun _ ↦ QuantumComp.primBind (L := LocalSig.instruments.{0})
      ⟨Unit, fun _ ↦ B, SubInstrument.relabel (Equiv.uniqueProd B Unit)⟩ fun _ ↦ y)
    fun _ ↦ DropRec.prim _ fun _ ↦ h

theorem dropRec_progPorts (B : QReg) :
    ∀ ps : List (LazyProg X Z HPos XD),
      DropRec HPos (realizeT v (progPorts M B ps)) (progPortsD v B ps)
  | [] => DropRec.pure _
  | p :: ps => dropRec_progThen v p (dropRec_progPorts B ps)

theorem dropRec_progSlots (pub : Pub) (B : QReg) :
    ∀ ss : List Slot,
      DropRec HPos (realizeT v (progSlots M pub B ss)) (progSlotsD pub v B ss)
  | [] => DropRec.pure _
  | s :: ss => by
    rw [progSlots, progSlotsD, realizeT_bind₂]
    exact DropRec.bind₂ (dropRec_progPorts v B _) fun _ ↦ dropRec_progSlots pub B ss

end records

section game

variable {M : Type} (upd : TrialUpd M) (v : (s : HPos) → XD s)

/-- **The counter search at memories `M` and `Unit`.** -/
theorem readsRel_grindK (pub : Pub) (B : QReg) (K : Key) (m : Digest) :
    ∀ n c, ReadsRel goodAll v (grindK M upd pub B K m n c)
      (grindK Unit (keepUpd Unit) pub B K m n c)
  | 0, _ => readsRel_pure v _
  | n + 1, c => by
    rw [grindK, grindK]
    refine (readsRel_hashTrial pub.perm (upd K) (keepUpd Unit K) _).bind fun out ↦ ?_
    generalize TargetSum.decodeDigest (truncateHash out) = d
    cases d with
    | none => exact readsRel_grindK pub B K m n (c + 1)
    | some x => exact readsRel_pure v _

theorem dropRec_signLayerT (pub : Pub) (B : QReg) (K : Key) :
    DropRec HPos (realizeT v (signLayerT M upd pub B K)) (signLayerD pub v B K) := by
  rw [signLayerT]
  refine dropRec_revealThen v _ _ fun _ ↦ ?_
  rw [signLayerD, realizeT_bind₂]
  refine DropRec.bind₂ (readsRel_grindK upd v pub B K _ _ _) fun g ↦ ?_
  rcases g with _ | ⟨c, x⟩
  · exact DropRec.pure _
  · refine dropRec_revealThen v _ _ fun _ ↦ ?_
    rw [realizeT_bind₂]
    exact DropRec.bind₂ (dropRec_progSlots v pub B _) fun _ ↦ DropRec.pure _

theorem dropRec_forsOpenT (pub : Pub) (B : QReg) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    DropRec HPos (realizeT v (forsOpenT M pub B idx lv)) (forsOpenD pub v B idx lv) := by
  rw [forsOpenT]
  refine dropRec_revealThen v _ _ fun _ ↦ ?_
  rw [forsOpenD, realizeT_bind₂]
  exact DropRec.bind₂ (dropRec_progSlots v pub B _) fun _ ↦ DropRec.pure _

/-- **A signature at `msgPol` drops to `signD`**: its reveals are record calls, and the coordinates
it reveals and the cells it programs do not depend on the memory label. -/
theorem dropRec_signT (pub : Pub) (B : QReg) (msg : Message) :
    DropRec HPos (realizeT v (signT M upd msgPol pub B msg)) (signD pub v B msg) := by
  rw [signT]
  refine dropRec_revealThen v _ _ fun _ ↦ dropRec_revealThen v _ _ fun _ ↦ ?_
  rw [realizeT_bind₂, signD]
  refine DropRec.bind₂ (dropRec_progPorts v B _) fun _ ↦ ?_
  rw [realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_forsOpenT v pub B _ _) fun fo ↦ ?_
  rw [realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_signLayerT upd v pub B _) fun s₀ ↦ ?_
  rcases s₀ with _ | bottom
  · exact DropRec.pure _
  dsimp only
  rw [realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_signLayerT upd v pub B _) fun s₁ ↦ ?_
  rcases s₁ with _ | middle
  · exact DropRec.pure _
  dsimp only
  rw [realizeT_bind₂]
  refine DropRec.bind₂ (dropRec_signLayerT upd v pub B _) fun s₂ ↦ ?_
  rcases s₂ with _ | top
  · exact DropRec.pure _
  · exact DropRec.pure _

theorem dropRec_signAt (pub : Pub) (msg : Message) (E : QReg) {A : QReg}
    (ℓ : A ≃ sAdvSpec.In (.sign msg) × E) :
    DropRec HPos (realizeT v (signAt M upd msgPol pub msg E ℓ)) (signAtD pub v msg E ℓ) := by
  rw [signAt, signAtD]
  exact dropRec_realizeT_act_bind v _ fun _ ↦ dropRec_signT upd v pub _ msg

theorem dropRec_challengeT (pub : Pub) (A : QReg)
    (c : (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).A A) :
    DropRec HPos (realizeT v (challengeT M upd msgPol pub A c)) (challengeD pub v A c) := by
  rcases c with o | ⟨p | msg, E, ℓ⟩
  · exact dropRec_readLift_liftOrdinary v _
  · exact dropRec_readLift_liftOrdinary v _
  · exact dropRec_realizeT_bind v (dropRec_signAt upd v pub msg E ℓ) fun _ _ ↦ DropRec.pure _

/-- **The realized game at `msgPol` drops to `gameD`**: with its record calls removed and its reads
keeping the memory `Unit`, the template game is `gameD pub v A`. -/
theorem dropRec_gameT (pub : Pub) (A : SAdversary) :
    DropRec HPos (realizeT v (gameT M upd msgPol pub A)) (gameD pub v A) := by
  rw [gameT]
  refine dropRec_revealThen v _ _ fun _ ↦ ?_
  rw [realizeT_bind₂, gameD]
  refine DropRec.bind₂ (dropRec_realizeT_substitute v (dropRec_challengeT upd v pub) _)
    fun run ↦ ?_
  rw [realizeT_bind₂]
  exact DropRec.bind₂ ((readsRel_readsProgram pub.perm _).map Prod.fst) fun _ ↦ DropRec.pure _

end game

end Quantum.Sphincs.Assembly

end
