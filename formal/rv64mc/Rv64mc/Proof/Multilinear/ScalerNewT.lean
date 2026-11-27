/-
  Rv64mc.Proof.Multilinear.ScalerNewT

  `Scaler::new(r, uses)` is total. `safe`: from the slot 8-byte aligned, in a window and the caller's (`PreS`), it
  stores `Plain(r)` (the niche `usize::MAX`, then `r`'s limbs) for `uses` below `256`, or tail-calls `Scaled::new`
  (`ScaledNewT`) on the same slot, whose total postcondition it gives (`PostS`: a vector of `1408` `E`s, its buffer
  allocated since the entry), writing at most the slot (`NewOut`), or the run ends with `a0 = 2` where `Scaled::new`'s
  does. `total`: `safe` with the partial contract's postcondition beside it (`HoldsT.of_holds`, the partial proof
  `ScalerNew.ok` at the image as the hypothesis `hpart`).

  `Scaler::new`'s partial proof at the image rests on `Scaled::new`'s partial contract, which no proof discharges yet
  (its functional contract is owed, `notes/total-status.md`), so `total`'s `Table` instance carries that contract as
  a hypothesis; `safe`'s carries only environment facts.

  ## Main definitions

  * `PreS`, `PostS`, `safeT`, `NewPreT`, `specT`

  ## Main results

  * `safe`, `total`
-/

import Rv64mc.Proof.Multilinear.ScalerNew
import Rv64mc.Proof.Field.ScaledNewT
import Rv64mc.Core.HoldsTOfHolds

namespace Rv64mc.Proof.Multilinear.ScalerNewT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.Scaler
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Multilinear.Scaler.New (Link tmpl)

/-- The safety precondition: the slot (`24` bytes at `a0`) in a window, 8-byte aligned and the caller's. -/
def PreS (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ env.Owned m (regs .x2) (regs .x10) 24

/-- The safety postcondition: for `uses` (`a3`) at most `255` the slot holds `Plain` (`usize::MAX`, then `a1`,
    `a2`), otherwise `Scaled::new`'s total postcondition (`ScaledNewT.PostT`). -/
def PostS (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  ((regs .x13).toNat ≤ 255 → m'.getMem (regs .x10) = 0xffffffffffffffff#64 ∧
      m'.getMem (regs .x10 + 8#64) = regs .x11 ∧ m'.getMem (regs .x10 + 16#64) = regs .x12) ∧
    (255 < (regs .x13).toNat → Field.ScaledNewT.PostT env regs m r' m')

/-- **`Scaler::new`'s safety contract**: `PreS` to `PostS`, writing at most the slot, or `a0 = 2`. -/
def safeT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreS env) (PostS env) NewOut (Stop := AbortStop)

/-- The total precondition: the partial one (`NewPre`) and the slot in a window, 8-byte aligned. -/
def NewPreT (env : Env) (r : E) (regs : Reg → Word) (m : MachineState) : Prop :=
  NewPre env r regs m ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0

/-- **The total contract of `Scaler::new`**: `PostS` and the partial contract's postcondition (`NewPost`), writing at
    most the slot, or `a0 = 2`; for every `r`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ r, HoldsT env p i need (NewPreT env r) (fun regs m r' m' => PostS env regs m r' m' ∧ NewPost env r regs m r' m')
    NewOut (Stop := AbortStop)

set_option rv_sym.heap true in
/-- **`Scaler::new` is safe**: the stores of `Plain`, or the tail call. -/
theorem safe (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS : Nat} (hnS : needS ≤ need) (hsn : Field.ScaledNewT.specT env p L.new.idx needS) :
    safeT env p i need := by
  rv_autoT hp with [hL] using [hsn]
  exact fun _ => ⟨⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩, hret1_22, hret1_23⟩

/-- **`Scaler::new` is total**: `safe` and the partial proof (`hpart`) combined by `HoldsT.of_holds`. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS : Nat} (hnS : needS ≤ need) (hsn : Field.ScaledNewT.specT env p L.new.idx needS)
    (hpart : newSpec env p i need) : specT env p i need := fun r =>
  ((safe env p i L hp hL hnS hsn).of_holds (hpart r)).contract.mono
    (fun _ _ _ _ ⟨⟨he, hs, hst, hn, ⟨hP, hw, hal⟩, h16⟩, hW⟩ =>
      ⟨⟨he, hs, hst, hn, ⟨⟨hw, hal, hP.1⟩, hP⟩, h16⟩, hW⟩)
    (fun _ _ _ _ _ _ _ h => h) fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Multilinear.ScalerNewT

/-- info: 'Rv64mc.Proof.Multilinear.ScalerNewT.safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.ScalerNewT.safe

/-- info: 'Rv64mc.Proof.Multilinear.ScalerNewT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.ScalerNewT.total
