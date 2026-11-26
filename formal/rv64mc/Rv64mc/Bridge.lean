/-
  Rv64mc.Bridge

  From the statement's machine to machine-checked's. A run of `step` that halts with `a0 = 0` is a run of SP1's
  `stepSp1` that ends `Accepted` (`steps_stepsSp1`, `accepted_of_halts`), so a state from which every accepting
  `stepSp1` run gives `P` (`SafeN`) gives `P` (`SafeN.of_accepted`). `sound_of_safe`: an image is `Sound` once every
  loaded state is safe for the verdict. `Loaded` puts machine-checked's lifted functions in the code
  (`codeAt_of_loaded`), when they are the image's (`FnsIn`, which the link step decides).

  ## Main definitions

  * `Verdict`, `FnsIn`

  ## Main results

  * `sound_of_safe`, `codeAt_of_loaded`
-/

import Rv64mc.StepMeet
import MachineChecked.RiscV.Lift.Contract

namespace Rv64mc

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Lift MachineChecked.RiscV.Sym LeanVM.Parameters
  LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- What an accepting run must show of the input `words`: they decode to a proof the verifier accepts. -/
def Verdict (words : List Word) : Prop :=
  ∃ bytecode publicInput proof, decodeInput words = some (bytecode, publicInput, proof) ∧
    verify bytecode publicInput proof = true

/-- A run of the statement's machine is one of SP1's. -/
theorem steps_stepsSp1 {n : Nat} {s t : MachineState} (h : steps n s = some t) : stepsSp1 n s = some t := by
  induction n generalizing s with
  | zero => simpa [steps] using h
  | succ n ih =>
    simp only [steps, Option.bind_eq_some_iff] at h
    obtain ⟨s1, h1, h2⟩ := h
    rw [stepsSp1_succ_of_step (step_stepSp1 h1)]
    exact ih h2

/-- The halting state with `a0 = 0` is SP1's accepting halt. -/
theorem accepted_of_halts {s : MachineState} {n : Nat} (h : Halts s n 0) :
    ∃ t, stepsSp1 n s = some t ∧ Accepted t :=
  let ⟨t, hrun, hec, h5, h10⟩ := h
  ⟨t, steps_stepsSp1 hrun, hec, h5, h10⟩

/-- A run of `stepSp1` as the run `SafeN` speaks of. -/
theorem run_of_stepsSp1 {k : Nat} {s t : MachineState} (h : stepsSp1 k s = some t) :
    Lprog.Ascent.Run (Lprog.Ascent.detStep stepSp1) (fun _ => True) k s (.ok t) := by
  induction k generalizing s with
  | zero => simp at h; subst h; exact .done trivial
  | succ k ih =>
    obtain ⟨s1, h1, h2⟩ := stepsSp1_succ h
    exact .next trivial ((Lprog.Ascent.detStep_of_some h1).2 rfl) (ih h2)

/-- **A safe state's accepting runs give `P`.** -/
theorem SafeN.of_accepted {N k : Nat} {P : Prop} {s t : MachineState} (hs : SafeN (fun _ => True) N P s)
    (hrun : stepsSp1 k s = some t) (hk : k < N) (ha : Accepted t) : P :=
  hs k hk _ (run_of_stepsSp1 hrun) ha

/-- **Soundness from safety**: if every loaded state is safe for the verdict at every budget, the image is
    sound. -/
theorem sound_of_safe {img : Image}
    (h : ∀ words s, Loaded img words s → ∀ N, SafeN (fun _ => True) N (Verdict words) s) : Sound img := by
  intro words s n hl hh
  obtain ⟨t, hrun, ha⟩ := accepted_of_halts hh
  exact SafeN.of_accepted (h words s hl (n + 1)) hrun (Nat.lt_succ_self n) ha

/-- machine-checked's functions `fns` are the image's: each instruction at its address in the image's code. -/
def FnsIn (img : Image) (fns : List Fn) : Prop :=
  ∀ f ∈ fns, ∀ i (h : i < f.prog.length), img.codeAt (f.base + BitVec.ofNat 64 (4 * i)) = some f.prog[i]

/-- A loaded image holds machine-checked's functions, when they are its own. -/
theorem codeAt_of_loaded {img : Image} {fns : List Fn} {words : List Word} {s : MachineState} (hfns : FnsIn img fns)
    (hl : Loaded img words s) : ∀ f ∈ fns, CodeAt f.base (f.prog.map some) s := by
  intro f hf i hi
  rw [hl.2.1]
  simp only [List.length_map] at hi
  rw [hfns f hf i hi]
  simp [hi]

end Rv64mc
