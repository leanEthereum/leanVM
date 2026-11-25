/-
  Rv64mc.Final.EndT

  The termination end theorem for the concrete image: `rv64_halts_of_main`, `HaltsSafely image`
  from `main`'s total contract alone. Every other hypothesis of `haltsSafely_of_main` is
  discharged as `rv64_sound` discharges `sound_of_main`'s (`Final/End.lean`): by the kernel's
  checks on the image and the link step's. `loaded_bounded`: `Loaded image words` is satisfiable
  for every input `HaltsSafely` covers, so `HaltsSafely image` is not vacuous by its loader. Until
  `MainSpecT` is proved, it is the one hypothesis.
-/

import Rv64mc.Final.StartT
import Rv64mc.Final.End

namespace Rv64mc

open RiscvZkvm.Rv64 MachineChecked.RiscV.Lift

/-- **Every input `HaltsSafely` covers can be loaded.** -/
theorem loaded_bounded (words : List Word) (h : words.length < maxInputWords) : ∃ s, Loaded image words s :=
  loaded_nonempty words (by have : maxInputWords ≤ inputCapacity := by decide
                            omega)

/-- **Every run of the image on an input of fewer than `2^16` words ends at a verdict**, if `main` keeps its total
    contract. -/
theorem rv64_halts_of_main (hmain : MainSpecT env (liftProg Gen.fns) Gen.Start.link.main.idx need) :
    HaltsSafely image := by
  have hw := wordsIn_of_check words_in_check
  obtain ⟨fn, hg⟩ : ∃ fn, Gen.fns[0]? = some fn := by
    have := Gen.Start.tmpl_eq
    simp only [liftProg, List.getElem?_map, Option.map_eq_some_iff] at this
    obtain ⟨fn, h, -⟩ := this
    exact ⟨fn, h⟩
  have hl := layout_facts
  exact haltsSafely_of_main (fns := Gen.fns) (env := env) (need := need) (by rw [fns_eq]; exact progOk_of_wordsIn hw)
    (by rw [fns_eq]; exact fnsIn_of_wordsIn hw) hg Gen.Start.tmpl_eq (by simpa using entry_check) Gen.Start.wf
    (fun _ h p hp _ => h p hp) (by simpa [env] using next_check) hl.2.2.2
    (by simp only [env, need]; omega) hmain

end Rv64mc

/-- info: 'Rv64mc.rv64_halts_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.rv64_halts_of_main

/-- info: 'Rv64mc.loaded_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.loaded_bounded
