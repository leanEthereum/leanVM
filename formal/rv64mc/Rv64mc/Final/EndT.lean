/-
  Rv64mc.Final.EndT

  The termination end theorem for the concrete image: `rv64_halts_of_main`, `HaltsSafely image`
  from `main`'s total contract alone. Every other hypothesis of `haltsSafely_of_main` is
  discharged as `rv64_sound` discharges `sound_of_main`'s (`Final/End.lean`): by the kernel's
  checks on the image and the link step's. The facts `HoldsT`'s precondition `Windows` asks of the
  image (its code between the windows, `NEXT` and the static data in a window) are three more
  such checks. `loaded_bounded`: `Loaded image words` is satisfiable for every input
  `HaltsSafely` covers, so `HaltsSafely image` is not vacuous by its loader. Until `MainSpecT` is
  proved, it is the one hypothesis.
-/

import Rv64mc.Final.StartT
import Rv64mc.Final.End

namespace Rv64mc

open RiscvZkvm.Rv64 MachineChecked.RiscV.Lift Tools.ToLean

/-! ## Where the windows lie in the image -/

kernel_eq code_between_check : (decide (0x78000000 ≤ image.codeBase.toNat) &&
  decide (image.codeBase.toNat + 4 * image.code.length ≤ 0xa0000000)) = true

kernel_eq next_window_check : decide (0xa0000000 ≤ nextAddr.toNat) = true

kernel_eq data_window_check : (image.data.all fun p => inWindow p.1 8) = true

/-- A code word lies in the image's code range. -/
theorem Image.codeAt_range {img : Image} {a : Word} (h : img.codeAt a ≠ none) :
    img.codeBase.toNat ≤ a.toNat ∧ a.toNat < img.codeBase.toNat + 4 * img.code.length := by
  unfold Image.codeAt at h
  split_ifs at h with hc
  · refine ⟨hc.1, ?_⟩
    cases hi : img.code[(a.toNat - img.codeBase.toNat) / 4]? with
    | none => rw [hi] at h; exact absurd rfl h
    | some _ =>
      have := (List.getElem?_eq_some_iff.1 hi).1
      omega
  · exact absurd rfl h

/-- **The image's code lies between the windows.** -/
theorem code_between {a : Word} (h : image.codeAt a ≠ none) : 0x78000000 ≤ a.toNat ∧ a.toNat < 0xa0000000 := by
  have := Image.codeAt_range h
  have hc := code_between_check
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  omega

/-- **The environment's windows**: `NEXT` in the stack window, the heap's end at the first window's end, the static
    data words in a window. -/
theorem env_windows : 0xa0000000 ≤ env.nextAddr.toNat ∧ env.heapEnd.toNat ≤ 0x78000000 ∧
    ∀ q ∈ env.data, inWindow q.1 8 = true := by
  refine ⟨by simpa [env] using next_window_check, by decide, fun q hq => ?_⟩
  simp only [env, List.mem_filter] at hq
  exact List.all_eq_true.1 data_window_check q hq.1

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
    (by simp only [env, need]; omega) env_windows (fun _ h => code_between h) hmain

end Rv64mc

/-- info: 'Rv64mc.rv64_halts_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.rv64_halts_of_main

/-- info: 'Rv64mc.loaded_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.loaded_bounded
