import Rv64mc.Final.End
import Rv64mc.Final.EndT
import Rv64mc.Final.HaltsSafely
import Rv64mc.Final.MainSpecB

/-!
# The headline for the concrete image

`rv64_safeVerdict`: `SafeVerdict image` from `main`'s two contracts, the partial `MainSpec` (for `Sound`) and the
total `MainSpecT` (for `HaltsSafely`). `rv64_boolVerdict`: the target `BoolVerdict image` from `MainSpec` and
`MainSpecB`, `main`'s total contract stopping with `a0 = 2` only on an input that does not decode
(`Final/MainSpecB.lean`). `BoolVerdict.safeVerdict` and `BoolVerdict.bool` say what it gives: `SafeVerdict`, and on
a well-formed input one run, ending with `a0` equal to `0` or `1`.
-/

namespace Rv64mc

open RiscvZkvm.Rv64 MachineChecked.RiscV.Lift Tools.ToLean

theorem safeVerdict_of {img : Image} (hs : Sound img) (ht : HaltsSafely img) : SafeVerdict img := by
  intro words s hlen hl
  obtain ⟨n, v, hh, hv⟩ := ht words s hlen hl
  exact ⟨n, v, hh, hv, fun h => hs words s n hl (h ▸ hh)⟩

/-- **The headline**, conditional on `main`'s contracts. -/
theorem rv64_safeVerdict (hmain : MainSpec env (liftProg Gen.fns) Gen.Start.link.main.idx need)
    (hmainT : MainSpecT env (liftProg Gen.fns) Gen.Start.link.main.idx need) : SafeVerdict image :=
  safeVerdict_of (rv64_sound hmain).2 (rv64_halts_of_main hmainT)

theorem BoolVerdict.safeVerdict {img : Image} (h : BoolVerdict img) : SafeVerdict img := by
  intro words s hlen hl
  obtain ⟨n, v, hh, hv, hacc⟩ := h words s hlen hl
  exact ⟨n, v, hh, by rcases hv with hv | hv | ⟨hv, -⟩ <;> simp [hv], hacc⟩

/-- On a well-formed input of fewer than `maxInputWords` words, the run ends with `a0` equal to `0` or `1`, and it
    is the only run that ends at the halting `ECALL`. -/
theorem BoolVerdict.bool {img : Image} (h : BoolVerdict img) {words : List Word} {s : MachineState}
    (hlen : words.length < maxInputWords) (hl : Loaded img words s) (hdec : decodeInput words ≠ none) :
    ∃ n v, Halts s n v ∧ (v = 0 ∨ v = 1) ∧ ∀ n' v', Halts s n' v' → n' = n ∧ v' = v := by
  obtain ⟨n, v, hh, hv, -⟩ := h words s hlen hl
  refine ⟨n, v, hh, ?_, fun n' v' h' => ?_⟩
  · rcases hv with hv | hv | ⟨-, hd⟩
    exacts [.inl hv, .inr hv, absurd hd hdec]
  · obtain ⟨rfl, rfl⟩ := Halts.unique hh h'
    exact ⟨rfl, rfl⟩

/-- info: 'Rv64mc.rv64_safeVerdict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.rv64_safeVerdict

/-- **The targeted headline**, conditional on `main`'s partial contract and its total contract with abort only on
    malformed input. -/
theorem rv64_boolVerdict (hmain : MainSpec env (liftProg Gen.fns) Gen.Start.link.main.idx need)
    (hmainB : MainSpecB env (liftProg Gen.fns) Gen.Start.link.main.idx need) : BoolVerdict image := by
  intro words s hlen hl
  obtain ⟨n, v, hh, hv⟩ := rv64_halts_with (Stop := MainStopB)
    (V := fun words v => v = 0 ∨ v = 1 ∨ (v = 2 ∧ decodeInput words = none))
    (fun _ => ⟨.inl rfl, .inr (.inl rfl)⟩) (fun _ _ _ _ _ h => .inr (.inr h)) hmainB hlen hl
  exact ⟨n, v, hh, hv, fun h => (rv64_sound hmain).2 words s n hl (h ▸ hh)⟩

/-- info: 'Rv64mc.rv64_boolVerdict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.rv64_boolVerdict

end Rv64mc
