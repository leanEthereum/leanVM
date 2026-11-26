/-
  Rv64mc.Proof.Bus.BusGrindingBits

  `bus_grinding_bits` keeps its contract (`Spec.Bus.BusGrindingBits.spec`) from `grinding_bits`'s: it builds the
  `u128` `1 << mu` in two words (a mask of `mu < 64` selects the word the bit lands in) and tail-calls
  `grinding_bits`. The two words are `1 << mu`'s (`words_eq`, checked for each `mu < 64` by evaluation).
-/

import Rv64mc.Spec.Bus.BusGrindingBits
import Rv64mc.Spec.Transcript.GrindingBits
import Rv64mc.Gen.Tmpl.Verifier.Bus.BusGrindingBits
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Bus.BusGrindingBits

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Bus.BusGrindingBits
open Rv64mc.Gen.Verifier.Bus.BusGrindingBits (Link tmpl)

/-- The code's two words of `1 << mu`, high then low, for each `mu < 64`. -/
theorem words_eq (x : Word) (h : x.toNat < 64) :
    (((x + 0xffffffffffffffc0#64) >>> 63 + 0xffffffffffffffff#64) &&& 1#64 <<< (x &&& 0x3f#64).toNat) ++
        ((0#64 - (x + 0xffffffffffffffc0#64) >>> 63) &&& 1#64 <<< (x &&& 0x3f#64).toNat) =
      1#128 <<< x.toNat := by
  obtain ⟨k, hk, rfl⟩ : ∃ k, k < 64 ∧ x = BitVec.ofNat 64 k := ⟨x.toNat, h, by simp⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  interval_cases k <;> decide

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need : Nat} (hgb : Spec.Transcript.GrindingBits.spec env p L.grindingBits.idx need) : spec env p i need := by
  rv_auto hp with [hL] using [hgb]
  rw [words_eq _ (by assumption)]
  rfl

end Rv64mc.Proof.Bus.BusGrindingBits
