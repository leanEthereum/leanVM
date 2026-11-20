/-
  Rv64mc.Proof.Transcript.Finish

  `Transcript::finish` keeps its contract (`Spec.Transcript.Finish.spec`), over any program holding its template:
  the two comparisons with the lengths the proof's vectors hold, the second computed without a branch.
-/

import Rv64mc.Spec.Transcript.Finish
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Transcript.Finish
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Transcript.Finish

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Transcript Rv64mc.Spec.Transcript.Finish
open Rv64mc.Proof.Transcript
open Rv64mc.Gen.Verifier.Transcript.Transcript.Finish (Link tmpl)

/-- The branchless second test: `Ok`'s niche value exactly when the two words agree. -/
theorem tag_iff (x y : Word) :
    BinOp.ult.eval 0#64 (x ^^^ y) + 18446744073709551615#64 ||| 9#64 =
        BitVec.ofNat 64 Layouts.ResultUnit.Ok.tag ↔ x = y := by
  by_cases h : x = y
  · subst h; simp [BinOp.eval, Layouts.ResultUnit.Ok.tag]
  · have : BitVec.ult 0#64 (x ^^^ y) = true := by
      rw [BitVec.ult_iff_lt, BitVec.lt_def]
      have : x ^^^ y ≠ 0#64 := fun h' => h (by have := congrArg (· ^^^ y) h'; simpa [BitVec.xor_assoc] using this)
      simp only [BitVec.toNat_ofNat, Nat.zero_mod]
      exact Nat.pos_of_ne_zero fun h0 => this (BitVec.eq_of_toNat_eq (by simp [h0]))
    simp [BinOp.eval, this, h, Layouts.ResultUnit.Ok.tag]

theorem finish_run {t : Model.TState} :
    (Model.TM.finish.run t).isSome = true ↔
      t.streamOffset = t.proof.stream.length ∧ t.openingOffset = t.proof.openings.length := by
  simp only [StateT.run, Model.TM.finish]
  split_ifs <;> simp_all

/-- **`Transcript::finish` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (_hL : L.WF p)
    {need : Nat} : spec env p i need := by
  intro t
  rv_auto hp
  all_goals
    obtain ⟨hle, hle', -, hpf, -, hso, hoo, -⟩ := hpre_6
    simp only [Layouts.Transcript.proof, Layouts.Transcript.stream_offset, Layouts.Transcript.opening_offset]
      at hpf hso hoo
    obtain ⟨hlen, hlt⟩ := hpf.stream_len
    obtain ⟨holen, holt⟩ := hpf.openings_len
    rw [hso, hlen] at hc
    rw [finish_run]
  · have : t.streamOffset ≠ t.proof.stream.length := fun h => hc (by rw [h])
    simp [this, Layouts.ResultUnit.Ok.tag]
  · rw [hoo, holen, tag_iff, (ofNat_inj (by omega) (by omega)).1 hc]
    rw [ofNat_inj (by omega) (by omega)]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩

end Rv64mc.Proof.Transcript.Finish
