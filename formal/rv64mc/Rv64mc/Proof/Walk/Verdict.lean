/-
  Rv64mc.Proof.Walk.Verdict

  From the Model to the end statement's `Verdict`: an input that `decodeInput` reads, whose bytecode
  `Bytecode::new` prepares and whose proof `verify_execution` accepts, is a `Verdict` (`verdict_of_accept`), by
  `mainVerdictRust_sound`. The decoded leaf indices are words, so each is below `2^64` (`decodeInput_leafIndex`),
  the one hypothesis of the Model's end theorem the input format discharges.
-/

import Rv64mc.Bridge
import Rv64mc.Model.Walk

namespace Rv64mc.Proof.Walk

open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
  LeanVM.Protocol LeanVM.Protocol.Verifier Rv64mc.Model

private theorem bind_run {α β : Type} {x : Reader α} {f : α → Reader β} {ws : List Word} {b : β}
    {ws' : List Word} (h : (x >>= f).run ws = some (b, ws')) :
    ∃ a ws1, x.run ws = some (a, ws1) ∧ (f a).run ws1 = some (b, ws') := by
  rw [StateT.run_bind] at h
  cases h1 : x.run ws with
  | none => rw [h1] at h; cases h
  | some p => rw [h1] at h; exact ⟨p.1, p.2, rfl, h⟩

private theorem pure_run {α : Type} {a b : α} {ws ws' : List Word}
    (h : (pure a : Reader α).run ws = some (b, ws')) : a = b := by
  simp only [StateT.run_pure, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  exact h.1

private theorem readMany_mem {α : Type} {item : Reader α} {P : α → Prop}
    (hi : ∀ ws x ws', item.run ws = some (x, ws') → P x) :
    ∀ n ws xs ws', (readMany item n).run ws = some (xs, ws') → ∀ x ∈ xs, P x
  | 0, _, _, _, h => by rw [← pure_run h]; simp
  | n + 1, _, _, _, h => by
    obtain ⟨x, _, h1, h⟩ := bind_run h
    obtain ⟨xs, _, h2, h⟩ := bind_run h
    rw [← pure_run h]
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hi _ _ _ h1
    · exact readMany_mem hi n _ _ _ h2 y hy

private theorem readList_mem {α : Type} {item : Reader α} {P : α → Prop}
    (hi : ∀ ws x ws', item.run ws = some (x, ws') → P x) :
    ∀ ws xs ws', (readList item).run ws = some (xs, ws') → ∀ x ∈ xs, P x := by
  intro ws xs ws' h
  obtain ⟨n, ws1, -, h⟩ := bind_run h
  exact readMany_mem hi n ws1 xs ws' h

private theorem readOpening_lt (ws : List Word) (o : Opening) (ws' : List Word)
    (h : readOpening.run ws = some (o, ws')) : o.leafIndex < 2 ^ 64 := by
  obtain ⟨n, _, hn, h⟩ := bind_run h
  obtain ⟨_, _, -, h⟩ := bind_run h
  obtain ⟨_, _, -, h⟩ := bind_run h
  obtain ⟨w, _, -, hn⟩ := bind_run hn
  rw [← pure_run h, ← pure_run hn]
  exact w.isLt

/-- **The decoded leaf indices are words.** -/
theorem decodeInput_leafIndex {words : List Word} {bc : List K} {pi : Digest} {pf : Proof}
    (h : decodeInput words = some (bc, pi, pf)) :
    ∀ phase ∈ pf.openings, ∀ o ∈ phase, o.leafIndex < 2 ^ 64 := by
  unfold decodeInput at h
  split at h
  · rename_i value hr
    cases h
    obtain ⟨_, _, -, hr⟩ := bind_run hr
    obtain ⟨_, _, -, hr⟩ := bind_run hr
    obtain ⟨_, _, -, hr⟩ := bind_run hr
    obtain ⟨ops, w4, h4, hr⟩ := bind_run hr
    cases pure_run hr
    exact readList_mem (P := fun phase : List Opening ↦ ∀ o ∈ phase, o.leafIndex < 2 ^ 64)
      (fun ws x ws' hx ↦ readList_mem readOpening_lt ws x ws' hx) _ ops w4 h4
  · cases h

/-- **What `main` accepts is a `Verdict`**: an input `decodeInput` reads, its bytecode prepared by
    `Bytecode::new` and its proof accepted by `verify_execution`. -/
theorem verdict_of_accept {words : List Word} {bc : List K} {pi : Digest} {pf : Proof}
    (hd : decodeInput words = some (bc, pi, pf))
    (h : mainVerdictRust (bc.map BF64.toBitVec) (digestBits pi) pf = true) : Verdict words :=
  ⟨bc, pi, pf, hd, mainVerdictRust_sound bc pi pf (decodeInput_leafIndex hd) h⟩

end Rv64mc.Proof.Walk
