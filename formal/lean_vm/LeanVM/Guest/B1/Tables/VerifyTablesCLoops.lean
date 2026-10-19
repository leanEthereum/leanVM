/-
  LeanVM.Guest.B1.Tables.VerifyTablesCLoops

  `verify_tables`' selector loops backward: from the honest words in memory, each loop's relation.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesSel
public import LeanVM.Guest.B1.Main.LoopsC

/-!
# The selector loops, backward

`sel_complete`: a selector loop (`selPre`, any of the 65) holds from `g^0` to `g^m` once each
iteration's words hold (`SelBody`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem sel_back {self : String} (hok : selOk self = true) {N sb ec zh go sq ka : E} (d j : ℕ)
    (hK : IsInK (gen ^ j * gen + N)) (hB : SelBody rd sb ec zh go sq ka (gen ^ j))
    (hnext : gen ^ j * gen + N ≠ 0 →
      coreProgram.relN rd d self [gen ^ j * gen, N, sb, ec, zh, go, sq, ka] []) :
    coreProgram.relN rd (d + 1) self [gen ^ j, N, sb, ec, zh, go, sq, ka] [] := by
  unfold selOk at hok
  split at hok
  · next f hf =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hpar, hbody⟩ := hok
    obtain ⟨bit, e, z, o, s, l9, hbb, l13, l17, l19, l22, l26, l31⟩ := hB
    set x := gen ^ j
    rw [relN_succ_iff hf]
    refine ⟨setl (Val.ofArgs [x, N, sb, ec, zh, go, sq, ka]) 8 [sb * x, bit, bit * bit, sb * x, ec * x, e,
      word 1 0 0, word 1 0 0 + bit, zh * x, z, word 1 0 0 + bit + z, e * (word 1 0 0 + bit + z), ec * x,
      go * x, o, word 1 0 0, ka * x, sq * (ka * x), s, word 1 0 0, s + word 1 0 0, bit * (s + word 1 0 0),
      word 1 0 0 + bit * (s + word 1 0 0), o * (word 1 0 0 + bit * (s + word 1 0 0)), go * x, word 2 0 0,
      x * word 2 0 0, x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0], by
        simp only [hpar, List.map_cons, List.map_nil]; b1_look, ?_⟩
    rw [stmtsEqb_sound hbody]
    simp only [selPre, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
      List.map_nil]
    b1_look
    simp only [true_and, and_true, word_one, word_gen]
    rw [hbb]
    exact ⟨l9, l9, l13, l17, l19, l22, l26, l31, hK, hnext⟩
  · exact absurd hok (by simp)

/-- **A selector loop** runs its `m` iterations from their honest words. -/
theorem sel_complete {self : String} (hok : selOk self = true) {N sb ec zh go sq ka : E} {m : ℕ}
    (hm0 : 0 < m) (hN : N = gen ^ m) (hB : ∀ j < m, SelBody rd sb ec zh go sq ka (gen ^ j)) :
    coreProgram.Rel rd self [1, N, sb, ec, zh, go, sq, ka] [] :=
  Main.loop_complete hm0 hN hB fun d j hj hK hnext => sel_back hok d j hK hj hnext

end
end LeanVM.Guest.B1.VerifySub
