/-
  LeanVM.Guest.B2C.CplWalkZ

  The completeness walk is sound for every block, and a window's parts cut the function's body
  into consecutive pieces.
-/

module

public import LeanVM.Guest.B2C.CplWalkT

/-!
# The walk, by induction, and the parts of a window

`walk_Z`: the walk of every block from every position gives what `WGood` says, by the cases of
`CplWalk` and `CplWalkT` (mirroring `CheckSound.walk_sound`). `part_split`: part `k` of window `i`
is the body from its start up to where the next part, the next window, or the body ends
(`nextPos`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check LeanVM.Guest.Memory

@[expose] public section

section Walk

variable {κ : ℕ} {L : MemImage κ} {j fp : ℕ} {σ : Val} {es : List Ev} {vs : List V}
  {kfps : List ℕ} {hdr : E × E} {ck : List (Opcode → ℕ)} {segs : List Exec.Seg} {X : CX}
  {wJ : ℕ} {wenv : Trie Sym}

mutual
/-- **The completeness walk is sound** for every block and position. -/
theorem walk_Z (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) :
    ∀ (ss : List Stmt) (st : CW), WGood H ss st
  | [], st => walk_nilZ H st
  | .atom a :: ss, st => walk_atomZ H a ss st (walk_Z H ss)
  | .ite c z n :: ss, st => walk_iteZ H c z n ss st (walk_Z H z) (walk_Z H n) (walk_Z H ss)
  | .match_ v [] :: ss, st => walk_matchNilZ H v ss st
  | .match_ v (a0 :: as) :: ss, st => walk_matchZ H v a0 as ss st (walk_armsZ H (a0 :: as)) (walk_Z H ss)
  | .call f args rets :: ss, st => walk_callZ H f args rets ss st (walk_Z H ss)
  | .callIf c f args :: ss, st => walk_callIfZ H c f args ss st (walk_Z H ss)
  | .dispatch v fs args rets :: ss, st => walk_dispatchZ H v fs args rets ss st (walk_Z H ss)
  | .ret vs' :: ss, st => walk_retZ H vs' ss st

theorem walk_armsZ (H : WH L j fp X segs wJ wenv σ es vs kfps hdr ck) :
    ∀ (arms : List (List Stmt)) (k : ℕ) (hk : k < arms.length) (st : CW), WGood H arms[k] st
  | [], _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | a :: _, 0, _, st => walk_Z H a st
  | _ :: as, k + 1, hk, st => walk_armsZ H as k (by simpa using hk) st
end

end Walk

/-! ## The parts of a window -/

/-- Where part `k` of window `i` ends: at the next part's start, the next window's, or the
body's end. -/
noncomputable def nextPos (j i k : ℕ) : ℕ :=
  bif Nat.blt (k + 1) (nParts j i) then ((certOf j).cutAt i).start + partS j i (k + 1)
  else bif Nat.blt i (certOf j).cuts.length then ((certOf j).cutAt (i + 1)).start
  else (coreOf j).body.length

/-- What `cplWin` checks of where part `k` starts: within its window, after the part before. -/
theorem tbl_partS {j i k : ℕ} (h : cplWin j i k = true) :
    partS j i k ≤ ((certOf j).stmtsAt (coreOf j) i).length ∧
      (k ≠ 0 → partS j i (k - 1) ≤ partS j i k) := by
  unfold cplWin at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := h
  refine ⟨Nat.le_of_ble_eq_true h2, fun hk ↦ ?_⟩
  cases hb : Nat.beq k 0
  · rw [hb, Bool.cond_false] at h1
    exact Nat.le_of_ble_eq_true h1
  · exact absurd (Nat.eq_of_beq_eq_true hb) hk

theorem tbl_drop_split {α : Type} (B : List α) (x m : ℕ) :
    B.drop x = (B.drop x).take m ++ B.drop (x + m) := by
  conv_lhs => rw [← List.take_append_drop m (B.drop x)]
  rw [List.drop_drop]

/-- **Part `k` of window `i`** is the body from its start to `nextPos`. -/
theorem part_split {j i k : ℕ} (hk : k < nParts j i)
    (hle : i < (certOf j).cuts.length → ((certOf j).cutAt i).start ≤ ((certOf j).cutAt (i + 1)).start)
    (hc : ∀ k' < nParts j i, cplWin j i k' = true) :
    (coreOf j).body.drop (((certOf j).cutAt i).start + partS j i k) =
      partStmts j i k ++ (coreOf j).body.drop (nextPos j i k) := by
  have hW : ∀ p, ((certOf j).stmtsAt (coreOf j) i).drop p =
      bif Nat.blt i (certOf j).cuts.length then
        ((coreOf j).body.drop (((certOf j).cutAt i).start + p)).take
          (((certOf j).cutAt (i + 1)).start - ((certOf j).cutAt i).start - p)
      else (coreOf j).body.drop (((certOf j).cutAt i).start + p) := by
    intro p
    unfold Cert.stmtsAt
    cases Nat.blt i (certOf j).cuts.length
    · simp only [Bool.cond_false, List.drop_drop]
    · simp only [Bool.cond_true, List.drop_take, List.drop_drop]
  obtain ⟨hpk, -⟩ := tbl_partS (hc k hk)
  unfold partStmts nextPos
  cases hn : Nat.blt (k + 1) (nParts j i)
  · simp only [Bool.cond_false]
    rw [hW]
    cases hi : Nat.blt i (certOf j).cuts.length
    · simp only [Bool.cond_false, List.drop_length, List.append_nil]
    · simp only [Bool.cond_true]
      have hlt := hle (Nat.blt_eq.mp hi)
      have hpd : partS j i k ≤ ((certOf j).cutAt (i + 1)).start - ((certOf j).cutAt i).start := by
        unfold Cert.stmtsAt at hpk
        rw [hi, Bool.cond_true, List.length_take] at hpk
        omega
      have he : ((certOf j).cutAt i).start + partS j i k +
          (((certOf j).cutAt (i + 1)).start - ((certOf j).cutAt i).start - partS j i k) =
          ((certOf j).cutAt (i + 1)).start := by omega
      conv_lhs => rw [tbl_drop_split _ _ (((certOf j).cutAt (i + 1)).start - ((certOf j).cutAt i).start -
        partS j i k), he]
  · simp only [Bool.cond_true]
    have hk1 : k + 1 < nParts j i := Nat.blt_eq.mp hn
    obtain ⟨hp1, hp0⟩ := tbl_partS (hc (k + 1) hk1)
    have hkk : partS j i k ≤ partS j i (k + 1) := hp0 (Nat.succ_ne_zero k)
    have he : ((certOf j).cutAt i).start + partS j i k + (partS j i (k + 1) - partS j i k) =
        ((certOf j).cutAt i).start + partS j i (k + 1) := by omega
    have ht : (((certOf j).stmtsAt (coreOf j) i).drop (partS j i k)).take (partS j i (k + 1) - partS j i k) =
        ((coreOf j).body.drop (((certOf j).cutAt i).start + partS j i k)).take
          (partS j i (k + 1) - partS j i k) := by
      rw [hW]
      cases hi : Nat.blt i (certOf j).cuts.length
      · simp only [Bool.cond_false]
      · simp only [Bool.cond_true, List.take_take]
        congr 1
        unfold Cert.stmtsAt at hp1
        rw [hi, Bool.cond_true, List.length_take] at hp1
        omega
    rw [ht]
    conv_lhs => rw [tbl_drop_split _ _ (partS j i (k + 1) - partS j i k), he]

end
end LeanVM.Guest.B2C
