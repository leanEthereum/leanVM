/-
  LeanVM.Guest.B1.Gkr.RoundsIn

  `verify_bus_gkr`'s rounds (`gkr_rounds__L{0,1,2,4,6}`, `verify_bus_gkr_loop0_loop0`) load from any
  region holding their records, points and the round polynomials at the records' cursors.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Loop8
public import LeanVM.Guest.B1.Gkr.Loop29Complete
public import LeanVM.Guest.Data.NameStrings

/-!
# The GKR rounds, loading from a region

A round record is seven consecutive words (`ROUND_SLOTS`), its cursor at `5`.

* `gkr_rounds_relIn`: `gkr_rounds__L{n}`, `n ∈ {0, 1, 2, 4, 6}`, on a record `rec` (`7n + 7`
  words), a point `pt` (`42 + n`) and the window table (unread), reads the `4n` words at the
  record's cursor; a kernel check (`grCheck`) of its body: no call, loads through `rec`, `pt` and
  the cursor only (at `n = 0`, no load at all).
* `loop29_relIn`: iteration `k < K` of `verify_bus_gkr_loop0_loop0` (eight rounds) on the record
  `head·g^(56k)` (`63` words) and the point `ptrow·g^(8k)` (`50`), reading `32` words at the
  record's cursor.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The rounds' counts of `verify_bus_gkr`'s specializations of `gkr_rounds`. -/
def grCounts : List ℕ := [0, 1, 2, 4, 6]

/-- `gkr_rounds__L{n}`'s pointers and their runs: the record, the point, and (at `n ≥ 1`) the
cursor. -/
def grTbl (n : ℕ) : List (ℕ × ℕ) :=
  [(0, 7 * n + 7), (1, 42 + n)] ++ if n = 0 then [] else [(8, 4 * n)]

/-- `gkr_rounds__L{n}`'s body, checked: three parameters (the window table unread), a `ret` last,
no call, its loads through `grTbl n`, its cursor (at `n ≥ 1`) read at `rec·g^5` into `.n 8`. -/
noncomputable def grCheck (n : ℕ) : Bool :=
  match coreProgram.find? (lName "gkr_rounds" n) with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2]) &&
      (match fn.body.getLast? with
        | some (.ret _) => true
        | _ => false) &&
      fn.body.dropLast.all Stmt.flat && fn.body.dropLast.all seqB &&
      fn.body.dropLast.all noCallSB && fn.body.dropLast.all (loadsViaB (grTbl n)) &&
      (n == 0 || fn.body.dropLast.any fun s ↦ tbStmtsEqb [s] [.atom (.load (.n 8) (.n 0) 5)])
  | none => false

theorem gr_check : ∀ n ∈ grCounts, grCheck n = true := by
  intro n hn
  simp only [grCounts, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- **`gkr_rounds__L{n}` loads from `R`**, `n ∈ {0, 1, 2, 4, 6}`. -/
theorem gkr_rounds_relIn {n : ℕ} (hn : n ∈ grCounts) {rd : Reader} {R : ℕ → Prop}
    {rec pt tabs : E} {rets : List E} (hrec : PtrIn R rec (7 * n + 7)) (hpt : PtrIn R pt (42 + n))
    (hcur : ∀ c, LoadHolds rd rec 5 c → PtrIn R c (4 * n))
    (h : coreProgram.Rel rd (lName "gkr_rounds" n) [rec, pt, tabs] rets) :
    coreProgram.RelIn rd R (lName "gkr_rounds" n) [rec, pt, tabs] rets := by
  have hck := gr_check n hn
  unfold grCheck at hck
  split at hck
  swap
  · exact absurd hck (by simp)
  rename_i fn hf
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true] at hck
  obtain ⟨⟨⟨⟨⟨⟨hp, hlast⟩, hfl⟩, hseq⟩, hnc⟩, hld⟩, hs7⟩ := hck
  obtain ⟨vs, hb⟩ : ∃ vs, fn.body = fn.body.dropLast ++ [.ret vs] := by
    split at hlast
    · rename_i vs hl
      exact ⟨vs, (List.dropLast_append_getLast? _ hl).symm⟩
    · exact absurd hlast (by simp)
  have hnl : fn.body.dropLast.all noLoadIte = true := List.all_eq_true.mpr fun s hs ↦
    noLoadIte_of_seqB (List.all_eq_true.mp hseq s hs)
  refine relIn_of_flatRel (hnl := hnl) hf hb hfl h fun σ hpar hh ↦ ?_
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨p0, p1, -⟩ := hpar
  rw [hb, holdsList_append] at hh
  refine ⟨fun s hs ↦ dispOk_of_noCall (List.all_eq_true.mp hnc s hs),
    loads_via hld fun pb hpb ↦ ?_, fun c hc _ ↦ ?_⟩
  · simp only [grTbl, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hpb
    rcases hpb with (rfl | rfl) | hpb
    · rw [p0]; exact hrec
    · rw [p1]; exact hpt
    · split at hpb
      · simp at hpb
      rename_i hn0
      simp only [List.mem_singleton] at hpb
      subst hpb
      obtain ⟨s7, hs7, hs7e⟩ := hs7.resolve_left hn0
      have hs7' : s7 = .atom (.load (.n 8) (.n 0) 5) := by
        have := tbStmtsEqb_sound hs7e; simpa using this
      subst hs7'
      have h7 := holds_of_mem_seq _ hseq hh _ hs7
      simp only [Fwd.SHolds, Atom.Holds] at h7
      rw [p0] at h7; exact hcur _ h7
  · exfalso
    obtain ⟨t, ht, -⟩ := List.mem_map.mp hc
    obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht
    rw [callSF_none (List.all_eq_true.mp hnc s hs)] at hst
    exact absurd hst (by simp)

/-! ## `verify_bus_gkr_loop0_loop0` -/

/-- `verify_bus_gkr_loop0_loop0`'s statements before its `ret`. -/
def l29PreK : List Stmt := l29A ++ [.callIf (.n 337) name% «verify_bus_gkr_loop0_loop0» [.n 339,
    .n 1, .n 2, .n 3, .n 4]]

theorem l29Body_pre_eq : l29Body = l29PreK ++ [.ret []] := by
  rw [l29Body_eq, l29PreK, List.append_assoc]; rfl

theorem l29_flat : l29PreK.all Stmt.flat = true := by decide +kernel

theorem l29_noDisp : l29PreK.all noDispB = true := by decide +kernel

theorem l29_seq : l29PreK.all seqB = true := by decide +kernel

theorem l29_loads : l29PreK.all (loadsViaB [(12, 63), (13, 50), (19, 32)]) = true := by
  decide +kernel

theorem l29_calls : l29PreK.filterMap Main.Stmt.callS =
    [(some (.n 337), name% «verify_bus_gkr_loop0_loop0», [.n 339, .n 1, .n 2, .n 3, .n 4],
        [])] := by decide +kernel

/-- **`verify_bus_gkr_loop0_loop0` loads from `R`**, every iteration `k < K`. -/
theorem loop29_relIn {rd : Reader} {R : ℕ → Prop} {K : ℕ}
    {head ptrow tabs : E} (hh : PtrIn R head (56 * K + 7)) (hp : PtrIn R ptrow (8 * K + 42))
    (hcur : ∀ k < K, ∀ c, LoadHolds rd (head * gen ^ (56 * k)) 5 c → PtrIn R c 32) :
    ∀ d k, k < K → coreProgram.relN rd d name% «verify_bus_gkr_loop0_loop0» [gen ^ k, gen ^ K,
        head, ptrow, tabs] [] →
      coreProgram.RelIn rd R name% «verify_bus_gkr_loop0_loop0» [gen ^ k, gen ^ K, head, ptrow,
          tabs] [] := by
  intro d
  induction d with
  | zero => intro k _ h; exact h.elim
  | succ d ih =>
    intro k hk h
    obtain ⟨fn, hf, hsem⟩ := h
    obtain ⟨fn', hf', hpm, hb⟩ := l29Found
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    refine relIn_of_flat hf (by rw [hb, l29Body_pre_eq]) l29_flat hsem fun σ hpar hhl ↦ ?_
    rw [hpm] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨p0, p1, p2, p3, p4⟩ := hpar
    rw [hb, l29Body_pre_eq, holdsList_append] at hhl
    have hS := holds_of_mem_seq _ l29_seq hhl
    have m5 := hS _ (mem_of_slice (i := 0) (s := .atom (.mul (.n 5) (.n 0) (.n 0))) (by decide +kernel))
    have m6 := hS _ (mem_of_slice (i := 1) (s := .atom (.mul (.n 6) (.n 5) (.n 5))) (by decide +kernel))
    have m7 := hS _ (mem_of_slice (i := 2) (s := .atom (.mul (.n 7) (.n 6) (.n 6))) (by decide +kernel))
    have m8 := hS _ (mem_of_slice (i := 3) (s := .atom (.mul (.n 8) (.n 7) (.n 7))) (by decide +kernel))
    have m9 := hS _ (mem_of_slice (i := 4) (s := .atom (.mul (.n 9) (.n 8) (.n 7))) (by decide +kernel))
    have m10 := hS _ (mem_of_slice (i := 5) (s := .atom (.mul (.n 10) (.n 9) (.n 9))) (by decide +kernel))
    have m11 := hS _ (mem_of_slice (i := 6) (s := .atom (.mul (.n 11) (.n 10) (.n 7))) (by decide +kernel))
    have m12 := hS _ (mem_of_slice (i := 7) (s := .atom (.mul (.n 12) (.n 2) (.n 11))) (by decide +kernel))
    have m13 := hS _ (mem_of_slice (i := 8) (s := .atom (.mul (.n 13) (.n 3) (.n 7))) (by decide +kernel))
    have l19 := hS _ (mem_of_slice (i := 14) (s := .atom (.load (.n 19) (.n 12) 5))
      (by decide +kernel))
    have c335 := hS _ (mem_of_slice (i := 249) (s := .atom (.const (.n 335) (word 2 0)))
      (by decide +kernel))
    have m336 := hS _ (mem_of_slice (i := 250) (s := .atom (.mul (.n 336) (.n 0) (.n 335)))
      (by decide +kernel))
    have a337 := hS _ (mem_of_slice (i := 251) (s := .atom (.add (.n 337) (.n 336) (.n 1)))
      (by decide +kernel))
    have c338 := hS _ (mem_of_slice (i := 252) (s := .atom (.const (.n 338) (word 2 0)))
      (by decide +kernel))
    have m339 := hS _ (mem_of_slice (i := 253) (s := .atom (.mul (.n 339) (.n 0) (.n 338)))
      (by decide +kernel))
    have hci := hS _ (mem_of_slice (i := 254)
      (s := .callIf (.n 337) name% «verify_bus_gkr_loop0_loop0» [.n 339, .n 1, .n 2, .n 3,
          .n 4]) (by decide +kernel))
    simp only [Fwd.SHolds, Atom.Holds] at m5 m6 m7 m8 m9 m10 m11 m12 m13 l19
    simp only [Fwd.SHolds, Atom.Holds] at c335 m336 a337 c338 m339 hci
    rw [tb_word_gen] at c335 c338
    have e12 : σ (.n 12) = head * gen ^ (56 * k) := by
      rw [m12, m11, m10, m9, m8, m7, m6, m5, p0, p2]; ring
    have e13 : σ (.n 13) = ptrow * gen ^ (8 * k) := by rw [m13, m7, m6, m5, p0, p3]; ring
    refine ⟨fun s hs ↦ dispOk_of_noDisp (List.all_eq_true.mp l29_noDisp s hs),
      loads_via l29_loads fun pb hpb ↦ ?_, fun c hc ht ↦ ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
      rcases hpb with rfl | rfl | rfl
      · rw [e12]; exact ptrIn_mul (ptrIn_mono hh (by omega))
      · rw [e13]; exact ptrIn_mul (ptrIn_mono hp (by omega))
      · rw [e12] at l19; exact hcur k hk _ l19
    · rw [filterMap_callSF l29_noDisp, l29_calls] at hc
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
      subst hc
      simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
      have e339 : σ (.n 339) = gen ^ (k + 1) := by rw [m339, c338, p0, pow_succ]
      have e337 : σ (.n 337) = gen ^ (k + 1) + gen ^ K := by rw [a337, m336, c335, p0, p1, pow_succ]
      have hk1 : k + 1 < K := by
        rcases Nat.lt_or_ge (k + 1) K with h' | h'
        · exact h'
        · exfalso
          apply ht
          rw [e337, show k + 1 = K by omega, e_add_eq_zero_iff]
      have hrel := hci.2 ht
      simp only [List.map_cons, List.map_nil, e339, p1, p2, p3, p4] at hrel ⊢
      exact ih (k + 1) hk1 hrel

end
end LeanVM.Guest.B1.Tables
