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
# The GKR rounds, loading from a region (G:1108-1131, 1821-1843)

A round record holds its fields `862` words apart (`gkCap`), its cursor at `5·862 = 4310`.

* `gkr_rounds_relIn`: `gkr_rounds__L{n}`, `n ∈ {1, 2}`, on a record `rec` (`5174` words), a
  point `pt` (`43 + n`), a cursor (`4n` words), the window table and the stream (unread); a kernel
  check (`grCheck`) of its body: no call, loads through `rec`, `pt` and the cursor only.
* `loop29_relIn`: iteration `k < K` of `verify_bus_gkr_loop0_loop0` (two rounds) on the record
  `head·g^k` (`5174` words) and the point `ptrow·g^(2k)` (`44`), reading `8` words at the
  record's cursor.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- The rounds' counts of `verify_bus_gkr`'s specializations of `gkr_rounds`. -/
def grCounts : List ℕ := [1, 2]

/-- `gkr_rounds__L{n}`'s pointers and their runs: the record (and the next), the point (with an odd
count's zero), the cursor. -/
def grTbl (n : ℕ) : List (ℕ × ℕ) := [(0, 5174), (1, 43 + n), (2, 4 * n)]

/-- `gkr_rounds__L{n}`'s body, checked: five parameters (the window table and the stream unread), a
`ret` last, no call, its loads through `grTbl n`. -/
noncomputable def grCheck (n : ℕ) : Bool :=
  match coreProgram.find? (lName "gkr_rounds" n) with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) &&
      (match fn.body.getLast? with
        | some (.ret _) => true
        | _ => false) &&
      fn.body.dropLast.all Stmt.flat && fn.body.dropLast.all seqB &&
      fn.body.dropLast.all noCallSB && fn.body.dropLast.all (loadsViaB (grTbl n))
  | none => false

theorem gr_check : ∀ n ∈ grCounts, grCheck n = true := by
  intro n hn
  simp only [grCounts, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl <;> decide +kernel

/-- **`gkr_rounds__L{n}` loads from `R`**, `n ∈ {1, 2}`. -/
theorem gkr_rounds_relIn {n : ℕ} (hn : n ∈ grCounts) {rd : Reader} {R : ℕ → Prop}
    {rec pt cur tabs stream : E} {rets : List E} (hrec : PtrIn R rec 5174)
    (hpt : PtrIn R pt (43 + n)) (hcur : PtrIn R cur (4 * n))
    (h : coreProgram.Rel rd (lName "gkr_rounds" n) [rec, pt, cur, tabs, stream] rets) :
    coreProgram.RelIn rd R (lName "gkr_rounds" n) [rec, pt, cur, tabs, stream] rets := by
  have hck := gr_check n hn
  unfold grCheck at hck
  split at hck
  swap
  · exact absurd hck (by simp)
  rename_i fn hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨hp, hlast⟩, hfl⟩, hseq⟩, hnc⟩, hld⟩ := hck
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
  obtain ⟨p0, p1, p2, -⟩ := hpar
  refine ⟨fun s hs ↦ dispOk_of_noCall (List.all_eq_true.mp hnc s hs),
    loads_via hld fun pb hpb ↦ ?_, fun c hc _ ↦ ?_⟩
  · simp only [grTbl, List.mem_cons, List.not_mem_nil, or_false] at hpb
    rcases hpb with rfl | rfl | rfl
    · rw [p0]; exact hrec
    · rw [p1]; exact hpt
    · rw [p2]; exact hcur
  · exfalso
    obtain ⟨t, ht, -⟩ := List.mem_map.mp hc
    obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht
    rw [callSF_none (List.all_eq_true.mp hnc s hs)] at hst
    exact absurd hst (by simp)

/-! ## `verify_bus_gkr_loop0_loop0` -/

/-- `verify_bus_gkr_loop0_loop0`'s statements before its `ret`. -/
def l29PreK : List Stmt := l29A ++ [.callIf (.n 99) name% «verify_bus_gkr_loop0_loop0» [.n 101,
    .n 1, .n 2, .n 3, .n 4]]

theorem l29Body_pre_eq : l29Body = l29PreK ++ [.ret []] := by
  rw [l29Body, l29PreK, List.append_assoc]; rfl

theorem l29_flat : l29PreK.all Stmt.flat = true := by decide +kernel

theorem l29_noDisp : l29PreK.all noDispB = true := by decide +kernel

theorem l29_seq : l29PreK.all seqB = true := by decide +kernel

theorem l29_loads : l29PreK.all (loadsViaB [(5, 5174), (7, 44), (13, 8)]) = true := by
  decide +kernel

theorem l29_calls : l29PreK.filterMap Main.Stmt.callS =
    [(some (.n 99), name% «verify_bus_gkr_loop0_loop0», [.n 101, .n 1, .n 2, .n 3, .n 4],
        [])] := by decide +kernel

/-- **`verify_bus_gkr_loop0_loop0` loads from `R`**, every iteration `k < K`. -/
theorem loop29_relIn {rd : Reader} {R : ℕ → Prop} {K : ℕ}
    {head ptrow tabs : E} (hh : PtrIn R head (K + 5173)) (hp : PtrIn R ptrow (2 * K + 42))
    (hcur : ∀ k < K, ∀ c, LoadHolds rd (head * gen ^ k) 4310 c → PtrIn R c 8) :
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
    have m5 := hS _ (mem_of_slice (i := 0) (s := .atom (.mul (.n 5) (.n 2) (.n 0))) (by decide +kernel))
    have m6 := hS _ (mem_of_slice (i := 1) (s := .atom (.mul (.n 6) (.n 3) (.n 0))) (by decide +kernel))
    have m7 := hS _ (mem_of_slice (i := 2) (s := .atom (.mul (.n 7) (.n 6) (.n 0))) (by decide +kernel))
    have l13 := hS _ (mem_of_slice (i := 8) (s := .atom (.load (.n 13) (.n 5) 4310))
      (by decide +kernel))
    have c97 := hS _ (mem_of_slice (i := 77) (s := .atom (.const (.n 97) (word 2 0)))
      (by decide +kernel))
    have m98 := hS _ (mem_of_slice (i := 78) (s := .atom (.mul (.n 98) (.n 0) (.n 97)))
      (by decide +kernel))
    have a99 := hS _ (mem_of_slice (i := 79) (s := .atom (.add (.n 99) (.n 98) (.n 1)))
      (by decide +kernel))
    have c100 := hS _ (mem_of_slice (i := 80) (s := .atom (.const (.n 100) (word 2 0)))
      (by decide +kernel))
    have m101 := hS _ (mem_of_slice (i := 81) (s := .atom (.mul (.n 101) (.n 0) (.n 100)))
      (by decide +kernel))
    have hci := hS _ (mem_of_slice (i := 82)
      (s := .callIf (.n 99) name% «verify_bus_gkr_loop0_loop0» [.n 101, .n 1, .n 2, .n 3,
          .n 4]) (by decide +kernel))
    simp only [Fwd.SHolds, Atom.Holds] at m5 m6 m7 l13 c97 m98 a99 c100 m101 hci
    rw [tb_word_gen] at c97 c100
    have e5 : σ (.n 5) = head * gen ^ k := by rw [m5, p0, p2]
    have e7 : σ (.n 7) = ptrow * gen ^ (2 * k) := by rw [m7, m6, p0, p3]; ring
    refine ⟨fun s hs ↦ dispOk_of_noDisp (List.all_eq_true.mp l29_noDisp s hs),
      loads_via l29_loads fun pb hpb ↦ ?_, fun c hc ht ↦ ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
      rcases hpb with rfl | rfl | rfl
      · rw [e5]; exact ptrIn_mul (ptrIn_mono hh (by omega))
      · rw [e7]; exact ptrIn_mul (ptrIn_mono hp (by omega))
      · rw [e5] at l13; exact hcur k hk _ l13
    · rw [filterMap_callSF l29_noDisp, l29_calls] at hc
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
      subst hc
      simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
      have e101 : σ (.n 101) = gen ^ (k + 1) := by rw [m101, c100, p0, pow_succ]
      have e99 : σ (.n 99) = gen ^ (k + 1) + gen ^ K := by rw [a99, m98, c97, p0, p1, pow_succ]
      have hk1 : k + 1 < K := by
        rcases Nat.lt_or_ge (k + 1) K with h' | h'
        · exact h'
        · exfalso
          apply ht
          rw [e99, show k + 1 = K by omega, e_add_eq_zero_iff]
      have hrel := hci.2 ht
      simp only [List.map_cons, List.map_nil, e101, p1, p2, p3, p4] at hrel ⊢
      exact ih (k + 1) hk1 hrel

end
end LeanVM.Guest.B1.Tables
