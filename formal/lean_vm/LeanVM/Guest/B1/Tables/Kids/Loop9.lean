/-
  LeanVM.Guest.B1.Tables.Kids.Loop9

  `__loop8` (the full nibbles of `shared_selector_tables`) and `shared_selector_tables` load from
  any region holding the runs they read.
-/

module

public import LeanVM.Guest.B1.Tables.Kids.Walk
public import LeanVM.Guest.B1.Tables.Kids.Families
public import LeanVM.Guest.B1.Selectors.SharedTables

/-!
# `__loop8` and `shared_selector_tables`, loading from a region

`loop9_relIn`: iteration `k < K` of `__loop8` (`x = g^k`, the end `g^K`) reads the coordinates,
complements and shares at `z·x^4`, `z1·x^4`, `gsq·x^4` (four each) and writes the eq levels at
`eqt·x^32` (`30`) and the `g` table at `gt·x^16` (`16`); by induction on the derivation's depth,
every iteration loads from `R` when the runs `z`, `z1`, `gsq` (`4K`), `eqt` (`32K`), `gt` (`16K`)
lie in `R`.

`shared_selector_tables_relIn`: a run of `n = 4q + r < 64` coordinates: its loop over `q` full
nibbles and its partial nibble `sel_partial_nibble__L{r}` at `q`; the runs `eqt` (`32⌈n/4⌉`),
`gt` (`16⌈n/4⌉`), `z`, `z1`, `gsq` (`n`) in `R`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- Not a dispatch. -/
def noDispB : Stmt → Bool
  | .dispatch .. => false
  | _ => true

theorem dispOk_of_noDisp {σ : Val} {s : Stmt} (h : noDispB s = true) : DispOk σ s := by
  cases s with
  | dispatch => simp [noDispB] at h
  | _ => trivial

theorem callSF_of_noDisp {σ : Val} {s : Stmt} (h : noDispB s = true) :
    Stmt.callSF σ s = Main.Stmt.callS s := by
  cases s with
  | dispatch => simp [noDispB] at h
  | _ => rfl

theorem filterMap_callSF {σ : Val} {pre : List Stmt} (h : pre.all noDispB = true) :
    pre.filterMap (Stmt.callSF σ) = pre.filterMap Main.Stmt.callS :=
  List.filterMap_congr fun s hs ↦ callSF_of_noDisp (List.all_eq_true.mp h s hs)

/-- `__loop8`'s statements before its `ret`. -/
def lpPreC : List Stmt := lpPre ++ [.callIf (.n 74) "__loop8" [.n 76, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]]

theorem lpBody_eq : lpBody = lpPreC ++ [.ret []] := by simp [lpBody, lpPreC]

theorem lp_flat : lpPreC.all Stmt.flat = true := by decide +kernel

theorem lp_noDisp : lpPreC.all noDispB = true := by decide +kernel

/-- The pointers `__loop8` loads through, and their runs. -/
def lpTbl : List (ℕ × ℕ) := [(12, 30), (13, 4), (14, 4), (51, 16), (52, 4)]

theorem lp_loads : lpPreC.all (loadsViaB lpTbl) = true := by decide +kernel

theorem lp_calls : lpPreC.filterMap Main.Stmt.callS =
    [(some (.n 74), "__loop8", [.n 76, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], [])] := by
  decide +kernel

/-- **`__loop8` loads from `R`**, every iteration `k < K`. -/
theorem loop9_relIn {rd : Reader} {R : ℕ → Prop} {K : ℕ} {eqt z z1 gt gsq : E}
    (he : PtrIn R eqt (32 * K)) (hgt : PtrIn R gt (16 * K)) (hz : PtrIn R z (4 * K))
    (hz1 : PtrIn R z1 (4 * K)) (hgs : PtrIn R gsq (4 * K)) :
    ∀ d k, k < K → coreProgram.relN rd d "__loop8" [gen ^ k, gen ^ K, eqt, z, z1, gt, gsq] [] →
      coreProgram.RelIn rd R "__loop8" [gen ^ k, gen ^ K, eqt, z, z1, gt, gsq] [] := by
  intro d
  induction d with
  | zero => intro k _ h; exact h.elim
  | succ d ih =>
    intro k hk h
    obtain ⟨fn, hf, hsem⟩ := h
    obtain ⟨fn', hf', hp, hb⟩ := lpFound
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    refine relIn_of_flat hf (by rw [hb, lpBody_eq]) lp_flat hsem fun σ hpar hh ↦ ?_
    rw [hp] at hpar
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
    obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ := hpar
    rw [hb, lpBody, holdsList_append, holdsList_noRet _ lpPre_noRet] at hh
    obtain ⟨hpre, hcall⟩ := hh
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil, and_true] at hcall
    rw [lpPre, tb_holdsList_append_noRet (by
        simp only [tb_noRetList_append, nbEq_noRet, nbG_noRet]; rfl),
      tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nbEq_noRet]; rfl),
      tb_holdsList_append_noRet (by simp only [tb_noRetList_append, nbEq_noRet]; rfl),
      tb_holdsList_append_noRet rfl] at hpre
    obtain ⟨⟨⟨⟨hh, -⟩, hm⟩, -⟩, ht⟩ := hpre
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hh hm ht
    obtain ⟨h7, h8, h9, h10, h11, h12, h13, h14⟩ := hh
    obtain ⟨h51, h52⟩ := hm
    obtain ⟨h72, h73, h74, h75, h76⟩ := ht
    have ex4 : σ (.n 8) = gen ^ (4 * k) := by rw [h8, h7, p0]; ring
    have ex16 : σ (.n 10) = gen ^ (16 * k) := by rw [h10, h9, h8, h7, p0]; ring
    refine ⟨fun s hs ↦ dispOk_of_noDisp (List.all_eq_true.mp lp_noDisp s hs),
      loads_via lp_loads fun pb hpb ↦ ?_, fun c hc ht ↦ ?_⟩
    · simp only [lpTbl, List.mem_cons, List.not_mem_nil, or_false] at hpb
      rcases hpb with rfl | rfl | rfl | rfl | rfl
      · rw [h12, h11, ex16, p2, mul_assoc, ← pow_add]
        exact ptrIn_mul (ptrIn_mono he (by omega))
      · rw [h13, ex4, p3]; exact ptrIn_mul (ptrIn_mono hz (by omega))
      · rw [h14, ex4, p4]; exact ptrIn_mul (ptrIn_mono hz1 (by omega))
      · rw [h51, ex16, p5]; exact ptrIn_mul (ptrIn_mono hgt (by omega))
      · rw [h52, ex4, p6]; exact ptrIn_mul (ptrIn_mono hgs (by omega))
    · rw [filterMap_callSF lp_noDisp, lp_calls] at hc
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
      subst hc
      simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
      have e76 : σ (.n 76) = gen ^ (k + 1) := by rw [h76, h75, tb_word_gen, p0, pow_succ]
      have e74 : σ (.n 74) = gen ^ (k + 1) + gen ^ K := by
        rw [h74, h73, h72, tb_word_gen, p0, p1, pow_succ]
      have hk1 : k + 1 < K := by
        rcases Nat.lt_or_ge (k + 1) K with h' | h'
        · exact h'
        · exfalso
          have : k + 1 = K := by omega
          apply ht
          rw [e74, this, e_add_eq_zero_iff]
      have hrel := hcall.2 ht
      simp only [List.map_cons, List.map_nil, e76, p1, p2, p3, p4, p5, p6] at hrel ⊢
      exact ih (k + 1) hk1 hrel

end
end LeanVM.Guest.B1.Tables
