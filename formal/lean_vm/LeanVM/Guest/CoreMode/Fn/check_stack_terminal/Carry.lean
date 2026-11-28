/-
  LeanVM.Guest.CoreMode.Fn.check_stack_terminal.Carry

  What `verify_sub` certifies of `check_stack_terminal`'s arguments, from its body's slices at an honest
  instance: `g_n` is `g^n`, `n ≤ 24`, at least every table's log height (`vs_gn`, the link shape's statements,
  as `VsRun.shapeOk` without a run); the sent targets' blocks' kappas are tables' log heights (`sent_kappas`).
-/

module

public import LeanVM.Guest.B1.VerifySub.PhLinkShape
public import LeanVM.Guest.B1.Stack.Certify
public import LeanVM.Protocol.Relation.Placement
public import LeanVM.Guest.CoreMode.Fn.check_stack_terminal.Data
import Mathlib.Tactic.IntervalCases
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The table of each column past the memory's two and `q_keccak` (`columnKappas_eq`). -/
def colTabs : List ℕ :=
  List.replicate 7 0 ++ List.replicate 9 1 ++ List.replicate 5 2 ++ List.replicate 10 3 ++ List.replicate 14 4 ++
    List.replicate 68 5

theorem columnKappas_tab (lm : ℕ) (hs : List ℕ) {c : ℕ} (hc : c < colTabs.length) :
    (columnKappas tables lm hs).getD (c + 3) 0 = hs.getD (colTabs.getD c 0) 0 := by
  have e : (List.replicate 7 (hs.getD 0 0) ++ List.replicate 9 (hs.getD 1 0) ++
        List.replicate 5 (hs.getD 2 0) ++ List.replicate 10 (hs.getD 3 0) ++
        List.replicate 14 (hs.getD 4 0)) ++ List.replicate 68 (hs.getD 5 0) = colTabs.map (hs.getD · 0) := by
    simp [colTabs]
  rw [columnKappas_eq, List.append_assoc, e]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp), List.getElem?_map, List.getElem?_eq_getElem hc]
  simp [List.getElem?_eq_getElem hc]

/-- Each listed block is a table's column. -/
theorem sentBlocks_tab : Guest.CoreMode.Own.check_stack_terminal.sentBlocks.all (fun b ↦
    decide (b < Stack.nStkBlocks) && decide (3 ≤ Stack.blockColumn b) &&
      decide (Stack.blockColumn b - 3 < colTabs.length) && decide (colTabs.getD (Stack.blockColumn b - 3) 0 < 6)) =
    true := by
  decide +kernel

/-- **`g_n` from `verify_sub`'s link shape** (statements `375 ..`, `vsShapeAT`): `g^n`, `n ≤ 24`, every table's log
height at most `n`. -/
theorem vs_gn {κ : ℕ} (hκ1 : 1 ≤ κ) (hκ : κ ≤ 32) (L : MemoryImage κ) {bytecode : List K} {σ : Val} {C : CallRel}
    {kret : List E → Prop} (S : SizesOk bytecode L.read σ) (hA : Stmt.HoldsList C L.read σ vsShapeAT True kret) :
    ∃ n ≤ 24, σ (.n 408) = gen ^ n ∧ ∀ t < 6, (vsLayout bytecode σ).tableLogHeights.getD t 0 ≤ n := by
  have hm := memOk_of hκ1 hκ L
  obtain ⟨-, -, -, hthL, -, -, -⟩ := Stack.buildLayout_some S.build
  have hlen : (vsLayout bytecode σ).tableLogHeights.length = 6 := by
    rw [hthL, List.length_zipWith]; simp [vsRows, vsAnnounced, tableLogFloors, nTables]
  obtain ⟨j0, j1, j2, j3, j4, j5, hTH⟩ : ∃ a0 a1 a2 a3 a4 a5,
      (vsLayout bytecode σ).tableLogHeights = [a0, a1, a2, a3, a4, a5] := by
    match h : (vsLayout bytecode σ).tableLogHeights, hlen with
    | [a0, a1, a2, a3, a4, a5], _ => exact ⟨a0, a1, a2, a3, a4, a5, rfl⟩
  have hHe := S.heights
  rw [hTH] at hHe
  simp only [nTables, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.cons.injEq, and_true] at hHe
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := hHe
  have h24 := S.heights24
  rw [hTH] at h24
  have h24' : ∀ t < 6, [j0, j1, j2, j3, j4, j5].getD t 0 ≤ 24 := fun t ht ↦ by
    have := h24 t ht; simpa using this
  have ha0 := h24' 0 (by decide); have ha1 := h24' 1 (by decide); have ha2 := h24' 2 (by decide)
  have ha3 := h24' 3 (by decide); have ha4 := h24' 4 (by decide); have ha5 := h24' 5 (by decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at ha0 ha1 ha2 ha3 ha4 ha5
  simp only [vsShapeAT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hA
  obtain ⟨-, -, -, -, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20,
    s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, -⟩ := hA
  have w24 : word 16777216 0 = gen ^ 24 := word_two_pow (a := 24) (by norm_num)
  have rcN : ∀ {x b t1 t2 k : E}, k = word 16777216 0 →
      (LoadHolds L.read x 0 t1 ∧ k = x * b ∧ LoadHolds L.read b 0 t2) → ∃ e ≤ 24, x = gen ^ e :=
    fun hk h ↦ Digest.rc_const hm (c := 24) (by norm_num) (hk.trans w24) h
  obtain ⟨f0, hf0, x0⟩ := rcN s4 s6
  obtain ⟨f1, hf1, x1⟩ := rcN s8 s10
  obtain ⟨f2, hf2, x2⟩ := rcN s13 s15
  obtain ⟨f3, hf3, x3⟩ := rcN s18 s20
  obtain ⟨f4, hf4, x4⟩ := rcN s23 s25
  obtain ⟨f5, hf5, x5⟩ := rcN s28 s30
  set n0 := f0 + j0 with hn0
  have gn : σ (.n 408) = gen ^ n0 := by rw [s5, x0, q0, ← pow_add]
  have nt : ∀ {f a : ℕ} {x kb : E}, f ≤ 24 → a ≤ 24 → σ (.n 408) = x * kb → x = gen ^ f →
      kb = gen ^ a → n0 = f + a := by
    intro f a x kb hf ha h1 h2 h3
    refine Digest.gen_pow_inj' (by omega) (by omega) ?_
    rw [← gn, h1, h2, h3, pow_add]
  have n1 := nt hf1 ha1 s9 x1 q1
  have n2 := nt hf2 ha2 s14 x2 q2
  have n3 := nt hf3 ha3 s19 x3 q3
  have n4 := nt hf4 ha4 s24 x4 q4
  have n5 := nt hf5 ha5 s29 x5 q5
  -- one height is `n`
  have hz : σ (.n 451) = 0 := by
    have := eq_of_add_zero s34; rw [this, s33, word_zero]
  have hone : n0 = j0 ∨ n0 = j1 ∨ n0 = j2 ∨ n0 = j3 ∨ n0 = j4 ∨ n0 = j5 := by
    have ef : ∀ {t : E} {a : ℕ}, σ (.n 408) + t = 0 → t = gen ^ a → a ≤ 24 → n0 = a := by
      intro t a h ht ha
      exact Digest.gen_pow_inj' (by omega) (by omega) (by rw [← gn, eq_of_add_zero h, ht])
    rw [s32, s27, s22, s17, s12] at hz
    rcases mul_zero_cases hz with hz | hz
    · rcases mul_zero_cases hz with hz | hz
      · rcases mul_zero_cases hz with hz | hz
        · rcases mul_zero_cases hz with hz | hz
          · rcases mul_zero_cases hz with hz | hz
            · exact .inl (ef (s7 ▸ hz) q0 ha0)
            · exact .inr (.inl (ef (s11 ▸ hz) q1 ha1))
          · exact .inr (.inr (.inl (ef (s16 ▸ hz) q2 ha2)))
        · exact .inr (.inr (.inr (.inl (ef (s21 ▸ hz) q3 ha3))))
      · exact .inr (.inr (.inr (.inr (.inl (ef (s26 ▸ hz) q4 ha4)))))
    · exact .inr (.inr (.inr (.inr (.inr (ef (s31 ▸ hz) q5 ha5)))))
  refine ⟨n0, by omega, gn, fun t ht ↦ ?_⟩
  rw [hTH]
  interval_cases t <;> simp <;> omega

/-- **The sent targets' blocks' kappas**: block `b`'s is a table's log height. -/
theorem sent_kappas {bytecode : List K} {rd : Reader} {σ : Val} (S : SizesOk bytecode rd σ) {b : ℕ}
    (hb : b ∈ Guest.CoreMode.Own.check_stack_terminal.sentBlocks) :
    ∃ t < 6, LoadHolds rd (σ (.n (val% «verify_sub» "kaps"))) b
      (gen ^ (vsLayout bytecode σ).tableLogHeights.getD t 0) := by
  have h := List.all_eq_true.mp sentBlocks_tab b hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hbn, h3⟩, hlt⟩, h6⟩ := h
  obtain ⟨p, hp, -, hk⟩ := S.placed.2 b hbn
  have hv := placement_variableCount S.build hp
  obtain ⟨hlmL, -⟩ := Stack.buildLayout_some S.build
  have hc : Stack.blockColumn b = (Stack.blockColumn b - 3) + 3 := by omega
  rw [hc, columnKappas_tab _ _ hlt] at hv
  exact ⟨_, h6, by rw [← hv]; exact hk⟩

end

end LeanVM.Guest.B1.VerifySub
