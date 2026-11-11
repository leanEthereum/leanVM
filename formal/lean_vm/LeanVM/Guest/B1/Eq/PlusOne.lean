/-
  LeanVM.Guest.B1.Eq.PlusOne

  B1 for `plus_one_run` (34 specializations).
-/

module

public import LeanVM.Guest.B1.Eq.Meaning

/-!
# `plus_one_run` (G:1022-1025, TRIAGE #27)

`plus_one_run__L{n}` (core function `116 + n`) writes `out[k] = 1 + src[k]`, `k < n` (`poBlk k`),
and returns `0`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Entry `k`. -/
def poBlk (k : ℕ) : List Stmt :=
  [.atom (.const (.n (2 + 3 * k)) (word 1 0)), .atom (.load (.n (3 + 3 * k)) (.n 1) k),
    .atom (.add (.n (4 + 3 * k)) (.n (2 + 3 * k)) (.n (3 + 3 * k))),
    .atom (.load (.n (4 + 3 * k)) (.n 0) k)]

/-- The expansion of `plus_one_run__L{n}`. -/
def poBody (n : ℕ) : List Stmt :=
  ((List.range n).map poBlk).flatten ++
    [.atom (.const (.n (2 + 3 * n)) (word 0 0)), .ret [.n (2 + 3 * n)]]

/-- What entry `k` asks. -/
def PoOk (rd : Reader) (σ : Val) (k : ℕ) : Prop :=
  σ (.n (2 + 3 * k)) = 1 ∧ LoadHolds rd (σ (.n 1)) k (σ (.n (3 + 3 * k))) ∧
    σ (.n (4 + 3 * k)) = σ (.n (2 + 3 * k)) + σ (.n (3 + 3 * k)) ∧
    LoadHolds rd (σ (.n 0)) k (σ (.n (4 + 3 * k)))

theorem holds_poBlk {C : CallRel} {rd : Reader} {σ : Val} (k : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (poBlk k) True kret ↔ PoOk rd σ k := by
  simp only [poBlk, PoOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one]

/-- The function's relation is its meaning, for a body `poBody n`. -/
theorem po_iff (n : ℕ) {f : Fn} (hfind : coreProgram.find? (plusOneRunNames.getD n "") = some f)
    (hparams : f.params = [.n 0, .n 1]) (hbody : f.body = poBody n) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD n "") args rets ↔ MeaningPlusOneRun n rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, poBody]
  simp only [holdsList_append, holdsList_range_flatten n poBlk (fun _ => rfl), holds_poBlk,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_zero]
  constructor
  · rintro ⟨σ, hp, hblk, h0, hret⟩
    subst hp
    refine ⟨⟨(List.range n).map fun k => σ (.n (3 + 3 * k)), by simp, fun k hk => ?_,
      fun k hk => ?_⟩, by rw [← hret, h0]⟩
    · simp only [List.length_map, List.length_range] at hk
      simpa using (hblk k hk).2.1
    · simp only [List.length_map, List.length_range] at hk
      obtain ⟨e2, -, e4, l4⟩ := hblk k hk
      rw [e4, e2] at l4
      simpa using l4
  · intro hm
    obtain ⟨out, src, rfl⟩ : ∃ out src, args = [out, src] := by
      match args, hm with
      | [x, y], _ => exact ⟨x, y, rfl⟩
    obtain ⟨⟨xs, hl, hS, hO⟩, rfl⟩ := hm
    have ifF : ∀ {c : Prop} [Decidable c] {x y : E}, ¬c → (if c then x else y) = y :=
      fun h => by simp [h]
    have ifT : ∀ {c : Prop} [Decidable c] {x y : E}, c → (if c then x else y) = x :=
      fun h => by simp [h]
    let σ : Val := fun v =>
      if v.idx < 2 then [out, src].getD v.idx 0
      else if v.idx < 2 + 3 * n then
        (match (v.idx - 2) % 3 with
          | 0 => 1
          | 1 => xs.getD ((v.idx - 2) / 3) 0
          | _ => 1 + xs.getD ((v.idx - 2) / 3) 0)
      else 0
    have gX : ∀ k (hk : k < xs.length), xs.getD k 0 = xs[k] := fun k hk => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    have ev : ∀ k < n, σ (.n (2 + 3 * k)) = 1 ∧ σ (.n (3 + 3 * k)) = xs.getD k 0 ∧
        σ (.n (4 + 3 * k)) = 1 + xs.getD k 0 := by
      intro k hk
      simp only [σ]
      refine ⟨?_, ?_, ?_⟩ <;> rw [ifF (by omega), ifT (by omega)]
      · rw [show (2 + 3 * k - 2) % 3 = 0 by omega]; rfl
      · rw [show (3 + 3 * k - 2) % 3 = 1 by omega, show (3 + 3 * k - 2) / 3 = k by omega]; rfl
      · rw [show (4 + 3 * k - 2) % 3 = 2 by omega, show (4 + 3 * k - 2) / 3 = k by omega]; rfl
    refine ⟨σ, rfl, fun k hk => ?_, ?_, ?_⟩
    · obtain ⟨f2, f3, f4⟩ := ev k hk
      refine ⟨f2, ?_, by rw [f4, f2, f3], ?_⟩
      · rw [f3, gX k (by omega)]; exact hS k (by omega)
      · rw [f4, gX k (by omega)]
        have := hO k (by simp; omega)
        rw [List.getElem_map] at this
        exact this
    · show σ (.n (2 + 3 * n)) = 0
      simp only [σ]
      rw [ifF (by omega), ifF (by omega)]
    · show [σ (.n (2 + 3 * n))] = [0]
      simp only [σ]
      rw [ifF (by omega), ifF (by omega)]

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem plus_one_run_L0_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 0 "") args rets ↔ MeaningPlusOneRun 0 rd args rets :=
  po_iff 0 (f := Data.core126) (Program.find?_of_indexOf? (j := 126) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L1_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 1 "") args rets ↔ MeaningPlusOneRun 1 rd args rets :=
  po_iff 1 (f := Data.core127) (Program.find?_of_indexOf? (j := 127) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L2_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 2 "") args rets ↔ MeaningPlusOneRun 2 rd args rets :=
  po_iff 2 (f := Data.core128) (Program.find?_of_indexOf? (j := 128) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L3_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 3 "") args rets ↔ MeaningPlusOneRun 3 rd args rets :=
  po_iff 3 (f := Data.core129) (Program.find?_of_indexOf? (j := 129) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L4_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 4 "") args rets ↔ MeaningPlusOneRun 4 rd args rets :=
  po_iff 4 (f := Data.core130) (Program.find?_of_indexOf? (j := 130) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L5_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 5 "") args rets ↔ MeaningPlusOneRun 5 rd args rets :=
  po_iff 5 (f := Data.core131) (Program.find?_of_indexOf? (j := 131) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L6_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 6 "") args rets ↔ MeaningPlusOneRun 6 rd args rets :=
  po_iff 6 (f := Data.core132) (Program.find?_of_indexOf? (j := 132) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L7_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 7 "") args rets ↔ MeaningPlusOneRun 7 rd args rets :=
  po_iff 7 (f := Data.core133) (Program.find?_of_indexOf? (j := 133) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L8_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 8 "") args rets ↔ MeaningPlusOneRun 8 rd args rets :=
  po_iff 8 (f := Data.core134) (Program.find?_of_indexOf? (j := 134) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L9_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 9 "") args rets ↔ MeaningPlusOneRun 9 rd args rets :=
  po_iff 9 (f := Data.core135) (Program.find?_of_indexOf? (j := 135) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L10_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 10 "") args rets ↔ MeaningPlusOneRun 10 rd args rets :=
  po_iff 10 (f := Data.core136) (Program.find?_of_indexOf? (j := 136) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L11_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 11 "") args rets ↔ MeaningPlusOneRun 11 rd args rets :=
  po_iff 11 (f := Data.core137) (Program.find?_of_indexOf? (j := 137) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L12_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 12 "") args rets ↔ MeaningPlusOneRun 12 rd args rets :=
  po_iff 12 (f := Data.core138) (Program.find?_of_indexOf? (j := 138) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L13_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 13 "") args rets ↔ MeaningPlusOneRun 13 rd args rets :=
  po_iff 13 (f := Data.core139) (Program.find?_of_indexOf? (j := 139) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L14_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 14 "") args rets ↔ MeaningPlusOneRun 14 rd args rets :=
  po_iff 14 (f := Data.core140) (Program.find?_of_indexOf? (j := 140) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L15_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 15 "") args rets ↔ MeaningPlusOneRun 15 rd args rets :=
  po_iff 15 (f := Data.core141) (Program.find?_of_indexOf? (j := 141) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L16_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 16 "") args rets ↔ MeaningPlusOneRun 16 rd args rets :=
  po_iff 16 (f := Data.core142) (Program.find?_of_indexOf? (j := 142) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L17_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 17 "") args rets ↔ MeaningPlusOneRun 17 rd args rets :=
  po_iff 17 (f := Data.core143) (Program.find?_of_indexOf? (j := 143) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L18_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 18 "") args rets ↔ MeaningPlusOneRun 18 rd args rets :=
  po_iff 18 (f := Data.core144) (Program.find?_of_indexOf? (j := 144) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L19_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 19 "") args rets ↔ MeaningPlusOneRun 19 rd args rets :=
  po_iff 19 (f := Data.core145) (Program.find?_of_indexOf? (j := 145) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L20_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 20 "") args rets ↔ MeaningPlusOneRun 20 rd args rets :=
  po_iff 20 (f := Data.core146) (Program.find?_of_indexOf? (j := 146) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L21_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 21 "") args rets ↔ MeaningPlusOneRun 21 rd args rets :=
  po_iff 21 (f := Data.core147) (Program.find?_of_indexOf? (j := 147) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L22_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 22 "") args rets ↔ MeaningPlusOneRun 22 rd args rets :=
  po_iff 22 (f := Data.core148) (Program.find?_of_indexOf? (j := 148) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L23_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 23 "") args rets ↔ MeaningPlusOneRun 23 rd args rets :=
  po_iff 23 (f := Data.core149) (Program.find?_of_indexOf? (j := 149) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L24_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 24 "") args rets ↔ MeaningPlusOneRun 24 rd args rets :=
  po_iff 24 (f := Data.core150) (Program.find?_of_indexOf? (j := 150) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L25_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 25 "") args rets ↔ MeaningPlusOneRun 25 rd args rets :=
  po_iff 25 (f := Data.core151) (Program.find?_of_indexOf? (j := 151) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L26_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 26 "") args rets ↔ MeaningPlusOneRun 26 rd args rets :=
  po_iff 26 (f := Data.core152) (Program.find?_of_indexOf? (j := 152) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L27_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 27 "") args rets ↔ MeaningPlusOneRun 27 rd args rets :=
  po_iff 27 (f := Data.core153) (Program.find?_of_indexOf? (j := 153) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L28_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 28 "") args rets ↔ MeaningPlusOneRun 28 rd args rets :=
  po_iff 28 (f := Data.core154) (Program.find?_of_indexOf? (j := 154) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L29_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 29 "") args rets ↔ MeaningPlusOneRun 29 rd args rets :=
  po_iff 29 (f := Data.core155) (Program.find?_of_indexOf? (j := 155) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L30_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 30 "") args rets ↔ MeaningPlusOneRun 30 rd args rets :=
  po_iff 30 (f := Data.core156) (Program.find?_of_indexOf? (j := 156) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L31_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 31 "") args rets ↔ MeaningPlusOneRun 31 rd args rets :=
  po_iff 31 (f := Data.core157) (Program.find?_of_indexOf? (j := 157) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L32_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 32 "") args rets ↔ MeaningPlusOneRun 32 rd args rets :=
  po_iff 32 (f := Data.core158) (Program.find?_of_indexOf? (j := 158) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem plus_one_run_L33_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (plusOneRunNames.getD 33 "") args rets ↔ MeaningPlusOneRun 33 rd args rets :=
  po_iff 33 (f := Data.core159) (Program.find?_of_indexOf? (j := 159) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

/-- **`plus_one_run`'s core IR is its meaning**, every specialization. -/
theorem plus_one_run_holds : plus_one_run_Spec := by
  intro n hn
  interval_cases n
  exacts [plus_one_run_L0_iff, plus_one_run_L1_iff, plus_one_run_L2_iff, plus_one_run_L3_iff, plus_one_run_L4_iff, plus_one_run_L5_iff, plus_one_run_L6_iff, plus_one_run_L7_iff, plus_one_run_L8_iff, plus_one_run_L9_iff, plus_one_run_L10_iff, plus_one_run_L11_iff, plus_one_run_L12_iff, plus_one_run_L13_iff, plus_one_run_L14_iff, plus_one_run_L15_iff, plus_one_run_L16_iff, plus_one_run_L17_iff, plus_one_run_L18_iff, plus_one_run_L19_iff, plus_one_run_L20_iff, plus_one_run_L21_iff, plus_one_run_L22_iff, plus_one_run_L23_iff, plus_one_run_L24_iff, plus_one_run_L25_iff, plus_one_run_L26_iff, plus_one_run_L27_iff, plus_one_run_L28_iff, plus_one_run_L29_iff, plus_one_run_L30_iff, plus_one_run_L31_iff, plus_one_run_L32_iff, plus_one_run_L33_iff]

end
end LeanVM.Guest.B1
