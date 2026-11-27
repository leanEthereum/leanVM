/-
  LeanVM.Guest.B1.Eq.PlusOne

  B1 for `plus_one_run` (34 specializations).
-/

module

public import LeanVM.Guest.B1.Eq.Meaning
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.B1.Common.Family
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«plus_one_run__L»
meta import LeanVM.Guest.KernelRfl
import LeanVM.Guest.StmtsAppend

/-!
# `plus_one_run`

`plus_one_run__L{n}` writes `out[k] = 1 + src[k]`, `k < n` (`poBlk k`), and returns `0`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Entry `k`. -/
def poBlk (k : ℕ) : List Stmt :=
  [.atom (.const (.n (2 + 3 * k)) (word 1 0)), .atom (.load (.n (3 + 3 * k)) (.n (valf% «plus_one_run» "src")) k),
    .atom (.add (.n (4 + 3 * k)) (.n (2 + 3 * k)) (.n (3 + 3 * k))),
    .atom (.load (.n (4 + 3 * k)) (.n (valf% «plus_one_run» "out")) k)]

/-- The expansion of `plus_one_run__L{n}`. -/
def poBody (n : ℕ) : List Stmt :=
  ((List.range n).map poBlk).flatten ⧺
    [.atom (.const (.n (2 + 3 * n)) (word 0 0)), .ret [.n (2 + 3 * n)]]

/-- What entry `k` asks. -/
def PoOk (rd : Reader) (σ : Val) (k : ℕ) : Prop :=
  σ (.n (2 + 3 * k)) = 1 ∧ LoadHolds rd (σ (.n (valf% «plus_one_run» "src"))) k (σ (.n (3 + 3 * k))) ∧
    σ (.n (4 + 3 * k)) = σ (.n (2 + 3 * k)) + σ (.n (3 + 3 * k)) ∧
    LoadHolds rd (σ (.n (valf% «plus_one_run» "out"))) k (σ (.n (4 + 3 * k)))

theorem holds_poBlk {C : CallRel} {rd : Reader} {σ : Val} (k : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (poBlk k) True kret ↔ PoOk rd σ k := by
  simp only [poBlk, PoOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one]

/-- The function's relation is its meaning, for a body `poBody n`. -/
theorem po_iff (n : ℕ) {f : Fn} (hfind : coreProgram.find? (plusOneRunNames.getD n "") = some f)
    (hparams : f.params = [.n (valf% «plus_one_run» "out"), .n (valf% «plus_one_run» "src")]) (hbody : f.body = poBody n) (rd : Reader)
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

/-- The deployed `plus_one_run__L{n}`, `n ≤ 33`, are the template. -/
private theorem plus_one_run_found :
    coreRunB (idxs% «plus_one_run__L» 0 34) (plusOneRunNames.getD · "")
      (shapeB [.n (valf% «plus_one_run» "out"), .n (valf% «plus_one_run» "src")]
        poBody) = true := by
  decide +kernel

/-- **`plus_one_run`'s core IR is its meaning**, every specialization. -/
theorem plus_one_run_holds : plus_one_run_Spec := fun n hn ↦
  have ⟨_, hf, hp, hb⟩ := coreRunB_shape plus_one_run_found (Nat.lt_succ_of_le hn)
  po_iff n hf hp hb

end
end LeanVM.Guest.B1
