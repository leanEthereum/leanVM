/-
  LeanVM.Guest.B1.Eq.EqPrefix

  B1 for `eq_prefix_run` (41 specializations) and `eq_prefix_chain`, its dispatch.
-/

module

public import LeanVM.Guest.B1.Eq.Meaning
public import LeanVM.Guest.B1.Common.Find

/-!
# `eq_prefix_run`, `eq_prefix_chain` (G:992-1008, TRIAGE #25, #26)

`eq_prefix_run__L{n}` (core function `39 + n`) stores the seed at `chain[0]`, then per coordinate
`k < n` (`epBlk k`) reads `a[k]`, `b1[k]`, multiplies the running product by their sum and stores
it at `chain[k + 1]`; it returns `0`. `eq_prefix_chain` range-checks `count_g = g^n` below
`g^41` and dispatches to `eq_prefix_run__L{n}`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The prefix products -/

theorem prefixProd_zero (seed : E) (as bs : List E) : prefixProd seed as bs 0 = seed := by
  simp [prefixProd]

theorem prefixProd_succ (seed : E) (as bs : List E) (j : ℕ) (ha : j < as.length)
    (hb : j < bs.length) :
    prefixProd seed as bs (j + 1) = prefixProd seed as bs j * (as[j] + bs[j]) := by
  rw [prefixProd, prefixProd, List.take_add_one, List.take_add_one, List.getElem?_eq_getElem ha,
    List.getElem?_eq_getElem hb]
  simp only [Option.toList_some]
  rw [List.zipWith_append (by simp; omega), List.foldl_append]
  rfl

/-! ## The template -/

/-- The running product's value after `k` coordinates. -/
def epV : ℕ → ℕ
  | 0 => 1
  | k + 1 => 7 + 4 * k

/-- Coordinate `k`. -/
def epBlk (k : ℕ) : List Stmt :=
  [.atom (.load (.n (4 + 4 * k)) (.n 2) k), .atom (.load (.n (5 + 4 * k)) (.n 3) k),
    .atom (.add (.n (6 + 4 * k)) (.n (4 + 4 * k)) (.n (5 + 4 * k))),
    .atom (.mul (.n (7 + 4 * k)) (.n (epV k)) (.n (6 + 4 * k))),
    .atom (.load (.n (7 + 4 * k)) (.n 0) (k + 1))]

/-- The expansion of `eq_prefix_run__L{n}`. -/
def epBody (n : ℕ) : List Stmt :=
  [.atom (.load (.n 1) (.n 0) 0)] ++ ((List.range n).map epBlk).flatten ++
    [.atom (.const (.n (4 + 4 * n)) (word 0 0)), .ret [.n (4 + 4 * n)]]

/-- What coordinate `k` asks. -/
def EpOk (rd : Reader) (σ : Val) (k : ℕ) : Prop :=
  LoadHolds rd (σ (.n 2)) k (σ (.n (4 + 4 * k))) ∧ LoadHolds rd (σ (.n 3)) k (σ (.n (5 + 4 * k))) ∧
    σ (.n (6 + 4 * k)) = σ (.n (4 + 4 * k)) + σ (.n (5 + 4 * k)) ∧
    σ (.n (7 + 4 * k)) = σ (.n (epV k)) * σ (.n (6 + 4 * k)) ∧
    LoadHolds rd (σ (.n 0)) (k + 1) (σ (.n (7 + 4 * k)))

theorem holds_epBlk {C : CallRel} {rd : Reader} {σ : Val} (k : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (epBlk k) True kret ↔ EpOk rd σ k := by
  simp only [epBlk, EpOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

/-- The function's relation, on the conditions of its blocks. -/
theorem ep_iff (n : ℕ) {f : Fn} (hfind : coreProgram.find? (eqPrefixRunNames.getD n "") = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : f.body = epBody n) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD n "") args rets ↔ MeaningEqPrefixRun n rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, epBody]
  simp only [holdsList_append, holdsList_range_flatten n epBlk (fun _ => rfl), holds_epBlk,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_zero]
  constructor
  · rintro ⟨σ, hp, l0, hblk, h4, hret⟩
    subst hp
    have hv : ∀ j ≤ n, σ (.n (epV j)) = prefixProd (σ (.n 1))
        ((List.range n).map fun k => σ (.n (4 + 4 * k)))
        ((List.range n).map fun k => σ (.n (5 + 4 * k))) j := by
      intro j hj
      induction j with
      | zero => rw [prefixProd_zero]; rfl
      | succ j ih =>
        obtain ⟨-, -, e6, e7, -⟩ := hblk j (by omega)
        rw [prefixProd_succ _ _ _ _ (by simp; omega) (by simp; omega), ← ih (by omega)]
        simp only [List.getElem_map, List.getElem_range]
        rw [epV, e7, e6]
    refine ⟨⟨(List.range n).map fun k => σ (.n (4 + 4 * k)),
      (List.range n).map fun k => σ (.n (5 + 4 * k)), by simp, by simp, fun k hk => ?_,
      fun k hk => ?_, fun j hj => ?_⟩, ?_⟩
    · simp only [List.length_map, List.length_range] at hk
      simpa using (hblk k hk).1
    · simp only [List.length_map, List.length_range] at hk
      simpa using (hblk k hk).2.1
    · rw [← hv j hj]
      cases j with
      | zero => exact l0
      | succ j => exact (hblk j (by omega)).2.2.2.2
    · rw [← hret, h4]
  · intro hm
    obtain ⟨chain, seed, a, b1, rfl⟩ : ∃ chain seed a b1, args = [chain, seed, a, b1] := by
      match args, hm with
      | [c, s, x, y], _ => exact ⟨c, s, x, y, rfl⟩
    obtain ⟨⟨as, bs, ha, hb, hA, hB, hc⟩, rfl⟩ := hm
    let σ : Val := fun v =>
      if v.idx < 4 then [chain, seed, a, b1].getD v.idx 0
      else if v.idx < 4 + 4 * n then
        (match (v.idx - 4) % 4 with
          | 0 => as.getD ((v.idx - 4) / 4) 0
          | 1 => bs.getD ((v.idx - 4) / 4) 0
          | 2 => as.getD ((v.idx - 4) / 4) 0 + bs.getD ((v.idx - 4) / 4) 0
          | _ => prefixProd seed as bs ((v.idx - 4) / 4 + 1))
      else 0
    have e0 : σ (.n 0) = chain := rfl
    have e2 : σ (.n 2) = a := rfl
    have e3 : σ (.n 3) = b1 := rfl
    have ifF : ∀ {c : Prop} [Decidable c] {x y : E}, ¬c → (if c then x else y) = y :=
      fun h => by simp [h]
    have ifT : ∀ {c : Prop} [Decidable c] {x y : E}, c → (if c then x else y) = x :=
      fun h => by simp [h]
    have ev : ∀ k < n, σ (.n (4 + 4 * k)) = as.getD k 0 ∧ σ (.n (5 + 4 * k)) = bs.getD k 0 ∧
        σ (.n (6 + 4 * k)) = as.getD k 0 + bs.getD k 0 ∧
        σ (.n (7 + 4 * k)) = prefixProd seed as bs (k + 1) := by
      intro k hk
      simp only [σ]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ifF (by omega), ifT (by omega)]
      · rw [show (4 + 4 * k - 4) % 4 = 0 by omega, show (4 + 4 * k - 4) / 4 = k by omega]; rfl
      · rw [show (5 + 4 * k - 4) % 4 = 1 by omega, show (5 + 4 * k - 4) / 4 = k by omega]; rfl
      · rw [show (6 + 4 * k - 4) % 4 = 2 by omega, show (6 + 4 * k - 4) / 4 = k by omega]; rfl
      · rw [show (7 + 4 * k - 4) % 4 = 3 by omega, show (7 + 4 * k - 4) / 4 = k by omega]; rfl
    have gA : ∀ k (hk : k < as.length), as.getD k 0 = as[k] := fun k hk => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    have gB : ∀ k (hk : k < bs.length), bs.getD k 0 = bs[k] := fun k hk => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    have hepV : ∀ k < n, σ (.n (epV k)) = prefixProd seed as bs k := by
      intro k hk
      cases k with
      | zero => rw [prefixProd_zero]; rfl
      | succ k => exact (ev k (by omega)).2.2.2
    refine ⟨σ, rfl, ?_, fun k hk => ?_, ?_, ?_⟩
    · have := hc 0 (by omega); rwa [prefixProd_zero] at this
    · obtain ⟨f4, f5, f6, f7⟩ := ev k hk
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [e2, f4, gA k (by omega)]; exact hA k (by omega)
      · rw [e3, f5, gB k (by omega)]; exact hB k (by omega)
      · rw [f6, f4, f5]
      · rw [f7, hepV k hk, f6, prefixProd_succ _ _ _ _ (by omega) (by omega), gA k (by omega), gB k (by omega)]
      · rw [e0, f7]; exact hc (k + 1) (by omega)
    · show σ (.n (4 + 4 * n)) = 0
      simp only [σ]
      rw [ifF (by omega), ifF (by omega)]
    · show [σ (.n (4 + 4 * n))] = [0]
      simp only [σ]
      rw [ifF (by omega), ifF (by omega)]

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L0_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 0 "") args rets ↔ MeaningEqPrefixRun 0 rd args rets :=
  ep_iff 0 (f := fn% «eq_prefix_run__L0») (coreProgram_find?_at (j := idx% «eq_prefix_run__L0») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L1_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 1 "") args rets ↔ MeaningEqPrefixRun 1 rd args rets :=
  ep_iff 1 (f := fn% «eq_prefix_run__L1») (coreProgram_find?_at (j := idx% «eq_prefix_run__L1») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L2_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 2 "") args rets ↔ MeaningEqPrefixRun 2 rd args rets :=
  ep_iff 2 (f := fn% «eq_prefix_run__L2») (coreProgram_find?_at (j := idx% «eq_prefix_run__L2») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L3_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 3 "") args rets ↔ MeaningEqPrefixRun 3 rd args rets :=
  ep_iff 3 (f := fn% «eq_prefix_run__L3») (coreProgram_find?_at (j := idx% «eq_prefix_run__L3») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L4_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 4 "") args rets ↔ MeaningEqPrefixRun 4 rd args rets :=
  ep_iff 4 (f := fn% «eq_prefix_run__L4») (coreProgram_find?_at (j := idx% «eq_prefix_run__L4») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L5_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 5 "") args rets ↔ MeaningEqPrefixRun 5 rd args rets :=
  ep_iff 5 (f := fn% «eq_prefix_run__L5») (coreProgram_find?_at (j := idx% «eq_prefix_run__L5») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L6_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 6 "") args rets ↔ MeaningEqPrefixRun 6 rd args rets :=
  ep_iff 6 (f := fn% «eq_prefix_run__L6») (coreProgram_find?_at (j := idx% «eq_prefix_run__L6») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L7_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 7 "") args rets ↔ MeaningEqPrefixRun 7 rd args rets :=
  ep_iff 7 (f := fn% «eq_prefix_run__L7») (coreProgram_find?_at (j := idx% «eq_prefix_run__L7») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L8_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 8 "") args rets ↔ MeaningEqPrefixRun 8 rd args rets :=
  ep_iff 8 (f := fn% «eq_prefix_run__L8») (coreProgram_find?_at (j := idx% «eq_prefix_run__L8») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L9_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 9 "") args rets ↔ MeaningEqPrefixRun 9 rd args rets :=
  ep_iff 9 (f := fn% «eq_prefix_run__L9») (coreProgram_find?_at (j := idx% «eq_prefix_run__L9») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L10_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 10 "") args rets ↔ MeaningEqPrefixRun 10 rd args rets :=
  ep_iff 10 (f := fn% «eq_prefix_run__L10») (coreProgram_find?_at (j := idx% «eq_prefix_run__L10») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L11_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 11 "") args rets ↔ MeaningEqPrefixRun 11 rd args rets :=
  ep_iff 11 (f := fn% «eq_prefix_run__L11») (coreProgram_find?_at (j := idx% «eq_prefix_run__L11») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L12_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 12 "") args rets ↔ MeaningEqPrefixRun 12 rd args rets :=
  ep_iff 12 (f := fn% «eq_prefix_run__L12») (coreProgram_find?_at (j := idx% «eq_prefix_run__L12») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L13_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 13 "") args rets ↔ MeaningEqPrefixRun 13 rd args rets :=
  ep_iff 13 (f := fn% «eq_prefix_run__L13») (coreProgram_find?_at (j := idx% «eq_prefix_run__L13») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L14_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 14 "") args rets ↔ MeaningEqPrefixRun 14 rd args rets :=
  ep_iff 14 (f := fn% «eq_prefix_run__L14») (coreProgram_find?_at (j := idx% «eq_prefix_run__L14») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L15_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 15 "") args rets ↔ MeaningEqPrefixRun 15 rd args rets :=
  ep_iff 15 (f := fn% «eq_prefix_run__L15») (coreProgram_find?_at (j := idx% «eq_prefix_run__L15») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L16_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 16 "") args rets ↔ MeaningEqPrefixRun 16 rd args rets :=
  ep_iff 16 (f := fn% «eq_prefix_run__L16») (coreProgram_find?_at (j := idx% «eq_prefix_run__L16») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L17_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 17 "") args rets ↔ MeaningEqPrefixRun 17 rd args rets :=
  ep_iff 17 (f := fn% «eq_prefix_run__L17») (coreProgram_find?_at (j := idx% «eq_prefix_run__L17») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L18_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 18 "") args rets ↔ MeaningEqPrefixRun 18 rd args rets :=
  ep_iff 18 (f := fn% «eq_prefix_run__L18») (coreProgram_find?_at (j := idx% «eq_prefix_run__L18») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L19_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 19 "") args rets ↔ MeaningEqPrefixRun 19 rd args rets :=
  ep_iff 19 (f := fn% «eq_prefix_run__L19») (coreProgram_find?_at (j := idx% «eq_prefix_run__L19») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L20_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 20 "") args rets ↔ MeaningEqPrefixRun 20 rd args rets :=
  ep_iff 20 (f := fn% «eq_prefix_run__L20») (coreProgram_find?_at (j := idx% «eq_prefix_run__L20») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L21_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 21 "") args rets ↔ MeaningEqPrefixRun 21 rd args rets :=
  ep_iff 21 (f := fn% «eq_prefix_run__L21») (coreProgram_find?_at (j := idx% «eq_prefix_run__L21») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L22_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 22 "") args rets ↔ MeaningEqPrefixRun 22 rd args rets :=
  ep_iff 22 (f := fn% «eq_prefix_run__L22») (coreProgram_find?_at (j := idx% «eq_prefix_run__L22») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L23_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 23 "") args rets ↔ MeaningEqPrefixRun 23 rd args rets :=
  ep_iff 23 (f := fn% «eq_prefix_run__L23») (coreProgram_find?_at (j := idx% «eq_prefix_run__L23») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L24_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 24 "") args rets ↔ MeaningEqPrefixRun 24 rd args rets :=
  ep_iff 24 (f := fn% «eq_prefix_run__L24») (coreProgram_find?_at (j := idx% «eq_prefix_run__L24») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L25_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 25 "") args rets ↔ MeaningEqPrefixRun 25 rd args rets :=
  ep_iff 25 (f := fn% «eq_prefix_run__L25») (coreProgram_find?_at (j := idx% «eq_prefix_run__L25») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L26_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 26 "") args rets ↔ MeaningEqPrefixRun 26 rd args rets :=
  ep_iff 26 (f := fn% «eq_prefix_run__L26») (coreProgram_find?_at (j := idx% «eq_prefix_run__L26») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L27_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 27 "") args rets ↔ MeaningEqPrefixRun 27 rd args rets :=
  ep_iff 27 (f := fn% «eq_prefix_run__L27») (coreProgram_find?_at (j := idx% «eq_prefix_run__L27») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L28_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 28 "") args rets ↔ MeaningEqPrefixRun 28 rd args rets :=
  ep_iff 28 (f := fn% «eq_prefix_run__L28») (coreProgram_find?_at (j := idx% «eq_prefix_run__L28») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L29_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 29 "") args rets ↔ MeaningEqPrefixRun 29 rd args rets :=
  ep_iff 29 (f := fn% «eq_prefix_run__L29») (coreProgram_find?_at (j := idx% «eq_prefix_run__L29») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L30_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 30 "") args rets ↔ MeaningEqPrefixRun 30 rd args rets :=
  ep_iff 30 (f := fn% «eq_prefix_run__L30») (coreProgram_find?_at (j := idx% «eq_prefix_run__L30») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L31_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 31 "") args rets ↔ MeaningEqPrefixRun 31 rd args rets :=
  ep_iff 31 (f := fn% «eq_prefix_run__L31») (coreProgram_find?_at (j := idx% «eq_prefix_run__L31») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L32_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 32 "") args rets ↔ MeaningEqPrefixRun 32 rd args rets :=
  ep_iff 32 (f := fn% «eq_prefix_run__L32») (coreProgram_find?_at (j := idx% «eq_prefix_run__L32») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L33_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 33 "") args rets ↔ MeaningEqPrefixRun 33 rd args rets :=
  ep_iff 33 (f := fn% «eq_prefix_run__L33») (coreProgram_find?_at (j := idx% «eq_prefix_run__L33») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L34_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 34 "") args rets ↔ MeaningEqPrefixRun 34 rd args rets :=
  ep_iff 34 (f := fn% «eq_prefix_run__L34») (coreProgram_find?_at (j := idx% «eq_prefix_run__L34») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L35_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 35 "") args rets ↔ MeaningEqPrefixRun 35 rd args rets :=
  ep_iff 35 (f := fn% «eq_prefix_run__L35») (coreProgram_find?_at (j := idx% «eq_prefix_run__L35») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L36_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 36 "") args rets ↔ MeaningEqPrefixRun 36 rd args rets :=
  ep_iff 36 (f := fn% «eq_prefix_run__L36») (coreProgram_find?_at (j := idx% «eq_prefix_run__L36») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L37_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 37 "") args rets ↔ MeaningEqPrefixRun 37 rd args rets :=
  ep_iff 37 (f := fn% «eq_prefix_run__L37») (coreProgram_find?_at (j := idx% «eq_prefix_run__L37») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L38_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 38 "") args rets ↔ MeaningEqPrefixRun 38 rd args rets :=
  ep_iff 38 (f := fn% «eq_prefix_run__L38») (coreProgram_find?_at (j := idx% «eq_prefix_run__L38») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L39_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 39 "") args rets ↔ MeaningEqPrefixRun 39 rd args rets :=
  ep_iff 39 (f := fn% «eq_prefix_run__L39») (coreProgram_find?_at (j := idx% «eq_prefix_run__L39») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem eq_prefix_run_L40_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD 40 "") args rets ↔ MeaningEqPrefixRun 40 rd args rets :=
  ep_iff 40 (f := fn% «eq_prefix_run__L40») (coreProgram_find?_at (j := idx% «eq_prefix_run__L40») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

/-- **`eq_prefix_run`'s core IR is its meaning**, every specialization. -/
theorem eq_prefix_run_holds : eq_prefix_run_Spec := by
  intro n hn
  interval_cases n
  exacts [eq_prefix_run_L0_iff, eq_prefix_run_L1_iff, eq_prefix_run_L2_iff, eq_prefix_run_L3_iff, eq_prefix_run_L4_iff, eq_prefix_run_L5_iff, eq_prefix_run_L6_iff, eq_prefix_run_L7_iff, eq_prefix_run_L8_iff, eq_prefix_run_L9_iff, eq_prefix_run_L10_iff, eq_prefix_run_L11_iff, eq_prefix_run_L12_iff, eq_prefix_run_L13_iff, eq_prefix_run_L14_iff, eq_prefix_run_L15_iff, eq_prefix_run_L16_iff, eq_prefix_run_L17_iff, eq_prefix_run_L18_iff, eq_prefix_run_L19_iff, eq_prefix_run_L20_iff, eq_prefix_run_L21_iff, eq_prefix_run_L22_iff, eq_prefix_run_L23_iff, eq_prefix_run_L24_iff, eq_prefix_run_L25_iff, eq_prefix_run_L26_iff, eq_prefix_run_L27_iff, eq_prefix_run_L28_iff, eq_prefix_run_L29_iff, eq_prefix_run_L30_iff, eq_prefix_run_L31_iff, eq_prefix_run_L32_iff, eq_prefix_run_L33_iff, eq_prefix_run_L34_iff, eq_prefix_run_L35_iff, eq_prefix_run_L36_iff, eq_prefix_run_L37_iff, eq_prefix_run_L38_iff, eq_prefix_run_L39_iff, eq_prefix_run_L40_iff]

/-! ## `eq_prefix_chain` -/

theorem find_eq_prefix_chain : coreProgram.find? "eq_prefix_chain" = some fn% «eq_prefix_chain» :=
  coreProgram_find?_at (j := idx% «eq_prefix_chain») rfl

theorem core4_body : Fn.body fn% «eq_prefix_chain» =
    [.atom (.const (.n 5) (word (2 ^ 40) 0)),
      .atom (.rangeCheck (.n 4) (.n 6) (.n 7) (.n 8) (.n 5)),
      .dispatch (.n 4) eqPrefixRunNames [.n 0, .n 1, .n 2, .n 3] [.n 9], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

/-- **`eq_prefix_chain`'s core IR is its meaning.** -/
theorem eq_prefix_chain_holds : eq_prefix_chain_Spec := by
  intro rd args rets
  have hlen : eqPrefixRunNames.length = 41 := rfl
  have hname : ∀ j (hj : j < eqPrefixRunNames.length), eqPrefixRunNames[j] = eqPrefixRunNames.getD j "" :=
    fun j hj => by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  rw [rel_iff_sem find_eq_prefix_chain,
    show Fn.params fn% «eq_prefix_chain» = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl, core4_body]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  rw [word_two_pow (by norm_num)]
  constructor
  · rintro ⟨σ, hp, h5, ⟨r1, r2, r3⟩, ⟨j, hj, hx, hcall⟩, hret⟩
    subst hp
    rw [hname j hj, eq_prefix_run_holds j (by omega)] at hcall
    obtain ⟨hep, h9⟩ := hcall
    refine ⟨hret.symm, ⟨σ (.n 6), σ (.n 7), σ (.n 8), r1, by rw [← h5]; exact r2, r3⟩, j,
      by omega, by rw [hx, gen_pow_eq_ofK], hep⟩
  · intro hm
    obtain ⟨chain, seed, a, b1, cg, rfl⟩ : ∃ chain seed a b1 cg, args = [chain, seed, a, b1, cg] := by
      match args, hm with
      | [c, s, x, y, z], _ => exact ⟨c, s, x, y, z, rfl⟩
    obtain ⟨rfl, ⟨y, t1, t2, r1, r2, r3⟩, n, hn, rfl, hep⟩ := hm
    refine ⟨setl (Val.ofArgs [chain, seed, a, b1, gen ^ n]) 5 [gen ^ 40, y, t1, t2, 0], ?_, ?_, ?_,
      ?_, ?_⟩
    · b1_look
    · b1_look
    · refine ⟨?_, ?_, ?_⟩
      all_goals b1_look
      exacts [r1, r2, r3]
    · refine ⟨n, by rw [hlen]; exact hn, ?_, ?_⟩
      · b1_look
        rw [gen_pow_eq_ofK]
      · rw [hname n (by rw [hlen]; exact hn), eq_prefix_run_holds n (by omega)]
        b1_look
        exact ⟨hep, rfl⟩
    · b1_look

end
end LeanVM.Guest.B1
