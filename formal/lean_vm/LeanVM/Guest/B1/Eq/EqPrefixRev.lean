/-
  LeanVM.Guest.B1.Eq.EqPrefixRev

  B1 for `eq_prefix_run_rev` (33 specializations) and `eq_prefix_chain_rev`, its dispatch.
-/

module

public import LeanVM.Guest.B1.Eq.EqPrefix
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«eq_prefix_chain_rev»
import LeanVM.Guest.Data.ValNames.«eq_prefix_run_rev__L»
import LeanVM.Guest.B1.Common.Vc

/-!
# `eq_prefix_run_rev`, `eq_prefix_chain_rev`

`eq_prefix_run_rev__L{n}(chain, out, src, b1)` stores `1` at `chain[0]`, then per coordinate
`k < n` (`rvBlk n k`) reads `a = src[n - 1 - k]`, stores it at `out[k]`, multiplies the running
product by `a + b1[k]` and stores it at `chain[k + 1]`; it returns `0`. So `out` is `src`
reversed and `chain` is `eq_prefix_run`'s from `1` over `out` (`EqPrefixRev`).
`eq_prefix_chain_rev` range-checks `count_g = g^n` below `g^32` and dispatches to
`eq_prefix_run_rev__L{n}`. Coordinate `0` multiplies by the constant `1`, which the compiler
folds: its block has no product.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The meaning -/

/-- `out` holds `src` reversed below `n`, and `chain` the prefix products from `1` of `out`
against `b1`. -/
def EqPrefixRev (rd : Reader) (chain out src b1 : E) (n : ℕ) : Prop :=
  (∀ k < n, ∃ v, LoadHolds rd src (n - 1 - k) v ∧ LoadHolds rd out k v) ∧
    EqPrefix rd chain 1 out b1 n

/-- **`eq_prefix_run_rev(chain, out, src, b1, n)`**: the reversed copy and the prefix products;
it returns `0`. -/
def MeaningEqPrefixRunRev (n : ℕ) (rd : Reader) : List E → List E → Prop
  | [chain, out, src, b1], rets => EqPrefixRev rd chain out src b1 n ∧ rets = [0]
  | _, _ => False

/-- The specializations' names, `eq_prefix_run_rev__L{n}`, `n ≤ 32` (`eq_prefix_chain_rev`'s
dispatch list). -/
def eqPrefixRunRevNames : List String :=
    ["eq_prefix_run_rev__L0", "eq_prefix_run_rev__L1", "eq_prefix_run_rev__L2",
      "eq_prefix_run_rev__L3", "eq_prefix_run_rev__L4", "eq_prefix_run_rev__L5",
      "eq_prefix_run_rev__L6", "eq_prefix_run_rev__L7", "eq_prefix_run_rev__L8",
      "eq_prefix_run_rev__L9", "eq_prefix_run_rev__L10", "eq_prefix_run_rev__L11",
      "eq_prefix_run_rev__L12", "eq_prefix_run_rev__L13", "eq_prefix_run_rev__L14",
      "eq_prefix_run_rev__L15", "eq_prefix_run_rev__L16", "eq_prefix_run_rev__L17",
      "eq_prefix_run_rev__L18", "eq_prefix_run_rev__L19", "eq_prefix_run_rev__L20",
      "eq_prefix_run_rev__L21", "eq_prefix_run_rev__L22", "eq_prefix_run_rev__L23",
      "eq_prefix_run_rev__L24", "eq_prefix_run_rev__L25", "eq_prefix_run_rev__L26",
      "eq_prefix_run_rev__L27", "eq_prefix_run_rev__L28", "eq_prefix_run_rev__L29",
      "eq_prefix_run_rev__L30", "eq_prefix_run_rev__L31", "eq_prefix_run_rev__L32"]

/-- `eq_prefix_run_rev__L{n}`'s core IR is its meaning, `n ≤ 32`. -/
def eq_prefix_run_rev_Spec : Prop :=
  ∀ n ≤ 32, ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd (eqPrefixRunRevNames.getD n "") args rets ↔
      MeaningEqPrefixRunRev n rd args rets

/-- **`eq_prefix_chain_rev(chain, out, src, b1, count_g)`**: `count_g = g^n` with `n < 33`
(`assert log(count_g) < COUNT_BITS`, its range check's memory facts kept), the reversed copy and
the prefix products up to `n`. -/
def MeaningEqPrefixChainRev (rd : Reader) : List E → List E → Prop
  | [chain, out, src, b1, cg], rets =>
      rets = [] ∧ RangeChecked rd cg (gen ^ 32) ∧ ∃ n < 33, cg = gen ^ n ∧
        EqPrefixRev rd chain out src b1 n
  | _, _ => False

/-- `eq_prefix_chain_rev`'s core IR is its meaning. -/
def eq_prefix_chain_rev_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "eq_prefix_chain_rev" args rets ↔ MeaningEqPrefixChainRev rd args rets

/-! ## The template -/

/-- The word read at coordinate `k`. -/
def rvA : ℕ → ℕ
  | 0 => 5
  | k + 1 => 8 + 4 * k

/-- The word of `b1` at coordinate `k`. -/
def rvB : ℕ → ℕ
  | 0 => 6
  | k + 1 => 9 + 4 * k

/-- The running product's value after `k` coordinates. -/
def rvV : ℕ → ℕ
  | 0 => 4
  | k + 1 => 7 + 4 * k

/-- Coordinate `k` of `eq_prefix_run_rev__L{n}`. -/
def rvBlk (n : ℕ) : ℕ → List Stmt
  | 0 => [.atom (.load (.n 5) (.n (valf% «eq_prefix_run_rev» "src")) (n - 1 - 0)), .atom (.load (.n 5) (.n (valf% «eq_prefix_run_rev» "out")) 0),
      .atom (.load (.n 6) (.n (valf% «eq_prefix_run_rev» "b1")) 0), .atom (.add (.n 7) (.n 5) (.n 6)),
      .atom (.load (.n 7) (.n (valf% «eq_prefix_run_rev» "chain")) (0 + 1))]
  | k + 1 => [.atom (.load (.n (8 + 4 * k)) (.n (valf% «eq_prefix_run_rev» "src")) (n - 1 - (k + 1))),
      .atom (.load (.n (8 + 4 * k)) (.n (valf% «eq_prefix_run_rev» "out")) (k + 1)), .atom (.load (.n (9 + 4 * k)) (.n (valf% «eq_prefix_run_rev» "b1")) (k + 1)),
      .atom (.add (.n (10 + 4 * k)) (.n (8 + 4 * k)) (.n (9 + 4 * k))),
      .atom (.mul (.n (7 + 4 * (k + 1))) (.n (7 + 4 * k)) (.n (10 + 4 * k))),
      .atom (.load (.n (7 + 4 * (k + 1))) (.n (valf% «eq_prefix_run_rev» "chain")) (k + 1 + 1))]

/-- The expansion of `eq_prefix_run_rev__L{n}`. -/
def rvBody (n : ℕ) : List Stmt :=
  [.atom (.const (.n (valf% «eq_prefix_run_rev» "s0#0")) (word 1 0)), .atom (.load (.n (valf% «eq_prefix_run_rev» "s0#0")) (.n (valf% «eq_prefix_run_rev» "chain")) 0)] ++
    ((List.range n).map (rvBlk n)).flatten ++ [.atom (.const (.n (rvA n)) (word 0 0)), .ret [.n (rvA n)]]

/-- The sum `a + b1[k]` at coordinate `k` (coordinate `0`'s is its product). -/
def rvS : ℕ → ℕ
  | 0 => 7
  | k + 1 => 10 + 4 * k

/-- What coordinate `k` asks. -/
def RvOk (rd : Reader) (σ : Val) (n k : ℕ) : Prop :=
  LoadHolds rd (σ (.n (valf% «eq_prefix_run_rev» "src"))) (n - 1 - k) (σ (.n (rvA k))) ∧ LoadHolds rd (σ (.n (valf% «eq_prefix_run_rev» "out"))) k (σ (.n (rvA k))) ∧
    LoadHolds rd (σ (.n (valf% «eq_prefix_run_rev» "b1"))) k (σ (.n (rvB k))) ∧
    σ (.n (rvS k)) = σ (.n (rvA k)) + σ (.n (rvB k)) ∧
    σ (.n (rvV (k + 1))) = σ (.n (rvV k)) * σ (.n (rvS k)) ∧
    LoadHolds rd (σ (.n (valf% «eq_prefix_run_rev» "chain"))) (k + 1) (σ (.n (rvV (k + 1))))

theorem rvBlk_noRet (n k : ℕ) : Stmt.noRetList (rvBlk n k) = true := by
  cases k <;> rfl

theorem holds_rvBlk {C : CallRel} {rd : Reader} {σ : Val} (h4 : σ (.n (valf% «eq_prefix_run_rev» "s0#0")) = 1) (n k : ℕ)
    (kret : List E → Prop) : Stmt.HoldsList C rd σ (rvBlk n k) True kret ↔ RvOk rd σ n k := by
  cases k with
  | zero =>
    simp only [rvBlk, RvOk, rvA, rvB, rvV, rvS, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
      h4, one_mul, true_and]
  | succ k =>
    simp only [rvBlk, RvOk, rvA, rvB, rvV, rvS, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

/-- The function's relation, on the conditions of its blocks. -/
theorem rv_iff (n : ℕ) {f : Fn} (hfind : coreProgram.find? (eqPrefixRunRevNames.getD n "") = some f)
    (hparams : f.params = [.n (valf% «eq_prefix_run_rev» "chain"), .n (valf% «eq_prefix_run_rev» "out"), .n (valf% «eq_prefix_run_rev» "src"), .n (valf% «eq_prefix_run_rev» "b1")]) (hbody : f.body = rvBody n) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD n "") args rets ↔
      MeaningEqPrefixRunRev n rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, rvBody]
  simp only [holdsList_append, holdsList_range_flatten n (rvBlk n) (rvBlk_noRet n),
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_zero, word_one]
  constructor
  · rintro ⟨σ, hp, h4, l0, hblk, hr, hret⟩
    subst hp
    have hblk' : ∀ k < n, RvOk rd σ n k := fun k hk => (holds_rvBlk h4 n k _).mp (hblk k hk)
    let as := (List.range n).map fun k => σ (.n (rvA k))
    let bs := (List.range n).map fun k => σ (.n (rvB k))
    have hv : ∀ j ≤ n, σ (.n (rvV j)) = prefixProd 1 as bs j := by
      intro j hj
      induction j with
      | zero => rw [prefixProd_zero]; exact h4
      | succ j ih =>
        obtain ⟨-, -, -, e5, e6, -⟩ := hblk' j (by omega)
        rw [prefixProd_succ _ _ _ _ (by simp [as]; omega) (by simp [bs]; omega), ← ih (by omega)]
        simp only [as, bs, List.getElem_map, List.getElem_range]
        rw [e6, e5]
    refine ⟨⟨fun k hk => ⟨_, (hblk' k hk).1, (hblk' k hk).2.1⟩, as, bs, by simp [as],
      by simp [bs], fun k hk => ?_, fun k hk => ?_, fun j hj => ?_⟩, ?_⟩
    · simp only [as, List.length_map, List.length_range] at hk
      simpa [as] using (hblk' k hk).2.1
    · simp only [bs, List.length_map, List.length_range] at hk
      simpa [bs] using (hblk' k hk).2.2.1
    · rw [← hv j hj]
      cases j with
      | zero => exact l0
      | succ j => exact (hblk' j (by omega)).2.2.2.2.2
    · rw [← hret, hr]
  · intro hm
    obtain ⟨chain, out, src, b1, rfl⟩ : ∃ chain out src b1, args = [chain, out, src, b1] := by
      match args, hm with
      | [c, o, s, b], _ => exact ⟨c, o, s, b, rfl⟩
    obtain ⟨⟨hC, as, bs, ha, hb, hA, hB, hc⟩, rfl⟩ := hm
    let σ : Val := fun v =>
      if v.idx < 4 then [chain, out, src, b1].getD v.idx 0
      else if v.idx = 4 then 1
      else if v.idx < 4 + 4 * n then
        (if (v.idx - 4) % 4 = 0 then as.getD ((v.idx - 4) / 4) 0
        else if (v.idx - 4) % 4 = 1 then
          (if (v.idx - 4) / 4 = 0 then as.getD 0 0 else bs.getD ((v.idx - 4) / 4) 0)
        else if (v.idx - 4) % 4 = 2 then
          (if (v.idx - 4) / 4 = 0 then bs.getD 0 0
          else as.getD ((v.idx - 4) / 4) 0 + bs.getD ((v.idx - 4) / 4) 0)
        else prefixProd 1 as bs ((v.idx - 4) / 4 + 1))
      else 0
    have e0 : σ (.n (valf% «eq_prefix_run_rev» "chain")) = chain := rfl
    have e1 : σ (.n (valf% «eq_prefix_run_rev» "out")) = out := rfl
    have e2 : σ (.n (valf% «eq_prefix_run_rev» "src")) = src := rfl
    have e3 : σ (.n (valf% «eq_prefix_run_rev» "b1")) = b1 := rfl
    have e4 : σ (.n (valf% «eq_prefix_run_rev» "s0#0")) = 1 := rfl
    have ifF : ∀ {c : Prop} [Decidable c] {x y : E}, ¬c → (if c then x else y) = y :=
      fun h => by simp [h]
    have ifT : ∀ {c : Prop} [Decidable c] {x y : E}, c → (if c then x else y) = x :=
      fun h => by simp [h]
    have gA : ∀ k (hk : k < as.length), as.getD k 0 = as[k] := fun k hk => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    have gB : ∀ k (hk : k < bs.length), bs.getD k 0 = bs[k] := fun k hk => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    have ev : ∀ k < n, σ (.n (rvA k)) = as.getD k 0 ∧ σ (.n (rvB k)) = bs.getD k 0 ∧
        σ (.n (rvS k)) = as.getD k 0 + bs.getD k 0 ∧
        σ (.n (rvV (k + 1))) = prefixProd 1 as bs (k + 1) := by
      intro k hk
      cases k with
      | zero =>
        simp only [rvA, rvB, rvS, rvV, σ]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [ifF (by omega), ifF (by omega), ifT (by omega)]
          rw [show (5 - 4) % 4 = 1 by omega, show (5 - 4) / 4 = 0 by omega]; simp
        · rw [ifF (by omega), ifF (by omega), ifT (by omega)]
          rw [show (6 - 4) % 4 = 2 by omega, show (6 - 4) / 4 = 0 by omega]; simp
        · rw [ifF (by omega), ifF (by omega), ifT (by omega)]
          rw [show (7 - 4) % 4 = 3 by omega, show (7 - 4) / 4 = 0 by omega]
          simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.zero_add]
          rw [prefixProd_succ _ _ _ _ (by omega) (by omega), prefixProd_zero, one_mul,
            gA 0 (by omega), gB 0 (by omega)]
        · rw [ifF (by omega), ifF (by omega), ifT (by omega)]
          rw [show (7 - 4) % 4 = 3 by omega, show (7 - 4) / 4 = 0 by omega]
          simp
      | succ k =>
        simp only [rvA, rvB, rvS, rvV, σ]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ifF (by omega), ifF (by omega), ifT (by omega)]
        · rw [show (8 + 4 * k - 4) % 4 = 0 by omega, show (8 + 4 * k - 4) / 4 = k + 1 by omega]
          simp
        · rw [show (9 + 4 * k - 4) % 4 = 1 by omega, show (9 + 4 * k - 4) / 4 = k + 1 by omega]
          simp
        · rw [show (10 + 4 * k - 4) % 4 = 2 by omega, show (10 + 4 * k - 4) / 4 = k + 1 by omega]
          simp
        · rw [show (7 + 4 * (k + 1) - 4) % 4 = 3 by omega,
            show (7 + 4 * (k + 1) - 4) / 4 = k + 1 by omega]
          simp
    have hvv : ∀ k ≤ n, σ (.n (rvV k)) = prefixProd 1 as bs k := by
      intro k hk
      cases k with
      | zero => rw [prefixProd_zero]; rfl
      | succ k => exact (ev k (by omega)).2.2.2
    have hret : σ (.n (rvA n)) = 0 := by
      cases n with
      | zero => rfl
      | succ m =>
        simp only [rvA, σ]
        rw [ifF (by omega), ifF (by omega), ifF (by omega)]
    refine ⟨σ, rfl, e4, ?_, fun k hk => (holds_rvBlk e4 n k _).mpr ?_, hret, by rw [hret]⟩
    · have := hc 0 (by omega); rwa [prefixProd_zero] at this
    · obtain ⟨f4, f5, f6, f7⟩ := ev k hk
      obtain ⟨v, hsv, hov⟩ := hC k hk
      have hv : v = as.getD k 0 := by
        rw [gA k (by omega)]; exact loadHolds_unique hov (hA k (by omega))
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [e2, f4, ← hv]; exact hsv
      · rw [e1, f4, gA k (by omega)]; exact hA k (by omega)
      · rw [e3, f5, gB k (by omega)]; exact hB k (by omega)
      · rw [f6, f4, f5]
      · rw [f7, hvv k (by omega), f6, prefixProd_succ _ _ _ _ (by omega) (by omega),
          gA k (by omega), gB k (by omega)]
      · rw [e0, f7]; exact hc (k + 1) (by omega)

/-! ## The specializations -/

theorem eq_prefix_run_rev_L0_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 0 "") args rets ↔
      MeaningEqPrefixRunRev 0 rd args rets :=
  rv_iff 0 (f := fn% «eq_prefix_run_rev__L0»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L0») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L1_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 1 "") args rets ↔
      MeaningEqPrefixRunRev 1 rd args rets :=
  rv_iff 1 (f := fn% «eq_prefix_run_rev__L1»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L1») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L2_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 2 "") args rets ↔
      MeaningEqPrefixRunRev 2 rd args rets :=
  rv_iff 2 (f := fn% «eq_prefix_run_rev__L2»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L2») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L3_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 3 "") args rets ↔
      MeaningEqPrefixRunRev 3 rd args rets :=
  rv_iff 3 (f := fn% «eq_prefix_run_rev__L3»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L3») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L4_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 4 "") args rets ↔
      MeaningEqPrefixRunRev 4 rd args rets :=
  rv_iff 4 (f := fn% «eq_prefix_run_rev__L4»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L4») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L5_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 5 "") args rets ↔
      MeaningEqPrefixRunRev 5 rd args rets :=
  rv_iff 5 (f := fn% «eq_prefix_run_rev__L5»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L5») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L6_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 6 "") args rets ↔
      MeaningEqPrefixRunRev 6 rd args rets :=
  rv_iff 6 (f := fn% «eq_prefix_run_rev__L6»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L6») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L7_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 7 "") args rets ↔
      MeaningEqPrefixRunRev 7 rd args rets :=
  rv_iff 7 (f := fn% «eq_prefix_run_rev__L7»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L7») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L8_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 8 "") args rets ↔
      MeaningEqPrefixRunRev 8 rd args rets :=
  rv_iff 8 (f := fn% «eq_prefix_run_rev__L8»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L8») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L9_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 9 "") args rets ↔
      MeaningEqPrefixRunRev 9 rd args rets :=
  rv_iff 9 (f := fn% «eq_prefix_run_rev__L9»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L9») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L10_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 10 "") args rets ↔
      MeaningEqPrefixRunRev 10 rd args rets :=
  rv_iff 10 (f := fn% «eq_prefix_run_rev__L10»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L10») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L11_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 11 "") args rets ↔
      MeaningEqPrefixRunRev 11 rd args rets :=
  rv_iff 11 (f := fn% «eq_prefix_run_rev__L11»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L11») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L12_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 12 "") args rets ↔
      MeaningEqPrefixRunRev 12 rd args rets :=
  rv_iff 12 (f := fn% «eq_prefix_run_rev__L12»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L12») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L13_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 13 "") args rets ↔
      MeaningEqPrefixRunRev 13 rd args rets :=
  rv_iff 13 (f := fn% «eq_prefix_run_rev__L13»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L13») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L14_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 14 "") args rets ↔
      MeaningEqPrefixRunRev 14 rd args rets :=
  rv_iff 14 (f := fn% «eq_prefix_run_rev__L14»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L14») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L15_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 15 "") args rets ↔
      MeaningEqPrefixRunRev 15 rd args rets :=
  rv_iff 15 (f := fn% «eq_prefix_run_rev__L15»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L15») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L16_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 16 "") args rets ↔
      MeaningEqPrefixRunRev 16 rd args rets :=
  rv_iff 16 (f := fn% «eq_prefix_run_rev__L16»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L16») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L17_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 17 "") args rets ↔
      MeaningEqPrefixRunRev 17 rd args rets :=
  rv_iff 17 (f := fn% «eq_prefix_run_rev__L17»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L17») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L18_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 18 "") args rets ↔
      MeaningEqPrefixRunRev 18 rd args rets :=
  rv_iff 18 (f := fn% «eq_prefix_run_rev__L18»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L18») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L19_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 19 "") args rets ↔
      MeaningEqPrefixRunRev 19 rd args rets :=
  rv_iff 19 (f := fn% «eq_prefix_run_rev__L19»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L19») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L20_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 20 "") args rets ↔
      MeaningEqPrefixRunRev 20 rd args rets :=
  rv_iff 20 (f := fn% «eq_prefix_run_rev__L20»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L20») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L21_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 21 "") args rets ↔
      MeaningEqPrefixRunRev 21 rd args rets :=
  rv_iff 21 (f := fn% «eq_prefix_run_rev__L21»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L21») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L22_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 22 "") args rets ↔
      MeaningEqPrefixRunRev 22 rd args rets :=
  rv_iff 22 (f := fn% «eq_prefix_run_rev__L22»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L22») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L23_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 23 "") args rets ↔
      MeaningEqPrefixRunRev 23 rd args rets :=
  rv_iff 23 (f := fn% «eq_prefix_run_rev__L23»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L23») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L24_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 24 "") args rets ↔
      MeaningEqPrefixRunRev 24 rd args rets :=
  rv_iff 24 (f := fn% «eq_prefix_run_rev__L24»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L24») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L25_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 25 "") args rets ↔
      MeaningEqPrefixRunRev 25 rd args rets :=
  rv_iff 25 (f := fn% «eq_prefix_run_rev__L25»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L25») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L26_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 26 "") args rets ↔
      MeaningEqPrefixRunRev 26 rd args rets :=
  rv_iff 26 (f := fn% «eq_prefix_run_rev__L26»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L26») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L27_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 27 "") args rets ↔
      MeaningEqPrefixRunRev 27 rd args rets :=
  rv_iff 27 (f := fn% «eq_prefix_run_rev__L27»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L27») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L28_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 28 "") args rets ↔
      MeaningEqPrefixRunRev 28 rd args rets :=
  rv_iff 28 (f := fn% «eq_prefix_run_rev__L28»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L28») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L29_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 29 "") args rets ↔
      MeaningEqPrefixRunRev 29 rd args rets :=
  rv_iff 29 (f := fn% «eq_prefix_run_rev__L29»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L29») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L30_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 30 "") args rets ↔
      MeaningEqPrefixRunRev 30 rd args rets :=
  rv_iff 30 (f := fn% «eq_prefix_run_rev__L30»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L30») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L31_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 31 "") args rets ↔
      MeaningEqPrefixRunRev 31 rd args rets :=
  rv_iff 31 (f := fn% «eq_prefix_run_rev__L31»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L31») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

theorem eq_prefix_run_rev_L32_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunRevNames.getD 32 "") args rets ↔
      MeaningEqPrefixRunRev 32 rd args rets :=
  rv_iff 32 (f := fn% «eq_prefix_run_rev__L32»)
    (coreProgram_find?_at (j := idx% «eq_prefix_run_rev__L32») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

/-- **`eq_prefix_run_rev`'s core IR is its meaning**, every specialization. -/
theorem eq_prefix_run_rev_holds : eq_prefix_run_rev_Spec := by
  intro n hn
  interval_cases n
  exacts [eq_prefix_run_rev_L0_iff, eq_prefix_run_rev_L1_iff, eq_prefix_run_rev_L2_iff,
    eq_prefix_run_rev_L3_iff, eq_prefix_run_rev_L4_iff, eq_prefix_run_rev_L5_iff,
    eq_prefix_run_rev_L6_iff, eq_prefix_run_rev_L7_iff, eq_prefix_run_rev_L8_iff,
    eq_prefix_run_rev_L9_iff, eq_prefix_run_rev_L10_iff, eq_prefix_run_rev_L11_iff,
    eq_prefix_run_rev_L12_iff, eq_prefix_run_rev_L13_iff, eq_prefix_run_rev_L14_iff,
    eq_prefix_run_rev_L15_iff, eq_prefix_run_rev_L16_iff, eq_prefix_run_rev_L17_iff,
    eq_prefix_run_rev_L18_iff, eq_prefix_run_rev_L19_iff, eq_prefix_run_rev_L20_iff,
    eq_prefix_run_rev_L21_iff, eq_prefix_run_rev_L22_iff, eq_prefix_run_rev_L23_iff,
    eq_prefix_run_rev_L24_iff, eq_prefix_run_rev_L25_iff, eq_prefix_run_rev_L26_iff,
    eq_prefix_run_rev_L27_iff, eq_prefix_run_rev_L28_iff, eq_prefix_run_rev_L29_iff,
    eq_prefix_run_rev_L30_iff, eq_prefix_run_rev_L31_iff, eq_prefix_run_rev_L32_iff]

/-! ## `eq_prefix_chain_rev` -/

theorem find_eq_prefix_chain_rev :
    coreProgram.find? "eq_prefix_chain_rev" = some fn% «eq_prefix_chain_rev» :=
  coreProgram_find?_at (j := idx% «eq_prefix_chain_rev») rfl

theorem eq_prefix_chain_rev_body : Fn.body fn% «eq_prefix_chain_rev» =
    [.atom (.const (.n (val% «eq_prefix_chain_rev» "s0#0")) (word (2 ^ 32) 0)),
      .atom (.rangeCheck (.n (val% «eq_prefix_chain_rev» "count_g")) (.n (val% «eq_prefix_chain_rev» "s0#1")) (.n (val% «eq_prefix_chain_rev» "s0#2")) (.n (val% «eq_prefix_chain_rev» "s0#3")) (.n (val% «eq_prefix_chain_rev» "s0#0"))),
      .dispatch (.n (val% «eq_prefix_chain_rev» "count_g")) eqPrefixRunRevNames [.n (val% «eq_prefix_chain_rev» "chain"), .n (val% «eq_prefix_chain_rev» "out"), .n (val% «eq_prefix_chain_rev» "src"), .n (val% «eq_prefix_chain_rev» "b1")] [.n (val% «eq_prefix_chain_rev» "done")], .ret []] :=
  stmtsEqb_sound (by decide +kernel)

/-- **`eq_prefix_chain_rev`'s core IR is its meaning.** -/
theorem eq_prefix_chain_rev_holds : eq_prefix_chain_rev_Spec := by
  intro rd args rets
  have hname : ∀ j (hj : j < eqPrefixRunRevNames.length), eqPrefixRunRevNames[j] = eqPrefixRunRevNames.getD j "" :=
    fun j hj => by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  rw [rel_iff_fnSem find_eq_prefix_chain_rev]
  vc
  rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, word_two_pow (by norm_num)]
  constructor
  · rintro ⟨chain, out, src, b1, cg, rfl, y, t1, r1, r2, t2, r3, x9, ⟨j, hx, hj, hcall⟩, rfl⟩
    have hc : coreProgram.Rel rd (eqPrefixRunRevNames.getD j "") [chain, out, src, b1] [x9] := by
      rw [← hname j hj]; exact hcall
    rw [eq_prefix_run_rev_holds j (by omega)] at hc
    exact ⟨rfl, ⟨y, t1, t2, r1, r2, r3⟩, j, hj, by rw [hx, gen_pow_eq_ofK], hc.1⟩
  · intro hm
    obtain ⟨chain, out, src, b1, cg, rfl⟩ : ∃ chain out src b1 cg, args = [chain, out, src, b1, cg] := by
      match args, hm with
      | [x0, x1, x2, x3, x4], _ => exact ⟨x0, x1, x2, x3, x4, rfl⟩
    obtain ⟨rfl, ⟨y, t1, t2, r1, r2, r3⟩, n, hn, rfl, hep⟩ := hm
    refine ⟨chain, out, src, b1, gen ^ n, rfl, y, t1, r1, r2, t2, r3, 0, ⟨n, by rw [gen_pow_eq_ofK], hn, ?_⟩, rfl⟩
    have hc : coreProgram.Rel rd (eqPrefixRunRevNames.getD n "") [chain, out, src, b1] [0] :=
      (eq_prefix_run_rev_holds n (by omega) _ _ _).mpr ⟨hep, rfl⟩
    rw [← hname n hn] at hc
    exact hc

end
end LeanVM.Guest.B1
