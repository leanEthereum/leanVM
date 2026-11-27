/-
  LeanVM.Guest.B1.Eq.EqPrefix

  B1 for `eq_prefix_run` (41 specializations) and `eq_prefix_chain`, its dispatch.
-/

module

public import LeanVM.Guest.B1.Eq.Meaning
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.B1.Common.Family
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«eq_prefix_chain»
import LeanVM.Guest.Data.ValNames.«eq_prefix_run__L»
import LeanVM.Guest.B1.Common.Vc
meta import LeanVM.Guest.KernelRfl
import LeanVM.Guest.StmtsAppend

/-!
# `eq_prefix_run`, `eq_prefix_chain`

`eq_prefix_run__L{n}` stores the seed at `chain[0]`, then per coordinate `k < n` (`epBlk k`) reads
`a[k]`, `b1[k]`, multiplies the running product by their sum and stores it at `chain[k + 1]`; it
returns `0`. `eq_prefix_chain` range-checks `count_g = g^n` below `g^41` and dispatches to
`eq_prefix_run__L{n}`.
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
  [.atom (.load (.n (4 + 4 * k)) (.n (valf% «eq_prefix_run» "a")) k), .atom (.load (.n (5 + 4 * k)) (.n (valf% «eq_prefix_run» "b1")) k),
    .atom (.add (.n (6 + 4 * k)) (.n (4 + 4 * k)) (.n (5 + 4 * k))),
    .atom (.mul (.n (7 + 4 * k)) (.n (epV k)) (.n (6 + 4 * k))),
    .atom (.load (.n (7 + 4 * k)) (.n (valf% «eq_prefix_run» "chain")) (k + 1))]

/-- The expansion of `eq_prefix_run__L{n}`. -/
def epBody (n : ℕ) : List Stmt :=
  [.atom (.load (.n (valf% «eq_prefix_run» "seed")) (.n (valf% «eq_prefix_run» "chain")) 0)] ⧺ ((List.range n).map epBlk).flatten ⧺
    [.atom (.const (.n (4 + 4 * n)) (word 0 0)), .ret [.n (4 + 4 * n)]]

/-- What coordinate `k` asks. -/
def EpOk (rd : Reader) (σ : Val) (k : ℕ) : Prop :=
  LoadHolds rd (σ (.n (valf% «eq_prefix_run» "a"))) k (σ (.n (4 + 4 * k))) ∧ LoadHolds rd (σ (.n (valf% «eq_prefix_run» "b1"))) k (σ (.n (5 + 4 * k))) ∧
    σ (.n (6 + 4 * k)) = σ (.n (4 + 4 * k)) + σ (.n (5 + 4 * k)) ∧
    σ (.n (7 + 4 * k)) = σ (.n (epV k)) * σ (.n (6 + 4 * k)) ∧
    LoadHolds rd (σ (.n (valf% «eq_prefix_run» "chain"))) (k + 1) (σ (.n (7 + 4 * k)))

theorem holds_epBlk {C : CallRel} {rd : Reader} {σ : Val} (k : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (epBlk k) True kret ↔ EpOk rd σ k := by
  simp only [epBlk, EpOk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]

/-- The function's relation, on the conditions of its blocks. -/
theorem ep_iff (n : ℕ) {f : Fn} (hfind : coreProgram.find? (eqPrefixRunNames.getD n "") = some f)
    (hparams : f.params = [.n (valf% «eq_prefix_run» "chain"), .n (valf% «eq_prefix_run» "seed"), .n (valf% «eq_prefix_run» "a"), .n (valf% «eq_prefix_run» "b1")]) (hbody : f.body = epBody n) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd (eqPrefixRunNames.getD n "") args rets ↔ MeaningEqPrefixRun n rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, epBody]
  simp only [holdsList_append, holdsList_range_flatten n epBlk (fun _ => rfl), holds_epBlk,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_zero]
  constructor
  · rintro ⟨σ, hp, l0, hblk, h4, hret⟩
    subst hp
    have hv : ∀ j ≤ n, σ (.n (epV j)) = prefixProd (σ (.n (valf% «eq_prefix_run» "seed")))
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
    have e0 : σ (.n (valf% «eq_prefix_run» "chain")) = chain := rfl
    have e2 : σ (.n (valf% «eq_prefix_run» "a")) = a := rfl
    have e3 : σ (.n (valf% «eq_prefix_run» "b1")) = b1 := rfl
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

/-- The deployed `eq_prefix_run__L{n}`, `n ≤ 40`, are the template. -/
private theorem eq_prefix_run_found :
    coreRunB (idxs% «eq_prefix_run__L» 0 41) (eqPrefixRunNames.getD · "")
    (shapeB [.n (valf% «eq_prefix_run» "chain"), .n (valf% «eq_prefix_run» "seed"),
      .n (valf% «eq_prefix_run» "a"), .n (valf% «eq_prefix_run» "b1")] epBody) = true := by
  decide +kernel

/-- **`eq_prefix_run`'s core IR is its meaning**, every specialization. -/
theorem eq_prefix_run_holds : eq_prefix_run_Spec := fun n hn ↦
  have ⟨_, hf, hp, hb⟩ := coreRunB_shape eq_prefix_run_found (Nat.lt_succ_of_le hn)
  ep_iff n hf hp hb

/-! ## `eq_prefix_chain` -/

theorem find_eq_prefix_chain : coreProgram.find? "eq_prefix_chain" = some fn% «eq_prefix_chain» :=
  coreProgram_find?_at (j := idx% «eq_prefix_chain») rfl

theorem eq_prefix_chain_body : Fn.body fn% «eq_prefix_chain» =
    [.atom (.const (.n (val% «eq_prefix_chain» "s0#0")) (word (2 ^ 40) 0)),
      .atom (.rangeCheck (.n (val% «eq_prefix_chain» "count_g")) (.n (val% «eq_prefix_chain» "s0#1")) (.n (val% «eq_prefix_chain» "s0#2")) (.n (val% «eq_prefix_chain» "s0#3")) (.n (val% «eq_prefix_chain» "s0#0"))),
      .dispatch (.n (val% «eq_prefix_chain» "count_g")) eqPrefixRunNames [.n (val% «eq_prefix_chain» "chain"), .n (val% «eq_prefix_chain» "seed"), .n (val% «eq_prefix_chain» "a"), .n (val% «eq_prefix_chain» "b1")] [.n (val% «eq_prefix_chain» "done")], .ret []] := by
  kernel_rfl

theorem word_g40 : word 1099511627776 0 = gen ^ 40 := word_two_pow (a := 40) (by decide)

/-- **`eq_prefix_chain`'s core IR is its meaning.** -/
theorem eq_prefix_chain_holds : eq_prefix_chain_Spec := by
  intro rd args rets
  rw [rel_iff_fnSem find_eq_prefix_chain]
  rcases args with _ | ⟨chain, _ | ⟨seed, _ | ⟨a, _ | ⟨b1, _ | ⟨cg, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;> vc [] <;>
    simp only [MeaningEqPrefixChain]
  have hrun : ∀ j (hj : j < 41) (r : List E), coreProgram.Rel rd eqPrefixRunNames[j]
      [chain, seed, a, b1] r ↔ EqPrefix rd chain seed a b1 j ∧ r = [0] := fun j hj r =>
    List.getD_eq_getElem eqPrefixRunNames "" hj ▸ eq_prefix_run_holds j (by omega) rd _ r
  rw [word_g40]
  constructor
  · rintro ⟨y, t1, r1, r2, t2, r3, _, ⟨j, hx, hj, hcall⟩, rfl⟩
    exact ⟨rfl, ⟨y, t1, t2, r1, r2, r3⟩, j, hj, by rw [hx, gen_pow_eq_ofK],
      ((hrun j hj _).mp hcall).1⟩
  · rintro ⟨rfl, ⟨y, t1, t2, r1, r2, r3⟩, n, hn, rfl, hep⟩
    exact ⟨y, t1, r1, r2, t2, r3, 0, ⟨n, by rw [gen_pow_eq_ofK], hn, (hrun n hn _).mpr ⟨hep, rfl⟩⟩,
      rfl⟩

end
end LeanVM.Guest.B1
