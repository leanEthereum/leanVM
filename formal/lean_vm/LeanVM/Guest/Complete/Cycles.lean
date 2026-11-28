/-
  LeanVM.Guest.Complete.Cycles

  `main`'s instructions within the checker's count (`MainCycles`, the zero-challenge sum counted), from the honest
  valuation's hand values: the shape at the cycle certificates.
-/

module

public import LeanVM.Guest.Complete.HandShape
public import LeanVM.Guest.Complete.Open
import LeanVM.Guest.B1.Common.Find

/-!
# `main`'s instructions within the count

`CycH op it rd t` asks, at opcode `op`, of `main`'s honest tree `node "main" σ bufs kids`: every callee but the
children's loop with its hand facts at the cycle certificates (`chCertAt`, `chHandAt`, `chOut`), the loop a
`LoopRun` within `loopCntC iterSumV op it`, and `main`'s own preconditions and inner bound.

* Off `main`'s node (`OffNode`) a function is never left out (`not_chOut`), and one with no hand has its hand fact
  for free (`handFact_ch_none`).
* The loop (`cyc_loop`): entered at counter `g^0` with end `g^n`, `n` the children, its iteration at counter `g^j`
  costs `iterSumV op` and `claimV op` a claim of child `j`'s two lists (`chloopHand_eval`), and its tail frame
  `lastV op` (`ωC_loop_last`), so its run is within `loopCntC iterSumV op it` once each iteration's two virtual
  values (`σ 18`, `σ 19`) are powers of `g` summing to at most child `j`'s claims.
* `cycH_of` joins them with the hand facts of the other callees and `main`'s own.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Budget
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## Off `main`'s node -/

/-- No function is absent from the cycle check: `chabsL` is all `false`, by the kernel. -/
theorem chabsJ_false (j : ℕ) : Data.chabsJ j = false := by
  have h : Data.chabsL.all (· == false) = true := by decide +kernel
  unfold Data.chabsJ
  rcases hj : Data.chabsL[j]? with _ | b
  · rw [List.getD_eq_getElem?_getD, hj]; rfl
  · rw [List.getD_eq_getElem?_getD, hj, Option.getD_some]
    have := List.all_eq_true.mp h b (List.mem_of_getElem? hj)
    simpa using this

/-- The index of a name is the loop's only for the loop. -/
theorem coreIdx_eq_loop {f : String} (h : coreIdx f = Data.chidxLoop) : f = "__loop4_main" := by
  have hl : Data.chidxLoop < coreProgram.length := ch_nodeIdx.hl
  have hlt : (coreProgram.map (·.name)).idxOf f < (coreProgram.map (·.name)).length := by
    rw [List.length_map]; unfold coreIdx at h; rw [h]; exact hl
  have hg := List.getElem_idxOf hlt
  have hn := ch_nodeIdx.nl
  rw [List.getElem?_eq_getElem hl, Option.map_some, Option.some.injEq] at hn
  unfold coreIdx at h
  simp only [h, List.getElem_map] at hg
  rw [← hg, hn]

/-- **Off the children's loop, no function is left out of the cycle check.** -/
theorem not_chOut (op : Opcode) {f : String} (hf : f ≠ "__loop4_main") : ¬ chOut op f := by
  rintro (h | h)
  · rw [chabsJ_false] at h; cases h
  · unfold lhP Data.chloopJ at h
    split_ifs at h with hj
    · exact hf (coreIdx_eq_loop hj)
    · cases h

/-- **A function off `main`'s node with no hand has its hand fact.** -/
theorem handFact_ch_none (op : Opcode) (C₁ C₂ : ℕ) {f : String} (hf : f ≠ "__loop4_main")
    (hn : Data.chhandJ (coreIdx f) = none) (σ : Val) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) f σ := by
  refine ⟨not_chOut op hf, fun h hh => ?_⟩
  unfold chHandAt handAt handP at hh
  split_ifs at hh <;> simp [hn] at hh

/-! ## The children's loop -/

/-- The loop's parameters: sixteen. -/
theorem loop_params_length : (coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params.length = 16 := by
  decide +kernel

theorem chloopHand_pre : Data.chloopHand.pre = [] := rfl

theorem chloopHand_vps : Data.chloopHand.vps = [.n 18, .n 19] := rfl

/-- **The loop hand's inner bound at opcode `op`**: `iterSumV op` and `claimV op` an exponent of each virtual
value. -/
theorem chloopHand_eval (op : Opcode) (vs : List E) :
    (Data.chloopHand.proj (B2C.opIdx op)).b.eval vs = iterSumV op + claimV op * (argExp vs 16 + argExp vs 17) := by
  cases op <;> simp [HandV.proj, AffV.proj, Aff.eval, Data.chloopHand, B2C.opIdx, iterSumV, claimV, v6] <;> ring

/-- The loop's tail frame weighs `lastV op`. -/
theorem ωC_loop_last (op : Opcode) : ωC op "__loop4_main" = lastV op := by
  rw [ωC_loop]; cases op <;> decide +kernel

/-- The loop's function. -/
theorem loop_find : coreProgram.find? "__loop4_main" = some (coreProgram[Data.chidxLoop]'ch_nodeIdx.hl) := by
  have hn := ch_nodeIdx.nl
  rw [List.getElem?_eq_getElem ch_nodeIdx.hl, Option.map_some, Option.some.injEq] at hn
  exact coreProgram_find?_at (List.getElem?_eq_getElem ch_nodeIdx.hl) hn

/-- The loop's body without its tail call. -/
noncomputable def loopPre : List Stmt := (loopShape (coreProgram[Data.chidxLoop]'ch_nodeIdx.hl) none).getD []

theorem loopShape_loop : loopShape (coreProgram[Data.chidxLoop]'ch_nodeIdx.hl) none = some loopPre := by
  have h : (loopShape (coreProgram[Data.chidxLoop]'ch_nodeIdx.hl) none).isSome = true := by decide +kernel
  obtain ⟨pre, hp⟩ := Option.isSome_iff_exists.mp h
  rw [loopPre, hp]; rfl

/-- The loop's iteration calls only functions off `main`'s node. -/
theorem loopPre_callees : ∀ g ∈ Stmt.blockCallees loopPre, OffNode g := by
  have h : (Stmt.blockCallees loopPre).all (fun g => decide (g ≠ "main") && decide (g ≠ "da_verify") &&
      decide (g ≠ "__loop4_main")) = true := by
    unfold loopPre; decide +kernel
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- Child `j`'s claims, its two lists'. -/
def childClaims (it : NodeItems) (j : ℕ) : ℕ :=
  ((it.children[j]?).map fun c ↦ c.xmssClaims + c.sphincsClaims).getD 0

theorem sum_range_getD (K c : ℕ) (h : ChildItem → ℕ) : ∀ l : List ChildItem,
    ∑ m ∈ Finset.range l.length, (K + c * ((l[m]?).map h).getD 0) = (l.map fun x => K + c * h x).sum
  | [] => by simp
  | a :: t => by
      simp only [List.length_cons, Finset.sum_range_succ', List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.map_some, Option.getD_some, sum_range_getD K c h t, List.map_cons, List.sum_cons]
      ring

theorem sum_childClaims (op : Opcode) (it : NodeItems) :
    (∑ m ∈ Finset.Ico 0 it.children.length, (iterSumV op + claimV op * childClaims it m)) + lastV op =
      loopCntC iterSumV op it := by
  unfold loopCntC childClaims
  rw [← Finset.range_eq_Ico, sum_range_getD]

/-- **The children's loop within `loopCntC iterSumV op it`** at the cycle certificates: entered at counter `g^0`
with end `g^n`, `n` the children, each valid iteration at counter `g^j` having its virtual values (`σ 18`, `σ 19`)
powers of `g` summing to at most child `j`'s claims. -/
theorem cyc_loop (op : Opcode) (it : NodeItems) {rd : Reader} {Q : String → Val → Prop}
    (hkids : ∀ σ es ks, walk σ loopPre = .fall es → HoldsAll rd σ es →
      Memory.Tree.KidsValid coreProgram rd σ (calls es) ks → ∀ k ∈ ks, k.Every Q)
    (hn : it.children.length < 2 ^ 64 - 1)
    (hval : ∀ σ, (∃ bufs kids a r, (Memory.Tree.node "__loop4_main" σ bufs kids).Valid coreProgram rd a r) →
      ∀ j < it.children.length,
      ((coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params.map σ).take 2 = [gen ^ j, gen ^ it.children.length] →
        logG (σ (.n 18)) + logG (σ (.n 19)) ≤ childClaims it j)
    (t : Memory.Tree) {args rets : List E} (hv : t.Valid coreProgram rd args rets) (hname : t.name = "__loop4_main")
    (hargs : args.take 2 = [gen ^ 0, gen ^ it.children.length]) (h0 : 0 < it.children.length) :
    ∃ S, LoopRun "__loop4_main" (coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params
      (Data.chloopHand.proj (B2C.opIdx op)) (ωC op "__loop4_main") (fun k => k.Every Q) t S ∧
        S ≤ loopCntC iterSumV op it := by
  obtain ⟨S, hrun, hS'⟩ := loopRun_count loop_find loopShape_loop hkids
    (Data.chloopHand.proj (B2C.opIdx op)) (ωC op "__loop4_main") it.children.length hn
    (fun j => iterSumV op + claimV op * childClaims it j)
    (fun σ hnode j hj ht => by
      refine ⟨fun q hq => by simp [HandV.proj, chloopHand_pre] at hq, ?_⟩
      rw [chloopHand_eval]
      have hv := hval σ hnode j hj ht
      have e16 : argExp (((coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params ++
          (Data.chloopHand.proj (B2C.opIdx op)).vps).map σ) 16 = logG (σ (.n 18)) := by
        unfold argExp
        rw [List.getD_eq_getElem?_getD, List.map_append, List.getElem?_append_right (by simp [loop_params_length])]
        simp [loop_params_length, HandV.proj, chloopHand_vps]
      have e17 : argExp (((coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params ++
          (Data.chloopHand.proj (B2C.opIdx op)).vps).map σ) 17 = logG (σ (.n 19)) := by
        unfold argExp
        rw [List.getD_eq_getElem?_getD, List.map_append, List.getElem?_append_right (by simp [loop_params_length])]
        simp [loop_params_length, HandV.proj, chloopHand_vps]
      rw [e16, e17]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hv) _)
    t hv hname h0 hargs
  refine ⟨S, hrun, ?_⟩
  rw [← sum_childClaims, ← ωC_loop_last]
  exact hS'

end
end LeanVM.Guest.Complete
