module

public import LeanVM.Guest.Complete.Agg.Lib
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop2»

/-!
# `aggregate_claims_loop2`, completely

`a2_block`: the loop's block at the child `x` holds on its evaluated valuation (`Fwd.ev`) when its
record (`chain·x^2`) holds a power of `λ` and a running claim, the next record the power times
`λ²` and the claim plus the power times `fresh_val[x] + λ · carried[25]`, the carried claim reached
through the pointer table `lc` (the loop also loads the fresh claim's pointer from `lf`, an unnamed value `.n 11`). Its atoms but its stores hold (their side conditions its loads,
`a2COk`), which its stores find.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.Da

@[expose] public section

/-- `aggregate_claims_loop2`'s stores: the next record's power and claim. -/
def a2Stores : List Atom :=
  [.load (.n (val% «aggregate_claims_loop2» "s5#0")) (.n (val% «aggregate_claims_loop2» "row")) 2,
    .load (.n (val% «aggregate_claims_loop2» "s6#7")) (.n (val% «aggregate_claims_loop2» "row")) 3]

/-- `aggregate_claims_loop2`'s atoms but its stores. -/
noncomputable def a2A : List Atom :=
  (atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop2» default))).filter fun a =>
    decide (a ∉ a2Stores)

theorem mem_a2A {a : Atom} :
    a ∈ a2A ↔ a ∈ atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop2» default)) ∧
      a ∉ a2Stores := by
  simp [a2A]

/-- A load of `aggregate_claims_loop2`: the record's two words, the pointer to the carried claim,
its value, the fresh claim's folded value. -/
def isA2Load : Atom → Bool
  | .load _ p o => (decide (p = .n (val% «aggregate_claims_loop2» "row")) && decide (o < 2)) ||
      ((decide (p = .n 11) || decide (p = .n (val% «aggregate_claims_loop2» "carried~0"))) && decide (o = 0)) ||
      (decide (p = .n (val% «aggregate_claims_loop2» "s6#1")) && decide (o = 0)) ||
      (decide (p = .n (val% «aggregate_claims_loop2» "carried")) && decide (o = 25))
  | _ => false

set_option maxRecDepth 100000 in
theorem a2_stores : storesOf 8 (coreProgram.getD idx% «aggregate_claims_loop2» default).body =
    a2Stores := by
  decide +kernel

/-- **`aggregate_claims_loop2`, evaluated**: its values defined in order, its atoms but its stores
holding from its loads, and the facts of its block on them. -/
noncomputable def a2COk : Bool :=
  let fn := coreProgram.getD idx% «aggregate_claims_loop2» default
  let A := a2A
  let P := (atomsIn (loopPre fn)).filter pureB
  (chk 8 fn.body).isSome && (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) &&
  A.all (fun a => !needsSide a || isA2Load a) &&
  isMul P (.n (val% «aggregate_claims_loop2» "row~0")) (.n (val% «aggregate_claims_loop2» "xc")) (.n (val% «aggregate_claims_loop2» "xc")) &&
  isMul P (.n (val% «aggregate_claims_loop2» "row")) (.n (val% «aggregate_claims_loop2» "bc_chain")) (.n (val% «aggregate_claims_loop2» "row~0")) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "lam_pow")) (.n (val% «aggregate_claims_loop2» "row")) 0) &&
  isMul P (.n 11) (.n (val% «aggregate_claims_loop2» "fresh_row")) (.n (val% «aggregate_claims_loop2» "xc")) &&
  isMul P (.n (val% «aggregate_claims_loop2» "carried~0")) (.n (val% «aggregate_claims_loop2» "carried_row")) (.n (val% «aggregate_claims_loop2» "xc")) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "carried")) (.n (val% «aggregate_claims_loop2» "carried~0")) 0) &&
  isMul P (.n (val% «aggregate_claims_loop2» "s5#0")) (.n (val% «aggregate_claims_loop2» "lam_pow")) (.n (val% «aggregate_claims_loop2» "lam_sq")) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "s6#0")) (.n (val% «aggregate_claims_loop2» "row")) 1) &&
  isMul P (.n (val% «aggregate_claims_loop2» "s6#1")) (.n (val% «aggregate_claims_loop2» "fresh_val")) (.n (val% «aggregate_claims_loop2» "xc")) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "s6#2")) (.n (val% «aggregate_claims_loop2» "s6#1")) 0) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop2» "s6#3")) (.n (val% «aggregate_claims_loop2» "carried")) 25) &&
  isMul P (.n (val% «aggregate_claims_loop2» "s6#4")) (.n (val% «aggregate_claims_loop2» "lam")) (.n (val% «aggregate_claims_loop2» "s6#3")) &&
  P.any (isAddAt (.n (val% «aggregate_claims_loop2» "s6#5")) (.n (val% «aggregate_claims_loop2» "s6#2")) (.n (val% «aggregate_claims_loop2» "s6#4"))) &&
  isMul P (.n (val% «aggregate_claims_loop2» "s6#6")) (.n (val% «aggregate_claims_loop2» "lam_pow")) (.n (val% «aggregate_claims_loop2» "s6#5")) &&
  P.any (isAddAt (.n (val% «aggregate_claims_loop2» "s6#7")) (.n (val% «aggregate_claims_loop2» "s6#0")) (.n (val% «aggregate_claims_loop2» "s6#6")))

set_option maxRecDepth 100000 in
theorem a2_shape : loopShapeF (coreProgram.getD idx% «aggregate_claims_loop2» default)
    name% «aggregate_claims_loop2» = true ∧
    (coreProgram.getD idx% «aggregate_claims_loop2» default).params.length = 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem a2c_ok : a2COk = true := by decide +kernel

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **A child's record** (`aggregate_claims_loop2`), completely. -/
theorem a2_block {x N chainT lfT lcT lamSq fvT lam pf pc fv cv pw acc : E}
    (hrow : ReadsAt rd (chainT * x ^ 2) [pw, acc])
    (hnext : ReadsAt rd (chainT * x ^ 2 * gen ^ 2) [pw * lamSq, acc + pw * (fv + lam * cv)])
    (hlf : LoadHolds rd (lfT * x) 0 pf) (hlc : LoadHolds rd (lcT * x) 0 pc) (hfv : LoadHolds rd (fvT * x) 0 fv)
    (hcv : LoadHolds rd pc 25 cv) :
    LoopBlock rd (coreProgram.getD idx% «aggregate_claims_loop2» default) x N
      [chainT, lfT, lcT, lamSq, fvT, lam] := by
  obtain ⟨hshape, hlen⟩ := a2_shape
  have hcok := a2c_ok
  simp only [a2COk, Bool.and_eq_true, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hatoms⟩, hneeds⟩, hm7⟩, hm8⟩, hl9⟩, hm10⟩, hm12⟩, hl13⟩,
    hm14⟩, hl15⟩, hm16⟩, hl16⟩, hl17⟩, hm18⟩, ha19⟩, hm20⟩, ha21⟩ := hcok
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hatoms hneeds
  set fn := coreProgram.getD idx% «aggregate_claims_loop2» default
  set A := atomsIn (loopPre fn)
  let args : List E := [x, N, chainT, lfT, lcT, lamSq, fvT, lam]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body) := ⟨_, rfl⟩
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
  rw [show args.length = 8 from rfl, ← hσ, a2_stores] at hgs
  have hg : ∀ a ∈ A, Good rd a2Stores (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (loopPre_mem (atom_mem_of_atomsIn ha))
  have hpar : fn.params = (List.range 8).map V.n := params_of_shape hshape hlen
  have par : ∀ i (hi : i < 8), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n (val% «aggregate_claims_loop2» "xc")) = x := par 0 (by omega)
  have hP : ∀ a ∈ A.filter pureB, a.Holds rd σ := pure_holds hg
  have p8 : σ (.n (val% «aggregate_claims_loop2» "row")) = chainT * x ^ 2 := by
    rw [isMul_sound hm8 hP, isMul_sound hm7 hP, par 2 (by omega), e0, sq]; rfl
  have p10 : σ (.n 11) = lfT * x := by
    rw [isMul_sound hm10 hP, par 3 (by omega), e0]; rfl
  have p12 : σ (.n (val% «aggregate_claims_loop2» "carried~0")) = lcT * x := by
    rw [isMul_sound hm12 hP, par 4 (by omega), e0]; rfl
  have p16 : σ (.n (val% «aggregate_claims_loop2» "s6#1")) = fvT * x := by
    rw [isMul_sound hm16 hP, par 6 (by omega), e0]; rfl
  have hr0 : LoadHolds rd (chainT * x ^ 2) 0 pw := hrow 0 (by simp)
  have hr1 : LoadHolds rd (chainT * x ^ 2) 1 acc := hrow 1 (by simp)
  -- the atoms but the stores
  have hg' : ∀ a ∈ a2A, Good rd a2Stores (fun _ => 0) σ a := fun a ha => hg a (mem_a2A.mp ha).1
  have hnS : ∀ a ∈ a2A, a ∉ a2Stores := fun a ha => (mem_a2A.mp ha).2
  have v13 : σ (.n (val% «aggregate_claims_loop2» "carried")) = pc := by
    rw [(load_any_val hnS hg' hl13).1, p12, rdAt_of_load hlc]
  have hat' : ∀ a ∈ a2A, a.Holds rd σ := by
    refine atoms_holds hg' fun a ha hns => ?_
    rcases hneeds a ha with h | h
    · rw [hns] at h; exact absurd h (by simp)
    · cases a <;> simp only [isA2Load, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rename_i d p o
      refine Or.inr (side_load (hnS _ ha) (v := memAt rd (σ p) o) ?_)
      rcases h with ((⟨rfl, ho⟩ | ⟨rfl | rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
      · rcases (show o = 0 ∨ o = 1 by omega) with rfl | rfl
        · rw [p8, memAt_of_load hr0]; exact hr0
        · rw [p8, memAt_of_load hr1]; exact hr1
      · rw [p10, memAt_of_load hlf]; exact hlf
      · rw [p12, memAt_of_load hlc]; exact hlc
      · rw [p16, memAt_of_load hfv]; exact hfv
      · rw [v13, memAt_of_load hcv]; exact hcv
  -- the stores
  have e9 := (load_any_val hnS hg' hl9).1
  have e15 := (load_any_val hnS hg' hl15).1
  have e16 := (load_any_val hnS hg' hl16).1
  have e17 := (load_any_val hnS hg' hl17).1
  rw [p8, rdAt_of_load hr0] at e9
  rw [p8, rdAt_of_load hr1] at e15
  rw [p16, rdAt_of_load hfv] at e16
  rw [v13, rdAt_of_load hcv] at e17
  have hn0 : LoadHolds rd (chainT * x ^ 2) 2 (pw * lamSq) := by
    rw [show (2 : ℕ) = 2 + 0 from rfl, ← loadHolds_mul_gen_pow]; exact hnext 0 (by simp)
  have hn1 : LoadHolds rd (chainT * x ^ 2) 3 (acc + pw * (fv + lam * cv)) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, ← loadHolds_mul_gen_pow]; exact hnext 1 (by simp)
  have hat : ∀ a ∈ A, a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ a2Stores
    · simp only [a2Stores, List.mem_cons, List.not_mem_nil, or_false] at haS
      rcases haS with rfl | rfl
      · show LoadHolds rd (σ (.n (val% «aggregate_claims_loop2» "row"))) 2
          (σ (.n (val% «aggregate_claims_loop2» "s5#0")))
        rw [p8, isMul_sound hm14 hP, e9, par 5 (by omega)]
        exact hn0
      · show LoadHolds rd (σ (.n (val% «aggregate_claims_loop2» "row"))) 3
          (σ (.n (val% «aggregate_claims_loop2» "s6#7")))
        rw [p8, add_sound ha21 hP, isMul_sound hm20 hP, add_sound ha19 hP, isMul_sound hm18 hP,
          e9, e15, e16, e17, par 7 (by omega)]
        exact hn1
    · exact hat' a (mem_a2A.mpr ⟨ha, haS⟩)
  refine ⟨σ, ?_, fun s hs => ?_⟩
  · rw [hpar]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
      List.map_nil]
    rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega),
      par 5 (by omega), par 6 (by omega), par 7 (by omega)]
    rfl
  · have := hatoms s hs
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    exact ⟨hat a (mem_atomsIn hs), trivial⟩

end
end LeanVM.Guest.Complete.Agg
