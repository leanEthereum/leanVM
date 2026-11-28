module

public import LeanVM.Guest.Complete.Agg.Lib
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop1»

/-!
# `aggregate_claims_loop1`, completely

`a1_block`: the loop's block at the child `x` holds on its evaluated valuation (`Fwd.ev`) when the
pointer table `lf` at `x` holds the child's fresh claim `pf`, the `36` words of `eq_col` and the
fresh claim's values `pf·g^(19 + j)` are in memory, and `fresh_val[x]` holds their fold
`Σ_j eq_col[j] · fresh[19 + j]` (`fvAcc`). Its atoms but its store hold (their side conditions its
loads, `a1COk`), which its store finds.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.Da

@[expose] public section

/-- `aggregate_claims_loop1`'s store: the folded value. -/
def a1Stores : List Atom :=
  [.load (.n (val% «aggregate_claims_loop1» "fv@36")) (.n (val% «aggregate_claims_loop1» "s3#0")) 0]

/-- `aggregate_claims_loop1`'s atoms but its store. -/
noncomputable def a1A : List Atom :=
  (atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop1» default))).filter fun a =>
    decide (a ∉ a1Stores)

theorem mem_a1A {a : Atom} :
    a ∈ a1A ↔ a ∈ atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop1» default)) ∧
      a ∉ a1Stores := by
  simp [a1A]

/-- A load of `aggregate_claims_loop1`: the pointer to the fresh claim, `eq_col`'s words, the fresh
claim's values. -/
def isA1Load : Atom → Bool
  | .load _ p o => (decide (p = .n (val% «aggregate_claims_loop1» "fresh~0")) && decide (o = 0)) ||
      (decide (p = .n (val% «aggregate_claims_loop1» "eq_col")) && decide (o < 36)) ||
      (decide (p = .n (val% «aggregate_claims_loop1» "fresh")) && decide (19 ≤ o) && decide (o < 55))
  | _ => false

set_option maxRecDepth 100000 in
theorem a1_stores : storesOf 5 (coreProgram.getD idx% «aggregate_claims_loop1» default).body =
    a1Stores := by
  decide +kernel

/-- **`aggregate_claims_loop1`, evaluated**: its values defined in order, its atoms but its store
holding from its loads, and the facts of its block on them. -/
noncomputable def a1COk : Bool :=
  let fn := coreProgram.getD idx% «aggregate_claims_loop1» default
  let A := a1A
  let P := (atomsIn (loopPre fn)).filter pureB
  (chk 5 fn.body).isSome && (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) &&
  A.all (fun a => !needsSide a || isA1Load a) &&
  isMul P (.n (val% «aggregate_claims_loop1» "fresh~0")) (.n (val% «aggregate_claims_loop1» "fresh_row")) (.n (val% «aggregate_claims_loop1» "xc")) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop1» "fresh")) (.n (val% «aggregate_claims_loop1» "fresh~0")) 0) &&
  fvChainOk A (.n (val% «aggregate_claims_loop1» "eq_col")) (.n (val% «aggregate_claims_loop1» "fresh")) 36 (.n (val% «aggregate_claims_loop1» "fv@36")) &&
  isMul P (.n (val% «aggregate_claims_loop1» "s3#0")) (.n (val% «aggregate_claims_loop1» "fresh_val")) (.n (val% «aggregate_claims_loop1» "xc"))

set_option maxRecDepth 100000 in
theorem a1_shape : loopShapeF (coreProgram.getD idx% «aggregate_claims_loop1» default)
    name% «aggregate_claims_loop1» = true ∧
    (coreProgram.getD idx% «aggregate_claims_loop1» default).params.length = 5 := by decide +kernel

set_option maxRecDepth 100000 in
theorem a1c_ok : a1COk = true := by decide +kernel

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **A child's folded fresh value** (`aggregate_claims_loop1`), completely. -/
theorem a1_block {x N lfT eqc fvT pf : E} (hlf : LoadHolds rd (lfT * x) 0 pf)
    (heq : ∀ j < 36, ∃ v, LoadHolds rd eqc j v) (hfr : ∀ j < 36, ∃ v, LoadHolds rd pf (19 + j) v)
    (hout : LoadHolds rd (fvT * x) 0 (fvAcc rd eqc pf 36)) :
    LoopBlock rd (coreProgram.getD idx% «aggregate_claims_loop1» default) x N [lfT, eqc, fvT] := by
  obtain ⟨hshape, hlen⟩ := a1_shape
  have hcok := a1c_ok
  simp only [a1COk, Bool.and_eq_true, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hatoms⟩, hneeds⟩, hm5⟩, hl6⟩, hfv⟩, hm150⟩ := hcok
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hatoms hneeds
  set fn := coreProgram.getD idx% «aggregate_claims_loop1» default
  set A := atomsIn (loopPre fn)
  let args : List E := [x, N, lfT, eqc, fvT]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body) := ⟨_, rfl⟩
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
  rw [show args.length = 5 from rfl, ← hσ, a1_stores] at hgs
  have hg : ∀ a ∈ A, Good rd a1Stores (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (loopPre_mem (atom_mem_of_atomsIn ha))
  have hpar : fn.params = (List.range 5).map V.n := params_of_shape hshape hlen
  have par : ∀ i (hi : i < 5), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n (val% «aggregate_claims_loop1» "xc")) = x := par 0 (by omega)
  have hP : ∀ a ∈ A.filter pureB, a.Holds rd σ := pure_holds hg
  have p5 : σ (.n (val% «aggregate_claims_loop1» "fresh~0")) = lfT * x := by
    rw [isMul_sound hm5 hP, par 2 (by omega), e0]; rfl
  have pe : σ (.n (val% «aggregate_claims_loop1» "eq_col")) = eqc := par 3 (by omega)
  have hg' : ∀ a ∈ a1A, Good rd a1Stores (fun _ => 0) σ a := fun a ha => hg a (mem_a1A.mp ha).1
  have hnS : ∀ a ∈ a1A, a ∉ a1Stores := fun a ha => (mem_a1A.mp ha).2
  have v6 : σ (.n (val% «aggregate_claims_loop1» "fresh")) = pf := by
    rw [(load_any_val hnS hg' hl6).1, p5, rdAt_of_load hlf]
  have hat' : ∀ a ∈ a1A, a.Holds rd σ := by
    refine atoms_holds hg' fun a ha hns => ?_
    rcases hneeds a ha with h | h
    · rw [hns] at h; exact absurd h (by simp)
    · cases a <;> simp only [isA1Load, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rename_i d p o
      refine Or.inr (side_load (hnS _ ha) (v := memAt rd (σ p) o) ?_)
      rcases h with (⟨rfl, rfl⟩ | ⟨rfl, ho⟩) | ⟨⟨rfl, ho1⟩, ho2⟩
      · rw [p5, memAt_of_load hlf]; exact hlf
      · obtain ⟨v, hv⟩ := heq o ho
        rw [pe, memAt_of_load hv]; exact hv
      · obtain ⟨v, hv⟩ := hfr (o - 19) (by omega)
        rw [show 19 + (o - 19) = o by omega] at hv
        rw [v6, memAt_of_load hv]; exact hv
  have hfvv := fvChain_sound hfv hat'
  rw [pe, v6] at hfvv
  have hat : ∀ a ∈ A, a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ a1Stores
    · simp only [a1Stores, List.mem_cons, List.not_mem_nil, or_false] at haS
      subst haS
      show LoadHolds rd (σ (.n (val% «aggregate_claims_loop1» "s3#0"))) 0
        (σ (.n (val% «aggregate_claims_loop1» "fv@36")))
      rw [isMul_sound hm150 hP, par 4 (by omega), e0, hfvv]
      exact hout
    · exact hat' a (mem_a1A.mpr ⟨ha, haS⟩)
  refine ⟨σ, ?_, fun s hs => ?_⟩
  · rw [hpar]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
      List.map_nil]
    rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega)]
    rfl
  · have := hatoms s hs
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    exact ⟨hat a (mem_atomsIn hs), trivial⟩

end
end LeanVM.Guest.Complete.Agg
