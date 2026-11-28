module

public import LeanVM.Guest.Complete.Agg.Lib
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop3»

/-!
# `aggregate_claims_loop3`, completely

`a3_block`: the loop's block at the child `x` holds on its evaluated valuation (`Fwd.ev`) when the
pointer tables hold the child's claims `pf`, `pc`, their points' coordinates and `bc_point1`'s
(`pt1`) are in memory, the record at `chain·x^2` holds the power `pw` of `λ`, the weights' table
at `x` the weight `w0`, and at `x·g` the weight on: `w0 + pw · (eq(fresh, r[..19]) · eqc +
λ · eq(carried, r))`, `r = 1 + r1` (`A3Step`'s value). Its atoms but its store hold (their side
conditions its loads, `a3COk`), which its store finds.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.Da

@[expose] public section

/-- `aggregate_claims_loop3`'s store: the next weight. -/
def a3Stores : List Atom :=
  [.load (.n (val% «aggregate_claims_loop3» "s4#7")) (.n (val% «aggregate_claims_loop3» "s4#8")) 1]

/-- `aggregate_claims_loop3`'s atoms but its store. -/
noncomputable def a3A : List Atom :=
  (atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop3» default))).filter fun a =>
    decide (a ∉ a3Stores)

theorem mem_a3A {a : Atom} :
    a ∈ a3A ↔ a ∈ atomsIn (loopPre (coreProgram.getD idx% «aggregate_claims_loop3» default)) ∧
      a ∉ a3Stores := by
  simp [a3A]

/-- A load of `aggregate_claims_loop3`: the pointers to the child's claims, their points'
coordinates, `bc_point1`'s, the weight and the record's power. -/
def isA3Load : Atom → Bool
  | .load _ p o =>
      ((decide (p = .n (val% «aggregate_claims_loop3» "s0#0")) || decide (p = .n (val% «aggregate_claims_loop3» "s1#0")) ||
        decide (p = .n (val% «aggregate_claims_loop3» "s4#0")) || decide (p = .n (val% «aggregate_claims_loop3» "s3#1"))) &&
        decide (o = 0)) ||
      (decide (p = .n (val% «aggregate_claims_loop3» "fresh")) && decide (o < 19)) ||
      ((decide (p = .n (val% «aggregate_claims_loop3» "carried")) || decide (p = .n (val% «aggregate_claims_loop3» "bc_point1"))) &&
        decide (o < 25))
  | _ => false

set_option maxRecDepth 100000 in
theorem a3_stores : storesOf 9 (coreProgram.getD idx% «aggregate_claims_loop3» default).body =
    a3Stores := by
  decide +kernel

/-- **`aggregate_claims_loop3`, evaluated**: its values defined in order, its atoms but its store
holding from its loads, and the facts of its block on them. -/
noncomputable def a3COk : Bool :=
  let fn := coreProgram.getD idx% «aggregate_claims_loop3» default
  let A := a3A
  let P := (atomsIn (loopPre fn)).filter pureB
  (chk 9 fn.body).isSome && (loopPre fn).all (fun s => match s with | .atom _ => true | _ => false) &&
  A.all (fun a => !needsSide a || isA3Load a) &&
  isMul P (.n (val% «aggregate_claims_loop3» "s0#0")) (.n (val% «aggregate_claims_loop3» "fresh_row")) (.n (val% «aggregate_claims_loop3» "xc")) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop3» "fresh")) (.n (val% «aggregate_claims_loop3» "s0#0")) 0) &&
  isMul P (.n (val% «aggregate_claims_loop3» "s1#0")) (.n (val% «aggregate_claims_loop3» "carried_row")) (.n (val% «aggregate_claims_loop3» "xc")) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop3» "carried")) (.n (val% «aggregate_claims_loop3» "s1#0")) 0) &&
  eqChainOk A (.n (val% «aggregate_claims_loop3» "fresh")) (.n (val% «aggregate_claims_loop3» "bc_point1")) 19 (.n (val% «aggregate_claims_loop3» "eq_fresh@19")) &&
  eqChainOk A (.n (val% «aggregate_claims_loop3» "carried")) (.n (val% «aggregate_claims_loop3» "bc_point1")) 25 (.n (val% «aggregate_claims_loop3» "eq_carried@25")) &&
  isMul P (.n (val% «aggregate_claims_loop3» "s3#0")) (.n (val% «aggregate_claims_loop3» "xc")) (.n (val% «aggregate_claims_loop3» "xc")) &&
  isMul P (.n (val% «aggregate_claims_loop3» "s3#1")) (.n (val% «aggregate_claims_loop3» "bc_chain")) (.n (val% «aggregate_claims_loop3» "s3#0")) &&
  isMul P (.n (val% «aggregate_claims_loop3» "s4#0")) (.n (val% «aggregate_claims_loop3» "bc_wsum")) (.n (val% «aggregate_claims_loop3» "xc")) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop3» "s4#1")) (.n (val% «aggregate_claims_loop3» "s4#0")) 0) &&
  A.any (isLoadAt (.n (val% «aggregate_claims_loop3» "s4#2")) (.n (val% «aggregate_claims_loop3» "s3#1")) 0) &&
  isMul P (.n (val% «aggregate_claims_loop3» "s4#3")) (.n (val% «aggregate_claims_loop3» "eq_fresh@19")) (.n (val% «aggregate_claims_loop3» "eq_cols")) &&
  isMul P (.n (val% «aggregate_claims_loop3» "s4#4")) (.n (val% «aggregate_claims_loop3» "lam")) (.n (val% «aggregate_claims_loop3» "eq_carried@25")) &&
  P.any (isAddAt (.n (val% «aggregate_claims_loop3» "s4#5")) (.n (val% «aggregate_claims_loop3» "s4#3")) (.n (val% «aggregate_claims_loop3» "s4#4"))) &&
  isMul P (.n (val% «aggregate_claims_loop3» "s4#6")) (.n (val% «aggregate_claims_loop3» "s4#2")) (.n (val% «aggregate_claims_loop3» "s4#5")) &&
  P.any (isAddAt (.n (val% «aggregate_claims_loop3» "s4#7")) (.n (val% «aggregate_claims_loop3» "s4#1")) (.n (val% «aggregate_claims_loop3» "s4#6"))) &&
  isMul P (.n (val% «aggregate_claims_loop3» "s4#8")) (.n (val% «aggregate_claims_loop3» "bc_wsum")) (.n (val% «aggregate_claims_loop3» "xc"))

set_option maxRecDepth 100000 in
theorem a3_shape : loopShapeF (coreProgram.getD idx% «aggregate_claims_loop3» default)
    name% «aggregate_claims_loop3» = true ∧
    (coreProgram.getD idx% «aggregate_claims_loop3» default).params.length = 9 := by decide +kernel

set_option maxRecDepth 100000 in
theorem a3c_ok : a3COk = true := by decide +kernel

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **A child's weight** (`aggregate_claims_loop3`), completely. -/
theorem a3_block {x N lfT lcT pt1 chainT wT eqc lam pf pc pw w0 : E}
    (hlf : LoadHolds rd (lfT * x) 0 pf) (hlc : LoadHolds rd (lcT * x) 0 pc)
    (hpf : ∀ j < 19, ∃ v, LoadHolds rd pf j v) (hpc : ∀ j < 25, ∃ v, LoadHolds rd pc j v)
    (hpt : ∀ j < 25, ∃ v, LoadHolds rd pt1 j v)
    (hch : LoadHolds rd (chainT * x ^ 2) 0 pw) (hw : LoadHolds rd (wT * x) 0 w0)
    (hout : LoadHolds rd (wT * x) 1 (w0 + pw *
      (eqEval (memRun rd pf 19) ((memRun rd pt1 19).map (1 + ·)) * eqc +
        lam * eqEval (memRun rd pc 25) ((memRun rd pt1 25).map (1 + ·))))) :
    LoopBlock rd (coreProgram.getD idx% «aggregate_claims_loop3» default) x N
      [lfT, lcT, pt1, chainT, wT, eqc, lam] := by
  obtain ⟨hshape, hlen⟩ := a3_shape
  have hcok := a3c_ok
  simp only [a3COk, Bool.and_eq_true, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hatoms⟩, hneeds⟩, hm9⟩, hl10⟩, hm11⟩, hl12⟩, he1⟩, he2⟩,
    hm168⟩, hm169⟩, hm170⟩, hl171⟩, hl172⟩, hm173⟩, hm174⟩, ha175⟩, hm176⟩, ha177⟩, hm178⟩ := hcok
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hatoms hneeds
  set fn := coreProgram.getD idx% «aggregate_claims_loop3» default
  set A := atomsIn (loopPre fn)
  let args : List E := [x, N, lfT, lcT, pt1, chainT, wT, eqc, lam]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body) := ⟨_, rfl⟩
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
  rw [show args.length = 9 from rfl, ← hσ, a3_stores] at hgs
  have hg : ∀ a ∈ A, Good rd a3Stores (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (loopPre_mem (atom_mem_of_atomsIn ha))
  have hpar : fn.params = (List.range 9).map V.n := params_of_shape hshape hlen
  have par : ∀ i (hi : i < 9), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n (val% «aggregate_claims_loop3» "xc")) = x := par 0 (by omega)
  have hP : ∀ a ∈ A.filter pureB, a.Holds rd σ := pure_holds hg
  have p9 : σ (.n (val% «aggregate_claims_loop3» "s0#0")) = lfT * x := by
    rw [isMul_sound hm9 hP, par 2 (by omega), e0]; rfl
  have p11 : σ (.n (val% «aggregate_claims_loop3» "s1#0")) = lcT * x := by
    rw [isMul_sound hm11 hP, par 3 (by omega), e0]; rfl
  have p169 : σ (.n (val% «aggregate_claims_loop3» "s3#1")) = chainT * x ^ 2 := by
    rw [isMul_sound hm169 hP, isMul_sound hm168 hP, par 5 (by omega), e0, sq]; rfl
  have p170 : σ (.n (val% «aggregate_claims_loop3» "s4#0")) = wT * x := by
    rw [isMul_sound hm170 hP, par 6 (by omega), e0]; rfl
  have ppt : σ (.n (val% «aggregate_claims_loop3» "bc_point1")) = pt1 := par 4 (by omega)
  have hg' : ∀ a ∈ a3A, Good rd a3Stores (fun _ => 0) σ a := fun a ha => hg a (mem_a3A.mp ha).1
  have hnS : ∀ a ∈ a3A, a ∉ a3Stores := fun a ha => (mem_a3A.mp ha).2
  have v10 : σ (.n (val% «aggregate_claims_loop3» "fresh")) = pf := by
    rw [(load_any_val hnS hg' hl10).1, p9, rdAt_of_load hlf]
  have v12 : σ (.n (val% «aggregate_claims_loop3» "carried")) = pc := by
    rw [(load_any_val hnS hg' hl12).1, p11, rdAt_of_load hlc]
  have hat' : ∀ a ∈ a3A, a.Holds rd σ := by
    refine atoms_holds hg' fun a ha hns => ?_
    rcases hneeds a ha with h | h
    · rw [hns] at h; exact absurd h (by simp)
    · cases a <;> simp only [isA3Load, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rename_i d p o
      refine Or.inr (side_load (hnS _ ha) (v := memAt rd (σ p) o) ?_)
      rcases h with (⟨((rfl | rfl) | rfl) | rfl, rfl⟩ | ⟨rfl, ho⟩) | ⟨rfl | rfl, ho⟩
      · rw [p9, memAt_of_load hlf]; exact hlf
      · rw [p11, memAt_of_load hlc]; exact hlc
      · rw [p170, memAt_of_load hw]; exact hw
      · rw [p169, memAt_of_load hch]; exact hch
      · obtain ⟨v, hv⟩ := hpf o ho
        rw [v10, memAt_of_load hv]; exact hv
      · obtain ⟨v, hv⟩ := hpc o ho
        rw [v12, memAt_of_load hv]; exact hv
      · obtain ⟨v, hv⟩ := hpt o ho
        rw [ppt, memAt_of_load hv]; exact hv
  have ef := eqChain_sound he1 hat'
  have ec := eqChain_sound he2 hat'
  rw [v10, ppt] at ef
  rw [v12, ppt] at ec
  have e171 := (load_any_val hnS hg' hl171).1
  have e172 := (load_any_val hnS hg' hl172).1
  rw [p170, rdAt_of_load hw] at e171
  rw [p169, rdAt_of_load hch] at e172
  have hat : ∀ a ∈ A, a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ a3Stores
    · simp only [a3Stores, List.mem_cons, List.not_mem_nil, or_false] at haS
      subst haS
      show LoadHolds rd (σ (.n (val% «aggregate_claims_loop3» "s4#8"))) 1
        (σ (.n (val% «aggregate_claims_loop3» "s4#7")))
      rw [isMul_sound hm178 hP, add_sound ha177 hP, isMul_sound hm176 hP, add_sound ha175 hP,
        isMul_sound hm173 hP, isMul_sound hm174 hP, par 6 (by omega), par 7 (by omega),
        par 8 (by omega), e0, e171, e172, ef, ec]
      exact hout
    · exact hat' a (mem_a3A.mpr ⟨ha, haS⟩)
  refine ⟨σ, ?_, fun s hs => ?_⟩
  · rw [hpar]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
      List.map_nil]
    rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega),
      par 5 (by omega), par 6 (by omega), par 7 (by omega), par 8 (by omega)]
    rfl
  · have := hatoms s hs
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    exact ⟨hat a (mem_atomsIn hs), trivial⟩

end
end LeanVM.Guest.Complete.Agg
