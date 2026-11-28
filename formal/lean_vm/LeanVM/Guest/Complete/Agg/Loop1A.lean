module

public import LeanVM.Guest.Complete.Agg.Loop1
public import LeanVM.Guest.Complete.LoopFA
public import LeanVM.Guest.Complete.DaPadA
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop1»

/-!
# `aggregate_claims_loop1`, placed

`a1_blockA`: `a1_block`'s valuation, its atoms holding (`SOk`) and its loads in a region holding
the pointer table's cell `lf + j`, `eq_col`'s `36` cells, the fresh claim's values `q + 19 ..< q + 55`
and the folded value's cell `v + j`, at the child `j` with every pointer `ptrAt` of its base.
`agg_loop1_callAtA`: the loop placed from every counter by `loopF_callAtA`, its block
`lpBlk fs f (m - j)`, ending at its cursor, popping nothing, every node exact.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.Da

@[expose] public section

theorem addr_ptrAt (b o : ℕ) : (ptrAt b).limb 0 * addressOfIndex o = addressOfIndex (b + o) :=
  addr_ofK b o

/-- `aggregate_claims_loop1`'s region at the child `j`. -/
def A1Reg (lf e q v j : ℕ) (i : ℕ) : Prop :=
  i = lf + j ∨ (e ≤ i ∧ i < e + 36) ∨ (q + 19 ≤ i ∧ i < q + 55) ∨ i = v + j

set_option maxRecDepth 20000 in
/-- **`aggregate_claims_loop1`'s block at the child `j`, placed**: `a1_block`'s valuation, its
atoms holding, its loads in `A1Reg`. -/
theorem a1_blockA {rd : Reader} {j : ℕ} {N : E} {lf e q v : ℕ}
    (hlf : LoadHolds rd (ptrAt lf * gen ^ j) 0 (ptrAt q))
    (heq : ∀ i < 36, ∃ w, LoadHolds rd (ptrAt e) i w) (hfr : ∀ i < 36, ∃ w, LoadHolds rd (ptrAt q) (19 + i) w)
    (hout : LoadHolds rd (ptrAt v * gen ^ j) 0 (fvAcc rd (ptrAt e) (ptrAt q) 36)) :
    ∃ σ : Val, (coreProgram.getD idx% «aggregate_claims_loop1» default).params.map σ =
        gen ^ j :: N :: [ptrAt lf, ptrAt e, ptrAt v] ∧
      (∀ s ∈ loopPre (coreProgram.getD idx% «aggregate_claims_loop1» default), SOk rd σ s) ∧
      ∀ q' ∈ (loopPre (coreProgram.getD idx% «aggregate_claims_loop1» default)).filterMap stmtLoad?,
        ∃ i, (σ q'.1).limb 0 * addressOfIndex q'.2 = addressOfIndex i ∧ A1Reg lf e q v j i := by
  obtain ⟨hshape, hlen⟩ := a1_shape
  have hcok := a1c_ok
  simp only [a1COk, Bool.and_eq_true, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hatoms⟩, hneeds⟩, hm5⟩, hl6⟩, hfv⟩, hm150⟩ := hcok
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hatoms hneeds
  set fn := coreProgram.getD idx% «aggregate_claims_loop1» default
  set A := atomsIn (loopPre fn)
  set x := gen ^ j
  let args : List E := [x, N, ptrAt lf, ptrAt e, ptrAt v]
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
  have p5 : σ (.n (val% «aggregate_claims_loop1» "fresh~0")) = ptrAt lf * x := by
    rw [isMul_sound hm5 hP, par 2 (by omega), e0]; rfl
  have pe : σ (.n (val% «aggregate_claims_loop1» "eq_col")) = ptrAt e := par 3 (by omega)
  have hg' : ∀ a ∈ a1A, Good rd a1Stores (fun _ => 0) σ a := fun a ha => hg a (mem_a1A.mp ha).1
  have hnS : ∀ a ∈ a1A, a ∉ a1Stores := fun a ha => (mem_a1A.mp ha).2
  have v6 : σ (.n (val% «aggregate_claims_loop1» "fresh")) = ptrAt q := by
    rw [(load_any_val hnS hg' hl6).1, p5, rdAt_of_load hlf]
  have p150 : σ (.n (val% «aggregate_claims_loop1» "s3#0")) = ptrAt v * x := by
    rw [isMul_sound hm150 hP, par 4 (by omega), e0]; rfl
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
      · obtain ⟨w, hw⟩ := heq o ho
        rw [pe, memAt_of_load hw]; exact hw
      · obtain ⟨w, hw⟩ := hfr (o - 19) (by omega)
        rw [show 19 + (o - 19) = o by omega] at hw
        rw [v6, memAt_of_load hw]; exact hw
  have hfvv := fvChain_sound hfv hat'
  rw [pe, v6] at hfvv
  have hat : ∀ a ∈ A, a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ a1Stores
    · simp only [a1Stores, List.mem_cons, List.not_mem_nil, or_false] at haS
      subst haS
      show LoadHolds rd (σ (.n (val% «aggregate_claims_loop1» "s3#0"))) 0
        (σ (.n (val% «aggregate_claims_loop1» "fv@36")))
      rw [p150, hfvv]
      exact hout
    · exact hat' a (mem_a1A.mpr ⟨ha, haS⟩)
  refine ⟨σ, ?_, fun s hs => ?_, fun q' hq => ?_⟩
  · rw [hpar]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
      List.map_nil]
    rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega)]
    rfl
  · have := hatoms s hs
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    exact hat a (mem_atomsIn hs)
  · obtain ⟨s, hs, hq⟩ := List.mem_filterMap.mp hq
    cases s with
    | atom a =>
      cases a with
      | load d p o =>
        simp only [stmtLoad?, Option.some.injEq] at hq
        subst hq
        have ha : Atom.load d p o ∈ A := mem_atomsIn hs
        by_cases haS : Atom.load d p o ∈ a1Stores
        · simp only [a1Stores, List.mem_cons, List.not_mem_nil, or_false, Atom.load.injEq] at haS
          obtain ⟨-, rfl, rfl⟩ := haS
          refine ⟨v + j + 0, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
          rw [p150, ptrAt_mul_gen_pow, addr_ptrAt]
        · have ha' : Atom.load d p o ∈ a1A := mem_a1A.mpr ⟨ha, haS⟩
          rcases hneeds _ ha' with h | h
          · simp [needsSide] at h
          · simp only [isA1Load, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
            rcases h with (⟨rfl, rfl⟩ | ⟨rfl, ho⟩) | ⟨⟨rfl, ho1⟩, ho2⟩
            · exact ⟨lf + j + 0, by rw [p5, ptrAt_mul_gen_pow, addr_ptrAt], Or.inl rfl⟩
            · exact ⟨e + o, by rw [pe, addr_ptrAt], Or.inr (Or.inl ⟨by omega, by omega⟩)⟩
            · exact ⟨q + o, by rw [v6, addr_ptrAt], Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))⟩
      | _ => simp [stmtLoad?] at hq
    | _ => simp [stmtLoad?] at hq

theorem a1_find : coreProgram.find? name% «aggregate_claims_loop1» =
    some (coreProgram.getD idx% «aggregate_claims_loop1» default) := find_of_idx a1_idx

theorem a1_loop : coreProgram.loop name% «aggregate_claims_loop1» = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem a1_plain : (loopPre (coreProgram.getD idx% «aggregate_claims_loop1» default)).all loopPlainB = true := by
  decide +kernel

/-- **`aggregate_claims_loop1` completes placed** from every counter `j < m`, on memories where
each child's words of its block hold (`A1Pre` at `ptrAt` bases), loading in a region holding each
child's `A1Reg`: block `lpBlk fs f (m - j)`, ending at its cursor, popping nothing, every node
exact. -/
theorem agg_loop1_callAtA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k m : ℕ}
    (hm : m < 2 ^ 34) {lf e v : ℕ} {qs : ℕ → ℕ} {R : ℕ → Prop} {Pre : Reader → Prop}
    (hpre : ∀ rd, Pre rd → ∀ c < m, LoadHolds rd (ptrAt lf * gen ^ c) 0 (ptrAt (qs c)) ∧
      (∀ i < 36, ∃ w, LoadHolds rd (ptrAt e) i w) ∧ (∀ i < 36, ∃ w, LoadHolds rd (ptrAt (qs c)) (19 + i) w) ∧
      LoadHolds rd (ptrAt v * gen ^ c) 0 (fvAcc rd (ptrAt e) (ptrAt (qs c)) 36))
    (hR : ∀ c < m, ∀ i, A1Reg lf e (qs c) v c i → R i) :
    ∀ j < m, ∀ fp c, fp + lpBlk fs name% «aggregate_claims_loop1» (m - j) ≤ c →
      CallAtA fs al cert k name% «aggregate_claims_loop1» (gen ^ j :: gen ^ m :: [ptrAt lf, ptrAt e, ptrAt v])
        [] R (fun _ => False) (fun _ => True) Pre FreePost (lpBlk fs name% «aggregate_claims_loop1» (m - j)) fp c c :=
  fun j hj fp c hc =>
    (loopF_callAtA a1_find a1_shape.1 a1_loop a1_plain hm (hblk := fun j' hj' rd _ hp => by
      obtain ⟨h1, h2, h3, h4⟩ := hpre rd hp j' hj'
      obtain ⟨σ, hpar, hok, hlo⟩ := a1_blockA (N := gen ^ m) h1 h2 h3 h4
      exact ⟨σ, hpar, hok, fun q' hq => by
        obtain ⟨i, hi, hr⟩ := hlo q' hq
        exact ⟨i, hi, hR j' hj' i hr⟩⟩) j hj fp c hc).free agg_loop1_free.1 agg_loop1_free.2

end
end LeanVM.Guest.Complete.Agg
