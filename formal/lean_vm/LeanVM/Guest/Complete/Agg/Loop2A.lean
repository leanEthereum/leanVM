module

public import LeanVM.Guest.Complete.Agg.Loop2
public import LeanVM.Guest.Complete.Agg.Loop1A
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop2»

/-!
# `aggregate_claims_loop2`, placed

`a2_blockA`: `a2_block`'s valuation, its atoms holding (`SOk`) and its loads in `A2Reg`, at
the child `j` with every pointer `ptrAt` of its base. `agg_loop2_callAtA`: the loop placed from
every counter by `loopF_callAtA`, its block `lpBlk fs f (m - j)`, ending at its cursor, popping
nothing, every node exact.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.Da

@[expose] public section

/-- `aggregate_claims_loop2`'s region at the child `j`: its record and the next, the pointer
tables' cells, the folded value's cell, the carried claim's value. -/
def A2Reg (ich ilf ilc ifv ipc j : ℕ) (i : ℕ) : Prop :=
  (ich + j * 2 ≤ i ∧ i < ich + j * 2 + 4) ∨ i = ilf + j + 0 ∨ i = ilc + j + 0 ∨ i = ifv + j + 0 ∨ i = ipc + 25

set_option maxRecDepth 20000 in
/-- **`aggregate_claims_loop2`'s block at the child `j`, placed.** -/
theorem a2_blockA {rd : Reader} {j ich ilf ilc ifv ipc : ℕ}
    {x N chainT lfT lcT lamSq fvT lam pf pc fv cv pw acc : E}
    (hx : x = gen ^ j) (hch : chainT = ptrAt ich) (hlfT : lfT = ptrAt ilf) (hlcT : lcT = ptrAt ilc)
    (hfvT : fvT = ptrAt ifv) (hpc : pc = ptrAt ipc)
    (hrow : ReadsAt rd (chainT * x ^ 2) [pw, acc])
    (hnext : ReadsAt rd (chainT * x ^ 2 * gen ^ 2) [pw * lamSq, acc + pw * (fv + lam * cv)])
    (hlf : LoadHolds rd (lfT * x) 0 pf) (hlc : LoadHolds rd (lcT * x) 0 pc) (hfv : LoadHolds rd (fvT * x) 0 fv)
    (hcv : LoadHolds rd pc 25 cv) :
    ∃ σ : Val, (coreProgram.getD idx% «aggregate_claims_loop2» default).params.map σ =
        x :: N :: [chainT, lfT, lcT, lamSq, fvT, lam] ∧
      (∀ s ∈ loopPre (coreProgram.getD idx% «aggregate_claims_loop2» default), SOk rd σ s) ∧
      ∀ q' ∈ (loopPre (coreProgram.getD idx% «aggregate_claims_loop2» default)).filterMap stmtLoad?,
        ∃ i, (σ q'.1).limb 0 * addressOfIndex q'.2 = addressOfIndex i ∧ A2Reg ich ilf ilc ifv ipc j i := by
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
  refine ⟨σ, ?_, fun s hs => ?_, fun q' hq => ?_⟩
  · rw [hpar]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
      List.map_nil]
    rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega), par 5 (by omega), par 6 (by omega), par 7 (by omega)]
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
        have hrow' : σ (.n (val% «aggregate_claims_loop2» "row")) = ptrAt (ich + j * 2) := by
          rw [p8, hch, hx, ← pow_mul, ptrAt_mul_gen_pow]
        by_cases haS : Atom.load d p o ∈ a2Stores
        · simp only [a2Stores, List.mem_cons, List.not_mem_nil, or_false, Atom.load.injEq] at haS
          rcases haS with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
          · exact ⟨ich + j * 2 + 2, by rw [hrow', addr_ptrAt], Or.inl ⟨by omega, by omega⟩⟩
          · exact ⟨ich + j * 2 + 3, by rw [hrow', addr_ptrAt], Or.inl ⟨by omega, by omega⟩⟩
        · rcases hneeds _ (mem_a2A.mpr ⟨ha, haS⟩) with h | h
          · simp [needsSide] at h
          · simp only [isA2Load, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
            rcases h with ((⟨rfl, ho⟩ | ⟨rfl | rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
            · exact ⟨ich + j * 2 + o, by rw [hrow', addr_ptrAt], Or.inl ⟨by omega, by omega⟩⟩
            · exact ⟨ilf + j + 0, by rw [p10, hlfT, hx, ptrAt_mul_gen_pow, addr_ptrAt], Or.inr (Or.inl rfl)⟩
            · exact ⟨ilc + j + 0, by rw [p12, hlcT, hx, ptrAt_mul_gen_pow, addr_ptrAt],
                Or.inr (Or.inr (Or.inl rfl))⟩
            · exact ⟨ifv + j + 0, by rw [p16, hfvT, hx, ptrAt_mul_gen_pow, addr_ptrAt],
                Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
            · exact ⟨ipc + 25, by rw [v13, hpc, addr_ptrAt], Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
      | _ => simp [stmtLoad?] at hq
    | _ => simp [stmtLoad?] at hq

theorem a2_find : coreProgram.find? name% «aggregate_claims_loop2» =
    some (coreProgram.getD idx% «aggregate_claims_loop2» default) := find_of_idx a2_idx

theorem a2_loop : coreProgram.loop name% «aggregate_claims_loop2» = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem a2_plain : (loopPre (coreProgram.getD idx% «aggregate_claims_loop2» default)).all loopPlainB = true := by
  decide +kernel

/-- **`aggregate_claims_loop2` completes placed** from every counter `j < m`, on memories where
each child's record words hold (`a2_block`'s, at `ptrAt` bases), loading in a region holding each
child's `A2Reg`. -/
theorem agg_loop2_callAtA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k m : ℕ}
    (hm : m < 2 ^ 34) {ich ilf ilc ifv : ℕ} {lamSq lam : E} {ipc : ℕ → ℕ} {R : ℕ → Prop} {Pre : Reader → Prop}
    (hpre : ∀ rd, Pre rd → ∀ c < m, ∃ pf fv cv pw acc : E,
      ReadsAt rd (ptrAt ich * (gen ^ c) ^ 2) [pw, acc] ∧
      ReadsAt rd (ptrAt ich * (gen ^ c) ^ 2 * gen ^ 2) [pw * lamSq, acc + pw * (fv + lam * cv)] ∧
      LoadHolds rd (ptrAt ilf * gen ^ c) 0 pf ∧ LoadHolds rd (ptrAt ilc * gen ^ c) 0 (ptrAt (ipc c)) ∧
      LoadHolds rd (ptrAt ifv * gen ^ c) 0 fv ∧ LoadHolds rd (ptrAt (ipc c)) 25 cv)
    (hR : ∀ c < m, ∀ i, A2Reg ich ilf ilc ifv (ipc c) c i → R i) :
    ∀ j < m, ∀ fp c, fp + lpBlk fs name% «aggregate_claims_loop2» (m - j) ≤ c →
      CallAtA fs al cert k name% «aggregate_claims_loop2»
        (gen ^ j :: gen ^ m :: [ptrAt ich, ptrAt ilf, ptrAt ilc, lamSq, ptrAt ifv, lam])
        [] R (fun _ => False) (fun _ => True) Pre FreePost (lpBlk fs name% «aggregate_claims_loop2» (m - j)) fp c c :=
  fun j hj fp c hc =>
    (loopF_callAtA a2_find a2_shape.1 a2_loop a2_plain hm (hblk := fun j' hj' rd _ hp => by
      obtain ⟨pf, fv, cv, pw, acc, h1, h2, h3, h4, h5, h6⟩ := hpre rd hp j' hj'
      obtain ⟨σ, hpar, hok, hlo⟩ := a2_blockA (N := gen ^ m) rfl rfl rfl rfl rfl rfl h1 h2 h3 h4 h5 h6
      exact ⟨σ, hpar, hok, fun q' hq => by
        obtain ⟨i, hi, hr⟩ := hlo q' hq
        exact ⟨i, hi, hR j' hj' i hr⟩⟩) j hj fp c hc).free agg_loop2_free.1 agg_loop2_free.2

end
end LeanVM.Guest.Complete.Agg
