module

public import LeanVM.Guest.Complete.Agg.Loop3
public import LeanVM.Guest.Complete.Agg.Loop1A
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«aggregate_claims_loop3»

/-!
# `aggregate_claims_loop3`, placed

`a3_blockA`: `a3_block`'s valuation, its atoms holding (`SOk`) and its loads in `A3Reg`, at
the child `j` with every pointer `ptrAt` of its base. `agg_loop3_callAtA`: the loop placed from
every counter by `loopF_callAtA`, its block `lpBlk fs f (m - j)`, ending at its cursor, popping
nothing, every node exact.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier
open LeanVM.Guest.B1 LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.Da

@[expose] public section

/-- `aggregate_claims_loop3`'s region at the child `j`: the pointer tables' cells, the weight
and the next, the record's power, the claims' points and `bc_point1`. -/
def A3Reg (ilf ilc iw ich ipf ipc ipt j : ℕ) (i : ℕ) : Prop :=
  i = ilf + j + 0 ∨ i = ilc + j + 0 ∨ (iw + j ≤ i ∧ i < iw + j + 2) ∨ i = ich + j * 2 + 0 ∨
    (ipf ≤ i ∧ i < ipf + 19) ∨ (ipc ≤ i ∧ i < ipc + 25) ∨ (ipt ≤ i ∧ i < ipt + 25)

set_option maxRecDepth 20000 in
/-- **`aggregate_claims_loop3`'s block at the child `j`, placed.** -/
theorem a3_blockA {rd : Reader} {j ilf ilc iw ich ipf ipc ipt : ℕ}
    {x N lfT lcT pt1 chainT wT eqc lam pf pc pw w0 : E}
    (hx : x = gen ^ j) (hlfT : lfT = ptrAt ilf) (hlcT : lcT = ptrAt ilc) (hwT : wT = ptrAt iw)
    (hchE : chainT = ptrAt ich) (hpf' : pf = ptrAt ipf) (hpc' : pc = ptrAt ipc) (hpt1 : pt1 = ptrAt ipt)
    (hlf : LoadHolds rd (lfT * x) 0 pf) (hlc : LoadHolds rd (lcT * x) 0 pc)
    (hpf : ∀ j < 19, ∃ v, LoadHolds rd pf j v) (hpc : ∀ j < 25, ∃ v, LoadHolds rd pc j v)
    (hpt : ∀ j < 25, ∃ v, LoadHolds rd pt1 j v)
    (hch : LoadHolds rd (chainT * x ^ 2) 0 pw) (hw : LoadHolds rd (wT * x) 0 w0)
    (hout : LoadHolds rd (wT * x) 1 (w0 + pw *
      (eqEval (memRun rd pf 19) ((memRun rd pt1 19).map (1 + ·)) * eqc +
        lam * eqEval (memRun rd pc 25) ((memRun rd pt1 25).map (1 + ·))))) :
    ∃ σ : Val, (coreProgram.getD idx% «aggregate_claims_loop3» default).params.map σ =
        x :: N :: [lfT, lcT, pt1, chainT, wT, eqc, lam] ∧
      (∀ s ∈ loopPre (coreProgram.getD idx% «aggregate_claims_loop3» default), SOk rd σ s) ∧
      ∀ q' ∈ (loopPre (coreProgram.getD idx% «aggregate_claims_loop3» default)).filterMap stmtLoad?,
        ∃ i, (σ q'.1).limb 0 * addressOfIndex q'.2 = addressOfIndex i ∧ A3Reg ilf ilc iw ich ipf ipc ipt j i := by
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
  refine ⟨σ, ?_, fun s hs => ?_, fun q' hq => ?_⟩
  · rw [hpar]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
      List.map_nil]
    rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega), par 5 (by omega), par 6 (by omega), par 7 (by omega), par 8 (by omega)]
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
        have p178 : σ (.n (val% «aggregate_claims_loop3» "s4#8")) = wT * x := by
          rw [isMul_sound hm178 hP, par 6 (by omega), e0]; rfl
        by_cases haS : Atom.load d p o ∈ a3Stores
        · simp only [a3Stores, List.mem_cons, List.not_mem_nil, or_false, Atom.load.injEq] at haS
          obtain ⟨-, rfl, rfl⟩ := haS
          exact ⟨iw + j + 1, by rw [p178, hwT, hx, ptrAt_mul_gen_pow, addr_ptrAt],
            Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))⟩
        · rcases hneeds _ (mem_a3A.mpr ⟨ha, haS⟩) with h | h
          · simp [needsSide] at h
          · simp only [isA3Load, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
            rcases h with (⟨((rfl | rfl) | rfl) | rfl, rfl⟩ | ⟨rfl, ho⟩) | ⟨rfl | rfl, ho⟩
            · exact ⟨ilf + j + 0, by rw [p9, hlfT, hx, ptrAt_mul_gen_pow, addr_ptrAt], Or.inl rfl⟩
            · exact ⟨ilc + j + 0, by rw [p11, hlcT, hx, ptrAt_mul_gen_pow, addr_ptrAt], Or.inr (Or.inl rfl)⟩
            · exact ⟨iw + j + 0, by rw [p170, hwT, hx, ptrAt_mul_gen_pow, addr_ptrAt],
                Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))⟩
            · exact ⟨ich + j * 2 + 0, by rw [p169, hchE, hx, ← pow_mul, ptrAt_mul_gen_pow, addr_ptrAt],
                Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
            · exact ⟨ipf + o, by rw [v10, hpf', addr_ptrAt], Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))⟩
            · exact ⟨ipc + o, by rw [v12, hpc', addr_ptrAt],
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))⟩
            · exact ⟨ipt + o, by rw [ppt, hpt1, addr_ptrAt],
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))⟩
      | _ => simp [stmtLoad?] at hq
    | _ => simp [stmtLoad?] at hq

theorem a3_find : coreProgram.find? name% «aggregate_claims_loop3» =
    some (coreProgram.getD idx% «aggregate_claims_loop3» default) := find_of_idx a3_idx

theorem a3_loop : coreProgram.loop name% «aggregate_claims_loop3» = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem a3_plain : (loopPre (coreProgram.getD idx% «aggregate_claims_loop3» default)).all loopPlainB = true := by
  decide +kernel

/-- **`aggregate_claims_loop3` completes placed** from every counter `j < m`, on memories where
each child's weight words hold (`a3_block`'s, at `ptrAt` bases), loading in a region holding each
child's `A3Reg`. -/
theorem agg_loop3_callAtA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k m : ℕ}
    (hm : m < 2 ^ 34) {ilf ilc ipt ich iw : ℕ} {eqc lam : E} {ipf ipc : ℕ → ℕ} {R : ℕ → Prop}
    {Pre : Reader → Prop}
    (hpre : ∀ rd, Pre rd → ∀ c < m, ∃ pw w0 : E,
      LoadHolds rd (ptrAt ilf * gen ^ c) 0 (ptrAt (ipf c)) ∧ LoadHolds rd (ptrAt ilc * gen ^ c) 0 (ptrAt (ipc c)) ∧
      (∀ j < 19, ∃ v, LoadHolds rd (ptrAt (ipf c)) j v) ∧ (∀ j < 25, ∃ v, LoadHolds rd (ptrAt (ipc c)) j v) ∧
      (∀ j < 25, ∃ v, LoadHolds rd (ptrAt ipt) j v) ∧
      LoadHolds rd (ptrAt ich * (gen ^ c) ^ 2) 0 pw ∧ LoadHolds rd (ptrAt iw * gen ^ c) 0 w0 ∧
      LoadHolds rd (ptrAt iw * gen ^ c) 1 (w0 + pw *
        (eqEval (memRun rd (ptrAt (ipf c)) 19) ((memRun rd (ptrAt ipt) 19).map (1 + ·)) * eqc +
          lam * eqEval (memRun rd (ptrAt (ipc c)) 25) ((memRun rd (ptrAt ipt) 25).map (1 + ·)))))
    (hR : ∀ c < m, ∀ i, A3Reg ilf ilc iw ich (ipf c) (ipc c) ipt c i → R i) :
    ∀ j < m, ∀ fp c, fp + lpBlk fs name% «aggregate_claims_loop3» (m - j) ≤ c →
      CallAtA fs al cert k name% «aggregate_claims_loop3»
        (gen ^ j :: gen ^ m :: [ptrAt ilf, ptrAt ilc, ptrAt ipt, ptrAt ich, ptrAt iw, eqc, lam])
        [] R (fun _ => False) (fun _ => True) Pre FreePost (lpBlk fs name% «aggregate_claims_loop3» (m - j)) fp c c :=
  fun j hj fp c hc =>
    (loopF_callAtA a3_find a3_shape.1 a3_loop a3_plain hm (hblk := fun j' hj' rd _ hp => by
      obtain ⟨pw, w0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpre rd hp j' hj'
      obtain ⟨σ, hpar, hok, hlo⟩ :=
        a3_blockA (N := gen ^ m) rfl rfl rfl rfl rfl rfl rfl rfl h1 h2 h3 h4 h5 h6 h7 h8
      exact ⟨σ, hpar, hok, fun q' hq => by
        obtain ⟨i, hi, hr⟩ := hlo q' hq
        exact ⟨i, hi, hR j' hj' i hr⟩⟩) j hj fp c hc).free agg_loop3_free.1 agg_loop3_free.2

end
end LeanVM.Guest.Complete.Agg
