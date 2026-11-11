/-
  LeanVM.Guest.B1.Main.AggL26Complete

  `__loop34` (a child's lambdas) and `__loop35` (a child's weight), completely.
-/

module

public import LeanVM.Guest.B1.Main.AggL26CChk

/-!
# A child's record and weight, completely

`l26_block`: `__loop34`'s block at the child `x` holds on the evaluated valuation (`Fwd.ev`) when
its record (`chain·x^2`) holds a power of `λ` and a running claim, the next record the power times
`λ²` and the claim on, and the pointer tables the child's claims' values. Its atoms but its
stores hold (their side conditions its loads), which its stores find.

`l27_block`: `__loop35`'s block at `x` holds when the pointer tables point to the claims' points,
`pt1` holds `bc_point1` (`r1`, the point `1 + r1`), the record the power of `λ`, and the weights' table at `x` the
weight and the weight on.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Da

@[expose] public section

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **A child's record** (`__loop34`). -/
theorem l26_block {x N chainT lfT lcT lamSq lam pf pc fv cv pw acc : E}
    (hrow : ReadsAt rd (chainT * x ^ 2) [pw, acc])
    (hnext : ReadsAt rd (chainT * x ^ 2 * gen ^ 2) [pw * lamSq, acc + pw * (fv + lam * cv)])
    (hlf : LoadHolds rd (lfT * x) 0 pf) (hlc : LoadHolds rd (lcT * x) 0 pc)
    (hfv : LoadHolds rd pf 23 fv) (hcv : LoadHolds rd pc 23 cv) :
    LoopBlock rd (coreProgram.getD 408 default) x N [chainT, lfT, lcT, lamSq, lam] := by
  obtain ⟨hshape, hlen⟩ := l26_shape
  have hcok := l26c_ok
  simp only [l26COk, Bool.and_eq_true, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hatoms⟩, hcanA⟩, hneeds⟩, hm7⟩, hm8⟩, hl9⟩, hm10⟩, hl11⟩,
    hm12⟩, hl13⟩, hm14⟩, hl15⟩, hl16⟩, hl17⟩, hm18⟩, ha19⟩, hm20⟩, ha21⟩ := hcok
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hatoms hneeds
  set fn := coreProgram.getD 408 default
  set A := atomsIn (loopPre fn)
  let args : List E := [x, N, chainT, lfT, lcT, lamSq, lam]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body) := ⟨_, rfl⟩
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
  rw [show args.length = 7 from rfl, ← hσ, l26_stores] at hgs
  have hg : ∀ a ∈ A, Good rd l26Stores (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (loopPre_mem (atom_mem_of_atomsIn ha))
  have hpar : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] := by
    rw [params_of_shape hshape hlen]; rfl
  have par : ∀ i (hi : i < 7), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = x := par 0 (by omega)
  have hP : ∀ a ∈ A.filter pureB, a.Holds rd σ := pure_holds hg
  have p8 : σ (.n 8) = chainT * x ^ 2 := by
    rw [isMul_sound hm8 hP, isMul_sound hm7 hP, par 2 (by omega), e0, sq]; rfl
  have p10 : σ (.n 10) = lfT * x := by rw [isMul_sound hm10 hP, par 3 (by omega), e0]; rfl
  have p12 : σ (.n 12) = lcT * x := by rw [isMul_sound hm12 hP, par 4 (by omega), e0]; rfl
  have hr0 : LoadHolds rd (chainT * x ^ 2) 0 pw := hrow 0 (by simp)
  have hr1 : LoadHolds rd (chainT * x ^ 2) 1 acc := hrow 1 (by simp)
  -- the atoms but the stores
  have hg' : ∀ a ∈ l26A, Good rd l26Stores (fun _ => 0) σ a := fun a ha =>
    hg a (mem_l26A.mp ha).1
  have hnS : ∀ a ∈ l26A, a ∉ l26Stores := fun a ha => (mem_l26A.mp ha).2
  have v11 : σ (.n 11) = pf := by rw [(load_any_val hnS hg' hl11).1, p10, rdAt_of_load hlf]
  have v13 : σ (.n 13) = pc := by rw [(load_any_val hnS hg' hl13).1, p12, rdAt_of_load hlc]
  have hat' : ∀ a ∈ l26A, a.Holds rd σ := by
    refine atoms_holds hidx hcanA hg' (fun i hi => absurd hi (by simp)) fun a ha hns => ?_
    rcases hneeds a ha with h | h
    · rw [hns] at h; exact absurd h (by simp)
    · cases a <;> simp only [isL26Load, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rename_i d p o
      refine Or.inr (side_load (hnS _ ha) (v := memAt rd (σ p) o) ?_)
      rcases h with (⟨rfl, ho⟩ | ⟨rfl | rfl, rfl⟩) | ⟨rfl | rfl, rfl⟩
      · rcases (show o = 0 ∨ o = 1 by omega) with rfl | rfl
        · rw [p8, memAt_of_load hr0]; exact hr0
        · rw [p8, memAt_of_load hr1]; exact hr1
      · rw [p10, memAt_of_load hlf]; exact hlf
      · rw [p12, memAt_of_load hlc]; exact hlc
      · rw [v11, memAt_of_load hfv]; exact hfv
      · rw [v13, memAt_of_load hcv]; exact hcv
  -- the stores
  have e9 := (load_any_val hnS hg' hl9).1
  have e15 := (load_any_val hnS hg' hl15).1
  have e16 := (load_any_val hnS hg' hl16).1
  have e17 := (load_any_val hnS hg' hl17).1
  rw [p8, rdAt_of_load hr0] at e9
  rw [p8, rdAt_of_load hr1] at e15
  rw [v11, rdAt_of_load hfv] at e16
  rw [v13, rdAt_of_load hcv] at e17
  have hn0 : LoadHolds rd (chainT * x ^ 2) 2 (pw * lamSq) := by
    rw [show (2 : ℕ) = 2 + 0 from rfl, ← loadHolds_mul_gen_pow]; exact hnext 0 (by simp)
  have hn1 : LoadHolds rd (chainT * x ^ 2) 3 (acc + pw * (fv + lam * cv)) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, ← loadHolds_mul_gen_pow]; exact hnext 1 (by simp)
  have hat : ∀ a ∈ A, a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ l26Stores
    · simp only [l26Stores, List.mem_cons, List.not_mem_nil, or_false] at haS
      rcases haS with rfl | rfl
      · show LoadHolds rd (σ (.n 8)) 2 (σ (.n 14))
        rw [p8, isMul_sound hm14 hP, e9, par 5 (by omega)]
        exact hn0
      · show LoadHolds rd (σ (.n 8)) 3 (σ (.n 21))
        rw [p8, add_sound ha21 hP, isMul_sound hm20 hP, add_sound ha19 hP, isMul_sound hm18 hP,
          e9, e15, e16, e17, par 6 (by omega)]
        exact hn1
    · exact hat' a (mem_l26A.mpr ⟨ha, haS⟩)
  refine ⟨σ, ?_, fun s hs => ?_⟩
  · rw [hpar]
    simp only [List.map_cons, List.map_nil]
    rw [e0, par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega),
      par 5 (by omega), par 6 (by omega)]
    rfl
  · have := hatoms s hs
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    exact ⟨hat a (mem_atomsIn hs), trivial⟩

set_option maxRecDepth 20000 in
/-- **A child's weight** (`__loop35`). -/
theorem l27_block {x N lfT lcT pt1 chainT wT lam pf pc pw wc : E} {pp pq r1 : List E}
    (hlf : LoadHolds rd (lfT * x) 0 pf) (hlc : LoadHolds rd (lcT * x) 0 pc)
    (hpf : ReadsAt rd pf pp) (hpc : ReadsAt rd pc pq) (hr : ReadsAt rd pt1 r1)
    (hpl : pp.length = 23) (hql : pq.length = 23) (hrl : r1.length = 23)
    (hpw : LoadHolds rd (chainT * x ^ 2) 0 pw) (hw : LoadHolds rd (wT * x) 0 wc)
    (hw1 : LoadHolds rd (wT * x) 1 (wc + pw * (eqEval pp (r1.map (1 + ·)) +
      lam * eqEval pq (r1.map (1 + ·))))) :
    LoopBlock rd (coreProgram.getD 410 default) x N [lfT, lcT, pt1, chainT, wT, lam] := by
  obtain ⟨hshape, hlen⟩ := l27_shape
  have hcok := l27c_ok
  simp only [l27COk, Bool.and_eq_true, Option.isSome_iff_exists] at hcok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c', hchk⟩, hatoms⟩, hcanA⟩, hneeds⟩, hm8⟩, hl9⟩, hm10⟩, hl11⟩, he1⟩,
    he2⟩, hm171⟩, hm172⟩, hm173⟩, hl174⟩, hl175⟩, hm176⟩, ha177⟩, hm178⟩, ha179⟩, hm180⟩ := hcok
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hatoms hneeds
  set fn := coreProgram.getD 410 default
  set A := atomsIn (loopPre fn)
  let args : List E := [x, N, lfT, lcT, pt1, chainT, wT, lam]
  obtain ⟨σ, hσ⟩ : ∃ σ : Val, σ = B1.Val.ofArgs (ev rd (fun _ => 0) args fn.body) := ⟨_, rfl⟩
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) fn.body args hchk
  rw [show args.length = 8 from rfl, ← hσ, l27_stores] at hgs
  have hg : ∀ a ∈ A, Good rd l27Stores (fun _ => 0) σ a := fun a ha =>
    hgs (.atom a) (loopPre_mem (atom_mem_of_atomsIn ha))
  have hpar : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] := by
    rw [params_of_shape hshape hlen]; rfl
  have par : ∀ i (hi : i < 8), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n 0) = x := par 0 (by omega)
  have e4 : σ (.n 4) = pt1 := par 4 (by omega)
  have hP : ∀ a ∈ A.filter pureB, a.Holds rd σ := pure_holds hg
  have p8 : σ (.n 8) = lfT * x := by rw [isMul_sound hm8 hP, par 2 (by omega), e0]; rfl
  have p10 : σ (.n 10) = lcT * x := by rw [isMul_sound hm10 hP, par 3 (by omega), e0]; rfl
  have p172 : σ (.n 172) = chainT * x ^ 2 := by
    rw [isMul_sound hm172 hP, isMul_sound hm171 hP, par 5 (by omega), e0, sq]; rfl
  have p173 : σ (.n 173) = wT * x := by rw [isMul_sound hm173 hP, par 6 (by omega), e0]; rfl
  have p180 : σ (.n 180) = wT * x := by rw [isMul_sound hm180 hP, par 6 (by omega), e0]; rfl
  -- the atoms but the store
  have hg' : ∀ a ∈ l27A, Good rd l27Stores (fun _ => 0) σ a := fun a ha =>
    hg a (mem_l27A.mp ha).1
  have hnS : ∀ a ∈ l27A, a ∉ l27Stores := fun a ha => (mem_l27A.mp ha).2
  have v9 : σ (.n 9) = pf := by rw [(load_any_val hnS hg' hl9).1, p8, rdAt_of_load hlf]
  have v11 : σ (.n 11) = pc := by rw [(load_any_val hnS hg' hl11).1, p10, rdAt_of_load hlc]
  have hat' : ∀ a ∈ l27A, a.Holds rd σ := by
    refine atoms_holds hidx hcanA hg' (fun i hi => absurd hi (by simp)) fun a ha hns => ?_
    rcases hneeds a ha with h | h
    · rw [hns] at h; exact absurd h (by simp)
    · cases a <;> simp only [isL27Load, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rename_i d p o
      refine Or.inr (side_load (hnS _ ha) (v := memAt rd (σ p) o) ?_)
      rcases h with ((((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) |
        ⟨(rfl | rfl) | rfl, ho⟩)
      · rw [p8, memAt_of_load hlf]; exact hlf
      · rw [p10, memAt_of_load hlc]; exact hlc
      · rw [p172, memAt_of_load hpw]; exact hpw
      · rw [p173, memAt_of_load hw]; exact hw
      · rw [e4, memAt_of_load (hr o (by omega))]; exact hr o (by omega)
      · rw [v9, memAt_of_load (hpf o (by omega))]; exact hpf o (by omega)
      · rw [v11, memAt_of_load (hpc o (by omega))]; exact hpc o (by omega)
  -- the store
  have mp : memRun rd pf 23 = pp := by rw [← hpl]; exact (readsAt_memRun hpf).symm
  have mq : memRun rd pc 23 = pq := by rw [← hql]; exact (readsAt_memRun hpc).symm
  have mr : memRun rd pt1 23 = r1 := by rw [← hrl]; exact (readsAt_memRun hr).symm
  have ef := eqChain_sound he1 hat'
  have ec := eqChain_sound he2 hat'
  rw [v9, e4, mp, mr] at ef
  rw [v11, e4, mq, mr] at ec
  have e174 := (load_any_val hnS hg' hl174).1
  have e175 := (load_any_val hnS hg' hl175).1
  rw [p173, rdAt_of_load hw] at e174
  rw [p172, rdAt_of_load hpw] at e175
  have hat : ∀ a ∈ A, a.Holds rd σ := fun a ha => by
    by_cases haS : a ∈ l27Stores
    · simp only [l27Stores, List.mem_cons, List.not_mem_nil, or_false] at haS
      subst haS
      show LoadHolds rd (σ (.n 180)) 1 (σ (.n 179))
      rw [p180, add_sound ha179 hP, isMul_sound hm178 hP, add_sound ha177 hP,
        isMul_sound hm176 hP, e174, e175, ef, ec, par 7 (by omega)]
      exact hw1
    · exact hat' a (mem_l27A.mpr ⟨ha, haS⟩)
  refine ⟨σ, ?_, fun s hs => ?_⟩
  · rw [hpar]
    simp only [List.map_cons, List.map_nil]
    rw [e0, par 1 (by omega), par 2 (by omega), par 3 (by omega), e4, par 5 (by omega),
      par 6 (by omega), par 7 (by omega)]
    rfl
  · have := hatoms s hs
    cases s <;> simp only [Bool.false_eq_true] at this
    rename_i a
    exact ⟨hat a (mem_atomsIn hs), trivial⟩

end
end LeanVM.Guest.B1.Main
