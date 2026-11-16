/-
  LeanVM.Guest.B1.Gkr.LayerStep

  An iteration of `verify_bus_gkr`'s layer loop `verify_bus_gkr_loop0` is one step of two levels of
  the specification's GKR walk, between two layer slots.
-/

module

public import LeanVM.Guest.B1.Gkr.LayerTail
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreData

/-!
# An iteration of `verify_bus_gkr_loop0`

* `ly_stores`: the next slot's stores, the next row's first cells and the loop's next call;
* `ly_step`: an iteration at `x = g^j` runs `gkrStep 2` from the slot of `L = 2j + 2 - sh` to the
  slot of `L + 2` (`LyB`), and calls the next iteration below the bound.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **The next slot's stores**, the next row's first two cells, and the next iteration's call. -/
theorem ly_stores (h : Stmt.HoldsList C rd σ lyPre True kret) :
    (∀ k < 5, LoadHolds rd (σ (.n 17)) (20 + k) (σ (.n (194 + k)))) ∧
      LoadHolds rd (σ (.n 17)) 25 (σ (.n 80) * gen ^ 12) ∧
      LoadHolds rd (σ (.n 55)) 40 (σ (.n 185)) ∧ LoadHolds rd (σ (.n 55)) 41 (σ (.n 199)) ∧
      LoadHolds rd (σ (.n 17)) 29 (σ (.n 46) * σ (.n 0) * gen ^ 2) ∧
      (σ (.n 0) * gen + σ (.n 1) ≠ 0 →
        C name% «verify_bus_gkr_loop0» [σ (.n 0) * gen, σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4),
          σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9), σ (.n 10)] []) := by
  have hnr := lyPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have l185 := a 135 (.load (.n 185) (.n 55) 40) (by decide +kernel)
  have l199 := a 136 (.load (.n 199) (.n 55) 41) (by decide +kernel)
  have hcs := tb_holds_slice hnr h 137 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (194 + k)) (.n 17) (20 + k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs
  have c200 := a 142 (.const (.n 200) (word 4096 0)) (by decide +kernel)
  have m201 := a 143 (.mul (.n 201) (.n 80) (.n 200)) (by decide +kernel)
  have l201 := a 144 (.load (.n 201) (.n 17) 25) (by decide +kernel)
  have m229 := a 175 (.mul (.n 229) (.n 46) (.n 0)) (by decide +kernel)
  have c230 := a 176 (.const (.n 230) (word 4 0)) (by decide +kernel)
  have m231 := a 177 (.mul (.n 231) (.n 229) (.n 230)) (by decide +kernel)
  have l231 := a 178 (.load (.n 231) (.n 17) 29) (by decide +kernel)
  have c232 := a 179 (.const (.n 232) (word 2 0)) (by decide +kernel)
  have m233 := a 180 (.mul (.n 233) (.n 0) (.n 232)) (by decide +kernel)
  have a234 := a 181 (.add (.n 234) (.n 233) (.n 1)) (by decide +kernel)
  have c235 := a 182 (.const (.n 235) (word 2 0)) (by decide +kernel)
  have m236 := a 183 (.mul (.n 236) (.n 0) (.n 235)) (by decide +kernel)
  obtain ⟨-, hcall⟩ := tb_holds_callIf hnr h 184 (.n 234) name% «verify_bus_gkr_loop0»
    [.n 236, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10] (by decide +kernel)
  simp only [Atom.Holds] at l185 l199 hcs c200 m201 l201 m229 c230 m231 l231
  simp only [Atom.Holds] at c232 m233 a234 c235 m236
  rw [tb_word_gen] at c232 c235
  rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, tb_word_two_pow (by norm_num)] at c200
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)] at c230
  refine ⟨hcs, ?_, l185, l199, ?_, ?_⟩
  · rw [← c200, ← m201]; exact l201
  · rw [← c230, ← m229, ← m231]; exact l231
  · intro hne
    simp only [List.map_cons, List.map_nil] at hcall
    rw [m236, c235] at hcall
    exact hcall (by rw [a234, m233, c232]; exact hne)

/-- **An iteration of `verify_bus_gkr_loop0`**: one step of two levels of the walk between two
slots, and the next iteration below the bound. -/
theorem ly_step (hGR : tb_gkr_rounds_Spec) {N sg layers tabs pts rounds u og stream gmu : E}
    (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) name% «verify_bus_gkr_loop0»
      (x :: [N, sg, layers, tabs, pts, rounds, u, og, stream, gmu]) []) :
    LyB rd sg og layers pts x ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d name% «verify_bus_gkr_loop0»
        (x * gen :: [N, sg, layers, tabs, pts, rounds, u, og, stream, gmu]) []) := by
  obtain ⟨fn, hf, σ, hpar, hbody⟩ := h
  obtain ⟨fn', hf', hp, hb⟩ := lyFound
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hp] at hpar
  simp only [lyParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb, lyBody_eq, holdsList_append, holdsList_noRet _ lyPre_noRet] at hbody
  have h := hbody.1
  obtain ⟨s20, s25, s40, s41, s29, hcall⟩ := ly_stores h
  refine ⟨?_, hcall⟩
  intro j sh hx hsg hog hj hsh2 s cur st pos hslot
  have hslot' := hslot
  obtain ⟨-, -, -, -, hvl, -, hpl, hpt, -⟩ := hslot'
  obtain ⟨e11, e12, e17, e42, e55, e46, -, hcap0, hcur0, hcl0⟩ := ly_head h hx hsg hsh2 hslot
  have R := ly_rounds (relN_le_rel coreProgram d) hGR h hj hsh2 hx e11 hog
    (gkrRoundsOut_zero hcap0 hcur0 hcl0)
  set L := 2 * j + 2 - sh with hL
  obtain ⟨cap, cur', claim', cs, es, hc, hcur, hcl, hlen, h4, hrd, helen, hes, hre, hcapT, hcurT,
    hclT⟩ := R
  obtain rfl := tbCapAt_unique hc hcap0
  obtain rfl := tb_loadHolds_unique hcur hcur0
  obtain rfl := tb_loadHolds_unique hcl hcl0
  rw [e55] at hes hre
  obtain rfl := tbReadsAt_unique hes hpt (by rw [helen, hpl])
  -- the last record
  have hnr := lyPre_noRet
  have a := fun n a heq => tb_holds_atom (C := coreProgram.relN rd d) (rd := rd) (σ := σ)
    (kret := fun rs => rs = []) hnr h n a heq
  have m72 := a 54 (.mul (.n 72) (.n 56) (.n 0)) (by decide +kernel)
  have c73 := a 55 (.const (.n 73) (word 2 0)) (by decide +kernel)
  have m74 := a 56 (.mul (.n 74) (.n 72) (.n 73)) (by decide +kernel)
  have l80 := a 62 (.load (.n 80) (.n 74) 4310) (by decide +kernel)
  have l155 := a 113 (.load (.n 155) (.n 74) 5172) (by decide +kernel)
  have hlc := tb_holds_slice hnr h 57 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (75 + k)) (.n 74) (862 * k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hlc
  simp only [Atom.Holds] at m72 c73 m74 l80 l155 hlc
  rw [tb_word_gen] at c73
  have e74 : σ (.n 74) = σ (.n 56) * gen ^ (j + 1) := by rw [m74, m72, c73, hx, pow_succ]; ring
  rw [e74, tb_loadHolds_mul_gen_pow] at l80 l155
  set run := gkrRun cs st.point (polyEval st.values s.squeeze.1) ⟨s.squeeze.2.cap, []⟩ with hrun
  rw [e74] at hlc
  have hcapEq : ((List.range 5).map fun k ↦ σ (.n (75 + k))) = run.2.2.cap := by
    apply List.ext_getElem (by simp [hcapT.1])
    intro k h1 h2
    have hk5 : k < 5 := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    have h' := hlc k hk5
    rw [tb_loadHolds_mul_gen_pow] at h'
    have h'' := hcapT.2 k h2
    rw [show j + 1 + k * gkCap = j + 1 + 862 * k by unfold gkCap; ring] at h''
    exact tb_loadHolds_unique h' h''
  have e80 : σ (.n 80) = cur' * gen ^ (4 * L) := tb_loadHolds_unique l80 hcurT
  have e155 : σ (.n 155) = run.2.1 := tb_loadHolds_unique l155 hclT
  obtain ⟨treads, tcheck, tsq1, tsq2, tvals⟩ := ly_tail h
  have hsc := gkr_sumcheck_run cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2
    (hlen.trans helen.symm) h4
  have hsc' : RunsTo (sumcheck (polyEval st.values s.squeeze.1) (2 ^ 2 + 1)
      (st.point.map some)) s.squeeze.2 cs.flatten (run.1, σ (.n 155))
      ⟨(List.range 5).map fun k ↦ σ (.n (75 + k)), []⟩ :=
    hsc.of_eq rfl rfl (by rw [e155]; rfl) (by rw [hcapEq]; exact tb_gkrRun_eta _ _ _ _ rfl)
  have hcheck : σ (.n 155) = polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)]
      s.squeeze.1 := by rw [← e42]; exact tcheck
  have hstep := gkrStep_run (step := 2) le_rfl false hsc' (lyCh_length σ 0) (lyCh_length σ 1)
    (lyCh_length σ 2) hcheck
  have hstep' : RunsTo (gkrStep 2 false st) s (cs.flatten ++ (lyCh σ 0 ++ (lyCh σ 1 ++ lyCh σ 2)))
      ⟨[lyCh σ 0, lyCh σ 1, lyCh σ 2].map (fun c ↦ multilinearEval c [σ (.n 185), σ (.n 199)]),
        [σ (.n 185), σ (.n 199)] ++ run.1⟩ ⟨(List.range 5).map fun k ↦ σ (.n (194 + k)), []⟩ := by
    have hh := hstep
    rw [show ((((⟨(List.range 5).map fun k ↦ σ (.n (75 + k)), []⟩ : Fs).absorbAll (lyCh σ 0)
      dsObserve).absorbAll (lyCh σ 1) dsObserve).absorbAll (lyCh σ 2) dsObserve) = lySponge σ
      from rfl, tsq1, tsq2] at hh
    exact hh
  have ld : ∀ k w, LoadHolds rd (σ (.n 17)) k w → LoadHolds rd (σ (.n 3)) (10 * L + k) w :=
    fun k w hw => by rw [e17, tb_loadHolds_mul_gen_pow] at hw; exact hw
  rw [e55] at s40 s41
  refine ⟨_, _, _, σ (.n 46) * σ (.n 0) * gen ^ 2, hstep', ?_, ?_⟩
  · rw [tbReadsAt_append, flatten_length_four h4, hlen, ← e80]
    exact ⟨hrd, treads⟩
  refine ⟨by simp, ?_, rfl, ?_, by simp, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [show 10 * (L + 2) + k = 10 * L + (20 + k) by ring]
    have hg : ((List.range 5).map fun k ↦ σ (.n (194 + k))).getD k 0 = σ (.n (194 + k)) := by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [hg]
    exact ld _ _ (s20 k hk)
  · simp only [List.length_append, flatten_length_four h4, hlen, lyCh_length]
    rw [show 10 * (L + 2) + 5 = 10 * L + 25 by ring,
      show cur' * gen ^ (4 * L + (4 + (4 + 4))) = σ (.n 80) * gen ^ 12 by rw [e80]; ring]
    exact ld _ _ s25
  · intro t ht
    have hv : ([lyCh σ 0, lyCh σ 1, lyCh σ 2].map fun c ↦
        multilinearEval c [σ (.n 185), σ (.n 199)]).getD t 0 =
        multilinearEval (lyCh σ t) [σ (.n 185), σ (.n 199)] := by
      interval_cases t <;> rfl
    rw [hv, ← (tvals t ht).1, show 10 * (L + 2) + 6 + t = 10 * L + (26 + t) by ring]
    exact ld _ _ (tvals t ht).2
  · simp only [List.length_append, List.length_cons, List.length_nil]
    rw [hrun, tb_gkrRun_length _ _ _ _ (hlen.trans helen.symm), hlen]
    omega
  · rw [tbReadsAt_append]
    refine ⟨fun k hk => ?_, ?_⟩
    · simp only [List.length_cons, List.length_nil] at hk
      rw [show 40 * (j + 2) = 40 * (j + 1) + 40 by ring, pow_add, ← mul_assoc,
        tb_loadHolds_mul_gen_pow]
      interval_cases k
      · exact s40
      · exact s41
    · rw [show σ (.n 5) * gen ^ (40 * (j + 2)) * gen ^ [σ (.n 185), σ (.n 199)].length =
        σ (.n 5) * gen ^ (40 * (j + 1)) * gen ^ 42 by
          simp only [List.length_cons, List.length_nil]; rw [mul_assoc, mul_assoc, ← pow_add,
            ← pow_add]; ring_nf]
      exact hre
  · rw [show 10 * (L + 2) + 9 = 10 * L + 29 by ring]
    exact ld _ _ s29

end Sem

end
end LeanVM.Guest.B1.Tables
