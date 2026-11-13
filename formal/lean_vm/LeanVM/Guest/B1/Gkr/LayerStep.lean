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

* `ly_stores`: the next slot's stores and the loop's next call;
* `ly_step`: an iteration at `x = g^j` runs `gkrStep 2` from the slot of `L = 2j + 2 - sh` to the
  slot of `L + 2` (`LyB`), and calls the next iteration below the bound.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **The next slot's stores** and the next iteration's call. -/
theorem ly_stores (h : Stmt.HoldsList C rd σ lyPre True kret) :
    (∀ k < 5, LoadHolds rd (σ (.n 17)) (26 + k) (σ (.n (189 + k)))) ∧
      LoadHolds rd (σ (.n 17)) 31 (σ (.n 75) * gen ^ 12) ∧
      LoadHolds rd (σ (.n 46)) 40 (σ (.n 180)) ∧ LoadHolds rd (σ (.n 46)) 41 (σ (.n 194)) ∧
      LoadHolds rd (σ (.n 17)) 35 (σ (.n 46) * gen ^ 40) ∧
      LoadHolds rd (σ (.n 17)) 36 (σ (.n 47) * σ (.n 11) * gen) ∧
      (∀ hv pv : E, LoadHolds rd (σ (.n 9) * σ (.n 54)) 4 hv →
        LoadHolds rd (σ (.n 9) * σ (.n 54)) 0 pv →
        LoadHolds rd (σ (.n 17)) 37 (σ (.n 53) * hv) ∧ LoadHolds rd (σ (.n 17)) 38 pv) ∧
      (σ (.n 0) * gen + σ (.n 1) ≠ 0 →
        C name% «verify_bus_gkr_loop0» [σ (.n 0) * gen, σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4),
            σ (.n 5), σ (.n 6),
          σ (.n 7), σ (.n 8), σ (.n 9)] []) := by
  have hnr := lyPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have l180 := a 132 (.load (.n 180) (.n 46) 40) (by decide +kernel)
  have l194 := a 133 (.load (.n 194) (.n 46) 41) (by decide +kernel)
  have hcs := tb_holds_slice hnr h 134 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (189 + k)) (.n 17) (26 + k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs
  have c195 := a 139 (.const (.n 195) (word 4096 0)) (by decide +kernel)
  have m196 := a 140 (.mul (.n 196) (.n 75) (.n 195)) (by decide +kernel)
  have l196 := a 141 (.load (.n 196) (.n 17) 31) (by decide +kernel)
  have c224 := a 172 (.const (.n 224) (word 1099511627776 0)) (by decide +kernel)
  have m225 := a 173 (.mul (.n 225) (.n 46) (.n 224)) (by decide +kernel)
  have l225 := a 174 (.load (.n 225) (.n 17) 35) (by decide +kernel)
  have m226 := a 175 (.mul (.n 226) (.n 47) (.n 11)) (by decide +kernel)
  have c227 := a 176 (.const (.n 227) (word 2 0)) (by decide +kernel)
  have m228 := a 177 (.mul (.n 228) (.n 226) (.n 227)) (by decide +kernel)
  have l228 := a 178 (.load (.n 228) (.n 17) 36) (by decide +kernel)
  have m229 := a 179 (.mul (.n 229) (.n 9) (.n 54)) (by decide +kernel)
  have l230 := a 180 (.load (.n 230) (.n 229) 4) (by decide +kernel)
  have m231 := a 181 (.mul (.n 231) (.n 53) (.n 230)) (by decide +kernel)
  have l231 := a 182 (.load (.n 231) (.n 17) 37) (by decide +kernel)
  have m232 := a 183 (.mul (.n 232) (.n 9) (.n 54)) (by decide +kernel)
  have l233 := a 184 (.load (.n 233) (.n 232) 0) (by decide +kernel)
  have l233' := a 185 (.load (.n 233) (.n 17) 38) (by decide +kernel)
  have c234 := a 186 (.const (.n 234) (word 2 0)) (by decide +kernel)
  have m235 := a 187 (.mul (.n 235) (.n 0) (.n 234)) (by decide +kernel)
  have a236 := a 188 (.add (.n 236) (.n 235) (.n 1)) (by decide +kernel)
  have c237 := a 189 (.const (.n 237) (word 2 0)) (by decide +kernel)
  have m238 := a 190 (.mul (.n 238) (.n 0) (.n 237)) (by decide +kernel)
  obtain ⟨-, hcall⟩ := tb_holds_callIf hnr h 191 (.n 236) name% «verify_bus_gkr_loop0»
    [.n 238, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] (by decide +kernel)
  simp only [Atom.Holds] at l180 l194 hcs c195 m196 l196 c224 m225 l225 m226 c227 m228 l228
  simp only [Atom.Holds] at m229 l230 m231 l231 m232 l233 l233' c234 m235 a236 c237 m238
  rw [tb_word_gen] at c227 c234 c237
  rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, tb_word_two_pow (by norm_num)] at c195
  rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)] at c224
  refine ⟨hcs, ?_, l180, l194, ?_, ?_, ?_, ?_⟩
  · rw [← c195, ← m196]; exact l196
  · rw [← c224, ← m225]; exact l225
  · rw [← c227, ← m226, ← m228]; exact l228
  · intro hv pv hhv hpv
    rw [m229] at l230
    rw [m232] at l233
    rw [tb_loadHolds_unique l230 hhv] at m231
    rw [m231] at l231
    rw [tb_loadHolds_unique l233 hpv] at l233'
    exact ⟨l231, l233'⟩
  · intro hne
    simp only [List.map_cons, List.map_nil] at hcall
    rw [m238, c237] at hcall
    exact hcall (by rw [a236, m235, c234]; exact hne)

/-- `half` at the next layer index: `k_mod_next[g^4·g^(k % 4)]` is the carry. -/
theorem ly_half_next (k : ℕ) : gen ^ (k / 4) * gen ^ ((k % 4 + 1) / 4) = gen ^ ((k + 1) / 4) := by
  rw [← pow_add]; congr 1; omega

/-- `parity` at the next layer index: `k_mod_next[g^(k % 4)]`. -/
theorem ly_parity_next (k : ℕ) : gen ^ ((k % 4 + 1) % 4) = gen ^ ((k + 1) % 4) := by
  congr 1; omega

/-- **An iteration of `verify_bus_gkr_loop0`**: one step of two levels of the walk between two
slots, and the
next iteration below the bound. -/
theorem ly_step (hGR : tb_gkr_rounds_Spec) {N sg layers tabs rounds claim og gmu kmn : E} (d : ℕ)
    (x : E)
    (h : coreProgram.relN rd (d + 1) name% «verify_bus_gkr_loop0»
      (x :: [N, sg, layers, tabs, rounds, claim, og, gmu, kmn]) []) :
    LyB rd sg og layers kmn x ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d name% «verify_bus_gkr_loop0»
        (x * gen :: [N, sg, layers, tabs, rounds, claim, og, gmu, kmn]) []) := by
  obtain ⟨fn, hf, σ, hpar, hbody⟩ := h
  obtain ⟨fn', hf', hp, hb⟩ := lyFound
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hp] at hpar
  simp only [lyParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb, lyBody_eq, holdsList_append, holdsList_noRet _ lyPre_noRet] at hbody
  have h := hbody.1
  obtain ⟨s26, s31, s40, s41, s35, s36, s37, hcall⟩ := ly_stores h
  refine ⟨?_, hcall⟩
  intro hkmn j sh hx hsg hog hj hsh2 s cur st row pos hslot
  have hslot' := hslot
  obtain ⟨-, -, -, -, hvl, -, -, hpl, hpt, -, -, -⟩ := hslot'
  set k := j + 1 - sh with hk
  obtain ⟨e10, e11, e17, e42, e46, e47, -, e53, e54, hcap0, hcur0, hcl0⟩ :=
    ly_head h hx hsg hsh2 hslot
  have R := ly_rounds (relN_le_rel coreProgram d) hGR h hj hsh2 hk e10 hog e53 e54
    (gkrRoundsOut_zero hcap0 hcur0 hcl0)
  set L := 2 * j + 2 - sh with hL
  have hLk : 2 * k + sh = L := by omega
  rw [hLk] at R
  obtain ⟨cap, cur', claim', cs, es, hc, hcur, hcl, hlen, h4, hrd, helen, hes, hre, hcapT, hcurT,
    hclT⟩ := R
  obtain rfl := tbCapAt_unique hc hcap0
  obtain rfl := tb_loadHolds_unique hcur hcur0
  obtain rfl := tb_loadHolds_unique hcl hcl0
  rw [e46] at hes hre
  obtain rfl := tbReadsAt_unique hes hpt (by rw [helen, hpl])
  -- the last record
  have hnr := lyPre_noRet
  have a := fun n a heq => tb_holds_atom (C := coreProgram.relN rd d) (rd := rd) (σ := σ)
    (kret := fun rs => rs = []) hnr h n a heq
  have m69 := a 53 (.mul (.n 69) (.n 48) (.n 11)) (by decide +kernel)
  have l75 := a 59 (.load (.n 75) (.n 69) 4310) (by decide +kernel)
  have l150 := a 110 (.load (.n 150) (.n 69) 5172) (by decide +kernel)
  have hlc := tb_holds_slice hnr h 54 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (70 + k)) (.n 69) (862 * k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hlc
  simp only [Atom.Holds] at m69 l75 l150 hlc
  rw [m69, e11, tb_loadHolds_mul_gen_pow] at l75 l150
  set run := gkrRun cs st.point (polyEval st.values s.squeeze.1) ⟨s.squeeze.2.cap, []⟩ with hrun
  rw [m69, e11] at hlc
  have hcapEq : ((List.range 5).map fun k ↦ σ (.n (70 + k))) = run.2.2.cap := by
    apply List.ext_getElem (by simp [hcapT.1])
    intro k h1 h2
    have hk5 : k < 5 := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    have h' := hlc k hk5
    rw [tb_loadHolds_mul_gen_pow] at h'
    have h'' := hcapT.2 k h2
    rw [show L + k * gkCap = L + 862 * k by unfold gkCap; ring] at h''
    exact tb_loadHolds_unique h' h''
  have e75 : σ (.n 75) = cur' * gen ^ (4 * L) := tb_loadHolds_unique l75 hcurT
  have e150 : σ (.n 150) = run.2.1 := tb_loadHolds_unique l150 hclT
  obtain ⟨treads, tcheck, tsq1, tsq2, tvals⟩ := ly_tail h
  have hsc := gkr_sumcheck_run cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2
    (hlen.trans helen.symm) h4
  have hsc' : RunsTo (sumcheck (polyEval st.values s.squeeze.1) (2 ^ 2 + 1)
      (st.point.map some)) s.squeeze.2 cs.flatten (run.1, σ (.n 150))
      ⟨(List.range 5).map fun k ↦ σ (.n (70 + k)), []⟩ :=
    hsc.of_eq rfl rfl (by rw [e150]; rfl) (by rw [hcapEq]; exact tb_gkrRun_eta _ _ _ _ rfl)
  have hcheck : σ (.n 150) = polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)]
      s.squeeze.1 := by rw [← e42]; exact tcheck
  have hstep := gkrStep_run (step := 2) le_rfl false hsc' (lyCh_length σ 0) (lyCh_length σ 1)
    (lyCh_length σ 2) hcheck
  have hstep' : RunsTo (gkrStep 2 false st) s (cs.flatten ++ (lyCh σ 0 ++ (lyCh σ 1 ++ lyCh σ 2)))
      ⟨[lyCh σ 0, lyCh σ 1, lyCh σ 2].map (fun c ↦ multilinearEval c [σ (.n 180), σ (.n 194)]),
        [σ (.n 180), σ (.n 194)] ++ run.1⟩ ⟨(List.range 5).map fun k ↦ σ (.n (189 + k)), []⟩ := by
    have hh := hstep
    rw [show ((((⟨(List.range 5).map fun k ↦ σ (.n (70 + k)), []⟩ : Fs).absorbAll (lyCh σ 0)
      dsObserve).absorbAll (lyCh σ 1) dsObserve).absorbAll (lyCh σ 2) dsObserve) = lySponge σ
      from rfl, tsq1, tsq2] at hh
    exact hh
  have ld : ∀ k w, LoadHolds rd (σ (.n 17)) k w → LoadHolds rd (σ (.n 3)) (13 * L + k) w :=
    fun k w hw => by rw [e17, tb_loadHolds_mul_gen_pow] at hw; exact hw
  rw [e46] at s40 s41 s35
  refine ⟨_, _, _, σ (.n 47) * σ (.n 11) * gen, hstep', ?_, ?_⟩
  · rw [tbReadsAt_append, flatten_length_four h4, hlen, ← e75]
    exact ⟨hrd, treads⟩
  refine ⟨by simp, ?_, rfl, ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [show 13 * (L + 2) + k = 13 * L + (26 + k) by ring]
    have hg : ((List.range 5).map fun k ↦ σ (.n (189 + k))).getD k 0 = σ (.n (189 + k)) := by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [hg]
    exact ld _ _ (s26 k hk)
  · simp only [List.length_append, flatten_length_four h4, hlen, lyCh_length]
    rw [show 13 * (L + 2) + 5 = 13 * L + 31 by ring,
      show cur' * gen ^ (4 * L + (4 + (4 + 4))) = σ (.n 75) * gen ^ 12 by rw [e75]; ring]
    exact ld _ _ s31
  · intro t ht
    have hv : ([lyCh σ 0, lyCh σ 1, lyCh σ 2].map fun c ↦
        multilinearEval c [σ (.n 180), σ (.n 194)]).getD t 0 =
        multilinearEval (lyCh σ t) [σ (.n 180), σ (.n 194)] := by
      interval_cases t <;> rfl
    rw [hv, ← (tvals t ht).1, show 13 * (L + 2) + 6 + t = 13 * L + (32 + t) by ring]
    exact ld _ _ (tvals t ht).2
  · rw [show 13 * (L + 2) + 9 = 13 * L + 35 by ring]
    exact ld _ _ s35
  · simp only [List.length_append, List.length_cons, List.length_nil]
    rw [hrun, tb_gkrRun_length _ _ _ _ (hlen.trans helen.symm), hlen]
    omega
  · rw [tbReadsAt_append]
    refine ⟨fun k hk => ?_, ?_⟩
    · simp only [List.length_cons, List.length_nil] at hk
      rw [tb_loadHolds_mul_gen_pow]
      interval_cases k
      · exact s40
      · exact s41
    · rw [show row * gen ^ 40 * gen ^ [σ (.n 180), σ (.n 194)].length = row * gen ^ 42 by
        simp only [List.length_cons, List.length_nil]; ring]
      exact hre
  · rw [show 13 * (L + 2) + 10 = 13 * L + 36 by ring]
    exact ld _ _ s36
  · have hkm := hkmn (k % 4) (Nat.mod_lt _ (by omega))
    rw [e54] at s37
    simp only [tb_loadHolds_mul_gen_pow] at s37
    have := (s37 _ _ (by rw [show k % 4 + 4 = 4 + k % 4 by ring]; exact hkm.1)
      (by simpa using hkm.2)).1
    rw [show 13 * (L + 2) + 11 = 13 * L + 37 by ring,
      show (j + 2 - sh) / 4 = (k + 1) / 4 by omega, ← ly_half_next k, ← e53]
    exact ld _ _ this
  · have hkm := hkmn (k % 4) (Nat.mod_lt _ (by omega))
    rw [e54] at s37
    simp only [tb_loadHolds_mul_gen_pow] at s37
    have := (s37 _ _ (by rw [show k % 4 + 4 = 4 + k % 4 by ring]; exact hkm.1)
      (by simpa using hkm.2)).2
    rw [show 13 * (L + 2) + 12 = 13 * L + 38 by ring, show (j + 2 - sh) % 4 = (k + 1) % 4 by omega]
    exact ld _ _ this

end Sem

end
end LeanVM.Guest.B1.Tables
