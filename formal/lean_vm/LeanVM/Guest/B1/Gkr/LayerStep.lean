/-
  LeanVM.Guest.B1.Gkr.LayerStep

  An iteration of `verify_bus_gkr`'s layer loop `__loop6` is one step of two levels of the
  specification's GKR walk, between two layer slots.
-/

module

public import LeanVM.Guest.B1.Gkr.LayerTail

/-!
# An iteration of `__loop6`

* `ly_stores`: the next slot's stores and the loop's next call;
* `ly_step`: an iteration at `x = g^j` runs `gkrStep 2` from the slot of `L = 2j + sh` to the slot
  of `L + 2` (`LyB`), and calls the next iteration below the bound.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **The next slot's stores** and the next iteration's call. -/
theorem ly_stores (h : Stmt.HoldsList C rd σ lyPre True kret) :
    (∀ k < 5, LoadHolds rd (σ (.n 16)) (34 + k) (σ (.n (287 + k)))) ∧
      (∀ k < 4, LoadHolds rd (σ (.n 16)) (47 + k) 0) ∧
      LoadHolds rd (σ (.n 16)) 39 (σ (.n 83) * gen ^ 12) ∧
      LoadHolds rd (σ (.n 51)) 40 (σ (.n 278)) ∧ LoadHolds rd (σ (.n 51)) 41 (σ (.n 298)) ∧
      LoadHolds rd (σ (.n 16)) 43 (σ (.n 51) * gen ^ 40) ∧
      LoadHolds rd (σ (.n 16)) 44 (σ (.n 52) * σ (.n 10) * gen) ∧
      (∀ hv pv : E, LoadHolds rd (σ (.n 6) * σ (.n 63)) 4 hv →
        LoadHolds rd (σ (.n 6) * σ (.n 63)) 0 pv →
        LoadHolds rd (σ (.n 16)) 45 (σ (.n 62) * hv) ∧ LoadHolds rd (σ (.n 16)) 46 pv) ∧
      (σ (.n 0) * gen + σ (.n 1) ≠ 0 →
        C "__loop6" [σ (.n 0) * gen, σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)]
          []) := by
  have hnr := lyPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have l274 := a 230 (.load (.n 278) (.n 51) 40) (by decide +kernel)
  have l294 := a 231 (.load (.n 298) (.n 51) 41) (by decide +kernel)
  have hcs := tb_holds_slice hnr h 232 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (287 + k)) (.n 16) (34 + k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs
  have hzs := tb_holds_slice hnr h 237 ((List.range 4).map fun k ↦
    [Stmt.atom (.const (.n (299 + k)) (word 0 0 0)),
      .atom (.load (.n (299 + k)) (.n 16) (47 + k))]).flatten (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hzs
  have c299 := a 245 (.const (.n 303) (word 4096 0 0)) (by decide +kernel)
  have m300 := a 246 (.mul (.n 304) (.n 83) (.n 303)) (by decide +kernel)
  have l300 := a 247 (.load (.n 304) (.n 16) 39) (by decide +kernel)
  have c328 := a 278 (.const (.n 332) (word 1099511627776 0 0)) (by decide +kernel)
  have m329 := a 279 (.mul (.n 333) (.n 51) (.n 332)) (by decide +kernel)
  have l329 := a 280 (.load (.n 333) (.n 16) 43) (by decide +kernel)
  have m330 := a 281 (.mul (.n 334) (.n 52) (.n 10)) (by decide +kernel)
  have c331 := a 282 (.const (.n 335) (word 2 0 0)) (by decide +kernel)
  have m332 := a 283 (.mul (.n 336) (.n 334) (.n 335)) (by decide +kernel)
  have l332 := a 284 (.load (.n 336) (.n 16) 44) (by decide +kernel)
  have m337 := a 285 (.mul (.n 337) (.n 6) (.n 63)) (by decide +kernel)
  have l338 := a 286 (.load (.n 338) (.n 337) 4) (by decide +kernel)
  have m339 := a 287 (.mul (.n 339) (.n 62) (.n 338)) (by decide +kernel)
  have l339 := a 288 (.load (.n 339) (.n 16) 45) (by decide +kernel)
  have m340 := a 289 (.mul (.n 340) (.n 6) (.n 63)) (by decide +kernel)
  have l340 := a 290 (.load (.n 341) (.n 340) 0) (by decide +kernel)
  have l341 := a 291 (.load (.n 341) (.n 16) 46) (by decide +kernel)
  have c340 := a 292 (.const (.n 342) (word 2 0 0)) (by decide +kernel)
  have m341 := a 293 (.mul (.n 343) (.n 0) (.n 342)) (by decide +kernel)
  have a342 := a 294 (.add (.n 344) (.n 343) (.n 1)) (by decide +kernel)
  have c343 := a 295 (.const (.n 345) (word 2 0 0)) (by decide +kernel)
  have m344 := a 296 (.mul (.n 346) (.n 0) (.n 345)) (by decide +kernel)
  obtain ⟨-, hcall⟩ := tb_holds_callIf hnr h 297 (.n 344) "__loop6"
    [.n 346, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] (by decide +kernel)
  simp only [Atom.Holds] at l274 l294 hcs c299 m300 l300 c328 m329 l329 m330 c331 m332 l332
  simp only [Atom.Holds] at m337 l338 m339 l339 m340 l340 l341 c340 m341 a342 c343 m344
  rw [tb_word_gen] at c331 c340 c343
  rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, tb_word_two_pow (by norm_num)] at c299
  rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)] at c328
  refine ⟨hcs, fun k hk => ?_, ?_, l274, l294, ?_, ?_, ?_, ?_⟩
  · have := hzs k hk
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, tb_word_zero] at this
    rw [← this.1]
    exact this.2
  · rw [← c299, ← m300]; exact l300
  · rw [← c328, ← m329]; exact l329
  · rw [← c331, ← m330, ← m332]; exact l332
  · intro hv pv hhv hpv
    rw [m337] at l338
    rw [m340] at l340
    rw [tb_loadHolds_unique l338 hhv] at m339
    rw [m339] at l339
    rw [tb_loadHolds_unique l340 hpv] at l341
    exact ⟨l339, l341⟩
  · intro hne
    simp only [List.map_cons, List.map_nil] at hcall
    rw [m344, c343] at hcall
    exact hcall (by rw [a342, m341, c340]; exact hne)

/-- `half` at the next layer index: `k_mod_next[g^4·g^(j % 4)]` is the carry. -/
theorem ly_half_next (j : ℕ) : gen ^ (j / 4) * gen ^ ((j % 4 + 1) / 4) = gen ^ ((j + 1) / 4) := by
  rw [← pow_add]; congr 1; omega

/-- `parity` at the next layer index: `k_mod_next[g^(j % 4)]`. -/
theorem ly_parity_next (j : ℕ) : gen ^ ((j % 4 + 1) % 4) = gen ^ ((j + 1) % 4) := by
  congr 1; omega

theorem tb_rateOf_nil_getD (k : ℕ) : (rateOf []).getD k 0 = 0 := by
  rw [rateOf_eq_cells [] (by simp)]
  simp only [pendCells, List.flatMap_nil, List.nil_append, List.length_nil,
    List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- **An iteration of `__loop6`**: one step of two levels of the walk between two slots, and the
next iteration below the bound. -/
theorem ly_step (hGR : tb_gkr_rounds_Spec) {N dsb gmu layers rounds kmn : E} (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) "__loop6" (x :: [N, dsb, gmu, layers, rounds, kmn]) []) :
    LyB rd dsb gmu layers kmn x ∧
      (x * gen + N ≠ 0 →
        coreProgram.relN rd d "__loop6" (x * gen :: [N, dsb, gmu, layers, rounds, kmn]) []) := by
  obtain ⟨fn, hf, σ, hpar, hbody⟩ := h
  obtain ⟨fn', hf', hp, hb⟩ := lyFound
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb, lyBody_eq, holdsList_append, holdsList_noRet _ lyPre_noRet] at hbody
  have h := hbody.1
  obtain ⟨s34, s47, s39, s40, s41, s43, s44, s45, hcall⟩ := ly_stores h
  refine ⟨?_, hcall⟩
  intro hkmn j sh hx hsh hj hsh2 s cur st row pos hslot
  have hslot' := hslot
  obtain ⟨-, -, -, -, -, hvl, -, -, hpl, hpt, -, -, -⟩ := hslot'
  obtain ⟨e6, e9, e15, e49, e50, e51, -, e61, e62, hcap0, hcan0, hcur0, hcl0⟩ :=
    ly_head h hx hsh hslot
  have R := ly_rounds (relN_le_rel coreProgram d) hGR h hj hsh2 e6 e9 e61 e62
    (gkrRoundsOut_zero hcap0 hcan0 hcur0 hcl0)
  set L := 2 * j + sh with hL
  obtain ⟨cap, cur', claim, cs, es, hc, -, hcur, hcl, hlen, h4, hrd, helen, hes, hre, hcapT, hcurT,
    hclT⟩ := R
  obtain rfl := tbCapAt_unique hc hcap0
  obtain rfl := tb_loadHolds_unique hcur hcur0
  obtain rfl := tb_loadHolds_unique hcl hcl0
  rw [e50] at hes hre
  obtain rfl := tbReadsAt_unique hes hpt (by rw [helen, hpl])
  -- the last record
  have hnr := lyPre_noRet
  have a := fun n a heq => tb_holds_atom (C := coreProgram.relN rd d) (rd := rd) (σ := σ)
    (kret := fun rs => rs = []) hnr h n a heq
  have m73 := a 65 (.mul (.n 77) (.n 53) (.n 10)) (by decide +kernel)
  have l79 := a 71 (.load (.n 83) (.n 77) 4310) (by decide +kernel)
  have l80 := a 72 (.load (.n 84) (.n 77) 5172) (by decide +kernel)
  have hlc := tb_holds_slice hnr h 66 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (78 + k)) (.n 77) (862 * k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hlc
  simp only [Atom.Holds] at m73 l79 l80 hlc
  rw [m73, e9, tb_loadHolds_mul_gen_pow] at l79 l80
  set run := gkrRun cs st.point (polyEval st.values s.squeeze.1) ⟨s.squeeze.2.cap, []⟩ with hrun
  rw [m73, e9] at hlc
  have hcapEq : ((List.range 5).map fun k ↦ σ (.n (78 + k))) = run.2.2.cap := by
    apply List.ext_getElem (by simp [hcapT.1])
    intro k h1 h2
    have hk : k < 5 := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    have h' := hlc k hk
    rw [tb_loadHolds_mul_gen_pow] at h'
    have h'' := hcapT.2 k h2
    rw [show L + k * gkCap = L + 862 * k by unfold gkCap; ring] at h''
    exact tb_loadHolds_unique h' h''
  have e79 : σ (.n 83) = cur' * gen ^ (4 * L) := tb_loadHolds_unique l79 hcurT
  have e80 : σ (.n 84) = run.2.1 := tb_loadHolds_unique l80 hclT
  obtain ⟨treads, tcheck, tsq1, tsq2, tvals⟩ := ly_tail h
  have hsc := gkr_sumcheck_run cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2
    (hlen.trans helen.symm) h4
  have hsc' : RunsTo (sumcheck (polyEval st.values s.squeeze.1) (2 ^ 2 + 1)
      (st.point.map some)) s.squeeze.2 cs.flatten (run.1, σ (.n 84))
      ⟨(List.range 5).map fun k ↦ σ (.n (78 + k)), []⟩ :=
    hsc.of_eq rfl rfl (by rw [e80]; rfl) (by rw [hcapEq]; exact tb_gkrRun_eta _ _ _ _ rfl)
  have hcheck : σ (.n 84) = polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)]
      s.squeeze.1 := by rw [← e49]; exact tcheck
  have hstep := gkrStep_run (step := 2) hsc' (lyCh_length σ 0) (lyCh_length σ 1) (lyCh_length σ 2)
    hcheck
  have hstep' : RunsTo (gkrStep 2 st) s (cs.flatten ++ (lyCh σ 0 ++ (lyCh σ 1 ++ lyCh σ 2)))
      ⟨[lyCh σ 0, lyCh σ 1, lyCh σ 2].map (fun c ↦ multilinearEval c [σ (.n 278), σ (.n 298)]),
        [σ (.n 278), σ (.n 298)] ++ run.1⟩ ⟨(List.range 5).map fun k ↦ σ (.n (287 + k)), []⟩ := by
    have hh := hstep
    rw [show ((((⟨(List.range 5).map fun k ↦ σ (.n (78 + k)), []⟩ : Fs).absorbAll (lyCh σ 0)
      dsObserve).absorbAll (lyCh σ 1) dsObserve).absorbAll (lyCh σ 2) dsObserve) = lySponge σ
      from rfl, tsq1, tsq2] at hh
    exact hh
  have ld : ∀ k w, LoadHolds rd (σ (.n 16)) k w → LoadHolds rd (σ (.n 4)) (17 * L + k) w :=
    fun k w hw => by rw [e15, tb_loadHolds_mul_gen_pow] at hw; exact hw
  rw [e50] at s40 s41 s43
  refine ⟨_, _, _, σ (.n 52) * σ (.n 10) * gen, hstep', ?_, rfl, ?_⟩
  · rw [tbReadsAt_append, flatten_length_four h4, hlen, ← e79]
    exact ⟨hrd, treads⟩
  refine ⟨by simp, ?_, by simp, ?_, ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [show 17 * (L + 2) + k = 17 * L + (34 + k) by ring]
    have hg : ((List.range 5).map fun k ↦ σ (.n (287 + k))).getD k 0 = σ (.n (287 + k)) := by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [hg]
    exact ld _ _ (s34 k hk)
  · intro c hc _ k hk
    have hck := hc k hk
    rw [show 17 * (L + 2) + 13 + k = 17 * L + (47 + k) by ring] at hck
    rw [tb_rateOf_nil_getD]
    exact tb_loadHolds_unique hck (ld _ _ (s47 k hk))
  · simp only [List.length_append, flatten_length_four h4, hlen, lyCh_length]
    rw [show 17 * (L + 2) + 5 = 17 * L + 39 by ring,
      show cur' * gen ^ (4 * L + (4 + (4 + 4))) = σ (.n 83) * gen ^ 12 by rw [e79]; ring]
    exact ld _ _ s39
  · intro t ht
    have hv : ([lyCh σ 0, lyCh σ 1, lyCh σ 2].map fun c ↦
        multilinearEval c [σ (.n 278), σ (.n 298)]).getD t 0 =
        multilinearEval (lyCh σ t) [σ (.n 278), σ (.n 298)] := by
      interval_cases t <;> rfl
    rw [hv, ← (tvals t ht).1, show 17 * (L + 2) + 6 + t = 17 * L + (40 + t) by ring]
    exact ld _ _ (tvals t ht).2
  · rw [show 17 * (L + 2) + 9 = 17 * L + 43 by ring]
    exact ld _ _ s43
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
    · rw [show row * gen ^ 40 * gen ^ [σ (.n 278), σ (.n 298)].length = row * gen ^ 42 by
        simp only [List.length_cons, List.length_nil]; ring]
      exact hre
  · rw [show 17 * (L + 2) + 10 = 17 * L + 44 by ring]
    exact ld _ _ s44
  · have hk := hkmn (j % 4) (Nat.mod_lt _ (by omega))
    rw [e62] at s45
    simp only [tb_loadHolds_mul_gen_pow] at s45
    have := (s45 _ _ (by rw [show j % 4 + 4 = 4 + j % 4 by ring]; exact hk.1)
      (by simpa using hk.2)).1
    rw [show 17 * (L + 2) + 11 = 17 * L + 45 by ring, ← ly_half_next j, ← e61]
    exact ld _ _ this
  · have hk := hkmn (j % 4) (Nat.mod_lt _ (by omega))
    rw [e62] at s45
    simp only [tb_loadHolds_mul_gen_pow] at s45
    have := (s45 _ _ (by rw [show j % 4 + 4 = 4 + j % 4 by ring]; exact hk.1)
      (by simpa using hk.2)).2
    rw [show 17 * (L + 2) + 12 = 17 * L + 46 by ring]
    exact ld _ _ this

end Sem

end
end LeanVM.Guest.B1.Tables
