/-
  LeanVM.Guest.B1.Gkr.GlLayer

  `gkr_layer__L{p}_L{o}` is one step of two levels of the specification's GKR walk, between two
  layer slots.
-/

module

public import LeanVM.Guest.B1.Gkr.GlLoop
public import LeanVM.Guest.B1.Gkr.GlTail
public import LeanVM.Guest.B1.Gkr.GlHead
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L0_L0»
import LeanVM.Guest.B1.Tables.Basic

/-!
# A radix-four layer, soundly

`gl_layer`: a call of `gkr_layer__L{p}_L{o}` at `x_m = g^m`, `x_j = g^j`, `j = 4m + p`,
`start_g = g^(2 - o)` runs `gkrStep 2` from the slot of `L = 2j + 2 - o`, its point in row `j + 1`,
to the slot of `L + 2`, its point in row `j + 2`: its `L` rounds are the head's `2p`, the loop's
`8m` and the tail's `2 - o` (`glRun_append`), then the tail (`gl_tail`, renamed by `glRho p o`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem glHeadStore_noRet (p : ℕ) : Stmt.noRetList (glHeadStore p) = true := by
  unfold glHeadStore glHeadStore0 glHeadStoreP
  split <;> rw [tb_noRetList_append, tb_noRetList_mapAtoms] <;> rfl

theorem glLoopCall_noRet (p : ℕ) (nm : String) : Stmt.noRetList (glLoopCall p nm) = true := by
  unfold glLoopCall glLoopCall0 glLoopCallP
  split <;> rfl

theorem glTailLoads_noRet (p w : ℕ) : Stmt.noRetList (glTailLoads p w) = true := by
  unfold glTailLoads
  rw [tb_noRetList_append, tb_noRetList_mapAtoms]; rfl

theorem glTailSetup_noRet (p : ℕ) : Stmt.noRetList (glTailSetup p) = true := by
  unfold glTailSetup glTailSetup0 glTailSetupP
  split <;> rw [tb_noRetList_append, glTailLoads_noRet] <;> rfl

theorem glPad_noRet (p o : ℕ) : Stmt.noRetList (glPad p o) = true := by
  unfold glPad
  split <;> rfl

theorem glTailPre_noRet (off : ℕ) :
    Stmt.noRetList (glKids off ++ glCheck ++ glY ++ glNext (off + 12)) = true := by
  rw [tb_noRetList_append, tb_noRetList_append, tb_noRetList_append, glKids_noRet,
    glCheck_noRet, glY_noRet]
  unfold glNext chValT
  rfl

theorem glRho_lo {p o k : ℕ} (h : k < 58) : glRho p o (.n k) = .n k := by
  simp [glRho, h]

theorem glRho_mid {p o k : ℕ} (h1 : 58 ≤ k) (h2 : k < 121) : glRho p o (.n k) = .n (k + glD p) := by
  simp [glRho, h2, show ¬ k < 58 by omega]

theorem glRho_last {p o k : ℕ} (h1 : 121 ≤ k) (h2 : k < 160) :
    glRho p o (.n k) = .n (k + glD p - 39 * o) := by
  simp [glRho, h2, show ¬ k < 58 by omega, show ¬ k < 121 by omega]

section Sem

variable {rd : Reader}

/-- **A radix-four layer** at `x_m = g^m`, `x_j = g^(4m + p)`, the depth's parity `o`. -/
theorem gl_layer {p o : ℕ} (hp : p < 4) (ho : o < 2)
    {layers rounds pts xm xj sg gmu tabs stream : E}
    (hrel : coreProgram.Rel rd (glName p o) [layers, rounds, pts, xm, xj, sg, gmu, tabs, stream] [])
    {m : ℕ} (hxm : xm = gen ^ m) (hxj : xj = gen ^ (4 * m + p)) (hsg : sg = gen ^ (2 - o))
    (hj : 4 * m + p < 2 ^ 30) {s : Fs} {cur : E} {st : GkrState} {pos : E}
    (hslot : GkSlot rd layers (2 * (4 * m + p) + 2 - o) s cur st
      (pts * gen ^ (40 * (4 * m + p + 1))) pos) :
    ∃ (xs : List E) (st' : GkrState) (s' : Fs) (pos' : E),
      RunsTo (gkrStep 2 false st) s xs st' s' ∧ ReadsAt rd cur xs ∧
      GkSlot rd layers (2 * (4 * m + p) + 2 - o + 2) s' (cur * gen ^ xs.length) st'
        (pts * gen ^ (40 * (4 * m + p + 2))) pos' := by
  obtain ⟨n, hn⟩ := hrel
  cases n with
  | zero => exact hn.elim
  | succ n =>
  obtain ⟨fn, hf, σ, hpar, hbody⟩ := hn
  obtain ⟨fn', hf', hps, hb⟩ := glIs_sound (glIs_layers p hp o ho)
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hps] at hpar
  simp only [glParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpar
  have hC : CallRel.Le (coreProgram.relN rd n) (coreProgram.Rel rd) := relN_le_rel coreProgram n
  set j := 4 * m + p with hjdef
  set L := 2 * j + 2 - o with hL
  set D := glD p with hD
  -- the pieces
  rw [hb, glBody] at hbody
  simp only [List.append_assoc] at hbody
  rw [holdsList_append, holdsList_noRet _ glPre_noRet, holdsList_append,
    holdsList_noRet (glHeadRounds p) (glRounds_noRet ..), holdsList_append,
    holdsList_noRet _ (glHeadStore_noRet p), holdsList_append,
    holdsList_noRet _ (glLoopCall_noRet p _), holdsList_append,
    holdsList_noRet _ (glTailSetup_noRet p), holdsList_append,
    holdsList_noRet (glTailRounds p o) (glRounds_noRet ..), holdsList_append,
    holdsList_noRet _ (glPad_noRet p o), Stmt.holdsList_rename, glTail, holdsList_append,
    holdsList_noRet _ (glTailPre_noRet _)] at hbody
  obtain ⟨hPre, hHR, hHS, hLC, hTS, hTR, -, hTail, -⟩ := hbody
  -- the head
  obtain ⟨e15, e21, e40, e35, e44, e53, e54, e58, z23, z24, z25, z26⟩ :=
    gl_pre hPre hxj hsg (by omega) hslot
  have RH := glRounds_sound (rd := rd) (2 * p) hHR rfl
  obtain ⟨hsc, hscur, hscl⟩ := gl_headStore hp hHS
  have R0 := gkrRoundsOut_zero (pt := σ (.n (valf% «gkr_layer» "point_row")) * gen ^ (2 * p)) hsc hscur hscl
  -- the loop
  have RL := gl_loop hp ho (head := σ (.n (valf% «gkr_layer» "head"))) (tabs := σ (.n (valf% «gkr_layer» "tabs"))) hxm (by omega) rfl
    (fun hne => hC _ _ _ (gl_loopCall hp hLC hne)) R0
  obtain ⟨cap1, cap2, cur1, cl1, cl2, hc1, hcur1, hcl1, RLr, hc2, hcur2, hcl2⟩ := glRun_of_out RL
  obtain rfl := capAt_eq hc1 hsc
  obtain rfl := loadHolds_unique hcur1 hscur
  obtain rfl := loadHolds_unique hcl1 hscl
  -- the tail's setup and rounds
  obtain ⟨etp, entp, htc, htcur, htcl⟩ := gl_tailSetup hp hTS
  rw [hxm, ← pow_mul, mul_comm m 7, capAt_mul_gen_pow, Nat.add_zero] at htc
  rw [hxm, ← pow_mul, mul_comm m 7, loadHolds_mul_gen_pow] at htcur htcl
  obtain rfl := capAt_eq htc hc2
  have ecur := loadHolds_unique htcur hcur2
  have ecl := loadHolds_unique htcl hcl2
  have hcu : σ (.n (80 + D)) = σ (.n (valf% «gkr_layer» "s4#0")) * gen ^ (4 * (2 * p + 8 * m)) := by rw [ecur]; ring
  have hpt : σ (.n (71 + D)) = σ (.n (valf% «gkr_layer» "point_row")) * gen ^ (2 * p + 8 * m) := by
    rw [etp, hxm, ← pow_mul]; ring
  have RT := glRounds_sound (rd := rd) (2 - o) hTR (by rw [pow_zero, mul_one, entp])
  rw [hcu, hpt] at RT
  rw [← ecl] at RLr
  have RA := glRun_append RH RLr
  have R := glRun_append RA RT
  rw [show 2 * p + 8 * m + (2 - o) = L by omega, e21, e53, e58, e35] at R
  -- the tail
  set τ := σ ∘ glRho p o with hτ
  have tz : ∀ k, k < 58 → τ (.n k) = σ (.n k) := fun k hk => by
    simp only [hτ, Function.comp_apply, glRho_lo hk]
  have T := gl_tail (τ := τ) (by omega) hTail (by rw [tz 23 (by omega)]; exact z23)
    (by rw [tz 24 (by omega)]; exact z24) (by rw [tz 25 (by omega)]; exact z25)
    (by rw [tz 26 (by omega)]; exact z26)
  obtain ⟨treads, tcheck, tsq1, tsq2, tvals, tcap, tcur, tpt0, tpt1, tpos⟩ := T
  have t77 : τ (.n (val% «gkr_layer__L0_L0» "tcur")) = σ (.n (80 + D)) := by
    show σ (glRho p o (.n (val% «gkr_layer__L0_L0» "tcur"))) = _
    rw [glRho_mid (by omega) (by omega)]
  have tcapT : (glCap (val% «gkr_layer__L0_L0» "nxt[8]@3")).map τ = (glCapAfter (82 + D) (2 - o) (glCap (75 + D))).map σ := by
    simp only [glCapAfter, show 2 - o ≠ 0 by omega, ↓reduceIte, glCap, List.map_map]
    apply List.map_congr_left
    intro k hk
    have hk5 : k < 5 := List.mem_range.mp hk
    simp only [hτ, Function.comp_apply, glRho_last (show 121 ≤ 141 + k by omega)
      (show 141 + k < 160 by omega)]
    congr 2
    omega
  have t158 : τ (.n (val% «gkr_layer__L0_L0» "nclaim@2")) = σ (glClaimAfter (82 + D) (2 - o) (.n (81 + D))) := by
    simp only [glClaimAfter, show 2 - o ≠ 0 by omega, ↓reduceIte, hτ, Function.comp_apply,
      glRho_last (show 121 ≤ 159 by omega) (show 159 < 160 by omega)]
    congr 2
    omega
  rw [← tcapT, ← t158] at R
  -- the specification's step
  obtain ⟨-, -, -, -, hvl, -, hpl, hpt, -⟩ := hslot
  obtain ⟨cs, es, hlen, h4, hrd, helen, hes, hre, hcapR, hclR⟩ := R
  obtain rfl := tbReadsAt_unique hes hpt (by rw [helen, hpl])
  set run := gkrRun cs st.point (polyEval st.values s.squeeze.1) ⟨s.squeeze.2.cap, []⟩ with hrun
  have hsc := gkr_sumcheck_run cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2
    (hlen.trans helen.symm) h4
  have hsc' : RunsTo (sumcheck (polyEval st.values s.squeeze.1) (2 ^ 2 + 1)
      (st.point.map some)) s.squeeze.2 cs.flatten (run.1, τ (.n (val% «gkr_layer__L0_L0» "nclaim@2")))
      ⟨(glCap (val% «gkr_layer__L0_L0» "nxt[8]@3")).map τ, []⟩ :=
    hsc.of_eq rfl rfl (by rw [hclR]; rfl) (by rw [hcapR]; exact tb_gkrRun_eta _ _ _ _ rfl)
  have t40 : τ (.n (valf% «gkr_layer» "nxt[0]@1")) = s.squeeze.1 := by rw [tz 27 (by omega)]; exact e40
  have hcheck : τ (.n (val% «gkr_layer__L0_L0» "nclaim@2")) = polyEval [prodE (glCh τ 0), prodE (glCh τ 1), prodE (glCh τ 2)]
      s.squeeze.1 := by rw [← t40]; exact tcheck
  have hstep := gkrStep_run (step := 2) le_rfl false hsc' (chWords_length τ (val% «gkr_layer__L0_L0» "x@9") 0)
    (chWords_length τ (val% «gkr_layer__L0_L0» "x@9") 1) (chWords_length τ (val% «gkr_layer__L0_L0» "x@9") 2) hcheck
  have hstep' : RunsTo (gkrStep 2 false st) s
      (cs.flatten ++ (glCh τ 0 ++ (glCh τ 1 ++ glCh τ 2)))
      ⟨[glCh τ 0, glCh τ 1, glCh τ 2].map
          (fun c ↦ multilinearEval c [τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")), τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7"))]),
        [τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")), τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7"))] ++ run.1⟩ ⟨(glCap (val% «gkr_layer__L0_L0» "nxt[8]@7")).map τ, []⟩ := by
    have hh := hstep
    rw [show ((((⟨(glCap (val% «gkr_layer__L0_L0» "nxt[8]@3")).map τ, []⟩ : Fs).absorbAll (glCh τ 0)
      dsObserve).absorbAll (glCh τ 1) dsObserve).absorbAll (glCh τ 2) dsObserve) = glSponge τ
      from rfl, tsq1, tsq2] at hh
    exact hh
  have t15 : τ (.n (valf% «gkr_layer» "layer")) = σ (.n (valf% «gkr_layer» "layers")) * gen ^ (10 * L) := by rw [tz 15 (by omega)]; exact e15
  have t53 : τ (.n (valf% «gkr_layer» "point_row")) = σ (.n (valf% «gkr_layer» "gkr_pts")) * gen ^ (40 * (j + 1)) := by rw [tz 52 (by omega)]; exact e53
  have ld : ∀ k w, LoadHolds rd (τ (.n (valf% «gkr_layer» "layer"))) k w → LoadHolds rd (σ (.n (valf% «gkr_layer» "layers"))) (10 * L + k) w :=
    fun k w hw => by rw [t15, loadHolds_mul_gen_pow] at hw; exact hw
  have hcurT : τ (.n (val% «gkr_layer__L0_L0» "tcur")) = σ (.n (valf% «gkr_layer» "s4#0")) * gen ^ (4 * (2 * p + 8 * m)) := by rw [t77, hcu]
  refine ⟨_, _, _, τ (.n (valf% «gkr_layer» "round_pos")) * (τ (.n (valf% «gkr_layer» "x_m")) * gen) ^ 7, hstep', ?_, ?_⟩
  · rw [tbReadsAt_append, flatten_length_four h4, hlen]
    refine ⟨hrd, ?_⟩
    rw [hcurT, mul_assoc, ← pow_add, e21] at treads
    convert treads using 3
    omega
  refine ⟨by simp [glCap], ?_, rfl, ?_, by simp, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [show 10 * (L + 2) + k = 10 * L + (20 + k) by ring]
    have hg : ((glCap (val% «gkr_layer__L0_L0» "nxt[8]@7")).map τ).getD k 0 = τ (.n ((val% «gkr_layer__L0_L0» "nxt[8]@7") + k)) := by
      simp [glCap, List.getD_eq_getElem?_getD, hk]
    rw [hg]
    exact ld _ _ (tcap k hk)
  · simp only [List.length_append, flatten_length_four h4, hlen, chWords_length]
    rw [show 10 * (L + 2) + 5 = 10 * L + 25 by ring]
    have := ld _ _ tcur
    rw [hcurT, mul_assoc, ← pow_add, e21] at this
    convert this using 3
    omega
  · intro t ht
    have hv : ([glCh τ 0, glCh τ 1, glCh τ 2].map fun c ↦
        multilinearEval c [τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")), τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7"))]).getD t 0 =
        multilinearEval (glCh τ t) [τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")), τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7"))] := by
      interval_cases t <;> rfl
    rw [hv, show 10 * (L + 2) + 6 + t = 10 * L + (26 + t) by ring]
    exact ld _ _ (tvals t ht)
  · simp only [List.length_append, List.length_cons, List.length_nil]
    rw [hrun, tb_gkrRun_length _ _ _ _ (hlen.trans helen.symm), hlen]
    omega
  · rw [tbReadsAt_append]
    refine ⟨fun k hk => ?_, ?_⟩
    · simp only [List.length_cons, List.length_nil] at hk
      rw [show 40 * (j + 2) = 40 * (j + 1) + 40 by ring, pow_add, ← mul_assoc,
        loadHolds_mul_gen_pow, ← t53]
      interval_cases k
      · exact tpt0
      · exact tpt1
    · rw [show σ (.n (valf% «gkr_layer» "gkr_pts")) * gen ^ (40 * (j + 2)) * gen ^ [τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@6")), τ (.n (val% «gkr_layer__L0_L0» "nxt[0]@7"))].length =
        σ (.n (valf% «gkr_layer» "gkr_pts")) * gen ^ (40 * (j + 1)) * gen ^ 42 by
          simp only [List.length_cons, List.length_nil]; rw [mul_assoc, mul_assoc, ← pow_add,
            ← pow_add]; ring_nf]
      exact hre
  · rw [show 10 * (L + 2) + 9 = 10 * L + 29 by ring]
    exact ld _ _ tpos

end Sem

end
end LeanVM.Guest.B1.Tables
