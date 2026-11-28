/-
  LeanVM.Guest.B1.VsC.Os.LeftBody

  `open_stacked`'s body on a memory: its valuation, its walk, its events.
-/

module

public import LeanVM.Guest.B1.VsC.Os.WalkArms
public import LeanVM.Guest.B1.VsC.Os.OsProtoSpec
public import LeanVM.Guest.B1.VsC.Os.CLow
public import LeanVM.Guest.B1.VsC.Quiet

/-!
# The body on a memory

`osHonestA_val`: from the body's honest data (`OsHonestA`), on every memory holding the cursor's
words, the window tables and the buffers' honest words, the valuation `fill (Val.ofArgs args) 11
kEnd f` the honest data names makes every statement hold at the trivial callee relation (which
`OsHA` admits), with `OsOutA`'s outcome, the calls' values fixed before the memory (`CV`), its
loads fixed and its window hints exact. `osArm_walk`: at an arm, that valuation walks the body
(`osBody_walk`), every event holding. `callsAgree_flatD`: two valuations giving a flat body's call
statements the same values (`CV`) agree on its path's calls.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **The body's valuation on a memory.** -/
theorem osHonestA_val {c : OsCfg} {args : List E} {cur tabs : E} {xs : List E} {tgt inn res : E}
    {pt pt1 : List E} (H : OsHonestA c args cur tabs xs tgt inn res pt pt1) (b : ℕ) :
    ∃ CV : List (List E), ∀ rd, LowDef 11 rd → ReadsAt rd cur xs → WinTabs rd tabs → OsMemA rd c b H.own →
      ∃ σ, AgreeBelow 11 (Val.ofArgs args) σ ∧ AllOk (fun _ _ _ ↦ True) rd σ (osBodyA c) ∧
        OsOutA c b tabs tgt inn res (cur * gen ^ xs.length) H.own H.D σ ∧
        ((osBodyA c).filterMap Stmt.callVarsS).map (·.map σ) = CV ∧ OsLoadsIn c b H.own cur tabs xs σ ∧
        WinEx (osBodyA c) σ := by
  obtain ⟨CV, hb⟩ := H.body b
  refine ⟨CV, fun rd hl hr hw hm ↦ ?_⟩
  obtain ⟨kEnd, f, hf⟩ := hb rd hl
  obtain ⟨hok, ho, hcv, hld, hwx⟩ := hf (fun _ _ _ ↦ True) rd
    ⟨hr, hw, hm, fun _ _ _ _ _ _ _ ↦ trivial, fun _ _ _ _ ↦ trivial⟩ (fun _ _ ↦ rfl)
    (fill (Val.ofArgs args) 11 kEnd f) (agree_fill _ _ _ _) (range_fill _ _ _ _)
  exact ⟨_, agree_fill _ _ _ _, hok, ho, hcv, hld, hwx⟩

/-- **An arm's body on a memory**: its valuation walks it to its return, every event holding. -/
theorem osArm_walk {m ri : ℕ} (hm : m < 15) {args : List E} {cur tabs : E} {xs : List E} {tgt inn res : E}
    {pt pt1 : List E} (H : OsHonestA (osCfgR m ri) args cur tabs xs tgt inn res pt pt1) (b : ℕ) :
    ∃ CV : List (List E), ∀ rd, LowDef 11 rd → ReadsAt rd cur xs → WinTabs rd tabs →
      OsMemA rd (osCfgR m ri) b H.own →
      ∃ σ, AgreeBelow 11 (Val.ofArgs args) σ ∧
        walk σ (osBody (osCfg m)) = .ret ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ)) (osBodyRet (osCfgR m ri)) ∧
        (∀ e ∈ (osBodyA (osCfgR m ri)).flatMap (fdEvs σ), e.Holds rd σ) ∧
        OsOutA (osCfgR m ri) b tabs tgt inn res (cur * gen ^ xs.length) H.own H.D σ ∧
        ((osBodyA (osCfgR m ri)).filterMap Stmt.callVarsS).map (·.map σ) = CV ∧
        OsLoadsIn (osCfgR m ri) b H.own cur tabs xs σ ∧ WinEx (osBodyA (osCfgR m ri)) σ := by
  obtain ⟨CV, hb⟩ := osHonestA_val H b
  refine ⟨CV, fun rd hl hr hw hmm ↦ ?_⟩
  obtain ⟨σ, hag, hok, ho, hcv, hld, hwx⟩ := hb rd hl hr hw hmm
  obtain ⟨hwk, hev⟩ := osBody_walk hm hok
  exact ⟨σ, hag, hwk, hev, ho, hcv, hld, hwx⟩

theorem map_append_eq {σ σ' : Val} {a r : List V} (h : (a ++ r).map σ = (a ++ r).map σ') :
    a.map σ = a.map σ' ∧ r.map σ = r.map σ' := by
  rw [List.map_append, List.map_append] at h
  exact List.append_inj h (by simp)

theorem calls_armEvs (arm : List Stmt) : calls (armEvs arm) = [] := by
  unfold calls
  rw [List.filterMap_eq_nil_iff]
  intro e he
  obtain ⟨s, -, hs⟩ := List.mem_filterMap.mp he
  cases s <;> simp at hs
  subst hs; rfl

/-- **Two valuations giving a flat body's call statements the same values agree on its calls**,
whichever valuation takes the path. -/
theorem callsAgree_flatD {σ σ' τ : Val} : ∀ {ss : List Stmt}, ss.all Stmt.flatD = true →
    (ss.filterMap Stmt.callVarsS).map (·.map σ) = (ss.filterMap Stmt.callVarsS).map (·.map σ') →
    VsC.CallsAgree σ σ' (calls (ss.flatMap (fdEvs τ)))
  | [], _, _ => fun c hc ↦ by simp [calls] at hc
  | s :: ss, hf, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hf
    have key : (∀ v, Stmt.callVarsS s = some v → v.map σ = v.map σ') ∧
        (ss.filterMap Stmt.callVarsS).map (·.map σ) = (ss.filterMap Stmt.callVarsS).map (·.map σ') := by
      cases hv : Stmt.callVarsS s with
      | none =>
        rw [List.filterMap_cons_none hv] at h
        exact ⟨fun _ h' ↦ (nomatch h'), h⟩
      | some v =>
        rw [List.filterMap_cons_some hv, List.map_cons, List.map_cons, List.cons.injEq] at h
        exact ⟨fun _ h' ↦ (by cases h'; exact h.1), h.2⟩
    have hc : calls ((s :: ss).flatMap (fdEvs τ)) = calls (fdEvs τ s) ++ calls (ss.flatMap (fdEvs τ)) := by
      simp only [calls, List.flatMap_cons, List.filterMap_append]
    rw [hc]
    intro c hcm
    rcases List.mem_append.mp hcm with hcm | hcm
    · cases s with
      | atom a =>
        change c ∈ calls [Ev.atom a] at hcm
        simp [calls, Ev.call?] at hcm
      | call f a r =>
        change c ∈ calls [Ev.call f a r] at hcm
        simp only [calls, List.filterMap_cons, Ev.call?, List.filterMap_nil, List.mem_singleton] at hcm
        subst hcm
        exact map_append_eq (key.1 (a ++ r) rfl)
      | callIf c0 f a =>
        change c ∈ calls [Ev.inK c0, if τ c0 = 0 then .skip f a else .call f a []] at hcm
        have hv := key.1 (c0 :: a) rfl
        rw [List.map_cons, List.map_cons, List.cons.injEq] at hv
        split at hcm <;>
        · simp only [calls, List.filterMap_cons, Ev.call?, List.filterMap_nil, List.mem_singleton] at hcm
          subst hcm
          exact ⟨hv.2, rfl⟩
      | match_ x arms =>
        change c ∈ calls (armEvs (arms.getD (logG (τ x)) [])) at hcm
        rw [calls_armEvs] at hcm
        exact absurd hcm List.not_mem_nil
      | dispatch x fs a r =>
        change c ∈ calls [Ev.call (fs.getD (logG (τ x)) "") a r] at hcm
        simp only [calls, List.filterMap_cons, Ev.call?, List.filterMap_nil, List.mem_singleton] at hcm
        subst hcm
        have hv := key.1 (x :: a ++ r) rfl
        simp only [List.cons_append, List.map_cons, List.cons.injEq] at hv
        exact map_append_eq hv.2
      | ite _ _ _ => simp [Stmt.flatD] at hf
      | ret _ => simp [Stmt.flatD] at hf
    · exact callsAgree_flatD hf.2 key.2 c hcm

/-! ## The node's buffers -/

set_option maxRecDepth 100000 in
theorem noAddr_0 : (osBodyA (osCfg 0)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_1 : (osBodyA (osCfg 1)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_2 : (osBodyA (osCfg 2)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_3 : (osBodyA (osCfg 3)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_4 : (osBodyA (osCfg 4)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_5 : (osBodyA (osCfg 5)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_6 : (osBodyA (osCfg 6)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_7 : (osBodyA (osCfg 7)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_8 : (osBodyA (osCfg 8)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_9 : (osBodyA (osCfg 9)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_10 : (osBodyA (osCfg 10)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_11 : (osBodyA (osCfg 11)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_12 : (osBodyA (osCfg 12)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_13 : (osBodyA (osCfg 13)).filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem noAddr_14 : (osBodyA (osCfg 14)).filterMap Stmt.addrS = [] := by decide +kernel

/-- Every arm's body places no `frameAddr`. -/
theorem noAddr_all (m : ℕ) (hm : m < 15) : (osBodyA (osCfg m)).filterMap Stmt.addrS = [] := by
  interval_cases m
  · exact noAddr_0
  · exact noAddr_1
  · exact noAddr_2
  · exact noAddr_3
  · exact noAddr_4
  · exact noAddr_5
  · exact noAddr_6
  · exact noAddr_7
  · exact noAddr_8
  · exact noAddr_9
  · exact noAddr_10
  · exact noAddr_11
  · exact noAddr_12
  · exact noAddr_13
  · exact noAddr_14

/-- **An arm's node is placed** where `OsOutA` puts its buffers: its sizes `osSizesL`, its
pointers the allocator's bases from `b`, no `frameAddr`. -/
theorem osArm_nodeAt {m ri : ℕ} (hm : m < 15) {b : ℕ} {tabs tgt inn res cr : E} {own : List (List E)}
    {D : ℕ → OsLvData} {σ : Val} (cert : String → V → ℕ) (fp : ℕ) (f : String)
    (ho : OsOutA (osCfgR m ri) b tabs tgt inn res cr own D σ) :
    allocs σ ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ)) = osSizesL (osCfgR m ri) ∧
      NodeAt cert (fp, b) f σ (osSizesL (osCfgR m ri)) ((osBodyA (osCfgR m ri)).flatMap (fdEvs σ)) := by
  have hf := flatBody_all m hm
  rw [osBodyA_rate m ri] at hf
  have h1 : (osBodyA (osCfgR m ri)).all Stmt.flatD = true := by
    simp only [FlatBody, List.all_eq_true, Bool.and_eq_true] at hf
    exact List.all_eq_true.mpr fun s hs ↦ (hf s hs).1
  obtain ⟨i1, i2, i3⟩ := flatD_parts σ _ h1
  obtain ⟨-, ha, hb, -⟩ := ho
  have hna := noAddr_all m hm
  rw [osBodyA_rate m ri] at hna
  refine ⟨by rw [i2]; exact ha, ?_, ?_⟩
  · rw [i1]; exact hb
  · intro q hq
    rw [i3, hna] at hq
    exact absurd hq List.not_mem_nil

end
end LeanVM.Guest.B1.Whir
