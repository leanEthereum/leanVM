/-
  LeanVM.Guest.B1.Tables.FlatLiftOut

  A flat function evaluated forward, placed, returning its buffers: `flat_completeAt` and
  `flat_completeAtTB` with returns depending on the frame pointer and the buffers its `Lout`.
-/

module

public import LeanVM.Guest.B1.Tables.FlatLiftT

/-!
# Flat functions returning their buffers

`flat_completeAtOut`, `flat_completeAtOutTB`: `flat_completeAt` and `flat_completeAtTB` on
`completeAt_flatOutD` and `completeAt_flatOutDTB`: the returns `rets fp` at the frame pointer
`fp`, the function's buffers its returned layout, of which `Res` holds. Their proofs are the
originals', copied.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem flat_completeAtOut (F : FlatFn) {κ : ℕ} (Lin : Layout) (args : List E) (rets : ℕ → List E)
    (Res : List E → Layout → Prop) (hl : args.length = F.k)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (hout : ∀ fp, Res (rets fp) (bufL (fp + fs F.name) sizes (own fp)))
    (w : ℕ → ℕ → E) (bufs : ℕ → List (E × ℕ))
    (hbufs : ∀ fp, ∀ q ∈ bufs fp, ∃ b, q.1 = ofK (addressOfIndex b) ∧
      ∀ i < q.2, RegionL (flatL F.name Lin sizes own fs fp) (b + i))
    (hrun : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) →
      (∀ s ∈ F.pre, VSH (coreProgram.RelIn rd (RegionL (flatL F.name Lin sizes own fs fp))) rd
        (F.σ rd (w fp) args) s) ∧
      LoadsInBuf (F.σ rd (w fp) args) (bufs fp) F.evL ∧
      (F.pre.filterMap Main.Stmt.allocSz).map
        (fun x => x.2.elim id fun s => logG (F.σ rd (w fp) args s)) = sizes ∧
      ((F.pre.filterMap Main.Stmt.allocSz).map Prod.fst).map (F.σ rd (w fp) args) =
        (bases (fp + fs F.name) sizes).map (fun b => ofK (addressOfIndex b)) ∧
      F.rets.map (F.σ rd (w fp) args) = rets fp) :
    CompleteAtD fs cert κ F.name Lin args Res := by
  have hf := F.hf
  have hp := F.hp
  have hb' := F.hb
  -- the canonical memory and its callees
  classical
  obtain ⟨rdS, hS⟩ : ∃ rdS : ℕ → Reader, ∀ fp, (∃ rd, LowDef κ rd ∧ MemL rd (flatL F.name Lin sizes own fs fp)) →
      LowDef κ (rdS fp) ∧ MemL (rdS fp) (flatL F.name Lin sizes own fs fp) :=
    ⟨fun fp ↦ if h : ∃ rd, LowDef κ rd ∧ MemL rd (flatL F.name Lin sizes own fs fp) then h.choose else fun _ ↦ none,
      fun fp h ↦ by simp only [h, ↓reduceDIte]; exact h.choose_spec⟩
  generalize hσS : (fun fp ↦ F.σ (rdS fp) (w fp) args) = σS
  -- the valuations agree at a call's values
  have hag : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) → ∀ s ∈ F.pre, callB s = true →
      ∀ v ∈ s.vals, F.σ rd (w fp) args v = σS fp v := by
    intro fp rd hlow hL s hs hc v hv
    obtain ⟨-, hld, -⟩ := hrun fp rd hlow hL
    rw [← hσS]
    exact F.agree hl hL (hS fp ⟨rd, hlow, hL⟩).2 (hbufs fp) hld (F.call_vals hs hc v hv)
  have hmap : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) → ∀ s ∈ F.pre, callB s = true →
      ∀ l : List V, (∀ v ∈ l, v ∈ s.vals) → l.map (F.σ rd (w fp) args) = l.map (σS fp) :=
    fun fp rd hlow hL s hs hc l hl' ↦
      List.map_congr_left fun v hv ↦ hag fp rd hlow hL s hs hc v (hl' v hv)
  -- the calls are the same on every memory
  have hcs : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) →
      (F.pre.filterMap (Stmt.callSF (F.σ rd (w fp) args))).map (Main.mkCall (F.σ rd (w fp) args)) =
        (F.pre.filterMap (Stmt.callSF (σS fp))).map (Main.mkCall (σS fp)) := by
    intro fp rd hlow hL
    rw [List.map_filterMap, List.map_filterMap]
    refine List.filterMap_congr fun s hs ↦ ?_
    cases s with
    | call f a r => simp only [Stmt.callSF, Main.Stmt.callS, Option.map_some, Main.mkCall]
    | callIf c f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.map_some, Main.mkCall]
      rw [hag fp rd hlow hL _ hs rfl c (by simp [Stmt.vals])]
    | dispatch x fs' a r =>
      simp only [Stmt.callSF, Option.map_some, Main.mkCall]
      rw [hag fp rd hlow hL _ hs rfl x (by simp [Stmt.vals])]
    | _ => simp only [Stmt.callSF, Main.Stmt.callS, Option.map_none]
  refine completeAt_flatOutD (fs := fs) (cert := cert) hf F.hloop κ Lin args rets Res hb'
    F.hflat F.haddrs sizes own hown hout
    (fun fp ↦ ((F.pre.filterMap (Stmt.callSF (σS fp))).map (Main.mkCall (σS fp))).map
      (kidOf (σS fp) (flatL F.name Lin sizes own fs fp))) ?hkc ?hkr ?hkm ?hσ
  case hkr =>
    intro fp k hk _ i hi
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact regionL_append hi
  case hkm =>
    intro fp rd hB hLin k hk
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact Main.memL_append.mpr ⟨hLin, hB⟩
  case hkc =>
    intro fp k hk ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
    by_cases hex : ∃ rd, LowDef κ rd ∧ MemL rd (flatL F.name Lin sizes own fs fp)
    swap
    · intro fp'
      refine ⟨0, [], c.rets.map (σS fp), [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
        fun rd hlow hL ↦ absurd ⟨rd, hlow, by simpa [kidOf] using hL⟩ hex⟩
    obtain ⟨hlS, hLS⟩ := hS fp hex
    have hvS : ∀ s ∈ F.pre, VSH (coreProgram.RelIn (rdS fp) (RegionL (flatL F.name Lin sizes own fs fp))) (rdS fp) (σS fp) s := by
      rw [← hσS]; exact (hrun fp (rdS fp) hlS hLS).1
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hc
    obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht'
    have hok := List.all_eq_true.mp F.hcall s hs
    cases s with
    | call f a r =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [Main.mkCall, kidOf]
      refine Lift.completeAtD_of_relIn F.hpure (by simpa [callOk] using hok)
        fun rd hlow hL ↦ ?_
      have h : coreProgram.RelIn rd (RegionL (flatL F.name Lin sizes own fs fp)) f (a.map (F.σ rd (w fp) args))
          (r.map (F.σ rd (w fp) args)) := (hrun fp rd hlow hL).1 _ hs
      rwa [hmap fp rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv]),
        hmap fp rd hlow hL _ hs rfl r (fun v hv ↦ by simp [Stmt.vals, hv])] at h
    | callIf cnd f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [Main.mkCall, kidOf, decide_eq_true_eq, List.map_nil] at ht ⊢
      refine Lift.completeAtD_of_relIn F.hpure (by simpa [callOk] using hok)
        fun rd hlow hL ↦ ?_
      have h : IsInK (F.σ rd (w fp) args cnd) ∧ (F.σ rd (w fp) args cnd ≠ 0 →
          coreProgram.RelIn rd (RegionL (flatL F.name Lin sizes own fs fp)) f (a.map (F.σ rd (w fp) args)) []) :=
        (hrun fp rd hlow hL).1 _ hs
      have e := hag fp rd hlow hL _ hs rfl cnd (by simp [Stmt.vals])
      have h2 := h.2 (by rw [e]; exact ht)
      rwa [hmap fp rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv])] at h2
    | dispatch x fs' a r =>
      simp only [Stmt.callSF, Option.some.injEq] at hst
      subst hst
      simp only [callOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
      obtain ⟨j, hj, hxj, -⟩ := hvS _ hs
      have hlog : logG (σS fp x) = j := by rw [hxj]; exact logG_spec (by omega)
      simp only [Main.mkCall, kidOf, hlog, List.getD_eq_getElem _ _ hj]
      refine Lift.completeAtD_of_relIn F.hpure (by simpa using hok.1 _ (List.getElem_mem hj))
        fun rd hlow hL ↦ ?_
      obtain ⟨j', hj', hxj', h⟩ := ((hrun fp rd hlow hL).1 _ hs :
        ∃ (j' : ℕ) (h : j' < fs'.length), F.σ rd (w fp) args x = ofK (addressOfIndex j') ∧
          coreProgram.RelIn rd (RegionL (flatL F.name Lin sizes own fs fp)) fs'[j'] (a.map (F.σ rd (w fp) args))
            (r.map (F.σ rd (w fp) args)))
      have e := hag fp rd hlow hL _ hs rfl x (by simp [Stmt.vals])
      have hjj : j' = j := by
        have := congrArg logG (hxj'.symm.trans (e.trans hxj))
        rwa [logG_spec (by omega), logG_spec (by omega)] at this
      subst hjj
      rwa [hmap fp rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv]),
        hmap fp rd hlow hL _ hs rfl r (fun v hv ↦ by simp [Stmt.vals, hv])] at h
    | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst
  case hσ =>
    intro fp outs ho rd hlow hB hLin
    have hL : MemL rd (flatL F.name Lin sizes own fs fp) := Main.memL_append.mpr ⟨hLin, hB⟩
    obtain ⟨hv, hld, hsz, hbs, hrt⟩ := hrun fp rd hlow hL
    have hvR : ∀ s ∈ F.pre, VSH (coreProgram.Rel rd) rd (F.σ rd (w fp) args) s := fun s hs ↦
      vsh_mono (fun _ _ _ h ↦ Program.RelIn.rel h) (hv s hs)
    have hpar := F.params (rd := rd) (w := w fp) hl
    have hag' := hag fp rd hlow hL
    have hcs' := hcs fp rd hlow hL
    beta_reduce at ho
    generalize F.σ rd (w fp) args = σ at hv hld hsz hbs hrt hvR hpar hag' hcs'
    refine ⟨σ, by rw [hp, List.map_map]; exact hpar, fun s hs ↦ ?_, ?_, hsz, hbs, ?_, ?_⟩
    · have hok := List.all_eq_true.mp F.hcall s hs
      cases s with
      | dispatch x fs' a r =>
        simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨j, hj, hxj, -⟩ := hvR _ hs
        exact ⟨j, hj, by omega, hxj⟩
      | _ => exact True.intro
    · rw [hb', holdsList_append]
      exact holdsList_of_vsh F.pre F.hiteOk hvR hrt
    · rw [hcs']
      apply callsMatch_kids (σS := σS fp) (L := flatL F.name Lin sizes own fs fp)
      rotate_left
      · exact ho
      intro c hc v hv
      obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hc
      obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht'
      cases s with
      | call f a r =>
        simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
        subst hst
        exact hag' _ hs rfl v (by simpa [Main.mkCall, Stmt.vals] using hv)
      | callIf cnd f a =>
        simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
        subst hst
        exact hag' _ hs rfl v (by simp_all [Main.mkCall, Stmt.vals])
      | dispatch x fs' a r =>
        simp only [Stmt.callSF, Option.some.injEq] at hst
        subst hst
        exact hag' _ hs rfl v (by simp_all [Main.mkCall, Stmt.vals])
      | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst
    · intro q hq
      obtain ⟨d, hd⟩ := F.loadsEv_mem hq
      obtain ⟨i, hi, hr⟩ := inBuf_region (hbufs fp) (hld d q.1 q.2 hd)
      exact ⟨i, hi, regionL_append hr⟩

set_option maxRecDepth 20000 in
/-- **A flat function is complete, placed, by a tree of honest shape, within its frame, its
buffers and its callees' bounds.** -/
theorem flat_completeAtOutTB (F : FlatFn) {κ : ℕ} (Lin : Layout) (args : List E) (rets : ℕ → List E)
    (Res : List E → Layout → Prop) (hl : args.length = F.k)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (hout : ∀ fp, Res (rets fp) (bufL (fp + fs F.name) sizes (own fp)))
    (w : ℕ → ℕ → E) (bufs : ℕ → List (E × ℕ))
    (hbufs : ∀ fp, ∀ q ∈ bufs fp, ∃ b, q.1 = ofK (addressOfIndex b) ∧
      ∀ i < q.2, RegionL (flatL F.name Lin sizes own fs fp) (b + i))
    (hrun : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) →
      (∀ s ∈ F.pre, VSH (coreProgram.RelIn rd (RegionL (flatL F.name Lin sizes own fs fp))) rd
        (F.σ rd (w fp) args) s) ∧
      LoadsInBuf (F.σ rd (w fp) args) (bufs fp) F.evL ∧
      (F.pre.filterMap Main.Stmt.allocSz).map
        (fun x => x.2.elim id fun s => logG (F.σ rd (w fp) args s)) = sizes ∧
      ((F.pre.filterMap Main.Stmt.allocSz).map Prod.fst).map (F.σ rd (w fp) args) =
        (bases (fp + fs F.name) sizes).map (fun b => ofK (addressOfIndex b)) ∧
      F.rets.map (F.σ rd (w fp) args) = rets fp)
    (Q : Val → Prop) (Ts : List (Tree → Prop))
    (hQ : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) →
      Q (F.σ rd (w fp) args))
    (hTl : (F.pre.filter callB).length ≤ Ts.length)
    (hT : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) → ∀ i (c : Call),
      (flatCalls F.pre (F.σ rd (w fp) args))[i]? = some c → c.taken = true →
      ∀ (t : Tree) (r : List E), t.name = c.f →
        t.Valid coreProgram rd (c.args.map (F.σ rd (w fp) args)) r → t.BufsOk coreProgram →
        (Ts.getD i fun _ ↦ True) t)
    (Bs : List ℕ) (KB : ℕ)
    (hB : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) → ∀ i (c : Call),
      (flatCalls F.pre (F.σ rd (w fp) args))[i]? = some c → c.taken = true →
      ∀ rd', LowDef κ rd' → MemL rd' (flatL F.name Lin sizes own fs fp) → ∀ (t : Tree) (r : List E), t.name = c.f →
        t.Valid coreProgram rd' (c.args.map (F.σ rd (w fp) args)) r → t.BufsOk coreProgram →
        t.total fs ≤ Bs.getD i 0)
    (hKB : ∀ σ, callsBound fs (flatCalls F.pre σ) Bs ≤ KB) :
    CompleteAtDTB fs cert κ F.name Lin args Res
      (Budget.NodeHonest coreProgram F.name Q (flatCalls F.pre) (fun _ ↦ sizes) Ts)
      (fs F.name + sizes.sum + KB) := by
  have hf := F.hf
  have hp := F.hp
  have hb' := F.hb
  classical
  obtain ⟨rdS, hS⟩ : ∃ rdS : ℕ → Reader, ∀ fp, (∃ rd, LowDef κ rd ∧
      MemL rd (flatL F.name Lin sizes own fs fp)) →
      LowDef κ (rdS fp) ∧ MemL (rdS fp) (flatL F.name Lin sizes own fs fp) :=
    ⟨fun fp ↦ if h : ∃ rd, LowDef κ rd ∧ MemL rd (flatL F.name Lin sizes own fs fp) then
      h.choose else fun _ ↦ none, fun fp h ↦ by simp only [h, ↓reduceDIte]; exact h.choose_spec⟩
  generalize hσS : (fun fp ↦ F.σ (rdS fp) (w fp) args) = σS
  have hag : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) → ∀ s ∈ F.pre,
      callB s = true → ∀ v ∈ s.vals, F.σ rd (w fp) args v = σS fp v := by
    intro fp rd hlow hL s hs hc v hv
    obtain ⟨-, hld, -⟩ := hrun fp rd hlow hL
    rw [← hσS]
    exact F.agree hl hL (hS fp ⟨rd, hlow, hL⟩).2 (hbufs fp) hld (F.call_vals hs hc v hv)
  have hmap : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) → ∀ s ∈ F.pre,
      callB s = true → ∀ l : List V, (∀ v ∈ l, v ∈ s.vals) →
        l.map (F.σ rd (w fp) args) = l.map (σS fp) :=
    fun fp rd hlow hL s hs hc l hl' ↦
      List.map_congr_left fun v hv ↦ hag fp rd hlow hL s hs hc v (hl' v hv)
  have hcs : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) →
      flatCalls F.pre (F.σ rd (w fp) args) = flatCalls F.pre (σS fp) := by
    intro fp rd hlow hL
    unfold flatCalls
    rw [List.map_filterMap, List.map_filterMap]
    refine List.filterMap_congr fun s hs ↦ ?_
    cases s with
    | call f a r => simp only [Stmt.callSF, Main.Stmt.callS, Option.map_some, Main.mkCall]
    | callIf c f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.map_some, Main.mkCall]
      rw [hag fp rd hlow hL _ hs rfl c (by simp [Stmt.vals])]
    | dispatch x fs' a r =>
      simp only [Stmt.callSF, Option.map_some, Main.mkCall]
      rw [hag fp rd hlow hL _ hs rfl x (by simp [Stmt.vals])]
    | _ => simp only [Stmt.callSF, Main.Stmt.callS, Option.map_none]
  -- a call's values agree
  have hagc : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) →
      ∀ c ∈ flatCalls F.pre (σS fp), ∀ v ∈ c.args ++ c.rets, F.σ rd (w fp) args v = σS fp v := by
    intro fp rd hlow hL c hc v hv
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hc
    obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht'
    cases s with
    | call f a r =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      exact hag fp rd hlow hL _ hs rfl v (by simpa [Main.mkCall, Stmt.vals] using hv)
    | callIf cnd f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      exact hag fp rd hlow hL _ hs rfl v (by simp_all [Main.mkCall, Stmt.vals])
    | dispatch x fs' a r =>
      simp only [Stmt.callSF, Option.some.injEq] at hst
      subst hst
      exact hag fp rd hlow hL _ hs rfl v (by simp_all [Main.mkCall, Stmt.vals])
    | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst
  -- each entered callee is complete
  have hkd : ∀ fp, (∃ rd, LowDef κ rd ∧ MemL rd (flatL F.name Lin sizes own fs fp)) →
      ∀ c ∈ flatCalls F.pre (σS fp), c.taken = true → c.f ∈ F.kids ∧
        ∀ rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) →
          coreProgram.RelIn rd (RegionL (flatL F.name Lin sizes own fs fp)) c.f (c.args.map (σS fp))
            (c.rets.map (σS fp)) := by
    intro fp hex c hc ht
    obtain ⟨hlS, hLS⟩ := hS fp hex
    have hvS : ∀ s ∈ F.pre, VSH (coreProgram.RelIn (rdS fp)
        (RegionL (flatL F.name Lin sizes own fs fp))) (rdS fp) (σS fp) s := by
      rw [← hσS]; exact (hrun fp (rdS fp) hlS hLS).1
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hc
    obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht'
    have hok := List.all_eq_true.mp F.hcall s hs
    cases s with
    | call f a r =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [Main.mkCall]
      refine ⟨(by simpa [callOk] using hok),
        fun rd hlow hL ↦ ?_⟩
      have h : coreProgram.RelIn rd (RegionL (flatL F.name Lin sizes own fs fp)) f
          (a.map (F.σ rd (w fp) args)) (r.map (F.σ rd (w fp) args)) := (hrun fp rd hlow hL).1 _ hs
      rwa [hmap fp rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv]),
        hmap fp rd hlow hL _ hs rfl r (fun v hv ↦ by simp [Stmt.vals, hv])] at h
    | callIf cnd f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      simp only [Main.mkCall, decide_eq_true_eq, List.map_nil] at ht ⊢
      refine ⟨(by simpa [callOk] using hok),
        fun rd hlow hL ↦ ?_⟩
      have h : IsInK (F.σ rd (w fp) args cnd) ∧ (F.σ rd (w fp) args cnd ≠ 0 →
          coreProgram.RelIn rd (RegionL (flatL F.name Lin sizes own fs fp)) f
            (a.map (F.σ rd (w fp) args)) []) := (hrun fp rd hlow hL).1 _ hs
      have e := hag fp rd hlow hL _ hs rfl cnd (by simp [Stmt.vals])
      have h2 := h.2 (by rw [e]; exact ht)
      rwa [hmap fp rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv])] at h2
    | dispatch x fs' a r =>
      simp only [Stmt.callSF, Option.some.injEq] at hst
      subst hst
      simp only [callOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
      obtain ⟨j, hj, hxj, -⟩ := hvS _ hs
      have hlog : logG (σS fp x) = j := by rw [hxj]; exact logG_spec (by omega)
      simp only [Main.mkCall, hlog, List.getD_eq_getElem _ _ hj]
      refine ⟨(by simpa using hok.1 _ (List.getElem_mem hj)),
        fun rd hlow hL ↦ ?_⟩
      obtain ⟨j', hj', hxj', h⟩ := ((hrun fp rd hlow hL).1 _ hs :
        ∃ (j' : ℕ) (h : j' < fs'.length), F.σ rd (w fp) args x = ofK (addressOfIndex j') ∧
          coreProgram.RelIn rd (RegionL (flatL F.name Lin sizes own fs fp)) fs'[j']
            (a.map (F.σ rd (w fp) args)) (r.map (F.σ rd (w fp) args)))
      have e := hag fp rd hlow hL _ hs rfl x (by simp [Stmt.vals])
      have hjj : j' = j := by
        have := congrArg logG (hxj'.symm.trans (e.trans hxj))
        rwa [logG_spec (by omega), logG_spec (by omega)] at this
      subst hjj
      rwa [hmap fp rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv]),
        hmap fp rd hlow hL _ hs rfl r (fun v hv ↦ by simp [Stmt.vals, hv])] at h
    | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst
  refine completeAt_flatOutDTB (fs := fs) (cert := cert) hf F.hloop κ Lin args rets Res hb'
    F.hflat F.haddrs sizes own hown hout
    (fun fp ↦ (flatCalls F.pre (σS fp)).map (kidOf (σS fp) (flatL F.name Lin sizes own fs fp)))
    Q Ts Bs KB ?hkc ?hKB ?hkl ?hkr ?hkm ?hσ
  case hkl =>
    intro fp
    rw [List.length_map, flatCalls_length]; exact hTl
  case hkr =>
    intro fp k hk _ i hi
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact regionL_append hi
  case hkm =>
    intro fp rd hB hLin k hk
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
    exact Main.memL_append.mpr ⟨hLin, hB⟩
  case hKB =>
    intro fp
    rw [kidsBoundL_map]
    exact hKB (σS fp)
  case hkc =>
    intro fp
    refine kidsDTB_of_getElem _ Ts Bs fun i c hc ht ↦ ?_
    by_cases hex : ∃ rd, LowDef κ rd ∧ MemL rd (flatL F.name Lin sizes own fs fp)
    swap
    · intro fp'
      exact ⟨0, [], c.rets.map (σS fp), [], Nat.zero_le _, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
        fun rd hlow hL ↦ absurd ⟨rd, hlow, by simpa using hL⟩ hex⟩
    obtain ⟨hlS, hLS⟩ := hS fp hex
    have hcm : c ∈ flatCalls F.pre (σS fp) := List.mem_of_getElem? hc
    obtain ⟨hmem, hrel⟩ := hkd fp hex c hcm ht
    have hBi : ∀ rd', LowDef κ rd' → MemL rd' (flatL F.name Lin sizes own fs fp) → ∀ (t : Tree) (r : List E),
        t.name = c.f → t.Valid coreProgram rd' (c.args.map (σS fp)) r → t.BufsOk coreProgram →
        t.total fs ≤ Bs.getD i 0 := by
      have hcS : (flatCalls F.pre (F.σ (rdS fp) (w fp) args))[i]? = some c := by
        rw [show F.σ (rdS fp) (w fp) args = σS fp from by rw [← hσS]]; exact hc
      have := hB fp (rdS fp) hlS hLS i c hcS ht
      rwa [show F.σ (rdS fp) (w fp) args = σS fp from by rw [← hσS]] at this
    refine ((completeAtDTB_of_relIn_on F.hpure hmem hBi hrel).and_valid_on
      fun rd hlow hL t r hn hv hbo ↦ ?_).mono le_rfl fun t h ↦ h.2
    have hc' : (flatCalls F.pre (F.σ rd (w fp) args))[i]? = some c := by
      rw [hcs fp rd hlow hL]; exact hc
    have ha : c.args.map (σS fp) = c.args.map (F.σ rd (w fp) args) :=
      List.map_congr_left fun v hv ↦
        (hagc fp rd hlow hL c hcm v (List.mem_append_left _ hv)).symm
    rw [ha] at hv
    exact hT fp rd hlow hL i c hc' ht t r hn hv hbo
  case hσ =>
    intro fp outs ho rd hlow hB hLin
    have hL : MemL rd (flatL F.name Lin sizes own fs fp) := Main.memL_append.mpr ⟨hLin, hB⟩

    obtain ⟨hv, hld, hsz, hbs, hrt⟩ := hrun fp rd hlow hL
    have hvR : ∀ s ∈ F.pre, VSH (coreProgram.Rel rd) rd (F.σ rd (w fp) args) s := fun s hs ↦
      vsh_mono (fun _ _ _ h ↦ Program.RelIn.rel h) (hv s hs)
    have hpar := F.params (rd := rd) (w := w fp) hl
    have hag' := hagc fp rd hlow hL
    have hcs' := hcs fp rd hlow hL
    have hQ' := hQ fp rd hlow hL
    generalize F.σ rd (w fp) args = σ at hv hld hsz hbs hrt hvR hpar hag' hcs' hQ'
    refine ⟨σ, by rw [hp, List.map_map]; exact hpar, fun s hs ↦ ?_, ?_, hsz, hbs, ?_, ?_, hQ'⟩
    · have hok := List.all_eq_true.mp F.hcall s hs
      cases s with
      | dispatch x fs' a r =>
        simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hok
        obtain ⟨j, hj, hxj, -⟩ := hvR _ hs
        exact ⟨j, hj, by omega, hxj⟩
      | _ => exact True.intro
    · rw [hb', holdsList_append]
      exact holdsList_of_vsh F.pre F.hiteOk hvR hrt
    · rw [hcs']
      exact callsMatch_kids (σS := σS fp) (L := (flatL F.name Lin sizes own fs fp)) _ outs hag' ho
    · intro q hq
      obtain ⟨d, hd⟩ := F.loadsEv_mem hq
      obtain ⟨i, hi, hr⟩ := inBuf_region (hbufs fp) (hld d q.1 q.2 hd)
      exact ⟨i, hi, regionL_append hr⟩

end
end LeanVM.Guest.B1.Tables
