/-
  LeanVM.Guest.B1.Tables.FlatLift

  A flat function evaluated forward (`Fwd.ev`), placed: from its honest valuation on every memory
  holding its layout, the uniform placed form (`CompleteAtD`).
-/

module

public import LeanVM.Guest.B1.Tables.FlatAtT
public import LeanVM.Guest.B1.Tables.VtC.Calls
public import LeanVM.Guest.B1.Tables.VtC.Agree
public import LeanVM.Guest.B1.Fwd.FlatIte
public import LeanVM.Guest.Memory.LiftPure
import LeanVM.Guest.StmtsAppend

/-!
# Flat functions, placed

`FlatFn`: a function's kernel facts: found, not a loop, its parameters `.n 0 .. .n (k-1)`, its
body `pre ++ [ret rets]` of flat statements (`Stmt.flat`) with no `frameAddr`, its `ite`s of
straight branches without loads, its evaluation list `evL = (flatIte pre).map fixNe` accepted by
the checker, its range checks' reads (`aux`) used by nothing else (`deadS`), its callees in a set
`kids` placing nothing (`Program.PureIn`) with short dispatch lists. `F.σ rd w args`: the honest
valuation, `Fwd.ev` on the memory `rd` and the oracle `w` from `args`.

`F` is complete on the caller's words `Lin` (`flat_completeAtTBR`, `FlatLiftT`) when, at every frame pointer,
its own buffers' words `own fp` (the allocator's sizes `sizes` from `fp + fs F.name`) and an oracle
`w fp` make the honest valuation satisfy every statement (`VSH`, calls by relations loading from
the layout `flatL`) on every memory defined below `2^κ` holding `Lin` and the buffers, its loads
inside listed buffers of that layout (`LoadsInBuf`), its allocations the allocator's, its returns
`rets`. The callees are placed from their relations (`Lift.completeAtD_of_relIn`); their
arguments and returns are the same on every such memory, the evaluations agreeing off the range
checks' reads (`FlatFn.agree`, `ev_agree`), so they are fixed from one such memory
(`FlatFn.fixCalls`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- A statement's callees are in `kids` and its dispatches are short. -/
def callOk (kids : List String) : Stmt → Bool
  | .call f _ _ | .callIf _ f _ => kids.contains f
  | .dispatch _ fs _ _ => fs.all kids.contains && decide (fs.length < 2 ^ 64 - 1)
  | _ => true

/-- **A flat function's kernel facts.** -/
structure FlatFn where
  name : String
  fn : Fn
  k : ℕ
  pre : List Stmt
  rets : List V
  evL : List Stmt
  aux : ℕ → Bool
  kids : List String
  hf : coreProgram.find? name = some fn
  hloop : coreProgram.loop name = false
  hp : fn.params = (List.range k).map V.n
  hb : fn.body = pre ⧺ [.ret rets]
  hevL : evL = (flatIte pre).map fixNe
  hchk : ∃ c, chk k evL = some c
  hdead : evL.all (deadS aux) = true
  haux : ∀ i ∈ auxIdx evL, aux i = true
  hflat : pre.all Stmt.flat = true
  haddrs : pre.filterMap Main.Stmt.addrS = []
  hiteOk : pre.all iteOk = true
  hcall : pre.all (callOk kids) = true
  hpure : coreProgram.PureIn kids

/-- **The honest valuation** of a flat function. -/
noncomputable def FlatFn.σ (F : FlatFn) (rd : Reader) (w : ℕ → E) (args : List E) : Val :=
  B1.Val.ofArgs (ev rd w args F.evL)

/-- The layout of the caller's words and the buffers at `fp`. -/
def flatL (f : String) (Lin : Layout) (sizes : List ℕ) (own : ℕ → List (List E))
    (fs : String → ℕ) (fp : ℕ) : Layout :=
  Lin ++ bufL (fp + fs f) sizes (own fp)

namespace FlatFn

variable (F : FlatFn)

theorem params {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = F.k) :
    (List.range F.k).map (fun k ↦ F.σ rd w args (.n k)) = args := by
  obtain ⟨c, hc⟩ := F.hchk
  apply List.ext_getElem (by simp [hl])
  intro i h1 _
  simp only [List.getElem_map, List.getElem_range]
  have hi : i < F.k := by simpa using h1
  rw [← List.getD_eq_getElem _ 0 (by omega)]
  exact ev_params rd w (by rw [hl]; exact hc) (by rw [hl]; exact hi)

theorem evL_mem {s : Stmt} (hs : s ∈ F.pre) (hni : ∀ c z n, s ≠ .ite c z n) : fixNe s ∈ F.evL := by
  rw [F.hevL]; exact List.mem_map_of_mem (mem_flatIte_of hni hs)

/-- A load the walk makes is a load of the evaluation list. -/
theorem loadsEv_mem {σ : Val} {q : V × ℕ} (h : q ∈ F.pre.flatMap (loadsEv σ)) :
    ∃ d, Stmt.atom (.load d q.1 q.2) ∈ F.evL := by
  obtain ⟨s, hs, hq⟩ := List.mem_flatMap.mp h
  have hld : ∀ t : Stmt, Stmt.loadS t = some q → ∃ d, t = .atom (.load d q.1 q.2) := by
    intro t ht
    match t, ht with
    | .atom (.load d p off), ht =>
      simp only [Stmt.loadS, Option.some.injEq] at ht
      subst ht; exact ⟨d, rfl⟩
  rw [F.hevL]
  cases s with
  | ite c z n =>
    simp only [loadsEv] at hq
    obtain ⟨t, ht, htq⟩ := List.mem_filterMap.mp hq
    have htm : t ∈ z ++ n := by split at ht <;> simp [ht]
    obtain ⟨d, rfl⟩ := hld t htq
    exact ⟨d, List.mem_map_of_mem (f := fixNe) (mem_flatIte_ite hs _ htm)⟩
  | _ =>
    simp only [loadsEv, Option.mem_toList] at hq
    obtain ⟨d, e⟩ := hld _ hq
    refine ⟨d, ?_⟩
    have := List.mem_map_of_mem (f := fixNe) (mem_flatIte_of (fun c z n h ↦ by cases h) hs)
    rw [e] at this
    exact this

end FlatFn

/-! ## Addresses -/

theorem limb_mul_gen (b j off : ℕ) :
    (ofK (addressOfIndex b) * gen ^ j).limb 0 * addressOfIndex off = addressOfIndex (b + j +
        off) := by
  have e : ofK (addressOfIndex b) * gen ^ j = ofK (addressOfIndex (b + j)) := by
    rw [gen_pow_eq_ofK, ← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, pow_add]
  rw [e, Main.addr_ofK]

/-- A load inside a listed buffer of a layout reads inside the layout. -/
theorem inBuf_region {σ : Val} {bufs : List (E × ℕ)} {L : Layout}
    (hbufs : ∀ q ∈ bufs, ∃ b, q.1 = ofK (addressOfIndex b) ∧ ∀ i < q.2, RegionL L (b + i))
    {p : V} {off : ℕ} (h : InBuf σ bufs p off) :
    ∃ i, (σ p).limb 0 * addressOfIndex off = addressOfIndex i ∧ RegionL L i := by
  obtain ⟨q, hq, j, hp, hj⟩ := h
  obtain ⟨b, hb, hr⟩ := hbufs q hq
  refine ⟨b + j + off, by rw [hp, hb, limb_mul_gen], ?_⟩
  have := hr (j + off) hj
  rwa [← Nat.add_assoc] at this

/-! ## Calls -/

/-- A statement holds with calls by `C`, by the taken branch for an `ite`: mono in `C`. -/
theorem vsh_mono {C C' : CallRel} (hC : CallRel.Le C C') {rd : Reader} {σ : Val} :
    ∀ {s : Stmt}, VSH C rd σ s → VSH C' rd σ s
  | .atom _, h => h
  | .call .., h => hC _ _ _ h
  | .callIf .., h => ⟨h.1, fun hc ↦ hC _ _ _ (h.2 hc)⟩
  | .dispatch .., h => let ⟨j, hj, hx, hc⟩ := h; ⟨j, hj, hx, hC _ _ _ hc⟩
  | .ite .., h => ⟨h.1, fun hc t ht ↦ sholds_mono hC (h.2.1 hc t ht),
      fun hc t ht ↦ sholds_mono hC (h.2.2 hc t ht)⟩
  | .ret _, h => h
  | .match_ .., h => h
where
  sholds_mono {C C' : CallRel} (hC : CallRel.Le C C') {rd : Reader} {σ : Val} :
      ∀ {s : Stmt}, SHolds C rd σ s → SHolds C' rd σ s
    | .atom _, h => h
    | .call .., h => hC _ _ _ h
    | .callIf .., h => ⟨h.1, fun hc ↦ hC _ _ _ (h.2 hc)⟩
    | .dispatch .., h => let ⟨j, hj, hx, hc⟩ := h; ⟨j, hj, hx, hC _ _ _ hc⟩
    | .ite .., h => h
    | .ret _, h => h
    | .match_ .., h => h

/-- The callee an entered frame is, its arguments' and returns' words under `σ`, on the layout
`L`. -/
noncomputable def kidOf (σ : Val) (L : Layout) (c : Call) : Kid :=
  ⟨c.f, c.taken, c.args.map σ, L, Returns (c.rets.map σ)⟩

theorem callsMatch_kids {σ σS : Val} {L : Layout} :
    ∀ (cs : List Call) (outs : List (List E × Layout)),
      (∀ c ∈ cs, ∀ v ∈ c.args ++ c.rets, σ v = σS v) →
      OutsOk (cs.map (kidOf σS L)) outs → CallsMatch σ cs (cs.map (kidOf σS L)) outs
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | c :: cs, o :: os, hag, ⟨ho, hos⟩ => by
    refine ⟨rfl, rfl, fun ht ↦ ⟨?_, ?_⟩, callsMatch_kids cs os
      (fun c' hc' ↦ hag c' (List.mem_cons_of_mem _ hc')) hos⟩
    · exact List.map_congr_left fun v hv ↦ hag c List.mem_cons_self v (List.mem_append_left _ hv)
    · rw [show o.1 = c.rets.map σS from (ho ht).1]
      exact List.map_congr_left fun v hv ↦ hag c List.mem_cons_self v (List.mem_append_right _ hv)

/-! ## The honest valuation on two memories -/

/-- **On two memories holding the layout, the honest valuations agree off the range checks'
reads**, when the first one's loads land inside the layout. -/
theorem FlatFn.agree (F : FlatFn) {rd1 rd2 : Reader} {w : ℕ → E} {args : List E}
    (hl : args.length = F.k)
    {L : Layout} (h1 : MemL rd1 L) (h2 : MemL rd2 L) {bufs : List (E × ℕ)}
    (hbufs : ∀ q ∈ bufs, ∃ b, q.1 = ofK (addressOfIndex b) ∧ ∀ i < q.2, RegionL L (b + i))
    (hld : LoadsInBuf (F.σ rd1 w args) bufs F.evL) {v : V} (hv : F.aux v.idx = false) :
    F.σ rd1 w args v = F.σ rd2 w args v := by
  have hrd : ∀ d p off, Stmt.atom (.load d p off) ∈ F.evL →
      rd1 ((B1.Val.ofArgs (ev rd1 w args F.evL) p).limb 0 * addressOfIndex off) =
        rd2 ((B1.Val.ofArgs (ev rd1 w args F.evL) p).limb 0 * addressOfIndex off) := by
    intro d p off hm
    obtain ⟨i, hi, hr⟩ := inBuf_region hbufs (hld d p off hm)
    have hi' : (B1.Val.ofArgs (ev rd1 w args F.evL) p).limb 0 * addressOfIndex off = addressOfIndex
        i := hi
    rw [hi']
    exact Main.memL_agree h1 h2 i hr
  obtain ⟨c, hc⟩ := F.hchk
  have hag := ev_agree rd1 rd2 w F.aux F.evL args args (by rw [hl]; exact hc) rfl
    (fun _ _ ↦ rfl) F.hdead F.haux hrd
  unfold FlatFn.σ B1.Val.ofArgs
  exact hag _ hv

/-- **A call statement's values are not range-check reads.** -/
theorem FlatFn.call_vals (F : FlatFn) {s : Stmt} (hs : s ∈ F.pre) (hc : callB s = true) :
    ∀ v ∈ s.vals, F.aux v.idx = false := by
  have hfix : fixNe s = s := by cases s <;> simp_all [callB, fixNe]
  have hm : s ∈ F.evL := by
    have := F.evL_mem hs (fun c z n h ↦ by subst h; simp [callB] at hc)
    rwa [hfix] at this
  have hd := List.all_eq_true.mp F.hdead s hm
  exact dead_vals hd (fun x y t1 t2 k h ↦ by subst h; simp [callB] at hc)
    (fun t p h ↦ by subst h; simp [callB] at hc)

theorem regionL_append {L L' : Layout} {i : ℕ} (h : RegionL (L ++ L') i) :
    RegionL L i ∨ RegionL L' i := by
  obtain ⟨q, hq, h1, h2⟩ := h
  rcases List.mem_append.mp hq with hq | hq
  · exact Or.inl ⟨q, hq, h1, h2⟩
  · exact Or.inr ⟨q, hq, h1, h2⟩

theorem regionL_append_left {L L' : Layout} {i : ℕ} (h : RegionL L i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_left _ hq, h1, h2⟩

theorem regionL_append_right {L L' : Layout} {i : ℕ} (h : RegionL L' i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_right _ hq, h1, h2⟩

/-! ## Statements from a body's relation -/

theorem sholds_of_straight {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
    ∀ (ss : List Stmt) {next : Prop}, ss.all straightB = true →
      Stmt.HoldsList C rd σ ss next kret → ∀ s ∈ ss, SHolds C rd σ s
  | [], _, _, _ => fun _ h ↦ absurd h (by simp)
  | s :: ss, _, hst, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hst
    simp only [Stmt.HoldsList] at h
    intro t ht
    cases s with
    | atom a =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact h.1
      · exact sholds_of_straight ss hst.2 h.2 t ht
    | call f a r =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact h.1
      · exact sholds_of_straight ss hst.2 h.2 t ht
    | callIf c f a =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨h.1, h.2.1⟩
      · exact sholds_of_straight ss hst.2 h.2.2 t ht
    | dispatch x fs a r =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact h.1
      · exact sholds_of_straight ss hst.2 h.2 t ht
    | _ => simp [straightB] at hst

/-- **Each statement of a body whose relation holds holds**, an `ite` by its taken branch. -/
theorem vsh_of_holdsList {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
    ∀ (ss : List Stmt) {next : Prop}, ss.all iteOk = true →
      Stmt.HoldsList C rd σ ss next kret → ∀ s ∈ ss, VSH C rd σ s
  | [], _, _, _ => fun _ h ↦ absurd h (by simp)
  | s :: ss, next, hok, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [Stmt.HoldsList] at h
    intro t ht
    cases s with
    | atom a =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact h.1
      · exact vsh_of_holdsList ss hok.2 h.2 t ht
    | call f a r =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact h.1
      · exact vsh_of_holdsList ss hok.2 h.2 t ht
    | callIf c f a =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨h.1, h.2.1⟩
      · exact vsh_of_holdsList ss hok.2 h.2.2 t ht
    | dispatch x fs a r =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact h.1
      · exact vsh_of_holdsList ss hok.2 h.2 t ht
    | ite c z n =>
      simp only [iteOk, Bool.and_eq_true] at hok
      obtain ⟨hk, hz, hn⟩ := h
      have tail : Stmt.HoldsList C rd σ ss next kret := by
        by_cases hc : σ c = 0
        · exact holdsList_tail z hok.1.1 (hz hc)
        · exact holdsList_tail n hok.1.2 (hn hc)
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨hk, fun hc ↦ sholds_of_straight z hok.1.1 (hz hc),
          fun hc ↦ sholds_of_straight n hok.1.2 (hn hc)⟩
      · exact vsh_of_holdsList ss hok.2 tail t ht
    | _ => simp [iteOk, straightB] at hok
where
  holdsList_tail {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
      ∀ (z : List Stmt) {next : Prop}, z.all straightB = true →
        Stmt.HoldsList C rd σ z next kret → next
    | [], _, _, h => h
    | s :: ss, _, hst, h => by
      simp only [List.all_cons, Bool.and_eq_true] at hst
      simp only [Stmt.HoldsList] at h
      cases s with
      | atom a => exact holdsList_tail ss hst.2 h.2
      | call f a r => exact holdsList_tail ss hst.2 h.2
      | callIf c f a => exact holdsList_tail ss hst.2 h.2.2
      | dispatch x fs a r => exact holdsList_tail ss hst.2 h.2
      | _ => simp [straightB] at hst

/-! ## The body on one memory -/

/-- **The honest valuation satisfies the body** on a memory where it satisfies every statement:
its parameters are the arguments, its dispatches name callees, and the body's relation holds. -/
theorem FlatFn.holds (F : FlatFn) {rd : Reader} {w : ℕ → E} {args rets : List E} {R : ℕ → Prop}
    (hl : args.length = F.k) (hv : ∀ s ∈ F.pre, VSH (coreProgram.RelIn rd R) rd (F.σ rd w args) s)
    (hrt : F.rets.map (F.σ rd w args) = rets) :
    F.fn.params.map (F.σ rd w args) = args ∧ (∀ s ∈ F.pre, DispOk (F.σ rd w args) s) ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd (F.σ rd w args) F.fn.body False (fun r => r = rets) := by
  have hvR : ∀ s ∈ F.pre, VSH (coreProgram.Rel rd) rd (F.σ rd w args) s := fun s hs ↦
    vsh_mono (fun _ _ _ h ↦ Program.RelIn.rel h) (hv s hs)
  refine ⟨by rw [F.hp, List.map_map]; exact F.params hl, fun s hs ↦ ?_, ?_⟩
  · have hok := List.all_eq_true.mp F.hcall s hs
    cases s with
    | dispatch x fs' a r =>
      simp only [callOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨j, hj, hxj, -⟩ := hvR _ hs
      exact ⟨j, hj, by omega, hxj⟩
    | _ => exact True.intro
  · rw [F.hb, holdsList_append]
    exact holdsList_of_vsh F.pre F.hiteOk hvR hrt

/-- The walk's loads, inside listed buffers of `L ++ L'`, read inside `L` or `L'`. -/
theorem FlatFn.loads_in (F : FlatFn) {σ : Val} {bufs : List (E × ℕ)} {L L' : Layout}
    (hbufs : ∀ q ∈ bufs, ∃ b, q.1 = ofK (addressOfIndex b) ∧ ∀ i < q.2, RegionL (L ++ L') (b + i))
    (hld : LoadsInBuf σ bufs F.evL) :
    ∀ q ∈ F.pre.flatMap (loadsEv σ), ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧
      (RegionL L i ∨ RegionL L' i) := fun q hq ↦
  let ⟨d, hd⟩ := F.loadsEv_mem hq
  let ⟨i, hi, hr⟩ := inBuf_region hbufs (hld d q.1 q.2 hd)
  ⟨i, hi, regionL_append hr⟩

theorem kidOf_region {σ : Val} {L L' : Layout} {cs : List Call} {k : Kid}
    (hk : k ∈ cs.map (kidOf σ (L ++ L'))) {i : ℕ} (hi : RegionL k.Lin i) : RegionL L i ∨ RegionL L' i := by
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
  exact regionL_append hi

theorem kidOf_memL {σ : Val} {L L' : Layout} {cs : List Call} {k : Kid} {rd : Reader}
    (hk : k ∈ cs.map (kidOf σ (L ++ L'))) (h : MemL rd L) (h' : MemL rd L') : MemL rd k.Lin := by
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hk
  exact Main.memL_append.mpr ⟨h, h'⟩

/-! ## The calls, fixed across memories -/

/-- **A flat function's calls are the same on every memory** holding a layout `L fp` that its loads
stay inside: one valuation `σS fp`, the honest one on some such memory, gives every call's
arguments and returns on each, and each entered call's relation holds at them on each. -/
theorem FlatFn.fixCalls (F : FlatFn) {κ : ℕ} {args : List E} (hl : args.length = F.k)
    (L : ℕ → Layout) (w : ℕ → ℕ → E) (bufs : ℕ → List (E × ℕ))
    (hbufs : ∀ fp, ∀ q ∈ bufs fp, ∃ b, q.1 = ofK (addressOfIndex b) ∧ ∀ i < q.2, RegionL (L fp) (b + i))
    (hrun : ∀ fp rd, LowDef κ rd → MemL rd (L fp) →
      (∀ s ∈ F.pre, VSH (coreProgram.RelIn rd (RegionL (L fp))) rd (F.σ rd (w fp) args) s) ∧
      LoadsInBuf (F.σ rd (w fp) args) (bufs fp) F.evL) :
    ∃ σS : ℕ → Val, ∀ fp rd, LowDef κ rd → MemL rd (L fp) →
      flatCalls F.pre (F.σ rd (w fp) args) = flatCalls F.pre (σS fp) ∧
      (∀ c ∈ flatCalls F.pre (σS fp), ∀ v ∈ c.args ++ c.rets, F.σ rd (w fp) args v = σS fp v) ∧
      ∀ c ∈ flatCalls F.pre (σS fp), c.taken = true → c.f ∈ F.kids ∧
        ∀ rd', LowDef κ rd' → MemL rd' (L fp) →
          coreProgram.RelIn rd' (RegionL (L fp)) c.f (c.args.map (σS fp)) (c.rets.map (σS fp)) := by
  classical
  -- one memory holding the layout, where there is one
  obtain ⟨rdS, hS⟩ : ∃ rdS : ℕ → Reader, ∀ fp, (∃ rd, LowDef κ rd ∧ MemL rd (L fp)) →
      LowDef κ (rdS fp) ∧ MemL (rdS fp) (L fp) :=
    ⟨fun fp ↦ if h : ∃ rd, LowDef κ rd ∧ MemL rd (L fp) then h.choose else fun _ ↦ none,
      fun fp h ↦ by simp only [h, ↓reduceDIte]; exact h.choose_spec⟩
  refine ⟨fun fp ↦ F.σ (rdS fp) (w fp) args, fun fp rd0 hl0 hL0 ↦ ?_⟩
  beta_reduce
  obtain ⟨hlS, hLS⟩ := hS fp ⟨rd0, hl0, hL0⟩
  -- the valuations agree at a call's values
  have hag : ∀ rd, LowDef κ rd → MemL rd (L fp) → ∀ s ∈ F.pre, callB s = true → ∀ v ∈ s.vals,
      F.σ rd (w fp) args v = F.σ (rdS fp) (w fp) args v := fun rd hlow hL s hs hc v hv ↦
    F.agree hl hL hLS (hbufs fp) (hrun fp rd hlow hL).2 (F.call_vals hs hc v hv)
  have hvS := (hrun fp (rdS fp) hlS hLS).1
  generalize F.σ (rdS fp) (w fp) args = σS at hag hvS
  have hmap : ∀ rd, LowDef κ rd → MemL rd (L fp) → ∀ s ∈ F.pre, callB s = true → ∀ l : List V,
      (∀ v ∈ l, v ∈ s.vals) → l.map (F.σ rd (w fp) args) = l.map σS :=
    fun rd hlow hL s hs hc l hl' ↦ List.map_congr_left fun v hv ↦ hag rd hlow hL s hs hc v (hl' v hv)
  have hagc : ∀ rd, LowDef κ rd → MemL rd (L fp) →
      ∀ c ∈ flatCalls F.pre σS, ∀ v ∈ c.args ++ c.rets, F.σ rd (w fp) args v = σS v := by
    intro rd hlow hL c hc v hv
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hc
    obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht'
    cases s with
    | call f a r =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      exact hag rd hlow hL _ hs rfl v (by simpa [Main.mkCall, Stmt.vals] using hv)
    | callIf cnd f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
      subst hst
      exact hag rd hlow hL _ hs rfl v (by simp_all [Main.mkCall, Stmt.vals])
    | dispatch x fs' a r =>
      simp only [Stmt.callSF, Option.some.injEq] at hst
      subst hst
      exact hag rd hlow hL _ hs rfl v (by simp_all [Main.mkCall, Stmt.vals])
    | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst
  refine ⟨?_, hagc rd0 hl0 hL0, fun c hc ht ↦ ?_⟩
  · unfold flatCalls
    rw [List.map_filterMap, List.map_filterMap]
    refine List.filterMap_congr fun s hs ↦ ?_
    cases s with
    | call f a r => simp only [Stmt.callSF, Main.Stmt.callS, Option.map_some, Main.mkCall]
    | callIf c f a =>
      simp only [Stmt.callSF, Main.Stmt.callS, Option.map_some, Main.mkCall]
      rw [hag rd0 hl0 hL0 _ hs rfl c (by simp [Stmt.vals])]
    | dispatch x fs' a r =>
      simp only [Stmt.callSF, Option.map_some, Main.mkCall]
      rw [hag rd0 hl0 hL0 _ hs rfl x (by simp [Stmt.vals])]
    | _ => simp only [Stmt.callSF, Main.Stmt.callS, Option.map_none]
  -- each entered callee's relation
  obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hc
  obtain ⟨s, hs, hst⟩ := List.mem_filterMap.mp ht'
  have hok := List.all_eq_true.mp F.hcall s hs
  cases s with
  | call f a r =>
    simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
    subst hst
    simp only [Main.mkCall]
    refine ⟨by simpa [callOk] using hok, fun rd hlow hL ↦ ?_⟩
    have h : coreProgram.RelIn rd (RegionL (L fp)) f (a.map (F.σ rd (w fp) args))
        (r.map (F.σ rd (w fp) args)) := (hrun fp rd hlow hL).1 _ hs
    rwa [hmap rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv]),
      hmap rd hlow hL _ hs rfl r (fun v hv ↦ by simp [Stmt.vals, hv])] at h
  | callIf cnd f a =>
    simp only [Stmt.callSF, Main.Stmt.callS, Option.some.injEq] at hst
    subst hst
    simp only [Main.mkCall, decide_eq_true_eq, List.map_nil] at ht ⊢
    refine ⟨by simpa [callOk] using hok, fun rd hlow hL ↦ ?_⟩
    have h : IsInK (F.σ rd (w fp) args cnd) ∧ (F.σ rd (w fp) args cnd ≠ 0 →
        coreProgram.RelIn rd (RegionL (L fp)) f (a.map (F.σ rd (w fp) args)) []) :=
      (hrun fp rd hlow hL).1 _ hs
    have h2 := h.2 (by rw [hag rd hlow hL _ hs rfl cnd (by simp [Stmt.vals])]; exact ht)
    rwa [hmap rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv])] at h2
  | dispatch x fs' a r =>
    simp only [Stmt.callSF, Option.some.injEq] at hst
    subst hst
    simp only [callOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
    obtain ⟨j, hj, hxj, -⟩ := hvS _ hs
    have hlog : logG (σS x) = j := by rw [hxj]; exact logG_spec (by omega)
    simp only [Main.mkCall, hlog, List.getD_eq_getElem _ _ hj]
    refine ⟨by simpa using hok.1 _ (List.getElem_mem hj), fun rd hlow hL ↦ ?_⟩
    obtain ⟨j', hj', hxj', h⟩ := ((hrun fp rd hlow hL).1 _ hs :
      ∃ (j' : ℕ) (h : j' < fs'.length), F.σ rd (w fp) args x = ofK (addressOfIndex j') ∧
        coreProgram.RelIn rd (RegionL (L fp)) fs'[j'] (a.map (F.σ rd (w fp) args))
          (r.map (F.σ rd (w fp) args)))
    have hjj : j' = j := by
      have := congrArg logG (hxj'.symm.trans ((hag rd hlow hL _ hs rfl x (by simp [Stmt.vals])).trans hxj))
      rwa [logG_spec (by omega), logG_spec (by omega)] at this
    subst hjj
    rwa [hmap rd hlow hL _ hs rfl a (fun v hv ↦ by simp [Stmt.vals, hv]),
      hmap rd hlow hL _ hs rfl r (fun v hv ↦ by simp [Stmt.vals, hv])] at h
  | _ => simp [Stmt.callSF, Main.Stmt.callS] at hst

end
end LeanVM.Guest.B1.Tables
