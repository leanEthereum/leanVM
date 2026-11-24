/-
  LeanVM.Guest.B1.Tables.FlatLiftT

  A flat function evaluated forward, placed by a tree of honest shape (`Budget.NodeHonest`).
-/

module

public import LeanVM.Guest.B1.Tables.FlatLift
public import LeanVM.Guest.Budget.Strengthen
public import LeanVM.Guest.Budget.LiftB

/-!
# Flat functions, placed, by a tree of honest shape

`flat_completeAtTBR`: `F` complete (`FlatLift`) by a tree `NodeHonest F.name (Q rd) (flatCalls F.pre)
(fun _ ↦ sizes) Ts` when the honest valuation satisfies `Q rd` on every memory `rd` holding the layout,
`Ts` covers the body's calls, and the predicate `Ts[i]` holds of every valid tree of call `i`'s
callee at its honest arguments, on every memory defined below `2^κ` holding the layout
(the callee's `Lift.completeAtD_of_relIn`). `flat_completeAtOutTB`: the function's buffers returned.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem flatCalls_length (pre : List Stmt) (σ : Val) :
    (flatCalls pre σ).length = (pre.filter callB).length := by
  unfold flatCalls
  rw [List.length_map]
  induction pre with
  | nil => rfl
  | cons s ss ih =>
    cases s <;> simp [List.filterMap_cons, List.filter_cons, Stmt.callSF, Main.Stmt.callS, callB, ih]

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- The callees' words, call by call: an entered call's bound, another's tail. -/
def callsBound (fs : String → ℕ) : List Call → List ℕ → ℕ
  | c :: cs, Bs => (if c.taken then Bs.headD 0 else fs (tailKey c.f)) + callsBound fs cs Bs.tail
  | [], _ => 0

theorem kidsBoundL_map {σS : Val} {L : Layout} :
    ∀ (cs : List Call) (Bs : List ℕ), kidsBoundL fs (cs.map (kidOf σS L)) Bs = callsBound fs cs Bs
  | [], _ => rfl
  | c :: cs, Bs => by
    simp only [List.map_cons, kidsBoundL, callsBound, kidsBoundL_map cs Bs.tail]
    rfl

/-- The tails of a body's conditional calls (the only calls a walk may skip). -/
def ifFrames (fs : String → ℕ) (pre : List Stmt) : ℕ :=
  (pre.filterMap fun s ↦ match s with
    | .callIf _ f _ => some (fs (tailKey f))
    | _ => none).sum

theorem sum_eq_headD_tail (Bs : List ℕ) : Bs.sum = Bs.headD 0 + Bs.tail.sum := by
  cases Bs <;> simp

/-- **The callees' words of a flat body are at most the bounds and the skipped tails.** -/
theorem callsBound_le (pre : List Stmt) (σ : Val) :
    ∀ Bs : List ℕ, callsBound fs (flatCalls pre σ) Bs ≤ Bs.sum + ifFrames fs pre := by
  induction pre with
  | nil => intro Bs; simp [flatCalls, callsBound]
  | cons s ss ih =>
    intro Bs
    cases s with
    | call f a r =>
      have := ih Bs.tail
      simp only [flatCalls, List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, List.map_cons,
        callsBound, Main.mkCall, ↓reduceIte, ifFrames] at this ⊢
      rw [sum_eq_headD_tail Bs]; omega
    | callIf c f a =>
      have := ih Bs.tail
      simp only [flatCalls, List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, List.map_cons,
        callsBound, Main.mkCall, ifFrames, List.sum_cons] at this ⊢
      rw [sum_eq_headD_tail Bs]
      split <;> omega
    | dispatch x fs' a r =>
      have := ih Bs.tail
      simp only [flatCalls, List.filterMap_cons, Stmt.callSF, List.map_cons,
        callsBound, Main.mkCall, ↓reduceIte, ifFrames] at this ⊢
      rw [sum_eq_headD_tail Bs]; omega
    | _ =>
      have := ih Bs
      simpa [flatCalls, List.filterMap_cons, Stmt.callSF, Main.Stmt.callS, ifFrames] using this

theorem kidsDTB_of_getElem {κ : ℕ} {σS : Val} {L : Layout} :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)) (Bs : List ℕ),
      (∀ i (c : Call), cs[i]? = some c → c.taken = true →
        CompleteAtDTB fs cert κ c.f L (c.args.map σS) (Returns (c.rets.map σS))
          (Ts.getD i fun _ ↦ True) (Bs.getD i 0)) →
      KidsDTB fs cert κ (cs.map (kidOf σS L)) Ts Bs
  | [], _, _, _ => trivial
  | c :: cs, Ts, Bs, h => by
    refine ⟨fun ht ↦ ?_, kidsDTB_of_getElem cs Ts.tail Bs.tail fun i c' hc ht ↦ ?_⟩
    · have := h 0 c rfl ht
      cases Ts <;> cases Bs <;> exact this
    · have := h (i + 1) c' (by simpa using hc) ht
      cases Ts <;> cases Bs <;> simpa using this

/-- `completeAtDTB_of_relIn` with the callee's words bounded on the memories it runs on only:
defined below `2^κ` and holding `Lin` (its tree is built on `lowLin rd1 κ Lin`). -/
theorem completeAtDTB_of_relIn_on {S : List String} (hS : coreProgram.PureIn S) {g : String}
    (hg : g ∈ S) {κ : ℕ} {Lin : Layout} {args rets : List E} {B : ℕ}
    (hB : ∀ rd, LowDef κ rd → MemL rd Lin → ∀ (t : Tree) (rets' : List E), t.name = g →
      t.Valid coreProgram rd args rets' → t.BufsOk coreProgram → t.total fs ≤ B)
    (h : ∀ rd, LowDef κ rd → MemL rd Lin → coreProgram.RelIn rd (RegionL Lin) g args rets) :
    CompleteAtDTB fs cert κ g Lin args (Returns rets) (fun _ => True) B := by
  intro fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], Nat.zero_le _, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨t, hn, hv, hb, hlr⟩ := h _ (Lift.lowLin_low (Lin := Lin) hl1) (Lift.lowLin_memL hL1)
  refine ⟨t.total fs, [], rets, [], hB _ (Lift.lowLin_low (Lin := Lin) hl1) (Lift.lowLin_memL hL1)
    t rets hn hv hb, ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  have hr := relAtIn_transfer (fs := fs) (cert := cert) (D := fun _ => False) (fp := fp)
    coreProgram_fresh hn hv hb (placed_of_pure hS t hv hb (hn ▸ hg) _)
    (loadsIn_of_loadsR t _ _ hlr) (fun _ h => h.elim) rd
    (fun i hi => hi.elim (fun hi => ?_) fun hd => (not_data_of_pure hS t hv hb (hn ▸ hg) _ i hd).elim)
    (fun A hA => ?_)
  · refine (relAtIn_dmono hr fun i hi => ?_).relAtInT
    obtain ⟨q, hq, _⟩ := hi; simp at hq
  · rw [Lift.lowLin, B1.Main.restrict_of ⟨i, rfl, Or.inl hi⟩, B1.Main.memL_agree hL' hL1 i hi]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi | hi⟩ := B1.Main.restrict_supp' rd1 _ _ _ hv
    · rw [B1.Main.memL_agree hL' hL1 i hi, ← B1.Main.restrict_of (rd := rd1)
        (S := fun i => RegionL Lin i ∨ i < 2 ^ κ) ⟨i, rfl, Or.inl hi⟩]
      exact Option.isSome_iff_exists.mpr ⟨v, hv⟩
    · exact hl i hi

/-- **The entered callees of fixed calls are complete, placed, by trees satisfying `Ts` within
the bounds `Bs`**, when every valid tree of call `i`'s callee at its honest arguments, on every
memory holding the layout, satisfies `Ts[i]` and is within `Bs[i]`. -/
theorem FlatFn.kidsDTB (F : FlatFn) {κ : ℕ} {args : List E} {L : ℕ → Layout} {w : ℕ → ℕ → E}
    {σS : ℕ → Val}
    (hS : ∀ fp rd, LowDef κ rd → MemL rd (L fp) →
      flatCalls F.pre (F.σ rd (w fp) args) = flatCalls F.pre (σS fp) ∧
      (∀ c ∈ flatCalls F.pre (σS fp), ∀ v ∈ c.args ++ c.rets, F.σ rd (w fp) args v = σS fp v) ∧
      ∀ c ∈ flatCalls F.pre (σS fp), c.taken = true → c.f ∈ F.kids ∧
        ∀ rd', LowDef κ rd' → MemL rd' (L fp) →
          coreProgram.RelIn rd' (RegionL (L fp)) c.f (c.args.map (σS fp)) (c.rets.map (σS fp)))
    (Ts : List (Tree → Prop)) (Bs : List ℕ)
    (hT : ∀ fp rd, LowDef κ rd → MemL rd (L fp) → ∀ i (c : Call),
      (flatCalls F.pre (F.σ rd (w fp) args))[i]? = some c → c.taken = true →
      ∀ (t : Tree) (r : List E), t.name = c.f →
        t.Valid coreProgram rd (c.args.map (F.σ rd (w fp) args)) r → t.BufsOk coreProgram →
        (Ts.getD i fun _ ↦ True) t)
    (hB : ∀ fp rd, LowDef κ rd → MemL rd (L fp) → ∀ i (c : Call),
      (flatCalls F.pre (F.σ rd (w fp) args))[i]? = some c → c.taken = true →
      ∀ rd', LowDef κ rd' → MemL rd' (L fp) → ∀ (t : Tree) (r : List E), t.name = c.f →
        t.Valid coreProgram rd' (c.args.map (F.σ rd (w fp) args)) r → t.BufsOk coreProgram →
        t.total fs ≤ Bs.getD i 0) :
    ∀ fp, KidsDTB fs cert κ ((flatCalls F.pre (σS fp)).map (kidOf (σS fp) (L fp))) Ts Bs := by
  intro fp
  refine kidsDTB_of_getElem _ Ts Bs fun i c hc ht ↦ ?_
  by_cases hex : ∃ rd, LowDef κ rd ∧ MemL rd (L fp)
  swap
  · intro fp'
    exact ⟨0, [], c.rets.map (σS fp), [], Nat.zero_le _, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hlow hL ↦ absurd ⟨rd, hlow, by simpa using hL⟩ hex⟩
  obtain ⟨rd0, hl0, hL0⟩ := hex
  have hcm : c ∈ flatCalls F.pre (σS fp) := List.mem_of_getElem? hc
  obtain ⟨hmem, hrel⟩ := (hS fp rd0 hl0 hL0).2.2 c hcm ht
  -- on each memory, the call is the `i`-th, at the same arguments
  have hc' : ∀ rd, LowDef κ rd → MemL rd (L fp) → (flatCalls F.pre (F.σ rd (w fp) args))[i]? = some c :=
    fun rd hlow hL ↦ by rw [(hS fp rd hlow hL).1]; exact hc
  have ha : ∀ rd, LowDef κ rd → MemL rd (L fp) →
      c.args.map (σS fp) = c.args.map (F.σ rd (w fp) args) := fun rd hlow hL ↦
    List.map_congr_left fun v hv ↦ ((hS fp rd hlow hL).2.1 c hcm v (List.mem_append_left _ hv)).symm
  have hBi : ∀ rd', LowDef κ rd' → MemL rd' (L fp) → ∀ (t : Tree) (r : List E), t.name = c.f →
      t.Valid coreProgram rd' (c.args.map (σS fp)) r → t.BufsOk coreProgram →
      t.total fs ≤ Bs.getD i 0 := by
    intro rd' hl' hL' t r hn hv hbo
    rw [ha rd0 hl0 hL0] at hv
    exact hB fp rd0 hl0 hL0 i c (hc' rd0 hl0 hL0) ht rd' hl' hL' t r hn hv hbo
  refine ((completeAtDTB_of_relIn_on F.hpure hmem hBi hrel).and_valid_on
    fun rd hlow hL t r hn hv hbo ↦ ?_).mono le_rfl fun t h ↦ h.2
  rw [ha rd hlow hL] at hv
  exact hT fp rd hlow hL i c (hc' rd hlow hL) ht t r hn hv hbo

set_option maxRecDepth 20000 in
/-- **A flat function is complete, placed, by a tree of honest shape, within its frame, its
buffers and its callees' bounds**, its valuation satisfying `Q rd` on each memory `rd`. -/
theorem flat_completeAtTBR (F : FlatFn) {κ : ℕ} (Lin : Layout) (args rets : List E)
    (hl : args.length = F.k)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
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
      F.rets.map (F.σ rd (w fp) args) = rets)
    (Q : Reader → Val → Prop) (Ts : List (Tree → Prop))
    (hQ : ∀ fp rd, LowDef κ rd → MemL rd (flatL F.name Lin sizes own fs fp) →
      Q rd (F.σ rd (w fp) args))
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
    CompleteAtDTBR fs cert κ F.name Lin args (Returns rets)
      (fun rd ↦ Budget.NodeHonest coreProgram F.name (Q rd) (flatCalls F.pre) (fun _ ↦ sizes) Ts)
      (fs F.name + sizes.sum + KB) := by
  obtain ⟨σS, hS⟩ := F.fixCalls hl (flatL F.name Lin sizes own fs) w bufs hbufs
    fun fp rd hlow hL ↦ ⟨(hrun fp rd hlow hL).1, (hrun fp rd hlow hL).2.1⟩
  refine completeAt_flatDTBR F.hf F.hloop κ Lin args rets F.hb F.hflat F.haddrs sizes own hown
    (fun fp ↦ (flatCalls F.pre (σS fp)).map (kidOf (σS fp) (flatL F.name Lin sizes own fs fp)))
    Q Ts Bs KB (F.kidsDTB hS Ts Bs hT hB) (fun fp ↦ by rw [kidsBoundL_map]; exact hKB (σS fp))
    (fun fp ↦ by rw [List.length_map, flatCalls_length]; exact hTl) (fun _ _ hk _ _ ↦ kidOf_region hk)
    (fun _ _ hBuf hLin _ hk ↦ kidOf_memL hk hLin hBuf) fun fp outs ho rd hlow hBuf hLin ↦ ?_
  have hL : MemL rd (flatL F.name Lin sizes own fs fp) := Main.memL_append.mpr ⟨hLin, hBuf⟩
  obtain ⟨hv, hld, hsz, hbs, hrt⟩ := hrun fp rd hlow hL
  obtain ⟨hcs, hag, -⟩ := hS fp rd hlow hL
  obtain ⟨hp, hdo, hh⟩ := F.holds hl hv hrt
  refine ⟨_, hp, hdo, hh, hsz, hbs, ?_, F.loads_in (hbufs fp) hld, hQ fp rd hlow hL⟩
  rw [hcs]
  exact callsMatch_kids _ outs hag ho

set_option maxRecDepth 20000 in
/-- **`flat_completeAtTBR` returning its buffers**, `Q` a property of the valuation only: the
returns `rets fp` at the frame pointer `fp`, the function's buffers its returned layout, of which
`Res` holds. -/
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
  obtain ⟨σS, hS⟩ := F.fixCalls hl (flatL F.name Lin sizes own fs) w bufs hbufs
    fun fp rd hlow hL ↦ ⟨(hrun fp rd hlow hL).1, (hrun fp rd hlow hL).2.1⟩
  refine completeAt_flatOutDTB F.hf F.hloop κ Lin args rets Res F.hb F.hflat F.haddrs sizes own hown hout
    (fun fp ↦ (flatCalls F.pre (σS fp)).map (kidOf (σS fp) (flatL F.name Lin sizes own fs fp)))
    Q Ts Bs KB (F.kidsDTB hS Ts Bs hT hB) (fun fp ↦ by rw [kidsBoundL_map]; exact hKB (σS fp))
    (fun fp ↦ by rw [List.length_map, flatCalls_length]; exact hTl) (fun _ _ hk _ _ ↦ kidOf_region hk)
    (fun _ _ hBuf hLin _ hk ↦ kidOf_memL hk hLin hBuf) fun fp outs ho rd hlow hBuf hLin ↦ ?_
  have hL : MemL rd (flatL F.name Lin sizes own fs fp) := Main.memL_append.mpr ⟨hLin, hBuf⟩
  obtain ⟨hv, hld, hsz, hbs, hrt⟩ := hrun fp rd hlow hL
  obtain ⟨hcs, hag, -⟩ := hS fp rd hlow hL
  obtain ⟨hp, hdo, hh⟩ := F.holds hl hv hrt
  refine ⟨_, hp, hdo, hh, hsz, hbs, ?_, F.loads_in (hbufs fp) hld, hQ fp rd hlow hL⟩
  rw [hcs]
  exact callsMatch_kids _ outs hag ho

end
end LeanVM.Guest.B1.Tables
