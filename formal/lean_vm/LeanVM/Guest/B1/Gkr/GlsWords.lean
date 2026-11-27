/-
  LeanVM.Guest.B1.Gkr.GlsWords

  `gkr_layers__L{o}`'s words, by hand (it has no words certificate: its loop's iterations cost
  with the counter): on `n_four = g^n`, `n ≤ 3`, and `rem_g = g^r`, `r < 4`, at most `glsKL`.
-/

module

public import LeanVM.Guest.B1.Gkr.GlCLayers
public import LeanVM.Guest.B1.Tables.FlatAt
public import LeanVM.Guest.B1.Tables.FlatAtT
public import LeanVM.Guest.Budget.Chain
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_last_layers__L»
import LeanVM.Guest.Data.ValNames.«gkr_layers__L»
import LeanVM.Guest.Data.ValNames.«gkr_layers__L_loop0»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»
import LeanVM.ToMathlib.List
import LeanVM.Guest.StmtsAppend

/-!
# The radix-four layers' words

Every function of `gkr_layers__L{o}`'s tree has a flat body allocating nothing (`gw_node`: its
words are its frame and its calls' bounds, a call not entered its callee's frame). With the
words of the loops `gkr_layer__L{p}_L{o}_loop0` (`Kg p o` per iteration and the run's phantom
frame, as `Count.wSKt_totalLeOn` gives them):

* `gl_totalLeOn`: `gkr_layer__L{p}_L{o}` at `x_m = g^m` within `glWB` (its loop is entered iff
  `m ≠ 0`, from `1` below `x_m`);
* `glsl_total`: `gkr_layers__L{o}`'s loop from `g^c` below `g^n` within `glsIter` per iteration
  (four layers at `x_m = g^c`) and its phantom frame;
* `glLast_totalLeOn`: `gkr_last_layers__L{r}_L{o}` at `x_m = g^n` within `glsLast`;
* `gls_totalLeOn`: `gkr_layers__L{o}` at `g^n`, `g^r` (`n ≤ 3`, `r < 4`) within `glsKL`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## The bounds -/

/-- `gkr_layer__L{p}_L{o}`'s words at `x_m = g^m`: its frame, its loop's `m` iterations and its
phantom frame. -/
def glWB (fs : String → ℕ) (Kg : ℕ → ℕ → ℕ) (p o m : ℕ) : ℕ :=
  fs (glName p o) + (fs (glLoopName p o) + m * Kg p o)

/-- The layers `p < r` at `x_m = g^m`. -/
def glWs (fs : String → ℕ) (Kg : ℕ → ℕ → ℕ) (o m r : ℕ) : ℕ :=
  ((List.range r).map fun p ↦ glWB fs Kg p o m).sum

/-- An iteration of `gkr_layers__L{o}`'s loop at `g^c`: its frame and four layers. -/
def glsIter (fs : String → ℕ) (Kg : ℕ → ℕ → ℕ) (o c : ℕ) : ℕ :=
  fs (glcLsLN o) + glWs fs Kg o c 4

/-- `gkr_last_layers__L{r}_L{o}` at `x_m = g^n`. -/
def glsLast (fs : String → ℕ) (Kg : ℕ → ℕ → ℕ) (o n r : ℕ) : ℕ :=
  fs (glcLastN r o) + glWs fs Kg o n r

/-- `gkr_layers__L{o}` at `g^n`, `g^r`: its frame, its loop's `n` iterations and phantom frame,
the last layers. -/
def glsB (fs : String → ℕ) (Kg : ℕ → ℕ → ℕ) (o n r : ℕ) : ℕ :=
  fs (glcLsN o) + (Budget.iterSum (glsIter fs Kg o) 0 n + fs (glcLsLN o)) + glsLast fs Kg o n r

/-- The largest of `glsB` over `o < 2`, `n ≤ 3`, `r < 4`. -/
def glsKL (fs : String → ℕ) (Kg : ℕ → ℕ → ℕ) : ℕ :=
  ((List.range 2).flatMap fun o ↦ (List.range 4).flatMap fun n ↦
    (List.range 4).map fun r ↦ glsB fs Kg o n r).foldl max 0

theorem glsB_le_KL (fs : String → ℕ) (Kg : ℕ → ℕ → ℕ) {o n r : ℕ} (ho : o < 2) (hn : n ≤ 3)
    (hr : r < 4) : glsB fs Kg o n r ≤ glsKL fs Kg :=
  (List.foldl_max_ge _ 0).2 _ (List.mem_flatMap.2 ⟨o, List.mem_range.2 ho, List.mem_flatMap.2
    ⟨n, List.mem_range.2 (by omega), List.mem_map.2 ⟨r, List.mem_range.2 hr, rfl⟩⟩⟩)

/-! ## A flat node -/

/-- Not a dispatch. -/
def gwNoDisp : Stmt → Bool
  | .dispatch .. => false
  | _ => true

theorem gw_callSF {σ : Val} : ∀ {l : List Stmt}, l.all gwNoDisp = true →
    l.filterMap (Stmt.callSF σ) = l.filterMap Main.Stmt.callS
  | [], _ => rfl
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have e : Stmt.callSF σ s = Main.Stmt.callS s := by
      cases s with
      | dispatch => simp [gwNoDisp] at h
      | _ => rfl
    simp only [List.filterMap_cons, e, gw_callSF h.2]

theorem gw_dispOk {σ : Val} {l : List Stmt} (h : l.all gwNoDisp = true) : ∀ s ∈ l, DispOk σ s := by
  intro s hs
  have := List.all_eq_true.mp h s hs
  cases s with
  | dispatch => simp [gwNoDisp] at this
  | _ => trivial

/-- **A body's checks**: `b` is `pre ++ [ret vr]`, `pre` flat, allocating nothing, its static calls
`cs`, each atom of `as` one of its statements. -/
noncomputable def gwChk (b : List Stmt) (vr : List V) (cs : List (Option V × String × List V × List V))
    (as : List Atom) : Bool :=
  stmtsEqb b (b.dropLast ⧺ [.ret vr]) && b.dropLast.all Stmt.flat &&
    (b.dropLast.filterMap Main.Stmt.allocSz).isEmpty &&
    decide (b.dropLast.filterMap Main.Stmt.callS = cs) &&
    as.all fun a ↦ b.dropLast.any fun t ↦ stmtsEqb [t] [.atom a]

theorem gwChk_sound {b : List Stmt} {vr : List V} {cs : List (Option V × String × List V × List V)}
    {as : List Atom} (h : gwChk b vr cs as = true) :
    b = b.dropLast ⧺ [.ret vr] ∧ b.dropLast.all Stmt.flat = true ∧
      b.dropLast.filterMap Main.Stmt.allocSz = [] ∧ b.dropLast.filterMap Main.Stmt.callS = cs ∧
      ∀ a ∈ as, Stmt.atom a ∈ b.dropLast := by
  simp only [gwChk, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨stmtsEqb_sound h1, h2, h3, h4, fun a ha ↦ ?_⟩
  obtain ⟨t, ht, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp h5 a ha)
  have := stmtsEqb_sound he
  simp only [List.cons.injEq, and_true] at this
  rwa [← this]

variable {fs : String → ℕ}

/-- A call's bound: its callee's valid trees within `w` when entered, its tail frame within `w`
when not. -/
abbrev CallW (fs : String → ℕ) (rd : Reader) (σ : Val) (c : Call) (w : ℕ) : Prop :=
  (c.taken = true → ∀ (t : Tree) (rets : List E), t.name = c.f →
    t.Valid coreProgram rd (c.args.map σ) rets → t.BufsOk coreProgram → t.total fs ≤ w) ∧
  (c.taken = false → fs (tailKey c.f) ≤ w)

theorem gw_kids_total {rd : Reader} {σ : Val} : ∀ (cs : List Call) (Ws : List ℕ) (ks : List Tree),
    Tree.KidsValid coreProgram rd σ cs ks → Tree.BufsOkKids coreProgram ks →
    List.Forall₂ (CallW fs rd σ) cs Ws → Tree.totalKids fs ks ≤ Ws.sum
  | [], [], [], _, _, _ => by simp [Tree.totalKids]
  | [], _, _ :: _, hk, _, _ => hk.elim
  | _ :: _, _, [], hk, _, _ => hk.elim
  | c :: cs, w :: Ws, k :: ks, ⟨hn, hk, hks⟩, ⟨hb, hbs⟩, .cons ⟨hT, hU⟩ hF => by
    have ih := gw_kids_total cs Ws ks hks hbs hF
    rw [Tree.totalKids, List.sum_cons]
    refine Nat.add_le_add ?_ ih
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at hk
      exact hT ht k _ hn hk hb
    · simp only [Bool.not_eq_true] at ht
      simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
      obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
      simp only [Tree.name] at hn
      subst hn
      rw [Tree.total]
      exact hU ht

/-- **A flat node's words**: on a valid node of `f`, whose body is `pre ++ [ret vr]`, `pre` flat
allocating nothing, its parameters are its arguments, `pre`'s atoms hold, and it allocates its
frame and its calls' bounds. -/
theorem gw_node {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) {pre : List Stmt}
    {vr : List V} (hbody : fn.body = pre ⧺ [.ret vr]) (hfl : pre.all Stmt.flat = true)
    (hal : pre.filterMap Main.Stmt.allocSz = []) {rd : Reader} {σ : Val} {bufs : List ℕ}
    {ks : List Tree} {args rets : List E}
    (hv : (Memory.Tree.node f σ bufs ks).Valid coreProgram rd args rets)
    (hb : (Memory.Tree.node f σ bufs ks).BufsOk coreProgram) (hd : ∀ s ∈ pre, DispOk σ s) :
    fn.params.map σ = args ∧ (∀ a, Stmt.atom a ∈ pre → a.Holds rd σ) ∧
      ∀ Ws : List ℕ, List.Forall₂ (CallW fs rd σ) (flatCalls pre σ) Ws →
        (Memory.Tree.node f σ bufs ks).total fs ≤ fs f + Ws.sum := by
  have hw0 := walk_flat σ vr pre hfl hd
  rw [← hbody] at hw0
  have hv' := hv
  obtain ⟨fn', hf', hpar, es, vs, hw, -, hes, hk⟩ := hv'
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  rw [hw0, Out.ret.injEq] at hw
  obtain ⟨rfl, -⟩ := hw
  refine ⟨hpar, fun a ha ↦ hes (.atom a) (List.mem_flatMap.mpr ⟨.atom a, ha,
    by rw [show flEvs σ (.atom a) = [.atom a] from rfl]; exact List.mem_singleton_self _⟩),
    fun Ws hW ↦ ?_⟩
  have hbufs : bufs = [] := by
    have h := hb.1
    rw [Tree.events, Tree.name, hf] at h
    simp only [Tree.val, hw0] at h
    rw [(flat_parts σ pre hfl).2.1, hal] at h
    simpa using h
  subst hbufs
  rw [(flat_parts σ pre hfl).2.2.2.1] at hk
  have := gw_kids_total _ Ws ks hk hb.2 hW
  rw [Tree.total, List.sum_nil]
  omega

theorem gw_f2_map {α β : Type} {R : α → β → Prop} {F : ℕ → α} {G : ℕ → β} :
    ∀ (l : List ℕ), (∀ p ∈ l, R (F p) (G p)) → List.Forall₂ R (l.map F) (l.map G)
  | [], _ => .nil
  | p :: l, h => .cons (h p List.mem_cons_self) (gw_f2_map l fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

/-! ## `gkr_layer__L{p}_L{o}` -/

/-- The value the loop's guard adds `x_m` to (`1`). -/
def glOne (p : ℕ) : ℕ := if p = 0 then 58 else 60 + 78 * p

/-- The loop's arguments past the start and end. -/
def glLRest (p : ℕ) : List V :=
  if p = 0 then [.n (valf% «gkr_layer» "head"), .n (valf% «gkr_layer» "point_row"), .n 62, .n (valf% «gkr_layer» "tabs")] else [.n (valf% «gkr_layer» "head"), .n (64 + 78 * p), .n (66 + 78 * p), .n (valf% «gkr_layer» "tabs")]

/-- `gkr_layer__L{p}_L{o}`'s checks: its loop call from `σ (glOne p + 2) = 1` below `x_m`, guarded
by `σ (glOne p + 1) = 1 + x_m`. -/
noncomputable def glChk (p o : ℕ) : Bool :=
  gwChk (glBody p o (glLoopName p o)) []
    [(some (.n (glOne p + 1)), glLoopName p o, .n (glOne p + 2) :: .n (valf% «gkr_layer» "x_m") :: glLRest p, [])]
    [.const (.n (glOne p)) (word 1 0), .add (.n (glOne p + 1)) (.n (glOne p)) (.n (valf% «gkr_layer» "x_m")),
      .const (.n (glOne p + 2)) (word 1 0)] &&
  (glBody p o (glLoopName p o)).dropLast.all gwNoDisp

theorem gl_chk : ∀ p < 4, ∀ o < 2, glChk p o = true := by decide +kernel

/-- **`gkr_layer__L{p}_L{o}` within `glWB` at `x_m = g^m`.** -/
theorem gl_totalLeOn {Kg : ℕ → ℕ → ℕ}
    (htk : ∀ f, fs (tailKey f) ≤ fs f)
    (hK : ∀ p < 4, ∀ o < 2, TotalLeOn coreProgram fs (glLoopName p o) LoopPre
      (fun a ↦ logG (a.getD 1 0) * Kg p o + fs (glLoopName p o)))
    {p o m : ℕ} (hp : p < 4) (ho : o < 2) (hm : m < 2 ^ 62) :
    TotalLeOn coreProgram fs (glName p o) (fun a ↦ a.getD 3 0 = gen ^ m)
      (fun _ ↦ glWB fs Kg p o m) := by
  intro rd t args rets hn h3 hv hb
  cases t with
  | phantom => exact hv.elim
  | node f σ bufs ks =>
  simp only [Tree.name] at hn
  subst hn
  obtain ⟨fn, hf, hps, hbody⟩ := glIs_sound (glIs_layers p hp o ho)
  have hc := gl_chk p hp o ho
  simp only [glChk, Bool.and_eq_true] at hc
  obtain ⟨hsplit, hfl, hal, hcs, has⟩ := gwChk_sound hc.1
  have hnd := hc.2
  obtain ⟨hpar, hat, htot⟩ := gw_node (fs := fs) hf (hbody.trans hsplit) hfl hal hv hb (gw_dispOk hnd)
  simp only [List.forall_mem_cons] at has
  obtain ⟨a1, a2, a3, -⟩ := has
  have e1 := hat _ a1
  have e2 := hat _ a2
  have e3 := hat _ a3
  simp only [Atom.Holds, word_one] at e1 e2 e3
  have h3' : σ (.n (valf% «gkr_layer» "x_m")) = gen ^ m := by
    rw [← hpar, hps] at h3
    exact h3
  have hcalls : flatCalls (glBody p o (glLoopName p o)).dropLast σ =
      [⟨glLoopName p o, .n (glOne p + 2) :: .n (valf% «gkr_layer» "x_m") :: glLRest p, [],
        decide (σ (.n (glOne p + 1)) ≠ 0)⟩] := by
    rw [flatCalls, gw_callSF hnd, hcs]; rfl
  refine (htot [fs (glLoopName p o) + m * Kg p o] ?_).trans (by simp [glWB])
  rw [hcalls]
  refine .cons ⟨fun ht t' rets' htn htv htb ↦ ?_, fun _ ↦ (htk _).trans (by simp)⟩ .nil
  simp only [decide_eq_true_eq] at ht
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; apply ht
      rw [e2, e1, h3', h0, pow_zero]; exact e_add_self 1
    · exact h0
  have := hK p hp o ho rd t' _ rets' htn (by
    simp only [List.map_cons, e3, h3']
    exact loopPre_gen hm0 (by omega) _) htv htb
  simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero, h3', gen_pow_eq_ofK,
    logG_spec (show m < 2 ^ 64 - 1 by omega)] at this
  omega

/-! ## `gkr_last_layers__L{r}_L{o}` and `gkr_layers__L{o}`'s loop -/

/-- The layer calls `p < r` of `glcChain o hd x0 c0 r`. -/
def glcCalls (o : ℕ) (hd : List V) (x0 c0 r : ℕ) : List (Option V × String × List V × List V) :=
  (List.range r).map fun p ↦ (none, glName p o, hd ++ [.n (glcXj x0 c0 p), .n 5, .n 6, .n 7, .n 8], [])

/-- `gkr_last_layers__L{r}_L{o}`'s checks. -/
noncomputable def glLastChk (r o : ℕ) : Bool :=
  gwChk (glcLastBody r o) [.n (9 + 2 * (r - 1))] (glcCalls o [.n (valf% «gkr_last_layers» "layers"), .n (valf% «gkr_last_layers» "rounds"), .n (valf% «gkr_last_layers» "gkr_pts"), .n (valf% «gkr_last_layers» "n_four")] 4 9 r) [] &&
    (glcLastBody r o).dropLast.all gwNoDisp

/-- `gkr_layers__L{o}`'s loop's checks: the four layers at `x_m = σ 0`, the guard
`σ 19 = σ 0·g + σ 1`, the next counter `σ 21 = σ 0·g`. -/
noncomputable def glslChk (o : ℕ) : Bool :=
  gwChk (glcLsLBody o) []
    (glcCalls o [.n (valf% «gkr_layers» «_loop0» "layers"), .n (valf% «gkr_layers» «_loop0» "rounds"), .n (valf% «gkr_layers» «_loop0» "gkr_pts"), .n (valf% «gkr_layers» «_loop0» "x_m")] 10 11 4 ++
      [(some (.n (valf% «gkr_layers» «_loop0» "s6#2")), glcLsLN o, [.n (valf% «gkr_layers» «_loop0» "s6#4"), .n (valf% «gkr_layers» «_loop0» "bound"), .n (valf% «gkr_layers» «_loop0» "layers"), .n (valf% «gkr_layers» «_loop0» "rounds"), .n (valf% «gkr_layers» «_loop0» "gkr_pts"), .n (valf% «gkr_layers» «_loop0» "start_g"), .n (valf% «gkr_layers» «_loop0» "g_bus_mu"), .n (valf% «gkr_layers» «_loop0» "tabs"), .n (valf% «gkr_layers» «_loop0» "stream")], [])])
    [.const (.n (valf% «gkr_layers» «_loop0» "s6#0")) (word 2 0), .mul (.n (valf% «gkr_layers» «_loop0» "s6#1")) (.n (valf% «gkr_layers» «_loop0» "x_m")) (.n (valf% «gkr_layers» «_loop0» "s6#0")), .add (.n (valf% «gkr_layers» «_loop0» "s6#2")) (.n (valf% «gkr_layers» «_loop0» "s6#1")) (.n (valf% «gkr_layers» «_loop0» "bound")),
      .const (.n (valf% «gkr_layers» «_loop0» "s6#3")) (word 2 0), .mul (.n (valf% «gkr_layers» «_loop0» "s6#4")) (.n (valf% «gkr_layers» «_loop0» "x_m")) (.n (valf% «gkr_layers» «_loop0» "s6#3"))] &&
    (glcLsLBody o).dropLast.all gwNoDisp

theorem gl_last_chk : ∀ o < 2, (∀ r < 4, glLastChk r o = true) ∧ glslChk o = true := by
  decide +kernel

/-- The layer calls' frames: each entered, `gkr_layer__L{p}_L{o}` at `x_m = σ hd[3]`. -/
theorem glc_calls_W {Kg : ℕ → ℕ → ℕ}
    (htk : ∀ f, fs (tailKey f) ≤ fs f)
    (hK : ∀ p < 4, ∀ o < 2, TotalLeOn coreProgram fs (glLoopName p o) LoopPre
      (fun a ↦ logG (a.getD 1 0) * Kg p o + fs (glLoopName p o)))
    {rd : Reader} {σ : Val} {o m r : ℕ} (ho : o < 2) (hr : r ≤ 4) (hm : m < 2 ^ 62)
    {h0 h1 h2 h3 : V} (hx : σ h3 = gen ^ m) (x0 c0 : ℕ) :
    List.Forall₂ (CallW fs rd σ) ((glcCalls o [h0, h1, h2, h3] x0 c0 r).map (Main.mkCall σ))
      ((List.range r).map fun p ↦ glWB fs Kg p o m) := by
  rw [glcCalls, List.map_map]
  refine gw_f2_map _ fun p hp ↦ ⟨fun _ t rets htn htv htb ↦ ?_, fun ht ↦ by simp [Main.mkCall] at ht⟩
  have hp4 : p < 4 := by have := List.mem_range.mp hp; omega
  exact gl_totalLeOn htk hK hp4 ho hm rd t _ rets htn (by simp [Main.mkCall, hx]) htv htb

/-- **`gkr_last_layers__L{r}_L{o}` within `glsLast` at `x_m = g^n`.** -/
theorem glLast_totalLeOn {Kg : ℕ → ℕ → ℕ}
    (htk : ∀ f, fs (tailKey f) ≤ fs f)
    (hK : ∀ p < 4, ∀ o < 2, TotalLeOn coreProgram fs (glLoopName p o) LoopPre
      (fun a ↦ logG (a.getD 1 0) * Kg p o + fs (glLoopName p o)))
    {r o n : ℕ} (hr : r < 4) (ho : o < 2) (hn : n < 2 ^ 62) :
    TotalLeOn coreProgram fs (glcLastN r o) (fun a ↦ a.getD 3 0 = gen ^ n)
      (fun _ ↦ glsLast fs Kg o n r) := by
  intro rd t args rets hnm h3 hv hb
  cases t with
  | phantom => exact hv.elim
  | node f σ bufs ks =>
  simp only [Tree.name] at hnm
  subst hnm
  obtain ⟨fn, hf, hps, hbody⟩ := glcFnCheck_sound ((glc_layers_check o ho).2.2 r hr)
  have hc := (gl_last_chk o ho).1 r hr
  simp only [glLastChk, Bool.and_eq_true] at hc
  obtain ⟨hsplit, hfl, hal, hcs, -⟩ := gwChk_sound hc.1
  have hnd := hc.2
  obtain ⟨hpar, -, htot⟩ := gw_node (fs := fs) hf (hbody.trans hsplit) hfl hal hv hb (gw_dispOk hnd)
  have h3' : σ (.n (valf% «gkr_last_layers» "n_four")) = gen ^ n := by
    rw [← hpar, hps] at h3
    exact h3
  refine (htot _ ?_).trans (le_of_eq (by rfl))
  rw [flatCalls, gw_callSF hnd, hcs]
  exact glc_calls_W htk hK ho (by omega) hn h3' 4 9

/-- **`gkr_layers__L{o}`'s loop from `g^c` below `g^n` within `glsIter` per iteration** and its
phantom frame. -/
theorem glsl_total {Kg : ℕ → ℕ → ℕ}
    (htk : ∀ f, fs (tailKey f) ≤ fs f)
    (hK : ∀ p < 4, ∀ o < 2, TotalLeOn coreProgram fs (glLoopName p o) LoopPre
      (fun a ↦ logG (a.getD 1 0) * Kg p o + fs (glLoopName p o)))
    {rd : Reader} {o n : ℕ} (ho : o < 2) (hn : n < 2 ^ 62) :
    ∀ k c (t : Tree) (args rets : List E), c + k = n → 0 < k → t.name = glcLsLN o →
      args.getD 0 0 = gen ^ c → args.getD 1 0 = gen ^ n → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → t.total fs ≤ Budget.iterSum (glsIter fs Kg o) c k + fs (glcLsLN o) := by
  obtain ⟨fn, hf, hps, hbody⟩ := glcFnCheck_sound (glc_layers_check o ho).2.1
  have hc := (gl_last_chk o ho).2
  simp only [glslChk, Bool.and_eq_true] at hc
  obtain ⟨hsplit, hfl, hal, hcs, has⟩ := gwChk_sound hc.1
  have hnd := hc.2
  intro k
  induction k with
  | zero => intro _ _ _ _ _ h; omega
  | succ k ih =>
  intro c t args rets hck _ hnm h0 h1 hv hb
  cases t with
  | phantom => exact hv.elim
  | node f σ bufs ks =>
  simp only [Tree.name] at hnm
  subst hnm
  obtain ⟨hpar, hat, htot⟩ := gw_node (fs := fs) hf (hbody.trans hsplit) hfl hal hv hb (gw_dispOk hnd)
  simp only [List.forall_mem_cons] at has
  obtain ⟨a17, a18, a19, a20, a21, -⟩ := has
  have e17 := hat _ a17
  have e18 := hat _ a18
  have e19 := hat _ a19
  have e20 := hat _ a20
  have e21 := hat _ a21
  simp only [Atom.Holds, word_gen] at e17 e18 e19 e20 e21
  have h0' : σ (.n (valf% «gkr_layers» «_loop0» "x_m")) = gen ^ c := by rw [← hpar, hps] at h0; exact h0
  have h1' : σ (.n (valf% «gkr_layers» «_loop0» "bound")) = gen ^ n := by rw [← hpar, hps] at h1; exact h1
  have e21' : σ (.n (valf% «gkr_layers» «_loop0» "s6#4")) = gen ^ (c + 1) := by rw [e21, e20, h0', pow_succ]
  have e19' : σ (.n (valf% «gkr_layers» «_loop0» "s6#2")) = gen ^ (c + 1) + gen ^ n := by rw [e19, e18, e17, h0', h1', pow_succ]
  refine (htot ((List.range 4).map (fun p ↦ glWB fs Kg p o c) ++
    [Budget.iterSum (glsIter fs Kg o) (c + 1) k + fs (glcLsLN o)]) ?_).trans ?_
  · rw [flatCalls, gw_callSF hnd, hcs, List.map_append]
    refine List.rel_append (glc_calls_W htk hK ho le_rfl (by omega) h0' 10 11) (.cons ⟨?_, ?_⟩ .nil)
    · intro ht t' rets' htn htv htb
      have ht' : σ (.n (valf% «gkr_layers» «_loop0» "s6#2")) ≠ 0 := by simpa [Main.mkCall] using ht
      have hc1 : c + 1 ≠ n := fun h ↦ ht' (by rw [e19', h]; exact e_add_self _)
      exact ih (c + 1) t' _ rets' (by omega) (by omega) htn (by simp [Main.mkCall, e21'])
        (by simp [Main.mkCall, h1']) htv htb
    · intro _; exact (htk _).trans (by simp [Main.mkCall])
  · rw [List.sum_append, Budget.iterSum_succ, glsIter, glWs]
    simp only [List.sum_cons, List.sum_nil, add_zero]
    omega

/-! ## `gkr_layers__L{o}` -/

/-- `gkr_layers__L{o}`'s statements before its `ret`. -/
theorem gls_split (o : ℕ) : glcLsBody o = (glcLsBody o).dropLast ⧺ [.ret [.n (valf% «gkr_layers» "s3#0")]] := rfl

theorem gls_flat : ∀ o < 2, (glcLsBody o).dropLast.all Stmt.flat = true := by decide +kernel

theorem gls_alloc (o : ℕ) : (glcLsBody o).dropLast.filterMap Main.Stmt.allocSz = [] := rfl

theorem gls_calls (o : ℕ) (σ : Val) : flatCalls (glcLsBody o).dropLast σ =
    [⟨glcLsLN o, [.n (valf% «gkr_layers» "s0#2"), .n (valf% «gkr_layers» "n_four"), .n (valf% «gkr_layers» "layers"), .n (valf% «gkr_layers» "rounds"), .n (valf% «gkr_layers» "gkr_pts"), .n (valf% «gkr_layers» "start_g"), .n (valf% «gkr_layers» "g_bus_mu"), .n (valf% «gkr_layers» "tabs"), .n (valf% «gkr_layers» "stream")], [], decide (σ (.n (valf% «gkr_layers» "s0#1")) ≠ 0)⟩,
      ⟨[glcLastN 0 o, glcLastN 1 o, glcLastN 2 o, glcLastN 3 o].getD (logG (σ (.n (valf% «gkr_layers» "rem_g")))) "",
        [.n (valf% «gkr_layers» "layers"), .n (valf% «gkr_layers» "rounds"), .n (valf% «gkr_layers» "gkr_pts"), .n (valf% «gkr_layers» "n_four"), .n (valf% «gkr_layers» "m4"), .n (valf% «gkr_layers» "start_g"), .n (valf% «gkr_layers» "g_bus_mu"), .n (valf% «gkr_layers» "tabs"), .n (valf% «gkr_layers» "stream")], [.n (valf% «gkr_layers» "done")], true⟩] := rfl

/-- **`gkr_layers__L{o}` within `glsKL` at `n_four = g^n`, `n ≤ 3`, and `rem_g = g^r`, `r < 4`.** -/
theorem gls_totalLeOn {Kg : ℕ → ℕ → ℕ}
    (htk : ∀ f, fs (tailKey f) ≤ fs f)
    (hK : ∀ p < 4, ∀ o < 2, TotalLeOn coreProgram fs (glLoopName p o) LoopPre
      (fun a ↦ logG (a.getD 1 0) * Kg p o + fs (glLoopName p o))) :
    ∀ o < 2, TotalLeOn coreProgram fs (glcLsN o)
      (fun a ↦ ∃ n ≤ 3, ∃ r < 4, a.getD 3 0 = gen ^ n ∧ a.getD 4 0 = gen ^ r)
      (fun _ ↦ glsKL fs Kg) := by
  intro o ho rd t args rets hnm ⟨n, hn, r, hr, h3, h4⟩ hv hb
  cases t with
  | phantom => exact hv.elim
  | node f σ bufs ks =>
  simp only [Tree.name] at hnm
  subst hnm
  obtain ⟨fn, hf, hps, hbody⟩ := glcFnCheck_sound (glc_layers_check o ho).1
  have hv' := hv
  obtain ⟨fn', hf', hpar0, -⟩ := hv'
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  have h3' : σ (.n (valf% «gkr_layers» "n_four")) = gen ^ n := by rw [← hpar0, hps] at h3; exact h3
  have h4' : σ (.n (valf% «gkr_layers» "rem_g")) = gen ^ r := by rw [← hpar0, hps] at h4; exact h4
  have e : (glcLsBody o).dropLast = [.atom (.const (.n (valf% «gkr_layers» "s0#0")) (word 1 0)),
      .atom (.add (.n (valf% «gkr_layers» "s0#1")) (.n (valf% «gkr_layers» "s0#0")) (.n (valf% «gkr_layers» "n_four"))), .atom (.const (.n (valf% «gkr_layers» "s0#2")) (word 1 0)),
      .callIf (.n (valf% «gkr_layers» "s0#1")) (glcLsLN o) [.n (valf% «gkr_layers» "s0#2"), .n (valf% «gkr_layers» "n_four"), .n (valf% «gkr_layers» "layers"), .n (valf% «gkr_layers» "rounds"), .n (valf% «gkr_layers» "gkr_pts"), .n (valf% «gkr_layers» "start_g"), .n (valf% «gkr_layers» "g_bus_mu"), .n (valf% «gkr_layers» "tabs"), .n (valf% «gkr_layers» "stream")],
      .atom (.mul (.n (valf% «gkr_layers» "m4~0")) (.n (valf% «gkr_layers» "n_four")) (.n (valf% «gkr_layers» "n_four"))), .atom (.mul (.n (valf% «gkr_layers» "m4")) (.n (valf% «gkr_layers» "m4~0")) (.n (valf% «gkr_layers» "m4~0"))),
      .dispatch (.n (valf% «gkr_layers» "rem_g")) [glcLastN 0 o, glcLastN 1 o, glcLastN 2 o, glcLastN 3 o]
        [.n (valf% «gkr_layers» "layers"), .n (valf% «gkr_layers» "rounds"), .n (valf% «gkr_layers» "gkr_pts"), .n (valf% «gkr_layers» "n_four"), .n (valf% «gkr_layers» "m4"), .n (valf% «gkr_layers» "start_g"), .n (valf% «gkr_layers» "g_bus_mu"), .n (valf% «gkr_layers» "tabs"), .n (valf% «gkr_layers» "stream")] [.n (valf% «gkr_layers» "done")],
      .atom (.const (.n (valf% «gkr_layers» "s3#0")) (word 0 0))] := rfl
  have hd : ∀ s ∈ (glcLsBody o).dropLast, DispOk σ s := by
    intro s hs
    rw [e] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try trivial
    exact ⟨r, by simp only [List.length_cons, List.length_nil]; omega, by omega,
      by rw [h4', gen_pow_eq_ofK]⟩
  obtain ⟨-, hat, htot⟩ := gw_node (fs := fs) hf (hbody.trans (gls_split o))
    (gls_flat o ho) (gls_alloc o) hv hb hd
  have e9 := hat (.const (.n (valf% «gkr_layers» "s0#0")) (word 1 0)) (by rw [e]; simp)
  have e10 := hat (.add (.n (valf% «gkr_layers» "s0#1")) (.n (valf% «gkr_layers» "s0#0")) (.n (valf% «gkr_layers» "n_four"))) (by rw [e]; simp)
  have e11 := hat (.const (.n (valf% «gkr_layers» "s0#2")) (word 1 0)) (by rw [e]; simp)
  simp only [Atom.Holds, word_one] at e9 e10 e11
  have hlog : logG (σ (.n (valf% «gkr_layers» "rem_g"))) = r := by rw [h4', gen_pow_eq_ofK, logG_spec (by omega)]
  have hlast : [glcLastN 0 o, glcLastN 1 o, glcLastN 2 o, glcLastN 3 o].getD r "" = glcLastN r o := by
    interval_cases r <;> rfl
  have hB : fs (glcLsN o) + [Budget.iterSum (glsIter fs Kg o) 0 n + fs (glcLsLN o),
      glsLast fs Kg o n r].sum ≤ glsKL fs Kg := by
    have := glsB_le_KL fs Kg ho hn hr
    simp only [glsB, List.sum_cons, List.sum_nil, add_zero] at this ⊢
    omega
  refine (htot [Budget.iterSum (glsIter fs Kg o) 0 n + fs (glcLsLN o), glsLast fs Kg o n r] ?_).trans hB
  rw [gls_calls]
  refine .cons ⟨fun ht t' rets' htn htv htb ↦ ?_, fun _ ↦ (htk _).trans (by simp)⟩
    (.cons ⟨fun _ t' rets' htn htv htb ↦ ?_, fun ht ↦ by simp at ht⟩ .nil)
  · simp only [decide_eq_true_eq] at ht
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · exfalso; apply ht
        rw [e10, e9, h3', h0, pow_zero]; exact e_add_self 1
      · exact h0
    exact glsl_total (rd := rd) (n := n) htk hK ho (by omega) n 0 t' _ rets' (by omega) hn0 htn
      (by simp [e11]) (by simp [h3']) htv htb
  · have htn' : t'.name = glcLastN r o := by
      rw [htn]
      show [glcLastN 0 o, glcLastN 1 o, glcLastN 2 o, glcLastN 3 o].getD (logG (σ (.n (valf% «gkr_layers» "rem_g")))) "" = _
      rw [hlog, hlast]
    exact glLast_totalLeOn htk hK hr ho (by omega) rd t' _ rets' htn' (by simp [h3']) htv htb

end
end LeanVM.Guest.B1.Tables
