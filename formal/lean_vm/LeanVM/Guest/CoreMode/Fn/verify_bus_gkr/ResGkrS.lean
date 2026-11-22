/-
  LeanVM.Guest.CoreMode.Fn.verify_bus_gkr.ResGkrS

  The facts about `verify_bus_gkr`'s radix-four layers' code that the core route's cursor families
  (`ResGkrQ`, `ResGkrL`) carry down: their callers and call sites, the dispatch on the depth's parity,
  and the slots' cursors along the layers.
-/

module

public import LeanVM.Guest.CoreMode.Fam.Down
public import LeanVM.Guest.CoreMode.Fam.LoopDefs
public import LeanVM.Guest.B1.Gkr.Holds
public import LeanVM.Guest.B1.Gkr.GlCurs
public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.CoreMode.Gen.GlCallers
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_last_layers__L»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L_loop0»
import LeanVM.Guest.Data.ValNames.«gkr_layers__L»
import LeanVM.Guest.Data.ValNames.«gkr_layers__L_loop0»
import LeanVM.Guest.Data.ValNames.«verify_bus_gkr»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»

/-!
# The radix-four layers' code

* `gl_callers_mem`, `gl_caller`: each gkr callee's callers (`Res.glCallers_all`); `gl_loopsB`: which are
  loops; `gl_sites`, `vbg_ls_sites`: their call sites' arguments;
* `walk_disp_sel`: a call of a dispatch's callee, named nowhere else in the body, is the arm its
  selector picks (`verify_bus_gkr`'s on the depth's parity, `vbg_split`);
* `vbg_ls`: `verify_bus_gkr`'s tables and root slot, its cursor `14` or `8` words past the frame's;
* `gl_next`, `gl_slots`, `glsl_run`: a layer's call moves its slot's cursor `4L + 12` words on to the next
  slot (`B1.Tables.gl_curs`), so `140` at most a layer.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Tables
open LeanVM.Guest.Value (gen_pow_eq_ofK e_add_eq_zero_iff e_add_self gen_pow_inj)
open LeanVM.Guest.B2C (idxOf fsN cellJ siteOf)
open LeanVM.Guest.Res (topAtoms)
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `gkr_layers__L{o}`'s call arguments in `verify_bus_gkr`. -/
def vbgLsArgs : List V := [val% «verify_bus_gkr» "layers", val% «verify_bus_gkr» "rounds", val% «verify_bus_gkr» "gkr_pts", val% «verify_bus_gkr» "n_four", val% «verify_bus_gkr» "rem_g", val% «verify_bus_gkr» "start_g", val% «verify_bus_gkr» "g_bus_mu", val% «verify_bus_gkr» "tabs", val% «verify_bus_gkr» "stream"].map .n

/-- `gkr_layers__L{o}`'s loop's arguments to `gkr_layer__L{p}_L{o}`. -/
def glLsLArgs (p : ℕ) : List V := [.n (valf% «gkr_layers» «_loop0» "layers"), .n (valf% «gkr_layers» «_loop0» "rounds"), .n (valf% «gkr_layers» «_loop0» "gkr_pts"), .n (valf% «gkr_layers» «_loop0» "x_m"), .n (glcXj 10 11 p), .n (valf% «gkr_layers» «_loop0» "start_g"), .n (valf% «gkr_layers» «_loop0» "g_bus_mu"), .n (valf% «gkr_layers» «_loop0» "tabs"), .n (valf% «gkr_layers» «_loop0» "stream")]

/-- `gkr_last_layers`' arguments to `gkr_layer__L{p}_L{o}`. -/
def glLastArgs (p : ℕ) : List V := [.n (valf% «gkr_last_layers» "layers"), .n (valf% «gkr_last_layers» "rounds"), .n (valf% «gkr_last_layers» "gkr_pts"), .n (valf% «gkr_last_layers» "n_four"), .n (glcXj 4 9 p), .n (valf% «gkr_last_layers» "start_g"), .n (valf% «gkr_last_layers» "g_bus_mu"), .n (valf% «gkr_last_layers» "tabs"), .n (valf% «gkr_last_layers» "stream")]

/-- A function, if any, is no loop. -/
noncomputable def notLoopB (f : String) : Bool := (coreProgram.find? f).all fun fn ↦ !fn.loop

/-- A loop helper ending at its second parameter, which calls itself only by its tail. -/
noncomputable def loopB (f : String) : Bool :=
  (coreProgram.find? f).all fun fn ↦
    fn.loop && Res.endOfFn fn == some none && !(Stmt.blockCallees (loopBody fn)).contains f

/-- The loop's counter's argument in the layer: the constant `1`. -/
def glA0 (p : ℕ) : ℕ := if p = 0 then 60 else 62 + 78 * p

/-- The loop's call arguments in the layer. -/
def glLoopArgs (p : ℕ) : List V :=
  if p = 0 then [.n 60, .n (valf% «gkr_layer» "x_m"), .n (valf% «gkr_layer» "head"), .n (valf% «gkr_layer» "point_row"), .n 62, .n (valf% «gkr_layer» "tabs")]
  else [.n (62 + 78 * p), .n (valf% «gkr_layer» "x_m"), .n (valf% «gkr_layer» "head"), .n (64 + 78 * p), .n (66 + 78 * p), .n (valf% «gkr_layer» "tabs")]

/-- `gkr_layer__L{p}_L{o}`'s index. -/
def glIdx : ℕ → ℕ → ℕ
  | 0, 0 => fn_idx% «gkr_layer__L0_L0»
  | 1, 0 => fn_idx% «gkr_layer__L1_L0»
  | 2, 0 => fn_idx% «gkr_layer__L2_L0»
  | 3, 0 => fn_idx% «gkr_layer__L3_L0»
  | 0, _ => fn_idx% «gkr_layer__L0_L1»
  | 1, _ => fn_idx% «gkr_layer__L1_L1»
  | 2, _ => fn_idx% «gkr_layer__L2_L1»
  | _, _ => fn_idx% «gkr_layer__L3_L1»

end

public section

theorem glLoopArgs_eq (p : ℕ) : ∃ rest, glLoopArgs p = .n (glA0 p) :: .n (valf% «gkr_layer» "x_m") :: .n (valf% «gkr_layer» "head") :: rest := by
  by_cases h : p = 0
  · exact ⟨[.n (valf% «gkr_layer» "point_row"), .n 62, .n (valf% «gkr_layer» "tabs")], by simp [glLoopArgs, glA0, h]⟩
  · exact ⟨[.n (64 + 78 * p), .n (66 + 78 * p), .n (valf% «gkr_layer» "tabs")], by simp [glLoopArgs, glA0, h]⟩

theorem glLoopParams_eq : glLoopParams = [.n (valf% «gkr_layer» «_loop0» "y"), .n (valf% «gkr_layer» «_loop0» "bound"), .n (valf% «gkr_layer» «_loop0» "head"), .n (valf% «gkr_layer» «_loop0» "qrow"), .n (valf% «gkr_layer» «_loop0» "nqrow"), .n (valf% «gkr_layer» «_loop0» "tabs")] := rfl

/-- **The layer's index, its stream's cell and its loop's site.** -/
theorem gl_idx : ∀ p < 4, ∀ o < 2, idxOf (glName p o) = some (glIdx p o) ∧ cellJ (glIdx p o) (.n (valf% «gkr_layer» "stream")) = 10 ∧
    10 < fsN (glIdx p o) ∧ (siteOf (glIdx p o) ⟨glLoopName p o, glLoopArgs p, [], true⟩).isSome = true := by
  decide +kernel

/-- **The layer calls its loop only at its site**, its counter the constant `1`. -/
theorem gl_loop_sites : ∀ p < 4, ∀ o < 2,
    Res.sitesB (fun f args rets ↦ f != glLoopName p o || (args == glLoopArgs p && rets == []))
      (glBody p o (glLoopName p o)) = true ∧
    (topAtoms (glBody p o (glLoopName p o))).contains (.const (.n (glA0 p)) (word 1 0)) = true := by
  decide +kernel

/-- The loop's atoms the cursor moves through. -/
theorem gll_atoms : ∀ p < 4, ∀ o < 2,
    [Atom.mul (.n (valf% «gkr_layer» «_loop0» "rd")) (.n (valf% «gkr_layer» «_loop0» "head")) (.n (valf% «gkr_layer» «_loop0» "y")), .load (.n (valf% «gkr_layer» «_loop0» "cur")) (.n (valf% «gkr_layer» «_loop0» "rd")) 4310, .const (.n (valf% «gkr_layer» «_loop0» "s12#0")) (word (2 ^ 32) 0),
      .mul (.n (valf% «gkr_layer» «_loop0» "s12#1")) (.n (valf% «gkr_layer» «_loop0» "cur")) (.n (valf% «gkr_layer» «_loop0» "s12#0")), .load (.n (valf% «gkr_layer» «_loop0» "s12#1")) (.n (valf% «gkr_layer» «_loop0» "rd")) 4311].all
      (topAtoms (glLoopBody (glLoopName p o))).contains = true := by
  decide +kernel

theorem find_vbg : coreProgram.find? name% «verify_bus_gkr» = some fn% «verify_bus_gkr» :=
  coreProgram_find?_at (j := idx% «verify_bus_gkr») rfl

theorem vbg_params : (fn% «verify_bus_gkr»).params = [.n (val% «verify_bus_gkr» "fs0"), .n (val% «verify_bus_gkr» "fs1"), .n (val% «verify_bus_gkr» "fs2"), .n (val% «verify_bus_gkr» "fs3"), .n (val% «verify_bus_gkr» "fs4"), .n (val% «verify_bus_gkr» "cursor@1"), .n (val% «verify_bus_gkr» "g_bus_mu"), .n (val% «verify_bus_gkr» "zeta"), .n (val% «verify_bus_gkr» "tabs"), .n (val% «verify_bus_gkr» "stream")] :=
  rfl

theorem vbg_body : (fn% «verify_bus_gkr»).body = vbgPre ++ [.ret vbgRets] := by
  obtain ⟨fn, hf, -, hb⟩ := vbgFound
  rw [Option.some.inj (find_vbg.symm.trans hf)]; exact hb

theorem vbg_not_loop : (fn% «verify_bus_gkr»).loop = false := by decide +kernel

/-- **`verify_bus_gkr` calls `gkr_layers__L{o}` only at `vbgLsArgs`.** -/
theorem vbg_ls_sites : Res.sitesB (fun f args _ ↦ !([glcLsN 0, glcLsN 1].contains f) || args == vbgLsArgs)
    (fn% «verify_bus_gkr»).body = true := by
  decide +kernel

/-- `verify_bus_gkr`'s body around its dispatch on the depth's parity. -/
theorem vbg_split : (fn% «verify_bus_gkr»).body = (fn% «verify_bus_gkr»).body.take (pos% «verify_bus_gkr» "s30#0") ++
    .dispatch (.n (val% «verify_bus_gkr» "odd_g")) [glcLsN 0, glcLsN 1] vbgLsArgs [.n (val% «verify_bus_gkr» "done")] :: (fn% «verify_bus_gkr»).body.drop (pos% «verify_bus_gkr» "s31#0") := by
  have h : tbStmtsEqb ((fn% «verify_bus_gkr»).body.drop (pos% «verify_bus_gkr» "s30#0"))
      (.dispatch (.n (val% «verify_bus_gkr» "odd_g")) [glcLsN 0, glcLsN 1] vbgLsArgs [.n (val% «verify_bus_gkr» "done")] :: (fn% «verify_bus_gkr»).body.drop (pos% «verify_bus_gkr» "s31#0")) =
        true := by
    decide +kernel
  conv_lhs => rw [← List.take_append_drop 259 (fn% «verify_bus_gkr»).body]
  rw [tbStmtsEqb_sound h]

/-- Around the dispatch, `verify_bus_gkr` calls no `gkr_layers__L{o}`. -/
theorem vbg_split_sites :
    Res.sitesB (fun f _ _ ↦ !([glcLsN 0, glcLsN 1].contains f)) ((fn% «verify_bus_gkr»).body.take (pos% «verify_bus_gkr» "s30#0")) = true ∧
      Res.sitesB (fun f _ _ ↦ !([glcLsN 0, glcLsN 1].contains f)) ((fn% «verify_bus_gkr»).body.drop (pos% «verify_bus_gkr» "s31#0")) =
        true := by
  decide +kernel

/-- **The gkr callees' callers** (`Res.glCallers`). -/
theorem gl_callers_mem :
    (∀ o < 2, Res.glCallers.lookup (glcLsN o) = some [name% «verify_bus_gkr»] ∧
      Res.glCallers.lookup (glcLsLN o) = some [glcLsN o] ∧
      ∀ rr < 4, Res.glCallers.lookup (glcLastN rr o) = some [glcLsN o]) ∧
    ∀ p < 4, ∀ o < 2,
      Res.glCallers.lookup (glName p o) =
          some (glcLsLN o :: ((List.range 4).filter fun rr ↦ decide (p < rr)).map (glcLastN · o)) ∧
        Res.glCallers.lookup (glLoopName p o) = some [glName p o] := by
  decide +kernel

theorem lookup_mem' {a : String} {b : List String} :
    ∀ {l : List (String × List String)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by simp at h
  | (a', b') :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i he
      simp only [Option.some.injEq] at h
      subst h
      obtain rfl : a = a' := by simpa using he
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem' h)

/-- **Which of them are loops.** -/
theorem gl_loopsB :
    (∀ o < 2, notLoopB (glcLsN o) = true ∧ loopB (glcLsLN o) = true ∧ ∀ rr < 4, notLoopB (glcLastN rr o) = true) ∧
      ∀ p < 4, ∀ o < 2, notLoopB (glName p o) = true ∧ loopB (glLoopName p o) = true := by
  decide +kernel

theorem not_loop_of {f : String} {fn : Fn} (h : notLoopB f = true) (hf : coreProgram.find? f = some fn) :
    fn.loop = false := by
  unfold notLoopB at h
  rw [hf] at h
  simpa using h

theorem loop_of {f : String} {fn : Fn} (h : loopB f = true) (hf : coreProgram.find? f = some fn) :
    fn.loop = true ∧ Res.endOfFn fn = some none ∧ f ∉ Stmt.blockCallees (loopBody fn) := by
  unfold loopB at h
  rw [hf] at h
  simp only [Option.all_some, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun hm ↦ ?_⟩
  simp [hm] at h3

/-- **The calls of `gkr_layers__L{o}`, its loop and `gkr_last_layers__L{r}_L{o}`.** -/
theorem gl_sites : ∀ o < 2,
    Res.sitesB (fun f args _ ↦ (f != glcLsLN o || args == [11, 3, 0, 1, 2, 5, 6, 7, 8].map .n) &&
      (List.range 4).all fun rr ↦ f != glcLastN rr o || args == [0, 1, 2, 3, 13, 5, 6, 7, 8].map .n)
      (glcLsBody o) = true ∧
    Res.sitesB (fun f args _ ↦ (List.range 4).all fun p ↦ f != glName p o || args == glLsLArgs p)
      (glcLsLBody o) = true ∧
    ∀ rr < 4, Res.sitesB (fun f args _ ↦ (List.range 4).all fun p ↦ f != glName p o || args == glLastArgs p)
      (glcLastBody rr o) = true := by
  decide +kernel

theorem glcPar9_eq : glcPar9 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8] := rfl

theorem glParams_eq : glParams = [.n (valf% «gkr_layer» "layers"), .n (valf% «gkr_layer» "rounds"), .n (valf% «gkr_layer» "gkr_pts"), .n (valf% «gkr_layer» "x_m"), .n (valf% «gkr_layer» "x_j"), .n (valf% «gkr_layer» "start_g"), .n (valf% «gkr_layer» "g_bus_mu"), .n (valf% «gkr_layer» "tabs"), .n (valf% «gkr_layer» "stream")] := rfl

theorem glcLs_sel {o : ℕ} (ho : o < 2) {i : ℕ} (h : [glcLsN 0, glcLsN 1][i]? = some (glcLsN o)) : i = o := by
  have hl : i < 2 := by
    have := (List.getElem?_eq_some_iff.mp h).1
    simpa using this
  interval_cases o <;> interval_cases i <;> first | rfl | (simp [glcLsN] at h)

/-! ## The callers -/

/-- **A gkr callee's caller**: one listed in `Res.glCallers`, or itself, a loop. -/
theorem gl_caller {fI : String} {fnI : Fn} (hfI : coreProgram.find? fI = some fnI) {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fnI.body = .ret es vs) {c : Call} (hc : c ∈ calls es) {g : String}
    {L : List String} (hL : Res.glCallers.lookup g = some L) (hcf : c.f = g) :
    fI ∈ L ∨ (fI = g ∧ fnI.loop = true) := by
  have h := List.all_eq_true.mp (Res.calls_sites (Res.glCallers_all fnI (List.mem_of_find?_eq_some hfI)) hw c hc)
    _ (lookup_mem' hL)
  have hnI : fnI.name = fI := Da.fn_name_of_find hfI
  simp only [hcf, hnI, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    List.contains_iff_mem] at h
  exact h

/-- **A call of a body's dispatch**: a call of one of its callees, named nowhere else, is the arm its
selector picks. -/
theorem pick_sel {σ : Val} {x : V} {args rets : List V} : ∀ (gs : List String) (j : ℕ),
    ∀ c ∈ calls (pick σ x args rets j gs).evs, ∃ i, gs[i]? = some c.f ∧ σ x = ofK (addressOfIndex (j + i))
  | [], _, c, h => by simp [pick, Out.evs, calls] at h
  | g0 :: gs, j, c, h => by
    unfold pick at h
    split_ifs at h with hx
    · simp only [Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil, List.mem_cons,
        List.not_mem_nil, or_false] at h
      subst h
      exact ⟨0, rfl, by rw [Nat.add_zero]; exact hx⟩
    · obtain ⟨i, hi, hσ⟩ := pick_sel gs (j + 1) c h
      exact ⟨i + 1, hi, by rw [hσ, Nat.add_assoc, Nat.add_comm 1 i]⟩

theorem walk_disp_sel {σ : Val} {A B : List Stmt} {x : V} {gs : List String} {args rets : List V}
    (hA : Res.sitesB (fun f _ _ ↦ !gs.contains f) A = true) (hB : Res.sitesB (fun f _ _ ↦ !gs.contains f) B = true)
    {es : List Ev} {vs : List V} (hw : walk σ (A ++ .dispatch x gs args rets :: B) = .ret es vs) {c : Call}
    (hc : c ∈ calls es) (hf : gs.contains c.f = true) :
    ∃ i, gs[i]? = some c.f ∧ σ x = ofK (addressOfIndex i) := by
  have hc' : c ∈ calls (walk σ (A ++ .dispatch x gs args rets :: B)).evs := by rw [hw]; exact hc
  rw [walk_append] at hc'
  rcases Out.calls_seq hc' with h | h
  · have := Res.walk_sites A hA c h
    simp at this
    exact absurd (by simpa using hf) this
  · rw [walk] at h
    rcases Out.calls_seq h with h | h
    · rw [walk1] at h
      obtain ⟨i, hi, hx⟩ := pick_sel gs 0 c h
      exact ⟨i, hi, by rw [hx, Nat.zero_add]⟩
    · have := Res.walk_sites B hB c h
      simp at this
      exact absurd (by simpa using hf) this


/-! ## The bodies -/

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **`gkr_layers__L{o}`'s body**: the loop's call at `g^0` while `n_four ≠ 1`, and `m4 = n_four^4`. -/
theorem gls_holds {o : ℕ} (h : Stmt.HoldsList C rd σ (glcLsBody o) False kret) :
    σ (.n (valf% «gkr_layers» "s0#2")) = 1 ∧ σ (.n (valf% «gkr_layers» "s0#1")) = 1 + σ (.n (valf% «gkr_layers» "n_four")) ∧
      (σ (.n (valf% «gkr_layers» "s0#1")) ≠ 0 → C (glcLsLN o) [σ (.n (valf% «gkr_layers» "s0#2")), σ (.n (valf% «gkr_layers» "n_four")), σ (.n (valf% «gkr_layers» "layers")), σ (.n (valf% «gkr_layers» "rounds")), σ (.n (valf% «gkr_layers» "gkr_pts")), σ (.n (valf% «gkr_layers» "start_g")), σ (.n (valf% «gkr_layers» "g_bus_mu")),
        σ (.n (valf% «gkr_layers» "tabs")), σ (.n (valf% «gkr_layers» "stream"))] []) ∧
      σ (.n (valf% «gkr_layers» "m4")) = σ (.n (valf% «gkr_layers» "n_four")) * σ (.n (valf% «gkr_layers» "n_four")) * (σ (.n (valf% «gkr_layers» "n_four")) * σ (.n (valf% «gkr_layers» "n_four"))) := by
  simp only [glcLsBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨c9, a10, c11, -, hloop, m12, m13, -, -⟩ := h
  rw [tb_word_one] at c9 c11
  refine ⟨c11, by rw [a10, c9], hloop, by rw [m13, m12]⟩

/-- **`gkr_layers__L{o}`'s loop's body**: its four layers at `x_j = x_m^4·g^p`. -/
theorem glsl_holds {o : ℕ} (h : Stmt.HoldsList C rd σ (glcLsLBody o) False kret) :
    σ (.n (valf% «gkr_layers» «_loop0» "x4")) = σ (.n (valf% «gkr_layers» «_loop0» "x_m")) * σ (.n (valf% «gkr_layers» «_loop0» "x_m")) * (σ (.n (valf% «gkr_layers» «_loop0» "x_m")) * σ (.n (valf% «gkr_layers» «_loop0» "x_m"))) ∧
      (∀ p < 4, σ (.n (glcXj 10 11 p)) = σ (.n (valf% «gkr_layers» «_loop0» "x4")) * gen ^ p) ∧
      ∀ p < 4, C (glName p o) [σ (.n (valf% «gkr_layers» «_loop0» "layers")), σ (.n (valf% «gkr_layers» «_loop0» "rounds")), σ (.n (valf% «gkr_layers» «_loop0» "gkr_pts")), σ (.n (valf% «gkr_layers» «_loop0» "x_m")), σ (.n (valf% «gkr_layers» «_loop0» "x4")) * gen ^ p, σ (.n (valf% «gkr_layers» «_loop0» "start_g")), σ (.n (valf% «gkr_layers» «_loop0» "g_bus_mu")),
        σ (.n (valf% «gkr_layers» «_loop0» "tabs")), σ (.n (valf% «gkr_layers» «_loop0» "stream"))] [] := by
  rw [glcLsLBody, holdsList_append, holdsList_append,
    holdsList_noRet _ (by rfl : Stmt.noRetList [.atom (.mul (.n (valf% «gkr_layers» «_loop0» "x4~0")) (.n (valf% «gkr_layers» «_loop0» "x_m")) (.n (valf% «gkr_layers» «_loop0» "x_m"))),
      .atom (.mul (.n (valf% «gkr_layers» «_loop0» "x4")) (.n (valf% «gkr_layers» «_loop0» "x4~0")) (.n (valf% «gkr_layers» «_loop0» "x4~0")))] = true),
    holdsList_noRet _ (glcChain_noRet ..)] at h
  obtain ⟨hpre, hch, -⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hpre
  obtain ⟨m9, m10⟩ := hpre
  obtain ⟨hx, hcalls⟩ := glcChain_sound 4 hch
  exact ⟨by rw [m10, m9], hx, fun p hp ↦ by simpa using hcalls p hp⟩

/-- **`gkr_last_layers__L{r}_L{o}`'s body**: its `r` layers at `x_j = m4·g^p`. -/
theorem glast_holds {rr o : ℕ} (h : Stmt.HoldsList C rd σ (glcLastBody rr o) False kret) :
    (∀ p < rr, σ (.n (glcXj 4 9 p)) = σ (.n (valf% «gkr_last_layers» "m4")) * gen ^ p) ∧
      ∀ p < rr, C (glName p o) [σ (.n (valf% «gkr_last_layers» "layers")), σ (.n (valf% «gkr_last_layers» "rounds")), σ (.n (valf% «gkr_last_layers» "gkr_pts")), σ (.n (valf% «gkr_last_layers» "n_four")), σ (.n (valf% «gkr_last_layers» "m4")) * gen ^ p, σ (.n (valf% «gkr_last_layers» "start_g")), σ (.n (valf% «gkr_last_layers» "g_bus_mu")),
        σ (.n (valf% «gkr_last_layers» "tabs")), σ (.n (valf% «gkr_last_layers» "stream"))] [] := by
  rw [glcLastBody, holdsList_append, holdsList_noRet _ (glcChain_noRet ..)] at h
  obtain ⟨hx, hcalls⟩ := glcChain_sound rr h.1
  exact ⟨hx, fun p hp ↦ by simpa using hcalls p hp⟩

end Sem

/-! ## The slots along the layers -/

section Calls

variable {rd : Reader}

/-- **A layer's next slot**, from its call: `4L + 12` words past its own. -/
theorem gl_next {p o m : ℕ} (hp : p < 4) (ho : o < 2) (hm : m < 4) {layers rounds pts gmu tabs stream : E}
    {rets : List E}
    (h : coreProgram.Rel rd (glName p o) [layers, rounds, pts, gen ^ m, gen ^ (4 * m + p), gen ^ (2 - o), gmu,
      tabs, stream] rets) {cur : E} (hcur : LoadHolds rd layers (10 * (2 * (4 * m + p) + 2 - o) + 5) cur) :
    LoadHolds rd layers (10 * (2 * (4 * m + p) + 2 - o + 2) + 5)
      (cur * gen ^ (4 * (2 * (4 * m + p) + 2 - o) + 12)) := by
  obtain ⟨fn, hf, hpar, hb⟩ := glIs_sound (glIs_layers p hp o ho)
  obtain ⟨σ, hp', hbody⟩ := (tb_rel_iff_sem hf _ _).mp h
  rw [hpar, glParams_eq] at hp'
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp'
  obtain ⟨rfl, -, -, h3, h4, h5, -, -, -⟩ := hp'
  rw [hb] at hbody
  exact (gl_curs (fun _ _ _ h ↦ h) hp ho hbody h3 h4 h5 (by omega) hcur).2.2.2.2.2

/-- **The slots along a chain of layers** `4m .. 4m + r`, each at most `140` words on. -/
theorem gl_slots {o m : ℕ} (ho : o < 2) (hm : m < 4) {layers rounds pts gmu tabs stream S : E} {q : ℕ}
    (r : ℕ) (hr : r ≤ 4)
    (hR : ∀ p < r, coreProgram.Rel rd (glName p o) [layers, rounds, pts, gen ^ m, gen ^ (4 * m + p),
      gen ^ (2 - o), gmu, tabs, stream] [])
    (h0 : LoadHolds rd layers (10 * (2 * (4 * m) + 2 - o) + 5) (S * gen ^ q)) :
    ∀ p ≤ r, ∃ q', LoadHolds rd layers (10 * (2 * (4 * m + p) + 2 - o) + 5) (S * gen ^ q') ∧
      q' ≤ q + 140 * p := by
  intro p hp
  induction p with
  | zero => exact ⟨q, by simpa using h0, by omega⟩
  | succ p ih =>
    obtain ⟨q', h', hq'⟩ := ih (by omega)
    have hn := gl_next (p := p) (by omega) ho hm (hR p (by omega)) h'
    refine ⟨q' + (4 * (2 * (4 * m + p) + 2 - o) + 12), ?_, by omega⟩
    rw [show 2 * (4 * m + (p + 1)) + 2 - o = 2 * (4 * m + p) + 2 - o + 2 by omega, pow_add, ← mul_assoc]
    exact hn

theorem gl_pow4 (m p : ℕ) : gen ^ m * gen ^ m * (gen ^ m * gen ^ m) * gen ^ p = gen ^ (4 * m + p) := by
  rw [glc_pow4, ← pow_add]

theorem gen_succ_add_ne {m n : ℕ} (hmn : m + 1 < n) (hn : n < 34) : gen ^ m * gen + gen ^ n ≠ 0 := by
  intro h0
  rw [← pow_succ] at h0
  have := gen_pow_inj (by omega) (by omega) (e_add_eq_zero_iff.mp h0)
  omega

/-- **The loop's run**: from `x_m = g^m` to `n_four = g^n`, the slot of layer `4m` to that of `4n`. -/
theorem glsl_run {o n : ℕ} (ho : o < 2) (hn : n < 4) {layers rounds pts gmu tabs stream S : E} :
    ∀ d m q, m < n → coreProgram.relN rd d (glcLsLN o)
      (gen ^ m :: [gen ^ n, layers, rounds, pts, gen ^ (2 - o), gmu, tabs, stream]) [] →
      LoadHolds rd layers (10 * (2 * (4 * m) + 2 - o) + 5) (S * gen ^ q) →
      ∃ q', LoadHolds rd layers (10 * (2 * (4 * n) + 2 - o) + 5) (S * gen ^ q') ∧ q' ≤ q + 560 * (n - m)
  | 0, _, _, _, h, _ => h.elim
  | d + 1, m, q, hmn, h, h0 => by
    obtain ⟨hL, hnext⟩ := glsl_step ho d (gen ^ m) h
    have hR : ∀ p < 4, coreProgram.Rel rd (glName p o) [layers, rounds, pts, gen ^ m, gen ^ (4 * m + p),
        gen ^ (2 - o), gmu, tabs, stream] [] := fun p hp ↦ by
      have := hL p hp
      rwa [gl_pow4] at this
    obtain ⟨q1, h1, hq1⟩ := gl_slots ho (by omega) 4 le_rfl hR h0 4 le_rfl
    rw [show 4 * m + 4 = 4 * (m + 1) by ring] at h1
    rcases Nat.lt_or_ge (m + 1) n with hlt | hge
    · have := hnext (gen_succ_add_ne hlt (by omega))
      rw [← pow_succ] at this
      obtain ⟨q', h', hq'⟩ := glsl_run ho hn d (m + 1) q1 hlt this h1
      exact ⟨q', h', by omega⟩
    · obtain rfl : n = m + 1 := by omega
      exact ⟨q1, h1, by omega⟩

end Calls

/-! ## `verify_bus_gkr`'s dispatch -/

/-- **`verify_bus_gkr`'s tables and root slot**: at `g_bus_mu = g^d`, `d < 33`, `odd_g = g^(d % 2)`,
`n_four = g^((d - 1) / 8)`, `rem_g = g^(((d - 1) / 2) % 4)`, `start_g = g^(2 - d % 2)`, and the root
slot, of `L = 2 - d % 2`, holding the cursor `14` or `8` words past the frame's. -/
theorem vbg_ls {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) {C : CallRel} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList C Lm.read σ vbgPre True kret) :
    ∃ d < 33, σ (.n (val% «verify_bus_gkr» "odd_g")) = gen ^ (d % 2) ∧ σ (.n (val% «verify_bus_gkr» "n_four")) = gen ^ ((d - 1) / 8) ∧
      σ (.n (val% «verify_bus_gkr» "rem_g")) = gen ^ (((d - 1) / 2) % 4) ∧ σ (.n (val% «verify_bus_gkr» "start_g")) = gen ^ (2 - d % 2) ∧
      LoadHolds Lm.read (σ (.n (val% «verify_bus_gkr» "layers"))) (10 * (2 - d % 2) + 5) (σ (.n (val% «verify_bus_gkr» "cursor@1")) * gen ^ (if d % 2 = 0 then 14 else 8)) := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := Lm.read) (σ := σ) (kret := kret) hnr h n a heq
  have c19 := a 9 (.const (.n (val% «verify_bus_gkr» "s3#0")) (word 4294967296 0)) (by decide +kernel)
  have rc := a 10 (.rangeCheck (.n (val% «verify_bus_gkr» "g_bus_mu")) (.n (val% «verify_bus_gkr» "s3#1")) (.n (val% «verify_bus_gkr» "s3#2")) (.n (val% «verify_bus_gkr» "s3#3")) (.n (val% «verify_bus_gkr» "s3#0"))) (by decide +kernel)
  simp only [Atom.Holds] at c19 rc
  obtain ⟨d, hd, hg⟩ := tb_rc_sound' hμ Lm (K := 33) (by omega) (by norm_num)
    (by rw [c19, show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num),
      gen_pow_eq_ofK]) rc.1 rc.2.1 rc.2.2
  -- the tables
  have htab : σ (.n (val% «verify_bus_gkr» "odd_g")) = gen ^ (d % 2) ∧ σ (.n (val% «verify_bus_gkr» "n_four")) = gen ^ ((d - 1) / 8) ∧
      σ (.n (val% «verify_bus_gkr» "rem_g")) = gen ^ (((d - 1) / 2) % 4) ∧ σ (.n (val% «verify_bus_gkr» "start_g")) = gen ^ (2 - d % 2) := by
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · have c65 := a 40 (.const (.n (val% «verify_bus_gkr» "s16#0")) (word 1 0)) (by decide +kernel)
      have l65 := a 41 (.load (.n (val% «verify_bus_gkr» "s16#0")) (.n (val% «verify_bus_gkr» "depth_odd")) 0) (by decide +kernel)
      have c68 := a 44 (.const (.n (val% «verify_bus_gkr» "s19#0")) (word 1 0)) (by decide +kernel)
      have l68 := a 45 (.load (.n (val% «verify_bus_gkr» "s19#0")) (.n (val% «verify_bus_gkr» "four_bounds")) 0) (by decide +kernel)
      have c69 := a 46 (.const (.n (val% «verify_bus_gkr» "s20#0")) (word 1 0)) (by decide +kernel)
      have l69 := a 47 (.load (.n (val% «verify_bus_gkr» "s20#0")) (.n (val% «verify_bus_gkr» "four_rem")) 0) (by decide +kernel)
      have m166 := a 240 (.mul (.n (val% «verify_bus_gkr» "odd_g~0")) (.n (val% «verify_bus_gkr» "depth_odd")) (.n (val% «verify_bus_gkr» "g_bus_mu"))) (by decide +kernel)
      have l167 := a 241 (.load (.n (val% «verify_bus_gkr» "odd_g")) (.n (val% «verify_bus_gkr» "odd_g~0")) 0) (by decide +kernel)
      have c168 := a 242 (.const (.n (val% «verify_bus_gkr» "start_g~0")) (word 4 0)) (by decide +kernel)
      have m168 := a 243 (.mul (.n (val% «verify_bus_gkr» "start_g~0")) (.n (val% «verify_bus_gkr» "start_g")) (.n (val% «verify_bus_gkr» "odd_g"))) (by decide +kernel)
      have m399 := a 252 (.mul (.n (val% «verify_bus_gkr» "n_four~0")) (.n (val% «verify_bus_gkr» "four_bounds")) (.n (val% «verify_bus_gkr» "g_bus_mu"))) (by decide +kernel)
      have l400 := a 253 (.load (.n (val% «verify_bus_gkr» "n_four")) (.n (val% «verify_bus_gkr» "n_four~0")) 0) (by decide +kernel)
      have m401 := a 254 (.mul (.n (val% «verify_bus_gkr» "rem_g~0")) (.n (val% «verify_bus_gkr» "four_rem")) (.n (val% «verify_bus_gkr» "g_bus_mu"))) (by decide +kernel)
      have l402 := a 255 (.load (.n (val% «verify_bus_gkr» "rem_g")) (.n (val% «verify_bus_gkr» "rem_g~0")) 0) (by decide +kernel)
      simp only [Atom.Holds] at c65 l65 c68 l68 c69 l69 m166 l167 c168 m168 m399 l400 m401 l402
      rw [tb_word_one] at c65 c68 c69
      rw [m166, hg, pow_zero, mul_one] at l167
      rw [m399, hg, pow_zero, mul_one] at l400
      rw [m401, hg, pow_zero, mul_one] at l402
      have e167 : σ (.n (val% «verify_bus_gkr» "odd_g")) = 1 := (tb_loadHolds_unique l167 l65).trans c65
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)] at c168
      rw [c168, e167, mul_one] at m168
      refine ⟨by rw [e167]; simp, by rw [(tb_loadHolds_unique l400 l68).trans c68]; simp,
        by rw [(tb_loadHolds_unique l402 l69).trans c69]; simp, m168.symm.trans (by norm_num)⟩
    · obtain ⟨e167, e400, e402, e169⟩ := vbg_tables h hg hd (by omega)
      exact ⟨e167, e400, e402, e169⟩
  obtain ⟨e167, e400, e402, e169⟩ := htab
  -- the root slot
  have m170 := a 244 (.mul (.n (val% «verify_bus_gkr» "nxt~0")) (.n (val% «verify_bus_gkr» "start_g")) (.n (val% «verify_bus_gkr» "start_g"))) (by decide +kernel)
  have m171 := a 245 (.mul (.n (val% «verify_bus_gkr» "nxt~1")) (.n (val% «verify_bus_gkr» "nxt~0")) (.n (val% «verify_bus_gkr» "nxt~0"))) (by decide +kernel)
  have m172 := a 246 (.mul (.n (val% «verify_bus_gkr» "nxt~2")) (.n (val% «verify_bus_gkr» "nxt~1")) (.n (val% «verify_bus_gkr» "start_g"))) (by decide +kernel)
  have m173 := a 247 (.mul (.n (val% «verify_bus_gkr» "nxt~3")) (.n (val% «verify_bus_gkr» "nxt~2")) (.n (val% «verify_bus_gkr» "nxt~2"))) (by decide +kernel)
  have m174 := a 248 (.mul (.n (val% «verify_bus_gkr» "nxt")) (.n (val% «verify_bus_gkr» "layers")) (.n (val% «verify_bus_gkr» "nxt~3"))) (by decide +kernel)
  have c175 := a 249 (.const (.n (val% «verify_bus_gkr» "s26#0")) (word 1 0)) (by decide +kernel)
  have a176 := a 250 (.add (.n (val% «verify_bus_gkr» "s26#1")) (.n (val% «verify_bus_gkr» "odd_g")) (.n (val% «verify_bus_gkr» "s26#0"))) (by decide +kernel)
  simp only [Atom.Holds] at m170 m171 m172 m173 m174 c175 a176
  rw [tb_word_one] at c175
  have e174 : σ (.n (val% «verify_bus_gkr» "nxt")) = σ (.n (val% «verify_bus_gkr» "layers")) * gen ^ (10 * (2 - d % 2)) := by
    rw [m174, m173, m172, m171, m170, e169, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have hi := tb_holds_slice hnr h 251 [.ite (.n (val% «verify_bus_gkr» "s26#1")) (core% «verify_bus_gkr» s251_t)
    (core% «verify_bus_gkr» s251_e)] (by decide +kernel)
  simp only [Stmt.HoldsList] at hi
  rw [tb_holds_ite_noRet _ _ _ vbgArm_noRet_t vbgArm_noRet_e] at hi
  obtain ⟨⟨-, hfour, htwo⟩, -⟩ := hi
  rw [rtFour_eq, Stmt.holdsList_rename] at hfour
  rw [rtTwo_eq, Stmt.holdsList_rename] at htwo
  have h140 : (σ ∘ rtSh) (.n (val% «verify_bus_gkr» "s21.u24.s1#0")) = σ (.n (val% «verify_bus_gkr» "nxt")) := by rw [Function.comp_apply, rtSh_hi (by omega)]
  have h5 : (σ ∘ rtSh) (.n (val% «verify_bus_gkr» "cursor@1")) = σ (.n (val% «verify_bus_gkr» "cursor@1")) := by rw [Function.comp_apply, rtSh_lo (by omega)]
  refine ⟨d, hd, e167, e400, e402, e169, ?_⟩
  rw [← tb_loadHolds_mul_gen_pow, ← e174]
  rcases Nat.mod_two_eq_zero_or_one d with h2 | h2
  · have h0 : σ (.n (val% «verify_bus_gkr» "s26#1")) = 0 := by rw [a176, c175, e167, h2, pow_zero, e_add_self]
    have hf := hfour h0
    have b := fun n a heq => tb_holds_atom (C := C) (rd := Lm.read) (σ := σ ∘ rtSh) (kret := kret) rtFour_noRet
      hf n a heq
    have c261 := b 76 (.const (.n (val% «verify_bus_gkr» "product@6")) (word 16384 0)) (by decide +kernel)
    have m262 := b 77 (.mul (.n (val% «verify_bus_gkr» "combined@2~0")) (.n (val% «verify_bus_gkr» "cursor@1")) (.n (val% «verify_bus_gkr» "product@6"))) (by decide +kernel)
    have l262 := b 78 (.load (.n (val% «verify_bus_gkr» "combined@2~0")) (.n (val% «verify_bus_gkr» "s21.u24.s1#0")) 5) (by decide +kernel)
    simp only [Atom.Holds] at c261 m262 l262
    rw [show (16384 : ℕ) = 2 ^ 14 by norm_num, tb_word_two_pow (by norm_num)] at c261
    rw [m262, c261, h140, h5] at l262
    simpa [h2] using l262
  · have hne : σ (.n (val% «verify_bus_gkr» "s26#1")) ≠ 0 := by
      rw [a176, c175, e167, h2, pow_one]
      intro h0
      have := gen_pow_inj (a := 1) (b := 0) (by omega) (by omega)
        ((pow_one gen).trans ((e_add_eq_zero_iff.mp h0).trans (pow_zero gen).symm))
      omega
    have hf := htwo hne
    have b := fun n a heq => tb_holds_atom (C := C) (rd := Lm.read) (σ := σ ∘ rtSh) (kret := kret) rtTwo_noRet
      hf n a heq
    have c353 := b 45 (.const (.n (val% «verify_bus_gkr» "nxt[11]@6")) (word 256 0)) (by decide +kernel)
    have m354 := b 46 (.mul (.n (val% «verify_bus_gkr» "nxt[12]@6")) (.n (val% «verify_bus_gkr» "cursor@1")) (.n (val% «verify_bus_gkr» "nxt[11]@6"))) (by decide +kernel)
    have l354 := b 47 (.load (.n (val% «verify_bus_gkr» "nxt[12]@6")) (.n (val% «verify_bus_gkr» "s21.u24.s1#0")) 5) (by decide +kernel)
    simp only [Atom.Holds] at c353 m354 l354
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, tb_word_two_pow (by norm_num)] at c353
    rw [m354, c353, h140, h5] at l354
    simpa [h2] using l354

end

end LeanVM.Guest.EndExec
