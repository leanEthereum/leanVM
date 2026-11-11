/-
  LeanVM.Guest.B1.Place.OfrProof

  `opening_fold_round` complete placed, at both its specializations: the proof.
-/

module

public import LeanVM.Guest.B1.Place.Ofr
public import LeanVM.Guest.B1.Whir.CFoldCall
public import LeanVM.Guest.B1.Whir.HelperAll
public import LeanVM.Guest.B1.Bits.Grind3
public import LeanVM.Guest.B1.Tables.Kids.Walk
public import LeanVM.Guest.Budget.Bounded

/-!
# `opening_fold_round`, placed: the proof

Both specializations and their callees, `opening_fold` and `grind_check__L3`, place nothing
(`ofr_pureIn`), so the placed form follows from the relation loading from the caller's words
(`completeAtD_of_relIn`, and `completeAtDTB_of_relIn` within a bound). That relation is the
unplaced one (`ofr0_rel`, `ofr_rel`) along the flat body's walk: its loads, at `__L3`, the round's
three words at the cursor; its one call, a leaf loading at most the round's words
(`relIn_of_leafSpec`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir (MeaningFoldRound roundLen ofrZeroBody ofrBody ofrAtoms osParams osRun)

@[expose] public section

/-- **A leaf whose loads its spec bounds loads from `R`** when the spec's pointers' runs lie in
`R`. -/
theorem relIn_of_leafSpec {f : String} {spec : List (ℕ × ℕ)} (hok : LeafSpecOk f spec)
    {rd : Reader} {R : ℕ → Prop} {args rets : List E} (hreg : RegPtrs spec args R)
    (h : coreProgram.Rel rd f args rets) : coreProgram.RelIn rd R f args rets := by
  obtain ⟨fn, hf, hpar, hleaf⟩ := hok
  refine Lift.relIn_of_leaf hf hleaf (fun σ es vs hp hw A hA => ?_) h
  have hall := Lift.walk_leafOk (σ := σ) fn.body hleaf
  rw [hw] at hall
  obtain ⟨q, hq, off, hoff, rfl⟩ := loads_spec hall A hA
  have hσ : σ (.n q.1) = args.getD q.1 0 := by
    have h1 := hpar q hq
    have h2 : (fn.params.map σ)[q.1]? = args[q.1]? := by rw [hp]
    rw [List.getElem?_map, h1] at h2
    simp only [Option.map_some] at h2
    rw [List.getD_eq_getElem?_getD, ← h2]
    rfl
  rw [hσ]
  exact hreg q hq off hoff

set_option maxRecDepth 100000 in
theorem grind3_leafSpec : leafSpecB "grind_check__L3" [] = true := by decide +kernel

/-- `opening_fold_round`'s specializations and their callees. -/
def ofrPureS : List String :=
  ["opening_fold_round__L0", "opening_fold_round__L3", "opening_fold", "grind_check__L3"]

/-- `Program.PureIn`, decided. -/
noncomputable def ofrPureB (S : List String) : Bool :=
  S.all fun g => match coreProgram.find? g with
    | some fn => Stmt.pureList S fn.body
    | none => true

set_option maxRecDepth 100000 in
theorem ofrPureB_ok : ofrPureB ofrPureS = true := by decide +kernel

/-- **`opening_fold_round` and its callees place nothing.** -/
theorem ofr_pureIn : coreProgram.PureIn ofrPureS := by
  intro g hg fn hf
  have h := List.all_eq_true.mp ofrPureB_ok g hg
  rw [hf] at h
  exact h

/-- Not a dispatch. -/
def noDispB : Stmt → Bool
  | .dispatch .. => false
  | _ => true

theorem dispOk_of_noDisp {σ : Val} {s : Stmt} (h : noDispB s = true) : DispOk σ s := by
  cases s with
  | dispatch => simp [noDispB] at h
  | _ => trivial

theorem callSF_of_noDisp {σ : Val} : ∀ {pre : List Stmt}, pre.all noDispB = true →
    pre.filterMap (Stmt.callSF σ) = pre.filterMap Main.Stmt.callS
  | [], _ => rfl
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hs : Stmt.callSF σ s = Main.Stmt.callS s := by
      cases s with
      | dispatch => simp [noDispB] at h
      | _ => rfl
    rw [List.filterMap_cons, List.filterMap_cons, hs, callSF_of_noDisp h.2]

/-- The parameters' values are the arguments. -/
theorem osParams_val {σ : Val} {args : List E} (hp : (osParams 11).map σ = args) (i : ℕ)
    (hi : i < 11) : σ (.n i) = args.getD i 0 := by
  rw [← hp]
  simp [osParams, hi]

/-! ## At `0` bits -/

/-- `opening_fold_round__L0`'s statements before its `ret`. -/
def ofr0Pre : List Stmt :=
  [.call "opening_fold" ((List.range 11).map V.n) (osRun 11 10)] ++
    ((List.range 10).map fun i ↦ .atom (.copy (.n (21 + i)) (.n (11 + i))))

theorem ofr0Pre_body : ofrZeroBody = ofr0Pre ++ [.ret (osRun 21 10)] := rfl

theorem ofr0Pre_flat : ofr0Pre.all Core.Stmt.flat = true := by decide +kernel
theorem ofr0Pre_flatW : ofr0Pre.all Whir.Stmt.flat = true := by decide +kernel
theorem ofr0Pre_noDisp : ofr0Pre.all noDispB = true := by decide +kernel
theorem ofr0Pre_loads : ofr0Pre.filterMap Stmt.loadS = [] := by decide +kernel
theorem ofr0Pre_calls : ofr0Pre.filterMap Main.Stmt.callS =
    [(none, "opening_fold", (List.range 11).map V.n, osRun 11 10)] := by decide +kernel

/-- **`opening_fold_round__L0` loads from `R`** when the round's words at the cursor lie in `R`. -/
theorem ofr0_relIn {rd : Reader} {R : ℕ → Prop} {args rets : List E}
    (hcan : AllCanonical (args.take 5)) (hreg : RegPtrs [(7, roundLen 0)] args R)
    (hm : MeaningFoldRound 0 rd args rets) :
    coreProgram.RelIn rd R "opening_fold_round__L0" args rets := by
  obtain ⟨fn, hf, hps, hb⟩ := Whir.ofr0_fn
  have hrel := Whir.ofr0_rel Whir.ofr0_fn hcan hm
  refine Tables.relIn_of_flatRel hf (hb.trans ofr0Pre_body) ofr0Pre_flat hrel
    (fun σ hp hh ↦ ?_) (by decide +kernel)
  rw [hps] at hp
  rw [hb, ofr0Pre_body, Whir.holdsList_flat_ret _ ofr0Pre_flatW] at hh
  refine ⟨fun s hs ↦ dispOk_of_noDisp (List.all_eq_true.mp ofr0Pre_noDisp s hs),
    by simp [ofr0Pre_loads], fun c hc _ ↦ ?_⟩
  rw [callSF_of_noDisp ofr0Pre_noDisp, ofr0Pre_calls] at hc
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
  subst hc
  have hk := hh.1 _ (List.mem_append_left _ (List.mem_singleton_self _) :
    Stmt.call "opening_fold" ((List.range 11).map V.n) (osRun 11 10) ∈ ofr0Pre)
  have ha : ((List.range 11).map V.n).map σ = args := hp
  simp only [Whir.StmtOk] at hk
  simp only [Main.mkCall]
  rw [ha] at hk ⊢
  refine relIn_of_leafSpec (leafSpecOk_of fold_leafSpec) ?_ hk
  intro p hp' t ht
  simp only [foldSpec, List.mem_singleton] at hp'
  subst hp'
  exact hreg (7, roundLen 0) (List.mem_singleton_self _) t (by simpa [roundLen] using ht)

/-! ## At `3` bits -/

theorem grindName3 : "grind_check__L" ++ Whir.natStr 3 = "grind_check__L3" := by decide +kernel

theorem ofr3Pre_flat : (ofrAtoms 3).all Core.Stmt.flat = true := by decide +kernel
theorem ofr3Pre_flatW : (ofrAtoms 3).all Whir.Stmt.flat = true := by decide +kernel
theorem ofr3Pre_noDisp : (ofrAtoms 3).all noDispB = true := by decide +kernel
theorem ofr3Pre_loads : (ofrAtoms 3).filterMap Stmt.loadS = [(.n 7, 0), (.n 7, 1), (.n 7, 2)] := by
  decide +kernel
theorem ofr3Pre_calls : (ofrAtoms 3).filterMap Main.Stmt.callS =
    [(none, "grind_check__L3", [.n 46], [])] := by decide +kernel
theorem ofr3Pre_call : Stmt.call ("grind_check__L" ++ Whir.natStr 3) [.n 46] [] ∈ ofrAtoms 3 := by
  simp only [ofrAtoms, List.mem_append, List.mem_cons, true_or, or_true]

/-- **`opening_fold_round__L3` loads from `R`** when the round's words at the cursor lie in `R`. -/
theorem ofr3_relIn {rd : Reader} {R : ℕ → Prop} {args rets : List E}
    (hcan : AllCanonical (args.take 5)) (hreg : RegPtrs [(7, roundLen 3)] args R)
    (hm : MeaningFoldRound 3 rd args rets) :
    coreProgram.RelIn rd R "opening_fold_round__L3" args rets := by
  obtain ⟨fn, hf, hps, hb⟩ := Whir.ofr3_fn
  have hrel := Whir.ofr_rel (by decide) Whir.ofr3_fn
    (fun w hw ↦ by rw [grindName3]; exact (grind_check3_holds rd _ _).mpr hw) hcan hm
  refine Tables.relIn_of_flatRel hf (hb.trans (Whir.ofrBody_atoms 3)) ofr3Pre_flat hrel
    (fun σ hp hh ↦ ?_) (by decide +kernel)
  rw [hps] at hp
  rw [hb, Whir.ofrBody_atoms, Whir.holdsList_flat_ret _ ofr3Pre_flatW] at hh
  have h7 : σ (.n 7) = args.getD 7 0 := osParams_val hp 7 (by omega)
  refine ⟨fun s hs ↦ dispOk_of_noDisp (List.all_eq_true.mp ofr3Pre_noDisp s hs), fun q hq ↦ ?_,
    fun c hc _ ↦ ?_⟩
  · rw [ofr3Pre_loads] at hq
    have ho : q.1 = .n 7 ∧ q.2 < 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp
    rw [ho.1, h7]
    exact hreg (7, roundLen 3) (List.mem_singleton_self _) q.2 (by simpa [roundLen] using ho.2)
  · rw [callSF_of_noDisp ofr3Pre_noDisp, ofr3Pre_calls] at hc
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
    subst hc
    have hk := hh.1 _ ofr3Pre_call
    simp only [Whir.StmtOk, grindName3] at hk
    simp only [Main.mkCall]
    exact relIn_of_leafSpec (leafSpecOk_of grind3_leafSpec) (fun _ h ↦ by simp at h) hk

/-! ## Placed -/

theorem ofr_relIn {e : String × ℕ} (he : e ∈ ofrTable) {rd : Reader} {R : ℕ → Prop}
    {args rets : List E} (hcan : AllCanonical (args.take 5))
    (hreg : RegPtrs [(7, roundLen e.2)] args R) (hm : MeaningFoldRound e.2 rd args rets) :
    coreProgram.RelIn rd R e.1 args rets := by
  simp only [ofrTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact ofr0_relIn hcan hreg hm
  · exact ofr3_relIn hcan hreg hm

theorem ofrTable_pure {e : String × ℕ} (he : e ∈ ofrTable) : e.1 ∈ ofrPureS := by
  simp only [ofrTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> simp [ofrPureS]

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem CompleteAtD.toO {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} (h : CompleteAtD fs cert k f Lin args Out) :
    CompleteAtO fs cert k f Lin args Out none := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun _ h => by simp at h, hr⟩

theorem CompleteAtB.toO {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} (h : CompleteAtB fs cert k f Lin args Out B) :
    CompleteAtO fs cert k f Lin args Out (some B) := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun _ h => by cases h; exact hn, hr⟩

/-- **`opening_fold_round` is complete placed at both specializations.** -/
theorem opening_fold_round_completeAt : opening_fold_round_completeAt_Spec := by
  intro fs cert κ _ _ _ e he Bd Lin args rets _ hcan hreg hmean hbd
  have hrel : ∀ rd, LowDef κ rd → MemL rd Lin → coreProgram.RelIn rd (RegionL Lin) e.1 args rets :=
    fun rd hl hL ↦ ofr_relIn he hcan hreg (hmean rd hl hL)
  cases Bd with
  | none => exact (Lift.completeAtD_of_relIn ofr_pureIn (ofrTable_pure he) hrel).toO
  | some B =>
    exact (completeAtDTB_of_relIn ofr_pureIn (ofrTable_pure he)
      (fun rd t r hn hv hb ↦ hbd B rfl rd t args r hn hv hb) hrel).toCompleteAtB.toO

end
end LeanVM.Guest.B1
