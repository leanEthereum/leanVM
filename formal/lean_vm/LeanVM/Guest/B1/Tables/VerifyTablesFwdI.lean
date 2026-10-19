/-
  LeanVM.Guest.B1.Tables.VerifyTablesFwdI

  Forward completion over items: atoms, the `fs_next` and `squeeze` templates, conditional calls,
  dispatches and hints.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesFwd
public import LeanVM.Guest.B1.FsBlocks

/-!
# Forward completion over items

A body cut into items (`FItem`): atoms (`fStep`), the `fs_next` template (its word loaded at the
cursor, its values `fsVals` under the state its two cells hold), `squeeze` (`sqVals`), a
conditional call or a dispatch (the dispatch's results from an oracle `hv`) and a hint (its cells
from `hv`). `fRunI` runs them forward; `completes_items` is the body's `Completes` once the
obligations (`IOb`) hold of the final valuation.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig LeanVM.Guest.Memory

@[expose] public section

/-- An item of a body. -/
inductive FItem where
  | atom (a : Atom)
  | fs (s0 s1 cur : V) (j b : ℕ)
  | sq (s0 s1 : V) (b : ℕ)
  | callIf (c : V) (f : String) (args : List V)
  | disp (x : V) (fs : List String) (args rets : List V)
  | hint (h : Hint)

/-- An item's statements. -/
def FItem.stmts : FItem → List Stmt
  | .atom a => [.atom a]
  | .fs s0 s1 cur j b => fsNextT s0 s1 cur j b
  | .sq s0 s1 b => squeezeT s0 s1 b
  | .callIf c f args => [.callIf c f args]
  | .disp x fns args rets => [.dispatch x fns args rets]
  | .hint h => [.atom (.hint h)]

/-- A hint's cells. -/
def hintCells : Hint → List V
  | .witness _ (.stack vs) => vs
  | .bits _ _ _ (.stack vs) => vs
  | .bitsExp _ _ (.stack vs) => vs
  | .limbs _ ds => ds
  | .log2Ceil _ _ _ d => [d]
  | .inverse _ d => [d]
  | .alloc d _ => [d]
  | .allocDyn d _ => [d]
  | _ => []

/-- The values an item other than an atom sets. -/
def FItem.sets : FItem → List V
  | .fs _ _ _ _ b => (List.range 15).map fun k => .n (b + k)
  | .sq _ _ b => (List.range 14).map fun k => .n (b + k)
  | .disp _ _ _ rets => rets
  | .hint h => hintCells h
  | _ => []

/-- The values an item other than an atom reads. -/
def FItem.reads : FItem → List V
  | .fs s0 s1 cur _ _ => [s0, s1, cur]
  | .sq s0 s1 _ => [s0, s1]
  | .callIf c _ args => c :: args
  | .disp x _ args _ => x :: args
  | _ => []

/-- The digest whose cells are `(a, b)`, if any. -/
noncomputable def decodeCv (a b : E) : Digest :=
  open Classical in if h : ∃ cv, (a, b) = digestScalars cv then Classical.choose h else default

theorem decodeCv_spec {a b : E} (h : ∃ cv, (a, b) = digestScalars cv) :
    (a, b) = digestScalars (decodeCv a b) := by
  unfold decodeCv; simp only [h, ↓reduceDIte]; exact Classical.choose_spec h

/-- The values an item other than an atom sets, from `σ` (the oracle `hv` for results and
hints). -/
noncomputable def FItem.vals (rd : Reader) (hv : ℕ → E) (σ : Val) : FItem → List E
  | .fs s0 s1 cur j _ => memAt rd (σ cur) j :: (List.range 14).map fun k =>
      fsVals (memAt rd (σ cur) j) (decodeCv (σ s0) (σ s1)) 1 k
  | .sq s0 s1 _ => (List.range 14).map fun k => sqVals (decodeCv (σ s0) (σ s1)) k
  | it => it.sets.map fun v => hv v.idx

/-- `σ` updated at the values of a list, the earlier entries last. -/
def updMany (σ : Val) : List V → List E → Val
  | v :: vs, e :: es => Function.update (updMany σ vs es) v e
  | _, _ => σ

theorem updMany_of_not_mem (σ : Val) {v : V} : ∀ (vs : List V) (es : List E), v ∉ vs →
    updMany σ vs es v = σ v
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | w :: vs, e :: es, h => by
    simp only [List.mem_cons, not_or] at h
    rw [updMany, Function.update_of_ne h.1, updMany_of_not_mem σ vs es h.2]

theorem updMany_get (σ : Val) : ∀ (vs : List V) (es : List E) (_ : vs.Nodup) (hl : vs.length = es.length)
    (i : ℕ) (hi : i < vs.length), updMany σ vs es vs[i] = es[i]'(by omega)
  | [], _, _, _, i, hi => absurd hi (by simp)
  | _ :: _, [], _, hl, _, _ => absurd hl (by simp)
  | w :: vs, e :: es, hn, hl, i, hi => by
    rw [List.nodup_cons] at hn
    match i with
    | 0 => simp [updMany]
    | i + 1 =>
      simp only [List.getElem_cons_succ, updMany]
      rw [Function.update_of_ne (fun h => hn.1 (by rw [← h]; exact List.getElem_mem _)),
        updMany_get σ vs es hn.2 (by simpa using hl) i (by simpa using hi)]

/-- `D` with the values of a list. -/
def fAddMany (D : List ℕ) : List V → List ℕ
  | [] => D
  | v :: vs => fAdd (fAddMany D vs) v

/-- One item forward. -/
noncomputable def fStepI (rd : Reader) (lo : ℕ) (hv : ℕ → E) (D : List ℕ) (σ : Val) :
    FItem → List ℕ × Val
  | .atom a => fStep rd lo D σ a
  | it => (fAddMany D it.sets, updMany σ it.sets (it.vals rd hv σ))

/-- The new set values after an item, by its shape. -/
def fDStepI (lo : ℕ) (D : List ℕ) : FItem → List ℕ
  | .atom a => fDStep lo D a
  | it => fAddMany D it.sets

theorem fStepI_fst (rd : Reader) (lo : ℕ) (hv : ℕ → E) (D : List ℕ) (σ : Val) (it : FItem) :
    (fStepI rd lo hv D σ it).1 = fDStepI lo D it := by
  cases it <;> simp only [fStepI, fDStepI, fStep_fst]

/-- The items forward. -/
noncomputable def fRunI (rd : Reader) (lo : ℕ) (hv : ℕ → E) : List ℕ → Val → List FItem → Val
  | _, σ, [] => σ
  | D, σ, it :: its => fRunI rd lo hv (fStepI rd lo hv D σ it).1 (fStepI rd lo hv D σ it).2 its

/-- An item of a body: an atom of a window, or an item reading set values and setting new
distinct ones, as many as its values. -/
def fOkI1 (lo hi : ℕ) (D : List ℕ) : FItem → Bool
  | .atom a => fOk1 lo hi D a
  | it => it.reads.all (fDef lo D) && it.sets.all (fNew lo hi D) && decide it.sets.Nodup

/-- A body's items. -/
def fOkI (lo hi : ℕ) : List ℕ → List FItem → Bool
  | _, [] => true
  | D, it :: its => fOkI1 lo hi D it && fOkI lo hi (fDStepI lo D it) its

/-- What an item asks of the final valuation. -/
def IObl (C : CallRel) (rd : Reader) (lo : ℕ) (D : List ℕ) (σf : Val) : FItem → Prop
  | .atom a => fObl1 rd lo D σf a
  | .fs s0 s1 cur j _ => IsInK (σf cur) ∧ (rd ((σf cur).limb 0 * Parameters.gpow j)).isSome ∧
      ∃ cv, (σf s0, σf s1) = digestScalars cv
  | .sq s0 s1 _ => ∃ cv, (σf s0, σf s1) = digestScalars cv
  | .callIf c f args => IsInK (σf c) ∧ (σf c ≠ 0 → C f (args.map σf) [])
  | .disp x fns args rets => ∃ (j : ℕ) (h : j < fns.length), σf x = ofK (Parameters.gpow j) ∧
      C fns[j] (args.map σf) (rets.map σf)
  | .hint _ => True

/-- A body's obligations. -/
def IObls (C : CallRel) (rd : Reader) (lo : ℕ) (σf : Val) : List ℕ → List FItem → Prop
  | _, [] => True
  | D, it :: its => IObl C rd lo D σf it ∧ IObls C rd lo σf (fDStepI lo D it) its

/-! ## Framing -/

theorem fDef_addMany_of {lo : ℕ} {D : List ℕ} {v : V} (h : fDef lo D v = true) :
    ∀ vs, fDef lo (fAddMany D vs) v = true
  | [] => h
  | _ :: vs => fDef_add _ (fDef_addMany_of h vs)

theorem fDef_addMany_mem {lo : ℕ} {D : List ℕ} {v : V} : ∀ vs, v ∈ vs → fDef lo (fAddMany D vs) v = true
  | [], h => absurd h (by simp)
  | w :: vs, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact fDef_add_self _
    · exact fDef_add _ (fDef_addMany_mem vs h)

theorem fDStepI_mono {lo : ℕ} {D : List ℕ} {v : V} (it : FItem) (h : fDef lo D v = true) :
    fDef lo (fDStepI lo D it) v = true := by
  cases it with
  | atom a => exact fDStep_mono a h
  | _ => exact fDef_addMany_of h _

theorem not_mem_sets {lo hi : ℕ} {D : List ℕ} {it : FItem} {v : V}
    (hs : it.sets.all (fNew lo hi D) = true) (h : fDef lo D v = true) : v ∉ it.sets := fun hm => by
  have := fNew_not_def (List.all_eq_true.mp hs v hm)
  rw [h] at this; exact absurd this (by simp)

theorem fStepI_frame (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) {D : List ℕ} (σ : Val) {it : FItem}
    (hok : fOkI1 lo hi D it = true) {v : V} (h : fDef lo D v = true) :
    (fStepI rd lo hv D σ it).2 v = σ v := by
  cases it with
  | atom a => exact fStep_frame rd lo D σ a h
  | _ =>
    simp only [fOkI1, Bool.and_eq_true] at hok
    exact updMany_of_not_mem σ _ _ (not_mem_sets hok.1.2 h)

theorem fStepI_upd (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) {D : List ℕ} (σ : Val) {it : FItem}
    (hok : fOkI1 lo hi D it = true) {v : V} (h : (fStepI rd lo hv D σ it).2 v ≠ σ v) :
    fNew lo hi D v = true := by
  cases it with
  | atom a => exact fStep_upd rd σ hok h
  | _ =>
    simp only [fOkI1, Bool.and_eq_true] at hok
    by_contra hn
    refine h (updMany_of_not_mem σ _ _ fun hm => hn ?_)
    exact List.all_eq_true.mp hok.1.2 v hm

theorem fRunI_frame (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) : ∀ (its : List FItem) (D : List ℕ) (σ : Val),
    fOkI lo hi D its = true → ∀ {v : V}, fDef lo D v = true → fRunI rd lo hv D σ its v = σ v
  | [], _, _, _, _, _ => rfl
  | it :: its, D, σ, hok, v, h => by
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunI]
    rw [fRunI_frame rd hv its _ _ (by rw [fStepI_fst]; exact hok.2) (by rw [fStepI_fst]; exact fDStepI_mono it h),
      fStepI_frame rd hv σ hok.1 h]

theorem fRunI_upd (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) : ∀ (its : List FItem) (D : List ℕ) (σ : Val),
    fOkI lo hi D its = true → ∀ v, fRunI rd lo hv D σ its v ≠ σ v → ∃ k, v = .n k ∧ lo ≤ k ∧ k < hi
  | [], _, _, _, v, h => absurd rfl h
  | it :: its, D, σ, hok, v, h => by
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunI] at h
    by_cases e : (fStepI rd lo hv D σ it).2 v = σ v
    · rw [← e] at h
      exact fRunI_upd rd hv its _ _ (by rw [fStepI_fst]; exact hok.2) v h
    · exact fNew_num (fStepI_upd rd hv σ hok.1 e)

theorem fRunI_ext (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) {its : List FItem} {D : List ℕ} {σ : Val}
    (hok : fOkI lo hi D its = true) : Ext lo hi σ (fRunI rd lo hv D σ its) := by
  intro v hv'
  by_contra hne
  obtain ⟨k, rfl, h1, h2⟩ := fRunI_upd rd hv its D σ hok v hne
  exact hv' k h1 h2 rfl

/-- After an item, its values are set. -/
theorem fOkI1_vars {lo hi : ℕ} {D : List ℕ} {it : FItem} (hok : fOkI1 lo hi D it = true) :
    ∀ v ∈ it.reads ++ it.sets, fDef lo (fDStepI lo D it) v = true := by
  intro v hv
  cases it with
  | atom a => simp [FItem.reads, FItem.sets] at hv
  | _ =>
    simp only [fOkI1, Bool.and_eq_true] at hok
    rcases List.mem_append.mp hv with hv | hv
    · exact fDef_addMany_of (List.all_eq_true.mp hok.1.1 v hv) _
    · exact fDef_addMany_mem _ hv

/-! ## The items hold -/

theorem sets_get {rd : Reader} {hv : ℕ → E} {σ : Val} {lo hi : ℕ} {D : List ℕ} {it : FItem} (hok : fOkI1 lo hi D it = true)
    (hl : it.sets.length = (it.vals rd hv σ).length) (σ1 : Val) (h1 : σ1 = updMany σ it.sets (it.vals rd hv σ))
    (i : ℕ) (hi : i < it.sets.length) : σ1 it.sets[i] = (it.vals rd hv σ)[i]'(by omega) := by
  cases it with
  | atom a => simp [FItem.sets] at hi
  | _ =>
    simp only [fOkI1, Bool.and_eq_true, decide_eq_true_eq] at hok
    rw [h1]; exact updMany_get σ _ _ hok.2 hl i hi

set_option maxRecDepth 10000 in
/-- **An item holds** at a valuation agreeing with its step on its values, once its obligation
does. -/
theorem fStepI_holds {C : CallRel} (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) {D : List ℕ} {σ : Val}
    {it : FItem} (hok : fOkI1 lo hi D it = true) {σf : Val}
    (hag : ∀ v, fDef lo (fDStepI lo D it) v = true → σf v = (fStepI rd lo hv D σ it).2 v)
    (hob : IObl C rd lo D σf it) {next : Prop} {kret : List E → Prop} (hn : next) :
    Stmt.HoldsList C rd σf it.stmts next kret := by
  cases it with
  | atom a =>
    refine ⟨fStep_holds rd hok (fun v hv' => hag v (fOk1_vars hok v hv')) hob, hn⟩
  | fs s0 s1 cur j b =>
    have hv' := fOkI1_vars hok
    have hok' := hok
    simp only [fOkI1, Bool.and_eq_true, decide_eq_true_eq] at hok'
    have hrd : ∀ v ∈ [s0, s1, cur], σf v = σ v := fun v hm => by
      rw [hag v (hv' v (List.mem_append_left _ hm))]
      exact updMany_of_not_mem σ _ _ (not_mem_sets hok'.1.2 (List.all_eq_true.mp hok'.1.1 v hm))
    have hl : (FItem.fs s0 s1 cur j b).sets.length = ((FItem.fs s0 s1 cur j b).vals rd hv σ).length := by
      simp [FItem.sets, FItem.vals]
    have hset := fun i (hi : i < 15) =>
      (hag _ (hv' _ (List.mem_append_right _ (List.getElem_mem (by simp [FItem.sets]; exact hi))))).trans
        (sets_get hok hl _ rfl i (by simp [FItem.sets]; exact hi))
    obtain ⟨o1, o2, o3⟩ := hob
    rw [hrd cur (by simp)] at o1 o2
    rw [hrd s0 (by simp), hrd s1 (by simp)] at o3
    have e0 := hset 0 (by omega)
    simp only [FItem.sets, FItem.vals, List.getElem_map, List.getElem_range, List.getElem_cons_zero,
      Nat.add_zero] at e0
    rw [FItem.stmts, holds_fsNextT]
    refine ⟨⟨by rw [hrd cur (by simp), e0]; exact loadHolds_memAt o1 o2, decodeCv (σ s0) (σ s1), ?_,
      fun k hk1 hk2 => ?_⟩, hn⟩
    · rw [hrd s0 (by simp), hrd s1 (by simp)]; exact decodeCv_spec o3
    · have e := hset (k + 1) (by omega)
      simp only [FItem.sets, FItem.vals, List.getElem_map, List.getElem_range,
        List.getElem_cons_succ] at e
      rw [show b + 1 + k = b + (k + 1) by ring, e, e0]
  | sq s0 s1 b =>
    have hv' := fOkI1_vars hok
    have hok' := hok
    simp only [fOkI1, Bool.and_eq_true, decide_eq_true_eq] at hok'
    have hrd : ∀ v ∈ [s0, s1], σf v = σ v := fun v hm => by
      rw [hag v (hv' v (List.mem_append_left _ hm))]
      exact updMany_of_not_mem σ _ _ (not_mem_sets hok'.1.2 (List.all_eq_true.mp hok'.1.1 v hm))
    have hl : (FItem.sq s0 s1 b).sets.length = ((FItem.sq s0 s1 b).vals rd hv σ).length := by
      simp [FItem.sets, FItem.vals]
    have hob' : ∃ cv, (σf s0, σf s1) = digestScalars cv := hob
    rw [hrd s0 (by simp), hrd s1 (by simp)] at hob'
    rw [FItem.stmts, holds_squeezeT]
    refine ⟨⟨decodeCv (σ s0) (σ s1), ?_, fun k hk => ?_⟩, hn⟩
    · rw [hrd s0 (by simp), hrd s1 (by simp)]; exact decodeCv_spec hob'
    · have := (hag _ (hv' _ (List.mem_append_right _ (List.getElem_mem (by simp [FItem.sets]; exact hk))))).trans
        (sets_get hok hl _ rfl k (by simp [FItem.sets]; exact hk))
      simp only [FItem.sets, FItem.vals, List.getElem_map, List.getElem_range] at this
      exact this
  | callIf c f args => exact ⟨hob.1, hob.2, hn⟩
  | disp x fns args rets => exact ⟨hob, hn⟩
  | hint h => exact ⟨trivial, hn⟩

theorem holdsList_flatMap {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop} :
    ∀ (its : List FItem) {next : Prop},
      (∀ it ∈ its, ∀ {next' : Prop}, next' → Stmt.HoldsList C rd σ it.stmts next' kret) → next →
      Stmt.HoldsList C rd σ (its.flatMap FItem.stmts) next kret
  | [], _, _, hn => hn
  | it :: its, _, h, hn => by
    rw [List.flatMap_cons, holdsList_append]
    exact h it (List.mem_cons_self ..) (holdsList_flatMap its (fun i hi => h i (List.mem_cons_of_mem _ hi)) hn)

/-- **A body's items hold** once its obligations do. -/
theorem fRunI_holds {C : CallRel} (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) (σf : Val) :
    ∀ (its : List FItem) (D : List ℕ) (σ : Val), fOkI lo hi D its = true →
      (∀ v, fRunI rd lo hv D σ its v = σf v) → IObls C rd lo σf D its →
      ∀ it ∈ its, ∀ (next : Prop) (kret : List E → Prop), next → Stmt.HoldsList C rd σf it.stmts next kret
  | [], _, _, _, _, _, it, hit => absurd hit (by simp)
  | b :: its, D, σ, hok, hf, hob, it, hit => by
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunI] at hf
    obtain ⟨hob1, hob2⟩ := hob
    rcases List.mem_cons.mp hit with rfl | hit
    · intro next kret hn
      refine fStepI_holds (σ := σ) rd hv hok.1 (fun v hv' => ?_) hob1 hn
      rw [← hf v, fRunI_frame rd hv its _ _ (by rw [fStepI_fst]; exact hok.2) (by rw [fStepI_fst]; exact hv')]
    · rw [fStepI_fst] at hf
      exact fRunI_holds rd hv σf its _ _ hok.2 hf hob2 it hit

/-- **A body of items completes forward**, its values set by `fRunI`, once its obligations hold
there. -/
theorem completes_items {C : CallRel} {rd : Reader} {lo hi : ℕ} (hv : ℕ → E) (its : List FItem)
    (hok : fOkI lo hi [] its = true) (σ : Val) (hob : IObls C rd lo (fRunI rd lo hv [] σ its) [] its) :
    Completes C rd lo hi (its.flatMap FItem.stmts) σ (fun σ' => σ' = fRunI rd lo hv [] σ its) :=
  ⟨_, fRunI_ext rd hv hok, rfl, fun _ _ hn =>
    holdsList_flatMap its (fun it hit _ hn' => fRunI_holds rd hv _ its [] σ hok (fun _ => rfl) hob it hit _ _ hn') hn⟩

/-! ## The obligations as a list -/

/-- An item's obligation. -/
inductive IOb where
  | ob (o : Ob)
  | fs (s0 s1 cur : V) (j : ℕ)
  | sq (s0 s1 : V)
  | callIf (c : V) (f : String) (args : List V)
  | disp (x : V) (fns : List String) (args rets : List V)
  deriving DecidableEq

/-- What an item's obligation asks of the final valuation. -/
def IOb.Holds (C : CallRel) (rd : Reader) (σf : Val) : IOb → Prop
  | .ob o => o.Holds rd σf
  | .fs s0 s1 cur j => IsInK (σf cur) ∧ (rd ((σf cur).limb 0 * Parameters.gpow j)).isSome ∧
      ∃ cv, (σf s0, σf s1) = digestScalars cv
  | .sq s0 s1 => ∃ cv, (σf s0, σf s1) = digestScalars cv
  | .callIf c f args => IsInK (σf c) ∧ (σf c ≠ 0 → C f (args.map σf) [])
  | .disp x fns args rets => ∃ (j : ℕ) (h : j < fns.length), σf x = ofK (Parameters.gpow j) ∧
      C fns[j] (args.map σf) (rets.map σf)

/-- An item's obligations. -/
def iObs1 (lo : ℕ) (D : List ℕ) : FItem → List IOb
  | .atom a => (fObs1 lo D a).map .ob
  | .fs s0 s1 cur j _ => [.fs s0 s1 cur j]
  | .sq s0 s1 _ => [.sq s0 s1]
  | .callIf c f args => [.callIf c f args]
  | .disp x fns args rets => [.disp x fns args rets]
  | .hint _ => []

/-- A body's obligations. -/
def iObs (lo : ℕ) : List ℕ → List FItem → List IOb
  | _, [] => []
  | D, it :: its => iObs1 lo D it ++ iObs lo (fDStepI lo D it) its

theorem IObl_of_obs {C : CallRel} {rd : Reader} {lo : ℕ} {D : List ℕ} {σf : Val} {it : FItem}
    (h : ∀ o ∈ iObs1 lo D it, o.Holds C rd σf) : IObl C rd lo D σf it := by
  cases it with
  | atom a => exact fObl1_of_obs fun o ho => h (.ob o) (List.mem_map_of_mem ho)
  | fs s0 s1 cur j b => exact h _ (List.mem_singleton_self _)
  | sq s0 s1 b => exact h _ (List.mem_singleton_self _)
  | callIf c f args => exact h _ (List.mem_singleton_self _)
  | disp x fns args rets => exact h _ (List.mem_singleton_self _)
  | hint _ => trivial

theorem IObls_of_obs {C : CallRel} {rd : Reader} {lo : ℕ} {σf : Val} : ∀ (its : List FItem) (D : List ℕ),
    (∀ o ∈ iObs lo D its, o.Holds C rd σf) → IObls C rd lo σf D its
  | [], _, _ => trivial
  | _ :: its, _, h => ⟨IObl_of_obs fun o ho => h o (List.mem_append_left _ ho),
      IObls_of_obs its _ fun o ho => h o (List.mem_append_right _ ho)⟩

/-! ## What a body defines -/

/-- The atoms of a body's items defining their results by arithmetic. -/
def fDefAtomsI (lo : ℕ) : List ℕ → List FItem → List Atom
  | _, [] => []
  | D, .atom a :: its => (if fIsDef lo D a then [a] else []) ++ fDefAtomsI lo (fDStep lo D a) its
  | D, it :: its => fDefAtomsI lo (fDStepI lo D it) its

/-- The loads of a body's items defining their results. -/
def fLoadsI (lo : ℕ) : List ℕ → List FItem → List (V × V × ℕ)
  | _, [] => []
  | D, .atom (.load d p off) :: its => (if fDef lo D d then [] else [(d, p, off)]) ++
      fLoadsI lo (fDStep lo D (.load d p off)) its
  | D, it :: its => fLoadsI lo (fDStepI lo D it) its

/-- The items other than atoms of a body. -/
def fSetItems : List FItem → List FItem
  | [] => []
  | .atom _ :: its => fSetItems its
  | it :: its => it :: fSetItems its

theorem fRunI_eq_of_def (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) {its : List FItem} {D : List ℕ} {σ : Val}
    {σf : Val} (hok : fOkI lo hi D its = true) (hf : ∀ v, fRunI rd lo hv D σ its v = σf v) {v : V}
    (h : fDef lo D v = true) : σf v = σ v := by
  rw [← hf v, fRunI_frame rd hv its D σ hok h]

/-- **The defining atoms hold.** -/
theorem fRunI_defs (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) (σf : Val) : ∀ (its : List FItem) (D : List ℕ)
    (σ : Val), fOkI lo hi D its = true → (∀ v, fRunI rd lo hv D σ its v = σf v) →
      ∀ a ∈ fDefAtomsI lo D its, a.Holds rd σf
  | [], _, _, _, _, a, ha => absurd ha (by simp [fDefAtomsI])
  | .atom b :: its, D, σ, hok, hf, a, ha => by
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunI] at hf
    simp only [fDefAtomsI, List.mem_append] at ha
    rcases ha with ha | ha
    · split_ifs at ha with hd
      · rcases List.mem_singleton.mp ha with rfl
        rw [fStepI_fst] at hf
        refine fStep_holds (σ := σ) rd hok.1 (fun v hv' => ?_) (fObl1_of_def hd)
        rw [← hf v]
        exact fRunI_frame rd hv its _ _ hok.2 (fOk1_vars hok.1 v hv')
      · exact absurd ha (by simp)
    · rw [fStepI_fst] at hf
      exact fRunI_defs rd hv σf its _ _ hok.2 hf a ha
  | .fs .. :: its, D, σ, hok, hf, a, ha
  | .sq .. :: its, D, σ, hok, hf, a, ha
  | .callIf .. :: its, D, σ, hok, hf, a, ha
  | .disp .. :: its, D, σ, hok, hf, a, ha
  | .hint _ :: its, D, σ, hok, hf, a, ha => by
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunI] at hf
    rw [fStepI_fst] at hf
    exact fRunI_defs rd hv σf its _ _ hok.2 hf a (by simpa [fDefAtomsI] using ha)

/-- **The defining loads read the memory.** -/
theorem fRunI_loads (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) (σf : Val) : ∀ (its : List FItem) (D : List ℕ)
    (σ : Val), fOkI lo hi D its = true → (∀ v, fRunI rd lo hv D σ its v = σf v) →
      ∀ q ∈ fLoadsI lo D its, σf q.1 = memAt rd (σf q.2.1) q.2.2
  | [], _, _, _, _, q, hq => absurd hq (by simp [fLoadsI])
  | .atom b :: its, D, σ, hok, hf, q, hq => by
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunI] at hf
    rw [fStepI_fst] at hf
    have hrest : q ∈ fLoadsI lo (fDStepI lo D (.atom b)) its → σf q.1 = memAt rd (σf q.2.1) q.2.2 :=
      fun h => fRunI_loads rd hv σf its _ _ hok.2 hf q h
    cases b with
    | load d p off =>
      simp only [fLoadsI, List.mem_append] at hq
      rcases hq with hq | hq
      · split_ifs at hq with hd
        · exact absurd hq (by simp)
        · rcases List.mem_singleton.mp hq with rfl
          simp only [Bool.not_eq_true] at hd
          have hk1 : fOk1 lo hi D (.load d p off) = true := hok.1
          have hok1 := hk1
          simp only [fOk1, Bool.and_eq_true] at hok1
          have hfr := fun v (hv' : fDef lo (fDStepI lo D (.atom (.load d p off))) v = true) =>
            (hf v).symm.trans (fRunI_frame rd hv its _ _ hok.2 hv')
          have e1 := hfr d (fOk1_vars hk1 d (by simp [atomUses]))
          have e2 := hfr p (fOk1_vars hk1 p (by simp [atomUses]))
          simp only [fStepI, fStep, hd, Bool.false_eq_true, ↓reduceIte, Function.update_self] at e1 e2
          rw [Function.update_of_ne (ne_of_def hok1.1 hd)] at e2
          dsimp only
          rw [e1, e2]
      · exact hrest hq
    | _ => exact hrest (by simpa [fLoadsI] using hq)
  | .fs .. :: its, D, σ, hok, hf, q, hq
  | .sq .. :: its, D, σ, hok, hf, q, hq
  | .callIf .. :: its, D, σ, hok, hf, q, hq
  | .disp .. :: its, D, σ, hok, hf, q, hq
  | .hint _ :: its, D, σ, hok, hf, q, hq => by
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunI] at hf
    rw [fStepI_fst] at hf
    exact fRunI_loads rd hv σf its _ _ hok.2 hf q (by simpa [fLoadsI] using hq)

theorem FItem.vals_congr (rd : Reader) (hv : ℕ → E) {σ σ' : Val} (it : FItem)
    (h : ∀ v ∈ it.reads, σ' v = σ v) : it.vals rd hv σ' = it.vals rd hv σ := by
  cases it with
  | fs s0 s1 cur j b =>
    simp only [FItem.reads, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
    simp only [FItem.vals, h.1, h.2.1, h.2.2]
  | sq s0 s1 b =>
    simp only [FItem.reads, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
    simp only [FItem.vals, h.1, h.2]
  | _ => rfl

theorem FItem.vals_length (rd : Reader) (hv : ℕ → E) (σ : Val) (it : FItem) :
    (it.vals rd hv σ).length = it.sets.length := by
  cases it <;> simp [FItem.vals, FItem.sets]

/-- An atom item. -/
def FItem.isAtom : FItem → Bool
  | .atom _ => true
  | _ => false

theorem fSetItems_cons (it : FItem) (its : List FItem) :
    fSetItems (it :: its) = (if it.isAtom then [] else [it]) ++ fSetItems its := by
  cases it <;> rfl

theorem fStepI_nonatom (rd : Reader) (lo : ℕ) (hv : ℕ → E) (D : List ℕ) (σ : Val) {it : FItem}
    (h : it.isAtom = false) : fStepI rd lo hv D σ it = (fAddMany D it.sets, updMany σ it.sets (it.vals rd hv σ)) := by
  cases it <;> simp_all [FItem.isAtom, fStepI]

/-- **An item's values are its own**, at the final valuation. -/
theorem fRunI_sets (rd : Reader) {lo hi : ℕ} (hv : ℕ → E) (σf : Val) : ∀ (its : List FItem) (D : List ℕ)
    (σ : Val), fOkI lo hi D its = true → (∀ v, fRunI rd lo hv D σ its v = σf v) →
      ∀ it ∈ fSetItems its, ∀ (i : ℕ) (hi : i < it.sets.length) (hj : i < (it.vals rd hv σf).length),
        σf it.sets[i] = (it.vals rd hv σf)[i]
  | [], _, _, _, _, it, hit => absurd hit (by simp [fSetItems])
  | b :: its, D, σ, hok, hf, it, hit => by
    simp only [fOkI, Bool.and_eq_true] at hok
    simp only [fRunI] at hf
    rw [fStepI_fst] at hf
    rw [fSetItems_cons, List.mem_append] at hit
    rcases hit with hit | hit
    · cases hb : b.isAtom
      · rw [hb] at hit
        simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hit
        subst hit
        intro i hi hj
        have hfr := fun v (hv' : fDef lo (fDStepI lo D it) v = true) =>
          (hf v).symm.trans (fRunI_frame rd hv its _ _ hok.2 hv')
        have hvars := fOkI1_vars hok.1
        have hok1 := hok.1
        have hn : it.isAtom = false := hb
        cases it with
        | atom a => simp [FItem.isAtom] at hn
        | _ =>
          simp only [fOkI1, Bool.and_eq_true, decide_eq_true_eq] at hok1
          have hrd : ∀ v ∈ FItem.reads _, σf v = σ v := fun v hm => by
            rw [hfr v (hvars v (List.mem_append_left _ hm)), fStepI_nonatom rd lo hv D σ hn]
            exact updMany_of_not_mem σ _ _ (not_mem_sets hok1.1.2 (List.all_eq_true.mp hok1.1.1 v hm))
          rw [hfr _ (hvars _ (List.mem_append_right _ (List.getElem_mem hi))), fStepI_nonatom rd lo hv D σ hn]
          dsimp only
          rw [updMany_get σ _ _ hok1.2 (FItem.vals_length rd hv σ _).symm i hi]
          simp only [FItem.vals_congr rd hv _ hrd]
      · rw [hb] at hit; exact absurd hit (by simp)
    · exact fRunI_sets rd hv σf its _ _ hok.2 hf it hit

end
end LeanVM.Guest.B1.VerifySub
