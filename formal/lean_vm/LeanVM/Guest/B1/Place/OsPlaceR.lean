/-
  LeanVM.Guest.B1.Place.OsPlaceR

  A straight-line function whose `match`es and dispatches on one selector take its arm, complete in
  the placed form at a valuation chosen per memory.
-/

module

public import LeanVM.Guest.B1.Place.OsPlace
public import LeanVM.Guest.Memory.SelArm
public import LeanVM.Guest.B1.Opening.WalkMatch
import LeanVM.Guest.StmtsAppend

/-!
# Bodies at an arm, a valuation per memory

`SelOk x r n s`: `s` is an atom, a call, a conditional call, a dispatch (on `V.n x`, of more than `r`
and at most `n` names) or a `match` on `V.n x` of more than `r` and at most `n` quiet arms. At such a
statement the body at arm `r` (`selL`, `Memory/SelArm`) is flat (`selL_flat`), sets up the same
frames when the selector's word is `g^r` (`selL_calls`), allocates, places and loads as the body's
top level (`selL_allocSz`, `selL_addrS`, `selL_loads`), and walks as the body where that returns
(`walk_selRet`).

`os_completeAt_placeR`: such a body complete placed at an optional words bound (`CompleteAtOT`), its node with the
callees' trees satisfying their predicates (`FlatNodeT`), its valuation chosen per memory:
the buffers, the returns and the callees' layout fixed, on every memory a valuation with the
selector at `g^r` satisfying the body, setting up the fixed frames `cs`, allocating the buffers,
its loads in the caller's words or the buffers, its callees `KidsFromInT`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- A statement the selection at arm `r` of `V.n x` handles: an atom, a call, a conditional call, a
dispatch (on `V.n x`, of more than `r` and at most `n` names), a `match` on `V.n x` of more than `r`
and at most `n` quiet arms. -/
def SelOk (x r n : ℕ) : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | .callIf .. => true
  | .dispatch y fs _ _ => !selIs x y || (Nat.blt r fs.length && Nat.ble fs.length n)
  | .match_ y arms => selIs x y && Nat.blt r arms.length && Nat.ble arms.length n &&
      arms.all fun a ↦ a.all Stmt.quietS
  | _ => false

theorem selL_cons (x r : ℕ) (s : Stmt) (ss : List Stmt) : selL x r (s :: ss) = selS x r s ++ selL x r ss :=
  rfl

theorem selL_quiet (x r : ℕ) : ∀ arm : List Stmt, arm.all Stmt.quietS = true → selL x r arm = arm
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [selL_cons, selL_quiet x r ss h.2]
    match s, h.1 with
    | .atom _, _ => rfl

theorem quiet_atom {s : Stmt} (h : s.quietS = true) : ∃ a, s = .atom a ∧ a.quiet = true := by
  match s, h with
  | .atom a, h => exact ⟨a, rfl, h⟩

theorem selOk_match {x r n : ℕ} {y : V} {arms : List (List Stmt)} (h : SelOk x r n (.match_ y arms) = true) :
    y = V.n x ∧ r < arms.length ∧ arms.length ≤ n ∧ ∀ a ∈ arms, a.all Stmt.quietS = true := by
  simp only [SelOk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, List.all_eq_true] at h
  exact ⟨selIs_eq h.1.1.1, h.1.1.2, h.1.2, fun a ha ↦ List.all_eq_true.mpr (h.2 a ha)⟩

/-- A `match` on the selector at arm `r`: its arm `r`. -/
theorem selS_match {x r n : ℕ} {y : V} {arms : List (List Stmt)} (h : SelOk x r n (.match_ y arms) = true) :
    selS x r (.match_ y arms) = arms.getD r [] := by
  obtain ⟨rfl, hr, -, hq⟩ := selOk_match h
  show (bif selIs x (V.n x) && Nat.blt r (selA x r arms).length then (selA x r arms).getD r []
    else [.match_ (V.n x) (selA x r arms)]) = _
  have hs : selIs x (V.n x) = true := decide_eq_true rfl
  rw [selA_length, hs, show Nat.blt r arms.length = true from Nat.blt_eq.mpr hr]
  simp only [Bool.and_self, Bool.cond_true]
  rw [selA_getD]
  refine selL_quiet x r _ ?_
  by_cases hi : r < arms.length
  · rw [List.getD_eq_getElem _ _ hi]; exact hq _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; rfl

theorem selS_dispatch {x r : ℕ} {y : V} {fs : List String} {a rs : List V} :
    selS x r (.dispatch y fs a rs) = if selIs x y && Nat.blt r fs.length then [.call (fs.getD r "") a rs]
      else [.dispatch y fs a rs] := by
  show (bif selIs x y && Nat.blt r fs.length then [Stmt.call (fs.getD r "") a rs]
    else [Stmt.dispatch y fs a rs]) = _
  cases selIs x y && Nat.blt r fs.length <;> rfl

theorem getD_quiet {arms : List (List Stmt)} (hq : ∀ a ∈ arms, a.all Stmt.quietS = true) (r : ℕ) :
    (arms.getD r []).all Stmt.quietS = true := by
  by_cases hi : r < arms.length
  · rw [List.getD_eq_getElem _ _ hi]; exact hq _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; rfl

/-- **The selected block's statements**: the statement itself, a call, or a quiet atom. -/
theorem mem_selS {x r n : ℕ} {s : Stmt} (h : SelOk x r n s = true) {s' : Stmt} (hs' : s' ∈ selS x r s) :
    s' = s ∨ (∃ f a rs, s' = Stmt.call f a rs) ∨ s'.quietS = true := by
  match s, h with
  | .atom _, _ => exact Or.inl (List.mem_singleton.mp hs')
  | .call .., _ => exact Or.inl (List.mem_singleton.mp hs')
  | .callIf .., _ => exact Or.inl (List.mem_singleton.mp hs')
  | .dispatch y fs a rs, _ =>
    rw [selS_dispatch] at hs'
    split at hs'
    · exact Or.inr (Or.inl ⟨_, _, _, List.mem_singleton.mp hs'⟩)
    · exact Or.inl (List.mem_singleton.mp hs')
  | .match_ y arms, h =>
    rw [selS_match h] at hs'
    exact Or.inr (Or.inr (List.all_eq_true.mp (getD_quiet (selOk_match h).2.2.2 r) s' hs'))

theorem mem_selL {x r n : ℕ} : ∀ {ss : List Stmt}, ss.all (SelOk x r n) = true → ∀ {s' : Stmt}, s' ∈ selL x r ss →
    ∃ s ∈ ss, SelOk x r n s = true ∧ s' ∈ selS x r s ∧
      (s' = s ∨ (∃ f a rs, s' = Stmt.call f a rs) ∨ s'.quietS = true)
  | [], _, _, h => by simp [show selL x r [] = [] from rfl] at h
  | s :: ss, h, s', hs' => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [selL_cons, List.mem_append] at hs'
    rcases hs' with hs' | hs'
    · exact ⟨s, List.mem_cons_self, h.1, hs', mem_selS h.1 hs'⟩
    · obtain ⟨t, ht, r1, r2⟩ := mem_selL h.2 hs'
      exact ⟨t, List.mem_cons_of_mem _ ht, r1, r2⟩

/-- **The selected body is flat.** -/
theorem selL_flat {x r n : ℕ} {ss : List Stmt} (h : ss.all (SelOk x r n) = true) :
    (selL x r ss).all Stmt.flat = true := by
  refine List.all_eq_true.mpr fun s' hs' ↦ ?_
  obtain ⟨s, -, hok, hs'', h'⟩ := mem_selL h hs'
  rcases h' with rfl | ⟨f, a, rs, rfl⟩ | hq
  · match s', hok with
    | .atom _, _ => rfl
    | .call .., _ => rfl
    | .callIf .., _ => rfl
    | .dispatch .., _ => rfl
    | .match_ y arms, hok =>
      exfalso
      rw [selS_match hok] at hs''
      have := List.all_eq_true.mp (getD_quiet (selOk_match hok).2.2.2 r) _ hs''
      simp [Stmt.quietS] at this
  · rfl
  · obtain ⟨a, rfl, -⟩ := quiet_atom hq; rfl

/-- Every `match` and dispatch on the selector has at most `n` arms. -/
theorem armLeL_of {x r n : ℕ} : ∀ {ss : List Stmt}, ss.all (SelOk x r n) = true → armLeL x n ss = true
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := armLeL_of h.2
    show (armLeS x n s && armLeL x n ss) = true
    rw [ih, Bool.and_true]
    match s, h.1 with
    | .atom _, _ => rfl
    | .call .., _ => rfl
    | .callIf .., _ => rfl
    | .dispatch y fs a rs, hok =>
      show (!selIs x y || Nat.ble fs.length n) = true
      simp only [SelOk, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at hok
      rcases hok with hok | hok
      · simp [hok]
      · simp [hok.2]
    | .match_ y arms, hok =>
      obtain ⟨rfl, -, hn, hq⟩ := selOk_match hok
      show ((!selIs x (V.n x) || Nat.ble arms.length n) && armLeA x n arms) = true
      have hA : ∀ as : List (List Stmt), (∀ a ∈ as, a.all Stmt.quietS = true) → armLeA x n as = true := by
        intro as
        induction as with
        | nil => intro _; rfl
        | cons a as iha =>
          intro hq'
          show (armLeL x n a && armLeA x n as) = true
          have hl : ∀ b : List Stmt, b.all Stmt.quietS = true → armLeL x n b = true := by
            intro b
            induction b with
            | nil => intro _; rfl
            | cons t b ihb =>
              intro hb
              simp only [List.all_cons, Bool.and_eq_true] at hb
              obtain ⟨u, rfl, -⟩ := quiet_atom hb.1
              show (armLeS x n (.atom u) && armLeL x n b) = true
              rw [ihb hb.2]; rfl
          rw [hl a (hq' a List.mem_cons_self), iha fun b hb ↦ hq' b (List.mem_cons_of_mem _ hb)]; rfl
      rw [hA arms hq, Nat.ble_eq.mpr hn]
      simp

/-! ## The selected body's parts -/

theorem quiet_filterMap {β : Type} {G : Stmt → Option β} (hG : ∀ a : Atom, a.quiet = true → G (.atom a) = none) :
    ∀ arm : List Stmt, arm.all Stmt.quietS = true → arm.filterMap G = []
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨a, rfl, ha⟩ := quiet_atom h.1
    rw [List.filterMap_cons, hG a ha]
    exact quiet_filterMap hG ss h.2

/-- A map `none` on quiet atoms, `match`es, dispatches and calls: the selected statement's is the
statement's. -/
theorem selS_filterMap {β : Type} {x r n : ℕ} {G : Stmt → Option β}
    (hq : ∀ a : Atom, a.quiet = true → G (.atom a) = none) (hm : ∀ y arms, G (.match_ y arms) = none)
    (hd : ∀ y fs a rs, G (.dispatch y fs a rs) = none) (hc : ∀ f a rs, G (.call f a rs) = none)
    {s : Stmt} (h : SelOk x r n s = true) : (selS x r s).filterMap G = [s].filterMap G := by
  match s, h with
  | .atom _, _ => rfl
  | .call .., _ => rfl
  | .callIf .., _ => rfl
  | .dispatch y fs a rs, _ =>
    rw [selS_dispatch]
    split
    · simp [hc, hd]
    · rfl
  | .match_ y arms, h =>
    rw [selS_match h, quiet_filterMap hq _ (getD_quiet (selOk_match h).2.2.2 r)]
    simp [hm]

theorem selL_filterMap {β : Type} {x r n : ℕ} {G : Stmt → Option β}
    (hq : ∀ a : Atom, a.quiet = true → G (.atom a) = none) (hm : ∀ y arms, G (.match_ y arms) = none)
    (hd : ∀ y fs a rs, G (.dispatch y fs a rs) = none) (hc : ∀ f a rs, G (.call f a rs) = none) :
    ∀ ss : List Stmt, ss.all (SelOk x r n) = true → (selL x r ss).filterMap G = ss.filterMap G
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [selL_cons, List.filterMap_append, selL_filterMap hq hm hd hc ss h.2, selS_filterMap hq hm hd hc h.1,
      show s :: ss = [s] ++ ss from rfl, List.filterMap_append]

theorem selL_allocSz {x r n : ℕ} {ss : List Stmt} (h : ss.all (SelOk x r n) = true) :
    (selL x r ss).filterMap Main.Stmt.allocSz = ss.filterMap Main.Stmt.allocSz :=
  selL_filterMap (fun a ha ↦ by
      cases a with
      | hint hk => cases hk <;> simp_all [Main.Stmt.allocSz, Atom.quiet]
      | _ => rfl)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) ss h

theorem selL_addrS {x r n : ℕ} {ss : List Stmt} (h : ss.all (SelOk x r n) = true) :
    (selL x r ss).filterMap Main.Stmt.addrS = ss.filterMap Main.Stmt.addrS :=
  selL_filterMap (fun a ha ↦ by
      cases a with
      | frameAddr p run => simp [Atom.quiet] at ha
      | _ => rfl)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) ss h

theorem selL_loadS {x r n : ℕ} {ss : List Stmt} (h : ss.all (SelOk x r n) = true) :
    (selL x r ss).filterMap Stmt.loadS = ss.filterMap Stmt.loadS :=
  selL_filterMap (fun a ha ↦ by
      cases a with
      | load d p o => simp [Atom.quiet] at ha
      | _ => rfl)
    (fun _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) ss h

/-- The selected body's loads, as its events load: its top level's. -/
theorem selL_loads {σ : Val} {x r n : ℕ} {ss : List Stmt} (h : ss.all (SelOk x r n) = true) :
    (selL x r ss).flatMap (loadsEv σ) = ss.filterMap Stmt.loadS := by
  rw [← selL_loadS h]
  have hni : ∀ s ∈ selL x r ss, ∀ c z m, s ≠ .ite c z m := fun s hs c z m he ↦ by
    obtain ⟨t, -, hok, -, h'⟩ := mem_selL h hs
    subst he
    rcases h' with rfl | ⟨_, _, _, h'⟩ | hq
    · simp [SelOk] at hok
    · cases h'
    · simp [Stmt.quietS] at hq
  generalize selL x r ss = l at hni
  induction l with
  | nil => rfl
  | cons s l ih =>
    rw [List.flatMap_cons, ih fun t ht ↦ hni t (List.mem_cons_of_mem _ ht), List.filterMap_cons]
    have hs : ∀ c z m, s ≠ .ite c z m := hni s List.mem_cons_self
    have e : loadsEv σ s = (Stmt.loadS s).toList := by
      cases s with
      | ite c z m => exact absurd rfl (hs c z m)
      | _ => rfl
    rw [e]
    cases Stmt.loadS s <;> rfl

/-- **The selected body sets up the body's frames** when the selector's word is `g^r`. -/
theorem selL_calls {σ : Val} {x r n : ℕ} (hx : σ (V.n x) = ofK (addressOfIndex r)) (hr : r < 2 ^ 64 - 1) :
    ∀ {ss : List Stmt}, ss.all (SelOk x r n) = true →
      ((selL x r ss).filterMap (Stmt.callSF σ)).map (Main.mkCall σ) =
        (ss.filterMap (Stmt.callSF σ)).map (Main.mkCall σ)
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [selL_cons, List.filterMap_append, List.map_append, selL_calls hx hr h.2]
    have e : (selS x r s).filterMap (Stmt.callSF σ) = [s].filterMap (Stmt.callSF σ) := by
      match s, h.1 with
      | .atom _, _ => rfl
      | .call .., _ => rfl
      | .callIf .., _ => rfl
      | .dispatch y fs a rs, _ =>
        rw [selS_dispatch]
        split
        · next hs =>
          simp only [Bool.and_eq_true] at hs
          have hy := selIs_eq hs.1
          subst hy
          simp [Stmt.callSF, Main.Stmt.callS, hx, logG_spec hr]
        · rfl
      | .match_ y arms, hm =>
        rw [selS_match hm, quiet_filterMap (fun a ha ↦ ?_) _ (getD_quiet (selOk_match hm).2.2.2 r)]
        · rfl
        · cases a <;> rfl
    rw [e, show s :: ss = [s] ++ ss from rfl, List.filterMap_append, List.map_append]

theorem selL_dispOk {σ : Val} {x r n : ℕ} {ss : List Stmt} (h : ss.all (SelOk x r n) = true)
    (hdo : ∀ s ∈ ss, DispOk σ s) : ∀ s ∈ selL x r ss, DispOk σ s := fun s' hs' ↦ by
  obtain ⟨s, hs, -, -, h'⟩ := mem_selL h hs'
  rcases h' with rfl | ⟨f, a, rs, rfl⟩ | hq
  · exact hdo _ hs
  · trivial
  · obtain ⟨a, rfl, -⟩ := quiet_atom hq; trivial

/-- **The body walks as the selected body** where it returns, the selector's word `g^r`. -/
theorem walk_selRet {σ : Val} {C : CallRel} {rd : Reader} {x r n : ℕ} (hx : σ (V.n x) = ofK (addressOfIndex r))
    (hrn : r < n) (hn : n < 2 ^ 64 - 1) {body : List Stmt} {vs : List V} (h : body.all (SelOk x r n) = true)
    (hdo : ∀ s ∈ selL x r body, DispOk σ s) {next : Prop} {kret : List E → Prop}
    (hsat : (walk σ (body ⧺ [.ret vs])).Sat C rd σ next kret) :
    walk σ (body ++ [.ret vs]) = .ret ((selL x r body).flatMap (flEvs σ)) vs := by
  have hu : ∀ i < n, σ (V.n x) = ofK (addressOfIndex i) → i = r := fun i hi hxi ↦ by
    have he := congrArg logG (hxi.symm.trans hx)
    rwa [logG_spec (by omega), logG_spec (by omega)] at he
  have ho := outAg_seq (walk_sel hu body (armLeL_of h)) (outAg_refl (walk σ [.ret vs]))
  rw [← walk_append, ← walk_append] at ho
  have hw := walk_flat σ vs (selL x r body) (selL_flat h) hdo
  rcases ho with e | e
  · rw [← e, hw]
  · rw [e] at hsat
    exact hsat.elim

/-- **An arm of a selector complete placed, its valuation chosen per memory**: the buffers,
the returns, the callees' layout and frames `cs` fixed; on every memory holding the buffers and the
caller's words, a valuation with the selector at `g^r` satisfying the body, setting up `cs`,
allocating the buffers, its loads in the caller's words or the buffers, its callees `KidsFromInT`. -/
theorem os_completeAt_placeR {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args : List E)
    (Out : List E → Layout → Prop) (Bd : Option ℕ) {body : List Stmt} {vs : List V}
    (hb : fn.body = body ⧺ [.ret vs]) (x r n : ℕ) (hrn : r < n) (hn : n < 2 ^ 64 - 1)
    (hsel : body.all (SelOk x r n) = true) (haddrs : body.filterMap Main.Stmt.addrS = [])
    (sizes : List ℕ) (js : List ℕ) (hjs : js.Nodup) (hjl : ∀ j ∈ js, j < sizes.length)
    {C : CallRel} (Q : Val → Prop) (Ts : Val → Reader → List (Tree → Prop))
    (h : ∀ fp, ∃ (own : List (List E)) (rets : List E) (N : ℕ) (L : Layout) (Dk : ℕ → Prop) (cs : List Call),
      List.Forall₂ (fun c s => c.length ≤ s) own sizes ∧
      Out rets (osLoutJ (fp + fs f) sizes own js) ∧
      Within L (fp + fs f + sizes.sum) N ∧ DisjL L ∧ (∀ B ∈ Bd, fs f + sizes.sum + N ≤ B) ∧
      ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes own) → MemL rd Lin → ∃ σ : Val,
        σ (V.n x) = ofK (addressOfIndex r) ∧ Q σ ∧ fn.params.map σ = args ∧ (∀ s ∈ body, DispOk σ s) ∧
        (body.filterMap (Stmt.callSF σ)).map (Main.mkCall σ) = cs ∧
        Stmt.HoldsList C rd σ fn.body False (fun r => r = rets) ∧
        (body.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((body.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        (∀ q ∈ body.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes own) i)) ∧
        (MemL rd L → KidsFromInT coreProgram fs cert rd σ
          (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes own) i)
          (fun _ => False) cs (Ts σ rd) (fp + fs f + sizes.sum) N Dk)) :
    CompleteAtOT fs cert κ f Lin args Out Bd (FlatNodeT f fn body Q Ts) := by
  intro fp
  obtain ⟨own, rets, N, L, Dk, cs, hown, hout, hW, hD, hBd, hh⟩ := h fp
  set B := bufL (fp + fs f) sizes own with hB
  set pre := selL x r body with hpre
  have hst : pre.all Stmt.flat = true := selL_flat hsel
  have hBlen : B.length = sizes.length := by
    simp only [hB, bufL, List.length_zip, os_length_bases, hown.length_eq, Nat.min_self]
  have hLo : osLoutJ (fp + fs f) sizes own js = js.map (fun j => B.getD j default) := by
    unfold osLoutJ
    refine List.map_congr_left fun j hj => ?_
    rw [hB, os_bufL_getD hown (hjl j hj), os_bases_getD _ _ _ (hjl j hj)]
  set Lo := osLoutJ (fp + fs f) sizes own js with hLod
  set Lr : Layout := ((List.range B.length).filter (fun j => decide (j ∉ js))).map
    (fun j => B.getD j default)
  have hperm0 : (Lo ++ Lr).Perm B := by
    rw [hLo]; exact os_perm_pick B default js hjs fun j hj => hBlen ▸ hjl j hj
  have hperm : (Lo ++ (Lr ++ L)).Perm (B ++ L) := by
    rw [← List.append_assoc]; exact hperm0.append_right L
  have hmem : ∀ q, q ∈ Lo ++ (Lr ++ L) ↔ q ∈ B ++ L := fun q => hperm.mem_iff
  have hBW : Within B (fp + fs f) sizes.sum := bufL_within _ _ _ hown
  have hBD : DisjL B := bufL_disj _ _ _ hown
  have hBL : DisjL (B ++ L) := disj_append hBD hD hBW hW le_rfl
  refine ⟨fs f + sizes.sum + N, Lr ++ L, rets, Lo, hout, fun q hq => ?_, ?_, hBd, fun rd hlow hL => ?_⟩
  · rcases List.mem_append.mp ((hmem q).mp hq) with hq | hq
    · have := hBW q hq; omega
    · have := hW q hq; omega
  · exact hBL.perm hperm.symm fun h => Or.symm h
  have hLm : MemL rd (B ++ L) := fun q hq => hL q (List.mem_append_left _ ((hmem q).mpr hq))
  have hLin : MemL rd Lin := fun q hq => hL q (List.mem_append_right _ hq)
  obtain ⟨hB1, hL1⟩ := Main.memL_append.mp hLm
  obtain ⟨σ, hx, hQ, hp, hdo, hcs, hH, hsz, hbuf, hld, hK⟩ := hh rd hlow hB1 hLin
  have hdo' := selL_dispOk hsel hdo
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hH
  have hw : walk σ fn.body = .ret (pre.flatMap (flEvs σ)) vs := by
    rw [hb] at hsat ⊢
    exact walk_selRet hx hrn hn hsel hdo' hsat
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets := hsat.2
  obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre hst
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, selL_allocSz hsel, hsz]
  have hown' : ∀ i, RegionL B i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ)))
        (pre.flatMap (flEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ hown i hi)
  have hcalls : calls (pre.flatMap (flEvs σ)) = cs := by
    rw [i4, hpre, selL_calls hx (by omega) hsel, hcs]
  have hk := os_kidsFromInT_rmono (fs := fs) (cert := cert)
    (R' := fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ)))
        (pre.flatMap (flEvs σ)) i)
    (fun i hi => hi.imp_right (hown' i)) _ _ _ _ _ _ (hK hL1)
  rw [← hcalls, show fp + fs f + sizes.sum =
    fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum by rw [hal]] at hk
  have hrel := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert)
    (R := RegionL Lin) (D := RegionL Lo) (Dk := Dk) (N := N) (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw hr
    hes (by rw [hal, i1, selL_allocSz hsel]; exact hbuf) (by rw [i3, selL_addrS hsel, haddrs]; simp) _ hk
    (fun A hA => ?_) (fun i hi => ?_)
  · obtain ⟨t, ht, ks, rfl, hkT⟩ := hrel
    rw [hal] at ht
    refine ⟨_, ht, σ, _, ks, _, vs, rfl, hw, ?_, hQ, ?_⟩
    · rw [i4, hpre, selL_calls hx (by omega) hsel]
    · exact hkT
  · rw [i5, selL_loads hsel] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, hreg⟩ := hld q hq
    refine ⟨i, hi, ?_⟩
    rcases hreg with hreg | hreg
    · exact Or.inr (Or.inl hreg)
    · exact Or.inl (hown' i hreg)
  · obtain ⟨q, hq, h1, h2⟩ := hi
    have hqB : q ∈ B := hperm0.subset (List.mem_append_left _ hq)
    exact Or.inl (hown' i ⟨q, hqB, h1, h2⟩)

end
end LeanVM.Guest.B1
