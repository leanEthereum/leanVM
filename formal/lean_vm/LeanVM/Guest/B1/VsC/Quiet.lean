/-
  LeanVM.Guest.B1.VsC.Quiet

  Quiet nodes: a node whose valuation reads the memory, its callees' words fixed before it; a node
  popping nothing over quiet callees; a leaf whose relation holds and whose hints its atoms pin.
-/

module

public import LeanVM.Guest.B1.VsC.Fwd
public import LeanVM.Guest.Exact.Free

/-!
# Quiet nodes

* `callCompletes_nodeRd`: `callCompletes_node` with a valuation per memory. The callees' words come
  from a valuation `σ0` fixed before the memory, and each memory's valuation `σ` takes the path of
  `σ0` and agrees with it on every call's arguments and returns (`CallsAgree`): a range check's
  touched words, read from the memory, are no call's.
* `postQuiet_node`: a node whose path has no witness hint and is exact, over callees each quiet
  (`PostQuiet`) or a phantom, pops nothing and is exact.
* `walk_quiet`: a body with no witness hint (`Stmt.atomsAll atomQuiet`, decided by the kernel) has
  none on any path.
* `callCompletes_leaf_pinned`: a straight body with no witness hint completes where its relation
  holds and every valuation holding its atoms has its hints exact (hints pinned by the body).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd

@[expose] public section

/-- Two valuations agree on the calls' argument and return words. -/
def CallsAgree (σ σ' : Val) (cs : List Call) : Prop :=
  ∀ c ∈ cs, c.args.map σ = c.args.map σ' ∧ c.rets.map σ = c.rets.map σ'

theorem kidsValid_congr {rd : Reader} {σ σ' : Val} : ∀ (cs : List Call) (ts : List Tree),
    CallsAgree σ σ' cs → Tree.KidsValid coreProgram rd σ cs ts →
      Tree.KidsValid coreProgram rd σ' cs ts
  | [], [], _, h => h
  | c :: cs, t :: ts, ha, h => by
    rw [Tree.KidsValid] at h ⊢
    obtain ⟨e1, e2⟩ := ha c List.mem_cons_self
    refine ⟨h.1, ?_, kidsValid_congr cs ts (fun c' hc' => ha c' (List.mem_cons_of_mem _ hc')) h.2.2⟩
    rw [← e1, ← e2]; exact h.2.1
  | [], _ :: _, _, h => by simp [Tree.KidsValid] at h
  | _ :: _, [], _, h => by simp [Tree.KidsValid] at h

/-- **A node completes on a valuation per memory**, its callees' words those of a valuation `σ0`
fixed before the memory. -/
theorem callCompletes_nodeRd {k : ℕ} {f : String} {args rets : List E} {Pre : Reader → Prop}
    {Post : Reader → Tree → Prop}
    (h : ∀ b, ∃ (m : ℕ) (Wo : Words) (σ0 : Val) (fn : Core.Fn) (es : List Ev) (vs : List V)
        (Qs : List (Reader → Tree → Prop)),
      WordsIn Wo b m ∧ coreProgram.find? f = some fn ∧
      KidsCompl k σ0 (fun rd => HoldsWords rd Wo ∧ Pre rd) Qs (calls es) ∧
      ∀ rd, LowDef k rd → HoldsWords rd Wo → Pre rd → ∃ σ : Val,
        fn.params.map σ = args ∧ walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧
        CallsAgree σ0 σ (calls es) ∧ (∀ e ∈ es, e.Holds rd σ) ∧
        ∀ ts, Tree.KidsValid coreProgram rd σ (calls es) ts → KidsPost rd Qs (calls es) ts →
          Post rd (.node f σ (allocs σ es) ts)) :
    CallCompletes k f args rets Pre Post := by
  intro b
  obtain ⟨m, Wo, σ0, fn, es, vs, Qs, hWo, hf, hk, hrd⟩ := h b
  obtain ⟨n, Wk, hWk, hks⟩ := kidsCompl_words (calls es) Qs hk (b + m)
  refine ⟨m + n, Wo ++ Wk, hWo.append hWk, fun rd hl hW hP => ?_⟩
  obtain ⟨ho, hkw⟩ := holdsWords_append.mp hW
  obtain ⟨ts, hvs, hbs, hqs⟩ := hks rd hl hkw ⟨ho, hP⟩
  obtain ⟨σ, hp, hw, hr, hag, hev, hpost⟩ := hrd rd hl ho hP
  have hvs' := kidsValid_congr _ _ hag hvs
  have hev' : Tree.events coreProgram (.node f σ (allocs σ es) ts) = es := by
    simp only [Tree.events, Tree.name, Tree.val, hf, hw]
  refine ⟨.node f σ (allocs σ es) ts, rfl, ⟨fn, hf, hp, es, vs, hw, hr, hev, hvs'⟩, ?_,
    hpost ts hvs' hqs⟩
  rw [Tree.BufsOk, hev']
  exact ⟨rfl, hbs⟩

/-! ## Quiet nodes -/

/-- The callees of a node, each taken one quiet: none pops, each exact. -/
theorem kids_quiet {rd : Reader} {σ : Val} : ∀ (cs : List Call) (ts : List Tree),
    Tree.KidsValid coreProgram rd σ cs ts → KidsPost rd (cs.map fun _ => PostQuiet) cs ts →
      (∀ l ∈ Tree.popsKids coreProgram rd ts, l = []) ∧ Tree.EveryKids (ExactAt coreProgram rd) ts
  | [], [], _, _ => ⟨by simp [Tree.popsKids], by rw [Tree.EveryKids]; trivial⟩
  | c :: cs, t :: ts, hv, hp => by
    rw [Tree.KidsValid] at hv
    rw [List.map_cons, kidsPost_cons] at hp
    obtain ⟨ih1, ih2⟩ := kids_quiet cs ts hv.2.2 hp.2
    have ht : t.pops coreProgram rd = [] ∧ t.Every (ExactAt coreProgram rd) := by
      by_cases hc : c.taken = true
      · exact hp.1 hc
      · have hc' : c.taken = false := by simpa using hc
        have h1 := hv.2.1
        simp only [hc', Bool.false_eq_true, ↓reduceIte] at h1
        obtain ⟨⟨g, σ', rfl⟩, -⟩ := h1
        exact ⟨by rw [Tree.pops], Tree.every_phantom⟩
    refine ⟨fun l hl => ?_, ?_⟩
    · rw [Tree.popsKids] at hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact ht.1
      · exact ih1 l hl
    · rw [Tree.EveryKids]; exact ⟨ht.2, ih2⟩
  | [], _ :: _, hv, _ => by simp [Tree.KidsValid] at hv
  | _ :: _, [], hv, _ => by simp [Tree.KidsValid] at hv

theorem splice_quietKids {rd : Reader} {σ : Val} : ∀ (es : List Ev) (ks : List (List Pop)),
    (∀ a, Ev.atom a ∈ es → atomQuiet a = true) → (∀ l ∈ ks, l = []) → splice rd σ es ks = []
  | [], ks, _, _ => by cases ks <;> rfl
  | .atom a :: es, ks, ha, hk => by
    rw [splice, splice_quietKids es ks (fun b hb => ha b (List.mem_cons_of_mem _ hb)) hk]
    have := ha a List.mem_cons_self
    cases a with
    | hint hh => cases hh <;> simp_all [atomQuiet, Atom.pops, Hint.pops]
    | _ => rfl
  | .inK _ :: es, ks, ha, hk => by
    rw [splice]
    exact splice_quietKids es ks (fun b hb => ha b (List.mem_cons_of_mem _ hb)) hk
  | .call .. :: es, ks, ha, hk | .skip .. :: es, ks, ha, hk => by
    rw [splice, splice_quietKids es ks.tail (fun b hb => ha b (List.mem_cons_of_mem _ hb))
      (fun l hl => hk l (List.mem_of_mem_tail hl))]
    cases ks with
    | nil => rfl
    | cons l ks => simp [hk l List.mem_cons_self]

/-- **A quiet node**: its path pops nothing and is exact, its callees quiet or phantoms. -/
theorem postQuiet_node {rd : Reader} {f : String} {fn : Fn} {σ : Val} {es : List Ev} {vs : List V}
    {ts : List Tree} (hf : coreProgram.find? f = some fn) (hw : walk σ fn.body = .ret es vs)
    (hq : ∀ a, Ev.atom a ∈ es → atomQuiet a = true) (hx : ∀ e ∈ es, e.Exact rd σ)
    (hv : Tree.KidsValid coreProgram rd σ (calls es) ts)
    (hp : KidsPost rd ((calls es).map fun _ => PostQuiet) (calls es) ts) (bufs : List ℕ) :
    PostQuiet rd (.node f σ bufs ts) := by
  obtain ⟨h1, h2⟩ := kids_quiet _ _ hv hp
  refine ⟨?_, ?_⟩
  · rw [Tree.pops_node (P := coreProgram) hf hw]; exact splice_quietKids es _ hq h1
  · rw [Tree.every_node]; exact ⟨exactAt_of_walk hf hw hx, h2⟩

/-- **A body with no witness hint has none on a path.** -/
theorem walk_quiet {σ : Val} {body : List Stmt} {es : List Ev} {vs : List V}
    (h : Stmt.atomsAll atomQuiet body = true) (hw : walk σ body = .ret es vs) :
    ∀ a, Ev.atom a ∈ es → atomQuiet a = true := by
  have h' : Stmt.atomsAll (fun a => !(fun a => !atomQuiet a) a) body = true := by
    simpa only [Bool.not_not] using h
  have hp := walk_partnered (σ := σ) (p := fun a => !atomQuiet a) (q := fun _ _ => false) body
    (blockNextOk_of_atomsAll body h')
  rw [hw] at hp
  intro a ha
  by_contra hc
  obtain ⟨b, -, hb⟩ := hp a ha (by simpa using hc)
  exact absurd hb (by simp)

/-! ## Leaves pinned by their atoms -/

/-- **A straight leaf whose hints its atoms pin completes where its relation holds**, quiet. -/
theorem callCompletes_leaf_pinned {k : ℕ} {name : String} {fn : Fn} {args rets : List E}
    {Pre : Reader → Prop} (hfind : coreProgram.find? name = some fn)
    (hck : ((retOf fn.body).isSome && (atomsOf fn.body).all atomQuiet) = true)
    (hrel : ∀ rd, LowDef k rd → Pre rd → coreProgram.Rel rd name args rets)
    (hpin : ∀ rd σ, LowDef k rd → Pre rd → fn.params.map σ = args →
      (∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ) → ∀ a, Stmt.atom a ∈ fn.body → a.Exact rd σ) :
    CallCompletes k name args rets Pre PostQuiet := by
  simp only [Bool.and_eq_true] at hck
  obtain ⟨hr, hh⟩ := hck
  obtain ⟨vs, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  have hmem : ∀ a, Stmt.atom a ∈ ss → Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody]; exact List.mem_append_left _ ha
  have hq : (atomsOf ss).all atomQuiet = true := List.all_eq_true.mpr fun a ha =>
    List.all_eq_true.mp hh a (mem_atomsOf' (hmem a (mem_of_mem_atomsOf ha)))
  let P : Reader → Val → Prop := fun rd σ =>
    fn.params.map σ = args ∧ Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun rs => rs = rets)
  refine callCompletes_straightRd (fun rd => Classical.epsilon (P rd)) hfind hbody hss hq
    fun rd hl hP => ?_
  have hspec := Classical.epsilon_spec (p := P rd) ((rel_iff_sem hfind _ _).mp (hrel rd hl hP))
  generalize Classical.epsilon (P rd) = σ at hspec ⊢
  obtain ⟨hp, hH⟩ := hspec
  rw [hbody, holdsList_append, holdsList_atoms hss] at hH
  obtain ⟨hA, hret⟩ := hH
  simp only [Stmt.HoldsList, Stmt.Holds] at hret
  have hA' : ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ := fun a ha => by
    rw [hbody] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hA a ha
    · simp at ha
  exact ⟨hp, hret, fun a ha => ⟨hA a ha, hpin rd σ hl hP hp hA' a (hmem a ha)⟩⟩

/-- **A straight body with no witness hint completes on a valuation per memory**, given by an
existence: its parameters the arguments, its returns `rets`, each atom holding and exact. -/
theorem callCompletes_straight_ex {k : ℕ} {name : String} {fn : Fn} {args rets : List E}
    {Pre : Reader → Prop} (hfind : coreProgram.find? name = some fn)
    (hck : ((retOf fn.body).isSome && (atomsOf fn.body).all atomQuiet) = true)
    (h : ∀ rd, LowDef k rd → Pre rd → ∃ σ : Val, fn.params.map σ = args ∧
      (∀ vs, retOf fn.body = some vs → vs.map σ = rets) ∧
      ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ ∧ a.Exact rd σ) :
    CallCompletes k name args rets Pre PostQuiet := by
  simp only [Bool.and_eq_true] at hck
  obtain ⟨hr, hh⟩ := hck
  obtain ⟨vs, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  have hmem : ∀ a, Stmt.atom a ∈ ss → Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody]; exact List.mem_append_left _ ha
  have hq : (atomsOf ss).all atomQuiet = true := List.all_eq_true.mpr fun a ha =>
    List.all_eq_true.mp hh a (mem_atomsOf' (hmem a (mem_of_mem_atomsOf ha)))
  let P : Reader → Val → Prop := fun rd σ => fn.params.map σ = args ∧
    (∀ vs, retOf fn.body = some vs → vs.map σ = rets) ∧
    ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ ∧ a.Exact rd σ
  refine callCompletes_straightRd (fun rd => Classical.epsilon (P rd)) hfind hbody hss hq
    fun rd hl hP => ?_
  obtain ⟨hp, hv, ha⟩ := Classical.epsilon_spec (p := P rd) (h rd hl hP)
  exact ⟨hp, hv vs hr, fun a h' => ha a (hmem a h')⟩

/-- The atoms of a straight body holding as a block hold one by one. -/
theorem atoms_of_holdsList {C : CallRel} {rd : Reader} {σ : Val} {B : List Stmt} {vs : List V}
    {kret : List E → Prop} (hr : retOf B = some vs) (h : Stmt.HoldsList C rd σ B False kret) :
    ∀ a, Stmt.atom a ∈ B → a.Holds rd σ := by
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  rw [hbody, holdsList_append, holdsList_atoms hss] at h
  intro a ha
  rw [hbody] at ha
  rcases List.mem_append.mp ha with ha | ha
  · exact h.1 a ha
  · simp at ha

end
end LeanVM.Guest.B1.VsC
