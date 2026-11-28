/-
  LeanVM.Guest.B1.VsC.Fwd

  A straight body of atoms completes on the valuation its forward evaluation gives on each memory.
-/

module

public import LeanVM.Guest.B1.VsC.Atoms
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.B1.Common.Atoms
public import LeanVM.Guest.CoreLemmas
public import LeanVM.Guest.Complete.Call0

/-!
# Straight bodies, evaluated per memory

`callCompletes_straightRd`: a body `ss ++ [.ret vs]`, `ss` atoms with no witness hint, completes
when on every memory `Pre` admits some valuation `σ rd` takes the parameters to the arguments and
`vs` to the returns, its atoms holding and exact. The tree pops nothing and is exact (`PostQuiet`).
A body with no call fixes nothing before the memory, so the valuation may read it.

`fwdVal rd w args body`: the forward evaluation (`Fwd.ev`) on `rd`, with the oracle `w` for the
hints; `fwd_good` gives each atom's defining equation (`Fwd.Good`), `fwd_params` the parameters,
`fwd_holds` each atom from its side condition (`Fwd.Side`: a load's word defined, a store's word
in memory, an assertion).

`callCompletes_pure`: a body of atoms then a `ret` with no assertion, hint or store, every load
through a parameter array the memory holds (`pureChecks`, decided by the kernel per function),
completes when its relation pins its returns (`hrets`, from the soundness stream's meaning): the
forward valuation satisfies the relation, so its returns are the pinned ones.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd

@[expose] public section

/-- An atom that pops nothing: no witness hint. -/
def atomQuiet : Atom → Bool
  | .hint (.witness ..) => false
  | _ => true

/-- The atoms of a block. -/
def atomsOf : List Stmt → List Atom
  | [] => []
  | .atom a :: ss => a :: atomsOf ss
  | _ :: ss => atomsOf ss

theorem eq_map_atomsOf : ∀ {ss : List Stmt}, AllAtoms ss → ss = (atomsOf ss).map Stmt.atom
  | [], _ => rfl
  | s :: ss, h => by
    obtain ⟨a, rfl⟩ := h s List.mem_cons_self
    simp only [atomsOf, List.map_cons]
    rw [← eq_map_atomsOf (fun t ht => h t (List.mem_cons_of_mem _ ht))]

theorem mem_of_mem_atomsOf : ∀ {ss : List Stmt} {a : Atom}, a ∈ atomsOf ss → Stmt.atom a ∈ ss
  | [], _, h => by simp [atomsOf] at h
  | s :: ss, a, h => by
    cases s with
    | atom b =>
      simp only [atomsOf, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_mem_atomsOf h)
    | _ => exact List.mem_cons_of_mem _ (mem_of_mem_atomsOf (by simpa [atomsOf] using h))

theorem mem_atomsOf' {a : Atom} : ∀ {ss : List Stmt}, Stmt.atom a ∈ ss → a ∈ atomsOf ss
  | [], h => by simp at h
  | s :: ss, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · simp [atomsOf]
    · have ih := mem_atomsOf' h'
      cases s with
      | atom b => exact List.mem_cons_of_mem _ ih
      | _ => exact ih

theorem splice_quiet {rd : Reader} {σ : Val} :
    ∀ (as : List Atom), as.all atomQuiet = true → ∀ ks, splice rd σ (as.map Ev.atom) ks = []
  | [], _, ks => by cases ks <;> rfl
  | a :: as, h, ks => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, splice]
    rw [splice_quiet as h.2 ks]
    cases a with
    | hint hh => cases hh <;> simp_all [atomQuiet, Atom.pops, Hint.pops]
    | _ => rfl

/-- **A straight body completes on a valuation per memory**, with no words of its own, popping
nothing, exact. -/
theorem callCompletes0_straightRd {k : ℕ} {name : String} {fn : Fn} {ss : List Stmt} {vs : List V}
    {args rets : List E} {Pre : Reader → Prop} (σ : Reader → Val)
    (hfind : coreProgram.find? name = some fn) (hbody : fn.body = ss ++ [.ret vs]) (hss : AllAtoms ss)
    (hq : (atomsOf ss).all atomQuiet = true)
    (h : ∀ rd, LowDef k rd → Pre rd → fn.params.map (σ rd) = args ∧ vs.map (σ rd) = rets ∧
      ∀ a, Stmt.atom a ∈ ss → a.Holds rd (σ rd) ∧ a.Exact rd (σ rd)) :
    CallCompletes0 k name args rets Pre PostQuiet := by
  intro rd hl hP
  obtain ⟨hp, hr, ha⟩ := h rd hl hP
  have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs] := by rw [hbody, ← eq_map_atomsOf hss]
  have hw : walk (σ rd) fn.body = .ret ((atomsOf ss).map Ev.atom) vs := by
    rw [hb']; exact walk_atoms _ _ vs
  have hev : ∀ bufs, Tree.events coreProgram (.node name (σ rd) bufs []) = (atomsOf ss).map Ev.atom := by
    intro bufs; simp only [Tree.events, Tree.name, Tree.val, hfind, hw]
  refine ⟨.node name (σ rd) (allocs (σ rd) ((atomsOf ss).map Ev.atom)) [], rfl,
    ⟨fn, hfind, hp, (atomsOf ss).map Ev.atom, vs, hw, hr,
      holds_atoms fun a h' => (ha a (mem_of_mem_atomsOf h')).1, ?_⟩, ?_, ?_, ?_⟩
  · rw [calls_atoms, Tree.KidsValid]; trivial
  · rw [Tree.BufsOk, hev]; exact ⟨rfl, by rw [Tree.BufsOkKids]; trivial⟩
  · rw [Tree.pops_node (P := coreProgram) hfind hw]; exact splice_quiet _ hq _
  · rw [Tree.every_node]
    refine ⟨fun e he => ?_, by rw [Tree.EveryKids]; trivial⟩
    rw [hev] at he
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp he
    exact (ha a (mem_of_mem_atomsOf ha')).2

/-- **A straight body completes on a valuation per memory**, popping nothing, exact. -/
theorem callCompletes_straightRd {k : ℕ} {name : String} {fn : Fn} {ss : List Stmt} {vs : List V}
    {args rets : List E} {Pre : Reader → Prop} (σ : Reader → Val)
    (hfind : coreProgram.find? name = some fn) (hbody : fn.body = ss ++ [.ret vs]) (hss : AllAtoms ss)
    (hq : (atomsOf ss).all atomQuiet = true)
    (h : ∀ rd, LowDef k rd → Pre rd → fn.params.map (σ rd) = args ∧ vs.map (σ rd) = rets ∧
      ∀ a, Stmt.atom a ∈ ss → a.Holds rd (σ rd) ∧ a.Exact rd (σ rd)) :
    CallCompletes k name args rets Pre PostQuiet :=
  (callCompletes0_straightRd σ hfind hbody hss hq h).toCallCompletes

/-! ## Forward evaluation -/

/-- The valuation of a straight body evaluated forward on `rd`, the hints' words from `w`. -/
noncomputable def fwdVal (rd : Reader) (w : ℕ → E) (args : List E) (body : List Stmt) : Val :=
  B1.Val.ofArgs (ev rd w args body)

section

variable {rd : Reader} {w : ℕ → E} {args : List E} {body : List Stmt} {c' : ℕ}

/-- Each atom's defining equation. -/
theorem fwd_good (h : chk args.length body = some c') :
    ∀ a, Stmt.atom a ∈ body → Good rd (storesOf args.length body) w (fwdVal rd w args body) a :=
  fun _ ha => (ev_spec rd w body args h).2.2 _ ha

/-- The parameters `.n 0, …` keep the arguments. -/
theorem fwd_params (h : chk args.length body = some c') :
    ((List.range args.length).map V.n).map (fwdVal rd w args body) = args := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply]
  rw [fwdVal, ev_params rd w h h2, List.getD_eq_getElem _ _ h2]

/-- Parameter `i`'s word. -/
theorem fwd_param (h : chk args.length body = some c') {i : ℕ} (hi : i < args.length) :
    fwdVal rd w args body (.n i) = args.getD i 0 := ev_params rd w h hi

/-- **Each atom holds** given its side condition where it needs one. -/
theorem fwd_holds (h : chk args.length body = some c')
    (hs : ∀ a, Stmt.atom a ∈ body → needsSide a = true →
      a.Holds rd (fwdVal rd w args body) ∨ Side rd (storesOf args.length body) (fwdVal rd w args body) a) :
    ∀ a, Stmt.atom a ∈ body → a.Holds rd (fwdVal rd w args body) := by
  intro a ha
  have hb := atoms_holds (S := storesOf args.length body) (w := w) (rd := rd)
    (σ := fwdVal rd w args body) (atoms := [a]) (fun b hb => by
      rw [List.mem_singleton] at hb; subst hb; exact fwd_good h b ha)
    (fun b hb hn => by rw [List.mem_singleton] at hb; subst hb; exact hs b ha hn)
  exact hb a List.mem_cons_self

end

section Eqs

variable {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

theorem good_load_eq {d p : V} {off : ℕ} {x : E} (hm : LoadHolds rd (σ p) off x)
    (hg : Good rd S w σ (.load d p off)) (hS : Atom.load d p off ∉ S) : σ d = x := by
  have hg' : Atom.load d p off ∈ S ∨ σ d = rdAt rd (σ p) off := hg
  rw [hg'.resolve_left hS, rdAt, hm.2]
  rfl

theorem good_mul_eq {d x y : V} (hg : Good rd S w σ (.mul d x y)) (hx : x.idx < d.idx) (hy : y.idx < d.idx) :
    σ d = σ x * σ y := by
  have hg' : if x.idx < d.idx ∧ y.idx < d.idx then σ d = σ x * σ y else σ x = σ d * (σ y)⁻¹ := hg
  simpa [hx, hy] using hg'

end Eqs

/-! ## Pure bodies -/

/-- The returns of a body of atoms then a `ret`. -/
def retOf : List Stmt → Option (List V)
  | [.ret vs] => some vs
  | .atom _ :: ss => retOf ss
  | _ => none

theorem retOf_spec : ∀ {B : List Stmt} {vs : List V}, retOf B = some vs → ∃ ss, B = ss ++ [.ret vs] ∧ AllAtoms ss
  | [], _, h => by simp [retOf] at h
  | [.ret ws], vs, h => by
    simp only [retOf, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, allAtoms_nil⟩
  | .atom a :: ss, vs, h => by
    obtain ⟨ss', rfl, hs⟩ := retOf_spec (B := ss) h
    refine ⟨.atom a :: ss', rfl, fun s hs' => ?_⟩
    rcases List.mem_cons.mp hs' with rfl | hs'
    · exact ⟨a, rfl⟩
    · exact hs s hs'
  | .ret _ :: _ :: _, _, h => by simp [retOf] at h
  | .ite .. :: _, _, h | .match_ .. :: _, _, h | .call .. :: _, _, h | .callIf .. :: _, _, h
  | .dispatch .. :: _, _, h => by simp [retOf] at h

/-- A load through parameter `q.1` below offset `q.2`, `q ∈ ps`; no hint; any other atom needs no
side condition. -/
def loadOkB (ps : List (ℕ × ℕ)) : Atom → Bool
  | .load _ p k => ps.any fun q => p == .n q.1 && decide (k < q.2)
  | .hint _ => false
  | a => !needsSide a

/-- What the kernel checks of a pure body on `n` parameters reading the arrays `ps`. -/
def pureChecks (n : ℕ) (ps : List (ℕ × ℕ)) (B : List Stmt) : Bool :=
  (chk n B).isSome && (storesOf n B).isEmpty && (atomsOf B).all (loadOkB ps) && (retOf B).isSome

theorem readsAt_eq {rd : Reader} {p : E} {l l' : List E} (h : ReadsAt rd p l) (h' : ReadsAt rd p l')
    (hl : l.length = l'.length) : l = l' :=
  List.ext_getElem hl fun i h1 h2 => loadHolds_unique (h i h1) (h' i h2)

theorem readsAt_prefix {rd : Reader} {p : E} {l l' : List E} (h : ReadsAt rd p (l ++ l')) : ReadsAt rd p l :=
  fun i hi => by
    have := h i (by simp; omega)
    rwa [List.getElem_append_left hi] at this

theorem readsAt_last {rd : Reader} {p : E} {l : List E} {x : E} (h : ReadsAt rd p (l ++ [x])) :
    LoadHolds rd p l.length x := by
  have := h l.length (by simp)
  rwa [List.getElem_append_right (by omega), List.getElem_singleton] at this

/-- **A pure body whose relation pins its returns completes** with no words of its own, popping
nothing, exact. -/
theorem callCompletes0_pure {k : ℕ} {name : String} {fn : Fn} {args rets : List E} {Pre : Reader → Prop}
    (ps : List (ℕ × ℕ)) (hfind : coreProgram.find? name = some fn)
    (hparams : fn.params = (List.range args.length).map V.n) (hck : pureChecks args.length ps fn.body = true)
    (hargs : ∀ q ∈ ps, q.1 < args.length)
    (hpre : ∀ rd, LowDef k rd → Pre rd → ∀ q ∈ ps, ∃ l : List E, q.2 ≤ l.length ∧ ReadsAt rd (args.getD q.1 0) l)
    (hrets : ∀ rd, LowDef k rd → Pre rd → ∀ rets', coreProgram.Rel rd name args rets' → rets' = rets) :
    CallCompletes0 k name args rets Pre PostQuiet := by
  simp only [pureChecks, Bool.and_eq_true, List.isEmpty_iff] at hck
  obtain ⟨⟨⟨hc, hS⟩, hL⟩, hr⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨vs, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  have hmem : ∀ a, Stmt.atom a ∈ ss → Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody]; exact List.mem_append_left _ ha
  have hok : ∀ a, Stmt.atom a ∈ fn.body → loadOkB ps a = true := fun a ha =>
    List.all_eq_true.mp hL a (mem_atomsOf' ha)
  have hq : (atomsOf ss).all atomQuiet = true := List.all_eq_true.mpr fun a ha => by
    have := hok a (hmem a (mem_of_mem_atomsOf ha))
    cases a with
    | hint hh => simp [loadOkB] at this
    | _ => rfl
  refine callCompletes0_straightRd (fun rd => fwdVal rd (fun _ => 0) args fn.body) hfind hbody hss hq
    fun rd hl hP => ?_
  set σ := fwdVal rd (fun _ => 0) args fn.body with hσ
  have hA : ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ := by
    refine fwd_holds hc fun a ha hn => Or.inr ?_
    have hk := hok a ha
    cases a with
    | load d p off =>
      simp only [loadOkB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
      obtain ⟨q, hqm, rfl, hoff⟩ := hk
      obtain ⟨l, hlen, hrd⟩ := hpre rd hl hP q hqm
      have hm := hrd off (by omega)
      simp only [Side, hS, List.not_mem_nil, ↓reduceIte]
      rw [show fwdVal rd (fun _ => 0) args fn.body (.n q.1) = args.getD q.1 0 from
        fwd_param hc (hargs q hqm)]
      exact ⟨hm.1, by rw [hm.2]; rfl⟩
    | hint hh => simp [loadOkB] at hk
    | _ => simp only [loadOkB, hn, Bool.not_true, Bool.false_eq_true] at hk
  have hp : fn.params.map σ = args := by rw [hparams]; exact fwd_params hc
  have hR : coreProgram.Rel rd name args (vs.map σ) := by
    refine (rel_iff_sem hfind _ _).mpr ⟨σ, hp, ?_⟩
    rw [hbody, holdsList_append]
    refine ((holdsList_atoms hss _ _).mpr ⟨fun a ha => hA a (hmem a ha), ?_⟩)
    simp [Stmt.HoldsList, Stmt.Holds]
  refine ⟨hp, hrets rd hl hP _ hR, fun a ha => ⟨hA a (hmem a ha), ?_⟩⟩
  have := hok a (hmem a ha)
  cases a with
  | hint hh => simp [loadOkB] at this
  | _ => trivial

/-- **A pure body whose relation pins its returns completes**, popping nothing, exact. -/
theorem callCompletes_pure {k : ℕ} {name : String} {fn : Fn} {args rets : List E} {Pre : Reader → Prop}
    (ps : List (ℕ × ℕ)) (hfind : coreProgram.find? name = some fn)
    (hparams : fn.params = (List.range args.length).map V.n) (hck : pureChecks args.length ps fn.body = true)
    (hargs : ∀ q ∈ ps, q.1 < args.length)
    (hpre : ∀ rd, LowDef k rd → Pre rd → ∀ q ∈ ps, ∃ l : List E, q.2 ≤ l.length ∧ ReadsAt rd (args.getD q.1 0) l)
    (hrets : ∀ rd, LowDef k rd → Pre rd → ∀ rets', coreProgram.Rel rd name args rets' → rets' = rets) :
    CallCompletes k name args rets Pre PostQuiet :=
  (callCompletes0_pure ps hfind hparams hck hargs hpre hrets).toCallCompletes

/-- What the kernel checks of a straight body with no hint. -/
def straightChecks (B : List Stmt) : Bool := (retOf B).isSome && (atomsOf B).all noHint

/-- **A straight body with no hint completes where its relation holds**: a valuation the relation
gives, per memory. -/
theorem callCompletes_of_rel_straight {k : ℕ} {name : String} {fn : Fn} {args rets : List E}
    {Pre : Reader → Prop} (hfind : coreProgram.find? name = some fn) (hck : straightChecks fn.body = true)
    (hrel : ∀ rd, LowDef k rd → Pre rd → coreProgram.Rel rd name args rets) :
    CallCompletes k name args rets Pre PostQuiet := by
  simp only [straightChecks, Bool.and_eq_true] at hck
  obtain ⟨hr, hh⟩ := hck
  obtain ⟨vs, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  have hmem : ∀ a, Stmt.atom a ∈ ss → Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody]; exact List.mem_append_left _ ha
  have hnh : ∀ a, Stmt.atom a ∈ ss → noHint a = true := fun a ha =>
    List.all_eq_true.mp hh a (mem_atomsOf' (hmem a ha))
  have hq : (atomsOf ss).all atomQuiet = true := List.all_eq_true.mpr fun a ha => by
    have := hnh a (mem_of_mem_atomsOf ha)
    cases a with
    | hint _ => simp [noHint] at this
    | _ => rfl
  let P : Reader → Val → Prop := fun rd σ =>
    fn.params.map σ = args ∧ Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun rs => rs = rets)
  refine callCompletes_straightRd (fun rd => Classical.epsilon (P rd)) hfind hbody hss hq fun rd hl hP => ?_
  have hspec := Classical.epsilon_spec (p := P rd) ((rel_iff_sem hfind _ _).mp (hrel rd hl hP))
  generalize Classical.epsilon (P rd) = σ at hspec ⊢
  obtain ⟨hp, hH⟩ := hspec
  rw [hbody, holdsList_append, holdsList_atoms hss] at hH
  obtain ⟨hA, hret⟩ := hH
  simp only [Stmt.HoldsList, Stmt.Holds] at hret
  refine ⟨hp, hret, fun a ha => ⟨hA a ha, ?_⟩⟩
  have := hnh a ha
  cases a with
  | hint _ => simp [noHint] at this
  | _ => trivial

/-- **`callCompletes_of_rel_straight` with no words of its own.** -/
theorem callCompletes0_of_rel_straight {k : ℕ} {name : String} {fn : Fn} {args rets : List E}
    {Pre : Reader → Prop} (hfind : coreProgram.find? name = some fn) (hck : straightChecks fn.body = true)
    (hrel : ∀ rd, LowDef k rd → Pre rd → coreProgram.Rel rd name args rets) :
    CallCompletes0 k name args rets Pre PostQuiet := by
  simp only [straightChecks, Bool.and_eq_true] at hck
  obtain ⟨hr, hh⟩ := hck
  obtain ⟨vs, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  have hmem : ∀ a, Stmt.atom a ∈ ss → Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody]; exact List.mem_append_left _ ha
  have hnh : ∀ a, Stmt.atom a ∈ ss → noHint a = true := fun a ha =>
    List.all_eq_true.mp hh a (mem_atomsOf' (hmem a ha))
  have hq : (atomsOf ss).all atomQuiet = true := List.all_eq_true.mpr fun a ha => by
    have := hnh a (mem_of_mem_atomsOf ha)
    cases a with
    | hint _ => simp [noHint] at this
    | _ => rfl
  let P : Reader → Val → Prop := fun rd σ =>
    fn.params.map σ = args ∧ Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun rs => rs = rets)
  refine callCompletes0_straightRd (fun rd => Classical.epsilon (P rd)) hfind hbody hss hq fun rd hl hP => ?_
  have hspec := Classical.epsilon_spec (p := P rd) ((rel_iff_sem hfind _ _).mp (hrel rd hl hP))
  generalize Classical.epsilon (P rd) = σ at hspec ⊢
  obtain ⟨hp, hH⟩ := hspec
  rw [hbody, holdsList_append, holdsList_atoms hss] at hH
  obtain ⟨hA, hret⟩ := hH
  simp only [Stmt.HoldsList, Stmt.Holds] at hret
  refine ⟨hp, hret, fun a ha => ⟨hA a ha, ?_⟩⟩
  have := hnh a ha
  cases a with
  | hint _ => simp [noHint] at this
  | _ => trivial

end
end LeanVM.Guest.B1.VsC
