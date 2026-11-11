/-
  LeanVM.Guest.Memory.Retemp

  Re-choosing the temporaries of a call tree (range checks' and touches' cells): the same paths,
  `HeapBuf`s, placement, data and loads, valid on any reader that agrees with the old one on
  every other word the paths read and holds the new temporaries where their atoms read.
-/

module

public import LeanVM.Guest.Memory.Regions
public import LeanVM.Guest.Memory.Fresh

/-!
# Re-choosing temporaries

In a program whose temporaries are fresh (`Program.Fresh`), nothing but its own atom (a range
check, a touch) reads a temporary, so a tree stays valid when they change, provided the memory
holds the new values where those atoms read (`tmpReads`). `Tree.retemp P fs ν fp t` replaces,
in every instance of
`t` placed from `fp`, the value of each temporary `v` of its function `f` by `ν fp f σ v`, `σ`
its old valuation (`retempVal`).

* `retemp_valid`: if `t` is valid on `rd0` and `rd` agrees with `rd0` on every word a path reads
  except at the temporaries' atoms, and holds the new temporaries where those read
  (`Tree.ReadsAs`), the re-chosen tree is valid on `rd`;
* it keeps the name, the size, the `HeapBuf`s, the placement, the data and the loads
  (`name_retemp`, `total_retemp`, `bufsOk_retemp`, `placed_retemp`, `data_retemp`,
  `loadsIn_retemp`, `loadsR_retemp`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## Congruences -/

section Congr

variable {rd rd0 : Reader} {σ σ' : Val}

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
      rw [List.filterMap_cons, List.filterMap_cons, h a List.mem_cons_self,
        filterMap_congr' fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- An atom's relation depends only on the values it names. -/
theorem atom_holds_congr : ∀ (a : Atom), (∀ v ∈ atomUses a ++ atomTmps a, σ' v = σ v) →
    (a.Holds rd σ' ↔ a.Holds rd σ)
  | .const d c, h => by simp only [Atom.Holds, h d (by simp [atomUses])]
  | .add d x y, h => by
      simp only [Atom.Holds, h d (by simp [atomUses]), h x (by simp [atomUses]), h y (by simp [atomUses])]
  | .mul d x y, h => by
      simp only [Atom.Holds, h d (by simp [atomUses]), h x (by simp [atomUses]), h y (by simp [atomUses])]
  | .copy d s, h => by simp only [Atom.Holds, h d (by simp [atomUses]), h s (by simp [atomUses])]
  | .load d p off, h => by
      simp only [Atom.Holds, LoadHolds, h d (by simp [atomUses]), h p (by simp [atomUses])]
  | .assertEq x y, h => by simp only [Atom.Holds, h x (by simp [atomUses]), h y (by simp [atomUses])]
  | .assertNe x inv p, h => by
      simp only [Atom.Holds, h x (by simp [atomUses]), h inv (by simp [atomUses]),
        h p (by simp [atomUses])]
  | .rangeCheck x y t1 t2 k, h => by
      simp only [Atom.Holds, LoadHolds, h x (by simp [atomUses]), h y (by simp [atomUses]),
        h t1 (by simp [atomTmps]), h t2 (by simp [atomTmps]), h k (by simp [atomUses])]
  | .assertInK x y, h => by simp only [Atom.Holds, h x (by simp [atomUses]), h y (by simp [atomUses])]
  | .keccak ins outs inOdd outOdd, h => by
      have hi : ins.map σ' = ins.map σ :=
        List.map_congr_left fun v hv => h v (by simp [atomUses, hv])
      have ho : outs.map σ' = outs.map σ :=
        List.map_congr_left fun v hv => h v (by simp [atomUses, hv])
      simp only [Atom.Holds, hi, ho]
  | .frameAddr p run, h => by
      have hp := h p (by simp [atomUses])
      have hr : ∀ (k : ℕ) (hk : k < run.length), σ' run[k] = σ run[k] := fun k hk =>
        h _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.getElem_mem hk)))
      simp only [Atom.Holds, hp]
      exact and_congr_right fun _ => forall_congr' fun k => forall_congr' fun hk =>
        forall_congr' fun w => by rw [hr k hk]
  | .hint _, _ => Iff.rfl
  | .touch t p, h => by
      simp only [Atom.Holds, LoadHolds, h t (by simp [atomTmps]), h p (by simp [atomUses])]

/-- An atom holds on any reader agreeing with one it holds on where it reads. -/
theorem atom_holds_agree : ∀ (a : Atom), a.Holds rd0 σ →
    (∀ q ∈ atomEqns σ a, rd q.1 = rd0 q.1) → a.Holds rd σ
  | .load .., h, he => ⟨h.1, (he _ (List.mem_singleton_self _)).trans h.2⟩
  | .rangeCheck .., h, he =>
      ⟨⟨h.1.1, (he _ List.mem_cons_self).trans h.1.2⟩, h.2.1,
        ⟨h.2.2.1, (he _ (List.mem_cons_of_mem _ List.mem_cons_self)).trans h.2.2.2⟩⟩
  | .touch .., h, he => ⟨h.1, (he _ (List.mem_singleton_self _)).trans h.2⟩
  | .frameAddr p run, h, he => ⟨h.1, fun k hk w hw => h.2 k hk w <| by
      have hm : ((σ p).limb 0 * addressOfIndex k, σ run[k]) ∈ atomEqns σ (.frameAddr p run) :=
        List.mem_mapIdx.mpr ⟨k, hk, rfl⟩
      exact (he _ hm).symm.trans hw⟩
  | .const .., h, _ => h
  | .add .., h, _ => h
  | .mul .., h, _ => h
  | .copy .., h, _ => h
  | .assertEq .., h, _ => h
  | .assertNe .., h, _ => h
  | .assertInK .., h, _ => h
  | .keccak .., h, _ => h
  | .hint _, h, _ => h

/-- **An atom's temporary reads**: a range check's two and a touch's one, each temporary with
the address it reads. -/
def tmpReads (σ : Val) : Atom → List (V × K)
  | .rangeCheck x y t1 t2 _ =>
      [(t1, (σ x).limb 0 * addressOfIndex 0), (t2, (σ y).limb 0 * addressOfIndex 0)]
  | .touch t p => [(t, (σ p).limb 0 * addressOfIndex 0)]
  | _ => []

theorem tmpReads_fst (a : Atom) : (tmpReads σ a).map Prod.fst = atomTmps a := by
  cases a <;> rfl

theorem mem_atomTmps_of_tmpReads {a : Atom} {r : V × K} (hr : r ∈ tmpReads σ a) :
    r.1 ∈ atomTmps a := by
  rw [← tmpReads_fst (σ := σ)]
  exact List.mem_map_of_mem (f := Prod.fst) hr

theorem tmpReads_congr (a : Atom) (h : ∀ v ∈ atomUses a, σ' v = σ v) :
    tmpReads σ' a = tmpReads σ a := by
  cases a
  case rangeCheck x y t1 t2 k =>
    simp only [tmpReads, h x (by simp [atomUses]), h y (by simp [atomUses])]
  case touch t p => simp only [tmpReads, h p (by simp [atomUses])]
  all_goals rfl

/-- A temporary read is an equation of its atom. -/
theorem tmpReads_eqn {a : Atom} {r : V × K} (hr : r ∈ tmpReads σ a) :
    (r.2, σ r.1) ∈ atomEqns σ a := by
  cases a
  case rangeCheck x y t1 t2 k =>
    simp only [tmpReads, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  case touch t p =>
    rw [List.mem_singleton.mp hr]
    exact List.mem_singleton_self _
  all_goals exact (List.not_mem_nil hr).elim

/-- The equations of an atom with temporaries are its temporary reads. -/
theorem eqn_tmpReads {a : Atom} (ht : atomTmps a ≠ []) {q : K × E} (hq : q ∈ atomEqns σ a) :
    ∃ r ∈ tmpReads σ a, q = (r.2, σ r.1) := by
  cases a
  case rangeCheck x y t1 t2 k =>
    simp only [atomEqns, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨_, List.mem_cons_self, rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  case touch t p =>
    exact ⟨_, List.mem_singleton_self _, List.mem_singleton.mp hq⟩
  all_goals simp [atomTmps] at ht

/-- An atom reads its temporaries where it holds. -/
theorem tmpReads_read {a : Atom} (h : a.Holds rd σ) {r : V × K} (hr : r ∈ tmpReads σ a) :
    rd r.2 = some (σ r.1) := by
  cases a
  case rangeCheck x y t1 t2 k =>
    simp only [tmpReads, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.2
    · exact h.2.2.2
  case touch t p =>
    rw [List.mem_singleton.mp hr]
    exact h.2
  all_goals exact (List.not_mem_nil hr).elim

/-- **An atom with temporaries holds on a new reader** holding the new temporaries where it
reads, its other values unchanged. -/
theorem holds_of_tmpReads {a : Atom} (ht : atomTmps a ≠ []) (h : a.Holds rd0 σ)
    (hu : ∀ v ∈ atomUses a, σ' v = σ v) (hr : ∀ r ∈ tmpReads σ a, rd r.2 = some (σ' r.1)) :
    a.Holds rd σ' := by
  cases a
  case rangeCheck x y t1 t2 k =>
    have hx := hu x (by simp [atomUses])
    have hy := hu y (by simp [atomUses])
    have hk := hu k (by simp [atomUses])
    have r1 := hr _ List.mem_cons_self
    have r2 := hr _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only at r1 r2
    simp only [Atom.Holds, LoadHolds, hx, hy, hk]
    exact ⟨⟨h.1.1, r1⟩, h.2.1, ⟨h.2.2.1, r2⟩⟩
  case touch t p =>
    have hp := hu p (by simp [atomUses])
    have r1 := hr _ (List.mem_singleton_self _)
    simp only at r1
    simp only [Atom.Holds, LoadHolds, hp]
    exact ⟨h.1, r1⟩
  all_goals simp [atomTmps] at ht

/-- A path whose events' values agree under two valuations. -/
def EvAgree (σ σ' : Val) (es : List Ev) : Prop := ∀ e ∈ es, ∀ v ∈ e.uses, σ' v = σ v

theorem allocs_congr {es : List Ev} (h : EvAgree σ σ' es) : allocs σ' es = allocs σ es := by
  refine filterMap_congr' fun e he => ?_
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ | _⟩ | _ | _ | _ <;>
    try rfl
  rename_i d s
  simp only [Ev.alloc?, h _ he s (by simp [Ev.uses, atomUses, hintUses])]

theorem allocDsts_congr {es : List Ev} (h : EvAgree σ σ' es) :
    (allocDsts es).map σ' = (allocDsts es).map σ := by
  refine List.map_congr_left fun d hd => ?_
  obtain ⟨e, he, hed⟩ := List.mem_filterMap.mp hd
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ | _⟩ | _ | _ | _ <;>
    simp only [Ev.allocDst?, reduceCtorEq, Option.some.injEq] at hed
  · subst hed; exact h _ he _ (by simp [Ev.uses, atomUses, hintUses])
  · subst hed; exact h _ he _ (by simp [Ev.uses, atomUses, hintUses])

theorem addrs_congr {es : List Ev} (h : EvAgree σ σ' es) : ∀ q ∈ addrs es, σ' q.1 = σ q.1 := by
  intro q hq
  obtain ⟨e, he, heq⟩ := List.mem_filterMap.mp hq
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨p, _ | ⟨r, rs⟩⟩ | _ | _⟩ | _ | _ | _ <;>
    simp only [Ev.addr?, reduceCtorEq, Option.some.injEq] at heq
  subst heq
  exact h _ he p (by simp [Ev.uses, atomUses])

theorem loadAddrs_congr {es : List Ev} (h : EvAgree σ σ' es) : loadAddrs σ' es = loadAddrs σ es := by
  refine filterMap_congr' fun e he => ?_
  cases e with
  | atom a =>
      cases a with
      | load d p off => simp only [Ev.loadAddr?, h _ he p (by simp [Ev.uses, atomUses])]
      | _ => rfl
  | _ => rfl

end Congr

/-! ## The re-chosen tree -/

variable (P : Core.Program) (fs : String → ℕ) (ν : ℕ → String → Val → V → E)

/-- The valuation of an instance of `f` at `fp` with its temporaries re-chosen. -/
def retempVal (fp : ℕ) (f : String) (σ : Val) : Val := fun v =>
  if v ∈ P.temps f then ν fp f σ v else σ v

mutual
/-- **The re-chosen tree**: every instance's temporaries re-chosen, placed from `fp`. -/
def Tree.retemp (fp : ℕ) : Tree → Tree
  | .node f σ bufs kids => .node f (retempVal P ν fp f σ) bufs
      (Tree.retempKids (kidPos fs P.loop fp f bufs (kids.map (Tree.total fs))) kids)
  | .phantom f σ => .phantom f σ

/-- The re-chosen callees at `ps`. -/
def Tree.retempKids : List ℕ → List Tree → List Tree
  | _, [] => []
  | [], k :: ks => k :: ks
  | p :: ps, k :: ks => k.retemp p :: Tree.retempKids ps ks
end

variable {P fs ν}

theorem retemp_node {fp : ℕ} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} :
    (Tree.node f σ bufs kids).retemp P fs ν fp = .node f (retempVal P ν fp f σ) bufs
      (Tree.retempKids P fs ν (kidPos fs P.loop fp f bufs (kids.map (Tree.total fs))) kids) := by
  rw [Tree.retemp]

theorem retemp_phantom {fp : ℕ} {f : String} {σ : Val} :
    (Tree.phantom f σ).retemp P fs ν fp = .phantom f σ := by
  rw [Tree.retemp]

theorem retempKids_cons {p : ℕ} {ps : List ℕ} {k : Tree} {ks : List Tree} :
    Tree.retempKids P fs ν (p :: ps) (k :: ks) = k.retemp P fs ν p :: Tree.retempKids P fs ν ps ks := by
  rw [Tree.retempKids]

theorem retempKids_nil {ps : List ℕ} : Tree.retempKids P fs ν ps [] = [] := by
  cases ps <;> rw [Tree.retempKids]

theorem name_retemp (fp : ℕ) : ∀ t : Tree, (t.retemp P fs ν fp).name = t.name
  | .node .. => by rw [retemp_node]; rfl
  | .phantom .. => by rw [retemp_phantom]

mutual
theorem total_retemp : ∀ (t : Tree) (fp : ℕ), (t.retemp P fs ν fp).total fs = t.total fs
  | .node f σ bufs kids, fp => by
      rw [retemp_node, total_node, total_node, totalKids_retempKids kids _
        (by rw [length_kidPos, List.length_map])]
  | .phantom .., fp => by rw [retemp_phantom]

theorem totalKids_retempKids : ∀ (ks : List Tree) (ps : List ℕ), ps.length = ks.length →
    Tree.totalKids fs (Tree.retempKids P fs ν ps ks) = Tree.totalKids fs ks
  | [], _, _ => by rw [retempKids_nil]
  | _ :: _, [], h => absurd h (by simp)
  | k :: ks, p :: ps, h => by
      rw [retempKids_cons, totalKids_cons, totalKids_cons, total_retemp k p,
        totalKids_retempKids ks ps (by simpa using h)]
end

theorem map_total_retempKids : ∀ (ks : List Tree) (ps : List ℕ), ps.length = ks.length →
    (Tree.retempKids P fs ν ps ks).map (Tree.total fs) = ks.map (Tree.total fs)
  | [], _, _ => by rw [retempKids_nil]
  | _ :: _, [], h => absurd h (by simp)
  | k :: ks, p :: ps, h => by
      rw [retempKids_cons, List.map_cons, List.map_cons, total_retemp k p,
        map_total_retempKids ks ps (by simpa using h)]

theorem map_total_retempKids_kidPos {fp : ℕ} {f : String} {bufs : List ℕ} {kids : List Tree} :
    (Tree.retempKids P fs ν (kidPos fs P.loop fp f bufs (kids.map (Tree.total fs))) kids).map
      (Tree.total fs) = kids.map (Tree.total fs) :=
  map_total_retempKids kids _ (by rw [length_kidPos, List.length_map])

/-! ## Paths of a re-chosen tree -/

section Paths

variable {f : String} (hF : P.Fresh)
include hF

/-- A re-chosen valuation agrees with the old one on the body's uses. -/
theorem retempVal_uses {fn : Fn} (hf : P.find? f = some fn) {fp : ℕ} {σ : Val} {v : V}
    (hv : v ∈ Stmt.usesList fn.body) : retempVal P ν fp f σ v = σ v := by
  have hfr := hF fn (List.mem_of_find?_eq_some hf)
  have : v ∉ P.temps f := by
    rw [Program.temps, hf]
    exact fun ht => (hfr.2 v ht).1 hv
  simp only [retempVal, this, ↓reduceIte]

theorem retempVal_params {fn : Fn} (hf : P.find? f = some fn) {fp : ℕ} {σ : Val} :
    fn.params.map (retempVal P ν fp f σ) = fn.params.map σ := by
  have hfr := hF fn (List.mem_of_find?_eq_some hf)
  refine List.map_congr_left fun v hv => ?_
  have : v ∉ P.temps f := by
    rw [Program.temps, hf]
    exact fun ht => (hfr.2 v ht).2 hv
  simp only [retempVal, this, ↓reduceIte]

/-- The re-chosen valuation takes the same path. -/
theorem walk_retemp {fn : Fn} (hf : P.find? f = some fn) {fp : ℕ} {σ : Val} :
    walk (retempVal P ν fp f σ) fn.body = walk σ fn.body :=
  walk_congr fn.body fun _ hv => retempVal_uses hF hf hv

theorem events_retemp {fp : ℕ} {σ : Val} {bufs bufs' : List ℕ} {ks ks' : List Tree} :
    (Tree.node f (retempVal P ν fp f σ) bufs ks).events P = (Tree.node f σ bufs' ks').events P := by
  unfold Tree.events
  simp only [Tree.name, Tree.val]
  cases hf : P.find? f with
  | none => rfl
  | some fn => dsimp only; rw [walk_retemp hF hf]

/-- On a path that returns, the events' values agree. -/
theorem evAgree_retemp {fn : Fn} (hf : P.find? f = some fn) {fp : ℕ} {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) : EvAgree σ (retempVal P ν fp f σ) es := by
  have := walk_within (σ := σ) fn.body
  rw [hw] at this
  exact fun e he v hv => retempVal_uses hF hf (this.1 e he v hv)

end Paths

/-! ## Validity -/

variable (P fs ν) (rd rd0 : Reader)

mutual
/-- **What a reader must give a re-chosen tree**: every atom of a path without temporaries
reads what `rd0` reads, and every temporary read (a range check's, a touch's) reads the new
temporary. -/
def Tree.ReadsAs : ℕ → Tree → Prop
  | fp, t@(.node f σ _ kids) =>
      (∀ a, Ev.atom a ∈ t.events P → atomTmps a = [] → ∀ q ∈ atomEqns σ a, rd q.1 = rd0 q.1) ∧
      (∀ a, Ev.atom a ∈ t.events P → ∀ r ∈ tmpReads σ a, rd r.2 = some (ν fp f σ r.1)) ∧
      Tree.ReadsAsKids (kidPos fs P.loop fp f t.bufs (kids.map (Tree.total fs))) kids
  | _, .phantom .. => True

/-- `Tree.ReadsAs` of the callees at `ps`. -/
def Tree.ReadsAsKids : List ℕ → List Tree → Prop
  | _, [] => True
  | [], _ :: _ => True
  | p :: ps, k :: ks => k.ReadsAs p ∧ Tree.ReadsAsKids ps ks
end

variable {P fs ν rd rd0}

theorem readsAs_node {fp : ℕ} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} :
    (Tree.node f σ bufs kids).ReadsAs P fs ν rd rd0 fp ↔
      (∀ a, Ev.atom a ∈ (Tree.node f σ bufs kids).events P → atomTmps a = [] →
        ∀ q ∈ atomEqns σ a, rd q.1 = rd0 q.1) ∧
      (∀ a, Ev.atom a ∈ (Tree.node f σ bufs kids).events P → ∀ r ∈ tmpReads σ a,
        rd r.2 = some (ν fp f σ r.1)) ∧
      Tree.ReadsAsKids P fs ν rd rd0 (kidPos fs P.loop fp f bufs (kids.map (Tree.total fs))) kids := by
  rw [Tree.ReadsAs]; rfl

theorem readsAsKids_cons {p : ℕ} {ps : List ℕ} {k : Tree} {ks : List Tree} :
    Tree.ReadsAsKids P fs ν rd rd0 (p :: ps) (k :: ks) ↔
      k.ReadsAs P fs ν rd rd0 p ∧ Tree.ReadsAsKids P fs ν rd rd0 ps ks := by
  rw [Tree.ReadsAsKids]

/-- A temporary an atom on a path reads is a temporary of the function. -/
theorem mem_temps_of_event {fn : Fn} {f : String} (hf : P.find? f = some fn) {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) {a : Atom} (he : Ev.atom a ∈ es) {σ' : Val}
    {r : V × K} (hr : r ∈ tmpReads σ' a) : r.1 ∈ P.temps f := by
  have := (walk_within (σ := σ) fn.body)
  rw [hw] at this
  rw [Program.temps, hf]
  exact this.2.1.subset (List.mem_flatMap.mpr ⟨_, he, mem_atomTmps_of_tmpReads hr⟩)

section Valid

/-- The events of a re-chosen path hold on the new reader. -/
theorem events_holds_retemp (hF : P.Fresh) {fn : Fn} {f : String} (hf : P.find? f = some fn) {fp : ℕ} {σ : Val}
    {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs)
    (hes : ∀ e ∈ es, e.Holds rd0 σ)
    (hna : ∀ a, Ev.atom a ∈ es → atomTmps a = [] → ∀ q ∈ atomEqns σ a, rd q.1 = rd0 q.1)
    (hrc : ∀ a, Ev.atom a ∈ es → ∀ r ∈ tmpReads σ a, rd r.2 = some (ν fp f σ r.1)) :
    ∀ e ∈ es, e.Holds rd (retempVal P ν fp f σ) := by
  have hag := evAgree_retemp (ν := ν) hF hf (fp := fp) hw
  intro e he
  cases e with
  | atom a =>
      by_cases ht : atomTmps a = []
      · have h1 := atom_holds_agree a (hes _ he) (hna a he ht)
        refine (atom_holds_congr a fun v hv => ?_).mpr h1
        rw [ht, List.append_nil] at hv
        exact hag _ he v hv
      · refine holds_of_tmpReads ht (hes _ he) (fun v hv => hag _ he v hv) fun r hr => ?_
        rw [hrc a he r hr]
        simp [retempVal, mem_temps_of_event hf hw he hr]
  | inK c =>
      have := hes _ he
      simp only [Ev.Holds] at this ⊢
      rw [hag _ he c (by simp [Ev.uses])]
      exact this
  | call _ _ _ => trivial
  | skip _ _ => trivial

mutual
/-- **The re-chosen tree is valid** on a reader giving it what it reads. -/
theorem retemp_valid (hF : P.Fresh) : ∀ (t : Tree) (fp : ℕ) {args rets : List E}, t.Valid P rd0 args rets →
    t.ReadsAs P fs ν rd rd0 fp → (t.retemp P fs ν fp).Valid P rd args rets
  | .node f σ bufs kids, fp, args, rets, ⟨fn, hf, hp, es, vs, hw, hr, hes, hk⟩, hra => by
      have hag := evAgree_retemp (ν := ν) hF hf (fp := fp) hw
      have hw' : walk (retempVal P ν fp f σ) fn.body = .ret es vs := by
        rw [walk_retemp hF hf]; exact hw
      have hev : (Tree.node f σ bufs kids).events P = es := events_node hf hw
      rw [readsAs_node, hev] at hra
      have hvs : vs.map (retempVal P ν fp f σ) = vs.map σ := by
        have := walk_within (σ := σ) fn.body
        rw [hw] at this
        exact List.map_congr_left fun v hv => retempVal_uses hF hf (this.2.2 v hv)
      rw [retemp_node]
      refine ⟨fn, hf, by rw [retempVal_params hF hf]; exact hp, es, vs, hw', by rw [hvs]; exact hr,
        events_holds_retemp hF hf hw hes hra.1 hra.2.1, ?_⟩
      refine retempKids_valid hF kids σ _ (calls es) _ (by rw [length_kidPos, List.length_map])
        (fun c hc v hv => ?_) hk hra.2.2
      obtain ⟨e, he, hce⟩ := List.mem_filterMap.mp hc
      cases e with
      | call g a r =>
          cases hce
          exact hag _ he v (by simpa [Ev.uses] using hv)
      | skip g a =>
          cases hce
          exact hag _ he v (by simpa [Ev.uses] using hv)
      | atom _ => simp [Ev.call?] at hce
      | inK _ => simp [Ev.call?] at hce
  | .phantom .., _, _, _, h, _ => h.elim

/-- `retemp_valid` for the callees. -/
theorem retempKids_valid (hF : P.Fresh) : ∀ (ks : List Tree) (σ σ' : Val) (cs : List Call) (ps : List ℕ),
    ps.length = ks.length → (∀ c ∈ cs, ∀ v ∈ c.args ++ c.rets, σ' v = σ v) →
    Tree.KidsValid P rd0 σ cs ks → Tree.ReadsAsKids P fs ν rd rd0 ps ks →
      Tree.KidsValid P rd σ' cs (Tree.retempKids P fs ν ps ks)
  | [], _, _, [], _, _, _, _, _ => by rw [retempKids_nil]; trivial
  | _ :: _, _, _, _, [], hl, _, _, _ => absurd hl (by simp)
  | k :: ks, σ, σ', c :: cs, p :: ps, hl, hag, ⟨hn, hc, hks⟩, hra => by
      rw [readsAsKids_cons] at hra
      rw [retempKids_cons]
      have hargs : c.args.map σ' = c.args.map σ :=
        List.map_congr_left fun v hv => hag c List.mem_cons_self v (List.mem_append_left _ hv)
      have hrets : c.rets.map σ' = c.rets.map σ :=
        List.map_congr_left fun v hv => hag c List.mem_cons_self v (List.mem_append_right _ hv)
      refine ⟨by rw [name_retemp]; exact hn, ?_, retempKids_valid hF ks σ σ' cs ps (by simpa using hl)
        (fun c' hc' => hag c' (List.mem_cons_of_mem _ hc')) hks hra.2⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc ⊢
        rw [hargs, hrets]
        exact retemp_valid hF k p hc hra.1
      · rw [ite_eq_right ht] at hc ⊢
        obtain ⟨⟨f, σk, rfl⟩, hph⟩ := hc
        rw [retemp_phantom, hargs]
        exact ⟨⟨f, σk, rfl⟩, hph⟩
  | [], _, _, _ :: _, _, _, _, h, _ => h.elim
  | _ :: _, _, _, [], _ :: _, _, _, h, _ => h.elim
end

end Valid

/-! ## What a re-chosen valid tree keeps -/

section Keep

mutual
theorem bufsOk_retemp (hF : P.Fresh) : ∀ (t : Tree) (fp : ℕ) {args rets : List E}, t.Valid P rd0 args rets →
    t.BufsOk P → (t.retemp P fs ν fp).BufsOk P
  | .node f σ bufs kids, fp, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hb => by
      rw [Tree.BufsOk, events_node hf hw] at hb
      rw [retemp_node, Tree.BufsOk, events_retemp hF, events_node hf hw (bufs := bufs) (kids := kids),
        allocs_congr (evAgree_retemp hF hf hw)]
      exact ⟨hb.1, bufsOkKids_retemp hF kids σ (calls es) _ hk hb.2⟩
  | .phantom .., fp, _, _, _, _ => by rw [retemp_phantom, Tree.BufsOk]; trivial

theorem bufsOkKids_retemp (hF : P.Fresh) : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (ps : List ℕ),
    Tree.KidsValid P rd0 σ cs ks → Tree.BufsOkKids P ks →
      Tree.BufsOkKids P (Tree.retempKids P fs ν ps ks)
  | [], _, _, _, _, _ => by rw [retempKids_nil, Tree.BufsOkKids]; trivial
  | _ :: _, _, _, [], _, h => by rw [Tree.retempKids]; exact h
  | k :: ks, σ, c :: cs, p :: ps, ⟨_, hc, hks⟩, hb => by
      rw [Tree.BufsOkKids] at hb
      rw [retempKids_cons, Tree.BufsOkKids]
      refine ⟨?_, bufsOkKids_retemp hF ks σ cs ps hks hb.2⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact bufsOk_retemp hF k p hc hb.1
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σk, rfl⟩, -⟩ := hc
        rw [retemp_phantom, Tree.BufsOk]; trivial
  | _ :: _, _, [], _ :: _, h, _ => h.elim
end

variable {cert : String → V → ℕ}

mutual
theorem placed_retemp (hF : P.Fresh) : ∀ (t : Tree) (fp : ℕ) {args rets : List E}, t.Valid P rd0 args rets →
    t.Placed P fs cert fp → (t.retemp P fs ν fp).Placed P fs cert fp
  | .node f σ bufs kids, fp, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hp => by
      rw [placed_node, events_node hf hw] at hp
      have hag := evAgree_retemp (ν := ν) hF hf (fp := fp) hw
      rw [retemp_node, placed_node, events_retemp hF, events_node hf hw (bufs := bufs) (kids := kids),
        map_total_retempKids_kidPos]
      refine ⟨⟨by rw [allocDsts_congr hag]; exact hp.1.1, fun q hq => by
        rw [addrs_congr hag q hq]; exact hp.1.2 q hq⟩, ?_⟩
      exact placedKids_retemp hF kids σ (calls es) _ hk hp.2
  | .phantom .., fp, _, _, _, _ => by rw [retemp_phantom]; exact placed_phantom

theorem placedKids_retemp (hF : P.Fresh) : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (ps : List ℕ),
    Tree.KidsValid P rd0 σ cs ks → Tree.PlacedKids P fs cert ps ks →
      Tree.PlacedKids P fs cert ps (Tree.retempKids P fs ν ps ks)
  | [], _, _, _, _, _ => by rw [retempKids_nil]; exact placedKids_nil
  | _ :: _, _, _, [], _, h => by rw [Tree.retempKids]; exact h
  | k :: ks, σ, c :: cs, p :: ps, ⟨_, hc, hks⟩, hp => by
      rw [placedKids_cons] at hp
      rw [retempKids_cons, placedKids_cons]
      refine ⟨?_, placedKids_retemp hF ks σ cs ps hks hp.2⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact placed_retemp hF k p hc hp.1
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σk, rfl⟩, -⟩ := hc
        rw [retemp_phantom]; exact placed_phantom
  | _ :: _, _, [], _ :: _, h, _ => h.elim
end

mutual
theorem data_retemp (hF : P.Fresh) : ∀ (t : Tree) (fp : ℕ) (i : ℕ),
    (t.retemp P fs ν fp).Data P fs cert fp i ↔ t.Data P fs cert fp i
  | .node f σ bufs kids, fp, i => by
      rw [retemp_node, data_node, data_node, events_retemp hF (bufs' := bufs) (ks' := kids),
        map_total_retempKids_kidPos, dataKids_retemp hF kids _ i (by rw [length_kidPos, List.length_map])]
  | .phantom .., fp, i => by rw [retemp_phantom]

theorem dataKids_retemp (hF : P.Fresh) : ∀ (ks : List Tree) (ps : List ℕ) (i : ℕ), ps.length = ks.length →
    (Tree.DataKids P fs cert ps (Tree.retempKids P fs ν ps ks) i ↔ Tree.DataKids P fs cert ps ks i)
  | [], _, i, _ => by rw [retempKids_nil]
  | _ :: _, [], _, h => absurd h (by simp)
  | k :: ks, p :: ps, i, h => by
      rw [retempKids_cons, dataKids_cons, dataKids_cons, data_retemp hF k p i,
        dataKids_retemp hF ks ps i (by simpa using h)]
end

mutual
theorem loadsIn_retemp (hF : P.Fresh) : ∀ (t : Tree) (R : ℕ → Prop) (fp : ℕ) {args rets : List E},
    t.Valid P rd0 args rets → t.LoadsIn P fs cert R fp → (t.retemp P fs ν fp).LoadsIn P fs cert R fp
  | .node f σ bufs kids, R, fp, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hl => by
      have hag := evAgree_retemp (ν := ν) hF hf (fp := fp) hw
      rw [loadsIn_node, events_node hf hw] at hl
      have hd : ∀ i, (Tree.node f (retempVal P ν fp f σ) bufs
          (Tree.retempKids P fs ν (kidPos fs P.loop fp f bufs (kids.map (Tree.total fs))) kids)).Data
            P fs cert fp i ↔ (Tree.node f σ bufs kids).Data P fs cert fp i := fun i => by
        rw [← retemp_node]; exact data_retemp hF _ fp i
      rw [retemp_node, loadsIn_node, events_retemp hF, events_node hf hw (bufs := bufs) (kids := kids),
        map_total_retempKids_kidPos, loadAddrs_congr hag]
      refine ⟨fun A hA => ?_, ?_⟩
      · obtain ⟨i, hi, h⟩ := hl.1 A hA
        exact ⟨i, hi, h.imp_left (hd i).mpr⟩
      · exact loadsInKids_mono _ _ (fun i h => h.imp_left (hd i).mpr)
          (loadsInKids_retemp hF kids σ (calls es) _ _ hk hl.2)
  | .phantom .., _, fp, _, _, _, _ => by rw [retemp_phantom]; exact loadsIn_phantom

theorem loadsInKids_retemp (hF : P.Fresh) : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (R : ℕ → Prop)
    (ps : List ℕ), Tree.KidsValid P rd0 σ cs ks → Tree.LoadsInKids P fs cert R ps ks →
      Tree.LoadsInKids P fs cert R ps (Tree.retempKids P fs ν ps ks)
  | [], _, _, _, _, _, _ => by rw [retempKids_nil]; exact loadsInKids_nil
  | _ :: _, _, _, _, [], _, h => by rw [Tree.retempKids]; exact h
  | k :: ks, σ, c :: cs, R, p :: ps, ⟨_, hc, hks⟩, hl => by
      rw [loadsInKids_cons] at hl
      rw [retempKids_cons, loadsInKids_cons]
      refine ⟨?_, loadsInKids_retemp hF ks σ cs R ps hks hl.2⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact loadsIn_retemp hF k R p hc hl.1
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σk, rfl⟩, -⟩ := hc
        rw [retemp_phantom]; exact loadsIn_phantom
  | _ :: _, _, [], _, _ :: _, h, _ => h.elim
end

mutual
theorem loadsR_retemp (hF : P.Fresh) : ∀ (t : Tree) (R : ℕ → Prop) (fp : ℕ) {args rets : List E},
    t.Valid P rd0 args rets → t.LoadsR P R → (t.retemp P fs ν fp).LoadsR P R
  | .node f σ bufs kids, R, fp, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hl => by
      rw [Tree.LoadsR, events_node hf hw] at hl
      rw [retemp_node, Tree.LoadsR, events_retemp hF, events_node hf hw (bufs := bufs) (kids := kids),
        loadAddrs_congr (evAgree_retemp hF hf hw)]
      exact ⟨hl.1, loadsRKids_retemp hF kids σ (calls es) R _ hk hl.2⟩
  | .phantom .., _, fp, _, _, _, _ => by rw [retemp_phantom, Tree.LoadsR]; trivial

theorem loadsRKids_retemp (hF : P.Fresh) : ∀ (ks : List Tree) (σ : Val) (cs : List Call) (R : ℕ → Prop)
    (ps : List ℕ), Tree.KidsValid P rd0 σ cs ks → Tree.LoadsRKids P R ks →
      Tree.LoadsRKids P R (Tree.retempKids P fs ν ps ks)
  | [], _, _, _, _, _, _ => by rw [retempKids_nil, Tree.LoadsRKids]; trivial
  | _ :: _, _, _, _, [], _, h => by rw [Tree.retempKids]; exact h
  | k :: ks, σ, c :: cs, R, p :: ps, ⟨_, hc, hks⟩, hl => by
      rw [Tree.LoadsRKids] at hl
      rw [retempKids_cons, Tree.LoadsRKids]
      refine ⟨?_, loadsRKids_retemp hF ks σ cs R ps hks hl.2⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact loadsR_retemp hF k R p hc hl.1
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σk, rfl⟩, -⟩ := hc
        rw [retemp_phantom, Tree.LoadsR]; trivial
  | _ :: _, _, [], _, _ :: _, h, _ => h.elim
end

end Keep

/-! ## Transfer to another reader -/

section Transfer

theorem eq_of_nodup_flatMap {α β : Type} {g : α → List β} : ∀ {l : List α}, (l.flatMap g).Nodup →
    ∀ {a b : α} {x : β}, a ∈ l → b ∈ l → x ∈ g a → x ∈ g b → a = b
  | [], _, _, _, _, ha, _, _, _ => (List.not_mem_nil ha).elim
  | c :: l, h, a, b, x, ha, hb, hxa, hxb => by
      rw [List.flatMap_cons, List.nodup_append] at h
      have hl : ∀ {y}, y ∈ g c → ∀ {d}, d ∈ l → y ∈ g d → False := fun hy d hd hyd =>
        h.2.2 _ hy _ (List.mem_flatMap.mpr ⟨d, hd, hyd⟩) rfl
      rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
      · rw [h1, h2]
      · subst h1; exact (hl hxa h2 hxb).elim
      · subst h2; exact (hl hxb h1 hxa).elim
      · exact eq_of_nodup_flatMap h.2.1 h1 h2 hxa hxb

/-- An atom on the path of `f` under `σ` reads the temporary `t` at `A`. -/
def RcRead (P : Core.Program) (f : String) (σ : Val) (t : V) (A : K) : Prop :=
  ∃ a, Ev.atom a ∈ (Tree.node f σ [] []).events P ∧ (t, A) ∈ tmpReads σ a

theorem events_eq_node {f : String} {σ : Val} {bufs bufs' : List ℕ} {ks ks' : List Tree} :
    (Tree.node f σ bufs ks).events P = (Tree.node f σ bufs' ks').events P := rfl

theorem snd_eq_of_nodup_fst {α β : Type} : ∀ {l : List (α × β)}, (l.map Prod.fst).Nodup →
    ∀ {x : α} {b b' : β}, (x, b) ∈ l → (x, b') ∈ l → b = b'
  | [], _, _, _, _, h, _ => (List.not_mem_nil h).elim
  | c :: l, hn, x, b, b', h, h' => by
      rw [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.mp h with h1 | h1 <;> rcases List.mem_cons.mp h' with h2 | h2
      · exact (Prod.mk.inj (h1.trans h2.symm)).2
      · rw [← h1] at hn; exact absurd (List.mem_map_of_mem (f := Prod.fst) h2) hn.1
      · rw [← h2] at hn; exact absurd (List.mem_map_of_mem (f := Prod.fst) h1) hn.1
      · exact snd_eq_of_nodup_fst hn.2 h1 h2

/-- **A temporary is read at one address**, in a program with fresh temporaries. -/
theorem rcRead_unique (hF : P.Fresh) {f : String} {σ : Val} {t : V} {A A' : K}
    (h : RcRead P f σ t A) (h' : RcRead P f σ t A') : A = A' := by
  obtain ⟨a, he, hA⟩ := h
  obtain ⟨a', he', hA'⟩ := h'
  unfold Tree.events at he he'
  simp only [Tree.name, Tree.val] at he he'
  cases hf : P.find? f with
  | none => rw [hf] at he; exact (List.not_mem_nil he).elim
  | some fn =>
      rw [hf] at he he'
      dsimp only at he he'
      cases hw : walk σ fn.body with
      | fall es => rw [hw] at he; exact (List.not_mem_nil he).elim
      | stuck => rw [hw] at he; exact (List.not_mem_nil he).elim
      | ret es vs =>
          rw [hw] at he he'
          dsimp only at he he'
          have hwi := walk_within (σ := σ) fn.body
          rw [hw] at hwi
          have hnd : (es.flatMap Ev.tmps).Nodup :=
            hwi.2.1.nodup (hF fn (List.mem_of_find?_eq_some hf)).1
          have m1 : t ∈ (Ev.atom a).tmps := mem_atomTmps_of_tmpReads hA
          have m2 : t ∈ (Ev.atom a').tmps := mem_atomTmps_of_tmpReads hA'
          have heq := eq_of_nodup_flatMap hnd he he' m1 m2
          simp only [Ev.atom.injEq] at heq
          subst heq
          have hnd1 : ((tmpReads σ a).map Prod.fst).Nodup := by
            rw [tmpReads_fst]
            rw [List.nodup_flatMap] at hnd
            exact hnd.1 _ he
          exact snd_eq_of_nodup_fst hnd1 hA hA'

open Classical in
/-- **Temporaries read from `rd`**: each temporary the word `rd` holds where its range check
reads, `0` if there is none. -/
noncomputable def nuRead (P : Core.Program) (rd : Reader) : ℕ → String → Val → V → E :=
  fun _ f σ t => if h : ∃ A, RcRead P f σ t A then (rd (Classical.choose h)).getD 0 else 0

theorem nuRead_eq (hF : P.Fresh) {rd : Reader} {fp : ℕ} {f : String} {σ : Val} {t : V} {A : K}
    (h : RcRead P f σ t A) {w : E} (hw : rd A = some w) : nuRead P rd fp f σ t = w := by
  have hex : ∃ A, RcRead P f σ t A := ⟨A, h⟩
  simp only [nuRead, hex, ↓reduceDIte]
  rw [rcRead_unique hF (Classical.choose_spec hex) h, hw]
  rfl

variable {cert : String → V → ℕ} {rd rd0 : Reader}

mutual
/-- **A reader agreeing on a tree's region and data gives the re-chosen tree what it reads**,
the temporaries read from it. -/
theorem readsAs_nuRead (hF : P.Fresh) (hdef : ∀ A, (rd0 A).isSome → (rd A).isSome) :
    ∀ (t : Tree) (R : ℕ → Prop) (fp : ℕ) {args rets : List E}, t.Valid P rd0 args rets →
    t.Placed P fs cert fp → t.LoadsIn P fs cert R fp →
    (∀ i, R i ∨ t.Data P fs cert fp i → rd (addressOfIndex i) = rd0 (addressOfIndex i)) →
    t.ReadsAs P fs (nuRead P rd) rd rd0 fp
  | .node f σ bufs kids, R, fp, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩, hp, hl, hag => by
      have hev : (Tree.node f σ bufs kids).events P = es := events_node hf hw
      rw [readsAs_node, hev]
      rw [placed_node, hev] at hp
      rw [loadsIn_node, hev] at hl
      refine ⟨fun a ha hta q hq => ?_, fun a ha r hr => ?_, ?_⟩
      · cases a with
        | load d p off =>
            rw [List.mem_singleton.mp hq]
            obtain ⟨i, hi, hd⟩ := hl.1 ((σ p).limb 0 * addressOfIndex off) (List.mem_filterMap.mpr ⟨_, ha, rfl⟩)
            simp only
            rw [hi]
            exact hag i hd.symm
        | frameAddr p run =>
            obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hq
            cases run with
            | nil => exact absurd hk (by simp)
            | cons r rs =>
                have hpv := hp.1.2 (p, r) (List.mem_filterMap.mpr ⟨_, ha, rfl⟩)
                simp only at hpv hk ⊢
                rw [hpv, show (ofK (addressOfIndex (fp + cert f r))).limb 0 = addressOfIndex (fp +
                    cert f r) by simp,
                  show addressOfIndex (fp + cert f r) * addressOfIndex k = addressOfIndex (fp + cert
                      f r + k) by
                    simp only [addressOfIndex, pow_add]]
                refine hag _ (Or.inr (data_node.mpr (Or.inl (Or.inr ⟨(r, rs.length + 1),
                  by rw [hev]; exact List.mem_filterMap.mpr ⟨_, ha, rfl⟩, ?_, ?_⟩))))
                · simp only; omega
                · simp only [List.length_cons] at hk ⊢; omega
        | rangeCheck _ _ _ _ _ => simp [atomTmps] at hta
        | touch _ _ => simp [atomTmps] at hta
        | const _ _ => exact (List.not_mem_nil hq).elim
        | add _ _ _ => exact (List.not_mem_nil hq).elim
        | mul _ _ _ => exact (List.not_mem_nil hq).elim
        | copy _ _ => exact (List.not_mem_nil hq).elim
        | assertEq _ _ => exact (List.not_mem_nil hq).elim
        | assertNe _ _ _ => exact (List.not_mem_nil hq).elim
        | assertInK _ _ => exact (List.not_mem_nil hq).elim
        | keccak _ _ _ _ => exact (List.not_mem_nil hq).elim
        | hint _ => exact (List.not_mem_nil hq).elim
      · have hmem : Ev.atom a ∈ (Tree.node f σ [] []).events P := by
          show Ev.atom _ ∈ (Tree.node f σ bufs kids).events P
          rw [hev]; exact ha
        have h0 := tmpReads_read (hes _ ha) hr
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hdef r.2 (by rw [h0]; rfl))
        rw [hw, nuRead_eq (t := r.1) (A := r.2) hF ⟨a, hmem, hr⟩ hw]
      · exact readsAsKids_nuRead hF hdef kids σ (calls es) _ _ hk hp.2 hl.2 fun i hi =>
          hi.elim (fun h => h.elim (fun hd => hag i (Or.inr hd)) fun hr => hag i (Or.inl hr))
            fun hd => hag i (Or.inr (data_node.mpr (Or.inr hd)))
  | .phantom .., _, _, _, _, h, _, _, _ => h.elim

/-- `readsAs_nuRead` for the callees. -/
theorem readsAsKids_nuRead (hF : P.Fresh) (hdef : ∀ A, (rd0 A).isSome → (rd A).isSome) :
    ∀ (ks : List Tree) (σ : Val) (cs : List Call) (R : ℕ → Prop) (ps : List ℕ),
    Tree.KidsValid P rd0 σ cs ks → Tree.PlacedKids P fs cert ps ks →
    Tree.LoadsInKids P fs cert R ps ks →
    (∀ i, R i ∨ Tree.DataKids P fs cert ps ks i → rd (addressOfIndex i) = rd0 (addressOfIndex i)) →
    Tree.ReadsAsKids P fs (nuRead P rd) rd rd0 ps ks
  | [], _, _, _, ps, _, _, _, _ => by cases ps <;> (rw [Tree.ReadsAsKids]; trivial)
  | _ :: _, _, _, _, [], _, _, _, _ => by rw [Tree.ReadsAsKids]; trivial
  | k :: ks, σ, c :: cs, R, p :: ps, ⟨_, hc, hks⟩, hp, hl, hag => by
      rw [placedKids_cons] at hp
      rw [loadsInKids_cons] at hl
      rw [readsAsKids_cons]
      refine ⟨?_, readsAsKids_nuRead hF hdef ks σ cs R ps hks hp.2 hl.2 fun i hi =>
        hag i (hi.imp_right fun h => dataKids_cons.mpr (Or.inr h))⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact readsAs_nuRead hF hdef k R p hc hp.1 hl.1 fun i hi =>
          hag i (hi.imp_right fun h => dataKids_cons.mpr (Or.inl h))
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σk, rfl⟩, -⟩ := hc
        rw [Tree.ReadsAs]; trivial
  | _ :: _, _, [], _, _ :: _, h, _, _, _ => h.elim
end

/-- **A tree moves to another reader** agreeing with its own on its region and data and defined
wherever it is: its temporaries re-read, it keeps everything else. -/
theorem transfer (hF : P.Fresh) (hdef : ∀ A, (rd0 A).isSome → (rd A).isSome) {t : Tree}
    {R : ℕ → Prop} {fp : ℕ} {args rets : List E} (hv : t.Valid P rd0 args rets)
    (hp : t.Placed P fs cert fp) (hl : t.LoadsIn P fs cert R fp)
    (hag : ∀ i, R i ∨ t.Data P fs cert fp i → rd (addressOfIndex i) = rd0 (addressOfIndex i)) :
    (t.retemp P fs (nuRead P rd) fp).name = t.name ∧
      (t.retemp P fs (nuRead P rd) fp).Valid P rd args rets ∧
      (t.BufsOk P → (t.retemp P fs (nuRead P rd) fp).BufsOk P) ∧
      (t.retemp P fs (nuRead P rd) fp).Placed P fs cert fp ∧
      (t.retemp P fs (nuRead P rd) fp).total fs = t.total fs ∧
      (t.retemp P fs (nuRead P rd) fp).LoadsIn P fs cert R fp ∧
      ∀ i, (t.retemp P fs (nuRead P rd) fp).Data P fs cert fp i ↔ t.Data P fs cert fp i :=
  ⟨name_retemp fp t, retemp_valid hF t fp hv (readsAs_nuRead hF hdef t R fp hv hp hl hag),
    bufsOk_retemp hF t fp hv, placed_retemp hF t fp hv hp, total_retemp t fp,
    loadsIn_retemp hF t R fp hv hl, data_retemp hF t fp⟩

/-- **The placed relation of a tree on every reader** agreeing on its region and data. -/
theorem relAtIn_transfer (hF : P.Fresh) {t : Tree} {R D : ℕ → Prop} {fp : ℕ} {f : String}
    {args rets : List E} (hn : t.name = f) (hv : t.Valid P rd0 args rets) (hb : t.BufsOk P)
    (hp : t.Placed P fs cert fp) (hl : t.LoadsIn P fs cert R fp)
    (hD : ∀ i, D i → t.Data P fs cert fp i) (rd : Reader)
    (hag : ∀ i, R i ∨ t.Data P fs cert fp i → rd (addressOfIndex i) = rd0 (addressOfIndex i))
    (hdef : ∀ A, (rd0 A).isSome → (rd A).isSome) :
    RelAtIn P fs cert rd R D fp (t.total fs) f args rets := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := transfer (rd := rd) hF hdef hv hp hl hag
  exact ⟨_, h1.trans hn, h2, h3 hb, h4, h5, h6, fun i hi => (h7 i).mpr (hD i hi)⟩

theorem RelAtIn.mono {R R' D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    (h : RelAtIn P fs cert rd R D fp n f args rets) (hR : ∀ i, R i → R' i) :
    RelAtIn P fs cert rd R' D fp n f args rets :=
  let ⟨t, hn, hv, hb, hp, ht, hl, hd⟩ := h
  ⟨t, hn, hv, hb, hp, ht, loadsIn_mono t fp hR hl, hd⟩

/-! ### Pure functions on every reader -/

section Pure

variable {S : List String}

theorem runs_pure {es : List Ev} (h : ∀ e ∈ es, e.pure S) : runs es = [] := by
  refine List.filterMap_eq_nil_iff.mpr fun e he => ?_
  have := h e he
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ | _ | _ | _ <;>
    first | rfl | simp [Ev.pure, atomUnplaced] at this

mutual
/-- A valid tree of a function of a pure set has no data. -/
theorem not_data_of_pure (hS : P.PureIn S) : ∀ (t : Tree) {args rets : List E},
    t.Valid P rd0 args rets → t.BufsOk P → t.name ∈ S → ∀ fp i, ¬ t.Data P fs cert fp i
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hb, hn, fp, i => by
      have hpure : ∀ e ∈ es, e.pure S := by
        have := walk_pure (σ := σ) fn.body (hS f hn fn hf)
        rwa [hw] at this
      rw [Tree.BufsOk, events_node hf hw, allocs_pure hpure] at hb
      obtain ⟨rfl, hkb⟩ := hb
      rw [data_node, events_node hf hw]
      rintro ((⟨q, hq, -⟩ | ⟨q, hq, -⟩) | hd)
      · simp at hq
      · rw [runs_pure hpure] at hq; exact List.not_mem_nil hq
      · exact not_dataKids_of_pure hS kids σ (calls es) hk hkb (calls_pure hpure) _ i hd
  | .phantom .., _, _, h, _, _, _, _ => h.elim

/-- `not_data_of_pure` for the callees. -/
theorem not_dataKids_of_pure (hS : P.PureIn S) : ∀ (ks : List Tree) (σ : Val) (cs : List Call),
    Tree.KidsValid P rd0 σ cs ks → Tree.BufsOkKids P ks → (∀ c ∈ cs, c.f ∈ S) →
      ∀ ps i, ¬ Tree.DataKids P fs cert ps ks i
  | [], _, _, _, _, _, _, i => not_dataKids_nil
  | _ :: _, _, _, _, _, _, [], i => by rw [Tree.DataKids]; exact id
  | k :: ks, σ, c :: cs, ⟨hn, hc, hks⟩, hb, hS', p :: ps, i => by
      rw [Tree.BufsOkKids] at hb
      rw [dataKids_cons]
      rintro (hd | hd)
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact not_data_of_pure hS k hc hb.1 (hn ▸ hS' c List.mem_cons_self) p i hd
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          exact data_phantom hd
      · exact not_dataKids_of_pure hS ks σ cs hks hb.2
          (fun c' h => hS' c' (List.mem_cons_of_mem _ h)) ps i hd
  | _ :: _, _, [], h, _, _, _ :: _, _ => h.elim
end

/-- **A function of a pure set loading from `R`, on every reader**: the size is fixed first, then
on any reader agreeing with `rd0` on `R` and defined wherever it is, at any frame pointer. -/
theorem relAtIn_uniform_pure (hF : P.Fresh) (hS : P.PureIn S) {g : String} (hg : g ∈ S)
    {R : ℕ → Prop} {args rets : List E} (h : P.RelIn rd0 R g args rets) :
    ∃ n, ∀ (fp : ℕ) (rd : Reader), (∀ i, R i → rd (addressOfIndex i) = rd0 (addressOfIndex i)) →
      (∀ A, (rd0 A).isSome → (rd A).isSome) →
      RelAtIn P fs cert rd R (fun _ => False) fp n g args rets := by
  obtain ⟨t, hn, hv, hb, hl⟩ := h
  refine ⟨t.total fs, fun fp rd hag hdef => ?_⟩
  exact relAtIn_transfer hF hn hv hb (placed_of_pure hS t hv hb (hn ▸ hg) fp)
    (loadsIn_of_loadsR t R fp hl) (fun _ h => h.elim) rd
    (fun i hi => hi.elim (hag i) fun hd => (not_data_of_pure hS t hv hb (hn ▸ hg) fp i hd).elim) hdef

/-- **A function of a quiet set, on every reader**: `Program.Rel` on `rd0` gives the placed
relation on any reader defined wherever `rd0` is, at any frame pointer and region. -/
theorem relAtIn_uniform_quiet (hP : P.Wf) (hF : P.Fresh) (hS : P.QuietIn S) {g : String}
    (hg : g ∈ S) {args rets : List E} (h : P.Rel rd0 g args rets) :
    ∃ n, ∀ (fp : ℕ) (R : ℕ → Prop) (rd : Reader), (∀ A, (rd0 A).isSome → (rd A).isSome) →
      RelAtIn P fs cert rd R (fun _ => False) fp n g args rets := by
  obtain ⟨t, hn, hv, hb⟩ := Program.Rel.tree hP h
  obtain ⟨n, hn'⟩ := relAtIn_uniform_pure (fs := fs) (cert := cert) hF hS.pureIn hg
    ⟨t, hn, hv, hb, loadsR_of_quiet hS (fun _ => False) t hv (hn ▸ hg)⟩
  exact ⟨n, fun fp R rd hdef => (hn' fp rd (fun _ h => h.elim) hdef).mono fun _ h => h.elim⟩

end Pure

end Transfer

end
end LeanVM.Guest.Memory
