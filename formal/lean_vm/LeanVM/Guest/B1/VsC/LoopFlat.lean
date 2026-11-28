/-
  LeanVM.Guest.B1.VsC.LoopFlat

  A flat loop helper (atoms, then its tail call behind a guard) completes with no words of its
  own, and every valid tree of it has its shape.
-/

module

public import LeanVM.Guest.B1.VsC.SlowA

/-!
# Flat loop helpers

A loop helper whose body is atoms, then `callIf (.n g) self targs`, then `ret []`:

* `callCompletes0_loopFlat`: one iteration completes with no words of its own, popping nothing,
  exact, from a valuation per memory making its atoms hold, the next iteration's tree when the
  guard is nonzero.
* `shapeR_loopFlat`: every valid tree of an iteration has block `fs self + Bt` and ends at its
  cursor, loading in `R`, when its atoms read the arrays `ps` (`loadOkB`) at pointers `ptrAt`
  of cells of `R`, and the tail's trees have block `Bt`.
* Forward evaluation (`fwdVal`): an atom needing no side condition holds (`fwd_holds_noSide`), a
  load reading a defined word holds (`fwd_holds_load`), a load through a pointer of `ps` reads a
  defined word (`loadHolds_of_loadOk`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## The events of a flat iteration -/

theorem flat_straight (A : List Atom) (g : ℕ) (self : String) (targs : List V) :
    (A.map Stmt.atom ++ [Stmt.callIf (.n g) self targs]).all Stmt.straight = true := by
  simp [List.all_append, List.all_map, Function.comp_def, Stmt.straight]

theorem flat_evs (σ : Val) (A : List Atom) (g : ℕ) (self : String) (targs : List V) :
    (A.map Stmt.atom ++ [Stmt.callIf (.n g) self targs]).flatMap (slEvs σ) =
      A.map Ev.atom ++ [.inK (.n g), if σ (.n g) = 0 then .skip self targs else .call self targs []] := by
  rw [List.flatMap_append, flatMap_atoms]
  simp only [List.flatMap_cons, List.flatMap_nil, slEvs, List.append_nil]

theorem filterMap_callAtom : ∀ A : List Atom, List.filterMap (Ev.call? ∘ Ev.atom) A = []
  | [] => rfl
  | _ :: A => by rw [List.filterMap_cons]; exact filterMap_callAtom A

theorem flat_calls (σ : Val) (A : List Atom) (g : ℕ) (self : String) (targs : List V) :
    calls ((A.map Stmt.atom ++ [Stmt.callIf (.n g) self targs]).flatMap (slEvs σ)) =
      [⟨self, targs, [], decide (σ (.n g) ≠ 0)⟩] := by
  rw [flat_evs]
  show List.filterMap Ev.call? _ = _
  rw [List.filterMap_append, List.filterMap_map, filterMap_callAtom, List.nil_append]
  by_cases hz : σ (.n g) = 0 <;> (simp [hz, Ev.call?]; rfl)

/-- An atom a `loadOkB` check passes is no hint. -/
theorem notHint_of_loadOk {ps : List (ℕ × ℕ)} {a : Atom} (h : loadOkB ps a = true) : ∀ hh, a ≠ .hint hh := by
  rintro hh rfl
  simp [loadOkB] at h

theorem quiet_of_loadOk {ps : List (ℕ × ℕ)} {a : Atom} (h : loadOkB ps a = true) :
    atomQuiet a = true ∧ trivExact a = true := by
  cases a with
  | hint hh => simp [loadOkB] at h
  | _ => exact ⟨rfl, rfl⟩

theorem filterMap_allocSz_nil {ps : List (ℕ × ℕ)} :
    ∀ A : List Atom, A.all (loadOkB ps) = true → (A.map Stmt.atom).filterMap Stmt.allocSz = []
  | [], _ => rfl
  | a :: A, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.map_cons, List.filterMap_cons]
    cases a with
    | hint hh => simp [loadOkB] at h
    | _ => exact filterMap_allocSz_nil A h.2

theorem flat_allocs {ps : List (ℕ × ℕ)} (σ : Val) {A : List Atom} (hok : A.all (loadOkB ps) = true) (g : ℕ)
    (self : String) (targs : List V) :
    allocs σ ((A.map Stmt.atom ++ [Stmt.callIf (.n g) self targs]).flatMap (slEvs σ)) = [] := by
  rw [(straight_parts σ _ (flat_straight A g self targs)).2.1, List.filterMap_append,
    filterMap_allocSz_nil A hok]
  rfl

theorem allAtoms_of_isAtom {ss : List Stmt} (h : ss.all Stmt.isAtom = true) : AllAtoms ss := by
  intro s hs
  have := List.all_eq_true.mp h s hs
  cases s with
  | atom a => exact ⟨a, rfl⟩
  | _ => simp [Stmt.isAtom] at this

theorem params_range_map (vs : List E) :
    ((List.range vs.length).map V.n).map (fun v => vs.getD v.idx 0) = vs := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply]
  exact List.getD_eq_getElem _ _ h2

/-! ## Completeness of an iteration -/

/-- **An iteration of a flat loop helper completes** with no words of its own, popping nothing,
exact: on each memory, a valuation with the arguments making the atoms hold, the guard in `K`, and,
when it is nonzero, the next iteration's tree. -/
theorem callCompletes0_loopFlat {kd : ℕ} {self : String} {fn : Fn} {A : List Atom} {g : ℕ}
    {targs : List V} {ps : List (ℕ × ℕ)} (hfind : coreProgram.find? self = some fn)
    (hbody : fn.body = (A.map Stmt.atom ++ [Stmt.callIf (.n g) self targs]) ++ [.ret []])
    (hpar : fn.params = (List.range targs.length).map V.n) (hok : A.all (loadOkB ps) = true)
    {args : List E} {Pre : Reader → Prop} (σ : Reader → Val)
    (h : ∀ rd, LowDef kd rd → Pre rd → fn.params.map (σ rd) = args ∧ (∀ a ∈ A, a.Holds rd (σ rd)) ∧
      IsInK (σ rd (.n g)) ∧ (σ rd (.n g) ≠ 0 → ∃ t : Tree, t.name = self ∧
        t.Valid coreProgram rd (targs.map (σ rd)) [] ∧ t.BufsOk coreProgram ∧ PostQuiet rd t)) :
    CallCompletes0 kd self args [] Pre PostQuiet := by
  refine callCompletes0_node fun rd hl hP => ?_
  obtain ⟨hp, hA, hk, hn⟩ := h rd hl hP
  set s := σ rd with hs
  set es := (A.map Stmt.atom ++ [Stmt.callIf (.n g) self targs]).flatMap (slEvs s) with hes
  have hw : walk s fn.body = .ret es [] := by
    rw [hbody]; exact walk_straight s [] _ (flat_straight A g self targs)
  have hmem : ∀ e ∈ es, (∃ a ∈ A, e = .atom a) ∨ e = .inK (.n g) ∨
      e = (if s (.n g) = 0 then .skip self targs else .call self targs []) := by
    intro e he
    rw [hes, flat_evs] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ⟨a, ha, rfl⟩ | rfl | rfl
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  obtain ⟨t2, hk2, hb2, hq2⟩ : ∃ t2, Tree.KidsValid coreProgram rd s
      [⟨self, targs, [], decide (s (.n g) ≠ 0)⟩] [t2] ∧ Tree.BufsOk coreProgram t2 ∧ PostQuiet rd t2 := by
    by_cases hz : s (.n g) = 0
    · have hd : decide (s (.n g) ≠ 0) = false := by simp [hz]
      refine ⟨.phantom self (fun v => (targs.map s).getD v.idx 0),
        kidsValid_cons_skip (c := ⟨self, targs, [], decide (s (.n g) ≠ 0)⟩) (cs := []) (fn := fn) hd hfind
          ?_ kidsValid_nil,
        by rw [Tree.BufsOk]; trivial, by rw [PostQuiet, Tree.pops]; exact ⟨rfl, Tree.every_phantom⟩⟩
      rw [hpar]
      have := params_range_map (targs.map s)
      rwa [List.length_map] at this
    · have hd : decide (s (.n g) ≠ 0) = true := by simp [hz]
      obtain ⟨t2, hn2, hv2, hb2, hq2⟩ := hn hz
      exact ⟨t2, kidsValid_cons_taken hd hn2 hv2 kidsValid_nil, hb2, hq2⟩
  have hK : Tree.KidsValid coreProgram rd s (calls es) [t2] := by rw [hes, flat_calls]; exact hk2
  refine ⟨s, fn, es, [], [t2], hfind, hp, hw, rfl, fun e he => ?_, hK,
    by rw [Tree.BufsOkKids, Tree.BufsOkKids]; exact ⟨hb2, trivial⟩, ?_⟩
  · rcases hmem e he with ⟨a, ha, rfl⟩ | rfl | rfl
    · exact hA a ha
    · exact hk
    · split <;> trivial
  · refine postQuiet_node hfind hw (fun c hc => ?_) (fun e he => ?_) hK ?_ _
    · rcases hmem _ hc with ⟨a, ha, hae⟩ | hc' | hc'
      · have hca : c = a := by injection hae
        rw [hca]; exact (quiet_of_loadOk (List.all_eq_true.mp hok a ha)).1
      · cases hc'
      · split at hc' <;> cases hc'
    · rcases hmem e he with ⟨a, ha, rfl⟩ | rfl | rfl
      · exact exact_of_trivExact (quiet_of_loadOk (List.all_eq_true.mp hok a ha)).2
      · trivial
      · split <;> trivial
    · rw [hes, flat_calls, List.map_cons, List.map_nil, kidsPost_cons]
      exact ⟨fun _ => hq2, by simp [KidsPost]⟩

/-! ## Loads through pointers of known cells -/

/-- A load a `loadOkB ps` check passes, through pointers at cells of `R`, loads from `R`. -/
theorem loadAddr_of_loadOk {ps : List (ℕ × ℕ)} {σ : Val} {R : ℕ → Prop}
    (hb : ∀ q ∈ ps, ∃ b, σ (.n q.1) = ptrAt b ∧ ∀ o < q.2, R (b + o))
    {a : Atom} (ha : loadOkB ps a = true) {x : K} (hx : Ev.loadAddr? σ (.atom a) = some x) :
    ∃ i, x = addressOfIndex i ∧ R i := by
  cases a with
  | load d p off =>
    simp only [Ev.loadAddr?, Option.some.injEq] at hx
    simp only [loadOkB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ha
    obtain ⟨q, hq, rfl, hoff⟩ := ha
    obtain ⟨b, h1, h2⟩ := hb q hq
    refine ⟨b + off, ?_, h2 off hoff⟩
    rw [← hx, h1]
    exact Main.addr_ofK _ _
  | _ => simp [Ev.loadAddr?] at hx

/-- A load a `loadOkB ps` check passes, through pointers at defined words, reads one. -/
theorem loadHolds_of_loadOk {rd : Reader} {ps : List (ℕ × ℕ)} {σ : Val}
    (hb : ∀ q ∈ ps, ∃ b, σ (.n q.1) = ptrAt b ∧ ∀ o < q.2, ∃ v, LoadHolds rd (ptrAt b) o v)
    {d p : V} {off : ℕ} (ha : loadOkB ps (.load d p off) = true) : ∃ v, LoadHolds rd (σ p) off v := by
  simp only [loadOkB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ha
  obtain ⟨q, hq, rfl, hoff⟩ := ha
  obtain ⟨b, h1, h2⟩ := hb q hq
  rw [h1]
  exact h2 off hoff

/-! ## Shapes -/

/-- **Every valid tree of a flat loop helper's iteration has its shape**: block `fs self + Bt`,
ending at its cursor, loading from `R`, given its atoms' pointers at cells of `R` and the tail's
trees' block `Bt`. -/
theorem shapeR_loopFlat {fs : String → ℕ} {al : String → Bool} {self : String} {fn : Fn} {A : List Atom}
    {g : ℕ} {targs : List V} {ps : List (ℕ × ℕ)} (hfind : coreProgram.find? self = some fn)
    (hbody : fn.body = (A.map Stmt.atom ++ [Stmt.callIf (.n g) self targs]) ++ [.ret []])
    (hls : coreProgram.loop self = true) (hok : A.all (loadOkB ps) = true)
    {args : List E} {R : ℕ → Prop} {Bt : ℕ}
    (hstep : ∀ rd σ, fn.params.map σ = args → (∀ a ∈ A, a.Holds rd σ) →
      (∀ q ∈ ps, ∃ b, σ (.n q.1) = ptrAt b ∧ ∀ o < q.2, R (b + o)) ∧
      (σ (.n g) = 0 → Bt = fs (tailKey self)) ∧
      (σ (.n g) ≠ 0 → ∀ t, t.name = self → t.Valid coreProgram rd (targs.map σ) [] → t.BufsOk coreProgram →
        ShapeR fs al Bt id R t)) :
    ∀ rd t, t.name = self → t.Valid coreProgram rd args [] → t.BufsOk coreProgram →
      ShapeR fs al (fs self + Bt) id R t := by
  intro rd t hn hv hb
  cases t with
  | phantom _ _ => exact hv.elim
  | node f σ bufs kids =>
  simp only [Tree.name] at hn
  subst hn
  obtain ⟨fn', hf, hp, es, vs, hw, -, hev, hk⟩ := hv
  have hff : fn' = fn := Option.some.inj (hf.symm.trans hfind)
  subst hff
  have hw0 : walk σ fn'.body = .ret ((A.map Stmt.atom ++ [Stmt.callIf (.n g) f targs]).flatMap (slEvs σ)) [] := by
    rw [hbody]; exact walk_straight σ [] _ (flat_straight A g f targs)
  rw [hw0] at hw
  cases hw
  have hA : ∀ a ∈ A, a.Holds rd σ := fun a ha => hev (.atom a) (by rw [flat_evs]; simp [ha])
  obtain ⟨hbase, h0, hnext⟩ := hstep rd σ hp hA
  have hev0 : (Memory.Tree.node f σ bufs kids).events coreProgram =
      (A.map Stmt.atom ++ [Stmt.callIf (.n g) f targs]).flatMap (slEvs σ) := Complete.events_node hfind hw0
  rw [Tree.BufsOk, hev0, flat_allocs σ hok] at hb
  obtain ⟨rfl, hbk⟩ := hb
  rw [flat_calls] at hk
  rcases kids with _ | ⟨t2, _ | ⟨t3, ks⟩⟩ <;> try (simp [Tree.KidsValid] at hk; done)
  rw [Tree.KidsValid, Tree.KidsValid] at hk
  obtain ⟨hn2, hv2, -⟩ := hk
  rw [Tree.BufsOkKids] at hbk
  obtain ⟨hb2, -⟩ := hbk
  have hs2 : ShapeR fs al Bt id R t2 := by
    by_cases hz : σ (.n g) = 0
    · have hd : decide (σ (.n g) ≠ 0) = false := by simp [hz]
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at hv2
      obtain ⟨⟨f', σ', rfl⟩, -⟩ := hv2
      simp only [Tree.name] at hn2
      refine ⟨?_, fun c => ?_, by simp only [Tree.LoadsR], by simp only [Tree.HintsR]⟩
      · rw [Tree.block, hn2, h0 hz]
      · rw [endA_phantom]; rfl
    · have hd : decide (σ (.n g) ≠ 0) = true := by simp [hz]
      simp only [hd, ↓reduceIte] at hv2
      exact hnext hz t2 hn2 hv2 hb2
  obtain ⟨hB2, hE2, hL2, hH2⟩ := hs2
  refine ⟨?_, fun c => ?_, ?_, ?_⟩
  · rw [Tree.block, hls]
    simp only [↓reduceIte, Tree.blockLast]
    rw [hB2]
  · rw [endA_node, hls]
    simp only [↓reduceIte, List.sum_nil, add_zero]
    rw [endL_one, hE2]
  · rw [Tree.LoadsR, hev0]
    refine ⟨fun x hx => ?_, by rw [Tree.LoadsRKids, Tree.LoadsRKids]; exact ⟨hL2, trivial⟩⟩
    simp only [loadAddrs, List.mem_filterMap] at hx
    obtain ⟨e, he, hx⟩ := hx
    rw [flat_evs] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ⟨a, ha, rfl⟩ | rfl | rfl
    · exact loadAddr_of_loadOk hbase (List.all_eq_true.mp hok a ha) hx
    · simp [Ev.loadAddr?] at hx
    · split at hx <;> simp [Ev.loadAddr?] at hx
  · rw [Tree.HintsR, hev0]
    refine ⟨fun x hx => ?_, by rw [Tree.HintsRKids, Tree.HintsRKids]; exact ⟨hH2, trivial⟩⟩
    rw [heapHintAddrs] at hx
    obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    rw [flat_evs] at he
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with ⟨a, ha, rfl⟩ | rfl | rfl
    · have hk := List.all_eq_true.mp hok a ha
      cases a with
      | hint hh => simp [loadOkB] at hk
      | _ => simp [Ev.hintAddrs] at hx
    · simp [Ev.hintAddrs] at hx
    · split at hx <;> simp [Ev.hintAddrs] at hx

/-! ## Forward evaluation's atoms -/

section Fwd

variable {rd : Reader} {w : ℕ → E} {args : List E} {body : List Stmt} {c' : ℕ}

/-- **An atom needing no side condition holds** under forward evaluation. -/
theorem fwd_holds_noSide (h : chk args.length body = some c') {a : Atom} (ha : Stmt.atom a ∈ body)
    (hn : needsSide a = false) : a.Holds rd (fwdVal rd w args body) :=
  atoms_holds (S := storesOf args.length body) (w := w) (atoms := [a])
    (fun b hb => by rw [List.mem_singleton] at hb; subst hb; exact fwd_good h b ha)
    (fun b hb hb' => by rw [List.mem_singleton] at hb; subst hb; rw [hn] at hb'; cases hb')
    a List.mem_cons_self

/-- **A load that is no store, reading a defined word, holds** under forward evaluation. -/
theorem fwd_holds_load (h : chk args.length body = some c') {d p : V} {off : ℕ}
    (ha : Stmt.atom (.load d p off) ∈ body) (hS : Atom.load d p off ∉ storesOf args.length body)
    (hm : ∃ v, LoadHolds rd (fwdVal rd w args body p) off v) :
    (Atom.load d p off).Holds rd (fwdVal rd w args body) := by
  refine holds_of_good (fwd_good h _ ha) ?_
  obtain ⟨v, hv⟩ := hm
  simp only [Side, hS, ↓reduceIte]
  exact ⟨hv.1, by rw [hv.2]; rfl⟩

end Fwd

end
end LeanVM.Guest.B1.VsC
