/-
  LeanVM.Guest.B1.VsC.LeafA

  A leaf with its own `HeapBuf`s completes placed: a valuation per memory, or a straight body's
  forward evaluation, its buffers at the cursor.
-/

module

public import LeanVM.Guest.Complete.ComposeA
public import LeanVM.Guest.B1.VsC.FwdStore

/-!
# Placed leaves with their own buffers

`callAtA_node` fixes the valuation before the memory, as a node with callees must. A leaf (no
call, not a loop helper) need not: `callAtA_leaf` places it from a valuation chosen per memory,
its `HeapBuf`s `bufs` at the cursor `c` (`NodeAt`), its own words `W` in them or its frame, its
loads in its buffers or the caller's region `R`, ending at `c + bufs.sum`.

`callAtA_fwd`: a straight body (`leafChecks`: the forward checker passes, it returns, no atom pops,
takes a frame address or hints into the heap) on its forward evaluation `fwdVal rd w args`, the
oracle `w` giving each `HeapBuf` pointer. The caller gives each non-store atom's side condition,
each store from the other atoms (the body's own words written, its template's values), the
returns, the buffers' sizes and pointers, and where the loads read. This is `callCompletes_stores`'
setting with output arrays that are the body's own `alloc`/`allocDyn` buffers, and stores whose
words come from the template rather than the relation (so a body may read back what it stored).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- The `HeapBuf`s `bufs` from `c` cover `[c, c + bufs.sum)`. -/
theorem bufs_cover : ∀ (bufs : List ℕ) (c i : ℕ), c ≤ i → i < c + bufs.sum →
    ∃ q ∈ bufs.zip (bases c bufs), q.2 ≤ i ∧ i < q.2 + q.1
  | [], c, i, h1, h2 => by simp at h2; omega
  | s :: ss, c, i, h1, h2 => by
    rw [bases, List.zip_cons_cons]
    by_cases hi : i < c + s
    · exact ⟨(s, c), List.mem_cons_self, h1, by omega⟩
    · rw [List.sum_cons] at h2
      obtain ⟨q, hq, h⟩ := bufs_cover ss (c + s) i (by omega) (by omega)
      exact ⟨q, List.mem_cons_of_mem _ hq, h⟩

/-- **A leaf completes placed** from a valuation per memory: its `HeapBuf`s `bufs` at `c`, its own
words in them or its frame, its loads and heap hints in them or `R`. -/
theorem callAtA_leaf {k : ℕ} {f : String} {args rets : List E} {R D : ℕ → Prop} {Out Pre : Reader → Prop}
    {Post : Reader → Tree → Prop} {fp c : ℕ} (bufs : List ℕ) (W : Words) (hlp : coreProgram.loop f = false)
    (hW : WordsInA W (fp + 2) (fp + fs f) c (c + bufs.sum)) (hO : ∀ rd, HoldsWords rd W → Out rd)
    (hD : ∀ i, D i → c ≤ i ∧ i < c + bufs.sum)
    (h : ∀ rd, LowDef k rd → HoldsWords rd W → Pre rd → ∃ (σ : Val) (fn : Fn) (es : List Ev) (vs : List V),
      coreProgram.find? f = some fn ∧ fn.params.map σ = args ∧ walk σ fn.body = .ret es vs ∧
      vs.map σ = rets ∧ calls es = [] ∧ allocs σ es = bufs ∧ NodeAt cert (fp, c) f σ bufs es ∧
      (∀ ev ∈ es, ev.Holds rd σ) ∧
      (∀ A ∈ loadAddrs σ es, ∃ i, A = addressOfIndex i ∧ ((c ≤ i ∧ i < c + bufs.sum) ∨ R i)) ∧
      (∀ A ∈ heapHintAddrs σ es, ∃ i, A = addressOfIndex i ∧ ((c ≤ i ∧ i < c + bufs.sum) ∨ R i)) ∧
      Post rd (.node f σ bufs [])) :
    CallAtA fs al cert k f args rets R D Out Pre Post (fs f) fp c (c + bufs.sum) := by
  refine ⟨W, hW, by omega, hO, fun rd hl hw hp => ?_⟩
  obtain ⟨σ, fn, es, vs, hf, hpar, hwk, hret, hcalls, hbufs, hnode, hev, hlo, hhi, hpost⟩ := h rd hl hw hp
  have hev' : (Memory.Tree.node f σ bufs []).events coreProgram = es := Complete.events_node hf hwk
  have hown : ∀ i, ((c ≤ i ∧ i < c + bufs.sum) ∨ R i) →
      (Memory.Tree.node f σ bufs []).DataA coreProgram fs al cert (fp, c) i ∨ R i := fun i hi => by
    rcases hi with hi | hi
    · exact Or.inl (dataA_node.mpr (Or.inl (Or.inl (bufs_cover bufs c i hi.1 hi.2))))
    · exact Or.inr hi
  refine ⟨.node f σ bufs [], rfl, ⟨fn, hf, hpar, es, vs, hwk, hret, hev, by rw [hcalls]; exact kidsValid_nil⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, hpost⟩
  · rw [Tree.BufsOk, hev', hbufs]; exact ⟨rfl, by rw [Tree.BufsOkKids]; trivial⟩
  · rw [Tree.block, hlp]; simp
  · rw [endA_node, hlp]; simp [endF_nil]
  · rw [placedA_node, hev']; exact ⟨hnode, placedKidsA_nil⟩
  · rw [loadsInA_node, hev']
    refine ⟨fun A hA => ?_, loadsInKidsA_nil⟩
    obtain ⟨i, hi, hm⟩ := hlo A hA
    exact ⟨i, hi, hown i hm⟩
  · rw [hintsIn_node, hev']
    refine ⟨fun A hA => ?_, hintsInKids_nil⟩
    obtain ⟨i, hi, hm⟩ := hhi A hA
    exact ⟨i, hi, hown i hm⟩
  · obtain ⟨h1, h2⟩ := hD i hi
    exact dataA_node.mpr (Or.inl (Or.inl (bufs_cover bufs c i h1 h2)))

/-! ## Straight bodies -/

/-- An atom of a placed straight leaf: no witness hint, no frame address, no hint into the heap. -/
def leafAtomOk (a : Atom) : Bool :=
  atomQuiet a && (match a with | .frameAddr .. => false | _ => true) && (atomHeapDest? a).isNone

/-- What the kernel checks of a placed straight leaf on `n` parameters. -/
def leafChecks (n : ℕ) (B : List Stmt) : Bool :=
  (chk n B).isSome && (retOf B).isSome && (atomsOf B).all leafAtomOk

theorem atomsOf_append_ret : ∀ (ss : List Stmt) (vs : List V), atomsOf (ss ++ [.ret vs]) = atomsOf ss
  | [], _ => rfl
  | s :: ss, vs => by
    cases s with
    | atom a => simp only [List.cons_append, atomsOf, atomsOf_append_ret ss vs]
    | _ => simpa only [List.cons_append, atomsOf] using atomsOf_append_ret ss vs

theorem addrs_atoms : ∀ (as : List Atom), (as.all fun a => match a with | .frameAddr .. => false | _ => true) →
    addrs (as.map Ev.atom) = []
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, addrs, List.filterMap_cons] at *
    cases a with
    | frameAddr => simp at h
    | _ => exact addrs_atoms as h.2

theorem heapHintAddrs_atoms {σ : Val} : ∀ (as : List Atom), (as.all fun a => (atomHeapDest? a).isNone) →
    heapHintAddrs σ (as.map Ev.atom) = []
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := heapHintAddrs_atoms (σ := σ) as h.2
    simp only [heapHintAddrs, List.map_cons, List.flatMap_cons] at ih ⊢
    rw [ih, List.append_nil]
    cases a with
    | hint hh =>
      simp only [atomHeapDest?, Option.isNone_iff_eq_none] at h
      simp only [Ev.hintAddrs, h.1]
    | _ => rfl

/-- A load address of a path of atoms is a load atom's. -/
theorem mem_loadAddrs {σ : Val} {as : List Atom} {A : K} (h : A ∈ loadAddrs σ (as.map Ev.atom)) :
    ∃ d p off, Atom.load d p off ∈ as ∧ A = (σ p).limb 0 * addressOfIndex off := by
  simp only [loadAddrs, List.filterMap_map, List.mem_filterMap, Function.comp] at h
  obtain ⟨a, ha, he⟩ := h
  cases a with
  | load d p off =>
    simp only [Ev.loadAddr?, Option.some.injEq] at he
    exact ⟨d, p, off, ha, he.symm⟩
  | _ => simp [Ev.loadAddr?] at he

/-- A store is a load. -/
theorem storesOf_isLoad : ∀ {c : ℕ} {ss : List Stmt} {a : Atom}, a ∈ storesOf c ss → ∃ d p o, a = .load d p o
  | _, [], _, h => by simp [storesOf] at h
  | c, s :: ss, a, h => by
    simp only [storesOf, List.mem_append] at h
    rcases h with h | h
    · unfold storeHd at h
      split at h
      · split at h
        · rename_i d p o _
          exact ⟨d, p, o, List.mem_singleton.mp h⟩
        · simp at h
      · simp at h
    · exact storesOf_isLoad h

/-- **A straight leaf with its own buffers completes placed**, on its forward evaluation. -/
theorem callAtA_fwd {k : ℕ} {f : String} {fn : Fn} {args rets : List E} {R D : ℕ → Prop}
    {Out Pre : Reader → Prop} {fp c : ℕ} (w : ℕ → E) (bufs : List ℕ) (W : Words)
    (hfind : coreProgram.find? f = some fn) (hlp : coreProgram.loop f = false)
    (hparams : fn.params = (List.range args.length).map V.n) (hck : leafChecks args.length fn.body = true)
    (hW : WordsInA W (fp + 2) (fp + fs f) c (c + bufs.sum)) (hO : ∀ rd, HoldsWords rd W → Out rd)
    (hD : ∀ i, D i → c ≤ i ∧ i < c + bufs.sum)
    (h : ∀ rd, LowDef k rd → HoldsWords rd W → Pre rd → ∀ σ, σ = fwdVal rd w args fn.body →
      (∀ a, Stmt.atom a ∈ fn.body → a ∉ storesOf args.length fn.body → needsSide a = true →
        Side rd (storesOf args.length fn.body) σ a) ∧
      ((∀ a, Stmt.atom a ∈ fn.body → a ∉ storesOf args.length fn.body → a.Holds rd σ) →
        ∀ a ∈ storesOf args.length fn.body, a.Holds rd σ) ∧
      (∀ a, Stmt.atom a ∈ fn.body → a.Exact rd σ) ∧
      (∀ vs, retOf fn.body = some vs → vs.map σ = rets) ∧
      allocs σ ((atomsOf fn.body).map Ev.atom) = bufs ∧
      (allocDsts ((atomsOf fn.body).map Ev.atom)).map σ = (bases c bufs).map (fun b => ofK (addressOfIndex b)) ∧
      ∀ A ∈ loadAddrs σ ((atomsOf fn.body).map Ev.atom), ∃ i, A = addressOfIndex i ∧
        ((c ≤ i ∧ i < c + bufs.sum) ∨ R i)) :
    CallAtA fs al cert k f args rets R D Out Pre PostQuiet (fs f) fp c (c + bufs.sum) := by
  simp only [leafChecks, Bool.and_eq_true] at hck
  obtain ⟨⟨hc, hr⟩, hok⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨vs, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  have hat : atomsOf fn.body = atomsOf ss := by rw [hbody, atomsOf_append_ret]
  have hok' : ∀ a ∈ atomsOf ss, leafAtomOk a = true := fun a ha => List.all_eq_true.mp hok a (hat ▸ ha)
  have hq : (atomsOf ss).all atomQuiet = true := List.all_eq_true.mpr fun a ha => by
    have := hok' a ha; simp only [leafAtomOk, Bool.and_eq_true] at this; exact this.1.1
  have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs] := by rw [hbody, ← eq_map_atomsOf hss]
  refine callAtA_leaf bufs W hlp hW hO hD fun rd hl hw hp => ?_
  set σ := fwdVal rd w args fn.body with hσ
  obtain ⟨hside, hst, hex, hret, hal, hdst, hlo⟩ := h rd hl hw hp σ rfl
  have hw' : walk σ fn.body = .ret ((atomsOf ss).map Ev.atom) vs := by rw [hb']; exact walk_atoms _ _ vs
  set S := storesOf args.length fn.body
  have hG : ∀ a, Stmt.atom a ∈ fn.body → Good rd S w σ a := fwd_good hc
  have hns : ∀ a, Stmt.atom a ∈ fn.body → a ∉ S → a.Holds rd σ := fun a ha hS =>
    atoms_holds (atoms := [a]) (fun b hb => by rw [List.mem_singleton.mp hb]; exact hG a ha)
      (fun b hb hn => by rw [List.mem_singleton.mp hb] at hn ⊢; exact Or.inr (hside a ha hS hn)) a
      List.mem_cons_self
  have hA : ∀ a, Stmt.atom a ∈ fn.body → a.Holds rd σ := fun a ha => by
    by_cases hS : a ∈ S
    · exact hst hns a hS
    · exact hns a ha hS
  have hmem : ∀ a ∈ atomsOf ss, Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody]; exact List.mem_append_left _ (mem_of_mem_atomsOf ha)
  have hframe : ((atomsOf ss).all fun a => match a with | .frameAddr .. => false | _ => true) = true :=
    List.all_eq_true.mpr fun a ha => by
      have := hok' a ha; simp only [leafAtomOk, Bool.and_eq_true] at this; exact this.1.2
  have hheap : ((atomsOf ss).all fun a => (atomHeapDest? a).isNone) = true :=
    List.all_eq_true.mpr fun a ha => by
      have := hok' a ha; simp only [leafAtomOk, Bool.and_eq_true] at this; exact this.2
  rw [hat] at hal hdst hlo
  refine ⟨σ, fn, (atomsOf ss).map Ev.atom, vs, hfind, by rw [hparams]; exact fwd_params hc, hw', hret vs hr,
    calls_atoms _, hal, ⟨hdst, by rw [addrs_atoms _ hframe]; simp⟩,
    holds_atoms fun a h' => hA a (hmem a h'), hlo, by rw [heapHintAddrs_atoms _ hheap]; simp, ?_, ?_⟩
  · rw [Tree.pops_node (P := coreProgram) hfind hw']; exact splice_quiet _ hq _
  · rw [Tree.every_node]
    refine ⟨fun e he => ?_, by rw [Tree.EveryKids]; trivial⟩
    rw [Complete.events_node hfind hw'] at he
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp he
    exact hex a (hmem a ha')

/-- **A straight leaf completes placed** on a valuation per memory whose atoms hold and are exact:
`callCompletes0_straightRd` placed, its `HeapBuf`s `bufs` at `c`. -/
theorem callAtA_straight {k : ℕ} {f : String} {fn : Fn} {args rets : List E} {R D : ℕ → Prop}
    {Out Pre : Reader → Prop} {fp c : ℕ} (σ : Reader → Val) (bufs : List ℕ) (W : Words)
    (hfind : coreProgram.find? f = some fn) (hlp : coreProgram.loop f = false)
    (hck : ((retOf fn.body).isSome && (atomsOf fn.body).all leafAtomOk) = true)
    (hW : WordsInA W (fp + 2) (fp + fs f) c (c + bufs.sum)) (hO : ∀ rd, HoldsWords rd W → Out rd)
    (hD : ∀ i, D i → c ≤ i ∧ i < c + bufs.sum)
    (h : ∀ rd, LowDef k rd → HoldsWords rd W → Pre rd →
      fn.params.map (σ rd) = args ∧ (∀ vs, retOf fn.body = some vs → vs.map (σ rd) = rets) ∧
      (∀ a, Stmt.atom a ∈ fn.body → a.Holds rd (σ rd) ∧ a.Exact rd (σ rd)) ∧
      allocs (σ rd) ((atomsOf fn.body).map Ev.atom) = bufs ∧
      (allocDsts ((atomsOf fn.body).map Ev.atom)).map (σ rd) = (bases c bufs).map (fun b => ofK (addressOfIndex b)) ∧
      ∀ A ∈ loadAddrs (σ rd) ((atomsOf fn.body).map Ev.atom), ∃ i, A = addressOfIndex i ∧
        ((c ≤ i ∧ i < c + bufs.sum) ∨ R i)) :
    CallAtA fs al cert k f args rets R D Out Pre PostQuiet (fs f) fp c (c + bufs.sum) := by
  simp only [Bool.and_eq_true] at hck
  obtain ⟨hr, hok⟩ := hck
  obtain ⟨vs, hr⟩ := Option.isSome_iff_exists.mp hr
  obtain ⟨ss, hbody, hss⟩ := retOf_spec hr
  have hat : atomsOf fn.body = atomsOf ss := by rw [hbody, atomsOf_append_ret]
  have hok' : ∀ a ∈ atomsOf ss, leafAtomOk a = true := fun a ha => List.all_eq_true.mp hok a (hat ▸ ha)
  have hq : (atomsOf ss).all atomQuiet = true := List.all_eq_true.mpr fun a ha => by
    have := hok' a ha; simp only [leafAtomOk, Bool.and_eq_true] at this; exact this.1.1
  have hb' : fn.body = (atomsOf ss).map Stmt.atom ++ [.ret vs] := by rw [hbody, ← eq_map_atomsOf hss]
  refine callAtA_leaf bufs W hlp hW hO hD fun rd hl hw hp => ?_
  obtain ⟨hpar, hret, hA, hal, hdst, hlo⟩ := h rd hl hw hp
  have hw' : walk (σ rd) fn.body = .ret ((atomsOf ss).map Ev.atom) vs := by rw [hb']; exact walk_atoms _ _ vs
  have hmem : ∀ a ∈ atomsOf ss, Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody]; exact List.mem_append_left _ (mem_of_mem_atomsOf ha)
  have hframe : ((atomsOf ss).all fun a => match a with | .frameAddr .. => false | _ => true) = true :=
    List.all_eq_true.mpr fun a ha => by
      have := hok' a ha; simp only [leafAtomOk, Bool.and_eq_true] at this; exact this.1.2
  have hheap : ((atomsOf ss).all fun a => (atomHeapDest? a).isNone) = true :=
    List.all_eq_true.mpr fun a ha => by
      have := hok' a ha; simp only [leafAtomOk, Bool.and_eq_true] at this; exact this.2
  rw [hat] at hal hdst hlo
  refine ⟨σ rd, fn, (atomsOf ss).map Ev.atom, vs, hfind, hpar, hw', hret vs hr, calls_atoms _, hal,
    ⟨hdst, by rw [addrs_atoms _ hframe]; simp⟩, holds_atoms fun a h' => (hA a (hmem a h')).1, hlo,
    by rw [heapHintAddrs_atoms _ hheap]; simp, ?_, ?_⟩
  · rw [Tree.pops_node (P := coreProgram) hfind hw']; exact splice_quiet _ hq _
  · rw [Tree.every_node]
    refine ⟨fun e he => ?_, by rw [Tree.EveryKids]; trivial⟩
    rw [Complete.events_node hfind hw'] at he
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp he
    exact (hA a (hmem a ha')).2

end
end LeanVM.Guest.B1.VsC
