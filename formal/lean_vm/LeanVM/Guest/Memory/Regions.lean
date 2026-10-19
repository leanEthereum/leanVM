/-
  LeanVM.Guest.Memory.Regions

  Where the loads of a placed call tree read: in its own data (its `HeapBuf`s and `frameAddr`
  runs) or in a region its caller hands it; the placed relation indexed by that region
  (`RelAtIn`), its composition along a path, the pure subtrees, and the global consequence: every
  load of `main`'s tree reads a `HeapBuf`, a run, or a word outside every frame.
-/

module

public import LeanVM.Guest.Memory.Placed

/-!
# Load regions

The honest memory holds every frame cell; a load landing in a frame cell that is not a
`frameAddr` run would have to read what that frame holds, which nothing in a completeness proof
controls. So completeness records where its loads read, compositionally:

* `Tree.Data P fs cert fp t`: the words of the subtree's data, every instance's `HeapBuf`s and
  `frameAddr` runs as `Tree.Placed` places them;
* `Tree.LoadsIn P fs cert R fp t`: every load of an instance reads its subtree's data or the
  region `R` its caller hands it, a callee getting its caller's subtree's data and `R`;
* `RelAtIn P fs cert rd R D fp n f args rets`: `RelAt` by a tree whose loads are in `R` and whose
  data contains `D` (the data the caller relies on afterwards, e.g. a `HeapBuf` a callee returns).

**Composition** (`relAtIn_of_walk`, `relAtIn_of_walk_loop`): as `relAt_of_walk`, the callees by
`KidsFromIn`, each in a region within the caller's region, its own data (`ownData`) and the data
earlier callees claimed; the caller's own loads in its own data, its region or what its callees
claimed.

**Pure subtrees.** A subtree with no `HeapBuf` and no `frameAddr` has no data, so its loads read
its region only, wherever it is placed. `Program.RelIn P rd R` is `Program.Rel` by a tree whose
loads all read `R`, proved along a path by `relIn_of_walk`; `relAtIn_of_relIn_pure` places it
anywhere, and `relIn_of_rel_noLoads` gives it for free to a call-closed set without loads.

**At the root** (`loads_classified`): if `main`'s tree is `LoadsIn R` at word `0`, every load
reads an instance's `HeapBuf`, a cell of an instance's run, or `R` (static data outside every
frame), which is what the honest memory's discharge needs of loads.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## Runs and loads of a path -/

/-- An event's `frameAddr` run: its first value and its length. -/
def Ev.run? : Ev → Option (V × ℕ)
  | .atom (.frameAddr _ (r :: rs)) => some (r, rs.length + 1)
  | _ => none

/-- The `frameAddr` runs of a path. -/
def runs (es : List Ev) : List (V × ℕ) := es.filterMap Ev.run?

/-- The address an event loads from. -/
def Ev.loadAddr? (σ : Val) : Ev → Option K
  | .atom (.load _ p off) => some ((σ p).limb 0 * gpow off)
  | _ => none

/-- The addresses a path loads from. -/
def loadAddrs (σ : Val) (es : List Ev) : List K := es.filterMap (Ev.loadAddr? σ)

variable (P : Core.Program) (fs : String → ℕ) (cert : String → V → ℕ)

/-- **An instance's own data**: its `HeapBuf`s from `b`, and its `frameAddr` runs in its frame. -/
def ownData (fp b : ℕ) (f : String) (bufs : List ℕ) (es : List Ev) (i : ℕ) : Prop :=
  (∃ q ∈ bufs.zip (bases b bufs), q.2 ≤ i ∧ i < q.2 + q.1) ∨
    ∃ q ∈ runs es, fp + cert f q.1 ≤ i ∧ i < fp + cert f q.1 + q.2

mutual
/-- **A subtree's data**: the own data of its instances placed from `fp`. -/
def Tree.Data (fp : ℕ) : Tree → ℕ → Prop
  | t@(.node f _ bufs kids), i =>
      ownData cert fp (bufBase fs P.loop fp f (kids.map (Tree.total fs))) f bufs (t.events P) i ∨
        Tree.DataKids (kidPos fs P.loop fp f bufs (kids.map (Tree.total fs))) kids i
  | .phantom .., _ => False

/-- The data of the callees `ks` placed at `ps`. -/
def Tree.DataKids : List ℕ → List Tree → ℕ → Prop
  | _, [], _ => False
  | [], _ :: _, _ => False
  | p :: ps, k :: ks, i => k.Data p i ∨ Tree.DataKids ps ks i
end

mutual
/-- **Loads in a region**: every load of every instance of `t` placed from `fp` reads its
subtree's data or `R`; a callee's region is its caller's subtree's data and `R`. -/
def Tree.LoadsIn : (ℕ → Prop) → ℕ → Tree → Prop
  | R, fp, t@(.node f σ bufs kids) =>
      (∀ A ∈ loadAddrs σ (t.events P), ∃ i, A = gpow i ∧ (t.Data P fs cert fp i ∨ R i)) ∧
        Tree.LoadsInKids (fun i => t.Data P fs cert fp i ∨ R i)
          (kidPos fs P.loop fp f bufs (kids.map (Tree.total fs))) kids
  | _, _, .phantom .. => True

/-- `Tree.LoadsIn` of the callees `ks` at `ps`. -/
def Tree.LoadsInKids : (ℕ → Prop) → List ℕ → List Tree → Prop
  | _, _, [] => True
  | _, [], _ :: _ => True
  | R, p :: ps, k :: ks => k.LoadsIn R p ∧ Tree.LoadsInKids R ps ks
end

/-- **`Program.Rel` placed at `fp`, loading from `R`**: `RelAt` by a tree whose loads read its
data or `R`, and whose data contains `D`. -/
def RelAtIn (rd : Reader) (R D : ℕ → Prop) (fp n : ℕ) (f : String) (args rets : List E) : Prop :=
  ∃ t : Tree, t.name = f ∧ t.Valid P rd args rets ∧ t.BufsOk P ∧ t.Placed P fs cert fp ∧
    t.total fs = n ∧ t.LoadsIn P fs cert R fp ∧ ∀ i, D i → t.Data P fs cert fp i

/-- **The callees of the frames `cs` sets up**, as `KidsFrom`, each loading from a region within
`R` and the data `Dacc` earlier callees claimed, claiming data `Dk` for the later ones; `Dend`
within all claimed. -/
def KidsFromIn (rd : Reader) (σ : Val) (R : ℕ → Prop) :
    (ℕ → Prop) → List Call → ℕ → ℕ → (ℕ → Prop) → Prop
  | Dacc, [], _, n, Dend => n = 0 ∧ ∀ i, Dend i → Dacc i
  | Dacc, c :: cs, b, n, Dend => ∃ (m n' : ℕ) (Rk Dk : ℕ → Prop), n = m + n' ∧
      (∀ i, Rk i → R i ∨ Dacc i) ∧
      (if c.taken then RelAtIn P fs cert rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ)
        else m = fs c.f) ∧
      KidsFromIn rd σ R (fun i => Dacc i ∨ (c.taken = true ∧ Dk i)) cs (b + m) n' Dend

variable {P fs cert}

theorem RelAtIn.relAt {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    (h : RelAtIn P fs cert rd R D fp n f args rets) : RelAt P fs cert rd fp n f args rets :=
  let ⟨t, hn, hv, hb, hp, ht, _⟩ := h
  ⟨t, hn, hv, hb, hp, ht⟩

/-! ## Unfolding -/

theorem data_node {fp : ℕ} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {i : ℕ} :
    (Tree.node f σ bufs kids).Data P fs cert fp i ↔
      ownData cert fp (bufBase fs P.loop fp f (kids.map (Tree.total fs))) f bufs
          ((Tree.node f σ bufs kids).events P) i ∨
        Tree.DataKids P fs cert (kidPos fs P.loop fp f bufs (kids.map (Tree.total fs))) kids i := by
  rw [Tree.Data]

theorem data_phantom {fp : ℕ} {f : String} {σ : Val} {i : ℕ} :
    ¬ (Tree.phantom f σ).Data P fs cert fp i := by
  rw [Tree.Data]; exact id

theorem dataKids_cons {p : ℕ} {ps : List ℕ} {k : Tree} {ks : List Tree} {i : ℕ} :
    Tree.DataKids P fs cert (p :: ps) (k :: ks) i ↔ k.Data P fs cert p i ∨ Tree.DataKids P fs cert ps ks i := by
  rw [Tree.DataKids]

theorem not_dataKids_nil {ps : List ℕ} {i : ℕ} : ¬ Tree.DataKids P fs cert ps [] i := by
  cases ps <;> (rw [Tree.DataKids]; exact id)

theorem dataKids_append : ∀ {ps : List ℕ} {ks : List Tree} {ps' : List ℕ} {ks' : List Tree} {i : ℕ},
    ps.length = ks.length →
    (Tree.DataKids P fs cert (ps ++ ps') (ks ++ ks') i ↔
      Tree.DataKids P fs cert ps ks i ∨ Tree.DataKids P fs cert ps' ks' i)
  | [], [], _, _, _, _ => by simp [not_dataKids_nil]
  | p :: ps, k :: ks, _, _, _, hl => by
      rw [List.cons_append, List.cons_append, dataKids_cons, dataKids_cons,
        dataKids_append (by simpa using hl), or_assoc]
  | [], _ :: _, _, _, _, hl => absurd hl (by simp)
  | _ :: _, [], _, _, _, hl => absurd hl (by simp)

theorem loadsIn_node {R : ℕ → Prop} {fp : ℕ} {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} :
    (Tree.node f σ bufs kids).LoadsIn P fs cert R fp ↔
      (∀ A ∈ loadAddrs σ ((Tree.node f σ bufs kids).events P), ∃ i, A = gpow i ∧
        ((Tree.node f σ bufs kids).Data P fs cert fp i ∨ R i)) ∧
      Tree.LoadsInKids P fs cert (fun i => (Tree.node f σ bufs kids).Data P fs cert fp i ∨ R i)
        (kidPos fs P.loop fp f bufs (kids.map (Tree.total fs))) kids := by
  rw [Tree.LoadsIn]

theorem loadsIn_phantom {R : ℕ → Prop} {fp : ℕ} {f : String} {σ : Val} :
    (Tree.phantom f σ).LoadsIn P fs cert R fp := by
  rw [Tree.LoadsIn]; trivial

theorem loadsInKids_cons {R : ℕ → Prop} {p : ℕ} {ps : List ℕ} {k : Tree} {ks : List Tree} :
    Tree.LoadsInKids P fs cert R (p :: ps) (k :: ks) ↔
      k.LoadsIn P fs cert R p ∧ Tree.LoadsInKids P fs cert R ps ks := by
  rw [Tree.LoadsInKids]

theorem loadsInKids_nil {R : ℕ → Prop} {ps : List ℕ} : Tree.LoadsInKids P fs cert R ps [] := by
  cases ps <;> (rw [Tree.LoadsInKids]; trivial)

theorem loadsInKids_append : ∀ {R : ℕ → Prop} {ps : List ℕ} {ks : List Tree} {ps' : List ℕ}
    {ks' : List Tree}, ps.length = ks.length → Tree.LoadsInKids P fs cert R ps ks →
      Tree.LoadsInKids P fs cert R ps' ks' → Tree.LoadsInKids P fs cert R (ps ++ ps') (ks ++ ks')
  | _, [], [], _, _, _, _, h => h
  | _, p :: ps, k :: ks, _, _, hl, h, h' => by
      rw [loadsInKids_cons] at h
      rw [List.cons_append, List.cons_append, loadsInKids_cons]
      exact ⟨h.1, loadsInKids_append (by simpa using hl) h.2 h'⟩
  | _, [], _ :: _, _, _, hl, _, _ => absurd hl (by simp)
  | _, _ :: _, [], _, _, hl, _, _ => absurd hl (by simp)

mutual
/-- A wider region. -/
theorem loadsIn_mono : ∀ (t : Tree) {R R' : ℕ → Prop} (fp : ℕ), (∀ i, R i → R' i) →
    t.LoadsIn P fs cert R fp → t.LoadsIn P fs cert R' fp
  | .node f σ bufs kids, R, R', fp, hR, h => by
      rw [loadsIn_node] at h ⊢
      refine ⟨fun A hA => ?_, loadsInKids_mono kids _ (fun i => Or.imp_right (hR i)) h.2⟩
      obtain ⟨i, hi, h'⟩ := h.1 A hA
      exact ⟨i, hi, h'.imp_right (hR i)⟩
  | .phantom .., _, _, _, _, _ => loadsIn_phantom

/-- `loadsIn_mono` for the callees. -/
theorem loadsInKids_mono : ∀ (ks : List Tree) {R R' : ℕ → Prop} (ps : List ℕ),
    (∀ i, R i → R' i) → Tree.LoadsInKids P fs cert R ps ks → Tree.LoadsInKids P fs cert R' ps ks
  | [], _, _, _, _, _ => loadsInKids_nil
  | _ :: _, _, _, [], _, _ => by rw [Tree.LoadsInKids]; trivial
  | k :: ks, R, R', p :: ps, hR, h => by
      rw [loadsInKids_cons] at h ⊢
      exact ⟨loadsIn_mono k p hR h.1, loadsInKids_mono ks ps hR h.2⟩
end

/-! ## Composition -/

section Compose

variable {rd : Reader} {σ : Val}

/-- The callee of one frame, its loads in its region and its data containing its claim. -/
theorem kid_ofIn {c : Call} {b m : ℕ} {Rk Dk : ℕ → Prop}
    (hc : c.taken = false → P.Takes c.f c.args.length = true)
    (h : if c.taken then RelAtIn P fs cert rd Rk Dk b m c.f (c.args.map σ) (c.rets.map σ)
      else m = fs c.f) :
    ∃ k : Tree, Tree.KidsValid P rd σ [c] [k] ∧ k.BufsOk P ∧ k.Placed P fs cert b ∧
      k.total fs = m ∧ k.LoadsIn P fs cert Rk b ∧ (c.taken = true → ∀ i, Dk i → k.Data P fs cert b i) := by
  by_cases ht : c.taken = true
  · rw [ite_eq_left ht] at h
    obtain ⟨k, hn, hv, hb, hp, htot, hl, hd⟩ := h
    exact ⟨k, ⟨hn, by rw [ite_eq_left ht]; exact hv, trivial⟩, hb, hp, htot, hl, fun _ => hd⟩
  · rw [ite_eq_right ht] at h
    obtain ⟨k, hkv, hkb, hkp, hkt⟩ := kid_of (P := P) (fs := fs) (cert := cert) (rd := rd)
      (σ := σ) (b := b) (m := m) hc (by rw [ite_eq_right ht]; exact h)
    have hk := hkv.2.1
    rw [ite_eq_right ht] at hk
    obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
    exact ⟨_, hkv, hkb, hkp, hkt, loadsIn_phantom, fun h' => absurd h' ht⟩

/-- The callees of `KidsFromIn`, placed one after another from `b`. -/
theorem kids_of_kidsFromIn (R : ℕ → Prop) : ∀ (cs : List Call) (Dacc : ℕ → Prop) (b n : ℕ)
    (Dend : ℕ → Prop), (∀ c ∈ cs, c.taken = false → P.Takes c.f c.args.length = true) →
    KidsFromIn P fs cert rd σ R Dacc cs b n Dend →
    ∃ ks : List Tree, Tree.KidsValid P rd σ cs ks ∧ Tree.BufsOkKids P ks ∧
      Tree.PlacedKids P fs cert (bases b (ks.map (Tree.total fs))) ks ∧
      (ks.map (Tree.total fs)).sum = n ∧
      (∀ i, Dend i → Dacc i ∨ Tree.DataKids P fs cert (bases b (ks.map (Tree.total fs))) ks i) ∧
      ∀ Rp : ℕ → Prop, (∀ i, R i → Rp i) → (∀ i, Dacc i → Rp i) →
        (∀ i, Tree.DataKids P fs cert (bases b (ks.map (Tree.total fs))) ks i → Rp i) →
        Tree.LoadsInKids P fs cert Rp (bases b (ks.map (Tree.total fs))) ks
  | [], Dacc, _, n, Dend, _, h => by
      rw [KidsFromIn] at h
      refine ⟨[], by simp [Tree.KidsValid], by rw [Tree.BufsOkKids]; trivial, placedKids_nil,
        by simp [h.1], fun i hi => Or.inl (h.2 i hi), fun _ _ _ _ => loadsInKids_nil⟩
  | c :: cs, Dacc, b, n, Dend, hw, h => by
      rw [KidsFromIn] at h
      obtain ⟨m, n', Rk, Dk, rfl, hRk, hc, hcs⟩ := h
      obtain ⟨k, hkv, hkb, hkp, hkt, hkl, hkd⟩ := kid_ofIn (hw c List.mem_cons_self) hc
      obtain ⟨ks, hv, hb, hp, hs, hd, hl⟩ := kids_of_kidsFromIn R cs _ (b + m) n' Dend
        (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) hcs
      have hpos : bases b ((k :: ks).map (Tree.total fs)) = b :: bases (b + m) (ks.map (Tree.total fs)) := by
        rw [List.map_cons, bases, hkt]
      refine ⟨k :: ks, ⟨hkv.1, hkv.2.1, hv⟩, by rw [Tree.BufsOkKids]; exact ⟨hkb, hb⟩, ?_, ?_, ?_, ?_⟩
      · rw [hpos, placedKids_cons]; exact ⟨hkp, hp⟩
      · rw [List.map_cons, List.sum_cons, hkt, hs]
      · intro i hi
        rw [hpos, dataKids_cons]
        rcases hd i hi with (h | ⟨ht, h⟩) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (hkd ht i h))
        · exact Or.inr (Or.inr h)
      · intro Rp hR hD hK
        rw [hpos] at hK ⊢
        rw [loadsInKids_cons]
        refine ⟨loadsIn_mono k b (fun i hi => (hRk i hi).elim (hR i) (hD i)) hkl,
          hl Rp hR (fun i hi => ?_) (fun i hi => hK i (dataKids_cons.mpr (Or.inr hi)))⟩
        rcases hi with h | ⟨ht, h⟩
        · exact hD i h
        · exact hK i (dataKids_cons.mpr (Or.inl (hkd ht i h)))

/-- **Composition with regions**, a function that is not a loop helper (or whose path calls
nothing): as `relAt_of_walk`, its callees in `KidsFromIn` from its region and its own data, its
loads in its own data, its region or its callees' claims, and its claim within its own data and
its callees' claims. -/
theorem relAtIn_of_walk (hP : P.Wf) {R D Dk : ℕ → Prop} {fp N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} (hf : P.find? f = some fn)
    (hl : P.loop f = false ∨ calls es = []) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFromIn P fs cert rd σ (fun i => R i ∨ ownData cert fp (fp + fs f) f (allocs σ es) es i)
      (fun _ => False) (calls es) (fp + fs f + (allocs σ es).sum) N Dk)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
      (ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ R i ∨ Dk i))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f) f (allocs σ es) es i ∨ Dk i) :
    RelAtIn P fs cert rd R D fp (fs f + (allocs σ es).sum + N) f args rets := by
  obtain ⟨ks, hkv, hkb, hkp, hks, hkd, hkl⟩ :=
    kids_of_kidsFromIn _ _ _ _ _ _ (takes_of_calls hP (List.mem_of_find?_eq_some hf) hw) hk
  have hl' : P.loop f = false ∨ ks.map (Tree.total fs) = [] := by
    rcases hl with hl | hl
    · exact Or.inl hl
    · rw [hl] at hkv
      cases ks with
      | nil => exact Or.inr rfl
      | cons _ _ => exact hkv.elim
  obtain ⟨hbb, hkpos⟩ := kidPos_not_loop (fs := fs) (fp := fp) (bufs := allocs σ es) hl'
  have hdata : ∀ i, (Tree.node f σ (allocs σ es) ks).Data P fs cert fp i ↔
      ownData cert fp (fp + fs f) f (allocs σ es) es i ∨
        Tree.DataKids P fs cert (bases (fp + fs f + (allocs σ es).sum) (ks.map (Tree.total fs))) ks i := by
    intro i
    rw [data_node, events_node hf hw, hbb, hkpos]
  refine ⟨.node f σ (allocs σ es) ks, rfl, ⟨fn, hf, hp, es, vs, hw, hr, hes, hkv⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Tree.BufsOk, events_node hf hw]
    exact ⟨rfl, hkb⟩
  · rw [placed_node, events_node hf hw, NodeAt, hbb, hkpos]
    exact ⟨⟨hbuf, haddr⟩, hkp⟩
  · rw [total_node, totalKids_eq_sum, hks]
    omega
  · rw [loadsIn_node, events_node hf hw, hkpos]
    refine ⟨fun A hA => ?_, hkl _ (fun i hi => ?_) (fun _ h => h.elim) (fun i hi => ?_)⟩
    · obtain ⟨i, hi, h⟩ := hload A hA
      refine ⟨i, hi, ?_⟩
      rw [hdata]
      rcases h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact (hkd i h).elim (fun h => h.elim) fun h => Or.inl (Or.inr h)
    · rcases hi with h | h
      · exact Or.inr h
      · exact Or.inl ((hdata i).mpr (Or.inl h))
    · exact Or.inl ((hdata i).mpr (Or.inr hi))
  · intro i hi
    rw [hdata]
    rcases hD i hi with h | h
    · exact Or.inl h
    · exact (hkd i h).elim (fun h => h.elim) fun h => Or.inr h

/-- **Composition with regions**, a loop helper: as `relAt_of_walk_loop`, its tail call loading
from its region, its own data and its other callees' claims, and claiming `Dt`. -/
theorem relAtIn_of_walk_loop (hP : P.Wf) {R D Dk Rt Dt : ℕ → Prop} {fp m N : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} {cs : List Call} {c : Call}
    (hf : P.find? f = some fn) (hl : P.loop f = true) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hc : calls es = cs ++ [c])
    (htail : if c.taken then RelAtIn P fs cert rd Rt Dt (fp + fs f) m c.f (c.args.map σ) (c.rets.map σ)
      else m = fs c.f)
    (hbuf : (allocDsts es).map σ = (bases (fp + fs f + m) (allocs σ es)).map fun b => ofK (gpow b))
    (haddr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cert f q.2)))
    (hk : KidsFromIn P fs cert rd σ (fun i => R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i)
      (fun _ => False) cs (fp + fs f + m + (allocs σ es).sum) N Dk)
    (hRt : ∀ i, Rt i → R i ∨ ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
      (ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ R i ∨ Dk i ∨ (c.taken = true ∧ Dt i)))
    (hD : ∀ i, D i → ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨ Dk i ∨
      (c.taken = true ∧ Dt i)) :
    RelAtIn P fs cert rd R D fp (fs f + m + (allocs σ es).sum + N) f args rets := by
  have htk := takes_of_calls hP (List.mem_of_find?_eq_some hf) hw
  rw [hc] at htk
  obtain ⟨ks, hkv, hkb, hkp, hks, hkd, hkl⟩ := kids_of_kidsFromIn _ _ _ _ _ _
    (fun c' hc' => htk c' (List.mem_append_left _ hc')) hk
  obtain ⟨k, hkv', hkb', hkp', hkt, hkl', hkd'⟩ :=
    kid_ofIn (htk c (List.mem_append_right _ List.mem_cons_self)) htail
  have hns : (ks ++ [k]).map (Tree.total fs) = ks.map (Tree.total fs) ++ [m] := by
    rw [List.map_append, List.map_singleton, hkt]
  have hbb : bufBase fs P.loop fp f ((ks ++ [k]).map (Tree.total fs)) = fp + fs f + m := by
    rw [hns]; simp [bufBase, hl]
  have hkpos : kidPos fs P.loop fp f (allocs σ es) ((ks ++ [k]).map (Tree.total fs)) =
      bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs)) ++ [fp + fs f] := by
    rw [kidPos, ite_eq_left hl, hbb, hns, List.dropLast_concat, List.getLast?_concat]
    rfl
  have hlen : (bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs))).length = ks.length := by
    rw [length_bases, List.length_map]
  have hdata : ∀ i, (Tree.node f σ (allocs σ es) (ks ++ [k])).Data P fs cert fp i ↔
      ownData cert fp (fp + fs f + m) f (allocs σ es) es i ∨
        Tree.DataKids P fs cert (bases (fp + fs f + m + (allocs σ es).sum) (ks.map (Tree.total fs))) ks i ∨
        k.Data P fs cert (fp + fs f) i := by
    intro i
    rw [data_node, events_node hf hw, hbb, hkpos, dataKids_append hlen, dataKids_cons]
    simp only [not_dataKids_nil, or_false]
  refine ⟨.node f σ (allocs σ es) (ks ++ [k]), rfl,
    ⟨fn, hf, hp, es, vs, hw, hr, hes, by rw [hc]; exact kidsValid_append hkv hkv'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Tree.BufsOk, events_node hf hw]
    refine ⟨rfl, bufsOkKids_append hkb ?_⟩
    rw [Tree.BufsOkKids, Tree.BufsOkKids]
    exact ⟨hkb', trivial⟩
  · rw [placed_node, events_node hf hw, NodeAt, hbb, hkpos]
    refine ⟨⟨hbuf, haddr⟩, placedKids_append hlen hkp ?_⟩
    rw [placedKids_cons]
    exact ⟨hkp', placedKids_nil⟩
  · rw [total_node, totalKids_eq_sum, hns, List.sum_append, hks]
    simp only [List.sum_cons, List.sum_nil]
    omega
  · have hDk : ∀ i, Dk i → (Tree.node f σ (allocs σ es) (ks ++ [k])).Data P fs cert fp i := fun i h =>
      (hkd i h).elim (fun h => h.elim) fun h => (hdata i).mpr (Or.inr (Or.inl h))
    have hDt : ∀ i, c.taken = true ∧ Dt i → (Tree.node f σ (allocs σ es) (ks ++ [k])).Data P fs cert fp i :=
      fun i h => (hdata i).mpr (Or.inr (Or.inr (hkd' h.1 i h.2)))
    have hown : ∀ i, ownData cert fp (fp + fs f + m) f (allocs σ es) es i →
        (Tree.node f σ (allocs σ es) (ks ++ [k])).Data P fs cert fp i := fun i h => (hdata i).mpr (Or.inl h)
    rw [loadsIn_node, events_node hf hw, hkpos]
    refine ⟨fun A hA => ?_, loadsInKids_append hlen ?_ ?_⟩
    · obtain ⟨i, hi, h⟩ := hload A hA
      refine ⟨i, hi, ?_⟩
      rcases h with h | h | h | h
      · exact Or.inl (hown i h)
      · exact Or.inr h
      · exact Or.inl (hDk i h)
      · exact Or.inl (hDt i h)
    · exact hkl _ (fun i hi => hi.elim Or.inr fun h => Or.inl (hown i h)) (fun _ h => h.elim)
        (fun i hi => Or.inl ((hdata i).mpr (Or.inr (Or.inl hi))))
    · rw [loadsInKids_cons]
      refine ⟨loadsIn_mono k _ (fun i hi => ?_) hkl', loadsInKids_nil⟩
      rcases hRt i hi with h | h | h
      · exact Or.inr h
      · exact Or.inl (hown i h)
      · exact Or.inl (hDk i h)
  · intro i hi
    rcases hD i hi with h | h | h
    · exact (hdata i).mpr (Or.inl h)
    · exact (hkd i h).elim (fun h => h.elim) fun h => (hdata i).mpr (Or.inr (Or.inl h))
    · exact (hdata i).mpr (Or.inr (Or.inr (hkd' h.1 i h.2)))

end Compose

/-! ## Loads by region only -/

section Pure

variable {S : List String}

mutual
/-- Every load of every instance of `t` reads `R`. -/
def Tree.LoadsR (P : Core.Program) (R : ℕ → Prop) : Tree → Prop
  | t@(.node _ σ _ kids) => (∀ A ∈ loadAddrs σ (t.events P), ∃ i, A = gpow i ∧ R i) ∧
      Tree.LoadsRKids P R kids
  | .phantom .. => True

/-- `Tree.LoadsR` of the callees. -/
def Tree.LoadsRKids (P : Core.Program) (R : ℕ → Prop) : List Tree → Prop
  | [] => True
  | k :: ks => k.LoadsR P R ∧ Tree.LoadsRKids P R ks
end

/-- **`Program.Rel` loading from `R` only**, by a tree whose `HeapBuf`s are its paths'. -/
def _root_.LeanVM.Guest.Core.Program.RelIn (P : Core.Program) (rd : Reader) (R : ℕ → Prop)
    (f : String) (args rets : List E) : Prop :=
  ∃ t : Tree, t.name = f ∧ t.Valid P rd args rets ∧ t.BufsOk P ∧ t.LoadsR P R

theorem _root_.LeanVM.Guest.Core.Program.RelIn.rel {rd : Reader} {R : ℕ → Prop} {f : String} {args rets : List E}
    (h : P.RelIn rd R f args rets) : P.Rel rd f args rets :=
  let ⟨t, hn, hv, _⟩ := h
  hn ▸ hv.rel t

mutual
/-- Loads in `R` are loads in `R` and the subtree's data, wherever it is placed. -/
theorem loadsIn_of_loadsR : ∀ (t : Tree) (R : ℕ → Prop) (fp : ℕ), t.LoadsR P R →
    t.LoadsIn P fs cert R fp
  | .node f σ bufs kids, R, fp, h => by
      rw [Tree.LoadsR] at h
      rw [loadsIn_node]
      refine ⟨fun A hA => ?_, loadsInKids_mono kids _ (fun i hi => Or.inr hi)
        (loadsInKids_of_loadsR kids R _ h.2)⟩
      obtain ⟨i, hi, hR⟩ := h.1 A hA
      exact ⟨i, hi, Or.inr hR⟩
  | .phantom .., _, _, _ => loadsIn_phantom

/-- `loadsIn_of_loadsR` for the callees. -/
theorem loadsInKids_of_loadsR : ∀ (ks : List Tree) (R : ℕ → Prop) (ps : List ℕ),
    Tree.LoadsRKids P R ks → Tree.LoadsInKids P fs cert R ps ks
  | [], _, _, _ => loadsInKids_nil
  | _ :: _, _, [], _ => by rw [Tree.LoadsInKids]; trivial
  | k :: ks, R, p :: ps, h => by
      rw [Tree.LoadsRKids] at h
      rw [loadsInKids_cons]
      exact ⟨loadsIn_of_loadsR k R p h.1, loadsInKids_of_loadsR ks R ps h.2⟩
end

/-- **A function of a pure set loading from `R` is placed anywhere**, loading from `R`. -/
theorem relAtIn_of_relIn_pure (hS : P.PureIn S) {rd : Reader} {R : ℕ → Prop} {g : String}
    (hg : g ∈ S) {args rets : List E} (h : P.RelIn rd R g args rets) :
    ∃ n, ∀ fp, RelAtIn P fs cert rd R (fun _ => False) fp n g args rets := by
  obtain ⟨t, hn, hv, hb, hl⟩ := h
  exact ⟨t.total fs, fun fp => ⟨t, hn, hv, hb, placed_of_pure hS t hv hb (hn ▸ hg) fp, rfl,
    loadsIn_of_loadsR t R fp hl, fun _ h => h.elim⟩⟩

variable {rd : Reader} {σ : Val}

/-- The callees of the frames `cs`: each call entered `RelIn R`, each not a phantom. -/
theorem kids_of_relIn {R : ℕ → Prop} : ∀ cs : List Call,
    (∀ c ∈ cs, c.taken = false → P.Takes c.f c.args.length = true) →
    (∀ c ∈ cs, c.taken = true → P.RelIn rd R c.f (c.args.map σ) (c.rets.map σ)) →
    ∃ ks, Tree.KidsValid P rd σ cs ks ∧ Tree.BufsOkKids P ks ∧ Tree.LoadsRKids P R ks
  | [], _, _ => ⟨[], by simp [Tree.KidsValid], by rw [Tree.BufsOkKids]; trivial,
      by rw [Tree.LoadsRKids]; trivial⟩
  | c :: cs, hw, hc => by
      obtain ⟨ks, hv, hb, hl⟩ := kids_of_relIn cs (fun c' h => hw c' (List.mem_cons_of_mem _ h))
        (fun c' h => hc c' (List.mem_cons_of_mem _ h))
      by_cases ht : c.taken = true
      · obtain ⟨k, hn, hkv, hkb, hkl⟩ := hc c List.mem_cons_self ht
        refine ⟨k :: ks, ⟨hn, by rw [ite_eq_left ht]; exact hkv, hv⟩,
          by rw [Tree.BufsOkKids]; exact ⟨hkb, hb⟩, by rw [Tree.LoadsRKids]; exact ⟨hkl, hl⟩⟩
      · obtain ⟨σ', hph⟩ := phantom_of_takes (P := P) (f := c.f) (ws := c.args.map σ)
          (by rw [List.length_map]; exact hw c List.mem_cons_self (by simpa using ht))
        refine ⟨.phantom c.f σ' :: ks, ⟨rfl, by rw [ite_eq_right ht]; exact ⟨⟨_, _, rfl⟩, hph⟩, hv⟩,
          by rw [Tree.BufsOkKids, Tree.BufsOk]; exact ⟨trivial, hb⟩,
          by rw [Tree.LoadsRKids, Tree.LoadsR]; exact ⟨trivial, hl⟩⟩

/-- **`RelIn` along a path**: the parameters, the path, its loads in `R`, and every call entered
`RelIn R`. -/
theorem relIn_of_walk (hP : P.Wf) {R : ℕ → Prop} {f : String} {args rets : List E} {fn : Fn}
    {es : List Ev} {vs : List V} (hf : P.find? f = some fn) (hp : fn.params.map σ = args)
    (hw : walk σ fn.body = .ret es vs) (hr : vs.map σ = rets) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hload : ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ R i)
    (hk : ∀ c ∈ calls es, c.taken = true → P.RelIn rd R c.f (c.args.map σ) (c.rets.map σ)) :
    P.RelIn rd R f args rets := by
  obtain ⟨ks, hkv, hkb, hkl⟩ := kids_of_relIn (calls es)
    (takes_of_calls hP (List.mem_of_find?_eq_some hf) hw) hk
  refine ⟨.node f σ (allocs σ es) ks, rfl, ⟨fn, hf, hp, es, vs, hw, hr, hes, hkv⟩, ?_, ?_⟩
  · rw [Tree.BufsOk, events_node hf hw]
    exact ⟨rfl, hkb⟩
  · rw [Tree.LoadsR, events_node hf hw]
    exact ⟨hload, hkl⟩

/-! ### Subtrees without loads -/

/-- Neither a `HeapBuf` hint, nor a `frameAddr`, nor a load. -/
def atomQuiet (a : Atom) : Bool :=
  atomUnplaced a && match a with
    | .load .. => false
    | _ => true

mutual
/-- A statement with quiet atoms, calling only functions of `S`. -/
def Stmt.quiet (S : List String) : Stmt → Bool
  | .atom a => atomQuiet a
  | .ite _ z n => Stmt.quietList S z && Stmt.quietList S n
  | .match_ _ arms => Stmt.quietArms S arms
  | .call f _ _ => decide (f ∈ S)
  | .callIf _ f _ => decide (f ∈ S)
  | .dispatch _ fs _ _ => fs.all fun f => decide (f ∈ S)
  | .ret _ => true

/-- `Stmt.quiet` of a block. -/
def Stmt.quietList (S : List String) : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.quiet S s && Stmt.quietList S ss

/-- `Stmt.quiet` of arms. -/
def Stmt.quietArms (S : List String) : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.quietList S a && Stmt.quietArms S as
end

/-- **A call-closed set of quiet functions**: no `HeapBuf` hint, `frameAddr` or load. -/
def _root_.LeanVM.Guest.Core.Program.QuietIn (P : Core.Program) (S : List String) : Prop :=
  ∀ g ∈ S, ∀ fn, P.find? g = some fn → Stmt.quietList S fn.body = true

mutual
theorem quiet_pure : ∀ (s : Stmt), Stmt.quiet S s = true → Stmt.pure S s = true
  | .atom a, h => by
      simp only [Stmt.quiet, atomQuiet, Bool.and_eq_true] at h
      exact h.1
  | .ite _ z n, h => by
      simp only [Stmt.quiet, Stmt.pure, Bool.and_eq_true] at h ⊢
      exact ⟨quietList_pure z h.1, quietList_pure n h.2⟩
  | .match_ _ arms, h => by
      simp only [Stmt.quiet, Stmt.pure] at h ⊢
      exact quietArms_pure arms h
  | .call .., h => h
  | .callIf .., h => h
  | .dispatch .., h => h
  | .ret _, _ => rfl

theorem quietList_pure : ∀ (ss : List Stmt), Stmt.quietList S ss = true → Stmt.pureList S ss = true
  | [], _ => rfl
  | s :: ss, h => by
      simp only [Stmt.quietList, Stmt.pureList, Bool.and_eq_true] at h ⊢
      exact ⟨quiet_pure s h.1, quietList_pure ss h.2⟩

theorem quietArms_pure : ∀ (arms : List (List Stmt)), Stmt.quietArms S arms = true →
    Stmt.pureArms S arms = true
  | [], _ => rfl
  | a :: as, h => by
      simp only [Stmt.quietArms, Stmt.pureArms, Bool.and_eq_true] at h ⊢
      exact ⟨quietList_pure a h.1, quietArms_pure as h.2⟩
end

theorem _root_.LeanVM.Guest.Core.Program.QuietIn.pureIn (h : P.QuietIn S) : P.PureIn S :=
  fun g hg fn hf => quietList_pure fn.body (h g hg fn hf)

/-- An event with a quiet atom. -/
def Ev.quiet : Ev → Prop
  | .atom a => atomQuiet a = true
  | _ => True

theorem pick_quiet {x : V} {args rets : List V} :
    ∀ (gs : List String) (j : ℕ), (pick σ x args rets j gs).All Ev.quiet
  | [], _ => trivial
  | g :: gs, j => by
      unfold pick
      split_ifs
      · intro e he
        rw [List.mem_singleton] at he
        subst he
        trivial
      · exact pick_quiet gs (j + 1)

mutual
theorem walk1_quiet : ∀ (s : Stmt), Stmt.quiet S s = true → (walk1 σ s).All Ev.quiet
  | .atom _, h => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      exact h
  | .ite c z n, h => by
      simp only [Stmt.quiet, Bool.and_eq_true] at h
      rw [walk1]
      refine Out.all_pre (fun e he => by rw [List.mem_singleton] at he; subst he; trivial) ?_
      split_ifs
      · exact walk_quiet z h.1
      · exact walk_quiet n h.2
  | .match_ x arms, h => walkArms_quiet x arms 0 h
  | .call .., _ => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      trivial
  | .callIf c f args, _ => by
      rw [walk1]
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · trivial
      · split_ifs <;> trivial
  | .dispatch x fs args rets, _ => pick_quiet fs 0
  | .ret _, _ => fun _ he => (List.not_mem_nil he).elim

theorem walk_quiet : ∀ (ss : List Stmt), Stmt.quietList S ss = true → (walk σ ss).All Ev.quiet
  | [], _ => fun _ he => (List.not_mem_nil he).elim
  | s :: ss, h => by
      simp only [Stmt.quietList, Bool.and_eq_true] at h
      rw [walk]
      exact Out.all_seq (walk_quiet ss h.2) (walk1_quiet s h.1)

theorem walkArms_quiet (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), Stmt.quietArms S arms = true →
    (walkArms σ x j arms).All Ev.quiet
  | [], _, _ => trivial
  | a :: as, j, h => by
      simp only [Stmt.quietArms, Bool.and_eq_true] at h
      unfold walkArms
      split_ifs
      · exact walk_quiet a h.1
      · exact walkArms_quiet x as (j + 1) h.2
end

theorem loadAddrs_quiet {es : List Ev} (h : ∀ e ∈ es, e.quiet) : loadAddrs σ es = [] := by
  refine List.filterMap_eq_nil_iff.mpr fun e he => ?_
  have := h e he
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _⟩ | _ | _ | _ <;>
    first | rfl | simp [Ev.quiet, atomQuiet, atomUnplaced] at this

mutual
/-- A valid tree of a function of a quiet set loads nothing. -/
theorem loadsR_of_quiet (hS : P.QuietIn S) (R : ℕ → Prop) : ∀ (t : Tree) {args rets : List E},
    t.Valid P rd args rets → t.name ∈ S → t.LoadsR P R
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hn => by
      have hq : ∀ e ∈ es, e.quiet := by
        have := walk_quiet (σ := σ) fn.body (hS f hn fn hf)
        rwa [hw] at this
      rw [Tree.LoadsR, events_node hf hw, loadAddrs_quiet hq]
      refine ⟨fun _ h => (List.not_mem_nil h).elim, loadsRKids_of_quiet hS R kids σ (calls es) hk ?_⟩
      exact calls_pure fun e he => by
        have := hq e he
        have hp := walk_pure (σ := σ) fn.body (quietList_pure fn.body (hS f hn fn hf))
        rw [hw] at hp
        exact hp e he
  | .phantom .., _, _, h, _ => h.elim

/-- `loadsR_of_quiet` for the callees. -/
theorem loadsRKids_of_quiet (hS : P.QuietIn S) (R : ℕ → Prop) : ∀ (ks : List Tree) (σ : Val)
    (cs : List Call), Tree.KidsValid P rd σ cs ks → (∀ c ∈ cs, c.f ∈ S) → Tree.LoadsRKids P R ks
  | [], _, _, _, _ => by rw [Tree.LoadsRKids]; trivial
  | k :: ks, σ, c :: cs, ⟨hn, hc, hks⟩, hS' => by
      rw [Tree.LoadsRKids]
      refine ⟨?_, loadsRKids_of_quiet hS R ks σ cs hks fun c' h => hS' c' (List.mem_cons_of_mem _ h)⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact loadsR_of_quiet hS R k hc (hn ▸ hS' c List.mem_cons_self)
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        rw [Tree.LoadsR]; trivial
  | _ :: _, _, [], h, _ => h.elim
end

/-- **A function of a quiet set is placed anywhere, loading nothing**: `Program.Rel` gives
`RelAtIn` at every frame pointer and region, of one size. -/
theorem relAtIn_of_rel_quiet (hP : P.Wf) (hS : P.QuietIn S) {g : String} (hg : g ∈ S)
    {args rets : List E} (h : P.Rel rd g args rets) :
    ∃ n, ∀ fp R, RelAtIn P fs cert rd R (fun _ => False) fp n g args rets := by
  obtain ⟨t, hn, hv, hb⟩ := Program.Rel.tree hP h
  exact ⟨t.total fs, fun fp R => ⟨t, hn, hv, hb, placed_of_pure hS.pureIn t hv hb (hn ▸ hg) fp, rfl,
    loadsIn_of_loadsR t R fp (loadsR_of_quiet hS R t hv (hn ▸ hg)), fun _ h => h.elim⟩⟩

end Pure

/-! ## At the root -/

section Root

variable {H : Inst → ℕ → E × E}

mutual
/-- **Every load of an instance reads its tree's data or its region.** -/
theorem loads_insts : ∀ (t : Tree) (R : ℕ → Prop) (fp : ℕ) (hdr : E × E), t.LoadsIn P fs cert R fp →
    ∀ I ∈ t.insts fs P.loop H fp hdr, (∃ f σ bufs kids, I.t = .node f σ bufs kids) →
      ∀ A ∈ loadAddrs I.t.val (I.t.events P), ∃ i, A = gpow i ∧ (t.Data P fs cert fp i ∨ R i)
  | .node f σ bufs kids, R, fp, hdr, h, I, hI, hn, A, hA => by
      rw [loadsIn_node] at h
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact h.1 A hA
      · obtain ⟨i, hi, h'⟩ := loadsKids_insts kids _ _ _ 0 h.2 I hI hn A hA
        refine ⟨i, hi, ?_⟩
        rcases h' with h' | h'
        · exact Or.inl (data_node.mpr (Or.inr h'))
        · exact h'
  | .phantom f σ, _, fp, hdr, _, I, hI, hn, _, _ => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      obtain ⟨_, _, _, _, h⟩ := hn
      cases h

/-- `loads_insts` for the callees. -/
theorem loadsKids_insts : ∀ (ks : List Tree) (R : ℕ → Prop) (ps : List ℕ) (J : Inst) (j : ℕ),
    Tree.LoadsInKids P fs cert R ps ks → ∀ I ∈ Tree.instsKids fs P.loop H J j ps ks,
      (∃ f σ bufs kids, I.t = .node f σ bufs kids) → ∀ A ∈ loadAddrs I.t.val (I.t.events P),
        ∃ i, A = gpow i ∧ (Tree.DataKids P fs cert ps ks i ∨ R i)
  | [], _, _, _, _, _, I, hI, _, _, _ => by
      rw [instsKids_nil] at hI; exact (List.not_mem_nil hI).elim
  | _ :: _, _, [], _, _, _, I, hI, _, _, _ => by
      rw [instsKids_nil_left] at hI; exact (List.not_mem_nil hI).elim
  | k :: ks, R, p :: ps, J, j, h, I, hI, hn, A, hA => by
      rw [loadsInKids_cons] at h
      rw [instsKids_cons, List.mem_append] at hI
      rcases hI with hI | hI
      · obtain ⟨i, hi, h'⟩ := loads_insts k R p _ h.1 I hI hn A hA
        exact ⟨i, hi, h'.imp_left fun h => dataKids_cons.mpr (Or.inl h)⟩
      · obtain ⟨i, hi, h'⟩ := loadsKids_insts ks R ps J (j + 1) h.2 I hI hn A hA
        exact ⟨i, hi, h'.imp_left fun h => dataKids_cons.mpr (Or.inr h)⟩
end

end Root

end
end LeanVM.Guest.Memory
