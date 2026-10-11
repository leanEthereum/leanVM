import Mathlib.Tactic

/-! The sorted level walk in `fiat_shamir/src/merkle.rs:186-206`.
No sorting or additional acceptance guard is performed by this walk. -/
namespace Whir.MerkleLevels

abbrev Level (D : Type*) := List (Nat × D)

def Sorted {D : Type*} (nodes : Level D) : Prop :=
  nodes.Pairwise (fun a b => a.1 < b.1)

def lookup {D : Type*} (index : Nat) : Level D → Option D
  | [] => none
  | (i, d) :: nodes => if index = i then some d else lookup index nodes

def right (index : Nat) : Bool := index % 2 == 1

def sibling (index : Nat) : Nat := if index % 2 = 0 then index + 1 else index - 1

def orient {D : Type*} (index : Nat) (current sibling : D) : D × D :=
  if index % 2 = 0 then (current, sibling) else (sibling, current)

def emit {D : Type*} (pair : D × D → D) (index : Nat) (left right : D)
    (result : Option (Level D × Level D × List D)) :
    Option (Level D × Level D × List D) :=
  result.map fun (parents, known, rest) =>
    ((index / 2, pair (left, right)) :: parents,
      (2 * (index / 2), left) :: (2 * (index / 2) + 1, right) :: known, rest)

def foldLevel {D : Type*} (pair : D × D → D) :
    Level D → List D → Option (Level D × Level D × List D)
  | [], supplied => some ([], [], supplied)
  | (i, d) :: nodes, supplied =>
    if i % 2 = 0 then
      match nodes with
      | (j, e) :: tail =>
        if j = i + 1 then emit pair i d e (foldLevel pair tail supplied)
        else match supplied with
          | [] => none
          | s :: ss => emit pair i d s (foldLevel pair ((j, e) :: tail) ss)
      | [] => match supplied with
        | [] => none
        | s :: ss => emit pair i d s (foldLevel pair [] ss)
    else match supplied with
      | [] => none
      | s :: ss => emit pair i s d (foldLevel pair nodes ss)
termination_by nodes => nodes.length

variable {D : Type*}

theorem lookup_mem {i : Nat} {d : D} {nodes : Level D}
    (h : lookup i nodes = some d) : (i, d) ∈ nodes := by
  induction nodes with
  | nil => simp [lookup] at h
  | cons x xs ih =>
    rcases x with ⟨j, e⟩
    by_cases hij : i = j
    · simp [lookup, hij] at h
      simp [hij, h]
    · simp [lookup, hij] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem lookup_of_mem {i : Nat} {d : D} {nodes : Level D}
    (sorted : Sorted nodes) (h : (i, d) ∈ nodes) : lookup i nodes = some d := by
  induction nodes with
  | nil => simp at h
  | cons x xs ih =>
    rcases x with ⟨j, e⟩
    rcases List.pairwise_cons.mp sorted with ⟨before, tail⟩
    rcases List.mem_cons.mp h with he | hm
    · cases he
      simp [lookup]
    · have hj : j < i := before _ hm
      simp [lookup, show i ≠ j by omega, ih tail hm]

theorem lookup_map {E : Type*} (f : D → E) (i : Nat) (nodes : Level D) :
    lookup i (nodes.map fun x => (x.1, f x.2)) = (lookup i nodes).map f := by
  induction nodes with
  | nil => rfl
  | cons x xs ih => rcases x with ⟨j, d⟩; simp [lookup, ih]; split <;> rfl

/-- An exact trace of successful loop iterations; even unpaired nodes retain
the Rust next-node guard rather than accepting an arbitrary hidden sibling. -/
inductive Folded (pair : D × D → D) :
    Level D → List D → Level D → Level D → List D → Prop
  | nil (supplied) : Folded pair [] supplied [] [] supplied
  | paired (i : Nat) (d e : D) (nodes supplied parents known rest)
      (even : i % 2 = 0)
      (tail : Folded pair nodes supplied parents known rest) :
      Folded pair ((i,d) :: (i+1,e) :: nodes) supplied
        ((i/2, pair (d,e)) :: parents) ((i,d) :: (i+1,e) :: known) rest
  | even (i : Nat) (d s : D) (nodes supplied parents known rest)
      (even : i % 2 = 0)
      (unpaired : nodes.head?.map Prod.fst ≠ some (i+1))
      (tail : Folded pair nodes supplied parents known rest) :
      Folded pair ((i,d) :: nodes) (s :: supplied)
        ((i/2, pair (d,s)) :: parents) ((i,d) :: (i+1,s) :: known) rest
  | odd (i : Nat) (d s : D) (nodes supplied parents known rest)
      (odd : i % 2 ≠ 0)
      (tail : Folded pair nodes supplied parents known rest) :
      Folded pair ((i,d) :: nodes) (s :: supplied)
        ((i/2, pair (s,d)) :: parents) ((i-1,s) :: (i,d) :: known) rest

theorem foldLevel_spec (pair : D × D → D) (nodes : Level D) (supplied : List D)
    {parents known : Level D} {rest : List D}
    (run : foldLevel pair nodes supplied = some (parents, known, rest)) :
    Folded pair nodes supplied parents known rest := by
  induction nodes using (measure List.length).wf.induction generalizing supplied parents known rest with
  | _ nodes ih =>
    cases nodes with
    | nil =>
      simp only [foldLevel, Option.some.injEq, Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl, rfl⟩
      exact .nil supplied
    | cons x nodes =>
      rcases x with ⟨i,d⟩
      by_cases he : i % 2 = 0
      · have hn : 2 * (i / 2) = i := by omega
        cases nodes with
        | nil =>
          cases supplied with
          | nil => simp [foldLevel, he] at run
          | cons s supplied =>
            rw [foldLevel] at run
            simp only [he, ↓reduceIte, emit, hn, Option.map_eq_some_iff] at run
            rcases run with ⟨⟨p,k,r⟩, hr, hout⟩
            cases hout
            exact .even i d s [] supplied p k r he (by simp)
              (ih [] (by change 0 < 1; omega) supplied hr)
        | cons y nodes =>
          rcases y with ⟨j,e⟩
          by_cases hj : j = i+1
          · subst j
            rw [foldLevel.eq_def] at run
            simp only [he, ↓reduceIte, emit, hn, Option.map_eq_some_iff] at run
            rcases run with ⟨⟨p,k,r⟩, hr, hout⟩
            cases hout
            exact .paired i d e nodes supplied p k r he
              (ih nodes (by change nodes.length < nodes.length + 2; omega) supplied hr)
          · cases supplied with
            | nil => simp [foldLevel, he, hj] at run
            | cons s supplied =>
              rw [foldLevel] at run
              simp only [he, hj, ↓reduceIte, emit, hn,
                Option.map_eq_some_iff] at run
              rcases run with ⟨⟨p,k,r⟩, hr, hout⟩
              cases hout
              exact .even i d s ((j,e)::nodes) supplied p k r he (by simpa using hj)
                (ih ((j,e)::nodes) (by change nodes.length + 1 < nodes.length + 2; omega) supplied hr)
      · have hn : 2 * (i / 2) = i-1 := by omega
        have hn' : i - 1 + 1 = i := by omega
        cases supplied with
        | nil => rw [foldLevel.eq_def] at run; simp [he] at run
        | cons s supplied =>
          rw [foldLevel.eq_def] at run
          simp only [he, ↓reduceIte, emit, hn', hn,
            Option.map_eq_some_iff] at run
          rcases run with ⟨⟨p,k,r⟩, hr, hout⟩
          cases hout
          exact .odd i d s nodes supplied p k r he
            (ih nodes (by change nodes.length < nodes.length + 1; omega) supplied hr)

namespace Folded

variable {pair : D × D → D} {nodes parents known : Level D} {supplied rest : List D}

theorem parent_source (h : Folded pair nodes supplied parents known rest) :
    ∀ p ∈ parents, ∃ x ∈ nodes, p.1 = x.1 / 2 := by
  induction h with
  | nil => simp
  | paired i d e nodes supplied parents known rest he h ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨(i,d), by simp, rfl⟩
    · obtain ⟨x,hx,eq⟩ := ih p hp
      exact ⟨x, by simp [hx], eq⟩
  | even i d s nodes supplied parents known rest he hu h ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨(i,d), by simp, rfl⟩
    · obtain ⟨x,hx,eq⟩ := ih p hp
      exact ⟨x, by simp [hx], eq⟩
  | odd i d s nodes supplied parents known rest ho h ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨(i,d), by simp, rfl⟩
    · obtain ⟨x,hx,eq⟩ := ih p hp
      exact ⟨x, by simp [hx], eq⟩

theorem known_source (h : Folded pair nodes supplied parents known rest) :
    ∀ k ∈ known, ∃ x ∈ nodes, k.1 / 2 = x.1 / 2 := by
  induction h with
  | nil => simp
  | paired i d e nodes supplied parents known rest he h ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact ⟨(i,d), by simp, rfl⟩
    rcases List.mem_cons.mp hk with rfl | hk
    · exact ⟨(i+1,e), by simp, rfl⟩
    obtain ⟨x,hx,eq⟩ := ih k hk
    exact ⟨x, by simp [hx], eq⟩
  | even i d s nodes supplied parents known rest he hu h ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact ⟨(i,d), by simp, rfl⟩
    rcases List.mem_cons.mp hk with rfl | hk
    · exact ⟨(i,d), by simp, by dsimp; omega⟩
    obtain ⟨x,hx,eq⟩ := ih k hk
    exact ⟨x, by simp [hx], eq⟩
  | odd i d s nodes supplied parents known rest ho h ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact ⟨(i,d), by simp, by dsimp; omega⟩
    rcases List.mem_cons.mp hk with rfl | hk
    · exact ⟨(i,d), by simp, rfl⟩
    obtain ⟨x,hx,eq⟩ := ih k hk
    exact ⟨x, by simp [hx], eq⟩

theorem range (h : Folded pair nodes supplied parents known rest) {bound : Nat}
    (bounded : ∀ x ∈ nodes, x.1 < bound) :
    ∀ p ∈ parents, p.1 < (bound + 1) / 2 := by
  intro p hp
  obtain ⟨x,hx,hp⟩ := h.parent_source p hp
  have := bounded x hx
  omega

theorem nonempty (h : Folded pair nodes supplied parents known rest)
    (hne : nodes ≠ []) : parents ≠ [] := by
  cases h <;> simp_all

/-- The suffix is literal, not merely a multiset: every unpaired iteration
consumes precisely the next supplied digest, and paired iterations consume none. -/
theorem accounting (h : Folded pair nodes supplied parents known rest) :
    ∃ consumed, supplied = consumed ++ rest ∧
      consumed.length + nodes.length = 2 * parents.length ∧
      known.length = 2 * parents.length := by
  induction h with
  | nil supplied => exact ⟨[], by simp⟩
  | paired i d e nodes supplied parents known rest he h ih =>
    obtain ⟨used,hs,hn,hk⟩ := ih
    refine ⟨used, hs, ?_, ?_⟩ <;> simp only [List.length_cons] <;> omega
  | even i d s nodes supplied parents known rest he hu h ih =>
    obtain ⟨used,hs,hn,hk⟩ := ih
    refine ⟨s::used, by simp [hs], ?_, ?_⟩ <;>
      simp only [List.length_cons] <;> omega
  | odd i d s nodes supplied parents known rest ho h ih =>
    obtain ⟨used,hs,hn,hk⟩ := ih
    refine ⟨s::used, by simp [hs], ?_, ?_⟩ <;>
      simp only [List.length_cons] <;> omega

private theorem extend_sorted (h : Folded pair nodes supplied parents known rest)
    (sp : Sorted parents) (sk : Sorted known) (i : Nat) (p left right : D)
    (separated : ∀ x ∈ nodes, i / 2 < x.1 / 2) :
    Sorted ((i/2,p)::parents) ∧
      Sorted ((2*(i/2),left)::(2*(i/2)+1,right)::known) := by
  constructor
  · apply List.pairwise_cons.mpr
    refine ⟨?_, sp⟩
    intro y hy
    obtain ⟨x,hx,eq⟩ := h.parent_source y hy
    have := separated x hx
    dsimp
    omega
  · apply List.pairwise_cons.mpr
    refine ⟨?_, List.pairwise_cons.mpr ⟨?_,sk⟩⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · dsimp; omega
      · obtain ⟨x,hx,eq⟩ := h.known_source y hy
        have := separated x hx
        dsimp
        omega
    · intro y hy
      obtain ⟨x,hx,eq⟩ := h.known_source y hy
      have := separated x hx
      dsimp
      omega

private theorem unpaired_separation (i : Nat) (d : D) (nodes : Level D)
    (sorted : Sorted ((i,d)::nodes))
    (unpaired : nodes.head?.map Prod.fst ≠ some (i+1)) :
    ∀ x ∈ nodes, i + 1 < x.1 := by
  cases nodes with
  | nil => simp
  | cons y ys =>
    rcases List.pairwise_cons.mp sorted with ⟨before, tail⟩
    have hi : i < y.1 := before y (by simp)
    have hn : y.1 ≠ i+1 := by simpa using unpaired
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := (List.pairwise_cons.mp tail).1 x hx
      omega

theorem sorted (h : Folded pair nodes supplied parents known rest)
    (input : Sorted nodes) : Sorted parents ∧ Sorted known := by
  induction h with
  | nil => simp [Sorted]
  | paired i d e nodes supplied parents known rest he h ih =>
    have ht := (List.pairwise_cons.mp (List.pairwise_cons.mp input).2)
    obtain ⟨sp,sk⟩ := ih ht.2
    have hs : ∀ x ∈ nodes, i/2 < x.1/2 := by
      intro x hx
      have := ht.1 x hx
      dsimp at this
      omega
    have hn : 2*(i/2) = i := by omega
    simpa [hn] using h.extend_sorted sp sk i (pair (d,e)) d e hs
  | even i d s nodes supplied parents known rest he hu h ih =>
    obtain ⟨sp,sk⟩ := ih (List.pairwise_cons.mp input).2
    have hs : ∀ x ∈ nodes, i/2 < x.1/2 := by
      intro x hx
      have := unpaired_separation i d nodes input hu x hx
      omega
    have hn : 2*(i/2) = i := by omega
    simpa [hn] using h.extend_sorted sp sk i (pair (d,s)) d s hs
  | odd i d s nodes supplied parents known rest ho h ih =>
    obtain ⟨sp,sk⟩ := ih (List.pairwise_cons.mp input).2
    have hs : ∀ x ∈ nodes, i/2 < x.1/2 := by
      intro x hx
      have := (List.pairwise_cons.mp input).1 x hx
      dsimp at this
      omega
    have hn : 2*(i/2) = i-1 := by omega
    have hn' : i-1+1 = i := by omega
    simpa [hn, hn'] using h.extend_sorted sp sk i (pair (s,d)) s d hs

theorem preserved (h : Folded pair nodes supplied parents known rest) :
    ∀ x ∈ nodes, x ∈ known := by
  induction h with
  | nil => simp
  | paired i d e nodes supplied parents known rest he h ih =>
    intro x hx
    simp only [List.mem_cons] at hx ⊢
    rcases hx with rfl | rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (ih x hx))
  | even i d s nodes supplied parents known rest he hu h ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih x hx))
  | odd i d s nodes supplied parents known rest ho h ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih x hx))

theorem edge (h : Folded pair nodes supplied parents known rest) :
    ∀ i d, (i,d) ∈ nodes → ∃ s,
      (sibling i,s) ∈ known ∧ (i/2,pair (orient i d s)) ∈ parents := by
  induction h with
  | nil => simp
  | paired j a b nodes supplied parents known rest he h ih =>
    intro i d hm
    rcases List.mem_cons.mp hm with hh | hm
    · cases hh
      exact ⟨b, by simp [sibling, he], by simp [orient, he]⟩
    rcases List.mem_cons.mp hm with hh | hm
    · cases hh
      have ho : (j+1)%2 ≠ 0 := by omega
      have hp : (j+1)/2 = j/2 := by omega
      exact ⟨a, by simp [sibling, ho], by simp [orient, ho, hp]⟩
    obtain ⟨s,hs,hp⟩ := ih i d hm
    exact ⟨s, by simp [hs], by simp [hp]⟩
  | even j a b nodes supplied parents known rest he hu h ih =>
    intro i d hm
    rcases List.mem_cons.mp hm with hh | hm
    · cases hh
      exact ⟨b, by simp [sibling, he], by simp [orient, he]⟩
    obtain ⟨s,hs,hp⟩ := ih i d hm
    exact ⟨s, by simp [hs], by simp [hp]⟩
  | odd j a b nodes supplied parents known rest ho h ih =>
    intro i d hm
    rcases List.mem_cons.mp hm with hh | hm
    · cases hh
      exact ⟨b, by simp [sibling, ho], by simp [orient, ho]⟩
    obtain ⟨s,hs,hp⟩ := ih i d hm
    exact ⟨s, by simp [hs], by simp [hp]⟩

end Folded

/-- Consumer-facing facts about the *actual* successful level walk. -/
structure Invariant (pair : D × D → D) (nodes : Level D) (supplied : List D)
    (parents known : Level D) (rest : List D) : Prop where
  parents_sorted : Sorted parents
  known_sorted : Sorted known
  preserved : ∀ {i d}, lookup i nodes = some d → lookup i known = some d
  edge : ∀ {i d}, lookup i nodes = some d → ∃ s,
    lookup (sibling i) known = some s ∧
      lookup (i/2) parents = some (pair (orient i d s))
  range : ∀ {bound}, (∀ x ∈ nodes, x.1 < bound) →
    ∀ p ∈ parents, p.1 < (bound + 1) / 2
  nonempty : nodes ≠ [] → parents ≠ []
  accounting : ∃ consumed, supplied = consumed ++ rest ∧
    consumed.length + nodes.length = 2 * parents.length ∧
    known.length = 2 * parents.length

theorem foldLevel_invariant (pair : D × D → D)
    {nodes : Level D} {supplied : List D} {parents known : Level D} {rest : List D}
    (sorted : Sorted nodes)
    (folded : foldLevel pair nodes supplied = some (parents,known,rest)) :
    Invariant pair nodes supplied parents known rest := by
  have h := foldLevel_spec pair nodes supplied folded
  obtain ⟨hp,hk⟩ := h.sorted sorted
  refine ⟨hp,hk,?_,?_,h.range,h.nonempty,h.accounting⟩
  · intro i d hi
    exact lookup_of_mem hk (h.preserved _ (lookup_mem hi))
  · intro i d hi
    obtain ⟨s,hs,he⟩ := h.edge i d (lookup_mem hi)
    exact ⟨s,lookup_of_mem hk hs,lookup_of_mem hp he⟩

theorem Sorted.keys_nodup {nodes : Level D} (h : Sorted nodes) :
    (nodes.map Prod.fst).Nodup := by
  apply List.pairwise_map.mpr
  exact h.imp (fun hlt => Nat.ne_of_lt hlt)

theorem Folded.remainder {pair : D × D → D} {nodes parents known : Level D}
    {supplied rest : List D} (h : Folded pair nodes supplied parents known rest) :
    rest = supplied.drop (2 * parents.length - nodes.length) := by
  obtain ⟨used,hs,hn,hk⟩ := h.accounting
  have hc : 2 * parents.length - nodes.length = used.length := by omega
  simp [hs, hc]

/-- Midpoint binary search on the half-open interval `[lo,hi)`. The result is
a position, as for Rust `binary_search_by_key(...).ok()`, not a digest. -/
def binarySearchAux (index : Nat) (nodes : Level D) (lo hi : Nat) : Option Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    match nodes[mid]? with
    | none => none
    | some node =>
      if node.1 < index then binarySearchAux index nodes (mid+1) hi
      else if index < node.1 then binarySearchAux index nodes lo mid
      else some mid
  else none
termination_by hi - lo
decreasing_by all_goals omega

def binarySearch (index : Nat) (nodes : Level D) : Option Nat :=
  binarySearchAux index nodes 0 nodes.length

def binaryLookup (index : Nat) (nodes : Level D) : Option D :=
  (binarySearch index nodes).bind fun pos => nodes[pos]?.map Prod.snd

theorem binarySearchAux_sound (index : Nat) (nodes : Level D) (lo hi pos : Nat)
    (found : binarySearchAux index nodes lo hi = some pos) :
    ∃ d, nodes[pos]? = some (index,d) := by
  rw [binarySearchAux.eq_def] at found
  split at found
  · rename_i interval
    dsimp only at found
    split at found
    · contradiction
    · rename_i node atMid
      split at found
      · exact binarySearchAux_sound index nodes ((lo+hi)/2+1) hi pos found
      · rename_i notLess
        split at found
        · exact binarySearchAux_sound index nodes lo ((lo+hi)/2) pos found
        · rename_i notGreater
          have hk : node.1 = index := by omega
          have hp : (lo+hi)/2 = pos := Option.some.inj found
          refine ⟨node.2, ?_⟩
          have hn : node = (index,node.2) := Prod.ext hk rfl
          rw [hp] at atMid
          exact atMid.trans (congrArg some hn)
  · contradiction
termination_by hi - lo
decreasing_by all_goals omega

theorem Sorted.get_key_lt {nodes : Level D} (sorted : Sorted nodes)
    {a b : Nat} {x y : Nat × D} (ha : nodes[a]? = some x)
    (hb : nodes[b]? = some y) (hab : a < b) : x.1 < y.1 := by
  obtain ⟨ha',hxa⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hb',hyb⟩ := List.getElem?_eq_some_iff.mp hb
  have h := List.pairwise_iff_getElem.mp sorted a b ha' hb' hab
  simpa [hxa,hyb] using h

theorem binarySearchAux_complete (index : Nat) (nodes : Level D) (lo hi pos : Nat)
    (sorted : Sorted nodes) (bounded : hi ≤ nodes.length)
    (inside : lo ≤ pos ∧ pos < hi) {d : D}
    (atPos : nodes[pos]? = some (index,d)) :
    binarySearchAux index nodes lo hi = some pos := by
  have interval : lo < hi := by omega
  have midBound : (lo+hi)/2 < nodes.length := by omega
  have atMid : nodes[(lo+hi)/2]? = some nodes[(lo+hi)/2] := List.getElem?_eq_getElem midBound
  rw [binarySearchAux.eq_def]
  simp only [interval, ↓reduceIte, atMid]
  split
  · rename_i less
    have hp : (lo+hi)/2 < pos := by
      by_contra bad
      have hp : pos ≤ (lo+hi)/2 := by omega
      rcases Nat.lt_or_eq_of_le hp with hp | hp
      · have := sorted.get_key_lt atPos atMid hp
        omega
      · have eq : (index,d) = nodes[(lo+hi)/2] := by
          rw [hp, atMid] at atPos
          exact (Option.some.inj atPos).symm
        have := congrArg Prod.fst eq
        omega
    exact binarySearchAux_complete index nodes ((lo+hi)/2+1) hi pos
      sorted bounded ⟨by omega,inside.2⟩ atPos
  · rename_i notLess
    split
    · rename_i greater
      have hp : pos < (lo+hi)/2 := by
        by_contra bad
        have hp : (lo+hi)/2 ≤ pos := by omega
        rcases Nat.lt_or_eq_of_le hp with hp | hp
        · have := sorted.get_key_lt atMid atPos hp
          omega
        · have eq : nodes[(lo+hi)/2] = (index,d) := by
            rw [← hp, atMid] at atPos
            exact Option.some.inj atPos
          have := congrArg Prod.fst eq
          omega
      exact binarySearchAux_complete index nodes lo ((lo+hi)/2) pos
        sorted (by omega) ⟨inside.1,hp⟩ atPos
    · rename_i notGreater
      have hp : (lo+hi)/2 = pos := by
        rcases Nat.lt_trichotomy ((lo+hi)/2) pos with hp | hp | hp
        · have := sorted.get_key_lt atMid atPos hp
          omega
        · exact hp
        · have := sorted.get_key_lt atPos atMid hp
          omega
      exact congrArg some hp
termination_by hi - lo
decreasing_by all_goals omega

theorem binarySearch_some_iff {index pos : Nat} {nodes : Level D}
    (sorted : Sorted nodes) :
    binarySearch index nodes = some pos ↔ ∃ d, nodes[pos]? = some (index,d) := by
  constructor
  · exact binarySearchAux_sound index nodes 0 nodes.length pos
  · rintro ⟨d,hd⟩
    have hp := (List.getElem?_eq_some_iff.mp hd).1
    exact binarySearchAux_complete index nodes 0 nodes.length pos sorted (by omega)
      ⟨by omega,hp⟩ hd

/-- Exact observable result of binary-searching a sorted unique known level
and reading the digest at the returned position. -/
theorem binaryLookup_eq_lookup (index : Nat) (nodes : Level D) (sorted : Sorted nodes) :
    binaryLookup index nodes = lookup index nodes := by
  unfold binaryLookup
  cases hs : binarySearch index nodes with
  | none =>
    simp only [Option.bind_none]
    cases hl : lookup index nodes with
    | none => rfl
    | some d =>
      obtain ⟨pos,hp⟩ := List.mem_iff_getElem?.mp (lookup_mem hl)
      have := (binarySearch_some_iff sorted).mpr ⟨d,hp⟩
      rw [hs] at this
      contradiction
  | some pos =>
    obtain ⟨d,hd⟩ := (binarySearch_some_iff sorted).mp hs
    simp only [Option.bind_some, hd, Option.map_some]
    exact (lookup_of_mem sorted (List.mem_iff_getElem?.mpr ⟨pos,hd⟩)).symm

theorem Folded.run {pair : D × D → D} {nodes parents known : Level D}
    {supplied rest : List D} (h : Folded pair nodes supplied parents known rest) :
    foldLevel pair nodes supplied = some (parents,known,rest) := by
  induction h with
  | nil => rw [foldLevel.eq_def]
  | paired i d e nodes supplied parents known rest he h ih =>
    have hn : 2*(i/2) = i := by omega
    rw [foldLevel.eq_def]
    simp [he, ih, emit, hn]
  | even i d s nodes supplied parents known rest he hu h ih =>
    have hn : 2*(i/2) = i := by omega
    rw [foldLevel.eq_def]
    cases nodes with
    | nil => simpa [he, emit, hn] using congrArg (emit pair i d s) ih
    | cons x xs =>
      rcases x with ⟨j,e⟩
      have hj : j ≠ i+1 := by simpa using hu
      simp [he, hj, ih, emit, hn]
  | odd i d s nodes supplied parents known rest ho h ih =>
    have hn : 2*(i/2) = i-1 := by omega
    have hn' : i-1+1 = i := by omega
    rw [foldLevel.eq_def]
    simp [ho, ih, emit, hn, hn']

/-- Number of stored digests demanded by precisely the same paired-node guard.
It depends only on indices, never on the hash function or digest values. -/
def requiredSiblings : Level D → Nat
  | [] => 0
  | (i,_) :: nodes =>
    if i % 2 = 0 then
      match nodes with
      | [] => 1
      | (j,e) :: tail =>
        if j = i+1 then requiredSiblings tail
        else 1 + requiredSiblings ((j,e)::tail)
    else 1 + requiredSiblings nodes

theorem requiredSiblings_odd (i : Nat) (d : D) (nodes : Level D) (odd : i % 2 ≠ 0) :
    requiredSiblings ((i,d)::nodes) = 1 + requiredSiblings nodes := by
  rw [requiredSiblings.eq_def]
  simp [odd]

theorem foldLevel_none_iff (pair : D × D → D) (nodes : Level D) (supplied : List D) :
    foldLevel pair nodes supplied = none ↔ supplied.length < requiredSiblings nodes := by
  fun_induction foldLevel pair nodes supplied <;>
    simp_all [requiredSiblings_odd, requiredSiblings, emit, Option.map_eq_none_iff] <;> omega

end Whir.MerkleLevels
