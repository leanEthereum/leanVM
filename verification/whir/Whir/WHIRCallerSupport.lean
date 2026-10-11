import Whir.WHIRCallerGeometry
import Whir.InitialBatching
import Whir.SuccinctRingWeight

/-! Production witness placement and the support of caller weights. The public
construction follows `witness::stack_offsets` / `placements_of`: committed
columns are sorted largest-first with index tie breaking; ports refer to their
packed committed column rather than occupying a second window. Public layouts
are constructed and checked once, before any transcript is decoded. The final
theorems derive each decoded claim's shape and the batched shape from that
construction; no terminal-support premise or extra native rejection is used. -/
namespace Whir.WHIRCallerSupport
open Concrete ArrayLayout WHIRCallerClaims RingPCSGame
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

inductive Source where
  | committed (dimension : Nat)
  | port (column slot strideLog : Nat)
  | sliced
  deriving DecidableEq, Repr

structure Window where
  column : Nat
  offset : Nat
  dimension : Nat
  deriving DecidableEq, Repr

/-- The source comparator: decreasing dimension, then increasing source index. -/
def before (a b : Nat × Nat) : Bool :=
  a.2 > b.2 || (a.2 == b.2 && a.1 ≤ b.1)

def committedItems (sources : Array Source) : List (Nat × Nat) :=
  sources.toList.zipIdx.filterMap fun (s,i) => match s with
    | .committed d => some (i,d)
    | _ => none

def sortedItems (sources : Array Source) : List (Nat × Nat) :=
  (committedItems sources).mergeSort before

/-- Executable offset loop; only committed columns advance the cursor. -/
def stackWindows (offset : Nat) : List (Nat × Nat) → List Window
  | [] => []
  | (column,dimension) :: rest =>
    ⟨column,offset,dimension⟩ :: stackWindows (offset + 2^dimension) rest

def windows (sources : Array Source) : List Window := stackWindows 0 (sortedItems sources)

def placedWords (sources : Array Source) : Nat :=
  ((sortedItems sources).map fun p => 2^p.2).sum

def lookupWindow (sources : Array Source) (column : Nat) : Option Window :=
  (windows sources).find? (fun w => w.column == column)

/-- Literal source placement projection; only a committed reference can back a port. -/
def placement (sources : Array Source) (column : Nat) : Option Placement := do
  match ← sources[column]? with
  | .committed dimension =>
    let w ← lookupWindow sources column
    pure (.committed w.offset dimension)
  | .port packed slot stride =>
    let w ← lookupWindow sources packed
    pure (.port w.offset slot stride)
  | .sliced => pure .sliced

def placementsOf (sources : Array Source) : Option (Array Placement) :=
  if sources.all (fun s => match s with | .committed d => d < 64 | _ => true) then
    (List.range sources.size).toArray.mapM (placement sources)
  else none

/-- The production constructor owns placements; raw caller metadata cannot
choose arbitrary offsets for ordinary or strided column claims. -/
def installPlacements (ps : Array Placement) : CallerLayout → CallerLayout
  | .cpu l => .cpu { l with placements := ps }
  | .recursion l => .recursion { l with placements := ps }

@[simp] theorem callerPlacements_install (ps : Array Placement) (layout : CallerLayout) :
    callerPlacements (installPlacements ps layout) = ps := by
  cases layout <;> rfl

/-- Rows addressed by a port are derived from its actual packed dimension. A
stride larger than that dimension is malformed production metadata, not a
condition on a terminal weight. -/
def columnDimension (sources : Array Source) (column : Nat) : Option Nat := do
  match ← sources[column]? with
  | .committed d => pure d
  | .port packed _ stride =>
    let w ← lookupWindow sources packed
    if stride ≤ w.dimension then pure (w.dimension - stride) else none
  | .sliced => pure 0

theorem stackWindows_bounds (offset : Nat) (items : List (Nat × Nat))
    (w : Window) (hw : w ∈ stackWindows offset items) :
    offset ≤ w.offset ∧ w.offset + 2^w.dimension ≤
      offset + (items.map fun p => 2^p.2).sum := by
  induction items generalizing offset with
  | nil => simp [stackWindows] at hw
  | cons p ps ih =>
    rcases p with ⟨col,dim⟩
    simp only [stackWindows, List.mem_cons] at hw
    rcases hw with rfl | hw
    · simp only [List.map_cons, List.sum_cons]
      constructor <;> omega
    · obtain ⟨lo,hi⟩ := ih (offset + 2^dim) hw
      simp only [List.map_cons, List.sum_cons]
      constructor
      · exact (Nat.le_add_right offset (2^dim)).trans lo
      · simpa only [Nat.add_assoc] using hi

theorem before_trans (a b c : Nat × Nat) (hab : before a b) (hbc : before b c) :
    before a c := by
  simp only [before,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at *
  omega

theorem before_total (a b : Nat × Nat) : before a b || before b a := by
  simp only [before,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  omega

theorem sorted_dimensions (sources : Array Source) :
    (sortedItems sources).Pairwise (fun a b => b.2 ≤ a.2) := by
  have h := List.pairwise_mergeSort before_trans before_total (committedItems sources)
  apply h.imp
  intro a b hab
  simp only [before,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hab
  omega

theorem stackWindows_aligned (items : List (Nat × Nat))
    (sorted : items.Pairwise (fun a b => b.2 ≤ a.2)) (offset : Nat)
    (aligned : ∀ p ∈ items, 2^p.2 ∣ offset) (w : Window)
    (mem : w ∈ stackWindows offset items) : 2^w.dimension ∣ w.offset := by
  induction items generalizing offset with
  | nil => simp [stackWindows] at mem
  | cons p ps ih =>
    rcases p with ⟨col,dim⟩
    rw [List.pairwise_cons] at sorted
    simp only [stackWindows,List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact aligned _ List.mem_cons_self
    · apply ih sorted.2 (offset + 2^dim) ?_ mem
      intro p hp
      exact dvd_add (aligned p (List.mem_cons_of_mem _ hp))
        (Nat.pow_dvd_pow 2 (sorted.1 p hp))

theorem windows_aligned (sources : Array Source) (w : Window) (mem : w ∈ windows sources) :
    2^w.dimension ∣ w.offset :=
  stackWindows_aligned (sortedItems sources) (sorted_dimensions sources) 0
    (fun _ _ => dvd_zero _) w mem

theorem lookupWindow_bounds (sources : Array Source) (column : Nat) (w : Window)
    (found : lookupWindow sources column = some w) :
    w.offset + 2^w.dimension ≤ placedWords sources := by
  have hw : w ∈ windows sources := List.mem_of_find?_eq_some found
  simpa [windows, placedWords] using
    (stackWindows_bounds 0 (sortedItems sources) w hw).2

theorem stackWindows_member (offset : Nat) (items : List (Nat × Nat))
    (w : Window) (hw : w ∈ stackWindows offset items) :
    (w.column,w.dimension) ∈ items := by
  induction items generalizing offset with
  | nil => simp [stackWindows] at hw
  | cons p ps ih =>
    rcases p with ⟨col,dim⟩
    simp only [stackWindows, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih _ hw)

theorem lookupWindow_source (sources : Array Source) (column : Nat) (w : Window)
    (found : lookupWindow sources column = some w) :
    w.column = column ∧ sources[column]? = some (.committed w.dimension) := by
  have hcol : w.column = column := by
    simpa using List.find?_some found
  have hm := stackWindows_member 0 (sortedItems sources) w
    (List.mem_of_find?_eq_some found)
  have hm' : (w.column,w.dimension) ∈ committedItems sources :=
    (List.mergeSort_perm (committedItems sources) before).mem_iff.mp hm
  simp only [committedItems, List.mem_filterMap] at hm'
  obtain ⟨⟨s,i⟩, hi, hs⟩ := hm'
  cases s with
  | committed d =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl,rfl⟩ := hs
    exact ⟨hcol, by simpa [hcol] using (List.mk_mem_zipIdx_iff_getElem?.mp hi)⟩
  | port _ _ _ => simp at hs
  | sliced => simp at hs

/-- The exact source placement has no support beyond its committed packed window. -/
def PlacementExtent (p : Placement) (rows : Nat) (bound : Nat) : Prop :=
  match p with
  | .committed offset dimension => rows ≤ dimension ∧ offset + 2^dimension ≤ bound
  | .port offset _ stride => offset + 2^(stride+rows) ≤ bound
  | .sliced => True

/-- The production constructor derives the interval bound, including a port's
stride, from its referenced committed column. -/
theorem placement_extent (sources : Array Source) (column rows : Nat) (p : Placement)
    (placed : placement sources column = some p)
    (dimension : columnDimension sources column = some rows) :
    PlacementExtent p rows (placedWords sources) := by
  unfold placement at placed
  unfold columnDimension at dimension
  cases hs : sources[column]? with
  | none => simp [hs] at placed
  | some s =>
    cases s with
    | committed d =>
      cases hw : lookupWindow sources column with
      | none => simp [hs,hw] at placed
      | some w =>
        have hh := (lookupWindow_source sources column w hw).2
        rw [hs] at hh
        have hd : d = w.dimension := by simpa using hh
        simp [hs,hw] at placed dimension
        subst p
        subst rows
        exact ⟨le_rfl, hd ▸ lookupWindow_bounds sources column w hw⟩
    | port packed slot stride =>
      cases hw : lookupWindow sources packed with
      | none => simp [hs,hw] at placed
      | some w =>
        simp [hs,hw] at placed dimension
        obtain ⟨h,hr⟩ := dimension
        subst p
        subst rows
        simpa only [PlacementExtent, Nat.add_sub_of_le h] using
          lookupWindow_bounds sources packed w hw
    | sliced =>
      simp [hs] at placed
      subst p
      trivial

theorem mapM_some_rel {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (ok : xs.mapM f = some ys) : List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => simpa using ok
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons,hx] at ok
    | some y =>
      cases hy : xs.mapM f with
      | none => simp [List.mapM_cons,hx,hy] at ok
      | some zs =>
        simp [List.mapM_cons,hx,hy] at ok
        subst ys
        exact .cons hx (ih zs hy)

theorem placementsOf_rel (sources : Array Source) (ps : Array Placement)
    (ok : placementsOf sources = some ps) :
    List.Forall₂ (fun i p => placement sources i = some p) (List.range sources.size) ps.toList := by
  unfold placementsOf at ok
  split at ok <;> try { simp at ok }
  rw [Array.mapM_eq_mapM_toList] at ok
  cases h : (List.range sources.size).mapM (placement sources) with
  | none => simp [h] at ok
  | some ys =>
    simp only [h,Functor.map,Option.map,Option.some.injEq] at ok
    subst ps
    simpa using mapM_some_rel (placement sources) _ ys h

theorem placementsOf_get (sources : Array Source) (ps : Array Placement)
    (ok : placementsOf sources = some ps) (column : Nat) (p : Placement)
    (atColumn : ps[column]? = some p) : placement sources column = some p := by
  have rel := placementsOf_rel sources ps ok
  have hlen := rel.length_eq
  have hp := (Array.getElem?_eq_some_iff.mp atColumn)
  have hi : column < sources.size := by simpa using hp.1.trans_eq hlen.symm
  have h := rel.get (i := column) (by simpa using hi) (by simpa using hp.1)
  simpa [getElem!_pos, List.getElem_range, hp.2] using h

def sourceWords : Source → Nat
  | .committed d => 2^d
  | _ => 0

def placementWords : Placement → Nat
  | .committed _ d => 2^d
  | _ => 0

theorem placedWords_eq (sources : Array Source) :
    placedWords sources = (sources.toList.map sourceWords).sum := by
  unfold placedWords sortedItems
  rw [((List.mergeSort_perm (committedItems sources) before).map
    (fun p => 2^p.2)).sum_eq]
  suffices ∀ (xs : List Source) (start : Nat),
      (((xs.zipIdx start).filterMap (fun (s,i) => match s with
        | .committed d => some (i,d)
        | _ => none)).map (fun p => 2^p.2)).sum = (xs.map sourceWords).sum by
    exact this sources.toList 0
  intro xs
  induction xs with
  | nil => simp
  | cons s xs ih =>
    intro start
    cases s <;> simp [ih,sourceWords]

theorem placement_words (sources : Array Source) (i : Nat) (p : Placement)
    (ok : placement sources i = some p) :
    some (placementWords p) = (sources[i]?).map sourceWords := by
  unfold placement at ok
  cases hs : sources[i]? with
  | none => simp [hs] at ok
  | some s =>
    cases s with
    | committed d =>
      cases hw : lookupWindow sources i with
      | none => simp [hs,hw] at ok
      | some w =>
        simp [hs,hw] at ok
        subst p
        simp [placementWords,sourceWords]
    | port col slot stride =>
      cases hw : lookupWindow sources col with
      | none => simp [hs,hw] at ok
      | some w =>
        simp [hs,hw] at ok
        subst p
        simp [placementWords,sourceWords]
    | sliced =>
      simp [hs] at ok
      subst p
      simp [placementWords,sourceWords]

theorem placementsOf_words (sources : Array Source) (ps : Array Placement)
    (ok : placementsOf sources = some ps) :
    (ps.toList.map placementWords).sum = placedWords sources := by
  rw [placedWords_eq]
  have hlen := (placementsOf_rel sources ps ok).length_eq
  have he : ps.toList.map placementWords = sources.toList.map sourceWords := by
    apply List.ext_getElem
    · simpa using hlen.symm
    · intro i hi hj
      have hip : i < ps.size := by simpa using hi
      have his : i < sources.size := by simpa using hj
      have h := placement_words sources i ps[i]
        (placementsOf_get sources ps ok i ps[i] (by simp [hip]))
      simpa [his] using h
  rw [he]

theorem callerWords_placementsOf (sources : Array Source) (layout : CallerLayout)
    (ok : placementsOf sources = some (callerPlacements layout)) :
    callerWords layout = placedWords sources := by
  rw [callerWords, ← Array.foldl_toList]
  have he :
      (callerPlacements layout).toList.foldl (fun n p => match p with
        | .committed _ d => n + 2^d
        | _ => n) 0 =
      (callerPlacements layout).toList.foldl (fun n p => n + placementWords p) 0 := by
    congr 1
    funext n p
    cases p <;> simp [placementWords]
  trans (callerPlacements layout).toList.foldl (fun n p => n + placementWords p) 0
  · convert he using 1
  rw [← List.foldl_map, ← List.sum_eq_foldl]
  exact placementsOf_words sources (callerPlacements layout) ok

/-- Production rounds occupied columns to a whole lane, with at least one lane. -/
theorem callerWords_le_occupied (layout : CallerLayout) :
    callerWords layout ≤ callerLanes layout * 2^(callerMu layout - 6) := by
  let block := 2^(callerMu layout-6)
  have hb : 0 < block := by positivity
  have h : callerWords layout ≤ ((callerWords layout + block - 1) / block) * block := by
    have hr := Nat.mod_lt (callerWords layout + block - 1) hb
    have he := Nat.mod_add_div (callerWords layout + block - 1) block
    rw [Nat.mul_comm block] at he
    omega
  exact h.trans (Nat.mul_le_mul_right block (Nat.le_max_right 1 _))

/-- Production ports are positions within one packed circuit instance. This
public source-schema condition is separate from any verifier acceptance guard. -/
def portSlotFits (sources : Array Source) (column : Nat) : Bool :=
  match sources[column]? with
  | some (.port _ slot stride) => slot < 2^stride
  | _ => true

/-- A column incidence check against production source dimensions. Sliced
columns emit no point claim and therefore impose no point-dimension condition. -/
def columnFits (sources : Array Source) (column rows : Nat) : Bool :=
  portSlotFits sources column &&
  match sources[column]? with
  | some .sliced => true
  | _ => match columnDimension sources column with
    | some dimension => rows ≤ dimension
    | none => false

/-- Family metadata must name a window actually emitted by the placement
constructor, not merely an arbitrary interval below a numeric bound. -/
def ringFits (sources : Array Source) (offset rows : Nat) : Bool :=
  (windows sources).any (fun w => w.offset == offset && rows ≤ w.dimension)

theorem columnFits_mono (sources : Array Source) (column small large : Nat)
    (h : small ≤ large) (fits : columnFits sources column large = true) :
    columnFits sources column small = true := by
  unfold columnFits at *
  simp only [Bool.and_eq_true] at fits ⊢
  obtain ⟨slot,fits⟩ := fits
  refine ⟨slot,?_⟩
  split at fits <;> simp_all
  split at fits <;> simp_all
  omega

theorem ringFits_mono (sources : Array Source) (offset small large : Nat)
    (h : small ≤ large) (fits : ringFits sources offset large = true) :
    ringFits sources offset small = true := by
  simp only [ringFits, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at *
  obtain ⟨w,hw,ho,hd⟩ := fits
  exact ⟨w,hw,ho,h.trans hd⟩

theorem ringFits_bound (sources : Array Source) (offset rows : Nat)
    (fits : ringFits sources offset rows = true) :
    offset + 2^rows ≤ placedWords sources := by
  simp only [ringFits,List.any_eq_true,Bool.and_eq_true,beq_iff_eq,
    decide_eq_true_eq] at fits
  obtain ⟨w,hw,rfl,hd⟩ := fits
  have hb := (stackWindows_bounds 0 (sortedItems sources) w hw).2
  have hp : 2^rows ≤ 2^w.dimension := Nat.pow_le_pow_right (by decide) hd
  simp only [Nat.zero_add] at hb
  change w.offset + 2^w.dimension ≤ placedWords sources at hb
  omega

theorem window_nativeShape (sources : Array Source) (w : Window)
    (mem : w ∈ windows sources) (n rows : Nat) (dimension : rows ≤ w.dimension)
    (bound : placedWords sources ≤ 2^n) :
    rows ≤ n ∧ w.offset % 2^rows = 0 ∧ w.offset + 2^rows ≤ 2^n := by
  have hi := (stackWindows_bounds 0 (sortedItems sources) w mem).2
  have hp : 2^rows ≤ 2^w.dimension := Nat.pow_le_pow_right (by decide) dimension
  have hb : w.offset + 2^rows ≤ 2^n := by
    change w.offset + 2^w.dimension ≤ 0 + placedWords sources at hi
    omega
  refine ⟨(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by omega), ?_, hb⟩
  exact Nat.mod_eq_zero_of_dvd ((Nat.pow_dvd_pow 2 dimension).trans (windows_aligned sources w mem))

theorem ringFits_nativeShape (sources : Array Source) (offset rows n : Nat)
    (fits : ringFits sources offset rows = true) (bound : placedWords sources ≤ 2^n) :
    rows ≤ n ∧ offset % 2^rows = 0 ∧ offset + 2^rows ≤ 2^n := by
  simp only [ringFits,List.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at fits
  obtain ⟨w,hw,rfl,hd⟩ := fits
  exact window_nativeShape sources w hw n rows hd bound

theorem production_point_nativeShape (sources : Array Source) (ps : Array Placement)
    (built : placementsOf sources = some ps) (c : ColumnClaim) (p : Placement)
    (atColumn : ps[c.column]? = some p)
    (fits : columnFits sources c.column c.point.length = true)
    (claim : PointClaim) (placed : placeClaim p c = some claim)
    (n : Nat) (bound : placedWords sources ≤ 2^n) :
    SuccinctPointWeight.Shape n claim := by
  have hp := placementsOf_get sources ps built c.column p atColumn
  unfold placement at hp
  cases hs : sources[c.column]? with
  | none => simp [hs] at hp
  | some source =>
    cases source with
    | committed d =>
      cases hw : lookupWindow sources c.column with
      | none => simp [hs,hw] at hp
      | some w =>
        have hh := (lookupWindow_source sources c.column w hw).2
        rw [hs] at hh
        have hd : d = w.dimension := by simpa using hh
        have hl : c.point.length ≤ w.dimension := by
          simpa [columnFits,portSlotFits,columnDimension,hs,hd] using fits
        simp [hs,hw] at hp
        subst p
        simp only [placeClaim,Option.some.injEq] at placed
        subst claim
        simpa only [SuccinctPointWeight.Shape,List.size_toArray] using
          (window_nativeShape sources w (List.mem_of_find?_eq_some hw) n c.point.length hl bound).2
    | port packed slot stride =>
      cases hw : lookupWindow sources packed with
      | none => simp [hs,hw] at hp
      | some w =>
        by_cases hd : stride ≤ w.dimension
        · have hf : slot < 2^stride ∧ c.point.length ≤ w.dimension - stride := by
            simpa [columnFits,portSlotFits,columnDimension,hs,hw,hd] using fits
          have hl : stride + c.point.length ≤ w.dimension := by omega
          have hshape := window_nativeShape sources w (List.mem_of_find?_eq_some hw)
            n (stride + c.point.length) hl bound
          simp [hs,hw] at hp
          subst p
          simp only [placeClaim,Option.some.injEq] at placed
          subst claim
          exact ⟨hshape.2.1,hshape.2.2,hf.1⟩
        · simp [columnFits,portSlotFits,columnDimension,hs,hw,hd] at fits
    | sliced =>
      simp [hs] at hp
      subst p
      simp [placeClaim] at placed

/-- Geometric support of plain and strided source claims, including short points. -/
theorem placeClaim_support (p : Placement) (c : ColumnClaim) (rows bound : Nat)
    (extent : PlacementExtent p rows bound) (length : c.point.length ≤ rows)
    (claim : PointClaim) (placed : placeClaim p c = some claim)
    (v : Nat) (hv : bound ≤ v) : pointWeight claim v = 0 := by
  cases p with
  | committed offset dimension =>
    simp only [placeClaim, Option.some.injEq] at placed
    subst claim
    change rows ≤ dimension ∧ offset + 2^dimension ≤ bound at extent
    have hpow : 2^c.point.length ≤ 2^dimension :=
      Nat.pow_le_pow_right (by decide) (length.trans extent.1)
    simp only [pointWeight, regionWeight, List.size_toArray]
    split_ifs with h
    · omega
    · rfl
  | port offset slot stride =>
    simp only [placeClaim, Option.some.injEq] at placed
    subst claim
    have hpow : 2^(stride+c.point.length) ≤ 2^(stride+rows) :=
      Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left length stride)
    simp only [pointWeight, List.size_toArray]
    split_ifs with h
    · change offset + 2^(stride+rows) ≤ bound at extent
      omega
    · rfl
  | sliced => simp [placeClaim] at placed
/-- Concrete source placement provenance suffices; there is no supplied
point-weight correctness or support premise. -/
theorem production_point_support (sources : Array Source) (ps : Array Placement)
    (built : placementsOf sources = some ps) (c : ColumnClaim) (p : Placement)
    (atColumn : ps[c.column]? = some p)
    (fits : columnFits sources c.column c.point.length = true)
    (claim : PointClaim) (placed : placeClaim p c = some claim)
    (v : Nat) (hv : placedWords sources ≤ v) : pointWeight claim v = 0 := by
  have hp := placementsOf_get sources ps built c.column p atColumn
  by_cases hs : sources[c.column]? = some .sliced
  · simp [placement,hs] at hp
    subst p
    simp [placeClaim] at placed
  · have hf : ∃ rows, columnDimension sources c.column = some rows ∧ c.point.length ≤ rows := by
      have hrows : (match columnDimension sources c.column with
          | some rows => decide (c.point.length ≤ rows)
          | none => false) = true := by
        unfold columnFits at fits
        simp only [Bool.and_eq_true] at fits
        have rowFits := fits.2
        cases hsource : sources[c.column]? with
        | none => simpa only [hsource] using rowFits
        | some source =>
          cases source with
          | committed _ => simpa only [hsource] using rowFits
          | port _ _ _ => simpa only [hsource] using rowFits
          | sliced => exact False.elim (hs hsource)
      cases hd : columnDimension sources c.column with
      | none => simp [hd] at hrows
      | some rows => exact ⟨rows,rfl,by simpa [hd] using hrows⟩
    obtain ⟨rows,hd,hl⟩ := hf
    exact placeClaim_support p c rows (placedWords sources)
      (placement_extent sources c.column rows p hp hd) hl claim placed v hv


/-- Ring switching preserves literal support: its Frobenius map sends zero to
zero, regardless of slices, gamma, or the six ring-switch challenges. -/
theorem family_support {m : Nat} (family : Fin m → FamilyClaim)
    (r : RingPCSGame.Prefix) (bound : Nat)
    (fits : ∀ j, (family j).offset + 2^(family j).point.size ≤ bound)
    (v : Nat) (hv : bound ≤ v) : transparentWeight family r v = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hf : ¬ ((family j).offset ≤ v ∧
      v < (family j).offset + 2^(family j).point.size) := by
    have := fits j
    omega
  simp [regionWeight, hf]

theorem transformed_claim_size {m : Nat} (width : Nat)
    (family : Fin m → FamilyClaim) (points : Array PointClaim) (r : RingPCSGame.Prefix)
    (claim : CausalGame.Claim) (mem : claim ∈ (transformedClaims width family points r).toList) :
    claim.weight.size = width := by
  simp only [transformedClaims,Array.toList_append,Array.toList_map] at mem
  change claim ∈ [familyPublic width family r] ++ points.toList.map (publicPoint width) at mem
  simp only [List.mem_append,List.mem_singleton,List.mem_map] at mem
  rcases mem with rfl | ⟨p,hp,rfl⟩ <;> simp [familyPublic,publicPoint]

theorem transformed_claim_support {m : Nat} (width bound : Nat)
    (family : Fin m → FamilyClaim) (points : Array PointClaim) (r : RingPCSGame.Prefix)
    (families : ∀ j, (family j).offset + 2^(family j).point.size ≤ bound)
    (pointSupport : ∀ p ∈ points.toList, ∀ v, bound ≤ v → pointWeight p v = 0)
    (claim : CausalGame.Claim) (mem : claim ∈ (transformedClaims width family points r).toList)
    (v : Nat) (hv : bound ≤ v) (hwidth : v < width) : claim.weight[v]! = 0 := by
  simp only [transformedClaims,Array.toList_append,Array.toList_map] at mem
  change claim ∈ [familyPublic width family r] ++ points.toList.map (publicPoint width) at mem
  simp only [List.mem_append,List.mem_singleton,List.mem_map] at mem
  rcases mem with rfl | ⟨p,hp,rfl⟩
  · simpa [familyPublic,getElem!_tab _ _ _ hwidth] using family_support family r bound families v hv
  · simpa [publicPoint,getElem!_tab _ _ _ hwidth] using pointSupport p hp v hv

/-- The actual transformed array and actual lambda batching retain the proven
occupied-word support; no terminal evaluator identity is assumed. -/
theorem transformed_batch_support {m : Nat} (width bound : Nat)
    (family : Fin m → FamilyClaim) (points : Array PointClaim)
    (r : RingPCSGame.Prefix) (lambda : E)
    (families : ∀ j, (family j).offset + 2^(family j).point.size ≤ bound)
    (pointSupport : ∀ p ∈ points.toList, ∀ v, bound ≤ v → pointWeight p v = 0) :
    ∀ v, bound ≤ v → v < width →
      (CausalGame.batchClaims width (transformedClaims width family points r) lambda).weight[v]! = 0 := by
  apply InitialBatching.batchClaims_zero_tail
  intro j v hv hwidth
  exact transformed_claim_support width bound family points r families pointSupport
    _ (by simp) v hv hwidth

/-- These are finite facts about the production configuration constructor. -/
theorem config_initial_geometry : ∀ p : ParameterBounds.Profile,
    (ParameterBounds.config p).logN = p.1.val + 15 ∧
      (ParameterBounds.config p).folds[0]! = 6 := by
  decide +kernel

theorem openingMatches_occupied (layout : CallerLayout) (p : ParameterBounds.Profile)
    (lanes : Nat) (metadata : openingMatches p lanes layout = true) :
    callerWords layout ≤ lanes *
      2^((ParameterBounds.config p).logN - (ParameterBounds.config p).folds[0]!) := by
  simp only [openingMatches, Bool.and_eq_true, beq_iff_eq] at metadata
  rw [(config_initial_geometry p).1, (config_initial_geometry p).2,
    metadata.1.1, metadata.1.2]
  exact callerWords_le_occupied layout

theorem openingMatches_positive (layout : CallerLayout) (p : ParameterBounds.Profile)
    (lanes : Nat) (metadata : openingMatches p lanes layout = true) : 0 < lanes := by
  simp only [openingMatches,Bool.and_eq_true,beq_iff_eq] at metadata
  rw [metadata.1.1]
  exact lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_left 1 _)

theorem shapeValid_of_support (c : Protocol.Config) (lanes : Nat) (b : Array E)
    (valid : c.valid = true) (positive : 0 < lanes) (laneBound : lanes ≤ 2^c.folds[0]!)
    (size : b.size = 2^c.logN)
    (support : ∀ i, lanes * 2^(c.logN-c.folds[0]!) ≤ i → i < b.size → b[i]! = 0) :
    Protocol.shapeValid c lanes b = true := by
  simp only [Protocol.shapeValid,valid,positive,laneBound,size,Bool.true_and,
    decide_true,beq_self_eq_true]
  apply Array.all_eq_true.mpr
  intro i hi
  simp only [beq_iff_eq]
  rw [Array.getElem_extract]
  have hbound : lanes * 2^(c.logN-c.folds[0]!) + i < b.size := by
    simp only [Array.size_extract] at hi
    omega
  have h := support (lanes * 2^(c.logN-c.folds[0]!) + i) (by omega) hbound
  rw [_root_.getElem!_pos b _ hbound] at h
  exact h

/-- A decoded request is traced back to the unchanged concrete caller parser,
not to an externally supplied list of claims. -/
theorem decodeCaller_source_run (layout : CallerLayout) (entry : FiatShamirGame.FramedHistory)
    (answers : FiatShamirGame.Coordinate → FiatShamirGame.Digest32) (claims : CallerClaims)
    (accepted : decodeCaller layout entry answers = some claims) :
    ∃ tokens rest, sourceClaims layout tokens = some (claims,rest) := by
  cases ht : entryTokens entry answers with
  | none => simp [decodeCaller,ht] at accepted
  | some tokens =>
    have hi : interpretCaller layout tokens = some claims := by
      simpa [decodeCaller,ht] using accepted
    unfold interpretCaller at hi
    split at hi
    next h => simp at hi
    next h =>
      cases hs : sourceClaims layout tokens with
      | none => simp [hs] at hi
      | some result =>
        rcases result with ⟨actual,rest⟩
        simp only [hs,bind,Option.bind] at hi
        split at hi
        next empty =>
          have he : actual = claims := by simpa using hi
          subst actual
          exact ⟨tokens,rest,hs⟩
        next nonempty => simp at hi

/-- Public production metadata, with offsets generated rather than trusted.
The geometry field checks finite source incidences/dimensions only. -/
structure ProductionLayout where
  sources : Array Source
  layout : CallerLayout
  constructed : placementsOf sources = some (callerPlacements layout)
  geometry : WHIRCallerGeometry.LayoutGeometry
    (fun i d => columnFits sources i d = true)
    (fun o d => ringFits sources o d = true) layout

/-- Checked public constructor. This is not a verifier acceptance test: the
result is the fixed caller layout used to configure the source decoder. -/
def productionLayout (sources : Array Source) (raw : CallerLayout) : Option ProductionLayout :=
  match h : placementsOf sources with
  | none => none
  | some ps =>
    let layout := installPlacements ps raw
    if geometry : WHIRCallerGeometry.LayoutGeometry
        (fun i d => columnFits sources i d = true)
        (fun o d => ringFits sources o d = true) layout then
      some ⟨sources,layout,by simpa [layout] using h,geometry⟩
    else none

/-- The parser theorem is instantiated with the actual production sources. -/
theorem decoded_geometry (model : ProductionLayout) (entry : FiatShamirGame.FramedHistory)
    (answers : FiatShamirGame.Coordinate → FiatShamirGame.Digest32) (claims : CallerClaims)
    (accepted : decodeCaller model.layout entry answers = some claims) :
    WHIRCallerGeometry.ClaimsValid
      (fun i d => columnFits model.sources i d = true)
      (fun o d => ringFits model.sources o d = true) (callerPlacements model.layout) claims := by
  obtain ⟨tokens,rest,trace⟩ := decodeCaller_source_run model.layout entry answers claims accepted
  exact WHIRCallerGeometry.sourceClaims_geometry _ _
    (columnFits_mono model.sources) (ringFits_mono model.sources)
    model.layout model.geometry tokens claims rest trace

theorem geometry_support (model : ProductionLayout) (claims : CallerClaims)
    (geometry : WHIRCallerGeometry.ClaimsValid
      (fun i d => columnFits model.sources i d = true)
      (fun o d => ringFits model.sources o d = true) (callerPlacements model.layout) claims) :
    (∀ ring ∈ claims.families, ring.offset + 2^ring.point.size ≤ callerWords model.layout) ∧
    (∀ point ∈ claims.points.toList, ∀ v, callerWords model.layout ≤ v → pointWeight point v = 0) := by
  obtain ⟨rings,points⟩ := geometry
  rw [callerWords_placementsOf model.sources model.layout model.constructed]
  constructor
  · intro ring mem
    exact ringFits_bound model.sources ring.offset ring.point.size (rings ring mem)
  · intro point mem v hv
    obtain ⟨column,placed,atColumn,claimed,fits⟩ := points point mem
    exact production_point_support model.sources (callerPlacements model.layout)
      model.constructed column placed atColumn fits point claimed v hv

/-- Support of every actual decoded family/plain/strided claim is a consequence
of production placement and parser provenance, not a decoder-correctness axiom. -/
theorem decoded_support (model : ProductionLayout) (entry : FiatShamirGame.FramedHistory)
    (answers : FiatShamirGame.Coordinate → FiatShamirGame.Digest32) (claims : CallerClaims)
    (accepted : decodeCaller model.layout entry answers = some claims) :
    (∀ ring ∈ claims.families,
      ring.offset + 2^ring.point.size ≤ callerWords model.layout) ∧
    (∀ point ∈ claims.points.toList, ∀ v, callerWords model.layout ≤ v →
      pointWeight point v = 0) := by
  exact geometry_support model claims (decoded_geometry model entry answers claims accepted)

/-- Each original transformed claim passes the actual causal experiment's
shape check, including the unencoded lane tail. -/
theorem decoded_claim_shape (model : ProductionLayout) (p : ParameterBounds.Profile)
    (lanes : Nat) (metadata : openingMatches p lanes model.layout = true)
    (laneBound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!)
    (entry : FiatShamirGame.FramedHistory)
    (answers : FiatShamirGame.Coordinate → FiatShamirGame.Digest32) (claims : CallerClaims)
    (accepted : decodeCaller model.layout entry answers = some claims) (r : RingPCSGame.Prefix)
    (claim : CausalGame.Claim)
    (mem : claim ∈ (transformedClaims (2^(ParameterBounds.config p).logN)
      (fun i : Fin claims.families.length => claims.families[i]) claims.points r).toList) :
    Protocol.shapeValid (ParameterBounds.config p) lanes claim.weight = true := by
  obtain ⟨rings,points⟩ := decoded_support model entry answers claims accepted
  have occupied := openingMatches_occupied model.layout p lanes metadata
  have hs := transformed_claim_size _ _ _ _ claim mem
  apply shapeValid_of_support _ _ _ (ParameterBounds.production_config_valid p).1
    (openingMatches_positive model.layout p lanes metadata) laneBound hs
  intro v hv hi
  rw [hs] at hi
  exact transformed_claim_support _ (callerWords model.layout) _ _ r
    (fun j => rings _ (by simp)) points claim mem v (occupied.trans hv) hi

/-- The actual initial lambda batch has the physical verifier's required shape,
with no `tailZero` or `regionsFit` hypothesis. -/
theorem decoded_batch_shape (model : ProductionLayout) (p : ParameterBounds.Profile)
    (lanes : Nat) (metadata : openingMatches p lanes model.layout = true)
    (laneBound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!)
    (entry : FiatShamirGame.FramedHistory)
    (answers : FiatShamirGame.Coordinate → FiatShamirGame.Digest32) (claims : CallerClaims)
    (accepted : decodeCaller model.layout entry answers = some claims)
    (r : RingPCSGame.Prefix) (lambda : E) :
    Protocol.shapeValid (ParameterBounds.config p) lanes
      (CausalGame.batchClaims (2^(ParameterBounds.config p).logN)
        (transformedClaims (2^(ParameterBounds.config p).logN)
          (fun i : Fin claims.families.length => claims.families[i]) claims.points r) lambda).weight = true := by
  obtain ⟨rings,points⟩ := decoded_support model entry answers claims accepted
  have occupied := openingMatches_occupied model.layout p lanes metadata
  apply shapeValid_of_support _ _ _ (ParameterBounds.production_config_valid p).1
    (openingMatches_positive model.layout p lanes metadata) laneBound (InitialBatching.batchClaims_size _ _ _)
  intro v hv hi
  rw [InitialBatching.batchClaims_size] at hi
  exact transformed_batch_support _ (callerWords model.layout) _ _ r lambda
    (fun j => rings _ (by simp)) points v (occupied.trans hv) hi

/-- Successful source request decoding supplies all metadata guards. The
occupied-tail obligation is derived from the production construction above. -/
theorem decodeRequest_shapes (model : ProductionLayout) (cap : Nat)
    (p : ParameterBounds.Profile) (lanes : Nat) (entry : FiatShamirGame.FramedHistory)
    (answers : FiatShamirGame.Coordinate → FiatShamirGame.Digest32)
    (request : CausalBindingState.ClaimRequest cap p)
    (accepted : decodeRequest cap p lanes model.layout entry answers = some request)
    (r : RingPCSGame.Prefix) (lambda : E) :
    let claims := transformedClaims (2^(ParameterBounds.config p).logN)
      request.claims.family request.claims.points r
    (claims.all (fun claim => Protocol.shapeValid (ParameterBounds.config p) request.lanes claim.weight) = true) ∧
    Protocol.shapeValid (ParameterBounds.config p) request.lanes
      (CausalGame.batchClaims (2^(ParameterBounds.config p).logN) claims lambda).weight = true := by
  unfold decodeRequest at accepted
  split at accepted
  next rejected => simp at accepted
  next allowed =>
    have metadata : openingMatches p lanes model.layout = true := by simpa using allowed
    cases hc : decodeCaller model.layout entry answers with
    | none => simp [hc] at accepted
    | some claims =>
      simp only [hc,bind,Option.bind] at accepted
      split at accepted
      next laneBound =>
        split at accepted
        next familyBound =>
          split at accepted
          next claimBound =>
            have he := Option.some.inj accepted
            subst request
            constructor
            · apply Array.all_eq_true'.mpr
              intro claim mem
              exact decoded_claim_shape model p lanes metadata laneBound entry answers claims hc r claim
                (by simpa using mem)
            · exact decoded_batch_shape model p lanes metadata laneBound entry answers claims hc r lambda
          next tooMany => simp at accepted
        next tooMany => simp at accepted
      next tooMany => simp at accepted

/-- The physical partial-cache decoder uses the same constructed-layout shape
theorem; cache availability neither supplies nor assumes support. -/
theorem decodeAvailableRequest_shapes (model : ProductionLayout) (cap : Nat)
    (p : ParameterBounds.Profile) (lanes : Nat) (entry : FiatShamirGame.FramedHistory)
    (answers : FiatShamirGame.Coordinate → Option FiatShamirGame.Digest32)
    (request : CausalBindingState.ClaimRequest cap p)
    (accepted : decodeAvailableRequest cap p lanes model.layout entry answers = some request)
    (r : RingPCSGame.Prefix) (lambda : E) :
    let claims := transformedClaims (2^(ParameterBounds.config p).logN)
      request.claims.family request.claims.points r
    (claims.all (fun claim => Protocol.shapeValid (ParameterBounds.config p) request.lanes claim.weight) = true) ∧
    Protocol.shapeValid (ParameterBounds.config p) request.lanes
      (CausalGame.batchClaims (2^(ParameterBounds.config p).logN) claims lambda).weight = true := by
  unfold decodeAvailableRequest at accepted
  split at accepted
  next present =>
    exact decodeRequest_shapes model cap p lanes entry _ request accepted r lambda
  next missing => simp at accepted

theorem openingMatches_words_bound (layout : CallerLayout) (p : ParameterBounds.Profile)
    (lanes : Nat) (metadata : openingMatches p lanes layout = true)
    (laneBound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!) :
    callerWords layout ≤ 2^(ParameterBounds.config p).logN := by
  have occupied := openingMatches_occupied layout p lanes metadata
  have hn : (ParameterBounds.config p).folds[0]! ≤ (ParameterBounds.config p).logN := by
    rw [(config_initial_geometry p).1,(config_initial_geometry p).2]
    omega
  have hb := Nat.mul_le_mul_right
    (2^((ParameterBounds.config p).logN-(ParameterBounds.config p).folds[0]!)) laneBound
  rw [← Nat.pow_add, Nat.add_sub_of_le hn] at hb
  exact occupied.trans hb

theorem geometry_nativeShapes (model : ProductionLayout) (p : ParameterBounds.Profile)
    (lanes : Nat) (metadata : openingMatches p lanes model.layout = true)
    (laneBound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!) (claims : CallerClaims)
    (geometry : WHIRCallerGeometry.ClaimsValid
      (fun i d => columnFits model.sources i d = true)
      (fun o d => ringFits model.sources o d = true) (callerPlacements model.layout) claims) :
    SuccinctRingWeight.FamilyShape (ParameterBounds.config p).logN
      (fun i : Fin claims.families.length => claims.families[i]) ∧
    (∀ point ∈ claims.points.toList, SuccinctPointWeight.Shape (ParameterBounds.config p).logN point) := by
  obtain ⟨rings,points⟩ := geometry
  have bound : placedWords model.sources ≤ 2^(ParameterBounds.config p).logN := by
    rw [← callerWords_placementsOf model.sources model.layout model.constructed]
    exact openingMatches_words_bound model.layout p lanes metadata laneBound
  constructor
  · intro j
    exact ringFits_nativeShape model.sources _ _ _ (rings _ (by simp)) bound
  · intro point mem
    obtain ⟨column,placed,atColumn,claimed,fits⟩ := points point mem
    exact production_point_nativeShape model.sources (callerPlacements model.layout)
      model.constructed column placed atColumn fits point claimed _ bound

/-- Every source-decoded selector has the dimension, alignment, cube range,
and port-slot bounds needed by the native caller-weight equality. -/
theorem decoded_nativeShapes (model : ProductionLayout) (p : ParameterBounds.Profile)
    (lanes : Nat) (metadata : openingMatches p lanes model.layout = true)
    (laneBound : lanes ≤ 2^(ParameterBounds.config p).folds[0]!)
    (entry : FiatShamirGame.FramedHistory)
    (answers : FiatShamirGame.Coordinate → FiatShamirGame.Digest32) (claims : CallerClaims)
    (accepted : decodeCaller model.layout entry answers = some claims) :
    SuccinctRingWeight.FamilyShape (ParameterBounds.config p).logN
      (fun i : Fin claims.families.length => claims.families[i]) ∧
    (∀ point ∈ claims.points.toList, SuccinctPointWeight.Shape (ParameterBounds.config p).logN point) := by
  exact geometry_nativeShapes model p lanes metadata laneBound claims
    (decoded_geometry model entry answers claims accepted)

theorem decodeRequest_nativeShapes (model : ProductionLayout) (cap : Nat)
    (p : ParameterBounds.Profile) (lanes : Nat) (entry : FiatShamirGame.FramedHistory)
    (answers : FiatShamirGame.Coordinate → FiatShamirGame.Digest32)
    (request : CausalBindingState.ClaimRequest cap p)
    (accepted : decodeRequest cap p lanes model.layout entry answers = some request) :
    SuccinctRingWeight.FamilyShape (ParameterBounds.config p).logN request.claims.family ∧
    (∀ point ∈ request.claims.points.toList,
      SuccinctPointWeight.Shape (ParameterBounds.config p).logN point) := by
  unfold decodeRequest at accepted
  split at accepted
  next rejected => simp at accepted
  next allowed =>
    have metadata : openingMatches p lanes model.layout = true := by simpa using allowed
    cases hc : decodeCaller model.layout entry answers with
    | none => simp [hc] at accepted
    | some claims =>
      simp only [hc,bind,Option.bind] at accepted
      split at accepted
      next laneBound =>
        split at accepted
        next familyBound =>
          split at accepted
          next claimBound =>
            have he := Option.some.inj accepted
            subst request
            exact decoded_nativeShapes model p lanes metadata laneBound entry answers claims hc
          next tooMany => simp at accepted
        next tooMany => simp at accepted
      next tooMany => simp at accepted

theorem decodeAvailableRequest_nativeShapes (model : ProductionLayout) (cap : Nat)
    (p : ParameterBounds.Profile) (lanes : Nat) (entry : FiatShamirGame.FramedHistory)
    (answers : FiatShamirGame.Coordinate → Option FiatShamirGame.Digest32)
    (request : CausalBindingState.ClaimRequest cap p)
    (accepted : decodeAvailableRequest cap p lanes model.layout entry answers = some request) :
    SuccinctRingWeight.FamilyShape (ParameterBounds.config p).logN request.claims.family ∧
    (∀ point ∈ request.claims.points.toList,
      SuccinctPointWeight.Shape (ParameterBounds.config p).logN point) := by
  unfold decodeAvailableRequest at accepted
  split at accepted
  next present => exact decodeRequest_nativeShapes model cap p lanes entry _ request accepted
  next missing => simp at accepted

#print axioms decodeAvailableRequest_nativeShapes

#print axioms placementsOf_words
#print axioms production_point_support
#print axioms decoded_support
#print axioms decodeAvailableRequest_shapes

end Whir.WHIRCallerSupport
