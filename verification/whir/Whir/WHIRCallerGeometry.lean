import Whir.WHIRCallerSource
import Lean.Util.CollectAxioms

/-! Static public-layout capacities imply support bounds for the actual caller
parser's successful outputs. These proofs follow its StateT recursion, shared
bus-column cache, table and settled loops, Flock construction, producer and
register rings, and final placement. The static geometry check belongs to public
configuration construction; no new verifier rejection or terminal-tail premise
is inserted into the source parser. -/

namespace Whir.WHIRCallerGeometry
open Concrete WHIRCallerClaims RingPCSGame
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- A successful return of the actual state parser, with arbitrary preceding
and remaining tokens. No decoder equivalence or acceptance assumption is used. -/
def Ensures {A : Type} (parser : CallerParser A) (post : A → Prop) : Prop :=
  ∀ tokens value rest, parser tokens = some (value,rest) → post value

theorem ensures_pure {A : Type} (value : A) (post : A → Prop) (h : post value) :
    Ensures (pure value) post := by
  intro tokens result rest success
  have equal : value = result := congrArg Prod.fst (Option.some.inj success)
  exact equal ▸ h

theorem ensures_bind {A B : Type} (parser : CallerParser A) (next : A → CallerParser B)
    (pre : A → Prop) (post : B → Prop) (before : Ensures parser pre)
    (after : ∀ value, pre value → Ensures (next value) post) :
    Ensures (parser >>= next) post := by
  intro tokens result rest success
  change (parser tokens).bind (fun pair => next pair.1 pair.2) = some (result,rest) at success
  cases first : parser tokens with
  | none => simp [first] at success
  | some pair =>
    exact after pair.1 (before tokens pair.1 pair.2 first) pair.2 result rest
      (by simpa only [first, Option.bind_some] using success)

theorem ensures_bind_any {A B : Type} (parser : CallerParser A) (next : A → CallerParser B)
    (post : B → Prop) (after : ∀ value, Ensures (next value) post) :
    Ensures (parser >>= next) post :=
  ensures_bind parser next (fun _ => True) post (fun _ _ _ _ => trivial) (fun value _ => after value)

theorem ensures_failure {A : Type} (post : A → Prop) :
    Ensures (fun _ => none) post := by
  intro tokens value rest success
  contradiction

theorem ensures_mono {A : Type} {parser : CallerParser A} {P Q : A → Prop}
    (before : Ensures parser P) (implies : ∀ value, P value → Q value) : Ensures parser Q :=
  fun tokens value rest success => implies value (before tokens value rest success)

theorem ensures_forIn {A B : Type} (xs : List A) (initial : B)
    (body : A → B → CallerParser (ForInStep B)) (inv : B → Prop)
    (start : inv initial)
    (step : ∀ x ∈ xs, ∀ value, inv value → Ensures (body x value) (fun out => inv out.value)) :
    Ensures (forIn xs initial body) inv := by
  induction xs generalizing initial with
  | nil => exact ensures_pure initial inv start
  | cons x xs ih =>
    rw [List.forIn_cons]
    refine ensures_bind _ _ _ _ (step x List.mem_cons_self initial start) ?_
    intro out valid
    cases out with
    | done value => exact ensures_pure value inv valid
    | yield value =>
      exact ih value valid (fun a ha v hv => step a (List.mem_cons_of_mem x ha) v hv)

theorem ensures_forIn_size {A B : Type} (xs : List A) (initial : B)
    (body : A → B → CallerParser (ForInStep B)) (size : B → Nat)
    (step : ∀ x ∈ xs, ∀ value, Ensures (body x value) (fun out => size out.value ≤ size value + 1)) :
    Ensures (forIn xs initial body) (fun out => size out ≤ size initial + xs.length) := by
  induction xs generalizing initial with
  | nil => exact ensures_pure initial _ (by simp)
  | cons x xs ih =>
    rw [List.forIn_cons]
    refine ensures_bind _ _ _ _ (step x List.mem_cons_self initial) ?_
    intro out bound
    cases out with
    | done value =>
      change size value ≤ size initial + 1 at bound
      exact ensures_pure value _ (by simp only [List.length_cons]; omega)
    | yield value =>
      refine ensures_mono (ih value (fun a ha v => step a (List.mem_cons_of_mem x ha) v)) ?_
      intro result hr
      simp only [List.length_cons]
      change size value ≤ size initial + 1 at bound
      omega

theorem ensures_mapM {A B : Type} (xs : List A) (f : A → CallerParser B)
    (rel : A → B → Prop) (step : ∀ x ∈ xs, Ensures (f x) (rel x)) :
    Ensures (xs.mapM f) (List.Forall₂ rel xs) := by
  induction xs with
  | nil => exact ensures_pure [] _ List.Forall₂.nil
  | cons x xs ih =>
    rw [List.mapM_cons]
    refine ensures_bind _ _ _ _ (step x List.mem_cons_self) ?_
    intro value valid
    refine ensures_bind _ _ _ _ (ih (fun a ha => step a (List.mem_cons_of_mem x ha))) ?_
    intro rest relation
    exact ensures_pure _ _ (List.Forall₂.cons valid relation)

theorem readScalars_length (n : Nat) :
    Ensures (readScalars n) (fun values => values.length = n) := by
  induction n with
  | zero => exact ensures_pure [] _ rfl
  | succ n ih =>
    unfold readScalars
    refine ensures_bind_any _ _ _ ?_
    intro value
    refine ensures_bind _ _ _ _ ih ?_
    intro values length
    exact ensures_pure _ _ (by simp [length])

def ColumnValid (C : Nat → Nat → Prop) (claim : ColumnClaim) : Prop :=
  C claim.column claim.point.length

def Downward (C : Nat → Nat → Prop) : Prop :=
  ∀ index small large, small ≤ large → C index large → C index small

def BusGeometry (C : Nat → Nat → Prop) (layout : BusLayout) : Prop :=
  ∀ block ∈ layout.push ++ layout.pull, block.tableOwned = false →
    ∀ coord ∈ block.coords, match coord with
      | .column column => C column block.kappa
      | _ => True

theorem busClaims_geometry (C : Nat → Nat → Prop) (down : Downward C)
    (layout : BusLayout) (geometry : BusGeometry C layout) :
    Ensures (busClaims layout) (fun result => ∀ claim ∈ result.2, ColumnValid C claim) := by
  unfold busClaims
  split
  all_goals
    try (refine ensures_bind_any (nonce _) _ _ ?_; intro ignored)
    refine ensures_bind_any _ _ _ ?_
    intro draws
    refine ensures_bind_any _ _ _ ?_
    intro draw
    refine ensures_bind_any _ _ _ ?_
    intro point
    refine ensures_bind _ _ (fun state => ∀ claim ∈ state.2, ColumnValid C claim) _ ?_ ?_
    · refine ensures_forIn _ _ _ _ (by simp) ?_
      intro block member state valid
      dsimp only
      refine ensures_bind_any _ _ _ ?_
      intro checked
      split
      · rename_i unowned
        refine ensures_bind _ _ (fun state => ∀ claim ∈ state.2, ColumnValid C claim) _ ?_ ?_
        · refine ensures_forIn _ _ _ _ valid ?_
          intro coord hc state valid
          cases coord with
          | column column =>
            dsimp only
            split
            · refine ensures_bind_any _ _ _ ?_
              intro value
              refine ensures_pure _ _ ?_
              intro claim found
              rcases List.mem_append.mp found with old | fresh
              · exact valid claim old
              · have eq := List.mem_singleton.mp fresh
                subst claim
                exact down column _ block.kappa (List.length_take_le _ _)
                  (geometry block member (by simpa using unowned) (.column column) hc)
            · exact ensures_pure _ _ valid
          | publicValue => exact ensures_pure _ _ valid
          | tableExpression =>
            intro tokens out rest success
            change none = some (out,rest) at success
            contradiction
        · intro state valid
          exact ensures_pure _ _ valid
      · exact ensures_pure _ _ valid
    · intro state valid
      exact ensures_pure _ _ valid

def TableGeometry (layout : AirLayout) (claims : TableClaims) : Prop :=
  claims.point.length ≤ layout.tau ∧ claims.evals.length ≤ layout.columns - layout.publicColumns

theorem receiveTable_geometry (layout : AirLayout) (point : List E) :
    Ensures (receiveTable layout point) (TableGeometry layout) := by
  unfold receiveTable
  refine ensures_bind_any _ _ _ ?_
  intro checked
  refine ensures_bind_any _ _ _ ?_
  intro checked
  refine ensures_bind_any _ _ _ ?_
  intro checked
  refine ensures_bind_any _ _ _ ?_
  intro sent
  refine ensures_bind_any _ _ _ ?_
  intro slices
  refine ensures_bind _ _ (fun state => state.2.length ≤ layout.columns-layout.publicColumns) _ ?_ ?_
  · refine ensures_mono (ensures_forIn_size _ _ _ (fun state => state.2.length) ?_) ?_
    · intro c member state
      dsimp only
      split
      · exact ensures_pure _ _ (by simp)
      · rename_i missing
        split
        · exact ensures_failure _
        · exact ensures_pure _ _ (by simp)
    · intro state bound
      simpa only [List.length_nil, Nat.zero_add, List.length_range] using bound
  · intro state bound
    refine ensures_bind_any _ _ _ ?_
    intro checked
    exact ensures_pure _ _ ⟨List.length_take_le _ _,bound⟩

theorem constraintClaims_geometry (layouts : List AirLayout) (busPoint : List E) :
    Ensures (constraintClaims layouts busPoint) (List.Forall₂ TableGeometry layouts) := by
  unfold constraintClaims
  refine ensures_bind_any _ _ _ ?_
  intro checked
  refine ensures_bind_any _ _ _ ?_
  intro rounds
  exact ensures_mapM _ _ _ (fun layout _ => receiveTable_geometry layout rounds.reverse)

theorem assembleFlock_geometry (layout : FlockLayout) (zc lc slices : List E)
    (claim : FamilyClaim) (success : assembleFlock layout zc lc slices = some claim) :
    claim.offset = layout.offset ∧ claim.point.size ≤ layout.kLog - 6 + layout.instanceLog := by
  unfold assembleFlock at success
  dsimp only at success
  split at success
  · contradiction
  · split at success
    · cases Option.some.inj success
      constructor
      · rfl
      · simp only [List.size_toArray, List.length_append, List.length_reverse, List.length_take]
        omega
    · contradiction

def RingValid (R : Nat → Nat → Prop) (claim : FamilyClaim) : Prop :=
  R claim.offset claim.point.size

theorem forall2_mem_right {A B : Type} {rel : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ rel xs ys) {value : B} (member : value ∈ ys) :
    ∃ input ∈ xs, rel input value := by
  induction related with
  | nil => simp at member
  | @cons x y xs ys h hs ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨x,List.mem_cons_self,h⟩
    · obtain ⟨a,ha,hr⟩ := ih tail
      exact ⟨a,List.mem_cons_of_mem x ha,hr⟩

theorem flockClaims_geometry (R : Nat → Nat → Prop) (down : Downward R)
    (layouts : List FlockLayout)
    (geometry : ∀ layout ∈ layouts, R layout.offset (layout.kLog - 6 + layout.instanceLog)) :
    Ensures (flockClaims layouts) (fun claims => ∀ claim ∈ claims, RingValid R claim) := by
  unfold flockClaims
  refine ensures_bind_any _ _ _ ?_
  intro checked
  refine ensures_bind_any _ _ _ ?_
  intro sampled
  refine ensures_bind_any _ _ _ ?_
  intro sampled
  refine ensures_bind_any _ _ _ ?_
  intro sent
  refine ensures_bind_any _ _ _ ?_
  intro sampled
  refine ensures_bind_any _ _ _ ?_
  intro zc
  refine ensures_bind_any _ _ _ ?_
  intro sent
  refine ensures_bind_any _ _ _ ?_
  intro sampled
  refine ensures_bind_any _ _ _ ?_
  intro lc
  refine ensures_mono (ensures_mapM _ _ (fun layout claim =>
    claim.offset = layout.offset ∧ claim.point.size ≤ layout.kLog - 6 + layout.instanceLog) ?_) ?_
  · intro layout member
    refine ensures_bind_any _ _ _ ?_
    intro slices
    refine ensures_bind_any _ _ _ ?_
    intro sent
    split
    · rename_i claim success
      exact ensures_pure _ _ (assembleFlock_geometry layout zc lc slices claim success)
    · exact ensures_failure _
  · intro claims relation claim member
    obtain ⟨layout,hl,hrel⟩ := forall2_mem_right relation member
    exact down claim.offset _ _ hrel.2 (hrel.1 ▸ geometry layout hl)

theorem paddedRing_geometry (offset : Nat) (point slices : List E) (claim : FamilyClaim)
    (success : paddedRing offset point slices = some claim) :
    claim.offset = offset ∧ claim.point.size = point.length := by
  unfold paddedRing at success
  split at success
  · cases Option.some.inj success
    exact ⟨rfl,List.size_toArray⟩
  · contradiction

theorem exitClaims_geometry (C : Nat → Nat → Prop) (column : Nat) (output : Fin 4 → UInt64)
    (geometry : C column 6) : ∀ claim ∈ exitClaims column output, ColumnValid C claim := by
  intro claim member
  simp only [exitClaims, List.mem_cons, List.mem_ofFn] at member
  rcases member with rfl | ⟨i,rfl⟩ <;> simpa [ColumnValid] using geometry

theorem forall2_append {A B : Type} {rel : A → B → Prop}
    {xs xs' : List A} {ys ys' : List B}
    (left : List.Forall₂ rel xs ys) (right : List.Forall₂ rel xs' ys') :
    List.Forall₂ rel (xs ++ xs') (ys ++ ys') := by
  induction left with
  | nil => exact right
  | cons first rest ih => exact List.Forall₂.cons first ih

theorem ensures_forIn_append {A B D : Type} (xs : List A) (initial : List B)
    (body : A → List B → CallerParser (ForInStep (List B))) (select : A → List D)
    (rel : D → B → Prop)
    (step : ∀ x ∈ xs, ∀ values, Ensures (body x values)
      (fun out => ∃ added, out = .yield (values ++ added) ∧ List.Forall₂ rel (select x) added)) :
    Ensures (forIn xs initial body)
      (fun out => ∃ added, out = initial ++ added ∧ List.Forall₂ rel (xs.flatMap select) added) := by
  induction xs generalizing initial with
  | nil => exact ensures_pure initial _ ⟨[],by simp,List.Forall₂.nil⟩
  | cons x xs ih =>
    rw [List.forIn_cons]
    refine ensures_bind _ _ _ _ (step x List.mem_cons_self initial) ?_
    rintro out ⟨added,rfl,related⟩
    refine ensures_mono (ih (initial ++ added)
      (fun a ha values => step a (List.mem_cons_of_mem x ha) values)) ?_
    rintro result ⟨tail,rfl,rest⟩
    exact ⟨added ++ tail,by simp [List.append_assoc],forall2_append related rest⟩

def SettledGeometry (layout : CpuTableLayout) (claims : TableClaims) : Prop :=
  claims.point.length ≤ layout.tau ∧ claims.evals.length ≤ layout.committedColumns

theorem settledClaims_geometry (tables : List CpuTableLayout) (point : List E) :
    Ensures (settledClaims tables point)
      (List.Forall₂ SettledGeometry (tables.filter CpuTableLayout.settled)) := by
  unfold settledClaims
  refine ensures_bind _ _ (fun out => ∃ added, out = [] ++ added ∧
    List.Forall₂ SettledGeometry
      (tables.flatMap fun t => if t.settled then [t] else []) added) _ ?_ ?_
  · refine ensures_forIn_append _ _ _ _ _ ?_
    intro table member values
    dsimp only
    split
    · rename_i settled
      refine ensures_bind_any _ _ _ ?_
      intro checked
      refine ensures_bind_any _ _ _ ?_
      intro checked
      refine ensures_bind_any _ _ _ ?_
      intro sent
      refine ensures_bind _ _ (fun state => state.2.length ≤ table.committedColumns) _ ?_ ?_
      · refine ensures_mono (ensures_forIn_size _ _ _ (fun state => state.2.length) ?_) ?_
        · intro c member state
          split
          · exact ensures_pure _ _ (by simp)
          · split
            · exact ensures_failure _
            · exact ensures_pure _ _ (by simp)
        · intro state bounded
          simpa only [List.length_nil, Nat.zero_add, List.length_range] using bounded
      · intro state bounded
        refine ensures_bind_any _ _ _ ?_
        intro checked
        refine ensures_pure _ _ ⟨[⟨point.take table.tau,state.2,[]⟩],rfl,?_⟩
        exact List.Forall₂.cons ⟨List.length_take_le _ _,bounded⟩ List.Forall₂.nil
    · rename_i unsettled
      refine ensures_pure _ _ ⟨[],by simp,?_⟩
      exact List.Forall₂.nil
  · rintro result ⟨added,equal,related⟩
    have select_eq : (tables.flatMap fun t => if t.settled then [t] else []) =
        tables.filter CpuTableLayout.settled := by
      clear related
      induction tables with
      | nil => rfl
      | cons t ts ih => cases h : t.settled <;> simp [h,ih]
    simp only [List.nil_append] at equal
    subst result
    rw [select_eq] at related
    exact ensures_pure _ _ related

theorem forall2_get? {A B : Type} {rel : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ rel xs ys) (index : Nat) (value : B)
    (found : ys[index]? = some value) : ∃ input, xs[index]? = some input ∧ rel input value := by
  obtain ⟨bound,equal⟩ := List.getElem?_eq_some_iff.mp found
  have inputBound : index < xs.length := by rw [related.length_eq]; exact bound
  refine ⟨xs[index],by simp [inputBound],?_⟩
  simpa only [List.get_eq_getElem, equal] using related.get inputBound bound

theorem tableColumns_geometry (C : Nat → Nat → Prop) (down : Downward C)
    (base tau count : Nat) (claims : TableClaims)
    (point : claims.point.length ≤ tau) (evals : claims.evals.length ≤ count)
    (geometry : ∀ i ∈ List.range count, C (base+i) tau) :
    ∀ claim ∈ tableColumns base claims, ColumnValid C claim := by
  intro claim member
  obtain ⟨⟨value,index⟩,found,rfl⟩ := List.mem_map.mp member
  have atIndex := List.mk_mem_zipIdx_iff_getElem?.mp found
  have bound := (List.getElem?_eq_some_iff.mp atIndex).1
  exact down (base+index) _ tau point
    (geometry index (List.mem_range.mpr (bound.trans_le evals)))

def TableColumnsGeometry (C : Nat → Nat → Prop) (base tau count : Nat) : Prop :=
  ∀ i ∈ List.range count, C (base+i) tau

def RecGeometry (C R : Nat → Nat → Prop) (layout : RecLayout) : Prop :=
  BusGeometry C layout.bus ∧
  (∀ table ∈ layout.tables, TableColumnsGeometry C table.1 table.2.tau
    (table.2.columns-table.2.publicColumns)) ∧
  R layout.hash.offset (layout.hash.kLog-6+layout.hash.instanceLog)

def PointValid (C : Nat → Nat → Prop) (placements : Array Placement) (point : PointClaim) : Prop :=
  ∃ claim placement, placements[claim.column]? = some placement ∧
    placeClaim placement claim = some point ∧ ColumnValid C claim

def ClaimsValid (C R : Nat → Nat → Prop) (placements : Array Placement) (claims : CallerClaims) : Prop :=
  (∀ ring ∈ claims.families, RingValid R ring) ∧
  (∀ point ∈ claims.points.toList, PointValid C placements point)

theorem option_mapM_rel {A B : Type} (f : A → Option B) (xs : List A) (ys : List B)
    (success : xs.mapM f = some ys) : List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => cases Option.some.inj success; exact List.Forall₂.nil
  | cons x xs ih =>
    rw [List.mapM_cons] at success
    change (f x).bind (fun y => (xs.mapM f).bind (fun ys => some (y :: ys))) = some ys at success
    cases first : f x with
    | none => simp only [first, Option.bind_none] at success; contradiction
    | some y =>
      cases rest : xs.mapM f with
      | none => simp only [first, Option.bind_some, rest, Option.bind_none] at success; contradiction
      | some tail =>
        simp only [first, Option.bind_some, rest] at success
        cases Option.some.inj success
        exact List.Forall₂.cons first (ih tail rest)

theorem placeClaims_geometry (C : Nat → Nat → Prop) (placements : Array Placement)
    (claims : List ColumnClaim) (valid : ∀ claim ∈ claims, ColumnValid C claim)
    (points : Array PointClaim) (success : placeClaims placements claims = some points) :
    ∀ point ∈ points.toList, PointValid C placements point := by
  change (claims.mapM (fun c => (placements[c.column]?).bind
    (fun p => some (placeClaim p c)))).bind
      (fun located => some ((located.filterMap id).toArray)) = some points at success
  cases located : claims.mapM (fun c => (placements[c.column]?).bind
      (fun p => some (placeClaim p c))) with
  | none =>
    simp only [located, Option.bind_none] at success
    contradiction
  | some options =>
    simp only [located, Option.bind_some] at success
    cases Option.some.inj success
    intro point member
    change point ∈ options.filterMap id at member
    obtain ⟨option,member,equal⟩ := List.mem_filterMap.mp member
    have related := option_mapM_rel _ _ _ located
    obtain ⟨claim,hclaim,hvalue⟩ := forall2_mem_right related member
    change option = some point at equal
    cases hp : placements[claim.column]? with
    | none =>
      simp only [hp, Option.bind_none] at hvalue
      contradiction
    | some placement =>
      refine ⟨claim,placement,hp,?_,valid claim hclaim⟩
      simp only [hp, Option.bind_some] at hvalue
      exact (Option.some.inj hvalue).trans equal

theorem rec_tableColumns_geometry (C : Nat → Nat → Prop) (down : Downward C)
    (layouts : List (Nat × AirLayout)) (claims : List TableClaims)
    (related : List.Forall₂ TableGeometry (layouts.map Prod.snd) claims)
    (geometry : ∀ table ∈ layouts, TableColumnsGeometry C table.1 table.2.tau
      (table.2.columns-table.2.publicColumns)) :
    ∀ claim ∈ ((layouts.map Prod.fst).zip claims).flatMap
      (fun (base,claims) => tableColumns base claims), ColumnValid C claim := by
  induction layouts generalizing claims with
  | nil => cases related; simp
  | cons layout layouts ih =>
    cases related with
    | cons first rest =>
      intro claim member
      simp only [List.map_cons, List.zip_cons_cons, List.flatMap_cons, List.mem_append] at member
      rcases member with current | later
      · exact tableColumns_geometry C down layout.1 layout.2.tau _ _ first.1 first.2
          (geometry layout List.mem_cons_self) claim current
      · exact ih _ rest (fun l hl => geometry l (List.mem_cons_of_mem layout hl)) claim later

def PayloadValid (C R : Nat → Nat → Prop) (placements : Array Placement)
    (payload : List FamilyClaim × Array PointClaim) : Prop :=
  (∀ ring ∈ payload.1, RingValid R ring) ∧
  (∀ point ∈ payload.2.toList, PointValid C placements point)

theorem recPayload_geometry (C R : Nat → Nat → Prop) (columnDown : Downward C) (ringDown : Downward R)
    (layout : RecLayout) (geometry : RecGeometry C R layout) :
    Ensures (recPayload layout) (PayloadValid C R layout.placements) := by
  unfold recPayload
  refine ensures_bind _ _ _ _ (busClaims_geometry C columnDown layout.bus geometry.1) ?_
  rintro ⟨point,bus⟩ busValid
  refine ensures_bind_any _ _ _ ?_
  intro draw
  refine ensures_bind _ _ _ _ (constraintClaims_geometry _ point) ?_
  intro tables tableValid
  refine ensures_bind _ _ _ _ (flockClaims_geometry R ringDown [layout.hash] (by simpa using geometry.2.2)) ?_
  intro rings ringValid
  dsimp only
  split
  · rename_i points success
    refine ensures_pure _ _ ⟨ringValid,?_⟩
    apply placeClaims_geometry C layout.placements _ _ points success
    intro claim member
    rcases List.mem_append.mp member with bus | table
    · exact busValid claim bus
    · exact rec_tableColumns_geometry C columnDown _ _ tableValid geometry.2.1 claim table
  · exact ensures_failure _

theorem recClaims_geometry (C R : Nat → Nat → Prop) (columnDown : Downward C) (ringDown : Downward R)
    (layout : RecLayout) (geometry : RecGeometry C R layout) :
    Ensures (recClaims layout) (ClaimsValid C R layout.placements) := by
  unfold recClaims
  refine ensures_bind_any _ _ _ ?_
  intro root
  refine ensures_bind _ _ _ _ (recPayload_geometry C R columnDown ringDown layout geometry) ?_
  rintro ⟨rings,points⟩ valid
  exact ensures_pure _ _ valid

theorem check_true (b : Bool) : Ensures (check b) (fun _ => b = true) := by
  cases b with
  | false => exact ensures_failure _
  | true => exact ensures_pure () _ rfl

theorem filter_true {A : Type} (xs : List A) (p : A → Bool) (all : xs.all p = true) :
    xs.filter p = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h : p x = true ∧ xs.all p = true := by simpa only [List.all_cons, Bool.and_eq_true] using all
    simp only [List.filter_cons, h.1, ↓reduceIte, ih h.2]

theorem filter_false {A : Type} (xs : List A) (p : A → Bool)
    (all : xs.all (fun x => !p x) = true) : xs.filter p = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h : (!p x) = true ∧ xs.all (fun x => !p x) = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using all
    have hx : p x = false := by simpa using h.1
    simp only [List.filter_cons, hx, Bool.false_eq_true, ↓reduceIte, ih h.2]

theorem settled_prefix (tables : List CpuTableLayout) (n : Nat)
    (before : (tables.take n).all CpuTableLayout.settled = true)
    (after : (tables.drop n).all (fun t => !t.settled) = true) :
    tables.filter CpuTableLayout.settled = tables.take n := by
  calc
    _ = (tables.take n).filter CpuTableLayout.settled ++ (tables.drop n).filter CpuTableLayout.settled := by
      rw [← List.filter_append, List.take_append_drop]
    _ = _ := by rw [filter_true _ _ before, filter_false _ _ after, List.append_nil]

def CpuTableGeometry (table : CpuTableLayout) (claims : TableClaims) : Prop :=
  claims.point.length ≤ table.tau ∧
    claims.evals.length ≤ max table.committedColumns table.summedColumns.length

theorem forall2_imp {A B : Type} {P Q : A → B → Prop} {xs : List A} {ys : List B}
    (h : List.Forall₂ P xs ys) (imp : ∀ a b, P a b → Q a b) : List.Forall₂ Q xs ys := by
  induction h with
  | nil => exact .nil
  | cons first rest ih => exact .cons (imp _ _ first) ih

theorem forall2_map_left {A B D : Type} {rel : D → B → Prop} (f : A → D) {xs : List A} {ys : List B}
    (h : List.Forall₂ rel (xs.map f) ys) : List.Forall₂ (fun a b => rel (f a) b) xs ys := by
  induction xs generalizing ys with
  | nil => cases h; exact .nil
  | cons x xs ih => cases h with | cons first rest => exact .cons first (ih rest)

theorem cpu_columns_geometry (tables : List CpuTableLayout) (producers : List AirLayout)
    (settled summed : List TableClaims)
    (settledValid : List.Forall₂ SettledGeometry (tables.filter CpuTableLayout.settled) settled)
    (summedValid : List.Forall₂ TableGeometry (tables.map CpuTableLayout.air ++ producers) summed)
    (before : (tables.take settled.length).all CpuTableLayout.settled = true)
    (after : (tables.drop settled.length).all (fun t => !t.settled) = true) :
    List.Forall₂ CpuTableGeometry tables
      (settled ++ (summed.take tables.length).drop settled.length) := by
  have first : List.Forall₂ CpuTableGeometry (tables.take settled.length) settled := by
    rw [← settled_prefix tables settled.length before after]
    exact forall2_imp settledValid (fun t c h => ⟨h.1,h.2.trans (Nat.le_max_left _ _)⟩)
  have total : List.Forall₂ TableGeometry (tables.map CpuTableLayout.air) (summed.take tables.length) := by
    have h := List.forall₂_take tables.length summedValid
    simpa [List.take_append, ← List.map_take] using h
  have total' := forall2_imp (forall2_map_left CpuTableLayout.air total)
    (Q := CpuTableGeometry) (fun t c h => (⟨h.1,
      (by simpa [CpuTableLayout.air] using h.2.trans (Nat.le_max_right t.committedColumns t.summedColumns.length))⟩))
  have last := List.forall₂_drop settled.length total'
  simpa only [List.take_append_drop] using forall2_append first last

def CpuGeometry (C R : Nat → Nat → Prop) (layout : CpuLayout) : Prop :=
  BusGeometry C layout.bus ∧
  (∀ table ∈ layout.tables, TableColumnsGeometry C table.base table.tau
    (max table.committedColumns table.summedColumns.length)) ∧
  C layout.finalRegisterColumn 6 ∧
  (∀ flock ∈ layout.flock, R flock.offset (flock.kLog-6+flock.instanceLog)) ∧
  (∀ producer ∈ layout.bus.producers, R producer.window producer.kappa) ∧
  (∀ word ∈ layout.registers, match word.tables.head? with
    | none => False
    | some first => match layout.tables[first]? with
      | none => False
      | some table => R word.offset table.tau)

def LayoutGeometry (C R : Nat → Nat → Prop) : CallerLayout → Prop
  | .cpu layout => CpuGeometry C R layout
  | .recursion layout => RecGeometry C R layout

instance (C : Nat → Nat → Prop) [DecidableRel C] (layout : BusLayout) :
    Decidable (BusGeometry C layout) := by
  letI (k : Nat) : DecidablePred (fun coord : BusCoord => match coord with
      | .column column => C column k
      | _ => True) := fun coord => by cases coord <;> infer_instance
  unfold BusGeometry
  infer_instance

instance (C : Nat → Nat → Prop) [DecidableRel C] (base tau count : Nat) :
    Decidable (TableColumnsGeometry C base tau count) :=
  inferInstanceAs (Decidable (∀ i ∈ List.range count, C (base+i) tau))

instance (C R : Nat → Nat → Prop) [DecidableRel C] [DecidableRel R] (layout : RecLayout) :
    Decidable (RecGeometry C R layout) := by unfold RecGeometry; infer_instance

instance (C R : Nat → Nat → Prop) [DecidableRel C] [DecidableRel R] (layout : CpuLayout) :
    Decidable (CpuGeometry C R layout) := by
  letI : DecidablePred (fun word : RegisterWord => match word.tables.head? with
    | none => False
    | some first => match layout.tables[first]? with
      | none => False
      | some table => R word.offset table.tau) := fun word => by
        dsimp only
        split
        · infer_instance
        · split <;> infer_instance
  unfold CpuGeometry
  infer_instance

instance (C R : Nat → Nat → Prop) [DecidableRel C] [DecidableRel R] (layout : CallerLayout) :
    Decidable (LayoutGeometry C R layout) := by
  cases layout <;> dsimp only [LayoutGeometry] <;> infer_instance

theorem forall2_zip {A B : Type} {rel : A → B → Prop} {xs : List A} {ys : List B}
    (related : List.Forall₂ rel xs ys) (x : A) (y : B) (member : (x,y) ∈ xs.zip ys) :
    rel x y := by
  induction related with
  | nil => simp at member
  | @cons a b as bs first rest ih =>
    rcases List.mem_cons.mp member with eq | tail
    · rcases Prod.mk.inj eq with ⟨rfl,rfl⟩
      exact first
    · exact ih tail

theorem zip_member_left {A B : Type} {xs : List A} {ys : List B} {x : A} {y : B}
    (member : (x,y) ∈ xs.zip ys) : x ∈ xs := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons a as ih =>
    cases ys with
    | nil => simp at member
    | cons b bs =>
      rcases List.mem_cons.mp member with equal | later
      · rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih later)

theorem get?_append_left {A : Type} (xs ys : List A) (index : Nat) (value : A)
    (found : xs[index]? = some value) : (xs ++ ys)[index]? = some value := by
  obtain ⟨bound,equal⟩ := List.getElem?_eq_some_iff.mp found
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨by simp only [List.length_append]; omega,?_⟩
  rw [List.getElem_append_left bound]
  exact equal

theorem cpu_tableColumns_geometry (C : Nat → Nat → Prop) (down : Downward C)
    (layouts : List CpuTableLayout) (claims : List TableClaims)
    (related : List.Forall₂ CpuTableGeometry layouts claims)
    (geometry : ∀ table ∈ layouts, TableColumnsGeometry C table.base table.tau
      (max table.committedColumns table.summedColumns.length)) :
    ∀ claim ∈ ((layouts.map CpuTableLayout.base).zip claims).flatMap
      (fun (base,claims) => tableColumns base claims), ColumnValid C claim := by
  induction related with
  | nil => simp
  | @cons layout claim layouts claims first rest ih =>
    intro result member
    simp only [List.map_cons, List.zip_cons_cons, List.flatMap_cons, List.mem_append] at member
    rcases member with current | later
    · exact tableColumns_geometry C down layout.base layout.tau _ _ first.1 first.2
        (geometry layout List.mem_cons_self) result current
    · exact ih (fun l hl => geometry l (List.mem_cons_of_mem layout hl)) result later

theorem cpuPayload_geometry (C R : Nat → Nat → Prop) (columnDown : Downward C) (ringDown : Downward R)
    (layout : CpuLayout) (geometry : CpuGeometry C R layout) :
    Ensures (cpuPayload layout) (PayloadValid C R layout.placements) := by
  unfold cpuPayload
  refine ensures_bind _ _ _ _ (busClaims_geometry C columnDown layout.bus geometry.1) ?_
  rintro ⟨point,bus⟩ busValid
  refine ensures_bind _ _ _ _ (settledClaims_geometry layout.tables point) ?_
  intro settled settledValid
  refine ensures_bind_any _ _ _ ?_
  intro draw
  refine ensures_bind _ _ _ _ (constraintClaims_geometry _ point) ?_
  intro summed summedValid
  refine ensures_bind _ _ _ _ (check_true _) ?_
  intro checked settledBefore
  refine ensures_bind _ _ _ _ (check_true _) ?_
  intro checked settledAfter
  have columnValid := cpu_columns_geometry layout.tables _ settled summed
    settledValid summedValid settledBefore settledAfter
  refine ensures_bind _ _ _ _ (flockClaims_geometry R ringDown layout.flock geometry.2.2.2.1) ?_
  intro packed packedValid
  have producersValid : List.Forall₂ (fun (p : BusProducer) (c : TableClaims) =>
      c.point.length ≤ p.kappa) layout.bus.producers (summed.drop layout.tables.length) := by
    have h := List.forall₂_drop layout.tables.length summedValid
    have hp : List.Forall₂ TableGeometry
        (layout.bus.producers.map (fun p => (⟨p.kappa,2*p.bits,p.bits,[]⟩ : AirLayout)))
        (summed.drop layout.tables.length) := by
      simpa [List.drop_append, ← List.map_drop] using h
    exact forall2_imp (forall2_map_left _ hp) (fun _ _ valid => valid.1)
  refine ensures_bind _ _ (fun rings => ∀ ring ∈ rings, RingValid R ring) _ ?_ ?_
  · refine ensures_forIn _ _ _ _ packedValid ?_
    rintro ⟨producer,claims⟩ member rings valid
    dsimp only
    split
    · rename_i ring assembled
      have h := paddedRing_geometry producer.window claims.point claims.evals ring assembled
      refine ensures_pure _ _ ?_
      intro value member'
      rcases List.mem_append.mp member' with old | fresh
      · exact valid value old
      · have eq := List.mem_singleton.mp fresh
        subst value
        have pointBound := forall2_zip producersValid producer claims member
        have producerMember : producer ∈ layout.bus.producers := zip_member_left member
        exact ringDown ring.offset _ _ (h.2 ▸ pointBound)
          (h.1 ▸ geometry.2.2.2.2.1 producer producerMember)
    · exact ensures_failure _
  · intro rings ringsValid
    refine ensures_bind _ _ (fun state => state.1 = none ∧ ∀ ring ∈ state.2, RingValid R ring) _ ?_ ?_
    · refine ensures_forIn _ _ _ _ ⟨rfl,ringsValid⟩ ?_
      intro word member state valid
      dsimp only
      split
      · rename_i first head
        split
        · rename_i firstClaims found
          have register := geometry.2.2.2.2.2 word member
          rw [head] at register
          cases ht : layout.tables[first]? with
          | none => simp only [ht] at register
          | some table =>
            have rowBound : firstClaims.point.length ≤ table.tau := by
              obtain ⟨air,atAir,valid⟩ := forall2_get? summedValid first firstClaims found
              have current : (layout.tables.map CpuTableLayout.air)[first]? = some table.air := by
                simp only [List.getElem?_map, ht, Option.map_some]
              have same := (get?_append_left (layout.tables.map CpuTableLayout.air) _ first table.air current).symm.trans atAir
              cases Option.some.inj same
              exact valid.1
            have ringCapacity : R word.offset table.tau := by simpa only [ht] using register
            refine ensures_bind _ _ (fun state => state.1 = none) _ ?_ ?_
            · refine ensures_forIn _ _ _ _ rfl ?_
              intro t member state valid
              split
              · exact ensures_pure _ _ rfl
              · exact ensures_failure _
            · intro slices noReturn
              rw [noReturn]
              dsimp only
              split
              · rename_i ring assembled
                have h := paddedRing_geometry word.offset firstClaims.point slices.2 ring assembled
                refine ensures_pure _ _ ⟨rfl,?_⟩
                intro value member'
                rcases List.mem_append.mp member' with old | fresh
                · exact valid.2 value old
                · have eq := List.mem_singleton.mp fresh
                  subst value
                  exact ringDown ring.offset _ _ (h.2 ▸ rowBound) (h.1 ▸ ringCapacity)
              · exact ensures_failure _
        · exact ensures_failure _
      · exact ensures_failure _
    · intro state valid
      dsimp only
      rw [valid.1]
      dsimp only
      split
      · rename_i points success
        refine ensures_pure _ _ ⟨valid.2,?_⟩
        apply placeClaims_geometry C layout.placements _ _ points success
        intro claim member
        rcases List.mem_append.mp member with earlier | exit
        · rcases List.mem_append.mp earlier with bus | table
          · exact busValid claim bus
          · exact cpu_tableColumns_geometry C columnDown _ _ columnValid geometry.2.1 claim table
        · exact exitClaims_geometry C layout.finalRegisterColumn layout.output geometry.2.2.1 claim exit
      · exact ensures_failure _

theorem cpuClaims_geometry (C R : Nat → Nat → Prop) (columnDown : Downward C) (ringDown : Downward R)
    (layout : CpuLayout) (geometry : CpuGeometry C R layout) :
    Ensures (cpuClaims layout) (ClaimsValid C R layout.placements) := by
  unfold cpuClaims
  refine ensures_bind_any _ _ _ ?_
  intro root
  refine ensures_bind _ _ _ _ (cpuPayload_geometry C R columnDown ringDown layout geometry) ?_
  rintro ⟨rings,points⟩ valid
  exact ensures_pure _ _ valid

theorem sourceClaims_geometry (C R : Nat → Nat → Prop) (columnDown : Downward C) (ringDown : Downward R)
    (layout : CallerLayout) (geometry : LayoutGeometry C R layout) :
    Ensures (sourceClaims layout) (ClaimsValid C R (callerPlacements layout)) := by
  cases layout with
  | cpu layout => exact cpuClaims_geometry C R columnDown ringDown layout geometry
  | recursion layout => exact recClaims_geometry C R columnDown ringDown layout geometry

theorem interpretCaller_geometry (C R : Nat → Nat → Prop) (columnDown : Downward C) (ringDown : Downward R)
    (layout : CallerLayout) (geometry : LayoutGeometry C R layout)
    (tokens : List CallerToken) (claims : CallerClaims)
    (success : interpretCaller layout tokens = some claims) :
    ClaimsValid C R (callerPlacements layout) claims := by
  unfold interpretCaller at success
  split at success
  · contradiction
  · cases parsed : sourceClaims layout tokens with
    | none => simp [parsed] at success
    | some pair =>
      simp only [parsed] at success
      change (if pair.2.isEmpty then some pair.1 else none) = some claims at success
      split at success
      · cases Option.some.inj success
        exact sourceClaims_geometry C R columnDown ringDown layout geometry tokens pair.1 pair.2 parsed
      · contradiction

theorem decodeCaller_geometry (C R : Nat → Nat → Prop)
    (columnDown : Downward C) (ringDown : Downward R)
    (layout : CallerLayout) (geometry : LayoutGeometry C R layout)
    (entry : FiatShamirGame.FramedHistory)
    (answers : FiatShamirGame.Coordinate → FiatShamirGame.Digest32) (claims : CallerClaims)
    (success : decodeCaller layout entry answers = some claims) :
    ClaimsValid C R (callerPlacements layout) claims := by
  cases parsed : entryTokens entry answers with
  | none => simp [decodeCaller, parsed] at success
  | some tokens =>
    apply interpretCaller_geometry C R columnDown ringDown layout geometry tokens claims
    simp only [decodeCaller, parsed] at success
    exact success

private def smokeBus : BusLayout :=
  ⟨[⟨2,false,[.column 0,.column 1,.column 0,.publicValue]⟩],
    [⟨2,false,[.column 1]⟩],[⟨2,2,0⟩],0⟩

private def smokePlacements : Array Placement :=
  (List.range 16).map (fun i => Placement.committed (64*i) 6) |>.toArray

private def smokeCpu : CpuLayout where
  bus := smokeBus
  tables := (List.range 11).map fun i =>
    ⟨if i = 0 then 2 else 3+i,2,if i = 0 then 2 else 1,i = 0,[0],[⟨0,1⟩]⟩
  placements := smokePlacements
  flock := [⟨64,7,6⟩]
  registers := [⟨128,[0,1]⟩]
  finalRegisterColumn := 15
  output := fun i => UInt64.ofNat (10+i.val)
  logInvRate := 0

private def smokeRec : RecLayout :=
  ⟨smokeBus,[(2,⟨2,2,0,[⟨0,1⟩]⟩)],smokePlacements,⟨64,7,6⟩,0⟩

private def smokeTokens (layout : CallerLayout) : List CallerToken :=
  (callerShape layout).flatMap fun event => match event with
  | .absorb bytes => List.replicate (bytes/24) (.sent 0)
  | .squeeze count => List.replicate (count/24) (.draw 0)
  | .nonce bits => [.nonce bits (fun _ => 0)]

private def smoke : IO Unit := do
  let C : Nat → Nat → Prop := fun column dimension => column < 16 ∧ dimension ≤ 6
  let R : Nat → Nat → Prop := fun offset dimension => offset ∈ [0,64,128] ∧ dimension ≤ 8
  unless decide (LayoutGeometry C R (.cpu smokeCpu)) &&
      decide (LayoutGeometry C R (.recursion smokeRec)) do
    throw (IO.userError "source-derived static geometry rejected")
  let cpuTokens := ((smokeTokens (.cpu smokeCpu)).zipIdx.map fun (token,index) =>
    if index < 11 then CallerToken.sent (E.ofK 2)
    else if index = 12 then CallerToken.sent (E.ofK (UInt64.ofNat (2^40))) else token)
  let some (cpu,rest) := sourceClaims (.cpu smokeCpu) cpuTokens |
    throw (IO.userError "actual CPU source parser rejected smoke")
  unless rest.isEmpty && cpu.points.size == 19 &&
      (cpu.families.map (fun ring => (ring.offset,ring.point.size))) == [(64,7),(0,2),(128,2)] do
    throw (IO.userError "CPU returned dimensions/provenance mismatch")
  let recTokens := smokeTokens (.recursion smokeRec)
  let some (rec,rest) := sourceClaims (.recursion smokeRec) recTokens |
    throw (IO.userError "actual recursion source parser rejected smoke")
  unless rest.isEmpty && rec.points.size == 4 &&
      (rec.families.map (fun ring => (ring.offset,ring.point.size))) == [(64,7)] do
    throw (IO.userError "recursion returned dimensions/provenance mismatch")
  let pointDimension := fun point => match point with
    | PointClaim.point _ point _ => point.size
    | .strided _ _ _ point _ => point.size
  unless cpu.points.toList.map pointDimension == List.replicate 14 2 ++ List.replicate 5 6 &&
      rec.points.toList.map pointDimension == List.replicate 4 2 do
    throw (IO.userError "bus/table/exit dimensions mismatch")
  unless !(decide (LayoutGeometry (fun _ d => d ≤ 1) R (.cpu smokeCpu))) do
    throw (IO.userError "insufficient public capacity unexpectedly passed static check")
  IO.println "caller geometry smoke: actual CPU 19 points + 3 rings; recursion 4 points + 1 ring; bus dedup, settled/summed tables, flock, producer, register, exit dimensions checked"

#eval smoke

open Lean in
run_cmd do
  let environment ← getEnv
  let mut count : Nat := 0
  for (name,info) in environment.constants.toList do
    if (`Whir.WHIRCallerGeometry).isPrefixOf name then
      match info with
      | .thmInfo _ =>
        for ax in (← collectAxioms name) do
          unless #[``propext,``Classical.choice,``Quot.sound].contains ax do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
      | .axiomInfo _ => throwError "new axiom {name}"
      | _ => pure ()
  logInfo m!"Audited {count} caller geometry theorems: only standard three axioms."

end Whir.WHIRCallerGeometry
