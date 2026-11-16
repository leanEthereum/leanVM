/-
  LeanVM.Guest.Backend.Guest.Cpl.At

  The guest's placed functions, entry by entry, and the per-function test the kernel evaluates on
  them for the completeness instance.
-/

module

public import LeanVM.Guest.Backend.Guest.Cpl.Static
public import LeanVM.Guest.Backend.Guest.Piece.Layout
public import LeanVM.Guest.Deployed.Data
public import LeanVM.Cost.Decoder.GuestPlaces

/-!
# The guest's placed functions

`placedAt i` is entry `i` of the back end's input (`guestTraced`, function `i + 1`) placed from the
jump tables the entries before it leave, as the pieces place it (`placedLocsAt`'s placement);
`fsWant i` the frame size the completeness instance gives it, the back end's table
(`Deployed.Data`): `mainCells` for `main` (its frame proper, without the jump tables), else
`max 2` of its frame size.

`cplOkWith i pf` is the per-function test of entry `i` placed as `pf`: the static test
(`staticOk`) against `fsWant i`; the placement-side hypotheses (`Complete.scopedB`,
`Complete.noSelfCallB`, `Complete.tmpsApartB`, `Complete.alL`); the counts: `Complete.pmaxP` is
the table's `pmax` and `Complete.armsP` its `arms`, keyed (counting arms apart) for the table's
`armFn`, the arms' selectors distinct; and the places: the decoder's table of place codes
(`Cost.Decoder.guestPlacesList`, `PlaceCode`) is the code of each value's place (`placesOk`).
`cplOkAt i` runs the placement; `CplOkAll` says the test passes for every entry, which the kernel
decides for runs of entries (`Eval/`).
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Guest LeanVM.Guest.Core GuestPiece

@[expose] public section

/-- **Entry `i` placed** from the jump tables the entries before it leave; `none` if its
placement fails. -/
noncomputable def placedAt (i : ℕ) : Option Placed :=
  match placeFn loopsG sigsG (tablesAt outsG i) (guestTraced.getD i default) with
  | .ok r => some r.1
  | .error _ => none

/-- The frame size of entry `i` in the completeness instance. -/
def fsWant (i : ℕ) : ℕ :=
  if i = 0 then Deployed.Data.mainCells else max 2 (Deployed.Data.frameSizes.getD (i + 1) 0)

/-- The separately counted arms of function `i + 1` (`Deployed.Data.arms`). -/
def armsOf (i : ℕ) : List (ℕ × List (List ℕ)) := listElementOrDefault Deployed.Data.arms (i + 1) []

/-- Whether function `i + 1`'s arms are counted separately: it is `Deployed.Data.armFn`. -/
def keyedOf (i : ℕ) : Bool := i + 1 == Deployed.Data.armFn

/-- Function `i + 1`'s place codes (`Cost.Decoder.guestPlacesList`). -/
def placesRow (i : ℕ) : List ℕ := Cost.Decoder.guestPlacesList.getD (i + 1) []

/-- **The code of a place** in the decoder's table (`placeWith`): `0` for no place, the cell `n`
as `n`, the cell `n` shifted by `g^e` as `n + 2^20 * (e + 1)`; none for cell `0` or a cell past
`2^20`. -/
def codeOf : Option Loc → Option ℕ
  | none => some 0
  | some (.cell n) => if 0 < n ∧ n < 2 ^ 20 then some n else none
  | some (.shifted n e) => if n < 2 ^ 20 then some (n + 2 ^ 20 * (e + 1)) else none

/-- Every key of the trie of a value map is a value `⟨[], 0, k⟩`. -/
noncomputable def keysNumbered (t : Trie (List (V × Loc))) : Bool :=
  Trie.rec (motive := fun _ => Bool) true
    (fun b _ _ bl br =>
      (b.all fun kvs => kvs.all fun kv => kv.1.path.isEmpty && kv.1.tag == 0) && bl && br) t

/-- From value `⟨[], 0, k⟩` on, each value's place has the next code of `row`. -/
def codesFrom (locs : VMap Loc) : ℕ → List ℕ → Bool
  | _, [] => true
  | k, c :: cs => codeOf locs[(⟨[], 0, k⟩ : V)]? == some c && codesFrom locs (k + 1) cs

/-- Every value a core function names is `⟨[], 0, k⟩` for some `k` below `n`. -/
def valsBelow (f : Fn) (n : ℕ) : Bool :=
  (f.params ++ Stmt.valsList f.body).all fun v => v.path.isEmpty && v.tag == 0 && Nat.blt v.idx n

/-- **The places are the row's codes**: the values with a place are `⟨[], 0, k⟩`, value `k`'s
place has code `row[k]` for `k` below the row's length, and the values the core function `f`
names are below it. -/
noncomputable def placesOk (f : Fn) (locs : VMap Loc) (row : List ℕ) : Bool :=
  keysNumbered locs.t && codesFrom locs 0 row && valsBelow f row.length

/-- **The per-function test** of entry `i` on its placed function `pf`. -/
noncomputable def cplOkWith (i : ℕ) (pf : Placed) : Bool :=
  staticOk loopsG (guestTraced.getD i default) pf (fsWant i) &&
    Complete.scopedB (guestTraced.getD i default) &&
    Complete.noSelfCallB (guestTraced.getD i default) &&
    Complete.tmpsApartB (guestTraced.getD i default) pf &&
    Complete.alL pf.fn.body (guestTraced.getD i default).core.body &&
    natsDistinct ((Complete.armsP (keyedOf i) (guestTraced.getD i default) pf).map (·.1)) &&
    decide (Complete.ofCnt (Complete.pmaxP (keyedOf i) pf) = Deployed.Data.pmax.getD (i + 1) []) &&
    decide (Complete.armsP (keyedOf i) (guestTraced.getD i default) pf = armsOf i) &&
    placesOk (guestTraced.getD i default).core pf.locs (placesRow i)

/-- **The per-function test of entry `i`**, its placement run. -/
noncomputable def cplOkAt (i : ℕ) : Bool :=
  match placedAt i with
  | some pf => cplOkWith i pf
  | none => false

theorem placedAt_of {i : ℕ} {pf : Placed} {t' : Tables}
    (h : placeFn loopsG sigsG (tablesAt outsG i) (guestTraced.getD i default) = .ok (pf, t')) :
    placedAt i = some pf := by
  unfold placedAt
  rw [h]

theorem cplOkAt_of {i : ℕ} {pf : Placed} (hp : placedAt i = some pf) (h : cplOkWith i pf = true) :
    cplOkAt i = true := by
  unfold cplOkAt
  rw [hp]
  exact h

theorem cplOkWith_of {i : ℕ} {pf : Placed} (hp : placedAt i = some pf) (h : cplOkAt i = true) :
    cplOkWith i pf = true := by
  unfold cplOkAt at h
  rw [hp] at h
  exact h

/-- **The per-function test passes for every entry** of the guest. -/
def CplOkAll : Prop := ∀ i < core_count%, cplOkAt i = true

/-- **The places are the row's codes**: a value with a place is `⟨[], 0, k⟩`, value `⟨[], 0, k⟩`'s
place has code `row[k]` (`codeOf`) for `k` below the row's length, and every value the core
function `f` names is `⟨[], 0, k⟩` for such a `k`. -/
structure PlacesAre (f : Fn) (locs : VMap Loc) (row : List ℕ) : Prop where
  keys : ∀ (v : V) (l : Loc), locs[v]? = some l → v = ⟨[], 0, v.idx⟩
  codes : ∀ k (hk : k < row.length), codeOf locs[(⟨[], 0, k⟩ : V)]? = some row[k]
  core : ∀ v ∈ f.params ++ Stmt.valsList f.body, v = ⟨[], 0, v.idx⟩ ∧ v.idx < row.length

theorem keysNumbered_get : ∀ {t : Trie (List (V × Loc))} {k : ℕ} {bs : List (V × Loc)},
    keysNumbered t = true → t.get k = some bs → ∀ kv ∈ bs, kv.1.path.isEmpty = true ∧ kv.1.tag = 0
  | .nil, _, _, _, hg => by cases hg
  | .node b l r, k, bs, h, hg => by
    change ((b.all fun kvs => kvs.all fun kv => kv.1.path.isEmpty && kv.1.tag == 0) &&
      keysNumbered l) && keysNumbered r = true at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hb, hl⟩, hr⟩ := h
    cases k with
    | zero =>
      change b = some bs at hg
      subst hg
      intro kv hkv
      have := List.all_eq_true.mp hb kv hkv
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact this
    | succ m =>
      change Bool.rec (r.get (Nat.div m 2)) (l.get (Nat.div m 2)) (Nat.beq (Nat.mod m 2) 0) =
        some bs at hg
      generalize Nat.beq (Nat.mod m 2) 0 = c at hg
      cases c
      · exact keysNumbered_get hr hg
      · exact keysNumbered_get hl hg

theorem lookup_mem {v : V} {l : Loc} : ∀ {bs : List (V × Loc)}, bs.lookup v = some l → (v, l) ∈ bs
  | [], h => by cases h
  | (k, a) :: bs, h => by
    rw [List.lookup_cons] at h
    by_cases e : v = k
    · subst e
      simp only [beq_self_eq_true] at h
      cases h
      exact List.mem_cons_self
    · simp only [beq_false_of_ne e] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem codesFrom_spec {locs : VMap Loc} : ∀ {k₀ : ℕ} {row : List ℕ}, codesFrom locs k₀ row = true →
    ∀ k (hk : k < row.length), codeOf locs[(⟨[], 0, k₀ + k⟩ : V)]? = some row[k]
  | _, [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | k₀, c :: cs, h, k, hk => by
    simp only [codesFrom, Bool.and_eq_true, beq_iff_eq] at h
    cases k with
    | zero => exact h.1
    | succ k =>
      have := codesFrom_spec h.2 k (by simpa using hk)
      rw [show k₀ + 1 + k = k₀ + (k + 1) by omega] at this
      exact this

theorem placesOk_spec {f : Fn} {locs : VMap Loc} {row : List ℕ} (h : placesOk f locs row = true) :
    PlacesAre f locs row := by
  simp only [placesOk, valsBelow, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Nat.blt_eq,
    List.isEmpty_iff] at h
  obtain ⟨⟨hk, hc⟩, hv⟩ := h
  refine ⟨fun v l hl => ?_, fun k hk => by simpa using codesFrom_spec hc k hk, fun v hm => ?_⟩
  · rw [KMap.getElem?_eq, KMap.get?] at hl
    cases hb : locs.t.get (Keyed.key v) with
    | none => rw [hb] at hl; cases hl
    | some bs =>
      rw [hb, Option.getD_some] at hl
      obtain ⟨hp, ht⟩ := keysNumbered_get hk hb (v, l) (lookup_mem hl)
      obtain ⟨p, t, i⟩ := v
      simp only [List.isEmpty_iff] at hp ht
      subst hp ht
      rfl
  · obtain ⟨⟨hp, ht⟩, hi⟩ := hv v hm
    obtain ⟨p, t, i⟩ := v
    change p = [] at hp
    change t = 0 at ht
    change i < row.length at hi
    subst hp ht
    exact ⟨rfl, hi⟩

/-- **What the per-function test says.** -/
structure CplFacts (i : ℕ) (pf : Placed) : Prop where
  sfacts : StaticFacts loopsG (guestTraced.getD i default) pf (fsWant i)
  isScoped : Complete.Scoped (guestTraced.getD i default)
  noSelf : Complete.NoSelfCall (guestTraced.getD i default)
  apart : Complete.TmpsApart (guestTraced.getD i default) pf
  aligned : Complete.Aligned (guestTraced.getD i default) pf
  armsNodup : ((Complete.armsP (keyedOf i) (guestTraced.getD i default) pf).map (·.1)).Nodup
  pmax : Complete.ofCnt (Complete.pmaxP (keyedOf i) pf) = Deployed.Data.pmax.getD (i + 1) []
  arms : Complete.armsP (keyedOf i) (guestTraced.getD i default) pf = armsOf i
  places : PlacesAre (guestTraced.getD i default).core pf.locs (placesRow i)

theorem cplOkWith_spec {i : ℕ} {pf : Placed} (h : cplOkWith i pf = true) : CplFacts i pf := by
  unfold cplOkWith at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs, hsc⟩, hns⟩, hta⟩, hal⟩, hnd⟩, hpm⟩, har⟩, hpl⟩ := h
  exact ⟨staticOk_spec hs, hsc, hns, hta, hal, natsDistinct_nodup hnd, hpm, har, placesOk_spec hpl⟩

end
end LeanVM.Guest.Backend.Cpl
