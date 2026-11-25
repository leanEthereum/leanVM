/-
  LeanVM.Guest.CoreMode.Fam.CarryIdx

  The nonzero facts' check (`Res.carryNzBy`) with each scan of a spine for a value read from an
  index of the spine's events by the values they name: equal to `Res.carryNzG`, faster in the kernel.
-/

module

public import LeanVM.Guest.CoreMode.Fam.CarryDefs
public import LeanVM.Guest.TrieFacts

/-!
# The nonzero facts' check, indexed

`carryNzG`'s searches (`nzOf` and its helpers) scan the whole spine of a body for the events naming
one value (`veq d v`, `veq T' T`, …), several times per level, so a long body's check walks its
spine thousands of times. They read the events to scan for `v` from `look v`, so the same check runs
over an index of the spine's events by the numbers of the values they name (`evIdx`, a trie of
lists, `evKeys`), each scan reading `evAt sp I v`, the events under `v.idx` (the whole spine for a
number past the trie's depth): `carryNzBy idxScan`. An event a scan accepts names `v`, so the
scan over `evAt` is the scan over the spine (`any_evAt`), two such scans give the same searches
(`ScanEq`, `nzOf_congr`), and the indexed check is the check (`carryNzBy_idxScan`).
`RangeOk (fun _ fn ↦ carryNzG fn)` follows from the indexed check's range (`rangeOk_carryNz`), which
is what the generated `Gen/CarryCallers*.lean` decide.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie)
open LeanVM.Guest.Check (getF setF)

@[expose] public section

/-! ## The index -/

/-- The numbers of the values an atom names. -/
def atomKeys : Atom → List ℕ
  | .const d _ => [d.idx]
  | .add d a b => [d.idx, a.idx, b.idx]
  | .mul d a b => [d.idx, a.idx, b.idx]
  | .copy d s => [d.idx, s.idx]
  | .load d p _ => [d.idx, p.idx]
  | .assertEq a b => [a.idx, b.idx]
  | .assertNe x i p => [x.idx, i.idx, p.idx]
  | .rangeCheck x y t1 t2 k => [x.idx, y.idx, t1.idx, t2.idx, k.idx]
  | .assertInK a b => [a.idx, b.idx]
  | .frameAddr p _ => [p.idx]
  | .touch t p => [t.idx, p.idx]
  | _ => []

/-- The numbers of the values an event names: an atom's, a call's words. -/
def evKeys : Ev → List ℕ
  | .atom a => atomKeys a
  | .call _ args rets => (args ++ rets).map V.idx
  | _ => []

/-- `e` added under key `k`, a key past the trie's depth left out. -/
noncomputable def addAt (e : Ev) (t : Trie (List Ev)) (k : ℕ) : Trie (List Ev) :=
  bif Nat.blt (k + 1) (2 ^ Exec.indexDepth) then setF (e :: (getF t k).getD []) Exec.indexDepth t k else t

/-- **The events of a spine by the numbers of the values they name.** -/
noncomputable def evIdx : List Ev → Trie (List Ev) → Trie (List Ev)
  | [], t => t
  | e :: sp, t => ((evKeys e).foldl (addAt e) t).seq fun t ↦ evIdx sp t

/-- The events to scan for `v`: those under its number, or the whole spine past the trie's depth. -/
noncomputable def evAt (sp : List Ev) (I : Trie (List Ev)) (v : V) : List Ev :=
  bif Nat.blt (v.idx + 1) (2 ^ Exec.indexDepth) then (getF I v.idx).getD [] else sp

/-- **The indexed scan** of a context: its events by value, indexed once. -/
noncomputable def idxScan (sp : List Ev) : V → List Ev := evAt sp (evIdx sp .nil)

end

public section

private theorem getF_setF' {a : List Ev} {t : Trie (List Ev)} {n m : ℕ} (h : n + 1 < 2 ^ Exec.indexDepth) :
    getF (setF a Exec.indexDepth t n) m = if m = n then some a else getF t m := by
  rw [Check.getF_eq, Check.setF_eq, Check.get_set_eq a _ t n m h, Check.getF_eq]

/-- What a key reads after adding `e` under keys `ks`. -/
private theorem mem_foldl_addAt (e : Ev) {m : ℕ} (hm : m + 1 < 2 ^ Exec.indexDepth) :
    ∀ (ks : List ℕ) (t : Trie (List Ev)) (x : Ev),
      x ∈ (getF (ks.foldl (addAt e) t) m).getD [] ↔ x ∈ (getF t m).getD [] ∨ (x = e ∧ m ∈ ks)
  | [], t, x => by simp
  | k :: ks, t, x => by
    rw [List.foldl_cons, mem_foldl_addAt e hm ks, addAt]
    cases hb : Nat.blt (k + 1) (2 ^ Exec.indexDepth)
    · have hmk : m ≠ k := by rintro rfl; rw [Nat.blt_eq.mpr hm] at hb; cases hb
      simp only [Bool.cond_false, List.mem_cons, hmk, false_or]
    · rw [Bool.cond_true, getF_setF' (Nat.blt_eq.mp hb)]
      by_cases hmk : m = k
      · subst hmk; simp only [↓reduceIte, Option.getD_some, List.mem_cons]; tauto
      · simp only [hmk, ↓reduceIte, List.mem_cons, false_or]

/-- **The index**: a key below the depth reads the events named by it, added to what it read. -/
theorem mem_evIdx {m : ℕ} (hm : m + 1 < 2 ^ Exec.indexDepth) :
    ∀ (sp : List Ev) (t : Trie (List Ev)) (x : Ev),
      x ∈ (getF (evIdx sp t) m).getD [] ↔ x ∈ (getF t m).getD [] ∨ (x ∈ sp ∧ m ∈ evKeys x)
  | [], t, x => by simp [evIdx]
  | e :: sp, t, x => by
    simp only [evIdx, Trie.seq_eq]
    rw [mem_evIdx hm sp, mem_foldl_addAt e hm, List.mem_cons]
    rcases eq_or_ne x e with rfl | hx
    · tauto
    · simp only [hx, false_and, or_false, false_or]

/-- **A scan for `v` over its events is the scan over the spine**, when every event the scan accepts
names `v`. -/
private theorem any_evAt {sp : List Ev} {v : V} {P : Ev → Bool} (hP : ∀ e, P e = true → v.idx ∈ evKeys e) :
    (evAt sp (evIdx sp .nil) v).any P = sp.any P := by
  unfold evAt
  cases hb : Nat.blt (v.idx + 1) (2 ^ Exec.indexDepth)
  · rfl
  · rw [Bool.cond_true, Bool.eq_iff_iff]
    simp only [List.any_eq_true, mem_evIdx (Nat.blt_eq.mp hb)]
    exact exists_congr fun e ↦ ⟨fun ⟨h, hp⟩ ↦ ⟨(h.resolve_left List.not_mem_nil).1, hp⟩,
      fun ⟨h, hp⟩ ↦ ⟨.inr ⟨h, hP e hp⟩, hp⟩⟩

end

/-! ## The indexed check is the check -/

section Congr

/-- **Two scans agree** on every search for a value by a predicate accepting only events naming it. -/
def ScanEq (l₁ l₂ : V → List Ev) : Prop :=
  ∀ v (P : Ev → Bool), (∀ e, P e = true → v.idx ∈ evKeys e) → (l₁ v).any P = (l₂ v).any P

variable {l₁ l₂ : V → List Ev}

/-- A search for `v` by predicates agreeing on every event, one accepting only events naming `v`. -/
private theorem ScanEq.any (h : ScanEq l₁ l₂) {v : V} {P Q : Ev → Bool} (hPQ : ∀ e, P e = Q e)
    (hQ : ∀ e, Q e = true → v.idx ∈ evKeys e) : (l₁ v).any P = (l₂ v).any Q := by
  rw [show P = Q from funext hPQ]; exact h v Q hQ

/-- The `simp only` set reading a scan's predicate on an event: `veq` as equal numbers, the event's keys. -/
local syntax "ev_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| ev_simp [$ls,*]) =>
    `(tactic| simp only [veq, evKeys, atomKeys, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Bool.false_eq_true, $ls,*] at *)

/-- An event a scan accepts names the value scanned for: by its constructors. -/
local syntax "ev_key" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| ev_key [$ls,*]) =>
    `(tactic| (intro e h; rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> ev_simp [$ls,*] <;> grind))

/-- Two searches' predicates agree on every event: by its constructors. -/
local syntax "ev_eq" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| ev_eq [$ls,*]) =>
    `(tactic| (intro e; rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> (try simp only [$ls,*]) <;> rfl))

private theorem pinNz_key (v : V) : ∀ e, pinNz v e = true → v.idx ∈ evKeys e
  | .atom a, h => by cases a <;> ev_simp [pinNz] <;> grind
  | .call g args rets, h => by
    simp only [pinNz, upAt, List.any_eq_true, Bool.and_eq_true] at h
    obtain ⟨c, -, hw, -⟩ := h
    split at hw
    next w hc =>
      simp only [veq, Bool.and_eq_true, beq_iff_eq] at hw
      exact List.mem_map.mpr ⟨w, List.mem_of_getElem? hc, hw.1⟩
    next => cases hw
  | .inK _, h | .skip .., h => by simp [pinNz] at h

theorem kIn0_congr (h : ScanEq l₁ l₂) (kv : List V) (v : V) : kIn0 l₁ kv v = kIn0 l₂ kv v := by
  rw [kIn0, kIn0, h v _ (by ev_key [pinIn])]

theorem kIn1_congr (h : ScanEq l₁ l₂) (kv : List V) (v : V) : kIn1 l₁ kv v = kIn1 l₂ kv v := by
  rw [kIn1, kIn1, kIn0_congr h]
  congr 1
  exact h.any (by ev_eq [kIn0_congr h]) (by ev_key [])

theorem kIn_congr (h : ScanEq l₁ l₂) (kv : List V) : ∀ n v, kIn l₁ kv n v = kIn l₂ kv n v
  | 0, v => kIn0_congr h kv v
  | n + 1, v => by
    rw [kIn, kIn, h v _ (by ev_key [pinIn])]
    congr 1
    exact h.any (by ev_eq [kIn_congr h kv n, kIn1_congr h]) (by ev_key [])

theorem tabAt_congr (h : ScanEq l₁ l₂) (nz : V → Bool) (T J : V) (off : ℕ) :
    tabAt l₁ nz T J off = tabAt l₂ nz T J off := by
  unfold tabAt
  refine h.any ?_ (by ev_key [])
  intro e
  rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> try rfl
  rename_i x _ _ _ k
  dsimp only
  congr 1
  refine h.any ?_ (by ev_key [])
  intro e
  rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> try rfl
  rename_i d c
  dsimp only
  congr 1
  cases powOf c with
  | none => rfl
  | some m =>
    dsimp only
    congr 2
    funext t
    exact h.any (by ev_eq []) (by ev_key [])

theorem tabNz_congr (h : ScanEq l₁ l₂) (nz : V → Bool) (p : V) (off : ℕ) :
    tabNz l₁ nz p off = tabNz l₂ nz p off := by
  rw [tabNz, tabNz]
  exact h.any (by ev_eq [tabAt_congr h]) (by ev_key [])

theorem nzOf_congr (h : ScanEq l₁ l₂) (kv : List V) : ∀ n v, nzOf l₁ kv n v = nzOf l₂ kv n v
  | 0, v => by rw [nzOf, nzOf, h v _ (pinNz_key v)]
  | n + 1, v => by
    rw [nzOf, nzOf, h v _ (pinNz_key v)]
    congr 1
    exact h.any (by ev_eq [funext (nzOf_congr h kv n), kIn_congr h, tabNz_congr h]) (by ev_key [])

end Congr

public section

/-- **The indexed check is the check.** -/
theorem carryNzBy_idxScan (fn : Fn) : carryNzBy idxScan fn = carryNzG fn := by
  have hn : ∀ sp, nzOf (idxScan sp) = nzOf fun _ ↦ sp := fun sp ↦
    funext fun kv ↦ funext fun n ↦ funext (nzOf_congr (fun _ _ hP ↦ any_evAt hP) kv n)
  have hs : siteNz idxScan = siteNz fun sp _ ↦ sp := by
    funext kv sp f args; simp only [siteNz, hn]
  have hst : nzStmt idxScan = nzStmt fun sp _ ↦ sp := by
    funext kv sp s
    cases s with
    | atom a =>
      cases a with
      | hint hh =>
        cases hh with
        | allocDyn _ s => simp only [nzStmt, hn]
        | _ => rfl
      | _ => rfl
    | call | callIf | dispatch => simp only [nzStmt, hs]
    | _ => rfl
  have hr : retNz idxScan = retNz fun sp _ ↦ sp := by
    funext j sp s; cases s <;> simp only [retNz, hn]
  have hu : upChk idxScan = upChk fun sp _ ↦ sp := by
    funext fn i; simp only [upChk, hn, hr]
  rw [carryNzG, carryNzBy, carryNzBy, hst, hu]

/-- **The nonzero facts' check of a range, from the indexed check's.** -/
theorem rangeOk_carryNz {a n : ℕ} (h : RangeOk (fun _ fn ↦ carryNzBy idxScan fn) a n) :
    RangeOk (fun _ fn ↦ carryNzG fn) a n := by
  simpa only [carryNzBy_idxScan] using h

end

end LeanVM.Guest.Res
