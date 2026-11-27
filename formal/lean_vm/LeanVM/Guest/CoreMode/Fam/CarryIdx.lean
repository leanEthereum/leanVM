/-
  LeanVM.Guest.CoreMode.Fam.CarryIdx

  The nonzero facts' check (`Res.carryNzG`) with each scan of a spine for a value read from an
  index of the spine's events by the values they name: equal to it, faster in the kernel.
-/

module

public import LeanVM.Guest.CoreMode.Fam.CarrySplit
public import LeanVM.Guest.TrieFacts

/-!
# The nonzero facts' check, indexed

`nzOf` and its helpers scan the whole spine of a body for the events naming one value (`veq d v`,
`veq T' T`, …), several times per level of their search, so a long body's check walks its spine
thousands of times. Here the spine's events are indexed once by the numbers of the values they
name (`evIdx`, a trie of lists, `evKeys`), and each scan for a value `v` reads `evAt sp I v`, the
events under `v.idx` (the whole spine for a number past the trie's depth). An event a scan accepts
names `v`, so the scan over `evAt` is the scan over the spine (`any_evAt`), and the indexed check
is the check (`carryNzGI_eq`). `RangeOk (fun _ fn ↦ carryNzG fn)` follows from the indexed check's
range (`rangeOk_carryNz`), and a slice of a body's pass (`allBSlice`, `CarrySplit.lean`) from the
indexed pass's slice (`allBSlice_nzStmtI`): what the generated `Gen/CarryCallers*.lean` decide.
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
    rw [List.foldl_cons, mem_foldl_addAt e hm ks]
    unfold addAt
    by_cases hk : k + 1 < 2 ^ Exec.indexDepth
    · have hb : Nat.blt (k + 1) (2 ^ Exec.indexDepth) = true := Nat.blt_eq.mpr hk
      rw [hb, Bool.cond_true, getF_setF' hk]
      by_cases hmk : m = k
      · subst hmk; simp only [↓reduceIte, Option.getD_some, List.mem_cons]; tauto
      · simp only [hmk, ↓reduceIte, List.mem_cons, false_or]
    · have hb : Nat.blt (k + 1) (2 ^ Exec.indexDepth) = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact hk
      have hmk : m ≠ k := fun h ↦ hk (h ▸ hm)
      rw [hb, Bool.cond_false]
      simp only [List.mem_cons, hmk, false_or]

/-- **The index**: a key below the depth reads the events named by it, added to what it read. -/
theorem mem_evIdx {m : ℕ} (hm : m + 1 < 2 ^ Exec.indexDepth) :
    ∀ (sp : List Ev) (t : Trie (List Ev)) (x : Ev),
      x ∈ (getF (evIdx sp t) m).getD [] ↔ x ∈ (getF t m).getD [] ∨ (x ∈ sp ∧ m ∈ evKeys x)
  | [], t, x => by simp [evIdx]
  | e :: sp, t, x => by
    simp only [evIdx, Trie.seq_eq]
    rw [mem_evIdx hm sp, mem_foldl_addAt e hm]
    constructor
    · rintro ((h | ⟨rfl, h⟩) | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_cons_self, h⟩
      · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp h1 with rfl | h1
        · exact Or.inl (Or.inr ⟨rfl, h2⟩)
        · exact Or.inr ⟨h1, h2⟩

/-- **A scan for `v` over its events is the scan over the spine**, when every event the scan accepts
names `v`. -/
theorem any_evAt {sp : List Ev} {v : V} {P : Ev → Bool} (hP : ∀ e, P e = true → v.idx ∈ evKeys e) :
    (evAt sp (evIdx sp .nil) v).any P = sp.any P := by
  unfold evAt
  by_cases hk : v.idx + 1 < 2 ^ Exec.indexDepth
  · rw [Nat.blt_eq.mpr hk, Bool.cond_true]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨e, he, hp⟩
      rcases (mem_evIdx hk sp .nil e).mp he with h | ⟨h, -⟩
      · simp [getF_nil'] at h
      · exact ⟨e, h, hp⟩
    · rintro ⟨e, he, hp⟩
      exact ⟨e, (mem_evIdx hk sp .nil e).mpr (Or.inr ⟨he, hP e hp⟩), hp⟩
  · have hb : Nat.blt (v.idx + 1) (2 ^ Exec.indexDepth) = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact hk
    rw [hb, Bool.cond_false]
where getF_nil' (k : ℕ) : getF (Trie.nil : Trie (List Ev)) k = none := rfl

end

/-! ## The check, its scans indexed -/

section Defs

variable (sp : List Ev) (I : Trie (List Ev))

@[expose] public section

/-- `kIn0`, indexed. -/
noncomputable def kIn0I (kv : List V) (v : V) : Bool := kv.any (veq · v) || (evAt sp I v).any (pinIn v)

/-- `kIn1`, indexed. -/
noncomputable def kIn1I (kv : List V) (v : V) : Bool :=
  kIn0I sp I kv v || (evAt sp I v).any fun
    | .atom (.mul d a b) => veq d v && kIn0I sp I kv a && kIn0I sp I kv b
    | .atom (.add d a b) => veq d v && kIn0I sp I kv a && kIn0I sp I kv b
    | _ => false

/-- `kIn`, indexed. -/
noncomputable def kInI (kv : List V) : ℕ → V → Bool
  | 0, v => kv.any (veq · v) || (evAt sp I v).any (pinIn v)
  | n + 1, v => kv.any (veq · v) || (evAt sp I v).any (pinIn v) || (evAt sp I v).any fun
      | .atom (.mul d a b) => veq d v && kInI kv n a && kInI kv n b
      | .atom (.add d a b) => veq d v && kIn1I sp I kv a && kIn1I sp I kv b
      | _ => false

/-- `tabAt`, indexed. -/
noncomputable def tabAtI (nz : V → Bool) (T J : V) (off : ℕ) : Bool :=
  (evAt sp I J).any fun
    | .atom (.rangeCheck x _ _ _ k) => veq x J && (evAt sp I k).any fun
        | .atom (.const d c) => veq d k && match powOf c with
            | some m => decide (m < 2 ^ 28) && (List.range (m + 1)).all fun t => (evAt sp I T).any fun
                | .atom (.load w T' o) => veq T' T && o == t + off && nz w
                | _ => false
            | none => false
        | _ => false
    | _ => false

/-- `tabNz`, indexed. -/
noncomputable def tabNzI (nz : V → Bool) (p : V) (off : ℕ) : Bool :=
  (evAt sp I p).any fun
    | .atom (.mul q a b) => veq q p && (tabAtI sp I nz a b off || tabAtI sp I nz b a off)
    | _ => false

/-- `nzOf`, indexed. -/
noncomputable def nzOfI (kv : List V) : ℕ → V → Bool
  | 0, v => kv.any (veq · v) || (evAt sp I v).any (pinNz v)
  | n + 1, v => kv.any (veq · v) || (evAt sp I v).any (pinNz v) || (evAt sp I v).any fun
      | .atom (.mul d a b) => (veq d v && nzOfI kv n a && nzOfI kv n b) ||
          (veq b v && kInI sp I kv kDepth a && nzOfI kv n d) ||
          (veq a v && kInI sp I kv kDepth b && nzOfI kv n d)
      | .atom (.copy d s) => (veq d v && nzOfI kv n s) || (veq s v && nzOfI kv n d)
      | .atom (.assertEq d s) => (veq d v && nzOfI kv n s) || (veq s v && nzOfI kv n d)
      | .atom (.load d p off) => veq d v && tabNzI sp I (nzOfI kv n) p off
      | _ => false


/-- `siteNz`, indexed. -/
noncomputable def siteNzI (kv : List V) (sp : List Ev) (f : String) (args : List V) : Bool :=
  carriedNz.all fun c => c.1 != f || match args[c.2]? with
    | some a => nzOfI sp (evIdx sp .nil) kv nzDepth a
    | none => false

/-- `nzStmt`, indexed. -/
noncomputable def nzStmtI (kv : List V) (sp : List Ev) : Stmt → Bool
  | .atom (.hint (.allocDyn _ s)) => nzOfI sp (evIdx sp .nil) kv nzDepth s
  | .call f args _ => siteNzI kv sp f args
  | .callIf _ f args => siteNzI kv sp f args
  | .dispatch _ fs args _ => fs.all fun f => siteNzI kv sp f args
  | _ => true

/-- `retNz`, indexed. -/
noncomputable def retNzI (j : ℕ) (sp : List Ev) : Stmt → Bool
  | .ret vs => match vs[j]? with
    | some v => nzOfI sp (evIdx sp .nil) [] nzDepth v
    | none => false
  | _ => true

/-- `upChk`, indexed. -/
noncomputable def upChkI (fn : Fn) (i : ℕ) : Bool :=
  match fn.params[i]? with
  | some p => nzOfI (spineE fn.body) (evIdx (spineE fn.body) .nil) [] nzDepth p
  | none => allB (fun sp s => retNzI (i - fn.params.length) sp s) fn.body (spineE fn.body)

/-- **`carryNzG`, its scans indexed.** -/
noncomputable def carryNzGI (fn : Fn) : Bool :=
  allB (nzStmtI (kvNz fn)) fn.body (spineE fn.body) && nzUp.all (fun c => c.1 != fn.name || upChkI fn c.2) &&
    ownNz.all fun c => c.1 != fn.name || ownChk fn (V.n c.2)

end

end Defs

/-! ## The indexed check is the check -/

public section

variable {sp : List Ev}

/-- A scan for `v` over its events, by a predicate equal to one that accepts only events naming `v`, is
the scan over the spine. -/
private theorem any_evAt_congr {v : V} {P Q : Ev → Bool} (hPQ : ∀ e, P e = Q e)
    (hQ : ∀ e, Q e = true → v.idx ∈ evKeys e) : (evAt sp (evIdx sp .nil) v).any P = sp.any Q := by
  rw [show P = Q from funext hPQ]; exact any_evAt hQ

/-- An event a scan accepts names the value scanned for: by its constructors, `veq` read as equal numbers. -/
local syntax "ev_key" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ev_key) => `(tactic| (
    intro e h
    rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;>
      simp only [veq, evKeys, atomKeys, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Bool.false_eq_true] at h ⊢ <;> grind))
  | `(tactic| ev_key [$ls,*]) => `(tactic| (
    intro e h
    rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;>
      simp only [veq, evKeys, atomKeys, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Bool.false_eq_true, $ls,*] at h ⊢ <;> grind))

/-- The indexed predicate and the plain one agree on every event: by its constructors. -/
local syntax "ev_eq" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ev_eq) => `(tactic| (
    intro e
    rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> rfl))
  | `(tactic| ev_eq [$ls,*]) => `(tactic| (
    intro e
    rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> (try simp only [$ls,*]) <;> rfl))

private theorem pinNz_key (v : V) : ∀ e, pinNz v e = true → v.idx ∈ evKeys e := by
  intro e h
  rcases e with ⟨a⟩ | _ | ⟨g, args, rets⟩ | _
  · cases a <;>
      simp only [pinNz, veq, evKeys, atomKeys, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
        List.mem_cons, List.not_mem_nil, or_false, Bool.false_eq_true] at h ⊢ <;> grind
  · simp [pinNz] at h
  · simp only [pinNz, upAt, List.any_eq_true, Bool.and_eq_true] at h
    obtain ⟨c, -, hw, -⟩ := h
    revert hw
    cases hc : (args ++ rets)[c.2]? with
    | none => simp
    | some w =>
      intro hw
      simp only [veq, Bool.and_eq_true, beq_iff_eq] at hw
      exact List.mem_map.mpr ⟨w, List.mem_of_getElem? hc, hw.1⟩
  · simp [pinNz] at h

theorem kIn0I_eq (kv : List V) (v : V) : kIn0I sp (evIdx sp .nil) kv v = kIn0 kv sp v := by
  rw [kIn0I, kIn0, any_evAt (by ev_key [pinIn])]

theorem kIn1I_eq (kv : List V) (v : V) : kIn1I sp (evIdx sp .nil) kv v = kIn1 kv sp v := by
  rw [kIn1I, kIn1, kIn0I_eq]
  congr 1
  exact any_evAt_congr (by ev_eq [kIn0I_eq]) (by ev_key)

theorem kInI_eq (kv : List V) : ∀ n v, kInI sp (evIdx sp .nil) kv n v = kIn kv sp n v
  | 0, v => by rw [kInI, kIn, any_evAt (by ev_key [pinIn])]
  | n + 1, v => by
    rw [kInI, kIn, any_evAt (by ev_key [pinIn])]
    congr 1
    exact any_evAt_congr (by ev_eq [kInI_eq kv n, kIn1I_eq]) (by ev_key)

theorem tabAtI_eq (nz : V → Bool) (T J : V) (off : ℕ) :
    tabAtI sp (evIdx sp .nil) nz T J off = tabAt sp nz T J off := by
  unfold tabAtI tabAt
  refine any_evAt_congr ?_ ?_
  swap
  · ev_key
  intro e
  rcases e with ⟨a⟩ | _ | _ | _ <;> (try cases a) <;> try rfl
  rename_i x _ _ _ k
  dsimp only
  congr 1
  refine any_evAt_congr ?_ ?_
  swap
  · ev_key
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
    refine any_evAt_congr ?_ ?_
    · ev_eq
    · ev_key

theorem tabNzI_eq (nz : V → Bool) (p : V) (off : ℕ) :
    tabNzI sp (evIdx sp .nil) nz p off = tabNz sp nz p off := by
  rw [tabNzI, tabNz]
  exact any_evAt_congr (by ev_eq [tabAtI_eq]) (by ev_key)

theorem nzOfI_eq (kv : List V) : ∀ n v, nzOfI sp (evIdx sp .nil) kv n v = nzOf kv sp n v
  | 0, v => by rw [nzOfI, nzOf, any_evAt (pinNz_key v)]
  | n + 1, v => by
    have ih : nzOfI sp (evIdx sp .nil) kv n = nzOf kv sp n := funext (nzOfI_eq kv n)
    rw [nzOfI, nzOf, any_evAt (pinNz_key v)]
    congr 1
    exact any_evAt_congr (by ev_eq [ih, kInI_eq, tabNzI_eq]) (by ev_key)

theorem nzStmtI_eq (kv : List V) (sp : List Ev) (s : Stmt) : nzStmtI kv sp s = nzStmt kv sp s := by
  have h : ∀ f args, siteNzI kv sp f args = siteNz kv sp f args := fun f args ↦ by
    simp only [siteNzI, siteNz, nzOfI_eq]; rfl
  cases s with
  | atom a =>
    cases a with
    | hint hh =>
      cases hh with
      | allocDyn _ s => exact nzOfI_eq kv nzDepth s
      | _ => rfl
    | _ => rfl
  | call f args _ => exact h f args
  | callIf _ f args => exact h f args
  | dispatch _ fs args _ => simp only [nzStmtI, nzStmt, h]
  | _ => rfl

theorem carryNzGI_eq (fn : Fn) : carryNzGI fn = carryNzG fn := by
  have hs : nzStmtI (kvNz fn) = nzStmt (kvNz fn) := funext fun sp ↦ funext (nzStmtI_eq _ sp)
  have hr : ∀ j, (fun sp s ↦ retNzI j sp s) = fun sp s ↦ retNz j sp s := fun j ↦ funext fun sp ↦ funext fun s ↦ by
    cases s <;> try rfl
    rename_i vs
    simp only [retNzI, retNz]
    cases vs[j]? <;> simp [nzOfI_eq]
  have hu : ∀ i, upChkI fn i = upChk fn i := fun i ↦ by
    unfold upChkI upChk
    cases fn.params[i]? <;> simp only [nzOfI_eq, hr]
  simp only [carryNzGI, carryNzG, hs, hu]

/-- **The nonzero facts' check of a range, from the indexed check's.** -/
theorem rangeOk_carryNz {a n : ℕ} (h : RangeOk (fun _ fn ↦ carryNzGI fn) a n) :
    RangeOk (fun _ fn ↦ carryNzG fn) a n := by
  simpa only [carryNzGI_eq] using h

/-- **A slice of the nonzero facts' pass over a body, from the indexed pass's.** -/
theorem allBSlice_nzStmtI {kv : List V} {ss : List Stmt} {ctx : List Ev} {a b : ℕ}
    (h : allBSlice (nzStmtI kv) ss ctx a b = true) : allBSlice (nzStmt kv) ss ctx a b = true := by
  have hs : nzStmtI kv = nzStmt kv := funext fun sp ↦ funext (nzStmtI_eq kv sp)
  rwa [hs] at h

end

end LeanVM.Guest.Res
