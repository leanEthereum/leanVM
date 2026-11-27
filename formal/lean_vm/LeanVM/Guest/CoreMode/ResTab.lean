/-
  LeanVM.Guest.CoreMode.ResTab

  Tries the route's checks read instead of scanning lists, each built once per kernel evaluation: a body's range checks
  and constants by value number, so that a residual a range check bounds (`Res.rcBound`) is two lookups, not two scans
  of the body; and a function's values' cells (`B2C.cellJ`), so that a pointer's cell is a lookup, not a walk of the
  certificate's cells. A residual's hint names the family that holds (`resFamHint`), `resFam` over the atoms indexed
  by value (`ResIx.lean`).
-/

module

public import LeanVM.Guest.CoreMode.Route
public import LeanVM.Guest.CoreMode.ResIx
public import LeanVM.Guest.CoreMode.ResSplit
public import LeanVM.Guest.TrieFacts

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.Exec (Trie)
open LeanVM.Guest.Check (getF setF)

@[expose] public section

/-- Each key's first entry among the atoms `l` (`f`), keys below the tries' depth, over `t`. -/
noncomputable def firstGo {β : Type} (f : Atom → Option (ℕ × β)) : List Atom → Trie β → Trie β
  | [], t => t
  | a :: l, t => match f a with
    | some (i, b) => bif Nat.blt (i + 1) (2 ^ Exec.indexDepth) then
        match getF t i with
        | some _ => firstGo f l t
        | none => (setF b Exec.indexDepth t i).seq fun t ↦ firstGo f l t
      else firstGo f l t
    | none => firstGo f l t

/-- `a` is the first atom of `l` that `f` gives key `x`, with `b`. -/
def FirstIn {β : Type} (f : Atom → Option (ℕ × β)) (x : ℕ) (b : β) (l : List Atom) : Prop :=
  ∃ pre a post, l = pre ++ a :: post ∧ f a = some (x, b) ∧ ∀ a' ∈ pre, ∀ b', f a' ≠ some (x, b')

theorem FirstIn.cons {β : Type} {f : Atom → Option (ℕ × β)} {x : ℕ} {b : β} {a : Atom} {l : List Atom}
    (h : FirstIn f x b l) (ha : ∀ b', f a ≠ some (x, b')) : FirstIn f x b (a :: l) := by
  obtain ⟨pre, a', post, rfl, h1, h2⟩ := h
  refine ⟨a :: pre, a', post, rfl, h1, fun a'' ha'' b' ↦ ?_⟩
  rcases List.mem_cons.1 ha'' with rfl | ha''
  · exact ha b'
  · exact h2 a'' ha'' b'

theorem firstGo_spec {β : Type} {f : Atom → Option (ℕ × β)} {x : ℕ} {b : β} (hx : x + 1 < 2 ^ Exec.indexDepth) :
    ∀ (l : List Atom) (t : Trie β), getF (firstGo f l t) x = some b →
      getF t x = some b ∨ (getF t x = none ∧ FirstIn f x b l)
  | [], t, h => Or.inl h
  | a :: l, t, h => by
    unfold firstGo at h
    cases hf : f a with
    | none =>
      rw [hf] at h
      rcases firstGo_spec hx l t h with h | ⟨h0, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨h0, h.cons fun b' e ↦ by rw [hf] at e; cases e⟩
    | some p =>
      obtain ⟨i, c⟩ := p
      rw [hf] at h
      simp only at h
      have hne : ∀ (h0 : x ≠ i) b', f a ≠ some (x, b') := fun h0 b' e ↦ by
        rw [hf] at e; simp only [Option.some.injEq, Prod.mk.injEq] at e; exact h0 e.1.symm
      cases hb : Nat.blt (i + 1) (2 ^ Exec.indexDepth)
      · rw [hb, Bool.cond_false] at h
        have hix : x ≠ i := fun e ↦ by
          subst e
          have : Nat.blt (x + 1) (2 ^ Exec.indexDepth) = true := by rw [Nat.blt_eq]; exact hx
          rw [this] at hb; cases hb
        rcases firstGo_spec hx l t h with h | ⟨h0, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨h0, h.cons (hne hix)⟩
      · rw [hb, Bool.cond_true] at h
        have hi : i + 1 < 2 ^ Exec.indexDepth := by rw [← Nat.blt_eq]; exact hb
        cases ht : getF t i with
        | some _ =>
          rw [ht] at h
          rcases firstGo_spec hx l t h with h | ⟨h0, h⟩
          · exact Or.inl h
          · have hix : x ≠ i := fun e ↦ by subst e; rw [ht] at h0; cases h0
            exact Or.inr ⟨h0, h.cons (hne hix)⟩
        | none =>
          rw [ht, Exec.Trie.seq_eq] at h
          have hs : getF (setF c Exec.indexDepth t i) x = if x = i then some c else getF t x := by
            rw [Check.getF_eq, Check.setF_eq, Check.get_set_eq c _ t i x hi, ← Check.getF_eq]
          rcases firstGo_spec hx l _ h with h | ⟨h0, h⟩
          · rw [hs] at h
            by_cases hix : x = i
            · subst hix
              simp only [↓reduceIte, Option.some.injEq] at h
              subst h
              exact Or.inr ⟨ht, [], a, l, rfl, hf, fun _ h ↦ absurd h List.not_mem_nil⟩
            · simp only [hix, ↓reduceIte] at h
              exact Or.inl h
          · rw [hs] at h0
            by_cases hix : x = i
            · subst hix; simp at h0
            · simp only [hix, ↓reduceIte] at h0
              exact Or.inr ⟨h0, h.cons (hne hix)⟩

theorem firstGo_nil {β : Type} {f : Atom → Option (ℕ × β)} {x : ℕ} {b : β} {l : List Atom}
    (hx : x + 1 < 2 ^ Exec.indexDepth) (h : getF (firstGo f l .nil) x = some b) : FirstIn f x b l := by
  rcases firstGo_spec hx l _ h with h | ⟨-, h⟩
  · cases h
  · exact h

/-- A constant atom's value number and word. -/
def constKey : Atom → Option (ℕ × E)
  | .const d w => (vnum d).map fun i ↦ (i, w)
  | _ => none

/-- A range check's value number and its bound's value. -/
def rcKey : Atom → Option (ℕ × V)
  | .rangeCheck x _ _ _ k => (vnum x).map fun i ↦ (i, k)
  | _ => none

theorem vnum_n (x : ℕ) : vnum (V.n x) = some x := rfl

theorem findSome?_first {α γ : Type} {g : α → Option γ} {c : γ} {l : List α} (pre : List α) (a : α)
    (post : List α) (hl : l = pre ++ a :: post) (ha : g a = some c) (hpre : ∀ a' ∈ pre, g a' = none) :
    l.findSome? g = some c := by
  subst hl
  rw [List.findSome?_append, List.findSome?_eq_none_iff.2 hpre, Option.none_or, List.findSome?_cons, ha]

theorem constOf_first {as : List Atom} {x : ℕ} {w : E} (h : FirstIn constKey x w as) :
    Res.constOf as (V.n x) = some w := by
  obtain ⟨pre, a, post, hl, ha, hpre⟩ := h
  unfold Res.constOf
  refine findSome?_first pre a post hl ?_ fun a' ha' ↦ ?_
  · cases a with
    | const d w' =>
      cases hd : vnum d with
      | none => simp [constKey, hd] at ha
      | some i =>
        simp only [constKey, hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        simp [vnum_eq hd]
    | _ => simp [constKey] at ha
  · cases a' with
    | const d w' =>
      have hd : d ≠ V.n x := fun e ↦ hpre _ ha' w' (by simp [constKey, e, vnum_n])
      simp [hd]
    | _ => rfl

theorem rcBound_first {as : List Atom} {x e : ℕ} {k : V} (h : FirstIn rcKey x k as)
    (hk : (Res.constOf as k).bind Res.powOf = some e) (he : e + 1 ≤ 2 ^ 33) :
    Res.rcBound as (V.n x) = some (e + 1) := by
  obtain ⟨pre, a, post, hl, ha, hpre⟩ := h
  unfold Res.rcBound
  refine findSome?_first pre a post hl ?_ fun a' ha' ↦ ?_
  · cases a with
    | rangeCheck y t1 t2 t3 k' =>
      cases hy : vnum y with
      | none => simp [rcKey, hy] at ha
      | some i =>
        simp only [rcKey, hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        simp only [vnum_eq hy, ↓reduceIte, hk, he]
    | _ => simp [rcKey] at ha
  · cases a' with
    | rangeCheck y t1 t2 t3 k' =>
      have hy : y ≠ V.n x := fun e ↦ hpre _ ha' k' (by simp [rcKey, e, vnum_n])
      simp [hy]
    | _ => rfl

/-- The body's first range check of each value, by number, from its top-level atoms. -/
noncomputable def rcT (body : List Stmt) : Trie V := firstGo rcKey (Res.topAtoms body) .nil

/-- The body's first constant of each value, by number, from its top-level atoms. -/
noncomputable def constT (body : List Stmt) : Trie E := firstGo constKey (Res.topAtoms body) .nil

/-- A range check's bound of value `x`, by the tries `R` and `C` (`rcT`, `constT`). -/
noncomputable def rcBndT (R : Trie V) (C : Trie E) (x : ℕ) : Option ℕ :=
  bif Nat.blt (x + 1) (2 ^ Exec.indexDepth) then
    match getF R x with
    | some k => match vnum k with
      | some j => bif Nat.blt (j + 1) (2 ^ Exec.indexDepth) then
          match getF C j with
          | some w => match Res.powOf w with
            | some e => bif Nat.ble (e + 1) (2 ^ 33) then some (e + 1) else none
            | none => none
          | none => none
        else none
      | none => none
    | none => none
  else none

theorem rcBndT_spec {body : List Stmt} {x N : ℕ} (h : rcBndT (rcT body) (constT body) x = some N) :
    Res.rcBound (Res.topAtoms body) (V.n x) = some N := by
  unfold rcBndT at h
  cases hx : Nat.blt (x + 1) (2 ^ Exec.indexDepth) <;> rw [hx] at h
  · cases h
  rw [Bool.cond_true] at h
  have hx : x + 1 < 2 ^ Exec.indexDepth := by rw [← Nat.blt_eq]; exact hx
  cases hR : getF (rcT body) x with
  | none => rw [hR] at h; cases h
  | some k =>
    rw [hR] at h
    simp only at h
    cases hk : vnum k with
    | none => rw [hk] at h; cases h
    | some j =>
      rw [hk] at h
      simp only at h
      cases hj : Nat.blt (j + 1) (2 ^ Exec.indexDepth) <;> rw [hj] at h
      · cases h
      rw [Bool.cond_true] at h
      have hj : j + 1 < 2 ^ Exec.indexDepth := by rw [← Nat.blt_eq]; exact hj
      cases hC : getF (constT body) j with
      | none => rw [hC] at h; cases h
      | some w =>
        rw [hC] at h
        simp only at h
        cases hp : Res.powOf w with
        | none => rw [hp] at h; cases h
        | some e =>
          rw [hp] at h
          simp only at h
          cases hb : Nat.ble (e + 1) (2 ^ 33) <;> rw [hb] at h
          · cases h
          rw [Bool.cond_true, Option.some.injEq] at h
          subst h
          have hc := constOf_first (firstGo_nil hj hC)
          rw [← vnum_eq hk] at hc
          exact rcBound_first (firstGo_nil hx hR) (by rw [hc, Option.bind_some, hp])
            (by rw [← Nat.ble_eq]; exact hb)

/-- `e(x) < n` with `x` range checked below `N ≤ n` (looked up in `R`, `C`: `rcT`, `constT`) or a top-level selector
of at most `n` arms (`resFam`'s first case). -/
noncomputable def cheapT (R : Trie V) (C : Trie E) (fn : Fn) : CRes → Bool
  | .lt (.val x) (.num n) => Nat.blt n capE && Nat.blt x GB &&
      ((match rcBndT R C x with
        | some N => Nat.ble N n
        | none => false) || (Res.topSels fn.body).any fun p ↦ decide (p.1 = V.n x) && decide (p.2 ≤ n))
  | _ => false

/-- **A residual of a family, a range check's bound looked up first** (`cheapT`), else `resFamG`. -/
noncomputable def resFamT (R : Trie V) (C : Trie E) (fn : Fn) (xc : List ℕ) (gw : List (CCell × ℕ)) (r : CRes) :
    Bool :=
  cheapT R C fn r || resFamG fn xc gw r

theorem resFamG_of_T {fn : Fn} {xc : List ℕ} {gw : List (CCell × ℕ)} {r : CRes}
    (h : resFamT (rcT fn.body) (constT fn.body) fn xc gw r = true) : resFamG fn xc gw r = true := by
  unfold resFamT cheapT at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · cases r with
    | lt a b =>
      cases a with
      | val x =>
        cases b with
        | num n =>
          simp only [Bool.and_eq_true, Nat.blt_eq, Bool.or_eq_true] at h
          obtain ⟨⟨hn, hg⟩, hT | hT⟩ := h
          · cases hN : rcBndT (rcT fn.body) (constT fn.body) x with
            | none => rw [hN] at hT; cases hT
            | some N =>
              rw [hN, Nat.ble_eq] at hT
              have hrc := rcBndT_spec hN
              simp [resFamG, resFam, hrc, hT, hn, CRes.vals, CIdx.vals, hg]
          · simp [resFamG, resFam, hT, hn, CRes.vals, CIdx.vals, hg]
        | _ => simp at h
      | _ => simp at h
    | _ => simp at h
  · exact h

/-- `resOk`'s residuals by `resFamT` at the body's tries. -/
theorem all_of_T {fn : Fn} {xc : List ℕ} {gw : List (CCell × ℕ)} {l : List CRes}
    (h : l.all (resFamT (rcT fn.body) (constT fn.body) fn xc gw) = true) : l.all (resFamG fn xc gw) = true :=
  List.all_eq_true.2 fun r hr ↦ resFamG_of_T (List.all_eq_true.1 h r hr)

/-- **The disjunct of `resFamG` a hint names**: `1` `resFam` over the indexed atoms (`resFamX`, `ResIx.lean`) or `resQ`,
`2` `resQ`, `3` `rcPts`, `4` `rcTab`, `5` `ownFam`, each with its values below `GB`; `6` the ghost families (`mlSub`,
`stSub`, `cmSub`, `gwFam`); none for any other hint. A generator's hint skips the disjuncts before the one that holds. -/
noncomputable def resFamHint (fn : Fn) (xc : List ℕ) (gw : List (CCell × ℕ)) : ℕ → CRes → Bool
  | 1, r => (resFamX (AtomIx.of (Res.topAtoms fn.body)) fn xc r || resQ fn r) && r.vals.all (Nat.blt · GB)
  | 2, r => resQ fn r && r.vals.all (Nat.blt · GB)
  | 3, r => rcPts fn r && r.vals.all (Nat.blt · GB)
  | 4, r => rcTab fn r && r.vals.all (Nat.blt · GB)
  | 5, r => ownFam fn r && r.vals.all (Nat.blt · GB)
  | 6, r => mlSub fn r || stSub fn r || cmSub fn r || gwFam fn gw r
  | _, _ => false

/-- `resFamT`, the disjunct its hint `h` names tried before `resFamG`. -/
noncomputable def resFamTH (R : Trie V) (C : Trie E) (fn : Fn) (xc : List ℕ) (gw : List (CCell × ℕ)) (h : ℕ)
    (r : CRes) : Bool :=
  cheapT R C fn r || resFamHint fn xc gw h r || resFamG fn xc gw r

theorem resFamG_of_hint {fn : Fn} {xc : List ℕ} {gw : List (CCell × ℕ)} {h : ℕ} {r : CRes}
    (hr : resFamHint fn xc gw h r = true) : resFamG fn xc gw r = true := by
  unfold resFamHint at hr
  unfold resFamG
  split at hr <;> first
    | (simp_all; done)
    | (simp only [resFamX_of, Bool.or_eq_true, Bool.and_eq_true] at hr ⊢; tauto)

theorem resFamTH_sound {R : Trie V} {C : Trie E} {fn : Fn} {xc : List ℕ} {gw : List (CCell × ℕ)} :
    ∀ h r, resFamTH R C fn xc gw h r = true → resFamT R C fn xc gw r = true := by
  intro h r hr
  simp only [resFamTH, Bool.or_eq_true] at hr
  simp only [resFamT, Bool.or_eq_true]
  rcases hr with (hr | hr) | hr
  · exact Or.inl hr
  · exact Or.inr (resFamG_of_hint hr)
  · exact Or.inr hr

/-- The hints of the runs `rs`: each `(h, n)` is `n` residuals of hint `h`. -/
def hintRuns (rs : List (ℕ × ℕ)) : List ℕ := rs.flatMap fun r ↦ List.replicate r.2 r.1

/-- `resOk`'s residuals by `resFamTH` at the body's tries, each at its hint from `hs` (`0` past them). -/
theorem all_of_TH {fn : Fn} {xc : List ℕ} {gw : List (CCell × ℕ)} {l : List CRes} {hs : List ℕ}
    (h : allH (resFamTH (rcT fn.body) (constT fn.body) fn xc gw) hs l = true) : l.all (resFamG fn xc gw) = true :=
  all_of_T (all_of_allH (q := resFamTH (rcT fn.body) (constT fn.body) fn xc gw) resFamTH_sound hs l h)

/-! ## The values' cells -/

/-- The entries of `l` by position from `i`, positions below the tries' depth, over `t`. -/
noncomputable def listGo : ℕ → List ℕ → Trie ℕ → Trie ℕ
  | _, [], t => t
  | i, c :: l, t => bif Nat.blt (i + 1) (2 ^ Exec.indexDepth) then (setF c Exec.indexDepth t i).seq fun t ↦ listGo (i + 1) l t
    else t

theorem listGo_spec {k c : ℕ} : ∀ (i : ℕ) (l : List ℕ) (t : Trie ℕ), getF (listGo i l t) k = some c →
    getF t k = some c ∨ (i ≤ k ∧ l[k - i]? = some c)
  | _, [], t, h => Or.inl h
  | i, c' :: l, t, h => by
    unfold listGo at h
    cases hb : Nat.blt (i + 1) (2 ^ Exec.indexDepth) <;> rw [hb] at h
    · exact Or.inl h
    rw [Bool.cond_true, Exec.Trie.seq_eq] at h
    have hi : i + 1 < 2 ^ Exec.indexDepth := by rw [← Nat.blt_eq]; exact hb
    have hs : getF (setF c' Exec.indexDepth t i) k = if k = i then some c' else getF t k := by
      rw [Check.getF_eq, Check.setF_eq, Check.get_set_eq c' _ t i k hi, ← Check.getF_eq]
    rcases listGo_spec (i + 1) l _ h with h | ⟨hk, h⟩
    · rw [hs] at h
      by_cases hki : k = i
      · subst hki
        simp only [↓reduceIte] at h
        exact Or.inr ⟨le_refl _, by simpa using h⟩
      · simp only [hki, ↓reduceIte] at h
        exact Or.inl h
    · refine Or.inr ⟨by omega, ?_⟩
      rw [show k - i = k - (i + 1) + 1 by omega, List.getElem?_cons_succ]
      exact h

/-- **Function `j`'s values' cells**, by value number (`B2C.cellJ`). -/
noncomputable def locT (j : ℕ) : Trie ℕ := listGo 0 (certOf j).locs .nil

theorem cellJ_of_locT {j : ℕ} {v : V} {c : ℕ} (h : getF (locT j) v.idx = some c) : B2C.cellJ j v = c := by
  rcases listGo_spec 0 _ _ h with h | ⟨-, h⟩
  · cases h
  · unfold B2C.cellJ
    rw [Nat.sub_zero] at h
    rw [List.getD_eq_getElem?_getD, h, Option.getD_some]

/-- `ptrCellB`, a pointer's cell looked up in `L` (`locT j`) first. -/
noncomputable def ptrCellT (L : Trie ℕ) (j : ℕ) : Stmt → Bool
  | .atom a => match ptrOf a with
    | some p => ((Bridge.extraOf j).lookup p.idx).isNone && decide (p.idx < 2 ^ 30) &&
        match getF L p.idx with
        | some c => decide (2 ≤ c) && decide (c < B2C.fsN j)
        | none => decide (2 ≤ B2C.cellJ j p) && decide (B2C.cellJ j p < B2C.fsN j)
    | none => true
  | _ => true

theorem ptrCellB_of_T {j : ℕ} {s : Stmt} (h : ptrCellT (locT j) j s = true) : ptrCellB j s = true := by
  cases s with
  | atom a =>
    simp only [ptrCellT] at h
    simp only [ptrCellB]
    cases hp : ptrOf a with
    | none => rfl
    | some p =>
      rw [hp] at h
      simp only at h ⊢
      cases hl : getF (locT j) p.idx with
      | none => rw [hl] at h; simpa only [Bool.and_assoc] using h
      | some c => rw [hl, ← cellJ_of_locT hl] at h; simpa only [Bool.and_assoc] using h
  | _ => rfl

/-- `ptrCellB` over statements, by `ptrCellT` at `locT j`. -/
theorem all_ptrCellB_of_T {j : ℕ} {l : List Stmt} (h : l.all (ptrCellT (locT j) j) = true) :
    l.all (ptrCellB j) = true :=
  List.all_eq_true.2 fun s hs ↦ ptrCellB_of_T (List.all_eq_true.1 h s hs)

end

end LeanVM.Guest.CoreMode
