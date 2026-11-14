/-
  LeanVM.Guest.Res.SelDefs

  The residual families' checks over the core IR: a table dispatch's selector below its count of
  arms, on every path through it.
-/

module

public import LeanVM.Guest.Memory.StaticSound
public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.Mode.Step

/-!
# The selectors' checks

An order residual at a table jump (`[o]`'s exponent, or `[[q]·g^k]`'s, below `N`) bounds the
selector of a `match` or `dispatch`: a path that passes one takes an arm, so its selector is
`g^e`, `e` below the count of arms (`walkArms_sel`, `pick_sel`), and the path of an instance that
returns passes every top-level statement once those before it have no `ret`.

`scanFr j o N ns body`: a top-level `match` or `dispatch` of at most `N` ways on a value of cell
`o` (`cellJ j`), named (in `ns`, the parameters, or used by a top-level atom before it), every
statement before it free of `ret` (`scanFr_sound`). `scanHp j q k N xs body`: the same on a value a
top-level atom before it loads from `[q]·g^k` (`scanHp_sound`). `ltSelB j r`: residual `r` is such
a bound of function `j`'s body, its cell inside the frame (`2 ≤ cell < fsN j`, where the
completeness check reads it).

`nzB nzs j o`: residual `nz o` is the cell of a parameter of function `j`, its loop counter or
listed in `nzs`. `ResOk exc nzs K`: certificate `K` is listed in `exc`, or each of its residuals
is a name, a selector's bound or such a divisor at its function's index, or a run inside others
(`sub`), decided per certificate (`resOk_of`). `allV p t`: every value stored in `t` satisfies `p`
(`allV_get`).
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie)
open LeanVM.Guest.B2C (cellJ fsN)

@[expose] public section

/-! ## Tries -/

/-- Every value stored in a trie satisfies `p`. -/
noncomputable def allV {α : Type} (p : α → Bool) (t : Trie α) : Bool :=
  Trie.rec (motive := fun _ ↦ Bool) true
    (fun v _ _ al ar ↦ (match v with | some a => p a | none => true) && al && ar) t

theorem allV_get {α : Type} {p : α → Bool} :
    ∀ {t : Trie α}, allV p t = true → ∀ {n : ℕ} {a : α}, t.get n = some a → p a = true
  | .nil, _, _, _, h => by simp [Trie.get] at h
  | .node v l r, hv, n, a, h => by
    simp only [allV, Bool.and_eq_true] at hv
    obtain ⟨⟨h0, hl⟩, hr⟩ := hv
    have hg : (Trie.node v l r).get n =
        bif n == 0 then v else bif n % 2 == 1 then l.get (n / 2) else r.get (n / 2 - 1) := rfl
    rw [hg] at h
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [beq_self_eq_true, Bool.cond_true] at h
      subst h
      exact h0
    · have hne : (n == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
      rw [hne, Bool.cond_false] at h
      cases hm : n % 2 == 1
      · rw [hm, Bool.cond_false] at h; exact allV_get hr h
      · rw [hm, Bool.cond_true] at h; exact allV_get hl h

/-! ## The scans -/

/-- A selector statement's value and its count of arms or callees. -/
def selOf : Stmt → Option (V × ℕ)
  | .match_ x arms => some (x, arms.length)
  | .dispatch x fs _ _ => some (x, fs.length)
  | _ => none

/-- The values named after a statement: an atom's uses added. -/
def namedAdd (ns : List V) : Stmt → List V
  | .atom a => atomUses a ++ ns
  | _ => ns

/-- **A frame cell's selector**: a top-level `match` or `dispatch` of at most `N` ways on a value
of cell `o`, named (in `ns`, or used by a top-level atom before it), the statements before it free
of `ret`. -/
noncomputable def scanFr (j o N : ℕ) (ns : List V) : List Stmt → Bool
  | [] => false
  | s :: ss =>
    (match selOf s with
      | some (x, n) => decide (x ∈ ns) && cellJ j x == o && decide (n ≤ N)
      | none => false) ||
    (Memory.Stmt.noRet s && scanFr j o N (namedAdd ns s) ss)

/-- The values loaded from `[q]·g^k` after a statement: a top-level `load`'s destination added. -/
noncomputable def loadsTo (j q k : ℕ) (xs : List V) : Stmt → List V
  | .atom (.load d p k') => if cellJ j p == q && k' == k then d :: xs else xs
  | _ => xs

/-- **A loaded selector**: a top-level `match` or `dispatch` of at most `N` ways on a value a
top-level atom before it loads from `[q]·g^k` (in `xs`), the statements before it free of `ret`. -/
noncomputable def scanHp (j q k N : ℕ) (xs : List V) : List Stmt → Bool
  | [] => false
  | s :: ss =>
    (match selOf s with
      | some (x, n) => decide (x ∈ xs) && decide (n ≤ N)
      | none => false) ||
    (Memory.Stmt.noRet s && scanHp j q k N (loadsTo j q k xs s) ss)

/-- **An order residual bounding a selector of function `j`**: a frame cell's (`scanFr` from the
parameters) or a loaded word's (`scanHp`), the cell inside the frame. -/
noncomputable def ltSelB (j : ℕ) : Mode.Res → Bool
  | .lt (.ex (.fr o) 0) (.num N) => decide (N ≤ 2 ^ 62) && decide (2 ≤ o) && decide (o < fsN j) &&
      scanFr j o N (coreOf j).params (coreOf j).body
  | .lt (.ex (.hp q k) 0) (.num N) => decide (N ≤ 2 ^ 62) && decide (2 ≤ q) && decide (q < fsN j) &&
      scanHp j q k N [] (coreOf j).body
  | _ => false

/-- A loop helper's counter, its first parameter. -/
noncomputable def ctrOf (j : ℕ) : Option V := if (coreOf j).loop then (coreOf j).params.head? else none

/-- **A nonzero divisor at a parameter**: residual `nz o` is the cell, inside the frame, of a
parameter `v` of function `j`, its loop counter or listed with the function's name in `nzs`. -/
noncomputable def nzB (nzs : List (String × V)) (j o : ℕ) : Bool :=
  decide (2 ≤ o) && decide (o < fsN j) && (coreOf j).params.any fun v ↦
    cellJ j v == o && (ctrOf j == some v || decide (((coreOf j).name, v) ∈ nzs))

/-- A residual the families take at function `j`: a name, a selector's bound (`ltSelB`), a run
inside others, or a nonzero divisor at a parameter (`nzB`). -/
noncomputable def famB (nzs : List (String × V)) (j : ℕ) : Mode.Res → Bool
  | .name _ => true
  | .lt a b => ltSelB j (.lt a b)
  | .sub _ _ => true
  | .nz o => nzB nzs j o

/-- **A certificate's residuals in the families**: it is listed in `exc`, or each of its residuals
is in the families at its function's index `j`. -/
def ResOk (exc : List Mode.Cert) (nzs : List (String × V)) (K : Mode.Cert) : Prop :=
  K ∈ exc ∨ ∃ j, j < nFns ∧ (fnOf j).entryPc = K.F.entry ∧ allV (fun l ↦ l.all (famB nzs j)) K.F.res = true

theorem resOk_of {exc : List Mode.Cert} {nzs : List (String × V)} {K : Mode.Cert} {j : ℕ}
    (h : (decide (j < nFns) && (fnOf j).entryPc == K.F.entry && allV (fun l ↦ l.all (famB nzs j)) K.F.res) = true) :
    ResOk exc nzs K := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact Or.inr ⟨j, h.1.1, h.1.2, h.2⟩

theorem resOk_exc {exc : List Mode.Cert} {nzs : List (String × V)} {K : Mode.Cert} (h : K ∈ exc) :
    ResOk exc nzs K := Or.inl h

/-! ## Soundness -/

section

variable {σ : Val}

theorem pick_sel {x : V} {a r : List V} : ∀ (fs : List String) (j : ℕ), pick σ x a r j fs ≠ .stuck →
    ∃ e < fs.length, σ x = ofK (addressOfIndex (j + e))
  | [], _, h => absurd rfl h
  | f :: fs, j, h => by
    unfold pick at h
    split_ifs at h with hx
    · exact ⟨0, by simp, by simpa using hx⟩
    · obtain ⟨e, he, hx'⟩ := pick_sel fs (j + 1) h
      exact ⟨e + 1, by simpa using he, by rw [hx']; congr 2; omega⟩

theorem walkArms_sel' {x : V} : ∀ (arms : List (List Stmt)) (j : ℕ), walkArms σ x j arms ≠ .stuck →
    ∃ e < arms.length, σ x = ofK (addressOfIndex (j + e))
  | [], _, h => absurd rfl h
  | a :: as, j, h => by
    unfold walkArms at h
    split_ifs at h with hx
    · exact ⟨0, by simp, by simpa using hx⟩
    · obtain ⟨e, he, hx'⟩ := walkArms_sel' as (j + 1) h
      exact ⟨e + 1, by simpa using he, by rw [hx']; congr 2; omega⟩

/-- A selector statement a path passes picks an arm. -/
theorem selOf_walk {s : Stmt} {x : V} {n : ℕ} (hs : selOf s = some (x, n)) (h : walk1 σ s ≠ .stuck) :
    ∃ e < n, σ x = ofK (addressOfIndex e) := by
  cases s with
  | match_ y arms =>
    simp only [selOf, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨e, he, hx⟩ := walkArms_sel' (σ := σ) arms 0 h
    exact ⟨e, he, by simpa using hx⟩
  | dispatch y fs a r =>
    simp only [selOf, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨e, he, hx⟩ := pick_sel (σ := σ) fs 0 h
    exact ⟨e, he, by simpa using hx⟩
  | _ => simp [selOf] at hs

/-- A returning path past a statement free of `ret`: its events, then the rest's. -/
theorem walk_cons_noRet {s : Stmt} {ss : List Stmt} {es : List Ev} {vs : List V}
    (hn : Memory.Stmt.noRet s = true) (h : walk σ (s :: ss) = .ret es vs) :
    ∃ es1 es2, walk1 σ s = .fall es1 ∧ walk σ ss = .ret es2 vs ∧ es = es1 ++ es2 := by
  rw [walk] at h
  rcases Memory.walk1_noRet (σ := σ) s hn with ⟨es1, h1⟩ | h1
  · rw [h1] at h
    cases h2 : walk σ ss with
    | fall _ => rw [h2] at h; simp [Out.seq, Out.pre] at h
    | ret es2 vs2 =>
      rw [h2] at h
      simp only [Out.seq, Out.pre, Out.ret.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨es1, es2, h1, rfl, rfl⟩
    | stuck => rw [h2] at h; simp [Out.seq, Out.pre] at h
  · rw [h1] at h; simp [Out.seq] at h

theorem walk1_ne_stuck {s : Stmt} {ss : List Stmt} {es : List Ev} {vs : List V}
    (h : walk σ (s :: ss) = .ret es vs) : walk1 σ s ≠ .stuck := by
  intro h1
  rw [walk, h1] at h
  simp [Out.seq] at h

/-- **A frame cell's selector on a returning path**: some value of cell `o`, named, is `g^e`,
`e < N`. -/
theorem scanFr_sound {j o N : ℕ} :
    ∀ {ss : List Stmt} {ns : List V} {es : List Ev} {vs : List V}, scanFr j o N ns ss = true →
      walk σ ss = .ret es vs → ∃ x e, cellJ j x = o ∧ e < N ∧ σ x = ofK (addressOfIndex e) ∧
        (x ∈ ns ∨ ∃ a, Ev.atom a ∈ es ∧ x ∈ atomUses a)
  | [], _, _, _, h, _ => by simp [scanFr] at h
  | s :: ss, ns, es, vs, h, hw => by
    simp only [scanFr, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hn, h⟩
    · split at h
      · rename_i x n hs
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        obtain ⟨⟨hx, hc⟩, hnN⟩ := h
        obtain ⟨e, he, hσ⟩ := selOf_walk hs (walk1_ne_stuck hw)
        exact ⟨x, e, hc, by omega, hσ, Or.inl hx⟩
      · cases h
    · obtain ⟨es1, es2, h1, h2, rfl⟩ := walk_cons_noRet hn hw
      obtain ⟨x, e, hc, he, hσ, hx⟩ := scanFr_sound h h2
      refine ⟨x, e, hc, he, hσ, ?_⟩
      rcases hx with hx | ⟨a, ha, hxa⟩
      · cases s with
        | atom b =>
          simp only [namedAdd, List.mem_append] at hx
          simp only [walk1, Out.fall.injEq] at h1
          subst h1
          rcases hx with hx | hx
          · exact Or.inr ⟨b, List.mem_cons_self, hx⟩
          · exact Or.inl hx
        | _ => exact Or.inl hx
      · exact Or.inr ⟨a, List.mem_append_right _ ha, hxa⟩

/-- **A loaded selector on a returning path**: some top-level `load` of the path, from `[p]·g^k`
with `p` of cell `q`, loads a value that is `g^e`, `e < N`, or the value is in `xs`. -/
theorem scanHp_sound {j q k N : ℕ} :
    ∀ {ss : List Stmt} {xs : List V} {es : List Ev} {vs : List V}, scanHp j q k N xs ss = true →
      walk σ ss = .ret es vs → ∃ x e, e < N ∧ σ x = ofK (addressOfIndex e) ∧
        (x ∈ xs ∨ ∃ p, Ev.atom (.load x p k) ∈ es ∧ cellJ j p = q)
  | [], _, _, _, h, _ => by simp [scanHp] at h
  | s :: ss, xs, es, vs, h, hw => by
    simp only [scanHp, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hn, h⟩
    · split at h
      · rename_i x n hs
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hx, hnN⟩ := h
        obtain ⟨e, he, hσ⟩ := selOf_walk hs (walk1_ne_stuck hw)
        exact ⟨x, e, by omega, hσ, Or.inl hx⟩
      · cases h
    · obtain ⟨es1, es2, h1, h2, rfl⟩ := walk_cons_noRet hn hw
      obtain ⟨x, e, he, hσ, hx⟩ := scanHp_sound h h2
      refine ⟨x, e, he, hσ, ?_⟩
      rcases hx with hx | ⟨p, ha, hp⟩
      · have key : ∀ b : Atom, s = .atom b → x ∈ loadsTo j q k xs (.atom b) →
            x ∈ xs ∨ ∃ p, Ev.atom (.load x p k) ∈ es1 ++ es2 ∧ cellJ j p = q := by
          intro b hsb hxb
          subst hsb
          simp only [walk1, Out.fall.injEq] at h1
          subst h1
          cases b with
          | load d p' k' =>
            simp only [loadsTo] at hxb
            split_ifs at hxb with hc
            · simp only [Bool.and_eq_true, beq_iff_eq] at hc
              rcases List.mem_cons.mp hxb with rfl | hxb
              · obtain ⟨hc1, rfl⟩ := hc
                exact Or.inr ⟨p', List.mem_cons_self, hc1⟩
              · exact Or.inl hxb
            · exact Or.inl hxb
          | _ => exact Or.inl hxb
        cases s with
        | atom b => exact key b rfl hx
        | _ => exact Or.inl hx
      · exact Or.inr ⟨p, List.mem_append_right _ ha, hp⟩

end

end

end LeanVM.Guest.Res
