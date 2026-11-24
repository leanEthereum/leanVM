/-
  LeanVM.Guest.CoreMode.Fam.SelDefs

  The residual families' checks over the core IR: a table dispatch's selector below its count of
  arms, on every path through it.
-/

module

public import LeanVM.Guest.Memory.StaticSound
public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.Mode.Step
public import LeanVM.Guest.CoreMode.Fam.ParamRef
public import LeanVM.Guest.CoreMode.Gen.FnData
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.ValRef

/-!
# The selectors' checks

An order residual at a table jump (`[o]`'s exponent, or `[[q]·g^k]`'s, below `N`) bounds the
selector of a `match` or `dispatch`: a path that passes one takes an arm, so its selector is
`g^e`, `e` below the count of arms (`walkArms_sel`, `pick_sel`), and the path of an instance that
returns passes every top-level statement once those before it have no `ret`.

`splits`: the frame's splits `[n] = [s]^S·[r]`, `[s]` and `[r]` powers of `g`. `nzB nzs j o`: residual
`nz o` is the cell of a parameter of function `j`, its loop counter or listed in `nzs`. `allV p t`: every value stored in `t` satisfies `p`
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

/-- A loop helper's counter, its first parameter. -/
noncomputable def ctrOf (j : ℕ) : Option V := if (coreOf j).loop then (coreOf j).params.head? else none

/-- **Value `v` is named before any `ret`**: a top-level atom of the block before its first
statement that may return uses it. -/
noncomputable def topUses (v : V) : List Stmt → Bool
  | [] => false
  | s :: ss => (match s with
      | .atom a => decide (v ∈ atomUses a)
      | _ => false) || (Memory.Stmt.noRet s && topUses v ss)

/-- **A nonzero divisor at a parameter or a named value**: residual `nz o` is the cell, inside the
frame, of a parameter `v` of function `j`, its loop counter or listed with the function's name in
`nzs`, or of a value listed so that a top-level atom names (`topUses`). -/
noncomputable def nzB (nzs : List (String × V)) (j o : ℕ) : Bool :=
  decide (2 ≤ o) && decide (o < fsN j) && ((coreOf j).params.any (fun v ↦
    cellJ j v == o && (ctrOf j == some v || decide (((coreOf j).name, v) ∈ nzs))) ||
    nzs.any fun p ↦ p.1 == (coreOf j).name && cellJ j p.2 == o && topUses p.2 (coreOf j).body)

/-- Cell `o` is inside function `j`'s frame. -/
noncomputable def inFr (j o : ℕ) : Bool := decide (2 ≤ o) && decide (o < fsN j)

/-- **Exponent facts at listed parameters**: function, parameter, offset (`none`: its word; `some k`: the word read at
`[parameter]·g^k`), bound; each function's own (`FnReg.expFacts`, `CoreMode/Fn/<f>/Data.lean`). -/
abbrev expFacts : List (String × ℕ × Option ℕ × ℕ) := CoreMode.FnReg.expFacts

/-- Parameter `p`'s fact at offset `o` names base `B` of function `j`. -/
noncomputable def baseAt (j : ℕ) (p : V) : Option ℕ → Mode.Base → Bool
  | none, .fr c => cellJ j p == c
  | some k, .hp q k' => cellJ j p == q && k == k'
  | _, _ => false

/-- **A base's exponent fact**: the parameter and the bound of a listed fact naming it. -/
noncomputable def expOf (j : ℕ) (B : Mode.Base) : Option (V × ℕ) :=
  expFacts.findSome? fun c ↦
    if c.1 == (coreOf j).name then
      match (coreOf j).params[c.2.1]? with
      | some p => if baseAt j p c.2.2.1 B then some (p, c.2.2.2) else none
      | none => none
    else none

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

/-- **A value `topUses` names is named on every returning path.** -/
theorem topUses_sound {v : V} :
    ∀ {ss : List Stmt} {es : List Ev} {vs : List V}, topUses v ss = true → walk σ ss = .ret es vs →
      ∃ a, Ev.atom a ∈ es ∧ v ∈ atomUses a
  | [], _, _, h, _ => by simp [topUses] at h
  | s :: ss, es, vs, h, hw => by
    simp only [topUses, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hn, h⟩
    · cases s with
      | atom a =>
        simp only [decide_eq_true_eq] at h
        obtain ⟨es1, es2, h1, -, rfl⟩ := walk_cons_noRet (s := .atom a) rfl hw
        simp only [walk1, Out.fall.injEq] at h1
        subst h1
        exact ⟨a, List.mem_cons_self, h⟩
      | _ => simp at h
    · obtain ⟨es1, es2, -, h2, rfl⟩ := walk_cons_noRet hn hw
      obtain ⟨a, ha, hv⟩ := topUses_sound h h2
      exact ⟨a, List.mem_append_right _ ha, hv⟩

end

end

end LeanVM.Guest.Res
