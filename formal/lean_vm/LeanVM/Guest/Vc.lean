/-
  LeanVM.Guest.Vc

  The forward verification condition of the core IR: a predicate transformer over the values
  defined so far, and the theorem that it is the relational semantics.
-/

module

public import LeanVM.Guest.Core

/-!
# The forward verification condition

`Fn.Sem` quantifies over a valuation of every value of a function, though almost every value is
defined by the statement that first names it. `Stmt.wp` walks a body with an environment `Env`, the
words of the values defined so far: reading a defined value gives its word, and reading one not
yet defined introduces an existential word, which defines it (`getv`). An atom then holds of the
words it reads (`Atom.rel`), a branch splits on the word read, a call is the call relation on its
words and a `ret` hands its words to the return condition.

`Fn.sem_iff_wp`: a function's relation is the condition of its body from the empty environment,
its parameters read first, for every body. Its invariant (`Stmt.wpList_iff`): the condition of a
block at an environment `ρ` holds exactly when some valuation agreeing with `ρ` satisfies the
block's relational semantics. The equations `wp_*` and `wpList_*` unfold one statement without
unfolding the rest of its block; the `vc` tactic (`VcTactic.lean`) applies them to a concrete body.
-/

namespace LeanVM.Guest.Core

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-! ## Environments and reads -/

/-- The words of the values defined so far. -/
abbrev Env := V → Option E

/-- No value defined. -/
def Env.empty : Env := fun _ => none

/-- Whether two values are the same, their indices compared first, which the kernel compares as
numerals. -/
def V.beq (a b : V) : Bool := a.idx.beq b.idx && a.tag.beq b.tag && a.path == b.path

theorem V.beq_iff {a b : V} : a.beq b = true ↔ a = b := by
  obtain ⟨p, t, i⟩ := a
  obtain ⟨p', t', i'⟩ := b
  simp only [V.beq, Bool.and_eq_true, Nat.beq_eq, beq_iff_eq, V.mk.injEq]
  tauto

/-- `ρ` with `v` defined as `x`. -/
def Env.upd (ρ : Env) (v : V) (x : E) : Env := fun w => bif w.beq v then some x else ρ w

theorem Env.upd_apply (ρ : Env) (v w : V) (x : E) :
    ρ.upd v x w = if w = v then some x else ρ w := by
  simp only [Env.upd, Bool.cond_eq_ite, V.beq_iff]

/-! ### Environments for the kernel

The kernel reads a value's word in `Env.upd`'s chain in a step per definition after it. `Defs`
stores the definitions by the bits of their values' indices, so that it reads one in a step per
bit; `vc` keeps its environments as `Env.ofDefs`, a read's definitions added by `Env.upd_ofDefs`. -/

/-- Definitions by the bits of their values' indices, low bit first. -/
inductive Defs where
  | nil
  | node (here : List (V × E)) (zero one : Defs)

namespace Defs

def here : Defs → List (V × E)
  | nil => []
  | node h _ _ => h

def zero : Defs → Defs
  | nil => nil
  | node _ z _ => z

def one : Defs → Defs
  | nil => nil
  | node _ _ o => o

/-- The word of `v` in `l`. -/
def wordIn : List (V × E) → V → Option E
  | [], _ => none
  | (w, x) :: l, v => bif v.beq w then some x else wordIn l v

/-- The word of `v`, `k` the bits of its index left to follow, in at most `n` more levels. -/
def find : Defs → V → Nat → Nat → Option E
  | nil, _, _, _ => none
  | node h _ _, v, _, 0 => wordIn h v
  | node h z o, v, k, n + 1 =>
    bif k.beq 0 then wordIn h v
    else bif (k % 2).beq 0 then z.find v (k / 2) n else o.find v (k / 2) n

/-- `t` with `v` defined as `x` at the node `k`'s bits lead to in at most `n` levels. -/
def insert (t : Defs) (v : V) (x : E) : Nat → Nat → Defs
  | _, 0 => node ((v, x) :: t.here) t.zero t.one
  | k, n + 1 =>
    bif k.beq 0 then node ((v, x) :: t.here) t.zero t.one
    else bif (k % 2).beq 0 then node t.here (t.zero.insert v x (k / 2) n) t.one
    else node t.here t.zero (t.one.insert v x (k / 2) n)

theorem find_eta (t : Defs) (v : V) (k n : Nat) :
    t.find v k n = (node t.here t.zero t.one).find v k n := by
  cases t <;> cases n <;> simp [find, here, zero, one, wordIn]

theorem find_insert (x : E) (v w : V) : ∀ (n : Nat) (t : Defs) (k kw : Nat), (w = v → kw = k) →
    (t.insert v x k n).find w kw n = if w = v then some x else t.find w kw n
  | 0, t, k, kw, _ => by
    rw [find_eta t]
    simp only [insert, find, wordIn, Bool.cond_eq_ite, V.beq_iff]
  | n + 1, t, k, kw, h => by
    rw [find_eta t]
    by_cases hw : w = v
    · subst hw
      obtain rfl := h rfl
      by_cases h0 : kw = 0
      · simp [insert, find, wordIn, h0, V.beq_iff]
      · by_cases h2 : kw % 2 = 0
        · simp [insert, find, h0, h2, find_insert x w w n t.zero (kw / 2) (kw / 2) fun _ => rfl]
        · simp [insert, find, h0, h2, find_insert x w w n t.one (kw / 2) (kw / 2) fun _ => rfl]
    · simp only [hw, ↓reduceIte]
      by_cases h0 : k = 0 <;> by_cases hk2 : k % 2 = 0 <;> by_cases hw0 : kw = 0 <;>
        by_cases hw2 : kw % 2 = 0 <;>
        simp [insert, find, wordIn, h0, hk2, hw0, hw2, hw, V.beq_iff,
          find_insert x v w n _ (k / 2) (kw / 2) (fun e => absurd e hw)]

end Defs

/-- An environment as a table of definitions. -/
def Env.ofDefs (t : Defs) : Env := fun w => t.find w w.idx 64

theorem Env.upd_ofDefs (t : Defs) (v : V) (x : E) :
    (Env.ofDefs t).upd v x = Env.ofDefs (t.insert v x v.idx 64) :=
  funext fun w => by
    rw [Env.upd_apply, Env.ofDefs, Env.ofDefs, Defs.find_insert x v w 64 t v.idx w.idx
      fun h => h ▸ rfl]

/-- Read `v`: its word if it is defined, else some word `x`, `v` then defined as `x`. -/
def getv (ρ : Env) (v : V) (Q : Env → E → Prop) : Prop :=
  match ρ v with
  | some x => Q ρ x
  | none => ∃ x, Q (ρ.upd v x) x

/-- Read values in order. -/
def getvs (ρ : Env) : List V → (Env → List E → Prop) → Prop
  | [], Q => Q ρ []
  | v :: vs, Q => getv ρ v fun ρ x => getvs ρ vs fun ρ xs => Q ρ (x :: xs)

/-! ## Atoms on words -/

/-- The values an atom's relation reads, in the order its words are listed (`Atom.rel`). -/
def Atom.vars : Atom → List V
  | .const d _ => [d]
  | .add d a b | .mul d a b => [a, b, d]
  | .copy d s => [s, d]
  | .load d p _ => [p, d]
  | .assertEq a b | .assertInK a b => [a, b]
  | .assertNe x i p => [x, i, p]
  | .rangeCheck x y t1 t2 k => [x, y, t1, t2, k]
  | .keccak ins outs _ _ => ins ++ outs
  | .frameAddr p run => p :: run
  | .hint _ => []
  | .touch t p => [p, t]

/-- An atom's relation on the words of its values (`Atom.vars`): `Atom.Holds` with each value's
word in its place (`Atom.rel_map`). -/
def Atom.rel (rd : Reader) : Atom → List E → Prop
  | .const _ c, [d] => d = c
  | .add .., [a, b, d] => d = a + b
  | .mul .., [a, b, d] => d = a * b
  | .copy .., [s, d] => d = s
  | .load _ _ off, [p, d] => LoadHolds rd p off d
  | .assertEq .., [a, b] => a + b = 0
  | .assertNe .., [x, i, p] => p = x * i ∧ p = 1
  | .rangeCheck .., [x, y, t1, t2, k] => LoadHolds rd x 0 t1 ∧ k = x * y ∧ LoadHolds rd y 0 t2
  | .assertInK .., [a, b] => IsInK a ∧ IsInK b
  | .keccak ins outs inOdd outOdd, ws => ins.length = 13 ∧ ∃ outCells : KeccakOutputCells,
      outs.length = outCells.cellCount ∧
        KeccakCellsRelation (cells13 (ws.take 13)) inOdd (cells13 (ws.drop 13)) outOdd outCells
  | .frameAddr _ run, p :: ws => IsInK p ∧ ∀ (k : Nat) (_ : k < run.length) (w : E),
      rd (p.limb 0 * addressOfIndex k) = some w → w = ws.getD k 0
  | .hint _, _ => True
  | .touch .., [p, t] => LoadHolds rd p 0 t
  | _, _ => False

/-- An atom: read its values, then its relation on their words. -/
def Atom.wp (rd : Reader) (ρ : Env) (Q : Env → Prop) (a : Atom) : Prop :=
  getvs ρ a.vars fun ρ xs => a.rel rd xs ∧ Q ρ

/-! ## Statements -/

mutual
/-- A statement's condition at `ρ`, `Q` the condition of the rest of its block and `kret` the
return condition. -/
def Stmt.wp (C : CallRel) (rd : Reader) (kret : List E → Prop) :
    Stmt → Env → (Env → Prop) → Prop
  | .atom a, ρ, Q => a.wp rd ρ Q
  | .ite c z n, ρ, Q => getv ρ c fun ρ x =>
      IsInK x ∧ (x = 0 → Stmt.wpList C rd kret z ρ Q) ∧ (x ≠ 0 → Stmt.wpList C rd kret n ρ Q)
  | .match_ x arms, ρ, Q => getv ρ x fun ρ xv => Stmt.wpArms C rd kret xv 0 arms ρ Q
  | .call f args rets, ρ, Q => getvs ρ args fun ρ as => getvs ρ rets fun ρ rs => C f as rs ∧ Q ρ
  | .callIf c f args, ρ, Q => getv ρ c fun ρ x => getvs ρ args fun ρ as =>
      (IsInK x ∧ (x ≠ 0 → C f as [])) ∧ Q ρ
  | .dispatch x fs args rets, ρ, Q => getv ρ x fun ρ xv => getvs ρ args fun ρ as =>
      getvs ρ rets fun ρ rs =>
        (∃ (j : Nat) (h : j < fs.length), xv = ofK (addressOfIndex j) ∧ C fs[j] as rs) ∧ Q ρ
  | .ret vs, ρ, _ => getvs ρ vs fun _ xs => kret xs

/-- A block's condition. -/
def Stmt.wpList (C : CallRel) (rd : Reader) (kret : List E → Prop) :
    List Stmt → Env → (Env → Prop) → Prop
  | [], ρ, Q => Q ρ
  | s :: ss, ρ, Q => Stmt.wp C rd kret s ρ fun ρ => Stmt.wpList C rd kret ss ρ Q

/-- Arm `j + i` runs at `xv = g^(j + i)`, for some arm `i` of the list. -/
def Stmt.wpArms (C : CallRel) (rd : Reader) (kret : List E → Prop) (xv : E) :
    Nat → List (List Stmt) → Env → (Env → Prop) → Prop
  | _, [], _, _ => False
  | j, a :: as, ρ, Q => (xv = ofK (addressOfIndex j) ∧ Stmt.wpList C rd kret a ρ Q) ∨
      Stmt.wpArms C rd kret xv (j + 1) as ρ Q
end

/-- Some arm `j + i` of the conditions `ps` holds at `xv = g^(j + i)`. -/
def armsDisj (xv : E) : Nat → List Prop → Prop
  | _, [] => False
  | j, p :: ps => (xv = ofK (addressOfIndex j) ∧ p) ∨ armsDisj xv (j + 1) ps

theorem armsDisj_cons (xv : E) (j : Nat) (p : Prop) (ps : List Prop) :
    armsDisj xv j (p :: ps) = ((xv = ofK (addressOfIndex j) ∧ p) ∨ armsDisj xv (j + 1) ps) := rfl

/-! ## One statement at a time -/

section Equations

variable (C : CallRel) (rd : Reader) (kret : List E → Prop) (ρ : Env) (Q : Env → Prop)

theorem wpList_nil : Stmt.wpList C rd kret [] ρ Q = Q ρ := rfl

theorem wpList_cons (s : Stmt) (ss : List Stmt) :
    Stmt.wpList C rd kret (s :: ss) ρ Q =
      Stmt.wp C rd kret s ρ fun ρ => Stmt.wpList C rd kret ss ρ Q := rfl

theorem wp_atom (a : Atom) :
    Stmt.wp C rd kret (.atom a) ρ Q = getvs ρ a.vars fun ρ xs => a.rel rd xs ∧ Q ρ := rfl

theorem wp_ite (c : V) (z n : List Stmt) :
    Stmt.wp C rd kret (.ite c z n) ρ Q = getv ρ c fun ρ x =>
      IsInK x ∧ (x = 0 → Stmt.wpList C rd kret z ρ Q) ∧ (x ≠ 0 → Stmt.wpList C rd kret n ρ Q) :=
  rfl

theorem wpArms_eq (xv : E) (arms : List (List Stmt)) :
    ∀ (j : Nat) (ρ : Env), Stmt.wpArms C rd kret xv j arms ρ Q =
      armsDisj xv j (arms.map fun a => Stmt.wpList C rd kret a ρ Q) := by
  induction arms with
  | nil => intro j ρ; rw [Stmt.wpArms, List.map_nil, armsDisj]
  | cons a as ih => intro j ρ; rw [Stmt.wpArms, List.map_cons, armsDisj, ih]

theorem wp_match (x : V) (arms : List (List Stmt)) :
    Stmt.wp C rd kret (.match_ x arms) ρ Q = getv ρ x fun ρ xv =>
      armsDisj xv 0 (arms.map fun a => Stmt.wpList C rd kret a ρ Q) := by
  rw [Stmt.wp]
  simp only [wpArms_eq]

theorem wp_call (f : String) (args rets : List V) :
    Stmt.wp C rd kret (.call f args rets) ρ Q =
      getvs ρ args fun ρ as => getvs ρ rets fun ρ rs => C f as rs ∧ Q ρ := rfl

theorem wp_callIf (c : V) (f : String) (args : List V) :
    Stmt.wp C rd kret (.callIf c f args) ρ Q = getv ρ c fun ρ x => getvs ρ args fun ρ as =>
      (IsInK x ∧ (x ≠ 0 → C f as [])) ∧ Q ρ := rfl

theorem wp_dispatch (x : V) (fs : List String) (args rets : List V) :
    Stmt.wp C rd kret (.dispatch x fs args rets) ρ Q = getv ρ x fun ρ xv =>
      getvs ρ args fun ρ as => getvs ρ rets fun ρ rs =>
        (∃ (j : Nat) (h : j < fs.length), xv = ofK (addressOfIndex j) ∧ C fs[j] as rs) ∧ Q ρ := rfl

theorem wp_ret (vs : List V) :
    Stmt.wp C rd kret (.ret vs) ρ Q = getvs ρ vs fun _ xs => kret xs := rfl

end Equations

/-! ## Some valuation agrees with the environment -/

/-- `σ` gives every defined value its word. -/
def Agree (ρ : Env) (σ : Val) : Prop := ∀ v x, ρ v = some x → σ v = x

/-- `ρ'` defines what `ρ` defines, alike. -/
def Le (ρ ρ' : Env) : Prop := ∀ v x, ρ v = some x → ρ' v = some x

theorem Le.refl (ρ : Env) : Le ρ ρ := fun _ _ h => h

theorem Le.trans {a b c : Env} (h : Le a b) (h' : Le b c) : Le a c :=
  fun v x hv => h' v x (h v x hv)

theorem le_upd {ρ : Env} {v : V} (hv : ρ v = none) (x : E) : Le ρ (ρ.upd v x) := by
  intro w y hw
  rw [Env.upd_apply]
  split
  · subst w; rw [hv] at hw; cases hw
  · exact hw

theorem upd_self (ρ : Env) (v : V) (x : E) : ρ.upd v x v = some x := by simp [Env.upd_apply]

theorem Agree.mono {ρ ρ' : Env} {σ : Val} (h : Agree ρ' σ) (hl : Le ρ ρ') : Agree ρ σ :=
  fun v x hv => h v x (hl v x hv)

theorem Agree.upd {ρ : Env} {σ : Val} (h : Agree ρ σ) (v : V) : Agree (ρ.upd v (σ v)) σ := by
  intro w x hw
  rw [Env.upd_apply] at hw
  split at hw
  · subst w; cases hw; rfl
  · exact h w x hw

/-- Some valuation agrees with every environment: `0` where undefined. -/
theorem agree_getD (ρ : Env) : Agree ρ fun v => (ρ v).getD 0 := fun v x hv => by simp [hv]

/-- A condition at `ρ` is a property of the valuations agreeing with every extension of `ρ`. -/
def Extends (ρ : Env) (Q : Env → Prop) (N : Val → Prop) : Prop :=
  ∀ ρ', Le ρ ρ' → (Q ρ' ↔ ∃ σ, Agree ρ' σ ∧ N σ)

theorem Extends.mono {ρ ρ' : Env} {Q : Env → Prop} {N : Val → Prop} (h : Extends ρ Q N)
    (hl : Le ρ ρ') : Extends ρ' Q N :=
  fun ρ'' hl' => h ρ'' (hl.trans hl')

theorem getv_iff {ρ : Env} {v : V} {Q : Env → E → Prop} {G : E → Val → Prop}
    (hQ : ∀ ρ' x, Le ρ ρ' → ρ' v = some x → (Q ρ' x ↔ ∃ σ, Agree ρ' σ ∧ G x σ)) :
    getv ρ v Q ↔ ∃ σ, Agree ρ σ ∧ G (σ v) σ := by
  unfold getv
  split
  · rename_i x hx
    rw [hQ ρ x (Le.refl ρ) hx]
    exact exists_congr fun σ => and_congr_right fun ag => by rw [ag v x hx]
  · rename_i hx
    constructor
    · rintro ⟨x, hq⟩
      obtain ⟨σ, ag, hg⟩ := (hQ _ x (le_upd hx x) (upd_self ρ v x)).1 hq
      exact ⟨σ, ag.mono (le_upd hx x), by rwa [ag v x (upd_self ρ v x)]⟩
    · rintro ⟨σ, ag, hg⟩
      exact ⟨σ v, (hQ _ _ (le_upd hx _) (upd_self ρ v _)).2 ⟨σ, ag.upd v, hg⟩⟩

theorem getvs_iff (vs : List V) : ∀ {ρ : Env} {Q : Env → List E → Prop} {G : List E → Val → Prop},
    (∀ ρ' xs, Le ρ ρ' → vs.map ρ' = xs.map some → (Q ρ' xs ↔ ∃ σ, Agree ρ' σ ∧ G xs σ)) →
      (getvs ρ vs Q ↔ ∃ σ, Agree ρ σ ∧ G (vs.map σ) σ) := by
  induction vs with
  | nil => intro ρ Q G hQ; exact hQ ρ [] (Le.refl ρ) rfl
  | cons v vs ih =>
    intro ρ Q G hQ
    refine getv_iff (G := fun x σ => G (x :: vs.map σ) σ) fun ρ' x hl hx => ?_
    refine ih (G := fun xs σ => G (x :: xs) σ) fun ρ'' xs hl' hxs => ?_
    exact hQ ρ'' (x :: xs) (hl.trans hl') (by simp [hl' v x hx, hxs])

/-- Read some values, then a condition on their words and the rest. -/
theorem reads_iff {ρ : Env} {vs : List V} {P : List E → Prop} {Q : Env → Prop} {N : Val → Prop}
    (hQ : Extends ρ Q N) :
    getvs ρ vs (fun ρ' xs => P xs ∧ Q ρ') ↔ ∃ σ, Agree ρ σ ∧ P (vs.map σ) ∧ N σ :=
  getvs_iff vs (G := fun xs σ => P xs ∧ N σ) fun ρ' _ hl _ => by
    rw [hQ ρ' hl]
    exact ⟨fun ⟨hp, σ, ag, hn⟩ => ⟨σ, ag, hp, hn⟩, fun ⟨σ, ag, hp, hn⟩ => ⟨hp, σ, ag, hn⟩⟩

/-- **An atom's relation on its values' words is its relation.** -/
theorem Atom.rel_map (rd : Reader) (σ : Val) (a : Atom) :
    a.rel rd (a.vars.map σ) ↔ a.Holds rd σ := by
  cases a with
  | keccak ins outs i o =>
    simp only [Atom.vars, List.map_append, Atom.rel, Atom.Holds]
    refine and_congr_right fun hi => ?_
    have hl : (ins.map σ).length = 13 := by rw [List.length_map, hi]
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
  | frameAddr p run =>
    simp only [Atom.vars, List.map_cons, Atom.rel, Atom.Holds]
    refine and_congr_right fun _ => forall_congr' fun k => forall_congr' fun hk => ?_
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  | _ => simp only [Atom.vars, List.map_cons, List.map_nil, Atom.rel, Atom.Holds]

theorem Atom.wp_iff (rd : Reader) (a : Atom) {ρ : Env} {Q : Env → Prop} {N : Val → Prop}
    (hQ : Extends ρ Q N) : a.wp rd ρ Q ↔ ∃ σ, Agree ρ σ ∧ a.Holds rd σ ∧ N σ := by
  rw [Atom.wp, reads_iff hQ]
  simp only [Atom.rel_map]

theorem armsDisj_iff (C : CallRel) (rd : Reader) (kret : List E → Prop) (x : V) (xv : E) :
    ∀ (arms : List (List Stmt)) (j : Nat) (ρ : Env) (_ : ρ x = some xv) (Q : Env → Prop)
    (N : Val → Prop), (∀ a ∈ arms, Stmt.wpList C rd kret a ρ Q ↔
        ∃ σ, Agree ρ σ ∧ Stmt.HoldsList C rd σ a (N σ) kret) →
      (armsDisj xv j (arms.map fun a => Stmt.wpList C rd kret a ρ Q) ↔
        ∃ σ, Agree ρ σ ∧ Stmt.HoldsArms C rd σ x j arms (N σ) kret)
  | [], j, ρ, _, Q, N, _ => by simp only [List.map_nil, armsDisj, Stmt.HoldsArms, and_false,
      exists_false]
  | a :: as, j, ρ, hx, Q, N, h => by
    rw [List.map_cons, armsDisj, armsDisj_iff C rd kret x xv as (j + 1) ρ hx Q N
      fun a' ha' => h a' (List.mem_cons_of_mem a ha'), h a (List.mem_cons_self ..)]
    simp only [Stmt.HoldsArms]
    constructor
    · rintro (⟨e, σ, ag, h⟩ | ⟨σ, ag, h⟩)
      · exact ⟨σ, ag, .inl ⟨(ag x xv hx).trans e, h⟩⟩
      · exact ⟨σ, ag, .inr h⟩
    · rintro ⟨σ, ag, ⟨e, h⟩ | h⟩
      · exact .inl ⟨(ag x xv hx).symm.trans e, σ, ag, h⟩
      · exact .inr ⟨σ, ag, h⟩

mutual
theorem Stmt.wp_iff (C : CallRel) (rd : Reader) (kret : List E → Prop) :
    ∀ (s : Stmt) {ρ : Env} {Q : Env → Prop} {N : Val → Prop}, Extends ρ Q N →
      (Stmt.wp C rd kret s ρ Q ↔ ∃ σ, Agree ρ σ ∧ Stmt.Holds C rd σ s (N σ) kret)
  | .atom a, ρ, Q, N, hQ => by rw [Stmt.wp, Atom.wp_iff rd a hQ]; simp only [Stmt.Holds]
  | .call f args rets, ρ, Q, N, hQ => by
    rw [Stmt.wp]
    exact getvs_iff args (G := fun as σ => C f as (rets.map σ) ∧ N σ)
      fun ρ' as hl _ => reads_iff (P := C f as) (hQ.mono hl)
  | .callIf c f args, ρ, Q, N, hQ => by
    rw [Stmt.wp]
    refine (getv_iff (G := fun x σ => (IsInK x ∧ (x ≠ 0 → C f (args.map σ) [])) ∧ N σ)
      fun ρ' x hl _ => reads_iff (P := fun as => IsInK x ∧ (x ≠ 0 → C f as [])) (hQ.mono hl)).trans
        ?_
    simp only [Stmt.Holds, and_assoc]
  | .dispatch x fs args rets, ρ, Q, N, hQ => by
    rw [Stmt.wp]
    exact getv_iff (G := fun xv σ => (∃ (j : Nat) (h : j < fs.length),
        xv = ofK (addressOfIndex j) ∧ C fs[j] (args.map σ) (rets.map σ)) ∧ N σ)
      fun ρ' xv hl _ => getvs_iff args (G := fun as σ => (∃ (j : Nat) (h : j < fs.length),
        xv = ofK (addressOfIndex j) ∧ C fs[j] as (rets.map σ)) ∧ N σ)
        fun ρ'' as hl' _ => reads_iff (P := fun rs => ∃ (j : Nat) (h : j < fs.length),
          xv = ofK (addressOfIndex j) ∧ C fs[j] as rs) (hQ.mono (hl.trans hl'))
  | .ret vs, ρ, Q, N, _ => by
    rw [Stmt.wp]
    exact getvs_iff vs (G := fun xs _ => kret xs)
      fun ρ' _ _ _ => ⟨fun h => ⟨_, agree_getD ρ', h⟩, fun ⟨_, _, h⟩ => h⟩
  | .ite c z n, ρ, Q, N, hQ => by
    rw [Stmt.wp]
    refine (getv_iff (G := fun x σ => IsInK x ∧ (x = 0 → Stmt.HoldsList C rd σ z (N σ) kret) ∧
      (x ≠ 0 → Stmt.HoldsList C rd σ n (N σ) kret)) fun ρ1 x l1 hx => ?_).trans
      (by simp only [Stmt.Holds])
    have hz := Stmt.wpList_iff C rd kret z (hQ.mono l1)
    have hn := Stmt.wpList_iff C rd kret n (hQ.mono l1)
    by_cases hx0 : x = 0 <;> simp [hx0, hz, hn, and_left_comm]
  | .match_ x arms, ρ, Q, N, hQ => by
    rw [wp_match]
    refine (getv_iff (G := fun _ σ => Stmt.HoldsArms C rd σ x 0 arms (N σ) kret)
      fun ρ1 xv l1 hx => ?_).trans (by simp only [Stmt.Holds])
    exact armsDisj_iff C rd kret x xv arms 0 ρ1 hx Q N fun a _ =>
      Stmt.wpList_iff C rd kret a (hQ.mono l1)
/-- **The invariant**: a block's condition at `ρ` holds exactly when some valuation agreeing with
`ρ` satisfies the block, `Q` being the condition of what follows and `N` its relational form. -/
theorem Stmt.wpList_iff (C : CallRel) (rd : Reader) (kret : List E → Prop) :
    ∀ (ss : List Stmt) {ρ : Env} {Q : Env → Prop} {N : Val → Prop}, Extends ρ Q N →
      (Stmt.wpList C rd kret ss ρ Q ↔ ∃ σ, Agree ρ σ ∧ Stmt.HoldsList C rd σ ss (N σ) kret)
  | [], ρ, Q, N, hQ => by rw [Stmt.wpList, hQ ρ (Le.refl ρ)]; simp only [Stmt.HoldsList]
  | s :: ss, ρ, Q, N, hQ => by
    rw [Stmt.wpList, Stmt.wp_iff C rd kret s (N := fun σ => Stmt.HoldsList C rd σ ss (N σ) kret)
      fun ρ' hl => Stmt.wpList_iff C rd kret ss (hQ.mono hl)]
    simp only [Stmt.HoldsList]
end

/-! ## A `KECCAK`'s written cells

Rules for the condition: an atom writing one, two or thirteen cells defines them as cells of
Keccak-f of the cells it reads, so each is substituted. -/

section Keccak

variable {I : Fin 13 → E} {i o : Bool}

theorem keccak_cells_one {y : E} :
    (∃ oc : KeccakOutputCells, 1 = oc.cellCount ∧ KeccakCellsRelation I i (cells13 [y]) o oc) ↔
      y = cellsOfState (keccakF1600 (stateOfCells I i)) o 0 := by
  constructor
  · rintro ⟨oc, h, hk⟩
    exact hk 0 (by omega)
  · intro h
    exact ⟨.one, rfl, fun c hc => by
      obtain rfl : c = 0 := Fin.ext (by simp [KeccakOutputCells.cellCount] at hc; omega)
      exact h⟩

theorem keccak_cells_two {y₀ y₁ : E} :
    (∃ oc : KeccakOutputCells, 2 = oc.cellCount ∧ KeccakCellsRelation I i (cells13 [y₀, y₁]) o oc) ↔
      y₀ = cellsOfState (keccakF1600 (stateOfCells I i)) o 0 ∧
        y₁ = cellsOfState (keccakF1600 (stateOfCells I i)) o 1 := by
  constructor
  · rintro ⟨oc, h, hk⟩
    exact ⟨hk 0 (by omega), hk 1 (by omega)⟩
  · rintro ⟨h₀, h₁⟩
    refine ⟨.two, rfl, fun c hc => ?_⟩
    simp only [KeccakOutputCells.cellCount] at hc
    match c, hc with
    | 0, _ => exact h₀
    | 1, _ => exact h₁

theorem keccak_cells_all {O : List E} (hO : O.length = 13) :
    (∃ oc : KeccakOutputCells, 13 = oc.cellCount ∧ KeccakCellsRelation I i (cells13 O) o oc) ↔
      let F := cellsOfState (keccakF1600 (stateOfCells I i)) o
      O = [F 0, F 1, F 2, F 3, F 4, F 5, F 6, F 7, F 8, F 9, F 10, F 11, F 12] := by
  have hall : ∀ oc : KeccakOutputCells, 13 = oc.cellCount → oc = .all := by
    intro oc h; cases oc <;> simp [KeccakOutputCells.cellCount] at h ⊢
  match O, hO with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _], _ =>
    constructor
    · rintro ⟨oc, h, hk⟩
      obtain rfl := hall oc h
      simp only [List.cons.injEq, and_true]
      exact ⟨hk 0 (by decide), hk 1 (by decide), hk 2 (by decide), hk 3 (by decide),
        hk 4 (by decide), hk 5 (by decide), hk 6 (by decide), hk 7 (by decide), hk 8 (by decide),
        hk 9 (by decide), hk 10 (by decide), hk 11 (by decide), hk 12 (by decide)⟩
    · intro h
      refine ⟨.all, rfl, fun c _ => ?_⟩
      simp only [List.cons.injEq, and_true] at h
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
      fin_cases c <;> assumption

end Keccak

/-- **A function's relation is its forward condition**: its parameters read from the empty
environment are the arguments, and its body's condition holds, returning `rets`. -/
theorem Fn.sem_iff_wp (C : CallRel) (rd : Reader) (f : Fn) (args rets : List E) :
    f.Sem C rd args rets ↔ getvs Env.empty f.params fun ρ xs => xs = args ∧
      Stmt.wpList C rd (fun rs => rs = rets) f.body ρ fun _ => False := by
  rw [Fn.Sem, reads_iff (P := (· = args)) (N := fun σ => Stmt.HoldsList C rd σ f.body False
      (fun rs => rs = rets))
    fun ρ _ => Stmt.wpList_iff C rd _ f.body fun _ _ => by simp]
  have ag (σ : Val) : Agree Env.empty σ := fun _ x h => (Option.some_ne_none x h.symm).elim
  exact ⟨fun ⟨σ, h⟩ => ⟨σ, ag σ, h⟩, fun ⟨σ, _, h⟩ => ⟨σ, h⟩⟩

end
end LeanVM.Guest.Core
