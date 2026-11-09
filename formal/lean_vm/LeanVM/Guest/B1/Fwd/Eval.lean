/-
  LeanVM.Guest.B1.Fwd.Eval

  An honest valuation of a straight-line body, by evaluation: each value is defined where it first
  occurs, by its atom's rule (a sum, a product, a quotient, a memory word, a `KECCAK` output, a
  limb, an inverse) or by an oracle (a hint's witness, a call's returns).
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.Renumber

/-!
# Forward evaluation

A renumbered function names its values `.n 0, .n 1, …` in order of first occurrence, its
parameters first (`Fn.numbering`). `chk c ss` checks, by kernel evaluation, that the straight-line
statements `ss` (no branch, no `match`) define each value at its first occurrence in a pattern of
its atom (`chkA`): the next value `.n c` and the ones after it are the defined ones, every other
value is older. `ev rd w l ss` extends the words `l` of the values below `c = l.length` by the
defined values' words: an atom's rule (`newA`), or the oracle `w` (hints, a call's returns).

`ev_good`: on `Val.ofArgs (ev rd w args ss)`, every atom satisfies `Good`, its defining equations,
and the parameters keep their words. `holds_of_good`: an atom satisfying `Good` and its side
condition `Side` (a pointer in `K` with a defined word, a nonzero divisor, canonical `KECCAK`
inputs, an assertion) holds. A load through an older value into an older value (a store) is in
`storesOf`; its `Side` is the load itself.
-/

namespace LeanVM.Guest.B1.Fwd

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak

@[expose] public section

/-! ## The checker -/

/-- `v` is a numbered value below `c`. -/
def oldB (c : Nat) (v : V) : Bool := decide (v = .n v.idx) && decide (v.idx < c)

/-- `v` is `.n c`. -/
def isN (c : Nat) (v : V) : Bool := decide (v = .n c)

/-- The values `vs` are `.n c, .n (c + 1), …`. -/
def runB (c : Nat) : List V → Bool
  | [] => true
  | v :: vs => isN c v && runB (c + 1) vs

/-- The pattern of an atom at the counter `c`: the counter after it. -/
def chkA (c : Nat) : Atom → Option Nat
  | .const d _ => if isN c d then some (c + 1) else none
  | .add d x y => if isN c d && oldB c x && oldB c y then some (c + 1) else none
  | .mul d x y =>
      if isN c d && oldB c x && oldB c y then some (c + 1)
      else if oldB c d && isN c x && oldB c y then some (c + 1) else none
  | .copy d s => if isN c d && oldB c s then some (c + 1) else none
  | .load d p _ =>
      if oldB c p then (if isN c d then some (c + 1) else if oldB c d then some c else none)
      else none
  | .assertEq x y | .assertInK x y => if oldB c x && oldB c y then some c else none
  | .assertNe x i p => if oldB c x && isN c i && isN (c + 1) p then some (c + 2) else none
  | .rangeCheck x y t1 t2 k =>
      if oldB c x && isN c y && isN (c + 1) t1 && isN (c + 2) t2 && oldB c k then some (c + 3)
      else if oldB c x && oldB c y && isN c t1 && isN (c + 1) t2 && isN (c + 2) k then some (c + 3)
      else none
  | .keccak ins outs _ _ =>
      if ins.length == 13 && (outs.length == 1 || outs.length == 2 || outs.length == 13) &&
          ins.all (oldB c) && runB c outs then some (c + outs.length)
      else none
  | .frameAddr p run => if isN c p && run.all (oldB (c + 1)) then some (c + 1) else none
  | .hint (.limbs v ds) =>
      if oldB c v && runB c ds && decide (ds.length ≤ 3) then some (c + ds.length) else none
  | .hint (.inverse x d) => if oldB c x && isN c d then some (c + 1) else none
  | .hint (.witness _ (.stack vs)) => if runB c vs then some (c + vs.length) else none
  | .hint (.witness _ (.heap p _ _)) => if oldB c p then some c else none
  | .hint (.bits v _ _ (.stack ds)) | .hint (.bitsExp v _ (.stack ds)) =>
      if oldB c v && runB c ds then some (c + ds.length) else none
  | .hint (.bits v _ _ (.heap p _ _)) | .hint (.bitsExp v _ (.heap p _ _)) =>
      if oldB c v && oldB c p then some c else none
  | .hint (.digitsExp v _ _ _ _ sc (.stack ds)) =>
      if (v :: sc.toList).all (oldB c) && runB c ds then some (c + ds.length) else none
  | .hint (.digitsExp v _ _ _ _ sc (.heap p _ _)) =>
      if (v :: sc.toList).all (oldB c) && oldB c p then some c else none
  | .hint (.windowsExp v _ _ _ (.stack ds)) =>
      if oldB c v && runB c ds then some (c + ds.length) else none
  | .hint (.windowsExp v _ _ _ (.heap p _ _)) => if oldB c v && oldB c p then some c else none
  | .hint (.log2Ceil b _ _ dst) => if b.vals.all (oldB c) && isN c dst then some (c + 1) else none
  | .hint (.alloc d _) => if isN c d then some (c + 1) else none
  | .hint (.allocDyn d s) => if isN c d && oldB c s then some (c + 1) else none

/-- The pattern of a statement: an atom's, or a call defining its returns. -/
def chkS (c : Nat) : Stmt → Option Nat
  | .atom a => chkA c a
  | .call _ args rets => if args.all (oldB c) && runB c rets then some (c + rets.length) else none
  | .dispatch x _ args rets =>
      if oldB c x && args.all (oldB c) && runB c rets then some (c + rets.length) else none
  | .callIf x _ args => if oldB c x && args.all (oldB c) then some c else none
  | .ret vs => if vs.all (oldB c) then some c else none
  | _ => none

/-- **The checker**: the counter after the statements. -/
def chk (c : Nat) : List Stmt → Option Nat
  | [] => some c
  | s :: ss => match chkS c s with
    | some c' => chk c' ss
    | none => none

/-- The stores of a load atom at the counter `c`. -/
def storeHd (c : Nat) : Stmt → List Atom
  | .atom (.load d p off) => if oldB c d then [.load d p off] else []
  | _ => []

/-- The loads into older values (stores). -/
def storesOf (c : Nat) : List Stmt → List Atom
  | [] => []
  | s :: ss => storeHd c s ++ storesOf ((chkS c s).getD c) ss

/-! ## The evaluator -/

/-- The word at `p·g^k`, or `0`. -/
noncomputable def rdAt (rd : Reader) (p : E) (k : Nat) : E := (rd (p.limb 0 * addressOfIndex
    k)).getD 0

/-- The outputs of a `KECCAK` of the words `ws`. -/
def kecOut (ws : List E) (inOdd outOdd : Bool) (c : Nat) : E :=
  if h : c < 13 then cellsOfState (keccakF1600 (stateOfCells (cells13 ws) inOdd)) outOdd ⟨c, h⟩ else 0

/-- Limb `j` of a word, in `K`. -/
def limbAt (x : E) (j : Nat) : E := if h : j < 3 then ofK (x.limb ⟨j, h⟩) else 0

/-- The oracle's words of `n` values from `.n c`. -/
def orc (w : Nat → E) (c n : Nat) : List E := (List.range n).map fun j => w (c + j)

/-- The words an atom defines, after the words `l`. -/
noncomputable def newA (rd : Reader) (w : Nat → E) (l : List E) (a : Atom) : List E :=
  let σ := B1.Val.ofArgs l
  let c := l.length
  match a with
  | .const _ e => [e]
  | .add _ x y => [σ x + σ y]
  | .mul d x y => if isN c d then [σ x * σ y] else [σ d * (σ y)⁻¹]
  | .copy _ s => [σ s]
  | .load d p off => if isN c d then [rdAt rd (σ p) off] else []
  | .assertEq _ _ | .assertInK _ _ => []
  | .assertNe x _ _ => [(σ x)⁻¹, σ x * (σ x)⁻¹]
  | .rangeCheck x y _ _ k =>
      if isN c y then [σ k * (σ x)⁻¹, rdAt rd (σ x) 0, rdAt rd (σ k * (σ x)⁻¹) 0]
      else [rdAt rd (σ x) 0, rdAt rd (σ y) 0, σ x * σ y]
  | .keccak ins outs i o => (List.range outs.length).map (kecOut (ins.map σ) i o)
  | .frameAddr _ _ => [w c]
  | .hint (.limbs v ds) => (List.range ds.length).map (limbAt (σ v))
  | .hint (.inverse x _) => [(σ x)⁻¹]
  | .hint (.witness _ (.stack vs)) => orc w c vs.length
  | .hint (.witness _ (.heap _ _ _)) => []
  | .hint (.bits _ _ _ (.stack ds)) | .hint (.bitsExp _ _ (.stack ds)) => orc w c ds.length
  | .hint (.bits _ _ _ (.heap _ _ _)) | .hint (.bitsExp _ _ (.heap _ _ _)) => []
  | .hint (.digitsExp _ _ _ _ _ _ (.stack ds)) | .hint (.windowsExp _ _ _ _ (.stack ds)) =>
      orc w c ds.length
  | .hint (.digitsExp _ _ _ _ _ _ (.heap _ _ _)) | .hint (.windowsExp _ _ _ _ (.heap _ _ _)) => []
  | .hint (.log2Ceil _ _ _ _) | .hint (.alloc _ _) | .hint (.allocDyn _ _) => [w c]

/-- The words a statement defines. -/
noncomputable def newS (rd : Reader) (w : Nat → E) (l : List E) : Stmt → List E
  | .atom a => newA rd w l a
  | .call _ _ rets | .dispatch _ _ _ rets => orc w l.length rets.length
  | _ => []

/-- **The evaluator.** -/
noncomputable def ev (rd : Reader) (w : Nat → E) : List E → List Stmt → List E
  | l, [] => l
  | l, s :: ss => ev rd w (l ++ newS rd w l s) ss

/-! ## What evaluation gives, and what an atom needs besides -/

/-- **The defining equations of an atom** (a load in `S` is a store: none). -/
def Good (rd : Reader) (S : List Atom) (w : Nat → E) (σ : Val) : Atom → Prop
  | .const d e => σ d = e
  | .add d x y => σ d = σ x + σ y
  | .mul d x y => if x.idx < d.idx ∧ y.idx < d.idx then σ d = σ x * σ y else σ x = σ d * (σ y)⁻¹
  | .copy d s => σ d = σ s
  | .load d p off => Atom.load d p off ∈ S ∨ σ d = rdAt rd (σ p) off
  | .assertEq _ _ | .assertInK _ _ => True
  | .assertNe x i p => σ i = (σ x)⁻¹ ∧ σ p = σ x * σ i
  | .rangeCheck x y t1 t2 k => σ t1 = rdAt rd (σ x) 0 ∧ σ t2 = rdAt rd (σ y) 0 ∧
      (if k.idx < y.idx then σ y = σ k * (σ x)⁻¹ else σ k = σ x * σ y)
  | .keccak ins outs i o => ins.length = 13 ∧
      (outs.length = 1 ∨ outs.length = 2 ∨ outs.length = 13) ∧
      ∀ (c : Fin 13) (hc : c.val < outs.length), σ outs[c.val] =
        cellsOfState (keccakF1600 (stateOfCells (cells13 (ins.map σ)) i)) o c
  | .frameAddr p _ => σ p = w p.idx
  | .hint (.limbs v ds) => ∀ j (h : j < ds.length), σ ds[j] = limbAt (σ v) j
  | .hint (.inverse x d) => σ d = (σ x)⁻¹
  | .hint (.witness _ (.stack vs)) => ∀ v ∈ vs, σ v = w v.idx
  | .hint (.bits _ _ _ (.stack ds)) | .hint (.bitsExp _ _ (.stack ds)) => ∀ v ∈ ds, σ v = w v.idx
  | .hint (.digitsExp _ _ _ _ _ _ (.stack ds)) | .hint (.windowsExp _ _ _ _ (.stack ds)) =>
      ∀ v ∈ ds, σ v = w v.idx
  | .hint (.log2Ceil _ _ _ d) | .hint (.alloc d _) | .hint (.allocDyn d _) => σ d = w d.idx
  | .hint _ => True

/-- **The side condition of an atom**: what its relation asks beyond `Good`. -/
def Side (rd : Reader) (S : List Atom) (σ : Val) : Atom → Prop
  | .mul d x y => if x.idx < d.idx ∧ y.idx < d.idx then True else σ y ≠ 0
  | .load d p off =>
      if Atom.load d p off ∈ S then LoadHolds rd (σ p) off (σ d)
      else IsInK (σ p) ∧ (rd ((σ p).limb 0 * addressOfIndex off)).isSome
  | .assertEq x y => σ x + σ y = 0
  | .assertInK x y => IsInK (σ x) ∧ IsInK (σ y)
  | .assertNe x _ _ => σ x ≠ 0
  | .rangeCheck x y _ _ k =>
      IsInK (σ x) ∧ (rd ((σ x).limb 0 * addressOfIndex 0)).isSome ∧ IsInK (σ y) ∧
        (rd ((σ y).limb 0 * addressOfIndex 0)).isSome ∧ (if k.idx < y.idx then σ x ≠ 0 else True)
  | .keccak ins _ _ _ => ∀ c : Fin 13, IsCanonical128 (cells13 (ins.map σ) c)
  | .frameAddr p run => Atom.Holds rd σ (.frameAddr p run)
  | _ => True

theorem load_of_rdAt {rd : Reader} {p d : E} {off : Nat} (hd : d = rdAt rd p off) (hp : IsInK p)
    (hs : (rd (p.limb 0 * addressOfIndex off)).isSome) : LoadHolds rd p off d := by
  refine ⟨hp, ?_⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  rw [hd, rdAt, hv]
  rfl

/-- **An atom with its equations and its side condition holds.** -/
theorem holds_of_good {rd : Reader} {S : List Atom} {w : Nat → E} {σ : Val} {a : Atom}
    (hg : Good rd S w σ a) (hs : Side rd S σ a) : a.Holds rd σ := by
  cases a with
  | const d e => exact hg
  | add d x y => exact hg
  | mul d x y =>
    simp only [Good, Side] at hg hs
    show σ d = σ x * σ y
    split at hg
    · exact hg
    · rename_i h
      rw [ite_neg' h] at hs
      rw [hg, mul_assoc, inv_mul_cancel₀ hs, mul_one]
  | copy d s => exact hg
  | load d p off =>
    simp only [Good, Side] at hg hs
    show LoadHolds rd (σ p) off (σ d)
    split at hs
    · exact hs
    · rename_i h
      rcases hg with hg | hg
      · exact absurd hg h
      · exact load_of_rdAt hg hs.1 hs.2
  | assertEq x y => exact hs
  | assertNe x i p =>
    simp only [Good, Side] at hg hs
    obtain ⟨h1, h2⟩ := hg
    refine ⟨h2, ?_⟩
    rw [h2, h1, mul_inv_cancel₀ hs]
  | rangeCheck x y t1 t2 k =>
    simp only [Good, Side] at hg hs
    obtain ⟨h1, h2, h3⟩ := hg
    obtain ⟨px, sx, py, sy, h0⟩ := hs
    refine ⟨load_of_rdAt h1 px sx, ?_, load_of_rdAt h2 py sy⟩
    split at h3
    · rename_i h
      rw [ite_pos' h] at h0
      rw [h3, mul_comm (σ k), ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
    · exact h3
  | assertInK x y => exact hs
  | keccak ins outs i o =>
    obtain ⟨h1, h2, h3⟩ := hg
    have hk : KeccakCellsRelation (cells13 (ins.map σ)) i
        (cellsOfState (keccakF1600 (stateOfCells (cells13 (ins.map σ)) i)) o) o .all :=
      ⟨hs, fun _ _ ↦ rfl⟩
    rcases h2 with h2 | h2 | h2
    · exact keccak_holds_of (oc := .one) h1 h2 hk h3
    · exact keccak_holds_of (oc := .two) h1 h2 hk h3
    · exact keccak_holds_of (oc := .all) h1 h2 hk h3
  | frameAddr p run => exact hs
  | hint h => trivial

/-- **A thirteen-cell `KECCAK`'s equations** in the form of the written cells' `cells13`. -/
theorem good_keccak13 {rd : Reader} {S : List Atom} {w : Nat → E} {σ : Val} {ins outs : List V}
    {i o : Bool} (hg : Good rd S w σ (.keccak ins outs i o))
    (ho : outs.length = 13 := by first | rfl | simp) :
    ins.length = 13 ∧ outs.length = 13 ∧ ∀ c : Fin 13, cells13 (outs.map σ) c =
      cellsOfState (keccakF1600 (stateOfCells (cells13 (ins.map σ)) i)) o c := by
  obtain ⟨h1, -, h3⟩ := hg
  refine ⟨h1, ho, fun c => ?_⟩
  rw [cells13, List.getD_eq_getElem _ _ (by simp [ho]), List.getElem_map]
  exact h3 c (by omega)

/-! ## The checker's facts -/

theorem oldB_spec {c : Nat} {v : V} (h : oldB c v = true) : v = .n v.idx ∧ v.idx < c := by
  simpa [oldB] using h

theorem isN_spec {c : Nat} {v : V} (h : isN c v = true) : v = .n c := by
  simpa [isN] using h

theorem runB_spec : ∀ {c : Nat} {vs : List V}, runB c vs = true →
    ∀ j (hj : j < vs.length), vs[j] = .n (c + j)
  | _, [], _, j, hj => absurd hj (by simp)
  | c, v :: vs, h, j, hj => by
    simp only [runB, Bool.and_eq_true] at h
    rcases j with _ | j
    · simpa using isN_spec h.1
    · have := runB_spec h.2 j (by simpa using hj)
      simp only [List.getElem_cons_succ, this]
      congr 1
      omega

theorem runB_mem {c : Nat} {vs : List V} (h : runB c vs = true) {v : V} (hv : v ∈ vs) :
    v = .n v.idx ∧ c ≤ v.idx ∧ v.idx < c + vs.length := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  rw [runB_spec h j hj]
  exact ⟨rfl, by simp, by simp; omega⟩

theorem ofArgs_old {l m : List E} {v : V} (h : v.idx < l.length) :
    B1.Val.ofArgs (l ++ m) v = B1.Val.ofArgs l v := by
  simp only [B1.Val.ofArgs, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem ofArgs_new (l m : List E) (j : Nat) :
    B1.Val.ofArgs (l ++ m) (.n (l.length + j)) = m.getD j 0 := by
  simp only [B1.Val.ofArgs, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem ofArgs_newV (l m : List E) {v : V} {j : Nat} (hv : v = .n (l.length + j)) :
    B1.Val.ofArgs (l ++ m) v = m.getD j 0 := by
  rw [hv, ofArgs_new]

theorem ofArgs_new0 (l m : List E) {v : V} (hv : v = .n l.length) :
    B1.Val.ofArgs (l ++ m) v = m.getD 0 0 := by
  rw [hv, ← ofArgs_new l m 0]; rfl


/-! ## One step -/

/-- What a statement's evaluation gives: an atom's equations, a call's oracle returns. -/
def GoodS (rd : Reader) (S : List Atom) (w : Nat → E) (σ : Val) : Stmt → Prop
  | .atom a => Good rd S w σ a
  | .call _ _ rets | .dispatch _ _ _ rets => ∀ v ∈ rets, σ v = w v.idx
  | _ => True

theorem good_mono {rd : Reader} {S S' : List Atom} {w : Nat → E} {σ : Val} {a : Atom}
    (hS : ∀ b ∈ S, b ∈ S') (h : Good rd S w σ a) : Good rd S' w σ a := by
  cases a with
  | load d p off =>
    rcases h with h | h
    · exact Or.inl (hS _ h)
    · exact Or.inr h
  | hint hh =>
    cases hh with
    | witness _ dd => cases dd <;> exact h
    | bits _ _ _ dd => cases dd <;> exact h
    | bitsExp _ _ dd => cases dd <;> exact h
    | digitsExp _ _ _ _ _ _ dd => cases dd <;> exact h
    | windowsExp _ _ _ _ dd => cases dd <;> exact h
    | _ => exact h
  | _ => exact h

theorem goodS_mono {rd : Reader} {S S' : List Atom} {w : Nat → E} {σ : Val} {s : Stmt}
    (hS : ∀ b ∈ S, b ∈ S') (h : GoodS rd S w σ s) : GoodS rd S' w σ s := by
  cases s with
  | atom a => exact good_mono hS h
  | _ => exact h

theorem good_congr {rd : Reader} {S : List Atom} {w : Nat → E} {σ σ' : Val} {a : Atom}
    (he : ∀ v ∈ a.vals, σ v = σ' v) (h : Good rd S w σ a) : Good rd S w σ' a := by
  cases a with
  | const d e =>
    simp only [Good, Atom.vals, List.mem_singleton, forall_eq] at h he ⊢; rwa [← he]
  | add d x y =>
    simp only [Good, Atom.vals, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h he ⊢
    rwa [← he.1, ← he.2.1, ← he.2.2]
  | mul d x y =>
    simp only [Good, Atom.vals, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h he ⊢
    rwa [← he.1, ← he.2.1, ← he.2.2]
  | copy d s =>
    simp only [Good, Atom.vals, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h he ⊢
    rwa [← he.1, ← he.2]
  | load d p off =>
    simp only [Good, Atom.vals, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h he ⊢
    rwa [← he.1, ← he.2]
  | assertEq x y => trivial
  | assertInK x y => trivial
  | assertNe x i p =>
    simp only [Good, Atom.vals, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h he ⊢
    rwa [← he.1, ← he.2.1, ← he.2.2]
  | rangeCheck x y t1 t2 k =>
    simp only [Good, Atom.vals, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h he ⊢
    rwa [← he.1, ← he.2.1, ← he.2.2.1, ← he.2.2.2.1, ← he.2.2.2.2]
  | keccak ins outs i o =>
    simp only [Good] at h ⊢
    have e1 : ins.map σ = ins.map σ' :=
      List.map_congr_left fun v hv => he v (by simp [Atom.vals, hv])
    refine ⟨h.1, h.2.1, fun c hc => ?_⟩
    rw [← e1, ← he _ (by simp [Atom.vals, List.getElem_mem])]
    exact h.2.2 c hc
  | frameAddr p run =>
    simp only [Good] at h ⊢
    rw [← he p (by simp [Atom.vals])]; exact h
  | hint hh =>
    cases hh with
    | limbs v ds =>
      simp only [Good] at h ⊢
      intro j hj
      rw [← he _ (by simp [Atom.vals, Hint.vals]), ← he v (by simp [Atom.vals, Hint.vals])]
      exact h j hj
    | inverse x d =>
      simp only [Good] at h ⊢
      rw [← he d (by simp [Atom.vals, Hint.vals]), ← he x (by simp [Atom.vals, Hint.vals])]
      exact h
    | witness s dd =>
      cases dd with
      | stack vs =>
        simp only [Good] at h ⊢
        intro v hv
        rw [← he v (by simp [Atom.vals, Hint.vals, Dest.vals, hv])]; exact h v hv
      | heap => trivial
    | bits v st nb dd =>
      cases dd with
      | stack vs =>
        simp only [Good] at h ⊢
        intro u hu
        rw [← he u (by simp [Atom.vals, Hint.vals, Dest.vals, hu])]; exact h u hu
      | heap => trivial
    | bitsExp v nb dd =>
      cases dd with
      | stack vs =>
        simp only [Good] at h ⊢
        intro u hu
        rw [← he u (by simp [Atom.vals, Hint.vals, Dest.vals, hu])]; exact h u hu
      | heap => trivial
    | digitsExp v nb nd db st sc dd =>
      cases dd with
      | stack vs =>
        simp only [Good] at h ⊢
        intro u hu
        rw [← he u (by simp [Atom.vals, Hint.vals, Dest.vals, hu])]; exact h u hu
      | heap => trivial
    | windowsExp v st wd ct dd =>
      cases dd with
      | stack vs =>
        simp only [Good] at h ⊢
        intro u hu
        rw [← he u (by simp [Atom.vals, Hint.vals, Dest.vals, hu])]; exact h u hu
      | heap => trivial
    | log2Ceil b nb fl d =>
      simp only [Good] at h ⊢
      rw [← he d (by simp [Atom.vals, Hint.vals])]; exact h
    | alloc d n =>
      simp only [Good] at h ⊢
      rw [← he d (by simp [Atom.vals, Hint.vals])]; exact h
    | allocDyn d s =>
      simp only [Good] at h ⊢
      rw [← he d (by simp [Atom.vals, Hint.vals])]; exact h

theorem goodS_congr {rd : Reader} {S : List Atom} {w : Nat → E} {σ σ' : Val} {s : Stmt}
    (he : ∀ v ∈ s.vals, σ v = σ' v) (h : GoodS rd S w σ s) : GoodS rd S w σ' s := by
  cases s with
  | atom a => exact good_congr he h
  | call f args rets =>
    intro v hv
    rw [← he v (by simp [Stmt.vals, hv])]; exact h v hv
  | dispatch x fs args rets =>
    intro v hv
    rw [← he v (by simp [Stmt.vals, hv])]; exact h v hv
  | _ => trivial


section step

variable (rd : Reader) (w : Nat → E) (l : List E)

local notation "σ₀" => B1.Val.ofArgs l

theorem idx_of_isN {c : Nat} {v : V} (h : isN c v = true) : v.idx = c := by
  rw [isN_spec h]

theorem old_eq {m : List E} {v : V} (h : oldB l.length v = true) :
    B1.Val.ofArgs (l ++ m) v = B1.Val.ofArgs l v := ofArgs_old (oldB_spec h).2

theorem new_at {m : List E} {v : V} {j : Nat} (h : isN (l.length + j) v = true) :
    B1.Val.ofArgs (l ++ m) v = m.getD j 0 := ofArgs_newV l m (isN_spec h)

theorem new_at0 {m : List E} {v : V} (h : isN l.length v = true) :
    B1.Val.ofArgs (l ++ m) v = m.getD 0 0 := ofArgs_new0 l m (isN_spec h)

theorem not_isN_of_old {c : Nat} {v : V} (h : oldB c v = true) : isN c v = false := by
  have := (oldB_spec h).2
  cases hv : isN c v
  · rfl
  · rw [idx_of_isN hv] at this; omega

theorem all_old {c : Nat} {vs : List V} (h : vs.all (oldB c) = true) : ∀ v ∈ vs, oldB c v = true :=
  fun v hv => List.all_eq_true.mp h v hv

/-- **One atom**: its words, the bound of its values, its equations. -/
theorem stepA {a : Atom} {c' : Nat} (h : chkA l.length a = some c') :
    (l ++ newA rd w l a).length = c' ∧ (∀ v ∈ a.vals, v.idx < c') ∧
      Good rd (storeHd l.length (.atom a)) w (B1.Val.ofArgs (l ++ newA rd w l a)) a := by
  cases a with
  | const d e =>
    simp only [chkA] at h
    split at h
    · rename_i hd
      cases h
      refine ⟨by simp [newA], fun v hv => ?_, ?_⟩
      · simp only [Atom.vals, List.mem_singleton] at hv; subst hv; rw [idx_of_isN hd]; omega
      · show B1.Val.ofArgs _ d = e
        rw [new_at0 l hd]; rfl
    · exact absurd h (by simp)
  | add d x y =>
    simp only [chkA] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hd, hx⟩, hy⟩ := hc
      refine ⟨by simp [newA], fun v hv => ?_, ?_⟩
      · simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl
        · rw [idx_of_isN hd]; omega
        · have := (oldB_spec hx).2; omega
        · have := (oldB_spec hy).2; omega
      · show B1.Val.ofArgs _ d = B1.Val.ofArgs _ x + B1.Val.ofArgs _ y
        rw [new_at0 l hd, old_eq l hx, old_eq l hy]; rfl
    · exact absurd h (by simp)
  | mul d x y =>
    simp only [chkA] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hd, hx⟩, hy⟩ := hc
      have hn : newA rd w l (.mul d x y) = [σ₀ x * σ₀ y] := by simp [newA, hd]
      have ix := (oldB_spec hx).2
      have iy := (oldB_spec hy).2
      have id := idx_of_isN hd
      refine ⟨by simp [hn], fun v hv => ?_, ?_⟩
      · simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega
      · simp only [Good]
        rw [ite_pos' ⟨by omega, by omega⟩, hn, new_at0 l hd, old_eq l hx, old_eq l hy]; rfl
    · split at h
      · rename_i _ hc
        cases h
        simp only [Bool.and_eq_true] at hc
        obtain ⟨⟨hd, hx⟩, hy⟩ := hc
        have hn : newA rd w l (.mul d x y) = [σ₀ d * (σ₀ y)⁻¹] := by
          simp [newA, not_isN_of_old hd]
        have id := (oldB_spec hd).2
        have iy := (oldB_spec hy).2
        have ix := idx_of_isN hx
        refine ⟨by simp [hn], fun v hv => ?_, ?_⟩
        · simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl <;> omega
        · simp only [Good]
          rw [ite_neg' (by omega), hn, new_at0 l hx, old_eq l hd, old_eq l hy]; rfl
      · exact absurd h (by simp)
  | copy d s =>
    simp only [chkA] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hd, hs⟩ := hc
      refine ⟨by simp [newA], fun v hv => ?_, ?_⟩
      · simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · rw [idx_of_isN hd]; omega
        · have := (oldB_spec hs).2; omega
      · show B1.Val.ofArgs _ d = B1.Val.ofArgs _ s
        rw [new_at0 l hd, old_eq l hs]; rfl
    · exact absurd h (by simp)
  | load d p off =>
    simp only [chkA] at h
    split at h
    · rename_i hp
      have ip := (oldB_spec hp).2
      split at h
      · rename_i hd
        cases h
        have hn : newA rd w l (.load d p off) = [rdAt rd (σ₀ p) off] := by simp [newA, hd]
        have id := idx_of_isN hd
        refine ⟨by simp [hn], fun v hv => ?_, ?_⟩
        · simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl <;> omega
        · refine Or.inr ?_
          rw [hn, new_at0 l hd, old_eq l hp]; rfl
      · split at h
        · rename_i _ hd
          cases h
          have id := (oldB_spec hd).2
          refine ⟨by simp [newA, not_isN_of_old hd], fun v hv => ?_, ?_⟩
          · simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl <;> omega
          · refine Or.inl ?_
            simp [storeHd, hd]
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  | assertEq x y =>
    simp only [chkA] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      refine ⟨by simp [newA], fun v hv => ?_, trivial⟩
      simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact (oldB_spec hc.1).2
      · exact (oldB_spec hc.2).2
    · exact absurd h (by simp)
  | assertInK x y =>
    simp only [chkA] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      refine ⟨by simp [newA], fun v hv => ?_, trivial⟩
      simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact (oldB_spec hc.1).2
      · exact (oldB_spec hc.2).2
    · exact absurd h (by simp)
  | assertNe x i p =>
    simp only [chkA] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hx, hi⟩, hp⟩ := hc
      have ix := (oldB_spec hx).2
      have ii := idx_of_isN hi
      have ip := idx_of_isN hp
      refine ⟨by simp [newA], fun v hv => ?_, ?_⟩
      · simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega
      · simp only [Good]
        rw [new_at0 l hi, new_at l hp, old_eq l hx]
        exact ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  | rangeCheck x y t1 t2 k =>
    simp only [chkA] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨⟨⟨hx, hy⟩, h1⟩, h2⟩, hk⟩ := hc
      have ix := (oldB_spec hx).2
      have ik := (oldB_spec hk).2
      have iy := idx_of_isN hy
      have i1 := idx_of_isN h1
      have i2 := idx_of_isN h2
      have hn : newA rd w l (.rangeCheck x y t1 t2 k) =
          [σ₀ k * (σ₀ x)⁻¹, rdAt rd (σ₀ x) 0, rdAt rd (σ₀ k * (σ₀ x)⁻¹) 0] := by
        simp [newA, hy]
      refine ⟨by simp [hn], fun v hv => ?_, ?_⟩
      · simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega
      · simp only [Good]
        rw [ite_pos' (by omega), hn, new_at0 l hy, new_at l h1, new_at l h2, old_eq l hx,
          old_eq l hk]
        exact ⟨rfl, rfl, rfl⟩
    · split at h
      · rename_i _ hc
        cases h
        simp only [Bool.and_eq_true] at hc
        obtain ⟨⟨⟨⟨hx, hy⟩, h1⟩, h2⟩, hk⟩ := hc
        have ix := (oldB_spec hx).2
        have iy := (oldB_spec hy).2
        have i1 := idx_of_isN h1
        have i2 := idx_of_isN h2
        have ik := idx_of_isN hk
        have hn : newA rd w l (.rangeCheck x y t1 t2 k) =
            [rdAt rd (σ₀ x) 0, rdAt rd (σ₀ y) 0, σ₀ x * σ₀ y] := by
          simp [newA, not_isN_of_old hy]
        refine ⟨by simp [hn], fun v hv => ?_, ?_⟩
        · simp only [Atom.vals, List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega
        · simp only [Good]
          rw [ite_neg' (by omega), hn, new_at0 l h1, new_at l h2, new_at l hk, old_eq l hx,
            old_eq l hy]
          exact ⟨rfl, rfl, rfl⟩
      · exact absurd h (by simp)
  | keccak ins outs i o =>
    simp only [chkA] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨hl, ho⟩, hin⟩, hout⟩ := hc
      have hn : newA rd w l (.keccak ins outs i o) =
          (List.range outs.length).map (kecOut (ins.map σ₀) i o) := by
        simp [newA]
      have hins : ins.map (B1.Val.ofArgs (l ++ newA rd w l (.keccak ins outs i o))) = ins.map σ₀ :=
        List.map_congr_left fun v hv => old_eq l (all_old hin v hv)
      refine ⟨by simp [hn], fun v hv => ?_, ?_⟩
      · simp only [Atom.vals, List.mem_append] at hv
        rcases hv with hv | hv
        · have := (oldB_spec (all_old hin v hv)).2; omega
        · have := (runB_mem hout hv).2.2; omega
      · refine ⟨hl, by rcases ho with (h | h) | h <;> simp [h], fun c hc => ?_⟩
        rw [hins, runB_spec hout c hc, ofArgs_new, hn]
        simp [kecOut, c.isLt, hc]
    · exact absurd h (by simp)
  | frameAddr p run =>
    simp only [chkA] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hp, hr⟩ := hc
      have ip := idx_of_isN hp
      refine ⟨by simp [newA], fun v hv => ?_, ?_⟩
      · simp only [Atom.vals, List.mem_cons] at hv
        rcases hv with rfl | hv
        · omega
        · exact (oldB_spec (all_old hr v hv)).2
      · show B1.Val.ofArgs _ p = w p.idx
        rw [new_at0 l hp, ip]; rfl
    · exact absurd h (by simp)
  | hint hh =>
    cases hh with
    | limbs v ds =>
      simp only [chkA] at h
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨hv, hds⟩, h3⟩ := hc
        have hn : newA rd w l (.hint (.limbs v ds)) = (List.range ds.length).map (limbAt (σ₀ v)) := by
          simp [newA]
        refine ⟨by simp [hn], fun u hu => ?_, ?_⟩
        · simp only [Atom.vals, Hint.vals, List.mem_cons] at hu
          rcases hu with rfl | hu
          · have := (oldB_spec hv).2; omega
          · have := (runB_mem hds hu).2.2; omega
        · intro j hj
          rw [runB_spec hds j hj, ofArgs_new, old_eq l hv, hn]
          simp [hj]
      · exact absurd h (by simp)
    | inverse x d =>
      simp only [chkA] at h
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true] at hc
        obtain ⟨hx, hd⟩ := hc
        have ix := (oldB_spec hx).2
        have id := idx_of_isN hd
        refine ⟨by simp [newA], fun u hu => ?_, ?_⟩
        · simp only [Atom.vals, Hint.vals, List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;> omega
        · show B1.Val.ofArgs _ d = (B1.Val.ofArgs _ x)⁻¹
          rw [new_at0 l hd, old_eq l hx]; rfl
      · exact absurd h (by simp)
    | witness s dd =>
      cases dd with
      | stack vs =>
        simp only [chkA] at h
        split at h
        · rename_i hc
          cases h
          refine ⟨by simp [newA, orc], fun u hu => ?_, ?_⟩
          · simp only [Atom.vals, Hint.vals, Dest.vals] at hu
            have := (runB_mem hc hu).2.2; omega
          · intro u hu
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
            rw [runB_spec hc j hj, ofArgs_new]
            simp [newA, orc, hj]
        · exact absurd h (by simp)
      | heap p off len =>
        simp only [chkA] at h
        split at h
        · rename_i hc
          cases h
          refine ⟨by simp [newA], fun u hu => ?_, trivial⟩
          simp only [Atom.vals, Hint.vals, Dest.vals, List.mem_singleton] at hu
          subst hu; exact (oldB_spec hc).2
        · exact absurd h (by simp)
    | bits v st nb dd =>
      cases dd with
      | stack ds =>
        simp only [chkA] at h
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true] at hc
          obtain ⟨hv, hds⟩ := hc
          refine ⟨by simp [newA, orc], fun u hu => ?_, ?_⟩
          · simp only [Atom.vals, Hint.vals, Dest.vals, List.mem_cons] at hu
            rcases hu with rfl | hu
            · have := (oldB_spec hv).2; omega
            · have := (runB_mem hds hu).2.2; omega
          · intro u hu
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
            rw [runB_spec hds j hj, ofArgs_new]
            simp [newA, orc, hj]
        · exact absurd h (by simp)
      | heap p off len =>
        simp only [chkA] at h
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true] at hc
          refine ⟨by simp [newA], fun u hu => ?_, trivial⟩
          simp only [Atom.vals, Hint.vals, Dest.vals, List.mem_cons, List.not_mem_nil,
            or_false] at hu
          rcases hu with rfl | rfl
          · exact (oldB_spec hc.1).2
          · exact (oldB_spec hc.2).2
        · exact absurd h (by simp)
    | bitsExp v nb dd =>
      cases dd with
      | stack ds =>
        simp only [chkA] at h
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true] at hc
          obtain ⟨hv, hds⟩ := hc
          refine ⟨by simp [newA, orc], fun u hu => ?_, ?_⟩
          · simp only [Atom.vals, Hint.vals, Dest.vals, List.mem_cons] at hu
            rcases hu with rfl | hu
            · have := (oldB_spec hv).2; omega
            · have := (runB_mem hds hu).2.2; omega
          · intro u hu
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
            rw [runB_spec hds j hj, ofArgs_new]
            simp [newA, orc, hj]
        · exact absurd h (by simp)
      | heap p off len =>
        simp only [chkA] at h
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true] at hc
          refine ⟨by simp [newA], fun u hu => ?_, trivial⟩
          simp only [Atom.vals, Hint.vals, Dest.vals, List.mem_cons, List.not_mem_nil,
            or_false] at hu
          rcases hu with rfl | rfl
          · exact (oldB_spec hc.1).2
          · exact (oldB_spec hc.2).2
        · exact absurd h (by simp)
    | digitsExp v nb nd db st sc dd =>
      cases dd with
      | stack ds =>
        simp only [chkA] at h
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true] at hc
          obtain ⟨hv, hds⟩ := hc
          refine ⟨by simp [newA, orc], fun u hu => ?_, ?_⟩
          · simp only [Atom.vals, Hint.vals, Dest.vals] at hu
            rcases List.mem_cons.mp hu with rfl | hu
            · have := (oldB_spec (all_old hv _ (List.mem_cons_self))).2; omega
            · rcases List.mem_append.mp hu with hu | hu
              · have := (oldB_spec (all_old hv _ (List.mem_cons_of_mem _ hu))).2; omega
              · have := (runB_mem hds hu).2.2; omega
          · intro u hu
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
            rw [runB_spec hds j hj, ofArgs_new]
            simp [newA, orc, hj]
        · exact absurd h (by simp)
      | heap p off len =>
        simp only [chkA] at h
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true] at hc
          refine ⟨by simp [newA], fun u hu => ?_, trivial⟩
          simp only [Atom.vals, Hint.vals, Dest.vals] at hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact (oldB_spec (all_old hc.1 _ (List.mem_cons_self))).2
          · rcases List.mem_append.mp hu with hu | hu
            · exact (oldB_spec (all_old hc.1 _ (List.mem_cons_of_mem _ hu))).2
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
              subst hu; exact (oldB_spec hc.2).2
        · exact absurd h (by simp)
    | windowsExp v st wd ct dd =>
      cases dd with
      | stack ds =>
        simp only [chkA] at h
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true] at hc
          obtain ⟨hv, hds⟩ := hc
          refine ⟨by simp [newA, orc], fun u hu => ?_, ?_⟩
          · simp only [Atom.vals, Hint.vals, Dest.vals, List.mem_cons] at hu
            rcases hu with rfl | hu
            · have := (oldB_spec hv).2; omega
            · have := (runB_mem hds hu).2.2; omega
          · intro u hu
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
            rw [runB_spec hds j hj, ofArgs_new]
            simp [newA, orc, hj]
        · exact absurd h (by simp)
      | heap p off len =>
        simp only [chkA] at h
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true] at hc
          refine ⟨by simp [newA], fun u hu => ?_, trivial⟩
          simp only [Atom.vals, Hint.vals, Dest.vals, List.mem_cons, List.not_mem_nil,
            or_false] at hu
          rcases hu with rfl | rfl
          · exact (oldB_spec hc.1).2
          · exact (oldB_spec hc.2).2
        · exact absurd h (by simp)
    | log2Ceil b nb fl d =>
      simp only [chkA] at h
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true] at hc
        obtain ⟨hb, hd⟩ := hc
        have id := idx_of_isN hd
        refine ⟨by simp [newA], fun u hu => ?_, ?_⟩
        · simp only [Atom.vals, Hint.vals, List.mem_append, List.mem_singleton] at hu
          rcases hu with hu | rfl
          · have := (oldB_spec (all_old hb u hu)).2; omega
          · omega
        · show B1.Val.ofArgs _ d = w d.idx
          rw [new_at0 l hd, id]; rfl
      · exact absurd h (by simp)
    | alloc d n =>
      simp only [chkA] at h
      split at h
      · rename_i hd
        cases h
        have id := idx_of_isN hd
        refine ⟨by simp [newA], fun u hu => ?_, ?_⟩
        · simp only [Atom.vals, Hint.vals, List.mem_singleton] at hu
          subst hu; omega
        · show B1.Val.ofArgs _ d = w d.idx
          rw [new_at0 l hd, id]; rfl
      · exact absurd h (by simp)
    | allocDyn d s =>
      simp only [chkA] at h
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true] at hc
        obtain ⟨hd, hs⟩ := hc
        have id := idx_of_isN hd
        refine ⟨by simp [newA], fun u hu => ?_, ?_⟩
        · simp only [Atom.vals, Hint.vals, List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · omega
          · have := (oldB_spec hs).2; omega
        · show B1.Val.ofArgs _ d = w d.idx
          rw [new_at0 l hd, id]; rfl
      · exact absurd h (by simp)

/-- **One statement.** -/
theorem stepS {s : Stmt} {c' : Nat} (h : chkS l.length s = some c') :
    (l ++ newS rd w l s).length = c' ∧ (∀ v ∈ s.vals, v.idx < c') ∧
      GoodS rd (storeHd l.length s) w (B1.Val.ofArgs (l ++ newS rd w l s)) s := by
  cases s with
  | atom a => exact stepA rd w l h
  | call f args rets =>
    simp only [chkS] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨ha, hr⟩ := hc
      refine ⟨by simp [newS, orc], fun u hu => ?_, ?_⟩
      · simp only [Stmt.vals, List.mem_append] at hu
        rcases hu with hu | hu
        · have := (oldB_spec (all_old ha u hu)).2; omega
        · have := (runB_mem hr hu).2.2; omega
      · intro u hu
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
        rw [runB_spec hr j hj, ofArgs_new]
        simp [newS, orc, hj]
    · exact absurd h (by simp)
  | dispatch x fs args rets =>
    simp only [chkS] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hx, ha⟩, hr⟩ := hc
      refine ⟨by simp [newS, orc], fun u hu => ?_, ?_⟩
      · simp only [Stmt.vals, List.mem_append, List.mem_cons] at hu
        rcases hu with (rfl | hu) | hu
        · have := (oldB_spec hx).2; omega
        · have := (oldB_spec (all_old ha u hu)).2; omega
        · have := (runB_mem hr hu).2.2; omega
      · intro u hu
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
        rw [runB_spec hr j hj, ofArgs_new]
        simp [newS, orc, hj]
    · exact absurd h (by simp)
  | callIf x f args =>
    simp only [chkS] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      refine ⟨by simp [newS], fun u hu => ?_, trivial⟩
      simp only [Stmt.vals, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact (oldB_spec hc.1).2
      · exact (oldB_spec (all_old hc.2 u hu)).2
    · exact absurd h (by simp)
  | ret vs =>
    simp only [chkS] at h
    split at h
    · rename_i hc
      cases h
      refine ⟨by simp [newS], fun u hu => (oldB_spec (all_old hc u hu)).2, trivial⟩
    · exact absurd h (by simp)
  | ite c z n => simp [chkS] at h
  | match_ x arms => simp [chkS] at h

end step

/-- **The evaluator's facts**: the words extend the given ones, and every statement's equations
hold of the final valuation. -/
theorem ev_spec (rd : Reader) (w : Nat → E) : ∀ (ss : List Stmt) (l : List E) {c' : Nat},
    chk l.length ss = some c' →
      (ev rd w l ss).length = c' ∧ (∃ m, ev rd w l ss = l ++ m) ∧
        ∀ s ∈ ss, GoodS rd (storesOf l.length ss) w (B1.Val.ofArgs (ev rd w l ss)) s
  | [], l, c', h => by
    simp only [chk, Option.some.injEq] at h
    subst h
    exact ⟨rfl, ⟨[], by simp [ev]⟩, by simp⟩
  | s :: ss, l, c', h => by
    simp only [chk] at h
    split at h
    · rename_i c1 hc1
      obtain ⟨hl1, hv1, hg1⟩ := stepS rd w l hc1
      have h' : chk (l ++ newS rd w l s).length ss = some c' := by rw [hl1]; exact h
      obtain ⟨hlen, ⟨m, hm⟩, hg⟩ := ev_spec rd w ss _ h'
      have hst : storesOf l.length (s :: ss) = storeHd l.length s ++ storesOf c1 ss := by
        simp [storesOf, hc1]
      refine ⟨hlen, ⟨newS rd w l s ++ m, by simp only [ev]; rw [hm, List.append_assoc]⟩, ?_⟩
      intro t ht
      rw [hst]
      simp only [ev]
      rcases List.mem_cons.mp ht with rfl | ht
      · refine goodS_mono (fun b hb => List.mem_append_left _ hb) (goodS_congr (fun v hv => ?_) hg1)
        rw [hm]
        exact (ofArgs_old (by rw [hl1]; exact hv1 v hv)).symm
      · rw [hl1] at hg
        exact goodS_mono (fun b hb => List.mem_append_right _ hb) (hg t ht)
    · exact absurd h (by simp)

/-- The parameters keep their words. -/
theorem ev_params (rd : Reader) (w : Nat → E) {ss : List Stmt} {l : List E} {c' : Nat}
    (h : chk l.length ss = some c') {i : Nat} (hi : i < l.length) :
    B1.Val.ofArgs (ev rd w l ss) (.n i) = l.getD i 0 := by
  obtain ⟨-, ⟨m, hm⟩, -⟩ := ev_spec rd w ss l h
  rw [hm, ofArgs_old hi]
  rfl

end
end LeanVM.Guest.B1.Fwd
