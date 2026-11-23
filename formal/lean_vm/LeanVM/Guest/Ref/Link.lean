/-
  LeanVM.Guest.Ref.Link

  A compiled function is its reference function: a check the kernel evaluates per specialization,
  and its soundness.
-/

module

public import LeanVM.Guest.Ref.Lang
public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.CoreLemmas
public import LeanVM.Guest.Value.KeccakSponge
public import LeanVM.Guest.Renumber
import LeanVM.Guest.Value.FieldBits

/-!
# Linking a core function to a reference function

`Map.check m f r` compares a core function `f` (`LeanVM.Guest.Core`, renumbered: its values are
`V.n k`) with a reference function `r` (`LeanVM.Guest.Ref`) given a map `m`, and
`Map.check_sem_iff` is what a `true` gives: the two relations are equal. The check is evaluated by
the kernel, once per specialization (`decide +kernel`); `Linked f r` is the check against the
inferred map.

**The check** (`Map.check`) walks the core body and the commands of `r` together, given a `Map`:
the term over `r`'s names of every core value (`Map.h`), and which values are *owners*, each
standing for the name its term is. No two owners have one name (`distinct`).

* `SET`, `XOR`, `MUL` and copies into a value are its definition: its term must be the term of the
  atom's right side, and no command of `r` answers it. So the constants the lowering sets (the
  Keccak padding run, a stored zero), their sharing and the copies into return cells are invisible
  in `r`. Into a known value or an owner (a cell every arm of a `match` writes) they answer a
  `Cmd.eq` of its term and the right side's (`Map.assign`).
* A `DEREF` answers a `Cmd.load`, a `KECCAK` of four cells and the 64-byte padding into two cells a
  `Cmd.hash2` (`keccak_pair_iff`), any other `KECCAK` a `Cmd.keccak`, an `assert` a `Cmd.eq`, a
  range check a `Cmd.range`, a forward branch a `Cmd.ifNz` and a `match` a `Cmd.match_` whose
  arms answer its arms exactly, on equal terms. A hint answers nothing.
* A value is read only once *known*: defined on this path, or the owner of the name its term is
  (a hinted or loaded word, an output cell). A branch's or an arm's definitions are forgotten at
  its join.

The kernel is slow per step of a recursion, so the check spends a bounded number of steps per
value: the known values and the owned names' numbers (`Coded`) are bit sets, and a value's entry
is read from a list by `sfx`, in order of first occurrence.

**Soundness.** From a valuation `σ` of the core values, the names take their owners' words
(`Map.rho`, `Map.rho_owner`); every known value's word is then its term's (`Map.Known`), and each
core atom gives its command (`Map.stmts_fwd`). From a valuation `ρ` of the names, every core value
takes its term's word (`Map.sig`), and each command gives its atom, a definition holding by the
check on terms (`Map.stmts_bwd`).

A `ret` ends the body; calls, a `ret` in a branch and the atoms not listed fail the check.

**The map is inferred** (`infer`) by the same walk, unverified: a wrong map fails the check. A
hinted value is named where a command first reads it, after later values (a value a `ret` reads
first is not named, and the inferred map fails). A function's module computes the map at
elaboration (`LeanVM.Guest.Ref.Elab`) and the kernel checks it (`Map.check_sem_iff`); `Linked`
infers it in the kernel too, which suits small functions only (naming a value late rewrites the
entries after it).

**In pieces.** A body too large for one evaluation is checked in pieces (`Map.Pieces`), each in a
declaration of its own: each piece answers its commands exactly and leaves a given set of values
known for the next (`Map.segOk`); `Map.pieces_fwd_at` and `Map.pieces_sem_iff` are what the pieces
give, `Map.pieces_fwd_at` with the values listed owning their names (`ownersAt`), for statements
that read a hinted value at its value.
-/

namespace LeanVM.Guest.Ref

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Guest.Value.Keccak

@[expose] public section

/-! ## What the kernel evaluates fast -/

/-- The rest of a list from element `k`: one `tail` of the rest from `k - 1`, which the kernel has
evaluated already when the elements are read in order. -/
def sfx {α : Type} (l : List α) : Nat → List α
  | 0 => l
  | k + 1 => (sfx l k).tail

theorem sfx_eq_drop {α : Type} (l : List α) (k : Nat) : sfx l k = l.drop k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sfx, ih, List.tail_drop]

/-- Numbers for names, by which the link check tells the names of two owners apart. Two names of
one number never both pass the check, so the numbers of a function's names are distinct. -/
class Coded (X : Type) where
  code : X → Nat

variable {X : Type} [DecidableEq X]

/-! ## Comparing terms -/

/-- Terms compared structurally, words limb by limb. -/
def Tm.eqb : Tm X → Tm X → Bool
  | .v x, .v y => decide (x = y)
  | .const a, .const b => eEqb a b
  | .add a b, .add a' b' => a.eqb a' && b.eqb b'
  | .mul a b, .mul a' b' => a.eqb a' && b.eqb b'
  | _, _ => false

theorem Tm.eqb_sound : ∀ {a b : Tm X}, a.eqb b = true → a = b
  | .v _, .v _, h => by simpa [Tm.eqb] using h
  | .const a, .const b, h => by
    rw [eEqb_sound (a := a) (b := b) (by simpa [Tm.eqb] using h)]
  | .add _ _, .add _ _, h | .mul _ _, .mul _ _, h => by
    simp only [Tm.eqb, Bool.and_eq_true] at h
    rw [Tm.eqb_sound h.1, Tm.eqb_sound h.2]
  | .v _, .const _, h | .v _, .add .., h | .v _, .mul .., h | .const _, .v _, h
  | .const _, .add .., h | .const _, .mul .., h | .add .., .v _, h | .add .., .const _, h
  | .add .., .mul .., h | .mul .., .v _, h | .mul .., .const _, h | .mul .., .add .., h => by
    simp [Tm.eqb] at h

/-- Term lists compared term by term. -/
def Tm.eqbs : List (Tm X) → List (Tm X) → Bool
  | [], [] => true
  | a :: as, b :: bs => a.eqb b && Tm.eqbs as bs
  | _, _ => false

theorem Tm.eqbs_sound : ∀ {as bs : List (Tm X)}, Tm.eqbs as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [Tm.eqbs, Bool.and_eq_true] at h
    rw [Tm.eqb_sound h.1, Tm.eqbs_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Tm.eqbs] at h

/-! ## The check -/

/-- A link's data: the term of each core value, by index, and whether the value is the owner of
the name its term is (the value that stands for the name). -/
structure Map (X : Type) where
  ent : List (Tm X × Bool)

/-- The entry of a core value. -/
def Map.e (m : Map X) (k : Nat) : Tm X × Bool := (sfx m.ent k).headD (.const 0, false)

/-- The rests of the entries from every `128`th value below `n`, evaluated in order, so that a
check that starts reading at `n` recurses no deeper through `sfx`. Always `true`. It works because
the kernel reuses the `sfx` terms it has evaluated and evaluates `||` left to right. -/
def Map.warm (m : Map X) (n : Nat) : Bool :=
  (List.range (n / 128)).all fun j => (sfx m.ent (128 * j)).isEmpty || true

omit [DecidableEq X] in
theorem Map.e_eq (m : Map X) (k : Nat) : m.e k = (m.ent.drop k).headD (.const 0, false) := by
  rw [Map.e, sfx_eq_drop]

/-- The term of a core value. -/
def Map.h (m : Map X) (d : V) : Tm X := (m.e d.idx).1

/-- The number of the name an entry owns. -/
def ownerCode [Coded X] : Tm X × Bool → Option Nat
  | (.v x, true) => some (Coded.code x)
  | _ => none

/-- No two entries own names of one number, `U` the bit set of the numbers before. -/
def distinct [Coded X] : List (Tm X × Bool) → Nat → Bool
  | [], _ => true
  | e :: l, U =>
      match ownerCode e with
      | some c => !U.testBit c && distinct l (U ||| 1 <<< c)
      | none => distinct l U

/-- Read `d`: it is known already (bit `d.idx` of `K`), or the owner of the name its term is. -/
def Map.use (m : Map X) (K : Nat) (d : V) : Option Nat :=
  if vEqb d (.n d.idx) then
    if K.testBit d.idx then some K
    else match m.e d.idx with
      | (.v _, true) => some (K ||| 1 <<< d.idx)
      | _ => none
  else none

/-- Read each of `ds`. -/
def Map.uses (m : Map X) (K : Nat) : List V → Option Nat
  | [] => some K
  | d :: ds => (m.use K d).bind fun K => m.uses K ds

/-- Define `d` as `t`: its term is `t`. -/
def Map.define (m : Map X) (K : Nat) (d : V) (t : Tm X) : Option Nat :=
  if vEqb d (.n d.idx) && (m.h d).eqb t then some (K ||| 1 <<< d.idx) else none

/-- What a `keccak` of 64 bytes reads after its four message cells: the padding's `0x01`, zeros,
the last rate byte's `0x80`, and the zero capacity. -/
def pad64 : List (Tm X) :=
  [.const (word 1 0), .const (word 0 0), .const (word 0 0), .const (word 0 0),
    .const (word 9223372036854775808 0), .const (word 0 0), .const (word 0 0), .const (word 0 0),
    .const (word 0 0)]

/-- Define `d` as `t`; or, `d` known or an owner, answer the command `a == t'` with `a` its term
and `t'` the term `t`. -/
def Map.assign (m : Map X) (K : Nat) (d : V) (t : Tm X) (rs : List (Cmd X)) :
    Option (Nat × List (Cmd X)) :=
  match m.define K d t, rs with
  | some K, rs => some (K, rs)
  | none, .eq a t' :: rs => (m.use K d).bind fun K =>
      if (m.h d).eqb a && t.eqb t' then some (K, rs) else none
  | none, _ => none

/-- Answer a command reading the values `ds` whose terms are `ts`: read each, compare its term. -/
def Map.answer (m : Map X) (K : Nat) :
    List V → List (Tm X) → List (Cmd X) → Option (Nat × List (Cmd X))
  | [], [], rs => some (K, rs)
  | d :: ds, t :: ts, rs =>
      (m.use K d).bind fun K => if (m.h d).eqb t then m.answer K ds ts rs else none
  | _, _, _ => none

/-- An atom against the commands left: the known values after it and the commands after it. -/
def Map.atom (m : Map X) (K : Nat) : Atom → List (Cmd X) → Option (Nat × List (Cmd X))
  | .const d c, rs => m.assign K d (.const c) rs
  | .copy d s, rs => (m.use K s).bind fun K => m.assign K d (m.h s) rs
  | .add d a b, rs => (m.use K a).bind fun K => (m.use K b).bind fun K =>
      m.assign K d (.add (m.h a) (m.h b)) rs
  | .mul d a b, rs => (m.use K a).bind fun K => (m.use K b).bind fun K =>
      m.assign K d (.mul (m.h a) (m.h b)) rs
  | .load d p off, .load td tp off' :: rs =>
      if off == off' then m.answer K [p, d] [tp, td] rs else none
  | .keccak ins [o0, o1] false false, .hash2 l0 l1 r0 r1 t0 t1 :: rs =>
      m.answer K (ins ++ [o0, o1]) ([l0, l1, r0, r1] ++ pad64 ++ [t0, t1]) rs
  | .keccak ins outs i o, .keccak tins touts i' o' :: rs =>
      if ins.length == tins.length && i == i' && o == o' then
        m.answer K (ins ++ outs) (tins ++ touts) rs
      else none
  | .assertEq a b, .eq ta tb :: rs => m.answer K [a, b] [ta, tb] rs
  | .rangeCheck x y t1 t2 k, .range tx ty tt1 tt2 tk :: rs =>
      m.answer K [x, y, t1, t2, k] [tx, ty, tt1, tt2, tk] rs
  | .hint _, rs => some (K, rs)
  | _, _ => none

/-- A branch on `c` against the commands left, given the check of each of its blocks: they answer
a `Cmd.ifNz`'s blocks, exactly. -/
def Map.branch (m : Map X) (K : Nat) (c : V) (rs : List (Cmd X))
    (zero nonzero : Nat → List (Cmd X) → Option (Nat × List (Cmd X))) :
    Option (Nat × List (Cmd X)) :=
  match rs with
  | .ifNz tc rz rn :: rs => (m.use K c).bind fun K =>
      if (m.h c).eqb tc then
        match zero K rz, nonzero K rn with
        | some (_, []), some (_, []) => some (K, rs)
        | _, _ => none
      else none
  | _ => none

mutual
/-- A statement against the commands left. -/
def Map.stmt (m : Map X) (K : Nat) : Stmt → List (Cmd X) → Option (Nat × List (Cmd X))
  | .atom a, rs => m.atom K a rs
  | .ite c z n, rs =>
      m.branch K c rs (fun K rz => Map.stmts m K z rz) (fun K rn => Map.stmts m K n rn)
  | .match_ x arms, .match_ tc rarms :: rs => (m.use K x).bind fun K =>
      if (m.h x).eqb tc && Map.arms m K arms rarms then some (K, rs) else none
  | .match_ .., _ | .call .., _ | .callIf .., _ | .dispatch .., _ | .ret _, _ => none

/-- A block against the commands left. -/
def Map.stmts (m : Map X) (K : Nat) : List Stmt → List (Cmd X) → Option (Nat × List (Cmd X))
  | [], rs => some (K, rs)
  | s :: ss, rs => (Map.stmt m K s rs).bind fun p => Map.stmts m p.1 ss p.2

/-- A `match`'s arms against the commands' arms: each block answers its commands exactly, from
the values known before the `match`. -/
def Map.arms (m : Map X) (K : Nat) : List (List Stmt) → List (List (Cmd X)) → Bool
  | [], [] => true
  | a :: as, r :: rs =>
      (match Map.stmts m K a r with
        | some (_, []) => true
        | _ => false) && Map.arms m K as rs
  | _, _ => false
end

/-- A `ret` of the returned terms, no command left. -/
def Map.last (m : Map X) (K : Nat) (s : Stmt) (rs : List (Cmd X)) (rets : List (Tm X)) : Bool :=
  match s, rs with
  | .ret vs, [] => (m.uses K vs).isSome && Tm.eqbs (vs.map m.h) rets
  | _, _ => false

/-- A body against all the commands and the returned terms: it ends in a `ret`. -/
def Map.body (m : Map X) (K : Nat) : List Stmt → List (Cmd X) → List (Tm X) → Bool
  | [], _, _ => false
  | s :: ss, rs, rets =>
      m.last K s rs rets ||
        match m.stmt K s rs with
        | some p => Map.body m p.1 ss p.2 rets
        | none => false

/-- The check of a core function against a reference function. -/
def Map.check [Coded X] (m : Map X) (f : Fn) (r : Func X) : Bool :=
  distinct m.ent 0 &&
  match m.uses 0 f.params with
  | some K => Tm.eqbs (f.params.map m.h) (r.params.map .v) && m.body K f.body r.body r.rets
  | none => false

/-! ## Inferring the map -/

/-- The map being inferred: the entries of the values below `n`, last first (`none` for a value
given none yet: a hint is named where it is first read, after later values), and the bit set of
the numbers of the names owned. The core values are numbered in order of first occurrence
(`Fn.renumber`), so an entry is mostly given to the next value, by a `cons`. The kernel evaluates
lazily: each step matches on the state, so that no chain of pending updates builds up. -/
structure Acc (X : Type) where
  rev : List (Option (Tm X × Bool))
  n : Nat
  used : Nat

/-- The entry of a core value so far. -/
def Acc.entry (a : Acc X) (k : Nat) : Option (Tm X × Bool) :=
  bif k.blt a.n then a.rev.getD (a.n - 1 - k) none else none

/-- The term of a core value so far. -/
def Acc.h (a : Acc X) (d : V) : Tm X := ((a.entry d.idx).map Prod.fst).getD (.const 0)

/-- Give `d` the entry `e` unless it has one, `used` the names owned after. -/
def Acc.give (a : Acc X) (d : V) (e : Tm X × Bool) (used : Nat) : Acc X :=
  match a with
  | ⟨rev, n, u⟩ =>
      bif d.idx.blt n then
        bif (rev.getD (n - 1 - d.idx) none).isSome then ⟨rev, n, u⟩
        else ⟨rev.set (n - 1 - d.idx) (some e), n, used⟩
      else ⟨some e :: (List.replicate (d.idx - n) none ++ rev), d.idx + 1, used⟩

/-- Give `d` the term `t`, unless it has one, as the owner of the name `t` is, unless it has
one. -/
def Acc.name [Coded X] (a : Acc X) (d : V) (t : Tm X) : Acc X :=
  match t with
  | .v x => bif a.used.testBit (Coded.code x) then a.give d (t, false) a.used
      else a.give d (t, true) (a.used ||| 1 <<< Coded.code x)
  | _ => a.give d (t, false) a.used

/-- Name each of `ds` by the term in its place. -/
def Acc.names [Coded X] (a : Acc X) : List V → List (Tm X) → Acc X
  | d :: ds, t :: ts =>
      match a.name d t with
      | ⟨rev, n, used⟩ => Acc.names ⟨rev, n, used⟩ ds ts
  | _, _ => a

/-- Define `d` as `t`, or, before the command `x == t` with `x` not owned yet, make it the owner of
`x`; `d` seen already, answer the command `_ == t'` unless `t` is its term. -/
def Acc.assign [Coded X] (a : Acc X) (d : V) (t : Tm X) (rs : List (Cmd X)) :
    Acc X × List (Cmd X) :=
  bif d.idx.blt a.n then
    match rs with
    | .eq _ _ :: rs' => bif (a.h d).eqb t then (a, rs) else (a, rs')
    | rs => (a, rs)
  else
    match rs with
    | .eq (.v x) t' :: rs' =>
        bif t'.eqb t && !a.used.testBit (Coded.code x) then
          (a.give d (.v x, true) (a.used ||| 1 <<< Coded.code x), rs')
        else (a.give d (t, false) a.used, rs)
    | rs => (a.give d (t, false) a.used, rs)

/-- The terms an atom gives. -/
def Acc.atom [Coded X] (a : Acc X) : Atom → List (Cmd X) → Acc X × List (Cmd X)
  | .const d c, rs => a.assign d (.const c) rs
  | .copy d s, rs => a.assign d (a.h s) rs
  | .add d x y, rs => a.assign d (.add (a.h x) (a.h y)) rs
  | .mul d x y, rs => a.assign d (.mul (a.h x) (a.h y)) rs
  | .load d _ _, .load td _ _ :: rs => (a.name d td, rs)
  | .keccak _ [o0, o1] _ _, .hash2 _ _ _ _ t0 t1 :: rs => ((a.name o0 t0).name o1 t1, rs)
  | .keccak ins outs _ _, .keccak tins touts _ _ :: rs => ((a.names ins tins).names outs touts, rs)
  | .assertEq x y, .eq tx ty :: rs => (a.names [x, y] [tx, ty], rs)
  | .rangeCheck x y t1 t2 k, .range tx ty tt1 tt2 tk :: rs =>
      (a.names [x, y, t1, t2, k] [tx, ty, tt1, tt2, tk], rs)
  | _, rs => (a, rs)

mutual
/-- The terms a statement gives. -/
def Acc.stmt [Coded X] (a : Acc X) : Stmt → List (Cmd X) → Acc X × List (Cmd X)
  | .atom x, rs => a.atom x rs
  | .ite _ z n, .ifNz _ rz rn :: rs => ((Acc.stmts (Acc.stmts a z rz).1 n rn).1, rs)
  | .match_ _ arms, .match_ _ rarms :: rs => (Acc.arms a arms rarms, rs)
  | _, rs => (a, rs)

/-- The terms a block gives. -/
def Acc.stmts [Coded X] (a : Acc X) : List Stmt → List (Cmd X) → Acc X × List (Cmd X)
  | [], rs => (a, rs)
  | s :: ss, rs =>
      match Acc.stmt a s rs with
      | (⟨rev, n, used⟩, rs) => Acc.stmts ⟨rev, n, used⟩ ss rs

/-- The terms a `match`'s arms give, in order. -/
def Acc.arms [Coded X] (a : Acc X) : List (List Stmt) → List (List (Cmd X)) → Acc X
  | b :: bs, r :: rs =>
      match (Acc.stmts a b r).1 with
      | ⟨rev, n, used⟩ => Acc.arms ⟨rev, n, used⟩ bs rs
  | _, _ => a
end

/-- The map of a core function and a reference function that agree, inferred by the walk of the
check. -/
def infer [Coded X] (f : Fn) (r : Func X) : Map X :=
  match ((⟨[], 0, 0⟩ : Acc X).names f.params (r.params.map .v)).stmts f.body r.body with
  | (⟨rev, _, _⟩, _) => ⟨rev.reverse.map (·.getD (.const 0, false))⟩

/-- The core function `f` is the reference function `r`, as the kernel evaluates it. -/
def Linked [Coded X] (f : Fn) (r : Func X) : Bool := (infer f r).check f r

/-! ## One `KECCAK` of 64 bytes -/

/-- The digest of 64 bytes: `keccak([a0, a1], [b0, b1], out)` (`keccak_one`). -/
theorem pair_digest (a0 a1 b0 b1 : E) (O : Fin 13 → E)
    (hK : KeccakCellsRelation (cells13 [a0, a1, b0, b1, word 1 0, 0, 0, 0,
      word 9223372036854775808 0, 0, 0, 0, 0]) false O false .all) :
    (O 0, O 1) = digestHalves (keccak256 (cellsBytes [a0, a1, b0, b1])) := by
  have := (keccak_one (cells := [a0, a1, b0, b1]) (len := 64) (by simp) (by decide)
    (getD_cellsBytes_of_le (by simp))
    (fun c hc ↦ by
      fin_cases c <;> simp_all [padCells, xorByte, padRead, rate, byteCell, cells13])
    (fun c hc ↦ by fin_cases c <;> simp_all [cells13]) hK).2
  rwa [List.take_of_length_le (by simp)] at this

/-- **A `KECCAK` of four cells and the 64-byte padding, into two cells**, hashes the pair. -/
theorem keccak_pair_iff {rd : Reader} {σ : Val} {ins : List V} {o0 o1 : V} {a0 a1 b0 b1 : E}
    (hins : ins.map σ = [a0, a1, b0, b1, word 1 0, word 0 0, word 0 0, word 0 0,
      word 9223372036854775808 0, word 0 0, word 0 0, word 0 0, word 0 0]) :
    (Atom.keccak ins [o0, o1] false false).Holds rd σ ↔ HashesPair a0 a1 b0 b1 (σ o0) (σ o1) := by
  simp only [word_zero] at hins
  constructor
  · intro h
    obtain ⟨-, -, O, hKC, hw⟩ := keccak_holds_full h
    rw [hins] at hKC
    rw [HashesPair, show σ o0 = O 0 from hw 0 (by simp), show σ o1 = O 1 from hw 1 (by simp)]
    exact pair_digest _ _ _ _ _ hKC
  · intro hH
    have hS := pair_digest a0 a1 b0 b1 _ (fun _ _ ↦ rfl)
    rw [← hH, Prod.mk.injEq] at hS
    refine keccak_holds_two.mpr ⟨by simpa using congrArg List.length hins, ?_, ?_⟩
    · rw [hins]; exact hS.1.symm
    · rw [hins]; exact hS.2.symm

/-! ## Soundness -/

variable {C : CallRel} {rd : Reader} (m : Map X)

open Classical in
/-- The names' words, from the core values': a name takes its owner's. -/
noncomputable def Map.rho (σ : Val) (x : X) : E :=
  if h : ∃ k, m.e k = (.v x, true) then σ (.n (Classical.choose h)) else 0

/-- The core values' words, from the names': a value takes its term's. -/
def Map.sig (ρ : X → E) : Val := fun d => (m.h d).eval ρ

/-- Every known value's word is its term's, and every name's word its owner's. -/
def Map.Known (σ : Val) (K : Nat) : Prop :=
  (∀ k x, m.e k = (.v x, true) → m.rho σ x = σ (.n k)) ∧
    ∀ k, K.testBit k = true → σ (.n k) = (m.h (.n k)).eval (m.rho σ)

theorem testBit_set {K i k : Nat} (h : (K ||| 1 <<< i).testBit k = true) :
    K.testBit k = true ∨ k = i := by
  rw [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow] at h
  exact h.imp id fun h => (of_decide_eq_true h).symm

variable {m}

omit [DecidableEq X] in
/-- Entries that own names of distinct numbers own distinct names. -/
theorem distinct_spec [Coded X] : ∀ (l : List (Tm X × Bool)) (U : Nat), distinct l U = true →
    (∀ (i c : Nat), l[i]?.bind ownerCode = some c → U.testBit c = false) ∧
      ∀ (i j c : Nat), l[i]?.bind ownerCode = some c → l[j]?.bind ownerCode = some c → i = j
  | [], _, _ => by simp
  | e :: l, U, h => by
    unfold distinct at h
    split at h
    · rename_i c0 hc
      rw [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨ha, hb⟩ := distinct_spec l _ h.2
      have hU : ∀ c, (U ||| 1 <<< c0).testBit c = false → U.testBit c = false ∧ c ≠ c0 := by
        intro c hc'
        rw [Nat.testBit_or, Bool.or_eq_false_iff, Nat.one_shiftLeft, Nat.testBit_two_pow] at hc'
        exact ⟨hc'.1, fun e => by simp [e] at hc'⟩
      refine ⟨fun i c hi => ?_, fun i j c hi hj => ?_⟩ <;>
        rcases i with _ | i <;> try rcases j with _ | j
      · simp only [List.getElem?_cons_zero, Option.bind_some, hc, Option.some.injEq] at hi
        exact hi ▸ h.1
      · exact (hU c (ha i c hi)).1
      · rfl
      · simp only [List.getElem?_cons_zero, Option.bind_some, hc, Option.some.injEq] at hi
        exact absurd hi.symm (hU _ (ha _ _ hj)).2
      · simp only [List.getElem?_cons_zero, Option.bind_some, hc, Option.some.injEq] at hj
        exact absurd hj.symm (hU _ (ha _ _ hi)).2
      · rw [hb _ _ c hi hj]
    · rename_i hc
      obtain ⟨ha, hb⟩ := distinct_spec l U h
      refine ⟨fun i c hi => ?_, fun i j c hi hj => ?_⟩
      · rcases i with _ | i
        exacts [by simp [hc] at hi, ha i c hi]
      · rcases i with _ | i <;> rcases j with _ | j
        exacts [rfl, absurd hi (by simp [hc]), absurd hj (by simp [hc]), by rw [hb _ _ c hi hj]]

omit [DecidableEq X] in
/-- Under the check, a name's word is its owner's. -/
theorem Map.rho_owner [Coded X] (hd : distinct m.ent 0 = true) (σ : Val) {k : Nat} {x : X}
    (hk : m.e k = (.v x, true)) : m.rho σ x = σ (.n k) := by
  have key : ∀ j, m.e j = (.v x, true) → m.ent[j]?.bind ownerCode = some (Coded.code x) :=
    fun j hj => by
      rw [Map.e_eq, List.headD_eq_head?_getD, List.head?_drop] at hj
      cases he : m.ent[j]? <;> simp_all [ownerCode]
  have hex : ∃ k, m.e k = (.v x, true) := ⟨k, hk⟩
  rw [Map.rho, dite_eq_left hex,
    (distinct_spec _ _ hd).2 _ _ _ (key _ (Classical.choose_spec hex)) (key _ hk)]

omit [DecidableEq X] in
theorem Map.use_fwd {σ : Val} {K K' : Nat} {d : V} (h : m.use K d = some K')
    (hK : m.Known σ K) : m.Known σ K' ∧ σ d = (m.h d).eval (m.rho σ) := by
  unfold Map.use at h
  split at h <;> [skip; cases h]
  have hd : σ d = σ (.n d.idx) := congrArg σ (vEqb_iff.mp ‹_›)
  split at h
  · cases h
    exact ⟨hK, hd.trans (hK.2 _ ‹_›)⟩
  split at h <;> cases h
  rename_i x hx
  have key : σ (.n d.idx) = (m.h (.n d.idx)).eval (m.rho σ) := by
    rw [Map.h, hx]
    exact (hK.1 _ _ hx).symm
  exact ⟨⟨hK.1, fun k hk => (testBit_set hk).elim (hK.2 k) fun e => e ▸ key⟩, hd.trans key⟩

omit [DecidableEq X] in
theorem Map.uses_fwd {σ : Val} : ∀ {ds : List V} {K K' : Nat}, m.uses K ds = some K' →
    m.Known σ K → m.Known σ K' ∧ ds.map σ = (ds.map m.h).map (Tm.eval (m.rho σ))
  | [], K, K', h, hK => by cases h; exact ⟨hK, rfl⟩
  | d :: ds, K, K', h, hK => by
    obtain ⟨K1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hK1, e⟩ := Map.use_fwd h1 hK
    obtain ⟨hK2, es⟩ := Map.uses_fwd h2 hK1
    exact ⟨hK2, by simp only [List.map_cons, e, es]⟩

theorem Map.define_eq {K K' : Nat} {d : V} {t : Tm X} (h : m.define K d t = some K') :
    m.h d = t ∧ d = .n d.idx ∧ K' = K ||| 1 <<< d.idx := by
  simp only [Map.define, Option.ite_none_right_eq_some, Bool.and_eq_true, Option.some.injEq] at h
  exact ⟨Tm.eqb_sound h.1.2, vEqb_iff.mp h.1.1, h.2.symm⟩

theorem Map.define_fwd {σ : Val} {K K' : Nat} {d : V} {t : Tm X} (h : m.define K d t = some K')
    (hK : m.Known σ K) (hd : σ d = t.eval (m.rho σ)) : m.Known σ K' := by
  obtain ⟨et, ed, rfl⟩ := Map.define_eq h
  refine ⟨hK.1, fun k hk => ?_⟩
  rcases testBit_set hk with hk | rfl
  · exact hK.2 k hk
  · rw [← ed, et, hd]

private theorem Map.assign_fwd {σ : Val} {K K' : Nat} {d : V} {t : Tm X} {rs rs' : List (Cmd X)}
    (h : m.assign K d t rs = some (K', rs')) (hK : m.Known σ K) (hd : σ d = t.eval (m.rho σ)) :
    m.Known σ K' ∧ (Cmd.SatList rd (m.rho σ) rs' → Cmd.SatList rd (m.rho σ) rs) := by
  unfold Map.assign at h
  split at h
  · cases h
    exact ⟨Map.define_fwd (by assumption) hK hd, id⟩
  · simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Bool.and_eq_true,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨K1, h1, ⟨ea, et⟩, rfl, rfl⟩ := h
    obtain ⟨hK1, e⟩ := Map.use_fwd h1 hK
    refine ⟨hK1, fun hr => Cmd.satList_cons.mpr ⟨?_, hr⟩⟩
    rw [Cmd.Sat, ← Tm.eqb_sound ea, ← Tm.eqb_sound et, ← e, hd]
  · cases h

private theorem Map.assign_bwd {ρ : X → E} {K K' : Nat} {d : V} {t : Tm X} {rs rs' : List (Cmd X)}
    (h : m.assign K d t rs = some (K', rs')) (hs : Cmd.SatList rd ρ rs) :
    m.sig ρ d = t.eval ρ ∧ Cmd.SatList rd ρ rs' := by
  unfold Map.assign at h
  split at h
  · cases h
    exact ⟨congrArg (Tm.eval ρ) (Map.define_eq (by assumption)).1, hs⟩
  · simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Bool.and_eq_true,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨K1, -, ⟨ea, et⟩, rfl, rfl⟩ := h
    obtain ⟨hl, hr⟩ := Cmd.satList_cons.mp hs
    rw [Cmd.Sat, ← Tm.eqb_sound ea, ← Tm.eqb_sound et] at hl
    exact ⟨hl, hr⟩
  · cases h

omit [DecidableEq X] in
private theorem keccakWords_map {σ : Val} {ins outs : List V} {i o : Bool} :
    KeccakWords (ins.map σ) (outs.map σ) i o ↔ (Atom.keccak ins outs i o).Holds rd σ := by
  simp only [KeccakWords, Atom.Holds, List.length_map]

/-- An answered command `c` holds of the names' words when the values read are their terms'. -/
private theorem Map.answer_fwd {σ : Val} {c : Cmd X} {rs : List (Cmd X)} :
    ∀ {K K' : Nat} {ds : List V} {ts : List (Tm X)} {rs' : List (Cmd X)},
      m.answer K ds ts rs = some (K', rs') → m.Known σ K →
      (ds.map σ = ts.map (Tm.eval (m.rho σ)) → c.Sat rd (m.rho σ)) →
      m.Known σ K' ∧ (Cmd.SatList rd (m.rho σ) rs' → Cmd.SatList rd (m.rho σ) (c :: rs))
  | _, _, [], [], _, h, hK, hc => by
    simp only [Map.answer, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hK, fun hr => Cmd.satList_cons.mpr ⟨hc rfl, hr⟩⟩
  | _, _, d :: ds, t :: ts, _, h, hK, hc => by
    simp only [Map.answer, Option.bind_eq_some_iff, Option.ite_none_right_eq_some] at h
    obtain ⟨K1, h1, he, h2⟩ := h
    obtain ⟨hK1, e⟩ := Map.use_fwd h1 hK
    exact Map.answer_fwd h2 hK1 fun es =>
      hc (by rw [List.map_cons, List.map_cons, e, Tm.eqb_sound he, es])
  | _, _, [], _ :: _, _, h, _, _ | _, _, _ :: _, [], _, h, _, _ => by simp [Map.answer] at h

/-- An answered command `c` that holds of the names' words gives `P` when the values read are their
terms. -/
private theorem Map.answer_bwd {ρ : X → E} {c : Cmd X} {rs : List (Cmd X)} {P : Prop} :
    ∀ {K K' : Nat} {ds : List V} {ts : List (Tm X)} {rs' : List (Cmd X)},
      m.answer K ds ts rs = some (K', rs') → Cmd.SatList rd ρ (c :: rs) →
      (ds.map (m.sig ρ) = ts.map (Tm.eval ρ) → c.Sat rd ρ → P) → P ∧ Cmd.SatList rd ρ rs'
  | _, _, [], [], _, h, hs, hc => by
    simp only [Map.answer, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hc rfl (Cmd.satList_cons.mp hs).1, (Cmd.satList_cons.mp hs).2⟩
  | _, _, d :: ds, t :: ts, _, h, hs, hc => by
    simp only [Map.answer, Option.bind_eq_some_iff, Option.ite_none_right_eq_some] at h
    obtain ⟨K1, -, he, h2⟩ := h
    exact Map.answer_bwd h2 hs fun es =>
      hc (by rw [List.map_cons, List.map_cons, es, ← Tm.eqb_sound he]; rfl)
  | _, _, [], _ :: _, _, h, _, _ | _, _, _ :: _, [], _, h, _, _ => by simp [Map.answer] at h

omit [DecidableEq X] in
/-- The words of a `KECCAK` of four cells and the 64-byte padding into two, split. -/
private theorem pair_words {ins : List V} {o0 o1 : V} {f : V → E} {l0 l1 r0 r1 t0 t1 : Tm X}
    {ρ : X → E}
    (e : (ins ++ [o0, o1]).map f = ([l0, l1, r0, r1] ++ pad64 ++ [t0, t1]).map (Tm.eval ρ)) :
    ins.map f = [l0.eval ρ, l1.eval ρ, r0.eval ρ, r1.eval ρ, word 1 0, word 0 0, word 0 0,
      word 0 0, word 9223372036854775808 0, word 0 0, word 0 0, word 0 0, word 0 0] ∧
      f o0 = t0.eval ρ ∧ f o1 = t1.eval ρ := by
  rw [List.map_append, List.map_append] at e
  obtain ⟨e1, e2⟩ := List.append_inj' e (by simp)
  simp only [pad64, List.cons_append, List.nil_append, List.map_cons, List.map_nil, Tm.eval,
    List.cons.injEq, and_true] at e1 e2
  exact ⟨e1, e2⟩

theorem Map.atom_fwd {σ : Val} {K K' : Nat} {a : Atom} {rs rs' : List (Cmd X)}
    (h : m.atom K a rs = some (K', rs')) (hK : m.Known σ K) (ha : a.Holds rd σ) :
    m.Known σ K' ∧ (Cmd.SatList rd (m.rho σ) rs' → Cmd.SatList rd (m.rho σ) rs) := by
  unfold Map.atom at h
  split at h
  · exact Map.assign_fwd h hK ha
  · obtain ⟨K1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hK1, es⟩ := Map.use_fwd h1 hK
    exact Map.assign_fwd h2 hK1 (Eq.trans ha es)
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨K1, h1, K2, h2, h3⟩ := h
    obtain ⟨hK1, ea⟩ := Map.use_fwd h1 hK
    obtain ⟨hK2, eb⟩ := Map.use_fwd h2 hK1
    exact Map.assign_fwd h3 hK2 (Eq.trans ha (congrArg₂ (· + ·) ea eb))
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨K1, h1, K2, h2, h3⟩ := h
    obtain ⟨hK1, ea⟩ := Map.use_fwd h1 hK
    obtain ⟨hK2, eb⟩ := Map.use_fwd h2 hK1
    exact Map.assign_fwd h3 hK2 (Eq.trans ha (congrArg₂ (· * ·) ea eb))
  · split at h
    · rename_i ho
      refine Map.answer_fwd h hK fun e => ?_
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
      rw [Cmd.Sat, ← e.1, ← e.2, ← beq_iff_eq.mp ho]
      exact ha
    · cases h
  · refine Map.answer_fwd h hK fun e => ?_
    obtain ⟨es, eo0, eo1⟩ := pair_words e
    rw [Cmd.Sat, ← eo0, ← eo1]
    exact (keccak_pair_iff es).mp ha
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hl, rfl⟩, rfl⟩ := hc
      refine Map.answer_fwd h hK fun e => ?_
      rw [List.map_append, List.map_append] at e
      obtain ⟨e1, e2⟩ := List.append_inj e (by simp [hl])
      rw [Cmd.Sat, ← e1, ← e2]
      exact keccakWords_map.mpr ha
    · cases h
  · refine Map.answer_fwd h hK fun e => ?_
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
    rw [Cmd.Sat, ← e.1, ← e.2]
    exact Value.e_add_eq_zero_iff.mp ha
  · refine Map.answer_fwd h hK fun e => ?_
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
    obtain ⟨ex, ey, e1, e2, ek⟩ := e
    rw [Cmd.Sat, ← ex, ← ey, ← e1, ← e2, ← ek]
    exact ha
  · cases h
    exact ⟨hK, id⟩
  · cases h

theorem Map.atom_bwd {ρ : X → E} {K K' : Nat} {a : Atom} {rs rs' : List (Cmd X)}
    (h : m.atom K a rs = some (K', rs')) (hs : Cmd.SatList rd ρ rs) :
    a.Holds rd (m.sig ρ) ∧ Cmd.SatList rd ρ rs' := by
  unfold Map.atom at h
  split at h
  · exact Map.assign_bwd h hs
  · obtain ⟨K1, -, h2⟩ := Option.bind_eq_some_iff.mp h
    exact Map.assign_bwd h2 hs
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨K1, -, K2, -, h3⟩ := h
    exact Map.assign_bwd h3 hs
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨K1, -, K2, -, h3⟩ := h
    exact Map.assign_bwd h3 hs
  · split at h
    · rename_i ho
      refine Map.answer_bwd h hs fun e hl => ?_
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
      rw [Cmd.Sat, ← e.1, ← e.2, ← beq_iff_eq.mp ho] at hl
      exact hl
    · cases h
  · refine Map.answer_bwd h hs fun e hl => ?_
    obtain ⟨es, eo0, eo1⟩ := pair_words e
    rw [Cmd.Sat, ← eo0, ← eo1] at hl
    exact (keccak_pair_iff es).mpr hl
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hl, rfl⟩, rfl⟩ := hc
      refine Map.answer_bwd h hs fun e hk => ?_
      rw [List.map_append, List.map_append] at e
      obtain ⟨e1, e2⟩ := List.append_inj e (by simp [hl])
      rw [Cmd.Sat, ← e1, ← e2] at hk
      exact keccakWords_map.mp hk
    · cases h
  · refine Map.answer_bwd h hs fun e hl => ?_
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
    rw [Cmd.Sat, ← e.1, ← e.2] at hl
    exact Value.e_add_eq_zero_iff.mpr hl
  · refine Map.answer_bwd h hs fun e hl => ?_
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
    obtain ⟨ex, ey, e1, e2, ek⟩ := e
    rw [Cmd.Sat, ← ex, ← ey, ← e1, ← e2, ← ek] at hl
    exact hl
  · cases h
    exact ⟨trivial, hs⟩
  · cases h

mutual
theorem Map.stmt_fwd {σ : Val} (kret : List E → Prop) :
    ∀ (s : Stmt) (K K' : Nat) (rs rs' : List (Cmd X)) (next : Prop),
      m.stmt K s rs = some (K', rs') → m.Known σ K → s.Holds C rd σ next kret →
      m.Known σ K' ∧ next ∧ (Cmd.SatList rd (m.rho σ) rs' → Cmd.SatList rd (m.rho σ) rs)
  | .atom a, K, K', rs, rs', next, h, hK, hs => by
    rw [Map.stmt] at h
    rw [Stmt.Holds] at hs
    obtain ⟨hK', i⟩ := Map.atom_fwd h hK hs.1
    exact ⟨hK', hs.2, i⟩
  | .ite c z n, K, K', rs, rs', next, h, hK, hs => by
    rw [Map.stmt] at h
    unfold Map.branch at h
    split at h <;>
      simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, reduceCtorEq] at h
    obtain ⟨K1, h1, hc, h2⟩ := h
    split at h2 <;> cases h2
    rename_i hz hn
    obtain ⟨hK1, ec⟩ := Map.use_fwd h1 hK
    rw [Stmt.Holds] at hs
    obtain ⟨hk, h0, h1'⟩ := hs
    have Z := fun e => Map.stmts_fwd kret z _ _ _ _ next hz hK1 (h0 e)
    have N := fun e => Map.stmts_fwd kret n _ _ _ _ next hn hK1 (h1' e)
    refine ⟨hK1, (em (σ c = 0)).elim (fun e => (Z e).2.1) fun e => (N e).2.1, fun hr => ?_⟩
    rw [Cmd.SatList, Cmd.Sat, ← Tm.eqb_sound hc, ← ec]
    exact ⟨⟨hk, fun e => (Z e).2.2 Cmd.satList_nil, fun e => (N e).2.2 Cmd.satList_nil⟩, hr⟩
  | .match_ x arms, K, K', rs, rs', next, h, hK, hs => by
    rcases rs with _ | ⟨_ | _ | _ | _ | _ | _ | ⟨tc, rarms⟩, rs⟩ <;> rw [Map.stmt] at h <;>
      try cases h
    simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Bool.and_eq_true,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨K1, h1, ⟨hc, ha⟩, rfl, rfl⟩ := h
    obtain ⟨hK1, ec⟩ := Map.use_fwd h1 hK
    rw [Stmt.Holds] at hs
    obtain ⟨hn, hsat⟩ := Map.arms_fwd kret arms rarms 0 K1 x next ha hK1 hs
    refine ⟨hK1, hn, fun hr => Cmd.satList_cons.mpr ⟨?_, hr⟩⟩
    rw [Cmd.Sat, ← Tm.eqb_sound hc, ← ec]
    exact hsat
  | .call .., _, _, _, _, _, h, _, _
  | .callIf .., _, _, _, _, _, h, _, _ | .dispatch .., _, _, _, _, _, h, _, _
  | .ret _, _, _, _, _, _, h, _, _ => by rw [Map.stmt] at h; cases h

theorem Map.stmts_fwd {σ : Val} (kret : List E → Prop) :
    ∀ (ss : List Stmt) (K K' : Nat) (rs rs' : List (Cmd X)) (next : Prop),
      m.stmts K ss rs = some (K', rs') → m.Known σ K → Stmt.HoldsList C rd σ ss next kret →
      m.Known σ K' ∧ next ∧ (Cmd.SatList rd (m.rho σ) rs' → Cmd.SatList rd (m.rho σ) rs)
  | [], K, K', rs, rs', next, h, hK, hs => by
    rw [Map.stmts] at h
    cases h
    rw [Stmt.HoldsList] at hs
    exact ⟨hK, hs, id⟩
  | s :: ss, K, K', rs, rs', next, h, hK, hs => by
    rw [Map.stmts] at h
    obtain ⟨⟨K1, rs1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    rw [Stmt.HoldsList] at hs
    obtain ⟨hK1, hn, i1⟩ := Map.stmt_fwd kret s _ _ _ _ _ h1 hK hs
    obtain ⟨hK2, hn2, i2⟩ := Map.stmts_fwd kret ss _ _ _ _ _ h2 hK1 hn
    exact ⟨hK2, hn2, i1 ∘ i2⟩

theorem Map.arms_fwd {σ : Val} (kret : List E → Prop) :
    ∀ (arms : List (List Stmt)) (rarms : List (List (Cmd X))) (j K : Nat) (x : V) (next : Prop),
      m.arms K arms rarms = true → m.Known σ K → Stmt.HoldsArms C rd σ x j arms next kret →
      next ∧ Cmd.SatArms rd (m.rho σ) (σ x) j rarms
  | [], _, _, _, _, _, _, _, hs => by rw [Stmt.HoldsArms] at hs; exact hs.elim
  | _ :: _, [], _, _, _, _, h, _, _ => by simp [Map.arms] at h
  | a :: as, r :: rs, j, K, x, next, h, hK, hs => by
    rw [Map.arms, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Stmt.HoldsArms] at hs
    rw [Cmd.SatArms]
    rcases hs with ⟨hx, ha⟩ | hs
    · split at h1
      · rename_i K' he
        obtain ⟨-, hn, i⟩ := Map.stmts_fwd kret a K K' r [] next he hK ha
        exact ⟨hn, .inl ⟨hx, i Cmd.satList_nil⟩⟩
      · cases h1
    · exact (Map.arms_fwd kret as rs (j + 1) K x next h2 hK hs).imp_right .inr
end

mutual
theorem Map.stmt_bwd {ρ : X → E} (kret : List E → Prop) :
    ∀ (s : Stmt) (K K' : Nat) (rs rs' : List (Cmd X)) (next : Prop),
      m.stmt K s rs = some (K', rs') → Cmd.SatList rd ρ rs → (Cmd.SatList rd ρ rs' → next) →
      s.Holds C rd (m.sig ρ) next kret
  | .atom a, K, K', rs, rs', next, h, hs, hn => by
    rw [Map.stmt] at h
    rw [Stmt.Holds]
    obtain ⟨ha, hr⟩ := Map.atom_bwd h hs
    exact ⟨ha, hn hr⟩
  | .ite c z n, K, K', rs, rs', next, h, hs, hn => by
    rw [Map.stmt] at h
    unfold Map.branch at h
    split at h <;>
      simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, reduceCtorEq] at h
    obtain ⟨K1, -, hc, h2⟩ := h
    split at h2 <;> cases h2
    rename_i hz hn'
    rw [Cmd.SatList, Cmd.Sat, ← Tm.eqb_sound hc] at hs
    obtain ⟨⟨hk, h0, h1'⟩, hr⟩ := hs
    rw [Stmt.Holds]
    exact ⟨hk, fun e => Map.stmts_bwd kret z _ _ _ _ next hz (h0 e) fun _ => hn hr,
      fun e => Map.stmts_bwd kret n _ _ _ _ next hn' (h1' e) fun _ => hn hr⟩
  | .match_ x arms, K, K', rs, rs', next, h, hs, hn => by
    rcases rs with _ | ⟨_ | _ | _ | _ | _ | _ | ⟨tc, rarms⟩, rs⟩ <;> rw [Map.stmt] at h <;>
      try cases h
    simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Bool.and_eq_true,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨K1, -, ⟨hc, ha⟩, rfl, rfl⟩ := h
    rw [Cmd.SatList, Cmd.Sat, ← Tm.eqb_sound hc] at hs
    rw [Stmt.Holds]
    exact Map.arms_bwd kret arms rarms 0 K1 x next ha hs.1 (hn hs.2)
  | .call .., _, _, _, _, _, h, _, _
  | .callIf .., _, _, _, _, _, h, _, _ | .dispatch .., _, _, _, _, _, h, _, _
  | .ret _, _, _, _, _, _, h, _, _ => by rw [Map.stmt] at h; cases h

theorem Map.stmts_bwd {ρ : X → E} (kret : List E → Prop) :
    ∀ (ss : List Stmt) (K K' : Nat) (rs rs' : List (Cmd X)) (next : Prop),
      m.stmts K ss rs = some (K', rs') → Cmd.SatList rd ρ rs → (Cmd.SatList rd ρ rs' → next) →
      Stmt.HoldsList C rd (m.sig ρ) ss next kret
  | [], K, K', rs, rs', next, h, hs, hn => by
    rw [Map.stmts] at h
    cases h
    rw [Stmt.HoldsList]
    exact hn hs
  | s :: ss, K, K', rs, rs', next, h, hs, hn => by
    rw [Map.stmts] at h
    obtain ⟨⟨K1, rs1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    rw [Stmt.HoldsList]
    exact Map.stmt_bwd kret s _ _ _ _ _ h1 hs fun hr =>
      Map.stmts_bwd kret ss _ _ _ _ _ h2 hr hn

theorem Map.arms_bwd {ρ : X → E} (kret : List E → Prop) :
    ∀ (arms : List (List Stmt)) (rarms : List (List (Cmd X))) (j K : Nat) (x : V) (next : Prop),
      m.arms K arms rarms = true → Cmd.SatArms rd ρ (m.sig ρ x) j rarms → next →
      Stmt.HoldsArms C rd (m.sig ρ) x j arms next kret
  | _, [], _, _, _, _, _, hs, _ => by rw [Cmd.SatArms] at hs; exact hs.elim
  | [], _ :: _, _, _, _, _, h, _, _ => by simp [Map.arms] at h
  | a :: as, r :: rs, j, K, x, next, h, hs, hn => by
    rw [Map.arms, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [Cmd.SatArms] at hs
    rw [Stmt.HoldsArms]
    rcases hs with ⟨hx, ha⟩ | hs
    · split at h1
      · rename_i K' he
        exact .inl ⟨hx, Map.stmts_bwd kret a K K' r [] next he ha fun _ => hn⟩
      · cases h1
    · exact .inr (Map.arms_bwd kret as rs (j + 1) K x next h2 hs hn)
end

theorem Map.body_fwd {σ : Val} {kret : List E → Prop} :
    ∀ (ss : List Stmt) (K : Nat) (rs : List (Cmd X)) (rets : List (Tm X)),
      m.body K ss rs rets = true → m.Known σ K → Stmt.HoldsList C rd σ ss False kret →
      Cmd.SatList rd (m.rho σ) rs ∧ kret (rets.map (Tm.eval (m.rho σ)))
  | [], _, _, _, h, _, _ => by simp [Map.body] at h
  | s :: ss, K, rs, rets, h, hK, hs => by
    rw [Map.body, Bool.or_eq_true] at h
    rw [Stmt.HoldsList] at hs
    rcases h with h | h
    · unfold Map.last at h
      split at h
      · rw [Bool.and_eq_true, Option.isSome_iff_exists] at h
        obtain ⟨⟨K', hu⟩, er⟩ := h
        rw [Stmt.Holds, (Map.uses_fwd hu hK).2, Tm.eqbs_sound er] at hs
        exact ⟨Cmd.satList_nil, hs⟩
      · cases h
    · split at h
      · rename_i p h1
        obtain ⟨hK1, hn, i⟩ := Map.stmt_fwd kret s _ _ _ _ _ h1 hK hs
        exact (Map.body_fwd ss _ _ rets h hK1 hn).imp_left i
      · cases h

theorem Map.body_bwd {ρ : X → E} {kret : List E → Prop} :
    ∀ (ss : List Stmt) (K : Nat) (rs : List (Cmd X)) (rets : List (Tm X)),
      m.body K ss rs rets = true → Cmd.SatList rd ρ rs → kret (rets.map (Tm.eval ρ)) →
      Stmt.HoldsList C rd (m.sig ρ) ss False kret
  | [], _, _, _, h, _, _ => by simp [Map.body] at h
  | s :: ss, K, rs, rets, h, hs, hk => by
    rw [Map.body, Bool.or_eq_true] at h
    rw [Stmt.HoldsList]
    rcases h with h | h
    · unfold Map.last at h
      split at h
      · rw [Bool.and_eq_true] at h
        rw [Stmt.Holds, show ∀ l : List V, l.map (m.sig ρ) = (l.map m.h).map (Tm.eval ρ) from
          fun l => (List.map_map ..).symm, Tm.eqbs_sound h.2]
        exact hk
      · cases h
    · split at h
      · rename_i p h1
        exact Map.stmt_bwd kret s _ _ _ _ _ h1 hs fun hr => Map.body_bwd ss _ _ rets h hr hk
      · cases h

omit [DecidableEq X] in
private theorem map_v_eval (ρ : X → E) (l : List X) : (l.map Tm.v).map (Tm.eval ρ) = l.map ρ := by
  rw [List.map_map]; rfl

/-! ## A body in pieces -/

/-- A list cut into pieces of the given lengths, and the rest. -/
def cutAt {α : Type} : List Nat → List α → List (List α)
  | [], l => [l]
  | c :: cs, l => l.take c :: cutAt cs (l.drop c)

theorem flatten_cutAt {α : Type} : ∀ (cs : List Nat) (l : List α), (cutAt cs l).flatten = l
  | [], l => by simp [cutAt]
  | c :: cs, l => by rw [cutAt, List.flatten_cons, flatten_cutAt cs, List.take_append_drop]

theorem length_cutAt {α : Type} :
    ∀ (cs : List Nat) (l : List α), (cutAt cs l).length = cs.length + 1
  | [], _ => rfl
  | _ :: cs, l => by rw [cutAt, List.length_cons, length_cutAt cs, List.length_cons]

/-- A piece of a body answers its commands exactly from the known values `K`, leaving those of
`Kc` known. -/
def Map.segOk (m : Map X) (K Kc : Nat) (ss : List Stmt) (rs : List (Cmd X)) : Bool :=
  match m.stmts K ss rs with
  | some (k, []) => k &&& Kc == Kc
  | _ => false

/-- A body in pieces against its commands in pieces: each piece but the last answers its commands
from the known values `K` (the first) or `Kc` (the others), leaving those of `Kc` known, and the
last ends the body, returning `rets`. -/
def Map.Pieces (m : Map X) (Kc : Nat) (rets : List (Tm X)) :
    Nat → List (List Stmt) → List (List (Cmd X)) → Prop
  | K, [ss], [rs] => m.body K ss rs rets = true
  | K, ss :: s' :: P, rs :: r' :: Q =>
      m.segOk K Kc ss rs = true ∧ Map.Pieces m Kc rets Kc (s' :: P) (r' :: Q)
  | _, _, _ => False

omit [DecidableEq X] in
private theorem Map.known_mono {σ : Val} {K Kc : Nat} (h : K &&& Kc = Kc) (hK : m.Known σ K) :
    m.Known σ Kc :=
  ⟨hK.1, fun k hk => hK.2 k (by
    rw [← h, Nat.testBit_and] at hk; exact ((Bool.and_eq_true _ _).mp hk).1)⟩

private theorem Map.segOk_eq {K Kc : Nat} {ss : List Stmt} {rs : List (Cmd X)}
    (h : m.segOk K Kc ss rs = true) :
    ∃ k, m.stmts K ss rs = some (k, []) ∧ k &&& Kc = Kc := by
  unfold Map.segOk at h
  split at h
  exacts [⟨_, ‹_›, by simpa using h⟩, by cases h]

private theorem Map.pieces_fwd {σ : Val} {kret : List E → Prop} {Kc : Nat} {rets : List (Tm X)} :
    ∀ (K : Nat) (P : List (List Stmt)) (Q : List (List (Cmd X))), m.Pieces Kc rets K P Q →
      m.Known σ K → Stmt.HoldsList C rd σ P.flatten False kret →
      Cmd.SatList rd (m.rho σ) Q.flatten ∧ kret (rets.map (Tm.eval (m.rho σ)))
  | K, [ss], [rs], h, hK, hb => by
    rw [Map.Pieces] at h
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hb ⊢
    exact Map.body_fwd _ _ _ _ h hK hb
  | K, ss :: s' :: P, rs :: r' :: Q, h, hK, hb => by
    rw [Map.Pieces] at h
    obtain ⟨k, hs, hk⟩ := Map.segOk_eq h.1
    rw [List.flatten_cons, holdsList_append] at hb
    obtain ⟨hK', hn, i⟩ := Map.stmts_fwd kret ss _ _ _ _ _ hs hK hb
    obtain ⟨hr, hret⟩ := Map.pieces_fwd Kc _ _ h.2 (Map.known_mono hk hK') hn
    exact ⟨by rw [List.flatten_cons, Cmd.satList_append]; exact ⟨i Cmd.satList_nil, hr⟩, hret⟩
  | _, [], _, h, _, _ | _, _ :: _, [], h, _, _ | _, [_], _ :: _ :: _, h, _, _
  | _, _ :: _ :: _, [_], h, _, _ => by simp [Map.Pieces] at h

private theorem Map.pieces_bwd {ρ : X → E} {kret : List E → Prop} {Kc : Nat} {rets : List (Tm X)} :
    ∀ (K : Nat) (P : List (List Stmt)) (Q : List (List (Cmd X))), m.Pieces Kc rets K P Q →
      Cmd.SatList rd ρ Q.flatten → kret (rets.map (Tm.eval ρ)) →
      Stmt.HoldsList C rd (m.sig ρ) P.flatten False kret
  | K, [ss], [rs], h, hs, hk => by
    rw [Map.Pieces] at h
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hs ⊢
    exact Map.body_bwd _ _ _ _ h hs hk
  | K, ss :: s' :: P, rs :: r' :: Q, h, hs, hk => by
    rw [Map.Pieces] at h
    obtain ⟨k, hst, -⟩ := Map.segOk_eq h.1
    rw [List.flatten_cons, Cmd.satList_append] at hs
    rw [List.flatten_cons, holdsList_append]
    exact Map.stmts_bwd kret ss _ _ _ _ _ hst hs.1 fun _ => Map.pieces_bwd Kc _ _ h.2 hs.2 hk
  | _, [], _, h, _, _ | _, _ :: _, [], h, _, _ | _, [_], _ :: _ :: _, h, _, _
  | _, _ :: _ :: _, [_], h, _, _ => by simp [Map.Pieces] at h

/-- `Map.Pieces` from its pieces read by index: the first from `K`, the others from `Kc`. -/
theorem Map.pieces_of {Kc : Nat} {rets : List (Tm X)} :
    ∀ (n K : Nat) (P : List (List Stmt)) (Q : List (List (Cmd X))), P.length = n + 1 →
      Q.length = n + 1 →
      (∀ i < n, m.segOk (if i = 0 then K else Kc) Kc (P.getD i []) (Q.getD i []) = true) →
      m.body (if n = 0 then K else Kc) (P.getD n []) (Q.getD n []) rets = true →
      m.Pieces Kc rets K P Q
  | 0, K, P, Q, hP, hQ, _, ht => by
    obtain ⟨ss, rfl⟩ := List.length_eq_one_iff.mp hP
    obtain ⟨rs, rfl⟩ := List.length_eq_one_iff.mp hQ
    rw [Map.Pieces]
    simpa using ht
  | n + 1, K, P, Q, hP, hQ, hs, ht => by
    match P, Q, hP, hQ with
    | ss :: s' :: P, rs :: r' :: Q, hP, hQ =>
      rw [Map.Pieces]
      exact ⟨by simpa using hs 0 (by omega), Map.pieces_of n Kc _ _ (by simpa using hP)
        (by simpa using hQ) (fun i hi => by simpa using hs (i + 1) (by omega)) (by simpa using ht)⟩
    | [], _, h, _ | [_], _, h, _ | _, [], _, h | _, [_], _, h => simp at h

/-! ## Owners at given values -/

/-- Each listed core value is the owner of the listed name. -/
def ownersAt (m : Map X) (pos : List (Nat × X)) : Bool :=
  pos.all fun p => match m.e p.1 with
    | (.v x, true) => decide (x = p.2)
    | _ => false

/-! ## Soundness of a check -/

/-- **A map that checks a core function's body in pieces makes it its reference function**: from
a valuation of the core values, the names' (their owners' words) satisfy the commands and give
the return words; the listed values own their names. -/
theorem Map.pieces_fwd_at [Coded X] {f : Fn} {r : Func X} {K Kc : Nat}
    {P : List (List Stmt)} {Q : List (List (Cmd X))} {pos : List (Nat × X)}
    (hd : distinct m.ent 0 = true) (hu : m.uses 0 f.params = some K)
    (hp : f.params.map m.h = r.params.map .v) (hP : f.body = P.flatten) (hQ : r.body = Q.flatten)
    (hs : m.Pieces Kc r.rets K P Q) (hpos : ownersAt m pos = true) {σ : Val}
    {kret : List E → Prop} (hb : Stmt.HoldsList C rd σ f.body False kret) :
    f.params.map σ = r.params.map (m.rho σ) ∧ (∀ p ∈ pos, m.rho σ p.2 = σ (.n p.1)) ∧
      Cmd.SatList rd (m.rho σ) r.body ∧ kret (r.rets.map (Tm.eval (m.rho σ))) := by
  obtain ⟨hK, ep⟩ := Map.uses_fwd (σ := σ) hu
    ⟨fun _ _ => Map.rho_owner hd σ, fun k hk => by simp at hk⟩
  obtain ⟨hsat, hret⟩ := Map.pieces_fwd K P Q hs hK (hP ▸ hb)
  refine ⟨by rw [ep, hp, map_v_eval], fun p hp => ?_, hQ ▸ hsat, hret⟩
  have := List.all_eq_true.mp hpos p hp
  split at this
  · rename_i x he
    rw [← of_decide_eq_true this]
    exact Map.rho_owner hd σ he
  · cases this

/-- **A map that checks a core function's body in pieces makes its reference function the core
function's**: from a valuation of the names satisfying the commands, the core values' words (their
terms', `Map.sig`) satisfy the body and give the return words; the listed values take their
names' words. -/
theorem Map.pieces_bwd_at {f : Fn} {r : Func X} {K Kc : Nat}
    {P : List (List Stmt)} {Q : List (List (Cmd X))} {pos : List (Nat × X)}
    (hp : f.params.map m.h = r.params.map .v) (hP : f.body = P.flatten) (hQ : r.body = Q.flatten)
    (hs : m.Pieces Kc r.rets K P Q) (hpos : ownersAt m pos = true) {ρ : X → E}
    {kret : List E → Prop} (hsat : Cmd.SatList rd ρ r.body) (hret : kret (r.rets.map (Tm.eval ρ))) :
    f.params.map (m.sig ρ) = r.params.map ρ ∧ (∀ p ∈ pos, m.sig ρ (.n p.1) = ρ p.2) ∧
      Stmt.HoldsList C rd (m.sig ρ) f.body False kret := by
  refine ⟨?_, fun p hp => ?_, hP ▸ Map.pieces_bwd K P Q hs (hQ ▸ hsat) hret⟩
  · rw [← map_v_eval ρ r.params, ← hp, List.map_map]
    rfl
  · have := List.all_eq_true.mp hpos p hp
    show (m.e p.1).1.eval ρ = ρ p.2
    split at this
    · rename_i x he
      rw [he, ← of_decide_eq_true this]
      rfl
    · cases this

/-- **A map that checks a core function's body in pieces makes it its reference function**: the
same relation on the memory, the arguments and the return words. -/
theorem Map.pieces_sem_iff [Coded X] {f : Fn} {r : Func X} {K Kc : Nat}
    {P : List (List Stmt)} {Q : List (List (Cmd X))}
    (hd : distinct m.ent 0 = true) (hu : m.uses 0 f.params = some K)
    (hp : f.params.map m.h = r.params.map .v) (hP : f.body = P.flatten) (hQ : r.body = Q.flatten)
    (hs : m.Pieces Kc r.rets K P Q) (args rets : List E) :
    f.Sem C rd args rets ↔ r.Sem rd args rets := by
  unfold Fn.Sem Func.Sem
  constructor
  · rintro ⟨σ, rfl, hb⟩
    obtain ⟨ep, -, hsat, hret⟩ := Map.pieces_fwd_at (pos := []) hd hu hp hP hQ hs rfl hb
    exact ⟨_, ep.symm, hsat, hret⟩
  · rintro ⟨ρ, rfl, hsat, hret⟩
    obtain ⟨ep, -, hb⟩ := Map.pieces_bwd_at (pos := []) (kret := (· = rets)) hp hP hQ hs rfl hsat hret
    exact ⟨m.sig ρ, ep, hb⟩

/-- **A map that checks a core function makes it its reference function**: the same relation on
the memory, the arguments and the return words. -/
theorem Map.check_sem_iff [Coded X] {f : Fn} {r : Func X} (h : m.check f r = true)
    (args rets : List E) : f.Sem C rd args rets ↔ r.Sem rd args rets := by
  unfold Map.check at h
  rw [Bool.and_eq_true] at h
  split at h
  · rename_i K hu
    rw [Bool.and_eq_true] at h
    exact Map.pieces_sem_iff (Kc := 0) (P := [f.body]) (Q := [r.body]) h.1 hu
      (Tm.eqbs_sound h.2.1) (by simp) (by simp) h.2.2 args rets
  · exact absurd h.2 (by simp)

/-- **A linked core function is its reference function**: the same relation on the memory, the
arguments and the return words. -/
theorem Linked.sem_iff [Coded X] {f : Fn} {r : Func X} (h : Linked f r = true)
    (args rets : List E) : f.Sem C rd args rets ↔ r.Sem rd args rets :=
  Map.check_sem_iff h args rets

end
end LeanVM.Guest.Ref
