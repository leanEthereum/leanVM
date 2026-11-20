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

/-!
# Linking a core function to a reference function

`Linked f r` compares a core function `f` (`LeanVM.Guest.Core`, renumbered: its values are
`V.n k`) with a reference function `r` (`LeanVM.Guest.Ref`), and `Linked.sem_iff` is what a
`true` gives: the two relations are equal. The check is evaluated by the kernel, once per
specialization (`decide +kernel`), with nothing written per specialization.

**The check** (`Map.check`) walks the core body and the commands of `r` together, given a `Map`:
the term over `r`'s names of every core value (`Map.h`), and which values are *owners*, each
standing for the name its term is. No two owners have one name (`distinct`).

* `SET`, `XOR`, `MUL` and copies into a value are its definition: its term must be the term of the
  atom's right side, and no command of `r` answers it. So the constants the lowering sets (the
  Keccak padding run, a stored zero), their sharing and the copies into return cells are invisible
  in `r`.
* A `DEREF` answers a `Cmd.load`, a `KECCAK` of four cells and the 64-byte padding into two cells a
  `Cmd.hash2` (`keccak_pair_iff`), a forward branch a `Cmd.ifNz`, on equal terms.
* A value is read only once *known*: defined on this path, or the owner of the name its term is
  (a hinted or loaded word, an output cell). A branch's definitions are forgotten at its join.

The kernel is slow per step of a recursion, so the check spends a bounded number of steps per
value: the known values and the owned names' numbers (`Coded`) are bit sets, and a value's entry
is read from a list by `sfx`, in order of first occurrence.

**Soundness.** From a valuation `σ` of the core values, the names take their owners' words
(`Map.rho`, `Map.rho_owner`); every known value's word is then its term's (`Map.Known`), and each
core atom gives its command (`Map.stmts_fwd`). From a valuation `ρ` of the names, every core value
takes its term's word (`Map.sig`), and each command gives its atom, a definition holding by the
check on terms (`Map.stmts_bwd`).

**The map is inferred** (`infer`) by the same walk, unverified: a wrong map fails the check.

What is covered is what `verify_merkle_cap` uses; a `ret` ends the body, and every other atom and
statement fails the check.
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

/-- An atom against the commands left: the known values after it and the commands after it. -/
def Map.atom (m : Map X) (K : Nat) : Atom → List (Cmd X) → Option (Nat × List (Cmd X))
  | .const d c, rs => (m.define K d (.const c)).map (·, rs)
  | .copy d s, rs => (m.use K s).bind fun K => (m.define K d (m.h s)).map (·, rs)
  | .add d a b, rs => (m.use K a).bind fun K => (m.use K b).bind fun K =>
      (m.define K d (.add (m.h a) (m.h b))).map (·, rs)
  | .mul d a b, rs => (m.use K a).bind fun K => (m.use K b).bind fun K =>
      (m.define K d (.mul (m.h a) (m.h b))).map (·, rs)
  | .load d p off, .load td tp off' :: rs => (m.use K p).bind fun K => (m.use K d).bind fun K =>
      if (m.h d).eqb td && (m.h p).eqb tp && off == off' then some (K, rs) else none
  | .keccak ins [o0, o1] false false, .hash2 l0 l1 r0 r1 t0 t1 :: rs =>
      (m.uses K ins).bind fun K => (m.use K o0).bind fun K => (m.use K o1).bind fun K =>
        if Tm.eqbs (ins.map m.h) ([l0, l1, r0, r1] ++ pad64) && (m.h o0).eqb t0 && (m.h o1).eqb t1
        then some (K, rs) else none
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
  | .match_ .., _ | .call .., _ | .callIf .., _ | .dispatch .., _ | .ret _, _ => none

/-- A block against the commands left. -/
def Map.stmts (m : Map X) (K : Nat) : List Stmt → List (Cmd X) → Option (Nat × List (Cmd X))
  | [], rs => some (K, rs)
  | s :: ss, rs => (Map.stmt m K s rs).bind fun p => Map.stmts m p.1 ss p.2
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

/-- The map being inferred: the entries of the values below `n`, last first, and the bit set of
the numbers of the names owned. The core values are numbered in order of first occurrence
(`Fn.renumber`), so an entry is given to the next value, by a `cons`. The kernel evaluates lazily:
each step matches on the state, so that no chain of pending updates builds up. -/
structure Acc (X : Type) where
  rev : List (Tm X × Bool)
  n : Nat
  used : Nat

/-- The term of a core value so far. -/
def Acc.h (a : Acc X) (d : V) : Tm X :=
  bif d.idx.blt a.n then (a.rev.getD (a.n - 1 - d.idx) (.const 0, false)).1 else .const 0

/-- The entries with one more, for the value `k`. -/
def Acc.push (rev : List (Tm X × Bool)) (n k : Nat) (e : Tm X × Bool) : List (Tm X × Bool) :=
  e :: (List.replicate (k - n) (.const 0, false) ++ rev)

/-- Give `d` the term `t`, unless it has one. -/
def Acc.bind (a : Acc X) (d : V) (t : Tm X) : Acc X :=
  match a with
  | ⟨rev, n, used⟩ =>
      bif d.idx.blt n then a else ⟨Acc.push rev n d.idx (t, false), d.idx + 1, used⟩

/-- Give `d` the term `t`, unless it has one, as the owner of the name `t` is, unless it has
one. -/
def Acc.name [Coded X] (a : Acc X) (d : V) (t : Tm X) : Acc X :=
  match a with
  | ⟨rev, n, used⟩ =>
      bif d.idx.blt n then a
      else
        match t with
        | .v x =>
            bif used.testBit (Coded.code x) then ⟨Acc.push rev n d.idx (t, false), d.idx + 1, used⟩
            else ⟨Acc.push rev n d.idx (t, true), d.idx + 1, used ||| 1 <<< Coded.code x⟩
        | _ => ⟨Acc.push rev n d.idx (t, false), d.idx + 1, used⟩

/-- The terms an atom gives. -/
def Acc.atom [Coded X] (a : Acc X) : Atom → List (Cmd X) → Acc X × List (Cmd X)
  | .const d c, rs => (a.bind d (.const c), rs)
  | .copy d s, rs => (a.bind d (a.h s), rs)
  | .add d x y, rs => (a.bind d (.add (a.h x) (a.h y)), rs)
  | .mul d x y, rs => (a.bind d (.mul (a.h x) (a.h y)), rs)
  | .load d _ _, .load td _ _ :: rs => (a.name d td, rs)
  | .keccak _ [o0, o1] _ _, .hash2 _ _ _ _ t0 t1 :: rs => ((a.name o0 t0).name o1 t1, rs)
  | _, rs => (a, rs)

mutual
/-- The terms a statement gives. -/
def Acc.stmt [Coded X] (a : Acc X) : Stmt → List (Cmd X) → Acc X × List (Cmd X)
  | .atom x, rs => a.atom x rs
  | .ite _ z n, .ifNz _ rz rn :: rs => ((Acc.stmts (Acc.stmts a z rz).1 n rn).1, rs)
  | _, rs => (a, rs)

/-- The terms a block gives. -/
def Acc.stmts [Coded X] (a : Acc X) : List Stmt → List (Cmd X) → Acc X × List (Cmd X)
  | [], rs => (a, rs)
  | s :: ss, rs =>
      match Acc.stmt a s rs with
      | (⟨rev, n, used⟩, rs) => Acc.stmts ⟨rev, n, used⟩ ss rs
end

/-- The map of a core function and a reference function that agree. -/
def infer [Coded X] (f : Fn) (r : Func X) : Map X :=
  match (((f.params.zip r.params).foldl (fun (a : Acc X) p => a.name p.1 (.v p.2))
    (⟨[], 0, 0⟩ : Acc X)).stmts f.body r.body).1 with
  | ⟨rev, _, _⟩ => ⟨rev.reverse⟩

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
      refine ⟨fun i c hi => ?_, fun i j c hi hj => ?_⟩
      · cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.bind_some, hc] at hi
          cases hi
          exact h.1
        | succ i => exact (hU c (ha i c hi)).1
      · cases i <;> cases j
        · rfl
        · simp only [List.getElem?_cons_zero, Option.bind_some, hc] at hi
          cases hi
          exact absurd rfl (hU _ (ha _ _ hj)).2
        · simp only [List.getElem?_cons_zero, Option.bind_some, hc] at hj
          cases hj
          exact absurd rfl (hU _ (ha _ _ hi)).2
        · rw [hb _ _ c hi hj]
    · rename_i hc
      obtain ⟨ha, hb⟩ := distinct_spec l U h
      refine ⟨fun i c hi => ?_, fun i j c hi hj => ?_⟩
      · cases i with
        | zero => simp [hc] at hi
        | succ i => exact ha i c hi
      · cases i <;> cases j
        · rfl
        · simp [hc] at hi
        · simp [hc] at hj
        · rw [hb _ _ c hi hj]

omit [DecidableEq X] in
/-- Under the check, a name's word is its owner's. -/
theorem Map.rho_owner [Coded X] (hd : distinct m.ent 0 = true) (σ : Val) {k : Nat} {x : X}
    (hk : m.e k = (.v x, true)) : m.rho σ x = σ (.n k) := by
  have key : ∀ j, m.e j = (.v x, true) → m.ent[j]?.bind ownerCode = some (Coded.code x) := by
    intro j hj
    rw [Map.e, sfx_eq_drop, List.headD_eq_head?_getD, List.head?_drop] at hj
    cases he : m.ent[j]? with
    | none => rw [he] at hj; cases hj
    | some e => rw [he] at hj; cases hj; rfl
  unfold Map.rho
  split
  · rename_i hex
    rw [(distinct_spec _ _ hd).2 _ _ _ (key _ (Classical.choose_spec hex)) (key _ hk)]
  · rename_i hex
    exact absurd ⟨k, hk⟩ hex

omit [DecidableEq X] in
theorem Map.use_fwd {σ : Val} {K K' : Nat} {d : V} (h : m.use K d = some K')
    (hK : m.Known σ K) : m.Known σ K' ∧ σ d = (m.h d).eval (m.rho σ) := by
  unfold Map.use at h
  split at h
  · rename_i hd
    have hd : σ d = σ (.n d.idx) := congrArg σ (vEqb_iff.mp hd)
    split at h
    · rename_i hb
      cases h
      exact ⟨hK, hd.trans (hK.2 _ hb)⟩
    · split at h
      · rename_i x hx
        cases h
        have key : σ (.n d.idx) = (m.h (.n d.idx)).eval (m.rho σ) := by
          show _ = (m.e d.idx).1.eval _
          rw [hx]
          exact (hK.1 _ _ hx).symm
        exact ⟨⟨hK.1, fun k hk => (testBit_set hk).elim (hK.2 k) fun e => by subst e; exact key⟩,
          hd.trans key⟩
      · cases h
  · cases h

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
  unfold Map.define at h
  split at h
  · rename_i hc
    rw [Bool.and_eq_true] at hc
    cases h
    exact ⟨Tm.eqb_sound hc.2, vEqb_iff.mp hc.1, rfl⟩
  · cases h

theorem Map.define_fwd {σ : Val} {K K' : Nat} {d : V} {t : Tm X} (h : m.define K d t = some K')
    (hK : m.Known σ K) (hd : σ d = t.eval (m.rho σ)) : m.Known σ K' := by
  obtain ⟨et, ed, rfl⟩ := Map.define_eq h
  refine ⟨hK.1, fun k hk => ?_⟩
  rcases testBit_set hk with hk | rfl
  · exact hK.2 k hk
  · rw [← ed, et, hd]

theorem Map.atom_fwd {σ : Val} {K K' : Nat} {a : Atom} {rs rs' : List (Cmd X)}
    (h : m.atom K a rs = some (K', rs')) (hK : m.Known σ K) (ha : a.Holds rd σ) :
    m.Known σ K' ∧ (Cmd.SatList rd (m.rho σ) rs' → Cmd.SatList rd (m.rho σ) rs) := by
  unfold Map.atom at h
  split at h
  · obtain ⟨K1, h1, e⟩ := Option.map_eq_some_iff.mp h
    cases e
    exact ⟨Map.define_fwd h1 hK ha, id⟩
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨K1, h1, K2, h2, e⟩ := h
    cases e
    obtain ⟨hK1, es⟩ := Map.use_fwd h1 hK
    exact ⟨Map.define_fwd h2 hK1 (Eq.trans ha es), id⟩
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨K1, h1, K2, h2, K3, h3, e⟩ := h
    cases e
    obtain ⟨hK1, ea⟩ := Map.use_fwd h1 hK
    obtain ⟨hK2, eb⟩ := Map.use_fwd h2 hK1
    exact ⟨Map.define_fwd h3 hK2 (Eq.trans ha (congrArg₂ (· + ·) ea eb)), id⟩
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨K1, h1, K2, h2, K3, h3, e⟩ := h
    cases e
    obtain ⟨hK1, ea⟩ := Map.use_fwd h1 hK
    obtain ⟨hK2, eb⟩ := Map.use_fwd h2 hK1
    exact ⟨Map.define_fwd h3 hK2 (Eq.trans ha (congrArg₂ (· * ·) ea eb)), id⟩
  · simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Bool.and_eq_true,
      beq_iff_eq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨K1, h1, K2, h2, ⟨⟨ed, ep⟩, rfl⟩, rfl, rfl⟩ := h
    obtain ⟨hK1, e1⟩ := Map.use_fwd h1 hK
    obtain ⟨hK2, e2⟩ := Map.use_fwd h2 hK1
    refine ⟨hK2, fun hr => Cmd.satList_cons.mpr ⟨?_, hr⟩⟩
    rw [Cmd.Sat, ← Tm.eqb_sound ed, ← Tm.eqb_sound ep, ← e1, ← e2]
    exact ha
  · simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Bool.and_eq_true,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨K1, h1, K2, h2, K3, h3, ⟨⟨ei, e0⟩, e1⟩, rfl, rfl⟩ := h
    obtain ⟨hK1, es⟩ := Map.uses_fwd h1 hK
    obtain ⟨hK2, eo0⟩ := Map.use_fwd h2 hK1
    obtain ⟨hK3, eo1⟩ := Map.use_fwd h3 hK2
    refine ⟨hK3, fun hr => Cmd.satList_cons.mpr ⟨?_, hr⟩⟩
    rw [Tm.eqbs_sound ei] at es
    simp only [pad64, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      Tm.eval] at es
    rw [Cmd.Sat, ← Tm.eqb_sound e0, ← Tm.eqb_sound e1, ← eo0, ← eo1]
    exact (keccak_pair_iff es).mp ha
  · cases h

theorem Map.atom_bwd {ρ : X → E} {K K' : Nat} {a : Atom} {rs rs' : List (Cmd X)}
    (h : m.atom K a rs = some (K', rs')) (hs : Cmd.SatList rd ρ rs) :
    a.Holds rd (m.sig ρ) ∧ Cmd.SatList rd ρ rs' := by
  unfold Map.atom at h
  split at h
  · obtain ⟨K1, h1, e⟩ := Option.map_eq_some_iff.mp h
    cases e
    exact ⟨congrArg (Tm.eval ρ) (Map.define_eq h1).1, hs⟩
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨K1, h1, K2, h2, e⟩ := h
    cases e
    exact ⟨congrArg (Tm.eval ρ) (Map.define_eq h2).1, hs⟩
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨K1, h1, K2, h2, K3, h3, e⟩ := h
    cases e
    exact ⟨congrArg (Tm.eval ρ) (Map.define_eq h3).1, hs⟩
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨K1, h1, K2, h2, K3, h3, e⟩ := h
    cases e
    exact ⟨congrArg (Tm.eval ρ) (Map.define_eq h3).1, hs⟩
  · simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Bool.and_eq_true,
      beq_iff_eq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨K1, h1, K2, h2, ⟨⟨ed, ep⟩, rfl⟩, rfl, rfl⟩ := h
    obtain ⟨hl, hr⟩ := Cmd.satList_cons.mp hs
    rw [Cmd.Sat, ← Tm.eqb_sound ed, ← Tm.eqb_sound ep] at hl
    exact ⟨hl, hr⟩
  · simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Bool.and_eq_true,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨K1, h1, K2, h2, K3, h3, ⟨⟨ei, e0⟩, e1⟩, rfl, rfl⟩ := h
    obtain ⟨hl, hr⟩ := Cmd.satList_cons.mp hs
    rw [Cmd.Sat, ← Tm.eqb_sound e0, ← Tm.eqb_sound e1] at hl
    have hins := congrArg (List.map (Tm.eval ρ)) (Tm.eqbs_sound ei)
    rw [List.map_map] at hins
    simp only [pad64, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      Tm.eval] at hins
    exact ⟨(keccak_pair_iff hins).mpr hl, hr⟩
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
    split at h
    · simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some] at h
      obtain ⟨K1, h1, hc, h2⟩ := h
      split at h2
      · rename_i hz hn
        cases h2
        obtain ⟨hK1, ec⟩ := Map.use_fwd h1 hK
        rw [Tm.eqb_sound hc] at ec
        rw [Stmt.Holds] at hs
        obtain ⟨hk, h0, h1'⟩ := hs
        have nil : Cmd.SatList rd (m.rho σ) [] := Cmd.satList_nil
        refine ⟨hK1, ?_, fun hr => ?_⟩
        · by_cases e : σ c = 0
          · exact (Map.stmts_fwd kret z _ _ _ _ next hz hK1 (h0 e)).2.1
          · exact (Map.stmts_fwd kret n _ _ _ _ next hn hK1 (h1' e)).2.1
        · rw [Cmd.SatList, Cmd.Sat, ← ec]
          exact ⟨⟨hk, fun e => (Map.stmts_fwd kret z _ _ _ _ next hz hK1 (h0 e)).2.2 nil,
            fun e => (Map.stmts_fwd kret n _ _ _ _ next hn hK1 (h1' e)).2.2 nil⟩, hr⟩
      · cases h2
    · cases h
  | .match_ .., _, _, _, _, _, h, _, _ | .call .., _, _, _, _, _, h, _, _
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
    split at h
    · simp only [Option.bind_eq_some_iff, Option.ite_none_right_eq_some] at h
      obtain ⟨K1, h1, hc, h2⟩ := h
      split at h2
      · rename_i hz hn'
        cases h2
        rw [Cmd.SatList, Cmd.Sat, ← Tm.eqb_sound hc] at hs
        obtain ⟨⟨hk, h0, h1'⟩, hr⟩ := hs
        rw [Stmt.Holds]
        exact ⟨hk, fun e => Map.stmts_bwd kret z _ _ _ _ next hz (h0 e) fun _ => hn hr,
          fun e => Map.stmts_bwd kret n _ _ _ _ next hn' (h1' e) fun _ => hn hr⟩
      · cases h2
    · cases h
  | .match_ .., _, _, _, _, _, h, _, _ | .call .., _, _, _, _, _, h, _, _
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
        obtain ⟨hr, hk⟩ := Map.body_fwd ss _ _ rets h hK1 hn
        exact ⟨i hr, hk⟩
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

/-- **A linked core function is its reference function**: the same relation on the memory, the
arguments and the return words. -/
theorem Linked.sem_iff [Coded X] {f : Fn} {r : Func X} (h : Linked f r = true)
    (args rets : List E) : f.Sem C rd args rets ↔ r.Sem rd args rets := by
  unfold Linked Map.check at h
  unfold Fn.Sem Func.Sem
  rw [Bool.and_eq_true] at h
  obtain ⟨hd, h⟩ := h
  split at h
  · rename_i K hu
    rw [Bool.and_eq_true] at h
    obtain ⟨hp, hb⟩ := h
    have hp := Tm.eqbs_sound hp
    have vmap : ∀ (ρ : X → E) (l : List X), (l.map Tm.v).map (Tm.eval ρ) = l.map ρ :=
      fun ρ l => by rw [List.map_map]; rfl
    constructor
    · rintro ⟨σ, rfl, hs⟩
      obtain ⟨hK, ep⟩ := Map.uses_fwd (σ := σ) hu
        ⟨fun _ _ => Map.rho_owner hd σ, fun k hk => by simp at hk⟩
      obtain ⟨hsat, hret⟩ := Map.body_fwd _ _ _ _ hb hK hs
      exact ⟨_, by rw [ep, hp, vmap], hsat, hret⟩
    · rintro ⟨ρ, rfl, hsat, hret⟩
      refine ⟨(infer f r).sig ρ, ?_, Map.body_bwd _ _ _ _ hb hsat hret⟩
      rw [← vmap ρ r.params, ← hp, List.map_map]
      rfl
  · cases h

end
end LeanVM.Guest.Ref
