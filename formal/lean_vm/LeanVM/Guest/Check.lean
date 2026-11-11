/-
  LeanVM.Guest.Check

  The checker of a compiled function against its core IR function: a walk over the core
  statements along the executor's segments, which finds every core constraint among the atoms of
  the path, with the frame cell of each core value given by an untrusted certificate.
-/

module

public import LeanVM.Guest.ExecCore
public import LeanVM.Guest.CoreLemmas

/-!
# The checker

`chkL` walks a core function's statements in order, together with a position in the segments of
`Exec.exec` (a segment and the items of it not yet passed), and a **book** of the atoms passed so
far on the path, by frame cell. A value's frame cell is the certificate's (`Cert.locs`); the
valuation the soundness proof uses reads every value from its cell.

* An atom (`atomOk`) must be implied by atoms in the book: a `SET` of its constant, an `XOR` of
  its three cells in any order (characteristic two), a `MUL`, a `DEREF`, the three instructions of
  a range check, a `JUMP` reading the two words of an `assert_in_k`, a `KECCAK` (its thirteen
  read and thirteen written cells, filed under its first written cell), copies and
  `assert ==` by sharing a cell or by a copy fact, and `addr` by the product of a cell holding the
  frame pointer and a known power of `g`. The walk passes items into the book until the atom is
  found, never past a branch; an atom found nowhere before the end of its segment stays pending
  and must be found by the end of its block.
* `ite` is the next branch, on the condition's cell, to a later offset of the function: both
  blocks are walked, from the fall-through and from the target, and must end at one join, where
  the walk goes on with the book of the branch point.
* `match` leaves its segment by a table jump: the selector's word is read from the jump table into
  the target cell, the selector is bounded by a range check, a known bound or booleanity
  (`selBound`: `1 + b·(1 + g^k)` with `b·b = b`, and products of such), every slot of the
  table holds its arm's offset, and the arms end at one join.
* A call leaves its segment into a callee frame: the callee's entry and name, the argument cells
  stored into the callee frame, the self frame pointer cell of a loop callee, its bounded
  arguments; the walk goes on at the return point, where the returned words are read back. A
  fused `dispatch` reads the callee from the jump table, as a `match`.
* A loop's closing `callIf` is a tail call to its own entry at the next frame `fp·g^S`, the
  arguments, the self frame pointer and the return registers copied into it; elsewhere `callIf`
  is a conditional call whose fall-through reaches the return point.
* `ret` leaves by the return jump (`main` by the halting jump) with its words in the return cells.

Everything is structural recursion over lists and tries keyed by `ℕ`, evaluated by the kernel.
-/

namespace LeanVM.Guest.Check

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-! ## Fast tries

`Trie.get` and `Trie.set` on the recursors and raw `Nat` operations, which the kernel evaluates
several times faster than the instance-based forms; equal to them (`getF_eq`, `setF_eq`). -/

section Fast

variable {α : Type}

/-- `Trie.get`, for the kernel. -/
noncomputable def getF (t : Trie α) : ℕ → Option α :=
  Trie.rec (motive := fun _ ↦ ℕ → Option α) (fun _ ↦ none)
    (fun v _ _ gl gr n ↦ Nat.rec (motive := fun _ ↦ Option α) v
      (fun m _ ↦ Bool.rec (gr (Nat.div m 2)) (gl (Nat.div m 2)) (Nat.beq (Nat.mod m 2) 0)) n) t

/-- `Trie.set`, for the kernel. -/
noncomputable def setF (a : α) (d : ℕ) : Trie α → ℕ → Trie α :=
  Nat.rec (motive := fun _ ↦ Trie α → ℕ → Trie α) (fun t _ ↦ t)
    (fun _ s t n ↦ Trie.casesOn (motive := fun _ ↦ Trie α) t
      (Nat.rec (motive := fun _ ↦ Trie α) (.node (some a) .nil .nil)
        (fun m _ ↦ Bool.rec ((s .nil (Nat.div m 2)).seq fun r ↦ .node none .nil r)
          ((s .nil (Nat.div m 2)).seq fun l ↦ .node none l .nil) (Nat.beq (Nat.mod m 2) 0)) n)
      (fun v l r ↦ Nat.rec (motive := fun _ ↦ Trie α) (.node (some a) l r)
        (fun m _ ↦ Bool.rec ((s r (Nat.div m 2)).seq fun r ↦ .node v l r)
          ((s l (Nat.div m 2)).seq fun l ↦ .node v l r) (Nat.beq (Nat.mod m 2) 0)) n)) d

/-- The child a key `m + 1` goes to: the left one at `m` even, the right one otherwise, at
`m / 2`. -/
theorem key_succ (m : ℕ) : (Nat.beq (Nat.mod m 2) 0 = true ∧ (m + 1) % 2 = 1 ∧ (m + 1) / 2 = m / 2) ∨
    (Nat.beq (Nat.mod m 2) 0 = false ∧ (m + 1) % 2 ≠ 1 ∧ (m + 1) / 2 - 1 = m / 2) := by
  cases hb : Nat.beq (Nat.mod m 2) 0
  · have h : m % 2 ≠ 0 := Nat.ne_of_beq_eq_false hb
    exact Or.inr ⟨rfl, by omega, by omega⟩
  · have h : m % 2 = 0 := Nat.eq_of_beq_eq_true hb
    exact Or.inl ⟨rfl, by omega, by omega⟩

theorem getF_eq (t : Trie α) (n : ℕ) : getF t n = t.get n := by
  induction t generalizing n with
  | nil => rfl
  | node v l r ihl ihr =>
    rw [Trie.get_node]
    cases n with
    | zero => rfl
    | succ m =>
      show @Bool.rec (fun _ ↦ Option α) (getF r (Nat.div m 2)) (getF l (Nat.div m 2))
        (Nat.beq (Nat.mod m 2) 0) = _
      rw [ihl, ihr, ite_eq_right (Nat.succ_ne_zero m)]
      rcases key_succ m with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩
      · rw [hb, ite_eq_left h1, h2]
        rfl
      · rw [hb, ite_eq_right h1, h2]
        rfl

theorem setF_eq (a : α) (d : ℕ) : ∀ (t : Trie α) (n : ℕ), setF a d t n = t.set a d n := by
  induction d with
  | zero => intro t n; rfl
  | succ d ih =>
    intro t n
    rw [Trie.set_succ]
    cases t with
    | nil =>
      cases n with
      | zero => rfl
      | succ m =>
        show @Bool.rec (fun _ ↦ Trie α) ((setF a d .nil (Nat.div m 2)).seq fun r ↦ Trie.node none .nil r)
          ((setF a d .nil (Nat.div m 2)).seq fun l ↦ Trie.node none l .nil)
          (Nat.beq (Nat.mod m 2) 0) = _
        rw [ih, Trie.seq_eq, Trie.seq_eq, ite_eq_right (Nat.succ_ne_zero m)]
        rcases key_succ m with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩
        · rw [hb, ite_eq_left h1, h2]
          rfl
        · rw [hb, ite_eq_right h1, h2]
          rfl
    | node v l r =>
      cases n with
      | zero => rfl
      | succ m =>
        show @Bool.rec (fun _ ↦ Trie α) ((setF a d r (Nat.div m 2)).seq fun r ↦ Trie.node v l r)
          ((setF a d l (Nat.div m 2)).seq fun l ↦ Trie.node v l r)
          (Nat.beq (Nat.mod m 2) 0) = _
        rw [ih, ih, Trie.seq_eq, Trie.seq_eq, ite_eq_right (Nat.succ_ne_zero m)]
        rcases key_succ m with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩
        · rw [hb, ite_eq_left h1, h2]
          rfl
        · rw [hb, ite_eq_right h1, h2]
          rfl

end Fast

/-! ## The book -/

/-- The atoms passed on a path, by frame cell. -/
abbrev Book := Trie (List Exec.Atom)

/-- The cells an atom is filed under: the cell it determines. -/
def keys : Exec.Atom → List ℕ
  | .instr _ (.xor _ _ c) => [c]
  | .instr _ (.mul _ _ c) => [c]
  | .instr _ (.set o _ _) => [o]
  | .instr _ (.deref _ _ o3 .cell) => [o3]
  | .instr _ (.deref o1 _ _ .fp) => [o1]
  | .instr _ (.keccak _ _ _ _ _ _ _ out _ _ _) => [out]
  | .jump _ od _ => [od]
  | .copy d s => [d, s]
  | .eq a b => [a, b]
  | .range x _ _ => [x]
  | _ => []

/-- The atoms filed under a cell. -/
noncomputable def look (B : Book) (o : ℕ) : List Exec.Atom := (getF B o).getD []

/-- File `a` under `o`. -/
noncomputable def addKey (a : Exec.Atom) (B : Book) (o : ℕ) : Book :=
  listSeq (look B o) fun l ↦ setF (a :: l) envDepth B o

/-- File an atom. -/
noncomputable def addFact (B : Book) (a : Exec.Atom) : Book := (keys a).foldl (addKey a) B

/-! ## Values -/

/-- The certificate's frame cell of a value, by its number. -/
noncomputable def cellOf (loc : Trie ℕ) (v : Core.V) : ℕ := (getF loc v.idx).getD 0

/-- The cells from value `k` on stored into `t`, each step evaluated. -/
noncomputable def locTrieFrom : List ℕ → ℕ → Trie ℕ → Trie ℕ
  | [], _, t => t
  | c :: cs, k, t => natSeq (k + 1) fun k' ↦ (setF c indexDepth t k).seq fun t ↦ locTrieFrom cs k' t

/-- The cells as a trie, value `k` at key `k`. -/
noncomputable def locTrie (locs : List ℕ) : Trie ℕ := locTrieFrom locs 0 .nil

/-- The cells of a list of values. -/
noncomputable def cellsOf (loc : Trie ℕ) (vs : List Core.V) : List ℕ := vs.map (cellOf loc)



/-! ## Atoms -/

section Atoms

variable (F : Exec.Facts) (B : Book) (ψ : Trie Sym)

/-- The bits of a limb. -/
def limbNat (x : E) (i : Fin 2) : ℕ := (x.limb i).toBitVec.toNat

/-- `fp[c]` is the word of limbs `l0, l1`, by a `SET`. -/
noncomputable def setImm (c l0 l1 : ℕ) : Bool :=
  (look B c).any fun a ↦ match a with
    | .instr _ (.set o k0 k1) => o == c && l0 == k0 && l1 == k1
    | _ => false

/-- `fp[c]` is the constant `x`, by a `SET` of its limbs. -/
noncomputable def setIs (c : ℕ) (x : E) : Bool := setImm B c (limbNat x 0) (limbNat x 1)

/-- `(x, y, z)` is a permutation of `(p, q, r)`. -/
def perm3 (x y z p q r : ℕ) : Bool :=
  (x == p && y == q && z == r) || (x == q && y == p && z == r) ||
  (x == p && y == r && z == q) || (x == r && y == p && z == q) ||
  (x == q && y == r && z == p) || (x == r && y == q && z == p)

/-- An `XOR` filed under `o` over the cells `p, q, r` in some order. -/
noncomputable def xorIn (o p q r : ℕ) : Bool :=
  (look B o).any fun a ↦ match a with
    | .instr _ (.xor x y z) => perm3 x y z p q r
    | _ => false

/-- `fp[d] = fp[a] + fp[b]`, by an `XOR` of the three cells in any order. -/
noncomputable def addOk (d a b : ℕ) : Bool := xorIn B d a b d || xorIn B a a b d || xorIn B b a b d

/-- `fp[d] = fp[a] · fp[b]`, by a `MUL`. -/
noncomputable def mulOk (d a b : ℕ) : Bool :=
  (look B d).any fun x ↦ match x with
    | .instr _ (.mul x y z) => z == d && ((x == a && y == b) || (x == b && y == a))
    | _ => false

/-- `fp[a] = fp[b]`: one cell, or a copy fact. -/
noncomputable def sameOk (a b : ℕ) : Bool :=
  a == b || (look B a).any fun x ↦ match x with
    | .copy d s => (d == a && s == b) || (d == b && s == a)
    | .eq d s => (d == a && s == b) || (d == b && s == a)
    | _ => false

/-- `L[fp[p]·g^off] = fp[d]`, `fp[p]` in `K`, by a `DEREF`. -/
noncomputable def loadOk (d p off : ℕ) : Bool :=
  (look B d).any fun x ↦ match x with
    | .instr _ (.deref o1 o2 o3 .cell) => o1 == p && o2 == off && o3 == d
    | _ => false

/-- The `!=` gadget: `fp[p] = fp[x] · fp[i]` and `fp[p] = 1` (its limbs, since a module's
kernel does not reduce `1 : E`). -/
noncomputable def neOk (x i p : ℕ) : Bool := mulOk B p x i && setImm B p 1 0

/-- `fp[p] = fp[q]`: one cell, or two cells `SET` to one immediate. -/
noncomputable def setSame (p q : ℕ) : Bool :=
  p == q || (look B p).any fun a ↦ match a with
    | .instr _ (.set o k0 k1) => o == p && setImm B q k0 k1
    | _ => false

/-- `fp[a] = fp[b]` by construction: `sameOk`, `setSame`, or products `fp[x]·fp[y]`,
`fp[x']·fp[y']` of one cell by two `setSame` cells (the compiler's `x·g` computed twice). -/
noncomputable def eqCell (a b : ℕ) : Bool :=
  sameOk B a b || setSame B a b || (look B a).any fun u ↦ match u with
    | .instr _ (.mul x y z) => z == a && (look B b).any fun w ↦ match w with
      | .instr _ (.mul x' y' z') => z' == b &&
          ((x == x' && setSame B y y') || (y == y' && setSame B x x') ||
            (x == y' && setSame B y x') || (y == x' && setSame B x y'))
      | _ => false
    | _ => false

/-- `fp[c] ≠ 0` gives `fp[a] ≠ fp[b]`: `fp[c] = fp[a'] + fp[b']` by an `XOR`, with `fp[a'] = fp[a]`
and `fp[b'] = fp[b]` (`eqCell`): a loop's `callIf (x·g + N)` passes `x·g ≠ N`. -/
noncomputable def neAt (c a b : ℕ) : Bool :=
  (look B c).any fun u ↦ match u with
    | .instr _ (.xor x y z) => z == c &&
        ((eqCell B x a && eqCell B y b) || (eqCell B x b && eqCell B y a))
    | _ => false

/-- The range check: `DEREF *(fp[x]) = fp[t1]`, `fp[k] = fp[x] · fp[y]`, `DEREF *(fp[y]) = fp[t2]`. -/
noncomputable def rangeOk (x y t1 t2 k : ℕ) : Bool := loadOk B t1 x 0 && mulOk B k x y && loadOk B t2 y 0

/-- `fp[a]`, `fp[b]` are read by a `JUMP` as its target registers. -/
noncomputable def inKOk (a b : ℕ) : Bool :=
  (look B a).any fun x ↦ match x with
    | .jump _ od of => od == a && of == b
    | _ => false

/-- A `KECCAK` reading the cells `ins` in the layout `inOdd` and writing the cells `outs` in the
layout `outOdd`: found under its first written cell, its read cells `keccakIns` and its written
cells `keccakOuts` of its offsets, as many as its `out_cells`. -/
noncomputable def keccakOk (ins outs : List ℕ) (inOdd outOdd : Bool) : Bool :=
  match outs with
  | [] => false
  | o :: _ => (look B o).any fun x ↦ match x with
    | .instr _ (.keccak m0 m1 m2 m3 tail b8 cap out iO oO oC) =>
        out == o && iO == inOdd && oO == outOdd && ins == keccakIns m0 m1 m2 m3 tail b8 cap &&
          outs == keccakOuts out oC.cellCount
    | _ => false

/-- `fp[x]` holds the frame pointer through a hinted cell: `DEREF *(fp[h]) = fp` and
`DEREF *(fp[h]) = fp[x]`. -/
noncomputable def bounceOk (x : ℕ) : Bool :=
  (look B x).any fun a ↦ match a with
    | .instr _ (.deref h 0 x' .cell) => x' == x && (look B h).any fun b ↦ match b with
        | .instr _ (.deref h' 0 _ .fp) => h' == h
        | _ => false
    | _ => false

/-- `fp[x] = fp · g^e`, known at the segment's start or through a bounce. -/
noncomputable def fpgAt (x : ℕ) : Option ℕ :=
  match ψ.get x with
  | some (.fpg e) => some e
  | _ => bif bounceOk B x then some 0 else none

/-- `fp[y] = g^e`, known at the segment's start or by a `SET` the powers name. -/
noncomputable def gpAt (y : ℕ) : Option ℕ :=
  match ψ.get y with
  | some (.gp e) => some e
  | _ => ((look B y).findSome? fun a ↦ match a with
      | .instr _ (.set o k0 0) => bif o == y then F.pows.find k0 else none
      | _ => none)

/-- `fp[x] = fp · g^e` through at most `n` products by known powers of `g` from a cell `fpgAt`
knows: the compiler steps a shifted frame address from another (`mat_cells`). -/
noncomputable def fpgChain : ℕ → ℕ → Option ℕ
  | 0, x => fpgAt B ψ x
  | n + 1, x => match fpgAt B ψ x with
    | some e => some e
    | none => (look B x).findSome? fun a ↦ match a with
      | .instr _ (.mul y z w) => bif w == x then (match fpgChain n y, gpAt F B ψ z with
          | some e1, some e2 => some (e1 + e2)
          | _, _ => none) else none
      | _ => none

/-- The products a frame address is stepped through, at most. -/
def fpgDepth : ℕ := 16

/-- The values of a run sit in consecutive cells from `base`. -/
noncomputable def runAt (loc : Trie ℕ) : ℕ → List Core.V → Bool
  | _, [] => true
  | base, v :: vs => cellOf loc v == base && runAt loc (base + 1) vs

/-- `addr(run)`: `fp[p] = fp[x] · fp[y]` with `fp[x] = fp·g^e₁`, `fp[y] = g^e₂`, and the run at
`fp·g^(e₁+e₂)`. -/
noncomputable def addrOk (loc : Trie ℕ) (p : ℕ) (run : List Core.V) : Bool :=
  (look B p).any fun a ↦ match a with
    | .instr _ (.mul x y z) => z == p && (match fpgChain F B ψ fpgDepth x, gpAt F B ψ y with
        | some e1, some e2 => runAt loc (e1 + e2) run
        | _, _ => false)
    | _ => false

/-- **A core atom is implied by the book.** -/
noncomputable def atomOk (loc : Trie ℕ) : Core.Atom → Bool
  | .const d x => setIs B (cellOf loc d) x
  | .add d a b => addOk B (cellOf loc d) (cellOf loc a) (cellOf loc b)
  | .mul d a b => mulOk B (cellOf loc d) (cellOf loc a) (cellOf loc b)
  | .copy d s => sameOk B (cellOf loc d) (cellOf loc s)
  | .load d p off => loadOk B (cellOf loc d) (cellOf loc p) off
  | .assertEq a b => sameOk B (cellOf loc a) (cellOf loc b)
  | .assertNe x i p => neOk B (cellOf loc x) (cellOf loc i) (cellOf loc p)
  | .rangeCheck x y t1 t2 k =>
      rangeOk B (cellOf loc x) (cellOf loc y) (cellOf loc t1) (cellOf loc t2) (cellOf loc k)
  | .assertInK a b => inKOk B (cellOf loc a) (cellOf loc b)
  | .keccak ins outs inOdd outOdd => keccakOk B (cellsOf loc ins) (cellsOf loc outs) inOdd outOdd
  | .frameAddr p run => addrOk F B ψ loc (cellOf loc p) run
  | .hint _ => true
  | .touch t p => loadOk B (cellOf loc t) (cellOf loc p) 0

end Atoms

/-! ## Located atoms

The walk tests an atom at every item it passes, so it looks the atom's cells up once: `locate`
maps a core atom to its cells, evaluated by `LAtom.seq`, and `atomOkL` is `atomOk` on them
(`atomOkL_locate`). -/

/-- A core atom over the cells of its values. -/
inductive LAtom where
  | const (d : ℕ) (x : E)
  | add (d a b : ℕ)
  | mul (d a b : ℕ)
  | same (a b : ℕ)
  | load (d p off : ℕ)
  | ne (x i p : ℕ)
  | range (x y t1 t2 k : ℕ)
  | inK (a b : ℕ)
  | keccak (ins outs : List ℕ) (inOdd outOdd : Bool)
  | addr (p : ℕ) (run : List ℕ)
  | none

/-- The cells of an atom's values. -/
noncomputable def locate (loc : Trie ℕ) : Core.Atom → LAtom
  | .const d x => .const (cellOf loc d) x
  | .add d a b => .add (cellOf loc d) (cellOf loc a) (cellOf loc b)
  | .mul d a b => .mul (cellOf loc d) (cellOf loc a) (cellOf loc b)
  | .copy d s => .same (cellOf loc d) (cellOf loc s)
  | .load d p off => .load (cellOf loc d) (cellOf loc p) off
  | .assertEq a b => .same (cellOf loc a) (cellOf loc b)
  | .assertNe x i p => .ne (cellOf loc x) (cellOf loc i) (cellOf loc p)
  | .rangeCheck x y t1 t2 k =>
      .range (cellOf loc x) (cellOf loc y) (cellOf loc t1) (cellOf loc t2) (cellOf loc k)
  | .assertInK a b => .inK (cellOf loc a) (cellOf loc b)
  | .keccak ins outs inOdd outOdd => .keccak (cellsOf loc ins) (cellsOf loc outs) inOdd outOdd
  | .frameAddr p run => .addr (cellOf loc p) (cellsOf loc run)
  | .hint _ => .none
  | .touch t p => .load (cellOf loc t) (cellOf loc p) 0

/-- `k ns`, the list and its numbers evaluated first. -/
def natsSeq {β : Type} : List ℕ → (List ℕ → β) → β
  | [], k => k []
  | n :: ns, k => natSeq n fun n ↦ natsSeq ns fun ns ↦ k (n :: ns)

theorem natsSeq_eq {β : Type} (l : List ℕ) (k : List ℕ → β) : natsSeq l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons n ns ih => simp only [natsSeq, natSeq_eq, ih]

/-- `k a`, the cells of `a` evaluated first. -/
def LAtom.seq {β : Type} (a : LAtom) (k : LAtom → β) : β :=
  match a with
  | .const d x => natSeq d fun d ↦ k (.const d x)
  | .add d a b => natsSeq [d, a, b] fun l ↦ k (.add (listElementOrDefault l 0 0) (listElementOrDefault l 1 0) (listElementOrDefault l 2 0))
  | .mul d a b => natsSeq [d, a, b] fun l ↦ k (.mul (listElementOrDefault l 0 0) (listElementOrDefault l 1 0) (listElementOrDefault l 2 0))
  | .same a b => natSeq a fun a ↦ natSeq b fun b ↦ k (.same a b)
  | .load d p off => natsSeq [d, p, off] fun l ↦ k (.load (listElementOrDefault l 0 0) (listElementOrDefault l 1 0) (listElementOrDefault l 2 0))
  | .ne x i p => natsSeq [x, i, p] fun l ↦ k (.ne (listElementOrDefault l 0 0) (listElementOrDefault l 1 0) (listElementOrDefault l 2 0))
  | .range x y t1 t2 c => natsSeq [x, y, t1, t2, c] fun l ↦
      k (.range (listElementOrDefault l 0 0) (listElementOrDefault l 1 0) (listElementOrDefault l 2
          0) (listElementOrDefault l 3 0) (listElementOrDefault l 4 0))
  | .inK a b => natSeq a fun a ↦ natSeq b fun b ↦ k (.inK a b)
  | .keccak ins outs inOdd outOdd =>
      natsSeq ins fun ins ↦ natsSeq outs fun outs ↦ k (.keccak ins outs inOdd outOdd)
  | .addr p run => natSeq p fun p ↦ natsSeq run fun run ↦ k (.addr p run)
  | .none => k .none

theorem LAtom.seq_eq {β : Type} (a : LAtom) (k : LAtom → β) : a.seq k = k a := by
  cases a <;> simp [LAtom.seq, natSeq_eq, natsSeq_eq, listElementOrDefault]

/-- The run's cells are consecutive from `base`. -/
def runCells : ℕ → List ℕ → Bool
  | _, [] => true
  | base, c :: cs => c == base && runCells (base + 1) cs

section LAtoms

variable (F : Exec.Facts) (B : Book) (ψ : Trie Sym)

/-- `addr` on cells. -/
noncomputable def addrOkC (p : ℕ) (run : List ℕ) : Bool :=
  (look B p).any fun a ↦ match a with
    | .instr _ (.mul x y z) => z == p && (match fpgChain F B ψ fpgDepth x, gpAt F B ψ y with
        | some e1, some e2 => runCells (e1 + e2) run
        | _, _ => false)
    | _ => false

/-- `atomOk` on a located atom. -/
noncomputable def atomOkL : LAtom → Bool
  | .const d x => setIs B d x
  | .add d a b => addOk B d a b
  | .mul d a b => mulOk B d a b
  | .same a b => sameOk B a b
  | .load d p off => loadOk B d p off
  | .ne x i p => neOk B x i p
  | .range x y t1 t2 k => rangeOk B x y t1 t2 k
  | .inK a b => inKOk B a b
  | .keccak ins outs inOdd outOdd => keccakOk B ins outs inOdd outOdd
  | .addr p run => addrOkC F B ψ p run
  | .none => true

end LAtoms

theorem runCells_cellsOf (loc : Trie ℕ) : ∀ (base : ℕ) (vs : List Core.V),
    runCells base (cellsOf loc vs) = runAt loc base vs
  | _, [] => rfl
  | base, v :: vs => by
    simp only [cellsOf, List.map_cons, runCells, runAt]
    rw [← runCells_cellsOf loc (base + 1) vs]
    rfl

theorem atomOkL_locate (F : Exec.Facts) (B : Book) (ψ : Trie Sym) (loc : Trie ℕ) (a : Core.Atom) :
    atomOkL F B ψ (locate loc a) = atomOk F B ψ loc a := by
  cases a <;> simp only [locate, atomOkL, atomOk]
  simp only [addrOkC, addrOk, runCells_cellsOf]

/-! ## Functions, the walk's context and state -/

/-- What a caller knows of a function: its name, entry, arity, the self frame pointer cells of
its entry environment, the bounds on its frame cells before (`pre`) and after (`post`), a pair
`(o, n)` saying `fp[o] = g^e` with `e < n`, the bounds on memory it assumes (`mem`), a triple
`(o, c, n)` saying that the word at `fp[o]·g^c` is `g^e` with `e < n`, and
the tuples of frame cells `(t, os)` whose words it assumes in the program's semantic relation
tagged `t` (`sem`, `Glob.sem`; tag `tagNe`: the two words differ). -/
structure Sig where
  name : String
  entry : ℕ
  nargs : ℕ
  nret : ℕ
  env : List (ℕ × Sym)
  pre : List (ℕ × ℕ)
  post : List (ℕ × ℕ)
  mem : List (ℕ × ℕ × ℕ)
  sem : List (ℕ × List ℕ)

/-- The start of a window of a function's check after the first: at the code offset `J`, in the
environment `env`, at core statement `start`, with the atoms `facts` filed under their cells and
the bounds `bnd` the previous window hands on, and the bounds on memory through its cells
`known`, `(o, c, n)` as in `Sig.mem`, the bounds on memory read through its cells `knownIf`, a
triple `(o, c, n)` saying that a word read at `fp[o]·g^c` is `g^e` with `e < n`, and the tagged
tuples of cells `sems` in the semantic relation, that it does not check but takes from
obligations on the statements before it. -/
structure Cut where
  J : ℕ
  env : List (ℕ × Sym)
  start : ℕ
  facts : List (ℕ × Exec.Atom) := []
  bnd : List (ℕ × ℕ) := []
  known : List (ℕ × ℕ × ℕ) := []
  knownIf : List (ℕ × ℕ × ℕ) := []
  sems : List (ℕ × List ℕ) := []

/-- The certificate of one compiled function. -/
structure Cert where
  /-- The executor's facts. -/
  facts : Exec.Facts
  /-- The frame cell of each core value, by its number, window by window: window `i`'s are the
  cells `cells[i]` of the values from `los[i]`, and `ins[i]` those of the values its statements
  name outside them, `(value, cell, window whose cells hold it)`. -/
  los : List ℕ
  cells : List (List ℕ)
  ins : List (List (ℕ × ℕ × ℕ))
  /-- The number of return words. -/
  nret : ℕ
  /-- The functions it calls, by index. -/
  callees : List ℕ
  /-- Bounds on its frame cells before and after, and on memory, as in `Sig`. -/
  pre : List (ℕ × ℕ) := []
  post : List (ℕ × ℕ) := []
  mem : List (ℕ × ℕ × ℕ) := []
  sem : List (ℕ × List ℕ) := []
  /-- Where each window after the first starts (`Cut`). -/
  cuts : List Cut := []
  /-- The code offset each window's executor runs to, but the last's (which runs to the end). -/
  ends : List ℕ := []
  /-- The entered windows (chained `match`es'): `(i, sel, succ)`, window `i` starting at the arms
  `succ` (its `J` the first) of a `match` on the value in cell `sel`. -/
  entered : List (ℕ × ℕ × List ℕ) := []

/-- The program's context of a check: every function's `Sig` by index, the indices of the
functions checked, the jump table, slot to target pc, and the relations on words over the memory,
by tag, that functions may assume of their arguments (`Sig.sem`; never evaluated; tag `tagNe` is
the checker's own, `a ≠ b`). -/
structure Glob where
  sig : ℕ → Sig
  good : ℕ → Bool
  jt : Trie ℕ
  sem : ℕ → Core.Reader → List E → Prop

/-- The tag of the relation `a ≠ b` on two words, which the checker discharges itself at a call
guarded by `a + b` (`neAt`). -/
def tagNe : ℕ := 1

/-- A conditional tag, `2^32` and above: `impTag t k l` holds of words whose `k`-th word, `k < 8`,
is the immediate `l` (one limb) only if those of tag `t < 2^32` do. A window's obligation on a
call's argument that is a constant `SET` after the window's start (in the call's own setup) takes
this form, and the call checks the constant (`semOk`). -/
def impTag (t k l : ℕ) : ℕ := t + 2 ^ 32 * (1 + k + 8 * l)

/-- A conditional tag's tag. -/
def impBase (t : ℕ) : ℕ := t % 2 ^ 32

/-- A tag conditional on a dispatch's arm, in `[2^31, 2^32)`: `selTag t e`, `t < 2^26`, `e < 32`,
holds of words whose last is `g^e` only if the others are in the relation of tag `t`. A window's
obligation on the arguments of a dispatched callee, which only arm `e` assumes, takes this form on
the arguments' cells and the selector's, and the dispatch checks the selector (`semOk`). -/
def selTag (t e : ℕ) : ℕ := 2 ^ 31 + 32 * t + e

/-- A tag conditional on a dispatch's arm: its tag. -/
def selBase (t : ℕ) : ℕ := (t - 2 ^ 31) / 32

/-- A tag conditional on a dispatch's arm: its arm. -/
def selArm (t : ℕ) : ℕ := (t - 2 ^ 31) % 32

/-- A conditional tag's position. -/
def impPos (t : ℕ) : ℕ := (t / 2 ^ 32 - 1) % 8

/-- A conditional tag's immediate. -/
def impImm (t : ℕ) : ℕ := (t / 2 ^ 32 - 1) / 8

/-- The context of one window's walk: its segments and their index, the bounds on memory words
read through its cells `mem` (the function's `mem` and the window's `known` and `knownIf`, as in
`Cut.knownIf`), its `known` and the cells `sems` in the semantic relation (as in `Cert`, `Cut`),
a window's end
`win = (J, facts, bounds)`: the atoms and bounds a walk arriving at `J` hands to the next window,
and the environment `wenv` the exits into `wJ = J` hold when no segment of the window starts
there. -/
structure Fx where
  G : Glob
  F : Exec.Facts
  entry : ℕ
  segs : List Exec.Seg
  idx : Trie Exec.Seg
  loc : Trie ℕ
  nargs : ℕ
  nret : ℕ
  main : Bool
  callees : List ℕ
  post : List (ℕ × ℕ)
  mem : List (ℕ × ℕ × ℕ)
  known : List (ℕ × ℕ × ℕ)
  sems : List (ℕ × List ℕ)
  win : Option (ℕ × List (ℕ × Exec.Atom) × List (ℕ × ℕ))
  wJ : ℕ
  wenv : Trie Sym

/-- A position of the walk: a segment and its items not yet passed, the book, the segment's entry
environment, the known bounds `(cell, n)`, and `fresh = some t` at the start of segment `t`
before any item is passed. -/
structure CS where
  seg : Exec.Seg
  its : List Exec.Item
  book : Book
  psi : Trie Sym
  bnd : List (ℕ × ℕ)
  fresh : Option ℕ

/-- `k st`, its book evaluated first. -/
def CS.seq {β : Type} (st : CS) (k : CS → β) : β :=
  match st with
  | ⟨s, its, b, p, n, f⟩ => b.seq fun b ↦ k ⟨s, its, b, p, n, f⟩

theorem CS.seq_eq {β : Type} (st : CS) (k : CS → β) : st.seq k = k st := by
  cases st
  simp only [CS.seq, Trie.seq_eq]

/-- The start of segment `t`. -/
noncomputable def segAt (X : Fx) (t : ℕ) (B : Book) (bnd : List (ℕ × ℕ)) : Option CS :=
  match getF X.idx t with
  | some s => bif s.start == t then some ⟨s, s.items, B, s.env, bnd, some t⟩ else none
  | none => none

/-! ## Passing items -/

/-- Pass items into the book until `test` holds, never past a branch; whether it held. -/
noncomputable def fwdL (test : Book → Bool) : List Exec.Item → Book → List Exec.Item × Book × Bool
  | [], B => ([], B, test B)
  | it :: its, B =>
    bif test B then (it :: its, B, true)
    else match it with
      | .ins a => (addFact B a).seq fun B ↦ fwdL test its B
      | .fact a => (addFact B a).seq fun B ↦ fwdL test its B
      | .branch .. => (it :: its, B, false)

/-- Pass items until `test` holds. -/
noncomputable def fwd (test : Book → Bool) (st : CS) : CS × Bool :=
  match st with
  | ⟨s, its, B, ψ, bnd, fr⟩ =>
    bif test B then (⟨s, its, B, ψ, bnd, fr⟩, true)
    else match fwdL test its B with
      | (its, B, ok) => (⟨s, its, B, ψ, bnd, none⟩, ok)

/-- Pass every item before the next branch or the end. -/
noncomputable def toEnd (st : CS) : CS :=
  match st with
  | ⟨s, its, B, ψ, bnd, _⟩ => match fwdL (fun _ ↦ false) its B with
    | (its, B, _) => ⟨s, its, B, ψ, bnd, none⟩

/-- The position at the end of the segment, if no branch is before it. -/
noncomputable def endAt (st : CS) : Option CS :=
  match toEnd st with
  | ⟨s, [], B, ψ, bnd, f⟩ => some ⟨s, [], B, ψ, bnd, f⟩
  | _ => none

/-- The next branch: the position after it, its condition cell and its exit. -/
noncomputable def branchAt (st : CS) : Option (CS × ℕ × Exec.Exit) :=
  match toEnd st with
  | ⟨s, .branch oc _ _ x :: its, B, ψ, bnd, _⟩ => some (⟨s, its, B, ψ, bnd, none⟩, oc, x)
  | _ => none

/-- Where a block's walk ends, and the position there: the segment it is at the start of, or the
target of the local jump that ends its segment. -/
noncomputable def endOf (st : CS) : Option (ℕ × CS) :=
  match st.fresh with
  | some t => some (t, st)
  | none => match endAt st with
    | some se => match se.seg.exit.kind with
      | .next t => bif se.seg.exit.succ == [t] then some (t, se) else none
      | _ => none
    | none => none

/-! ## Calls -/

/-! ### Selectors bounded by booleanity

A selector `x = 1 + b·(1 + g^k)` with `b·b = b` is `g^0` or `g^k`, so `x = g^e` with `e < k + 1`,
and a product of selectors `g^e₁ · g^e₂` with `e₁ < n₁`, `e₂ < n₂` is `g^(e₁ + e₂)` with
`e₁ + e₂ < n₁ + n₂ - 1`: the guest dispatches on such selectors (`odd_g` in `verify_keccak`,
`r_g` in `shared_selector_tables`), bounded by no range check. `selBound` finds the bound in the
book: an `XOR` of a cell `SET` to `1` and a `MUL` of a boolean cell (`MUL b = b·b`) by a cell
`SET` to `1 + g^k` (`onePlusPow`), and products of such, `fuel` deep. -/

/-- `k` with `k0 = 2^k + 1` and `1 ≤ k ≤ 63`: the bits of `1 + g^k` (`ofBits_onePlusPow`). -/
def onePlusPow (k0 : ℕ) : Option ℕ :=
  (List.range 63).findSome? fun i ↦ bif 2 ^ (i + 1) + 1 == k0 then some (i + 1) else none

/-- The first of two options that is `some`. -/
def orOpt {α : Type} : Option α → Option α → Option α
  | some a, _ => some a
  | none, b => b

/-- `o` if `p`, else `none`. -/
def optIf {α : Type} (p : Bool) (o : Option α) : Option α := bif p then o else none

section Sel

variable (B : Book)

/-- `fp[q] = 1 + g^k`, by a `SET`: `k`. -/
noncomputable def selConst (q : ℕ) : Option ℕ :=
  (look B q).findSome? fun a ↦ match a with
    | .instr _ (.set o k0 k1) => optIf (o == q && k1 == 0) (onePlusPow k0)
    | _ => none

/-- `fp[u] = fp[b] · (1 + g^k)` with `fp[b]·fp[b] = fp[b]`, by a `MUL`: `k`. -/
noncomputable def boolScaled (u : ℕ) : Option ℕ :=
  (look B u).findSome? fun a ↦ match a with
    | .instr _ (.mul x y z) =>
        optIf (z == u) (orOpt (optIf (mulOk B x x x) (selConst B y))
          (optIf (mulOk B y y y) (selConst B x)))
    | _ => none

/-- `fp[c] = 1 + fp[b] · (1 + g^k)` with `fp[b]·fp[b] = fp[b]`, by an `XOR`: the bound `k + 1`. -/
noncomputable def boolSel (c : ℕ) : Option ℕ :=
  (look B c).findSome? fun a ↦ match a with
    | .instr _ (.xor x y z) =>
        optIf (z == c) ((orOpt (optIf (setImm B x 1 0) (boolScaled B y))
          (optIf (setImm B y 1 0) (boolScaled B x))).map (· + 1))
    | _ => none

/-- **A bound on a selector from booleanity**: `boolSel`, or a `MUL` of two such, `fuel` deep. -/
noncomputable def selBound : ℕ → ℕ → Option ℕ
  | 0, c => boolSel B c
  | fuel + 1, c =>
    orOpt (boolSel B c) ((look B c).findSome? fun a ↦ match a with
      | .instr _ (.mul x y z) =>
          optIf (z == c) (match selBound fuel x, selBound fuel y with
            | some n₁, some n₂ => some (n₁ + n₂ - 1)
            | _, _ => none)
      | _ => none)

end Sel

/-- The depth of the products `boundOk` follows in `selBound`. -/
def selFuel : ℕ := 3

/-- A bound `e < n` on `fp[c]` from its own facts: a range check of it against a bound at most
`n`, a read through a frame cell whose memory read is bounded at that offset (`mem`), a known
bound, or
a selector bounded by booleanity (`selBound`). -/
noncomputable def boundBase (mem : List (ℕ × ℕ × ℕ)) (B : Book) (bnd : List (ℕ × ℕ)) (c n : ℕ) :
    Bool :=
  (look B c).any (fun a ↦ match a with
    | .range x _ k => x == c && Nat.ble k n
    | .instr _ (.deref o1 o2 o3 .cell) =>
        o3 == c && mem.any fun m ↦ m.1 == o1 && m.2.1 == o2 && Nat.ble m.2.2 n
    | _ => false) ||
  bnd.any (fun p ↦ p.1 == c && Nat.ble p.2 n) ||
  (match selBound B selFuel c with
    | some m => Nat.ble m n
    | none => false)

/-- `fp[x]` times a known power `g^k` (`gpAt`) is bounded by `n` when `fp[x]` is by `n - k`. -/
noncomputable def boundScaled (F : Exec.Facts) (ψ : Trie Sym) (mem : List (ℕ × ℕ × ℕ)) (B : Book)
    (bnd : List (ℕ × ℕ)) (x y n : ℕ) : Bool :=
  match gpAt F B ψ y with
  | some k => Nat.ble k n && boundBase mem B bnd x (n - k)
  | none => false

/-- A bound `e < n` on `fp[c]`: `boundBase`, a known power `g^k`, `k < n` (`gpAt`: `verify_tables`'
`kappa_g = kb[0]·g^adj`, a constant), or a product `fp[c] = fp[x]·g^k` by a known power of `g`
with `fp[x]` bounded by `n - k` (`boundScaled`): the guest shifts a bounded exponent by a
constant (`check_opening_terminal`'s `kb[i]·g^adj`). -/
noncomputable def boundOk0 (F : Exec.Facts) (ψ : Trie Sym) (mem : List (ℕ × ℕ × ℕ)) (B : Book)
    (bnd : List (ℕ × ℕ)) (c n : ℕ) : Bool :=
  boundBase mem B bnd c n ||
  (match gpAt F B ψ c with
    | some k => Nat.blt k n
    | none => false) ||
  (look B c).any (fun a ↦ match a with
    | .instr _ (.mul x y z) => z == c &&
        (boundScaled F ψ mem B bnd x y n || boundScaled F ψ mem B bnd y x n)
    | _ => false)

/-- A bound `e < n` on `fp[c]`: `boundOk0` of it, or of a cell it is a copy of (a returned word
copied into a return cell, as `list_split` and `log2_ceil_in_the_exponent` return a checked
one). -/
noncomputable def boundOk (F : Exec.Facts) (ψ : Trie Sym) (mem : List (ℕ × ℕ × ℕ)) (B : Book)
    (bnd : List (ℕ × ℕ)) (c n : ℕ) : Bool :=
  boundOk0 F ψ mem B bnd c n ||
  (look B c).any (fun a ↦ match a with
    | .copy d s => (d == c && boundOk0 F ψ mem B bnd s n) || (s == c && boundOk0 F ψ mem B bnd d n)
    | _ => false)

/-- The argument cells, stored into the callee frame `fp[q]` from offset `o`. -/
noncomputable def storesOk (B : Book) (q : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | o, c :: cs => loadOk B c q o && storesOk B q (o + 1) cs

/-- The callee's self frame pointer cells, stored into its frame. -/
noncomputable def envStoresOk (B : Book) (q : ℕ) (env : List (ℕ × Sym)) : Bool :=
  env.all fun p ↦ Sym.beq p.2 (.fpg 0) && loadOk B q q p.1

/-- The callee's argument bounds, on the caller's cells. -/
noncomputable def preOk (F : Exec.Facts) (ψ : Trie Sym) (mem : List (ℕ × ℕ × ℕ)) (B : Book)
    (bnd : List (ℕ × ℕ)) (args : List ℕ) (pre : List (ℕ × ℕ)) : Bool :=
  pre.all fun p ↦ Nat.ble 2 p.1 && Nat.blt (p.1 - 2) args.length &&
    boundOk F ψ mem B bnd (listElementOrDefault args (p.1 - 2) 0) p.2

/-- The callee's memory bounds, on memory the caller knows bounded through its argument cells, at
the same offset. -/
def memOk (known : List (ℕ × ℕ × ℕ)) (args : List ℕ) (mem : List (ℕ × ℕ × ℕ)) : Bool :=
  mem.all fun m ↦ Nat.ble 2 m.1 && Nat.blt (m.1 - 2) args.length &&
    known.any fun k ↦ k.1 == listElementOrDefault args (m.1 - 2) 0 && k.2.1 == m.2.1 && Nat.ble
        k.2.2 m.2.2

/-- The caller's cell of a callee frame cell, the arguments' and returns' cells after `fp[0..1]`. -/
def frameCell (cs : List ℕ) (o : ℕ) : ℕ := listElementOrDefault cs (o - 2) 0

/-- At arm `e` of a dispatch on the cell `c` (`sel`), the callee's tuple `s` on argument cells is
one the caller knows with the selector's cell appended, its tag conditional on that arm
(`selTag`). -/
def selOk (sel : Option (ℕ × ℕ)) (sems : List (ℕ × List ℕ)) (args : List ℕ) (s : ℕ × List ℕ) : Bool :=
  match sel with
  | some (c, e) => Nat.blt s.1 (2 ^ 26) && Nat.blt e 32 &&
      sems.any fun q ↦ q.1 == selTag s.1 e && q.2 == s.2.map (frameCell args) ++ [c]
  | none => false

/-- The callee's tagged tuples of cells in the semantic relation, on argument cells: a tuple the
caller knows with the same tag, or with that tag conditional on a cell the book knows `SET` to the
immediate (`impTag`), or a pair tagged `tagNe` that `ne` gives (`neAt` at a call guarded by their
sum), or, at a dispatch's arm, one `selOk` accepts. -/
noncomputable def semOk (B : Book) (ne : ℕ → ℕ → Bool) (sel : Option (ℕ × ℕ))
    (sems : List (ℕ × List ℕ)) (args : List ℕ) (sem : List (ℕ × List ℕ)) : Bool :=
  sem.all fun s ↦ s.2.all (fun o ↦ Nat.ble 2 o && Nat.blt (o - 2) args.length) &&
    (sems.any (fun q ↦ q.2 == s.2.map (frameCell args) &&
      (q.1 == s.1 || (Nat.ble (2 ^ 32) q.1 && impBase q.1 == s.1 && Nat.blt s.1 (2 ^ 31) &&
        Nat.blt (impPos q.1) s.2.length &&
        setImm B (listElementOrDefault q.2 (impPos q.1) 0) (impImm q.1) 0))) ||
      (s.1 == tagNe && match s.2 with
        | [a, b] => ne (frameCell args a) (frameCell args b)
        | _ => false) || selOk sel sems args s)

/-- The callee's bounds after the call, on the caller's cells. -/
def postBnd (cs : List ℕ) (post : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  post.map fun p ↦ (frameCell cs p.1, p.2)

/-- What a call needs of the callee `s` into the frame `fp[q]`: its name, arity, stored
arguments and self frame pointer cells, bounded arguments and memory, its semantic tuples (pairs
`ne` knows different; at a dispatch's arm, `sel`). -/
noncomputable def callOk (X : Fx) (B : Book) (ψ : Trie Sym) (bnd : List (ℕ × ℕ)) (ne : ℕ → ℕ → Bool)
    (sel : Option (ℕ × ℕ)) (s : Sig) (f : String) (q : ℕ) (args : List ℕ) (nrets : ℕ) : Bool :=
  f == s.name && args.length == s.nargs && nrets == s.nret && storesOk B q 2 args &&
    envStoresOk B q s.env && preOk X.F ψ X.mem B bnd args s.pre && memOk X.known args s.mem &&
    semOk B ne sel X.sems args s.sem &&
    s.post.all (fun p ↦ Nat.ble 2 p.1 && Nat.blt p.1 (2 + s.nargs + s.nret))

/-- The callee at `pc`, among the function's callees, by index. -/
noncomputable def calleeAt (X : Fx) (pc : ℕ) : Option ℕ :=
  X.callees.find? fun j ↦ X.G.good j && (X.G.sig j).entry == pc

/-- The table base of a jump through `fp[t]`: `DEREF *(fp[x]·g^base) = fp[t]`. -/
noncomputable def tableBase (B : Book) (t x : ℕ) : Option ℕ :=
  (look B t).findSome? fun a ↦ match a with
    | .instr _ (.deref o1 o2 o3 .cell) => bif o1 == x && o3 == t then some o2 else none
    | _ => none

/-- Slot `base + j` of the table holds the pc of arm `j`, the function's entry plus its
offset. -/
noncomputable def armsOk (G : Glob) (entry base : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | j, a :: as => G.jt.get (base + j) == some (entry + a) && armsOk G entry base (j + 1) as

/-- Slot `base + j` holds the entry of the callee named `fs[j]`, a callee meeting `ok j`. -/
noncomputable def tableCallsOk (X : Fx) (base : ℕ) (ok : ℕ → String → Sig → Bool) :
    ℕ → List String → Bool
  | _, [] => true
  | j, f :: fs => (match X.G.jt.get (base + j) with
      | some pc => match calleeAt X pc with
        | some j' => ok j f (X.G.sig j')
        | none => false
      | none => false) && tableCallsOk X base ok (j + 1) fs

/-- The returned words read back from the callee frame `fp[q]`. -/
noncomputable def loadsOk (B : Book) (q o : ℕ) (rets : List ℕ) : Bool := storesOk B q o rets

/-- A tail call's next frame `fp·g^S` holds `fp[c]` at cell `S + o`: one cell, or a copy. -/
noncomputable def nextHolds (B : Book) (S o c : ℕ) : Bool := sameOk B (S + o) c

/-- A tail call's arguments in the next frame. -/
noncomputable def tailArgsOk (B : Book) (S : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | o, c :: cs => nextHolds B S o c && tailArgsOk B S (o + 1) cs

/-- A tail call's self frame pointer cell `S + o` of the next frame holds `fp·g^S`: a copy of a
cell the exit's environment knows so. -/
noncomputable def tailEnvOk (B : Book) (env : Trie Sym) (S : ℕ) (o : ℕ) : Bool :=
  (match env.get (S + o) with
    | some (.fpg e) => e == S
    | _ => false) ||
  (look B (S + o)).any fun a ↦ match a with
    | .copy d w => d == S + o && (match env.get w with
        | some (.fpg e) => e == S
        | _ => false)
    | _ => false

/-! ## The walk -/

/-- How a walk ends: at a join, by the return, or not at all. -/
inductive Res where
  | join (J : ℕ)
  | done
  | fail
  /-- The block ends in a table jump through slot `log fp[x]` into the arms `succ` of the next
  `match` of a chain. -/
  | chain (x : ℕ) (succ : List ℕ)
  deriving DecidableEq

/-- The pending atoms hold in the book. -/
noncomputable def pendOk (X : Fx) (st : CS) (P : List Core.Atom) : Bool :=
  P.all fun a ↦ atomOk X.F st.book st.psi X.loc a

/-- At a window's end, the book and bounds hold what the window hands on: the atoms filed, and
bounds `boundOk` gives (one known, a range check, a selector bounded by booleanity). -/
noncomputable def handOk (X : Fx) (J : ℕ) (st : CS) : Bool :=
  match X.win with
  | some (J', fs, bs) => !(J == J') ||
      (fs.all (fun p ↦ (look st.book p.1).contains p.2) &&
        bs.all (fun b ↦ boundOk X.F st.psi X.mem st.book st.bnd b.1 b.2))
  | none => true

/-- The table read into `fp[t]`: `DEREF *(fp[x]·g^base) = fp[t]`, its `(x, base)`. -/
noncomputable def tableSrc (B : Book) (t : ℕ) : Option (ℕ × ℕ) :=
  (look B t).findSome? fun a ↦ match a with
    | .instr _ (.deref o1 o2 o3 .cell) => bif o3 == t then some (o1, o2) else none
    | _ => none

/-- What `chainEnd` checks at the end `se` of a block jumping through `ft`'s frame into the
arms `t0 :: ts`, the table read through `fp[x]` at `base`. -/
noncomputable def chainOk (X : Fx) (se : CS) (ft : Exec.Tgt) (t0 : ℕ) (ts : List ℕ) (x base : ℕ)
    (P : List Core.Atom) : Bool :=
  X.F.self ft && armsOk X.G X.entry base 0 (t0 :: ts) &&
    boundOk X.F se.psi X.mem se.book se.bnd x (ts.length + 1) && pendOk X se P &&
    handOk X t0 se && (!(t0 == X.wJ) || X.wenv.sub Sym.beq se.seg.exit.env)

/-- The end of a block in a chained `match`'s table jump: the segment's exit jumps through
`fp[t]`, read from the table at `base` through `fp[x]`, whose slots hold the arms `succ`, the
selector bounded by their number; every pending atom found; at a window's end its environment
and hand-over in place. -/
noncomputable def chainEnd (X : Fx) (st : CS) (P : List Core.Atom) : Res :=
  match endAt st with
  | some se => match se.seg.exit.kind, se.seg.exit.succ with
    | .jump (.cell t) ft, t0 :: ts =>
        match tableSrc se.book t with
        | some (x, base) => bif chainOk X se ft t0 ts x base P then .chain x (t0 :: ts) else .fail
        | none => .fail
    | _, _ => .fail
  | none => .fail

/-- The end of a block: its join, every pending atom found, a window's hand-over in place; or a
chained `match`'s table jump (`chainEnd`). -/
noncomputable def blockEnd (X : Fx) (st : CS) (P : List Core.Atom) : Res :=
  match endOf st with
  | some (J, se) => bif pendOk X se P && handOk X J se then .join J else .fail
  | none => chainEnd X st P

/-- The function's return: the return jump (`main`: the halting jump), its words in the return
cells, its bounds, every pending atom found. -/
noncomputable def retOk (X : Fx) (vs : List Core.V) (st : CS) (P : List Core.Atom) : Bool :=
  match endAt st with
  | some se =>
      (bif X.main then decide (se.seg.exit.kind = .jump (.gp (2 ^ 19 - 1)) (.gp 0))
        else decide (se.seg.exit.kind = .ret)) &&
      vs.length == X.nret && runAt X.loc (2 + X.nargs) vs && pendOk X se P &&
      X.post.all fun p ↦ boundOk X.F se.psi X.mem se.book se.bnd p.1 p.2
  | none => false

/-- A loop's closing tail call to `s` at the next frame `fp·g^S` from the branch position `st`
with exit `x`, guarded by `fp[oc]`: the callee's name and arity, no returns, bounds after or on
memory, its bounded arguments and semantic tuples (pairs `neAt oc` knows different), the
arguments, the self frame
pointer cells and the return registers copied into the next frame, every pending atom found,
and the fall-through returning. -/
noncomputable def tailOk (X : Fx) (st : CS) (x : Exec.Exit) (oc S : ℕ) (s : Sig) (f : String)
    (ca : List ℕ) (P : List Core.Atom) : Bool :=
  f == s.name && ca.length == s.nargs && s.nret == 0 && X.nret == 0 &&
    preOk X.F st.psi X.mem st.book st.bnd ca s.pre && s.mem.isEmpty && X.post.isEmpty &&
    semOk st.book (neAt st.book oc) none X.sems ca s.sem &&
    tailArgsOk st.book S 2 ca &&
    s.env.all (fun p ↦ Sym.beq p.2 (.fpg 0) && tailEnvOk st.book x.env S p.1) &&
    nextHolds st.book S 0 0 && nextHolds st.book S 1 1 && pendOk X st P && !X.main &&
    (match endAt st with
      | some se => decide (se.seg.exit.kind = .ret)
      | none => false)

/-- After a call into the frame `fp[q]` returning to offset `t`: the position there, once the
returned words are read back into their cells. -/
noncomputable def afterCall (X : Fx) (t q o : ℕ) (cr : List ℕ) (B : Book) (bnd : List (ℕ × ℕ)) :
    Option CS :=
  match segAt X t B bnd with
  | some sr => match fwd (fun B ↦ loadsOk B q o cr) sr with
    | (st', true) => some st'
    | (_, false) => none
  | none => none

/-- The walk after a `match`'s arms that end in the next chained `match`'s table jump through
`fp[x]` into the arms `succ`: the walk `k` of the next `match` of the chain, or, at the end of the
statements (a window ending there, the next one entered at `succ`), that table jump itself, with
nothing pending. -/
def chainTo (x : ℕ) (succ : List ℕ) (ss : List Core.Stmt) (P : List Core.Atom) (k : Res) : Res :=
  bif ss.isEmpty then (bif P.isEmpty then .chain x succ else .fail) else k

mutual
/-- **The walk** of a block from a position, with the atoms pending in it. -/
noncomputable def chkL (X : Fx) : List Core.Stmt → CS → List Core.Atom → Res
  | [], st, P => blockEnd X st P
  | .atom a :: ss, st, P =>
      (locate X.loc a).seq fun la ↦
      match fwd (fun B ↦ atomOkL X.F B st.psi la) st with
      | (st', true) => st'.seq fun st' ↦ chkL X ss st' P
      | (st', false) => st'.seq fun st' ↦ chkL X ss st' (a :: P)
  | .ite c z n :: ss, st, P =>
      match branchAt st with
      | some (st', oc, x) =>
          match x.kind with
          | .next t =>
              bif oc == cellOf X.loc c && x.succ == [t] then
                match segAt X t st'.book st'.bnd with
                | some sn => match chkL X z st' [], chkL X n sn [] with
                  | .join J, .join J' =>
                      bif J == J' then
                        match segAt X J st'.book st'.bnd with
                        | some sj => chkL X ss sj P
                        | none => .fail
                      else .fail
                  | _, _ => .fail
                | none => .fail
              else .fail
          | _ => .fail
      | none => .fail
  | .match_ v arms :: ss, st, P =>
      match endAt st with
      | some se => match se.seg.exit.kind, se.seg.exit.succ, arms with
        | .jump (.cell t) ft, t0 :: ts, a0 :: as =>
            bif X.F.self ft && ts.length == as.length &&
                boundOk X.F se.psi X.mem se.book se.bnd (cellOf X.loc v) (as.length + 1) then
              match tableBase se.book t (cellOf X.loc v) with
              | some base =>
                  bif armsOk X.G X.entry base 0 (t0 :: ts) then
                    match segAt X t0 se.book se.bnd with
                    | some s0 => match chkL X a0 s0 [] with
                      | .join J =>
                          bif chkArms X (.join J) as ts se.book se.bnd then
                            match segAt X J se.book se.bnd with
                            | some sj => chkL X ss sj P
                            | none => .fail
                          else .fail
                      | .chain x succ =>
                          bif chkArms X (.chain x succ) as ts se.book se.bnd then
                            chainTo x succ ss P (chainL X x succ se.book se.psi se.bnd ss P)
                          else .fail
                      | _ => .fail
                    | none => .fail
                  else .fail
              | none => .fail
            else .fail
        | _, _, _ => .fail
      | none => .fail
  | .call f args rets :: ss, st, P =>
      match endAt st with
      | some se => match se.seg.exit.kind with
        | .call (.gp e) q r =>
            match calleeAt X e with
            | some j =>
                bif callOk X se.book se.psi se.bnd (fun _ _ ↦ false) none (X.G.sig j) f q (cellsOf X.loc args)
                    rets.length &&
                    Nat.ble X.entry r && se.seg.exit.succ == [r - X.entry] then
                  match afterCall X (r - X.entry) q (2 + args.length) (cellsOf X.loc rets)
                      se.book se.bnd with
                  | some st' => st'.seq fun st' ↦
                      chkL X ss ⟨st'.seg, st'.its, st'.book, st'.psi,
                        postBnd (cellsOf X.loc args ++ cellsOf X.loc rets) (X.G.sig j).post ++ st'.bnd,
                        st'.fresh⟩ P
                  | none => .fail
                else .fail
            | none => .fail
        | _ => .fail
      | none => .fail
  | .dispatch v fs args rets :: ss, st, P =>
      match endAt st with
      | some se => match se.seg.exit.kind with
        | .call (.cell t) q r =>
            match tableBase se.book t (cellOf X.loc v) with
            | some base =>
                bif boundOk X.F se.psi X.mem se.book se.bnd (cellOf X.loc v) fs.length && Nat.ble X.entry r &&
                    se.seg.exit.succ == [r - X.entry] &&
                    tableCallsOk X base (fun e f s ↦
                      callOk X se.book se.psi se.bnd (fun _ _ ↦ false) (some (cellOf X.loc v, e)) s f q
                        (cellsOf X.loc args)
                        rets.length &&
                        s.post.isEmpty) 0 fs then
                  match afterCall X (r - X.entry) q (2 + args.length) (cellsOf X.loc rets)
                      se.book se.bnd with
                  | some st' => st'.seq fun st' ↦ chkL X ss st' P
                  | none => .fail
                else .fail
            | none => .fail
        | _ => .fail
      | none => .fail
  | .callIf c f args :: ss, st, P =>
      match branchAt st with
      | some (st', oc, x) =>
          bif oc == cellOf X.loc c then
            match x.kind with
            | .call (.gp e) q r =>
                match calleeAt X e with
                | some j =>
                    bif callOk X st'.book st'.psi st'.bnd (neAt st'.book oc) none (X.G.sig j) f q
                        (cellsOf X.loc args) 0 &&
                        (X.G.sig j).post.isEmpty &&
                        Nat.ble X.entry r && x.succ == [r - X.entry] then
                      match endOf st', segAt X (r - X.entry) st'.book st'.bnd with
                      | some (t, _), some sr => bif t == r - X.entry then chkL X ss sr P else .fail
                      | _, _ => .fail
                    else .fail
                | none => .fail
            | .jump (.gp e) (.fpg S) =>
                match calleeAt X e, ss with
                | some j, [.ret []] =>
                    bif tailOk X st' x oc S (X.G.sig j) f (cellsOf X.loc args) P then .done else .fail
                | _, _ => .fail
            | _ => .fail
          else .fail
      | none => .fail
  | .ret vs :: _, st, P => bif retOk X vs st P then .done else .fail

/-- The other arms of a `match`, each from its offset, ending as arm `0` does, `r`: at its join,
or in the next chained `match`'s table jump. -/
noncomputable def chkArms (X : Fx) (r : Res) :
    List (List Core.Stmt) → List ℕ → Book → List (ℕ × ℕ) → Bool
  | [], [], _, _ => true
  | a :: as, t :: ts, B, bnd => (match segAt X t B bnd with
      | some st => chkL X a st [] == r
      | none => false) && chkArms X r as ts B bnd
  | _, _, _, _ => false

/-- **A chained `match`**, entered from the previous one's arms by a table jump through slot
`log fp[x]` into the arms `succ`: the `match` on the value in `fp[x]`, one arm per target, each
walked from its offset with the book, environment and bounds `(B, ψ, bnd)` of the chain's first
dispatch, all ending at one join (the walk goes on there) or in one next table jump (the next
`match` of the chain). -/
noncomputable def chainL (X : Fx) (x : ℕ) (succ : List ℕ) (B : Book) (ψ : Trie Sym)
    (bnd : List (ℕ × ℕ)) : List Core.Stmt → List Core.Atom → Res
  | .match_ v arms :: ss, P =>
      match succ, arms with
      | t0 :: ts, a0 :: as =>
          bif cellOf X.loc v == x && ts.length == as.length then
            match segAt X t0 B bnd with
            | some s0 => match chkL X a0 s0 [] with
              | .join J =>
                  bif chkArms X (.join J) as ts B bnd then
                    match segAt X J B bnd with
                    | some sj => chkL X ss sj P
                    | none => .fail
                  else .fail
              | .chain x' succ' =>
                  bif chkArms X (.chain x' succ') as ts B bnd then
                    chainTo x' succ' ss P (chainL X x' succ' B ψ bnd ss P)
                  else .fail
              | _ => .fail
            | none => .fail
          else .fail
      | _, _ => .fail
  | _, _ => .fail
end

/-! ## A function, by windows

A function is checked in windows, each by its own kernel evaluation: window `i` runs the executor
from its start (`execWin`) to its end offset and walks its core statements from its start, with
the facts and bounds the previous window hands on; it ends at the next window's start, a join
where it hands on what the next needs (`Fx.win`, `handOk`) in an environment holding the next
one's, or, the last, by the return. A function of one window is `cuts = []`. -/

/-- Successors starting a segment of the index start it, in an environment their exit's holds; a
successor starting none (past a window's end) is left to the walk, which cannot go there, but
for the window's end `wJ`, whose environment `wenv` the exit's holds. -/
noncomputable def linkedWeak (idx : Trie Exec.Seg) (segs : List Exec.Seg) (wJ : ℕ) (wenv : Trie Sym) :
    Bool :=
  segs.all fun s ↦ s.exits.all fun x ↦ x.succ.all fun t ↦
    match getF idx t with
    | some s' => s'.start == t && s'.env.sub Sym.beq x.env
    | none => !(t == wJ) || wenv.sub Sym.beq x.env

/-- The facts a window starts with, filed under their cells. -/
noncomputable def bookOf : List (ℕ × Exec.Atom) → Book → Book
  | [], B => B
  | p :: ps, B => (addKey p.2 B p.1).seq fun B ↦ bookOf ps B

/-- Where window `i` starts: the function's entry for the first. -/
def Cert.cutAt (C : Cert) : ℕ → Cut
  | 0 => ⟨0, C.facts.env, 0, [], C.pre, [], [], C.sem⟩
  | i + 1 => listElementOrDefault C.cuts i ⟨0, [], 0, [], [], [], [], []⟩

/-- Window `i` entered (a chained `match`'s): the selector cell and the arms it starts at, or
`(0, [])`; never the first. -/
def Cert.enteredAt (C : Cert) : ℕ → ℕ × List ℕ
  | 0 => (0, [])
  | i + 1 => match C.entered.find? (·.1 == i + 1) with
    | some (_, s, l) => (s, l)
    | none => (0, [])

/-- The selector cell of an entered window. -/
def Cert.selAt (C : Cert) (i : ℕ) : ℕ := (C.enteredAt i).1

/-- The arms an entered window starts at (`[]`: not entered). -/
def Cert.succAt (C : Cert) (i : ℕ) : List ℕ := (C.enteredAt i).2

/-- The code offset window `i`'s executor runs to. -/
def Cert.endAt (C : Cert) (f : CompiledFunction) (i : ℕ) : ℕ :=
  bif Nat.blt i C.cuts.length then listElementOrDefault C.ends i 0 else f.instructionCount

/-- The core statements of window `i`. -/
def Cert.stmtsAt (C : Cert) (cf : Core.Fn) (i : ℕ) : List Core.Stmt :=
  bif Nat.blt i C.cuts.length then
    (cf.body.drop (C.cutAt i).start).take ((C.cutAt (i + 1)).start - (C.cutAt i).start)
  else cf.body.drop (C.cutAt i).start

/-- The walk's context of window `i` over the segments `segs`. -/
noncomputable def Cert.fxAt (G : Glob) (f : CompiledFunction) (cf : Core.Fn) (C : Cert) (main
    : Bool)
    (i : ℕ) (segs : List Exec.Seg) (idx : Trie Exec.Seg) (loc : Trie ℕ) : Fx :=
  ⟨G, C.facts, f.entryPc, segs, idx, loc, cf.params.length, C.nret, main, C.callees, C.post,
    C.mem ++ ((C.cutAt i).known ++ (C.cutAt i).knownIf), (C.cutAt i).known, (C.cutAt i).sems,
    bif Nat.blt i C.cuts.length then
      some ((C.cutAt (i + 1)).J, (C.cutAt (i + 1)).facts, (C.cutAt (i + 1)).bnd)
    else none,
    bif Nat.blt i C.cuts.length then (C.cutAt (i + 1)).J else 0,
    bif Nat.blt i C.cuts.length then envOf (C.cutAt (i + 1)).env else .nil⟩

/-- How window `i` must end: at the next window's start (a later statement), in an environment
holding the next one's (at a segment of the window starting there, or by `linkedWeak`), or by
the return. -/
noncomputable def winEnd (C : Cert) (i : ℕ) (idx : Trie Exec.Seg) (r : Res) : Bool :=
  bif Nat.blt i C.cuts.length then
    (bif (C.succAt (i + 1)).isEmpty then r == .join (C.cutAt (i + 1)).J
      else r == .chain (C.selAt (i + 1)) (C.succAt (i + 1)) &&
        (C.succAt (i + 1)).head? == some (C.cutAt (i + 1)).J) &&
      Nat.ble (C.cutAt i).start (C.cutAt (i + 1)).start &&
      (match getF idx (C.cutAt (i + 1)).J with
      | some s => s.start == (C.cutAt (i + 1)).J && (envOf (C.cutAt (i + 1)).env).sub Sym.beq s.env
      | none => true)
  else r == .done

/-- The frame cell of each core value: the windows' cells in order. -/
def Cert.locs (C : Cert) : List ℕ := C.cells.flatten

/-- Store the cells of `ps` into `t`. -/
noncomputable def insTrie : List (ℕ × ℕ × ℕ) → Trie ℕ → Trie ℕ
  | [], t => t
  | p :: ps, t => (setF p.2.1 indexDepth t p.1).seq fun t ↦ insTrie ps t

/-- Window `i`'s cells: its own, and those its statements name outside them. -/
noncomputable def Cert.locAt (C : Cert) (i : ℕ) : Trie ℕ :=
  (locTrieFrom (listElementOrDefault C.cells i []) (listElementOrDefault C.los i 0) .nil).seq fun t
      ↦ insTrie (listElementOrDefault C.ins i []) t

/-- The windows' cells are consecutive: window `0`'s from value `0`, window `i + 1`'s right after
window `i`'s. -/
def Cert.contOk (C : Cert) (i : ℕ) : Bool :=
  (bif i == 0 then listElementOrDefault C.los 0 0 == 0 else true) &&
    (bif Nat.blt i C.cuts.length then listElementOrDefault C.los (i + 1) 0 == listElementOrDefault C.los i 0 + (listElementOrDefault C.cells i []).length
      else true)

/-- The cells a window takes from other windows are theirs. -/
def Cert.insOk (C : Cert) (ps : List (ℕ × ℕ × ℕ)) : Bool :=
  ps.all fun p ↦ Nat.ble p.2.2 C.cuts.length && Nat.ble (listElementOrDefault C.los p.2.2 0) p.1 &&
    (listElementOrDefault C.cells p.2.2 [])[p.1 - listElementOrDefault C.los p.2.2 0]? == some p.2.1

/-- The values an atom names. -/
def atomVals : Core.Atom → List Core.V
  | .const d _ => [d]
  | .add d a b => [d, a, b]
  | .mul d a b => [d, a, b]
  | .copy d x => [d, x]
  | .assertEq d x => [d, x]
  | .assertInK d x => [d, x]
  | .load d q _ => [d, q]
  | .assertNe x i q => [x, i, q]
  | .rangeCheck x y t1 t2 k => [x, y, t1, t2, k]
  | .keccak ins outs _ _ => ins ++ outs
  | .frameAddr q run => q :: run
  | .hint _ => []
  | .touch t q => [t, q]

mutual
/-- The values a statement names. -/
def stmtVals : Core.Stmt → List Core.V
  | .atom a => atomVals a
  | .ite c z n => c :: (stmtsVals z ++ stmtsVals n)
  | .match_ x arms => x :: armsVals arms
  | .call _ args rets => args ++ rets
  | .callIf c _ args => c :: args
  | .dispatch x _ args rets => x :: (args ++ rets)
  | .ret vs => vs

/-- The values a block names. -/
def stmtsVals : List Core.Stmt → List Core.V
  | [] => []
  | s :: ss => stmtVals s ++ stmtsVals ss

/-- The values arms name. -/
def armsVals : List (List Core.Stmt) → List Core.V
  | [] => []
  | a :: as => stmtsVals a ++ armsVals as
end

/-- Every value of the statements has a cell. -/
noncomputable def covOk (loc : Trie ℕ) (ss : List Core.Stmt) : Bool :=
  (stmtsVals ss).all fun v ↦ (getF loc v.idx).isSome

/-- An entered window's arms each start a segment of its executor, in an environment its start's
holds. -/
noncomputable def startsOk (idx : Trie Exec.Seg) (env : List (ℕ × Sym)) (succ : List ℕ) : Bool :=
  succ.all fun t ↦ match getF idx t with
    | some s => s.start == t && s.env.sub Sym.beq (envOf env)
    | none => false

/-- A window's walk from its start `st`: the statements from the segment there, or, entered, the
chained `match` from its arms `succ` with the book, environment and bounds of `st`. -/
noncomputable def walkFrom (X : Fx) (env : List (ℕ × Sym)) (sel : ℕ) (succ : List ℕ)
    (ss : List Core.Stmt) (st : CS) : Res :=
  bif succ.isEmpty then chkL X ss st []
  else bif startsOk X.idx env succ then chainL X sel succ st.book st.psi st.bnd ss [] else .fail

theorem walkFrom_nil {X : Fx} {env : List (ℕ × Sym)} {sel : ℕ} {succ : List ℕ} (h : succ = [])
    (ss : List Core.Stmt) (st : CS) : walkFrom X env sel succ ss st = chkL X ss st [] := by
  simp [walkFrom, h]

/-- **The check of window `i`** of `f` with core function `cf` and certificate `C`: its
executor's segments are linked, its cells are the certificate's and cover its statements, its walk
starts at its start offset in its environment with what the previous window handed on, and ends
as `winEnd` says; the first window also has the parameters in their cells. -/
noncomputable def checkWin (G : Glob) (f : CompiledFunction) (cf : Core.Fn) (C : Cert) (main : Bool)
    (i : ℕ) : Bool :=
  match execWinS C.facts f (C.cutAt i).J (C.cutAt i).env ((C.succAt i).drop 1) (C.endAt f i) with
  | ⟨segs, _⟩ => listSeq segs fun segs ↦ (index segs).seq fun idx ↦ (C.locAt i).seq fun loc ↦
      C.contOk i && C.insOk (listElementOrDefault C.ins i []) && covOk loc (C.stmtsAt cf i) &&
      linkedWeak idx segs (C.fxAt G f cf main i segs idx loc).wJ (C.fxAt G f cf main i segs idx loc).wenv &&
      (bif i == 0 then runAt loc 2 cf.params && main == C.facts.fpOne else true) &&
      (match segAt (C.fxAt G f cf main i segs idx loc) (C.cutAt i).J
          (bookOf (C.cutAt i).facts .nil) (C.cutAt i).bnd with
        | some st => st.seg.env.sub Sym.beq (envOf (C.cutAt i).env) &&
            winEnd C i idx (walkFrom (C.fxAt G f cf main i segs idx loc) (C.cutAt i).env (C.selAt i)
              (C.succAt i) (C.stmtsAt cf i) st)
        | none => false)

end
end LeanVM.Guest.Check
