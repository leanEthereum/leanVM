/-
  LeanVM.Guest.ExecCore

  The symbolic executor of compiled functions: one pass over a function's code that cuts it into
  segments at the joins of its forward control flow, and turns each into atoms, one per executed
  instruction, along its forward paths, with the exits it leaves by. Its definitions alone: what
  it means and why it is sound are `Exec.lean`.
-/

module

public import LeanVM.Guest.Code

/-!
# The symbolic executor

`exec F f` walks the code of a compiled function `f` once, from offset `0`, and returns its
**segments** (`Seg`): a segment starts at the function's entry, at a forward jump's target, at a
dispatch arm or at the return point of a call, and runs straight until the next such start or a
jump that does not fall through. Its `items` are the path's atoms (`Item.ins`, one per executed
instruction, and `Item.fact`, what a recognized gadget means) and its forward branches
(`Item.branch`: a `JUMP` on an unknown condition, which falls through when the condition is zero
and leaves by its exit otherwise); `exit` is where the path leaves when it reaches the end.

What is known of the frame along a path is an **environment** (`Trie Sym`, by offset): the cells
holding `0`, a power of `g` (a `SET` whose immediate `Facts.pows` names, `g^0` always), or the
frame pointer times one (`fpg`: a loop's self frame pointer cell, the bounce through a hinted
buffer, a loop's next frame `MUL nfp = own·g^S`), and the last stores through frame cells. It
recognizes the jump shapes the compiler emits (`Kind`): a local forward jump (`next`), a return,
a call or a fused dispatch into a callee frame whose return registers it stored (`call`), and
everything else, tail calls, table dispatch and halting, as a jump to the registers it names
(`jump`). The gadgets it recognizes are facts: `!=`, booleanity, copies through `MUL x·1`,
`assert ==`, and the range check (`range` when the bound is a known power, `powPair` when it is
computed). At a join the entry environment is the intersection of the environments of the
edges into it; `Result.linked` checks that each edge's environment holds the target's, so the
executor's own bookkeeping is never trusted.

Inputs from outside are `Facts`: the entry environment (a loop's self frame pointer cell), the
cells whose products by powers of `g` are tracked, whether the frame is `1` (`main`), the powers
of `g` its constants name (a search tree the caller checks, `PowTree.Ok`), and the arms of each
table dispatch. A selector's bound is not an input: the dispatch exit names the register it
reads (`Tgt.cell`), and the caller resolves it from whatever bounds it (a gadget, a precondition,
a callee's postcondition).

`exec` is structural recursion over the code, tries keyed by `ℕ` and no field arithmetic, written
for the kernel, which evaluates it once per function (`decide +kernel`): the hot functions use
the recursors directly (hence `noncomputable`), and the walk passes its state evaluated (`seq`),
the kernel sharing no evaluation between the copies of a term.

**Soundness** (`exec_sound`): a halting run entering a segment, in a frame its environment holds
of, satisfies the atoms of the path it takes and leaves by that path's exit with fewer steps left
(`RunK`, `Exit.Reached`); a path with no branch gives all its atoms at once (`RunK.straight`).
**Completeness** (`exec_complete`): atoms holding along a path make the run reach the exit's
registers (`Follows`, `Reach`). **Linking** (`Result.linked_spec`): an exit's successors start
segments whose environments hold where the exit's does.

The definitions are here, apart from their semantics and proofs (`Exec.lean`, which imports the
guest program and the program logic), so that the kernel-checked certificates, which evaluate
`exec`, do not import those.
-/

namespace LeanVM.Guest.Exec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

@[expose] public section

-- The statement derives no `Repr`; the guest's derived ones need these.
deriving instance Repr for LeanVM.Semantics.DerefMode, LeanVM.Semantics.KeccakOutputCells,
  LeanVM.Guest.OffsetInstruction

/-! ## Evaluation order

The kernel evaluates by substitution and does not share the evaluation of a term between its
copies, so a value that a walk inspects at every step is passed on evaluated: each `seq`
evaluates its argument to a constructor and hands that on, and the functions that build the
walk's state build it evaluated. Each `seq` is the identity (`seq_eq`). -/

section

variable {α β : Type}

/-- `k n`, `n` evaluated first. -/
def natSeq (n : ℕ) (k : ℕ → β) : β :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

/-- `k o`, `o` evaluated first. -/
def optSeq (o : Option α) (k : Option α → β) : β :=
  match o with
  | none => k none
  | some a => k (some a)

/-- `k l`, the spine of `l` evaluated first. -/
def listSeq : List α → (List α → β) → β
  | [], k => k []
  | a :: as, k => listSeq as fun as ↦ k (a :: as)

theorem natSeq_eq (n : ℕ) (k : ℕ → β) : natSeq n k = k n := by cases n <;> rfl

theorem optSeq_eq (o : Option α) (k : Option α → β) : optSeq o k = k o := by cases o <;> rfl

theorem listSeq_eq (l : List α) (k : List α → β) : listSeq l k = k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a as ih => exact ih _

end

/-! ## Tries keyed by `ℕ` -/

/-- A map from `ℕ`: key `0` at the root, `2m+1` at key `m` of the left child, `2m+2` at key `m`
of the right one. -/
inductive Trie (α : Type) where
  | nil
  | node (v : Option α) (l r : Trie α)

namespace Trie

variable {α β : Type}

/-- `k t`, `t` evaluated first. -/
def seq (t : Trie α) (k : Trie α → β) : β :=
  match t with
  | nil => k nil
  | node v l r => k (node v l r)

theorem seq_eq (t : Trie α) (k : Trie α → β) : t.seq k = k t := by cases t <;> rfl

/-- The root value. -/
def val : Trie α → Option α
  | nil => none
  | node v _ _ => v

/-- The left child. -/
def left : Trie α → Trie α
  | nil => nil
  | node _ l _ => l

/-- The right child. -/
def right : Trie α → Trie α
  | nil => nil
  | node _ _ r => r

/-! Written with the recursors, which the kernel reduces much faster than the compiled form of
structural recursion; hence `noncomputable`: these are evaluated by the kernel only. -/

/-- The value at key `n`. -/
noncomputable def get (t : Trie α) : ℕ → Option α :=
  Trie.rec (motive := fun _ ↦ ℕ → Option α) (fun _ ↦ none)
    (fun v _ _ gl gr n ↦ bif n == 0 then v else bif n % 2 == 1 then gl (n / 2) else gr (n / 2 - 1)) t

/-- Store `a` at key `n`, within `d` levels (a deeper key is dropped). -/
noncomputable def set (a : α) (d : ℕ) : Trie α → ℕ → Trie α :=
  Nat.rec (motive := fun _ ↦ Trie α → ℕ → Trie α) (fun t _ ↦ t)
    (fun _ s t n ↦ Trie.casesOn (motive := fun _ ↦ Trie α) t
      (bif n == 0 then node (some a) nil nil
        else bif n % 2 == 1 then (s nil (n / 2)).seq fun l ↦ node none l nil
        else (s nil (n / 2 - 1)).seq fun r ↦ node none nil r)
      (fun v l r ↦ bif n == 0 then node (some a) l r
        else bif n % 2 == 1 then (s l (n / 2)).seq fun l ↦ node v l r
        else (s r (n / 2 - 1)).seq fun r ↦ node v l r)) d

/-- The value two roots agree on. -/
def meet (eq : α → α → Bool) : Option α → Option α → Option α
  | some x, some y => bif eq x y then some x else none
  | _, _ => none

/-- The entries on which two tries agree, `eq` deciding equality of values. -/
noncomputable def inter (eq : α → α → Bool) (a : Trie α) : Trie α → Trie α :=
  Trie.rec (motive := fun _ ↦ Trie α → Trie α) (fun _ ↦ nil)
    (fun v _ _ il ir b ↦ Trie.casesOn (motive := fun _ ↦ Trie α) b nil
      (fun v' l' r' ↦ (il l').seq fun l ↦ (ir r').seq fun r ↦
        optSeq (meet eq v v') fun v ↦ node v l r)) a

/-- Every entry of the first trie is one of the second, `eq` deciding equality of values. -/
noncomputable def sub (eq : α → α → Bool) (a : Trie α) : Trie α → Bool :=
  Trie.rec (motive := fun _ ↦ Trie α → Bool) (fun _ ↦ true)
    (fun v _ _ sl sr b ↦
      (match v, b.val with
        | none, _ => true
        | some x, some y => eq x y
        | some _, none => false) && sl b.left && sr b.right) a

end Trie

/-- The levels of an environment: frame offsets below `2^13`. -/
def envDepth : ℕ := 14

/-- The levels of a segment index: offsets below `2^19`. -/
def indexDepth : ℕ := 20

/-! ## Symbolic values -/

/-- A frame cell's known word. -/
inductive Sym where
  /-- `0`. -/
  | zero
  /-- `g^e`. -/
  | gp (e : ℕ)
  /-- `fp · g^e`. -/
  | fpg (e : ℕ)
  deriving DecidableEq, Repr

/-- Equality of symbolic values, as a `Bool`. -/
def Sym.beq : Sym → Sym → Bool
  | .zero, .zero => true
  | .gp e, .gp e' => e == e'
  | .fpg e, .fpg e' => e == e'
  | _, _ => false

/-- The word a symbolic value denotes at frame `fp`. -/
def Sym.val (fp : K) : Sym → E
  | .zero => 0
  | .gp e => ofK (addressOfIndex e)
  | .fpg e => ofK (fp * addressOfIndex e)

/-- The exponent of a known power of `g`. -/
def Sym.expo : Option Sym → Option ℕ
  | some (.gp e) => some e
  | _ => none

/-- A register value: `g^e`, `fp · g^e`, or limb `0` of a frame cell. -/
inductive Tgt where
  | gp (e : ℕ)
  | fpg (e : ℕ)
  | cell (o : ℕ)
  deriving DecidableEq, Repr

/-- `k t`, `t` evaluated first. -/
def Tgt.seq {β : Type} (t : Tgt) (k : Tgt → β) : β :=
  match t with
  | .gp e => k (.gp e)
  | .fpg e => k (.fpg e)
  | .cell o => k (.cell o)

theorem Tgt.seq_eq {β : Type} (t : Tgt) (k : Tgt → β) : t.seq k = k t := by cases t <;> rfl

/-- Cell `o` as a register, from what is known of it. -/
def tgtOf (s : Option Sym) (o : ℕ) : Tgt :=
  match s with
  | some (.fpg e) => .fpg e
  | some (.gp e) => .gp e
  | _ => .cell o

/-! ## Facts from outside -/

/-- Pairs `(k, e)`, `K.ofBits k = g^e`, as a search tree by `k`. -/
inductive PowTree where
  | leaf
  | node (k e : ℕ) (l r : PowTree)

/-- The exponent the tree gives the bits `k`. -/
noncomputable def PowTree.find (t : PowTree) (k : ℕ) : Option ℕ :=
  PowTree.rec (motive := fun _ ↦ Option ℕ) none
    (fun k' e _ _ fl fr ↦ bif k == k' then some e else bif Nat.blt k k' then fl else fr) t

/-- Every pair of the tree is a power of `g` (decided by the kernel). -/
def PowTree.Ok : PowTree → Prop
  | .leaf => True
  | .node k e l r => K.ofBits k = addressOfIndex e ∧ l.Ok ∧ r.Ok

instance PowTree.decOk : (t : PowTree) → Decidable t.Ok
  | .leaf => isTrue trivial
  | .node k e l r =>
    haveI := PowTree.decOk l
    haveI := PowTree.decOk r
    inferInstanceAs (Decidable (K.ofBits k = addressOfIndex e ∧ l.Ok ∧ r.Ok))

/-- What the executor is told about a function. -/
structure Facts where
  /-- The environment at the entry. -/
  env : List (ℕ × Sym) := []
  /-- The frame is `1` (`main`). -/
  fpOne : Bool := false
  /-- The powers of `g` the constants name. -/
  pows : PowTree := .leaf
  /-- The arm offsets of the table dispatch at each offset. -/
  arms : List (ℕ × List ℕ) := []
  /-- More of them, by offset (a function of many table jumps: `main_loop2`'s chained `match`es,
  each arm's end one), looked up first. -/
  armsT : Trie (List ℕ) := .nil
  /-- The cells whose products by a power of `g` are tracked (a loop's self frame pointer). -/
  scaled : List ℕ := []

/-- What a `SET` immediate is known as. -/
noncomputable def Facts.symOf (F : Facts) (k0 k1 : ℕ) : Option Sym :=
  bif k1 == 0 then
    (bif k0 == 0 then some .zero else bif k0 == 1 then some (.gp 0) else (F.pows.find k0).map .gp)
  else none

/-- A register that is the frame pointer. -/
def Facts.self (F : Facts) : Tgt → Bool
  | .fpg 0 => true
  | .gp 0 => F.fpOne
  | _ => false

/-- A known word that is `1`. -/
def isOne : Option Sym → Bool
  | some (.gp 0) => true
  | _ => false

/-- A known word that is not `0`. -/
def isNonzero : Option Sym → Bool
  | some (.gp _) => true
  | _ => false

/-- A known word that is `0`. -/
def isZero : Option Sym → Bool
  | some .zero => true
  | _ => false

/-! ## Atoms, items, exits, segments -/

/-- A relation on the memory, over the cells of a frame. -/
inductive Atom where
  /-- A non-`JUMP` instruction at pc `g^pc` holds (`Holds`): `fp[c] = fp[a] + fp[b]`,
  `fp[c] = fp[a]·fp[b]`, `fp[o] = k`, `L[fp[o1]·g^o2] = fp[o3]` (or `g²·pc`, or `fp`),
  `KeccakCellsRelation` over the operand cells. -/
  | instr (pc : ℕ) (ins : OffsetInstruction)
  /-- The cells a `JUMP` reads are words of `K`. -/
  | jump (oc od of : ℕ)
  /-- `fp[dst] = fp[src]` (a copy, `MUL dst = src·1`). -/
  | copy (dst src : ℕ)
  /-- `fp[a] = fp[b]` (`assert ==`, `XOR z = a + b` with `fp[z] = 0`). -/
  | eq (a b : ℕ)
  /-- `fp[x] ≠ 0` (`MUL p = x·inv; SET p = 1`). -/
  | nz (x : ℕ)
  /-- `fp[a] ≠ fp[b]` (`assert !=`: `XOR x = a + b; MUL p = x·inv; SET p = 1`). -/
  | ne (a b : ℕ)
  /-- `fp[x] ∈ {0, 1}` (`MUL x = x·x`). -/
  | bool (x : ℕ)
  /-- `fp[x] = g^e`, `fp[y] = g^e'` with `e + e' + 1 = k`, so `e < k` (the range check
  `DEREF *(x); MUL K = x·y; DEREF *(y)` with `K = g^(k-1)` known). -/
  | range (x y k : ℕ)
  /-- `fp[x] = g^e`, `fp[y] = g^e'`, `fp[z] = g^(e+e')`, both addresses (the range check with a
  bound `fp[z]` computed at run time). -/
  | powPair (x y z : ℕ)
  deriving DecidableEq, Repr

/-- Where a jump leaves to. -/
inductive Kind where
  /-- Offset `t` of the function, same frame. -/
  | next (t : ℕ)
  /-- The caller's registers, `fp[0]`, `fp[1]`. -/
  | ret
  /-- A callee at `(pc, fp[q])`, whose frame holds the return registers `(g^r, fp)`. -/
  | call (pc : Tgt) (q r : ℕ)
  /-- The registers `(pc, fp)`: a tail call, a table dispatch, halting, or anything else. -/
  | jump (pc fp : Tgt)
  deriving DecidableEq, Repr

/-- An exit: where it leaves to, the environment there, and the offsets of the function it
continues at (its successors: a jump's target, a call's return point, a dispatch's arms). -/
structure Exit where
  kind : Kind
  env : Trie Sym
  succ : List ℕ

/-- A step of a path. -/
inductive Item where
  /-- An executed instruction (one step) and its atom. -/
  | ins (a : Atom)
  /-- What a gadget means (no step). -/
  | fact (a : Atom)
  /-- `JUMP fp[oc], fp[od], fp[of]` on an unknown condition (one step): it falls through when
  `fp[oc] = 0`, and leaves by `x` otherwise. -/
  | branch (oc od of : ℕ) (x : Exit)

/-- A segment: from offset `start`, with the environment `env` there, its items, and the exit at
their end. -/
structure Seg where
  start : ℕ
  env : Trie Sym
  items : List Item
  exit : Exit
  /-- Its exits: the final one and its branches'. -/
  exits : List Exit

/-- The exits of the branches among `its`. -/
def branchExits : List Item → List Exit
  | [] => []
  | .branch _ _ _ x :: its => x :: branchExits its
  | _ :: its => branchExits its

/-- The executor's result: the segments, and the number of instructions on no path. -/
structure Result where
  segs : List Seg
  dead : ℕ

/-! ## One instruction -/

/-- What is known along a path: the environment, recent stores through frame cells
`(q, off, v)` (`L[fp[q]·g^off] = v`), and the last instructions with their pcs. -/
structure St where
  env : Trie Sym
  mem : List (ℕ × ℕ × Sym)
  prev : List (ℕ × OffsetInstruction)

/-- The state at a segment's start. -/
def St.init (env : Trie Sym) : St := ⟨env, [], []⟩

/-- `k st`, `st` evaluated first. -/
def St.seq {β : Type} (st : St) (k : St → β) : β :=
  match st with
  | ⟨env, mem, prev⟩ => env.seq fun env ↦ k ⟨env, mem, prev⟩

theorem St.seq_eq {β : Type} (st : St) (k : St → β) : st.seq k = k st := by
  cases st
  simp only [St.seq, Trie.seq_eq]

/-- A known store through frame cell `q` at offset `off`. -/
def memFind : List (ℕ × ℕ × Sym) → ℕ → ℕ → Option Sym
  | [], _, _ => none
  | (q, off, v) :: m, q', off' => bif q == q' && off == off' then some v else memFind m q' off'

/-- Learn `fp[o] = v` unless `fp[o]` is known. -/
noncomputable def learn (env : Trie Sym) (o : ℕ) (v : Sym) : Trie Sym :=
  match env.get o with
  | some _ => env
  | none => env.set v envDepth o

/-- The state after a non-`JUMP` instruction at pc `pc`. -/
def St.push (st : St) (env : Trie Sym) (mem : List (ℕ × ℕ × Sym)) (pc : ℕ) (ins : OffsetInstruction)
    : St :=
  ⟨env, mem, (pc, ins) :: st.prev.take 1⟩

/-- How an instruction continues a path. -/
inductive Res where
  /-- On to the next offset. -/
  | go (its : List Item) (st : St)
  /-- Leaves the function's code by `x`. -/
  | stop (its : List Item) (x : Exit)

/-- The facts of a `MUL a b c`. -/
def mulFacts (a b c : ℕ) (va vb : Option Sym) : List Atom :=
  (if a = b ∧ b = c then [.bool c] else []) ++
  (if isOne vb then [.copy c a] else if isOne va then [.copy c b] else [])

/-- The environment after `MUL a b c`: `fp · g^e` times `g^e'`, for `a` among the cells `F.scaled`
(the self frame pointer cell of a loop, whose `MUL` computes the next frame). -/
noncomputable def mulEnv (F : Facts) (env : Trie Sym) (a b c : ℕ) : Trie Sym :=
  bif F.scaled.contains a then
  match env.get a with
  | some (.fpg e) =>
    match Sym.expo (env.get b) with
    | some e' => learn env c (.fpg (e + e'))
    | none => env
  | _ => env
  else env

/-- The range check ending at `DEREF *(fp[y]·g^0) = fp[t]`: `DEREF *(fp[x]·g^0)`,
`MUL fp[z] = fp[x]·fp[y]` just before it. -/
noncomputable def rangeFact (env : Trie Sym) (y : ℕ) : List (ℕ × OffsetInstruction) → List Atom
  | [(_, .mul x y' z), (_, .deref x' 0 _ .cell)] =>
    if y' = y ∧ x' = x then
      match Sym.expo (env.get z) with
      | some k => if k < 2 ^ 63 then [.range x y (k + 1)] else [.powPair x y z]
      | none => [.powPair x y z]
    else []
  | _ => []

/-- The `!=` gadget ending at `SET fp[p] = 1`: `MUL fp[p] = fp[x]·fp[inv]` just before it, and
`XOR fp[x] = fp[a] + fp[b]` before that for `fp[a] ≠ fp[b]`. -/
def neFacts (p : ℕ) : List (ℕ × OffsetInstruction) → List Atom
  | (_, .mul x _ p') :: rest =>
    if p' = p then
      .nz x :: (match rest with
        | [(_, .xor a b x')] => if x' = x then [.ne a b] else []
        | _ => [])
    else []
  | _ => []

/-- The store a `DEREF` makes known (kept for the last four), and what a read through a known
store teaches. -/
noncomputable def derefMem (pc : ℕ) (st : St) (o1 o2 o3 : ℕ) :
    DerefMode → Trie Sym × List (ℕ × ℕ × Sym)
  | .fp => (st.env, ((o1, o2, .fpg 0) :: st.mem).take 4)
  | .pc => (st.env, ((o1, o2, .gp (pc + 2)) :: st.mem).take 4)
  | .cell => match memFind st.mem o1 o2 with
    | some v => (learn st.env o3 v, st.mem)
    | none =>
      bif o2 == 0 then
        (match st.env.get o3 with
          | some v => (st.env, ((o1, o2, v) :: st.mem).take 4)
          | none => (st.env, st.mem))
      else (st.env, st.mem)

/-- What a non-`JUMP` instruction at pc `pc` teaches: its facts, and the environment and stores
after it. -/
noncomputable def nonJump (F : Facts) (pc : ℕ) (st : St) :
    OffsetInstruction → List Atom × Trie Sym × List (ℕ × ℕ × Sym)
  | .xor a b c => (if isZero (st.env.get c) then [.eq a b] else [], st.env, st.mem)
  | .mul a b c => (mulFacts a b c (st.env.get a) (st.env.get b), mulEnv F st.env a b c, st.mem)
  | .set o k0 k1 =>
    (if k0 = 1 ∧ k1 = 0 then neFacts o st.prev else [],
      (match F.symOf k0 k1 with
        | some v => st.env.set v envDepth o
        | none => st.env), st.mem)
  | .deref o1 o2 o3 mode =>
    (if o2 = 0 ∧ mode = .cell then rangeFact st.env o1 st.prev else [],
      derefMem pc st o1 o2 o3 mode)
  | .keccak .. => ([], st.env, st.mem)
  | .jump .. => ([], st.env, st.mem)

/-- Where `JUMP fp[oc], fp[od], fp[of]` at offset `i` leaves to, and its successors. -/
noncomputable def jumpKind (F : Facts) (entry len i : ℕ) (st : St) (od of : ℕ) : Kind × List ℕ :=
  if od = 0 ∧ of = 1 then (.ret, [])
  else
    (tgtOf (st.env.get od) od).seq fun pt ↦ (tgtOf (st.env.get of) of).seq fun ft ↦
    if F.self ft then
      match pt with
      | .gp e => if entry + i < e ∧ e < entry + len then (.next (e - entry), [e - entry])
        else (.jump pt ft, [])
      | .cell _ => (.jump pt ft, match F.armsT.get i with
        | some l => l
        | none => ((F.arms.find? (·.1 == i)).map (·.2)).getD [])
      | .fpg _ => (.jump pt ft, [])
    else
      match ft with
      | .cell q =>
        match Sym.expo (memFind st.mem q 0), memFind st.mem q 1 with
        | some r, some (.fpg 0) =>
          (.call pt q r, if entry + i < r ∧ r < entry + len then [r - entry] else [])
        | _, _ => (.jump pt ft, [])
      | _ => (.jump pt ft, [])

/-- The exit of a `JUMP`. -/
noncomputable def jumpExit (F : Facts) (entry len i : ℕ) (st : St) (od of : ℕ) : Exit :=
  match jumpKind F entry len i st od of with
  | (k, succ) => ⟨k, st.env, succ⟩

/-- **One instruction**, at offset `i` of a function at `entry` of `len` instructions. -/
noncomputable def stepI (F : Facts) (entry len i : ℕ) (st : St) (ins : OffsetInstruction) : Res :=
  match ins with
  | .jump oc od of =>
    optSeq (st.env.get oc) fun c ↦
      if isZero c then .go [.ins (.jump oc od of)] st
      else if isNonzero c then .stop [.ins (.jump oc od of)] (jumpExit F entry len i st od of)
      else .go [.branch oc od of (jumpExit F entry len i st od of)] st
  | ins =>
    match nonJump F (entry + i) st ins with
    | (fs, env, mem) =>
      .go (.ins (.instr (entry + i) ins) :: fs.map .fact) (st.push env mem (entry + i) ins)

/-! ## The pass -/

/-- The segment being walked: its start, entry environment, items so far (latest first), and
state. -/
structure Cur where
  start : ℕ
  env : Trie Sym
  acc : List Item
  /-- The exits of its branches so far. -/
  xs : List Exit
  st : St

/-- A segment starting at `i` with environment `env`. -/
def Cur.init (i : ℕ) (env : Trie Sym) : Cur := ⟨i, env, [], [], St.init env⟩

/-- The segment, closed by `its` and the exit `x`. -/
def Cur.close (c : Cur) (its : List Item) (x : Exit) : Seg :=
  ⟨c.start, c.env, (its.reverseAux c.acc).reverse, x, x :: (branchExits its).reverseAux c.xs⟩

/-- Pending edges into later offsets, by increasing target: the target and the intersection of
the environments of its edges so far. -/
abbrev Pend := List (ℕ × Trie Sym)

/-- `k p`, the head of `p` evaluated first (its producers build the rest evaluated). -/
def headSeq {α β : Type} (p : List α) (k : List α → β) : β :=
  match p with
  | [] => k []
  | a :: as => k (a :: as)

theorem headSeq_eq {α β : Type} (p : List α) (k : List α → β) : headSeq p k = k p := by
  cases p <;> rfl

/-- Add an edge into `t` with environment `e`. The result's spine is evaluated as it is built,
each cell once (`headSeq` on the rest, itself built so): a table jump adds an edge per arm. -/
noncomputable def addEdge (t : ℕ) (e : Trie Sym) : Pend → Pend
  | [] => [(t, e)]
  | (u, a) :: ps =>
    if t < u then (t, e) :: (u, a) :: ps
    else if t = u then (u, Trie.inter Sym.beq a e) :: ps
    else headSeq (addEdge t e ps) fun ps ↦ (u, a) :: ps

/-- Add edges into the targets `ts`, each with environment `e`, merged into `p` in one pass when
`ts` is increasing (a table jump's arms): those below each pending target go in front of it. -/
noncomputable def addEdges (e : Trie Sym) (ts : List ℕ) : Pend → Pend
  | [] => ts.map fun t ↦ (t, e)
  | (u, a) :: ps =>
    (ts.takeWhile fun t ↦ decide (t < u)).map (fun t ↦ (t, e)) ++
      match ts.dropWhile fun t ↦ decide (t < u) with
      | t :: ts' =>
        if t = u then headSeq (addEdges e ts' ps) fun ps ↦ (u, Trie.inter Sym.beq a e) :: ps
        else headSeq (addEdges e (t :: ts') ps) fun ps ↦ (u, a) :: ps
      | [] => (u, a) :: ps

/-- Add the edges of an exit: one by `addEdge`, a table jump's arms (increasing) merged at once
(`addEdges`; an exit into each arm of the next chained `match` adds as many edges). -/
noncomputable def addExit (x : Exit) (p : Pend) : Pend :=
  match x.succ with
  | [t] => addEdge t x.env p
  | ts => addEdges x.env ts p

/-- Add the edges of the branches among `its`. -/
noncomputable def addItems : List Item → Pend → Pend
  | [], p => p
  | .branch _ _ _ x :: its, p => addItems its (addExit x p)
  | _ :: its, p => addItems its p

/-- Offset `i` is a join: the live segment, if any, ends by falling into it, and a new segment
starts there with the intersection of the environments of its edges. -/
noncomputable def atJoin (i : ℕ) (cur : Option Cur) (pend : Pend) (out : List Seg) :
    Option Cur × Pend × List Seg :=
  match pend with
  | (t, a) :: ps =>
    if t = i then
      match cur with
      | some c =>
        (Trie.inter Sym.beq a c.st.env).seq fun e ↦
          if c.start < i then
            (some (Cur.init i e), ps, c.close [] ⟨.next i, c.st.env, [i]⟩ :: out)
          else (some (Cur.init i e), ps, out)
      | none => a.seq fun e ↦ (some (Cur.init i e), ps, out)
    else (cur, pend, out)
  | [] => (cur, pend, out)

/-- One offset of the walk, `w` walking the rest. -/
noncomputable def passStep (F : Facts) (entry len : ℕ) (ins : OffsetInstruction)
    (w : ℕ → Option Cur → Pend → List Seg → ℕ → Result)
    (i : ℕ) (cur : Option Cur) (pend : Pend) (out : List Seg) (dead : ℕ) : Result :=
  match atJoin i cur pend out with
  | (none, pend, out) => natSeq (i + 1) fun i ↦ natSeq (dead + 1) fun dead ↦ w i none pend out dead
  | (some c, pend, out) =>
    match stepI F entry len i c.st ins with
    | .go its st =>
      st.seq fun st ↦ headSeq (addItems its pend) fun pend ↦ natSeq (i + 1) fun i ↦
        w i (some ⟨c.start, c.env, its.reverseAux c.acc, (branchExits its).reverseAux c.xs, st⟩)
          pend out dead
    | .stop its x =>
      headSeq (addExit x (addItems its pend)) fun pend ↦ natSeq (i + 1) fun i ↦
        w i none pend (c.close its x :: out) dead

/-- The end of the walk. -/
def passEnd (len i : ℕ) (cur : Option Cur) (out : List Seg) (dead : ℕ) : Result :=
  match cur with
  | some c =>
    if c.start < i then ⟨c.close [] ⟨.next i, c.st.env, if i < len then [i] else []⟩ :: out, dead⟩
    else ⟨out, dead⟩
  | none => ⟨out, dead⟩

/-- The walk over the code from offset `i`. -/
noncomputable def pass (F : Facts) (entry len : ℕ) (code : List OffsetInstruction) :
    ℕ → Option Cur → Pend → List Seg → ℕ → Result :=
  List.rec (motive := fun _ ↦ ℕ → Option Cur → Pend → List Seg → ℕ → Result)
    (fun i cur _ out dead ↦ passEnd len i cur out dead)
    (fun ins _ w ↦ passStep F entry len ins w) code

/-- The entry environment. -/
noncomputable def envOf (env : List (ℕ × Sym)) : Trie Sym :=
  env.foldl (fun t p ↦ t.set p.2 envDepth p.1) .nil

/-- The entry environment. -/
noncomputable def Facts.entryEnv (F : Facts) : Trie Sym := envOf F.env

/-- **The symbolic executor**: the segments of `f`'s code. -/
noncomputable def exec (F : Facts) (f : CompiledFunction) : Result :=
  pass F f.entryPc f.instructionCount f.code 0 (some (Cur.init 0 F.entryEnv)) [] [] 0

/-- **A window** of `f`'s code, offsets `a` to `b`, starting a segment at `a` with environment
`env`: the executor on a large function in pieces, each evaluated by the kernel on its own. The
segment live at `b` ends there with `b` its successor, to start the next window with. -/
noncomputable def execWin (F : Facts) (f : CompiledFunction) (a : ℕ) (env : List (ℕ × Sym))
    (b : ℕ) :
    Result :=
  pass F f.entryPc f.instructionCount ((f.code.drop a).take (b - a)) a (some (Cur.init a (envOf
      env))) [] [] 0

/-- **A window entered at several offsets**: `execWin` with pending edges into `seeds`, each in
the environment `env` (an entered window's arms past the first). -/
noncomputable def execWinS (F : Facts) (f : CompiledFunction) (a : ℕ) (env : List (ℕ × Sym))
    (seeds : List ℕ) (b : ℕ) : Result :=
  pass F f.entryPc f.instructionCount ((f.code.drop a).take (b - a)) a (some (Cur.init a (envOf
      env))) (seeds.map fun t ↦ (t, envOf env)) [] 0

theorem execWinS_nil (F : Facts) (f : CompiledFunction) (a : ℕ) (env : List (ℕ × Sym)) (b : ℕ) :
    execWinS F f a env [] b = execWin F f a env b := rfl

/-! ## Linking -/

/-- The segments by start. -/
noncomputable def index (segs : List Seg) : Trie Seg := segs.foldl (fun t s ↦ t.set s indexDepth s.start) .nil

/-- Every successor of every exit starts a segment whose entry environment the exit's holds. -/
noncomputable def linkedWith (idx : Trie Seg) (segs : List Seg) : Bool :=
  segs.all fun s ↦ s.exits.all fun x ↦ x.succ.all fun t ↦
    match idx.get t with
    | some s' => s'.start == t && s'.env.sub Sym.beq x.env
    | none => false

/-- `linkedWith`, a successor that starts no segment starting one of `ext`, the next windows'. -/
noncomputable def linkedExtWith (idx : Trie Seg) (ext : List (ℕ × Trie Sym)) (segs : List Seg) :
    Bool :=
  segs.all fun s ↦ s.exits.all fun x ↦ x.succ.all fun t ↦
    match idx.get t with
    | some s' => s'.start == t && s'.env.sub Sym.beq x.env
    | none => match ext.find? (·.1 == t) with
      | some e => e.2.sub Sym.beq x.env
      | none => false

/-- A window is linked, into itself or the windows starting at `ext` with their environments. -/
noncomputable def Result.linkedExt (ext : List (ℕ × List (ℕ × Sym))) (R : Result) : Bool :=
  match R with
  | ⟨segs, _⟩ => listSeq segs fun segs ↦ (index segs).seq fun idx ↦
      linkedExtWith idx (ext.map fun e ↦ (e.1, envOf e.2)) segs

/-- The segments are linked: every successor of an exit starts a segment whose entry environment
the exit's environment holds. -/
noncomputable def Result.linked (R : Result) : Bool :=
  match R with
  | ⟨segs, _⟩ => listSeq segs fun segs ↦ (index segs).seq fun idx ↦ linkedWith idx segs


/-! ## Tries: lemmas -/

namespace Trie

variable {α : Type}

theorem get_node (v : Option α) (l r : Trie α) (n : ℕ) :
    (node v l r).get n =
      if n = 0 then v else if n % 2 = 1 then l.get (n / 2) else r.get (n / 2 - 1) := by
  have : (node v l r).get n =
      (bif n == 0 then v else bif n % 2 == 1 then l.get (n / 2) else r.get (n / 2 - 1)) := rfl
  rw [this]
  simp only [Bool.cond_eq_ite, beq_iff_eq]

@[simp] theorem get_nil (n : ℕ) : (nil : Trie α).get n = none := rfl

/-- Every trie reads as a node. -/
theorem get_eq_node (t : Trie α) (n : ℕ) : t.get n = (node t.val t.left t.right).get n := by
  cases t with
  | nil => simp [get_node, val, left, right]
  | node v l r => rfl

theorem set_succ (a : α) (d : ℕ) (t : Trie α) (n : ℕ) :
    t.set a (d + 1) n =
      if n = 0 then node (some a) t.left t.right
      else if n % 2 = 1 then node t.val (t.left.set a d (n / 2)) t.right
      else node t.val t.left (t.right.set a d (n / 2 - 1)) := by
  cases t with
  | nil =>
    have : (nil : Trie α).set a (d + 1) n =
        (bif n == 0 then node (some a) nil nil
          else bif n % 2 == 1 then (nil.set a d (n / 2)).seq fun l ↦ node none l nil
          else (nil.set a d (n / 2 - 1)).seq fun r ↦ node none nil r) := rfl
    rw [this]
    simp only [Bool.cond_eq_ite, beq_iff_eq, seq_eq]
    rfl
  | node v l r =>
    have : (node v l r).set a (d + 1) n =
        (bif n == 0 then node (some a) l r
          else bif n % 2 == 1 then (l.set a d (n / 2)).seq fun l ↦ node v l r
          else (r.set a d (n / 2 - 1)).seq fun r ↦ node v l r) := rfl
    rw [this]
    simp only [Bool.cond_eq_ite, beq_iff_eq, seq_eq]
    rfl

/-- A read after a store reads the stored value or what was there. -/
theorem get_set {a b : α} : ∀ {d : ℕ} {t : Trie α} {n m : ℕ},
    (t.set a d n).get m = some b → (m = n ∧ b = a) ∨ t.get m = some b
  | 0, _, _, _, h => Or.inr h
  | d + 1, t, n, m, h => by
    rw [set_succ] at h
    rw [get_eq_node t m, get_node]
    by_cases h0 : n = 0
    · rw [ite_eq_left h0, get_node] at h
      by_cases hm : m = 0
      · rw [ite_eq_left hm] at h
        exact Or.inl ⟨by omega, (Option.some.inj h).symm⟩
      · rw [ite_eq_right hm] at h ⊢
        exact Or.inr h
    · rw [ite_eq_right h0] at h
      by_cases h1 : n % 2 = 1
      · rw [ite_eq_left h1, get_node] at h
        by_cases hm : m = 0
        · rw [ite_eq_left hm] at h ⊢
          exact Or.inr h
        · rw [ite_eq_right hm] at h ⊢
          by_cases hm1 : m % 2 = 1
          · rw [ite_eq_left hm1] at h ⊢
            rcases get_set h with ⟨he, rfl⟩ | h'
            · exact Or.inl ⟨by omega, rfl⟩
            · exact Or.inr h'
          · rw [ite_eq_right hm1] at h ⊢
            exact Or.inr h
      · rw [ite_eq_right h1, get_node] at h
        by_cases hm : m = 0
        · rw [ite_eq_left hm] at h ⊢
          exact Or.inr h
        · rw [ite_eq_right hm] at h ⊢
          by_cases hm1 : m % 2 = 1
          · rw [ite_eq_left hm1] at h ⊢
            exact Or.inr h
          · rw [ite_eq_right hm1] at h ⊢
            rcases get_set h with ⟨he, rfl⟩ | h'
            · exact Or.inl ⟨by omega, rfl⟩
            · exact Or.inr h'

theorem inter_nil (eq : α → α → Bool) (b : Trie α) : inter eq nil b = nil := rfl

theorem inter_node_nil (eq : α → α → Bool) (v : Option α) (l r : Trie α) :
    inter eq (node v l r) nil = nil := rfl

theorem inter_node_node (eq : α → α → Bool) (v v' : Option α) (l r l' r' : Trie α) :
    inter eq (node v l r) (node v' l' r') =
      node (meet eq v v') (inter eq l l') (inter eq r r') := by
  have : inter eq (node v l r) (node v' l' r') =
      ((inter eq l l').seq fun l ↦ (inter eq r r').seq fun r ↦
        optSeq (meet eq v v') fun v ↦ node v l r) := rfl
  rw [this]
  simp only [seq_eq, optSeq_eq]

/-- What the intersection holds, both hold. -/
theorem get_inter {eq : α → α → Bool} (heq : ∀ x y, eq x y = true → x = y) :
    ∀ {a b : Trie α} {n : ℕ} {x : α}, (inter eq a b).get n = some x →
      a.get n = some x ∧ b.get n = some x
  | nil, _, _, _, h => by simp [inter_nil] at h
  | node _ _ _, nil, _, _, h => by simp [inter_node_nil] at h
  | node v l r, node v' l' r', n, x, h => by
    rw [inter_node_node, get_node] at h
    rw [get_node, get_node]
    split_ifs at h ⊢ with h0 h1
    · rcases v with _ | v <;> rcases v' with _ | v' <;> simp only [meet, reduceCtorEq] at h
      · simp only [Bool.cond_eq_ite] at h
        split_ifs at h with hv
        obtain rfl := Option.some.inj h
        exact ⟨rfl, by rw [heq _ _ hv]⟩
    · exact get_inter heq h
    · exact get_inter heq h

theorem sub_eq (eq : α → α → Bool) (v : Option α) (l r b : Trie α) :
    sub eq (node v l r) b =
      ((match v, b.val with
        | none, _ => true
        | some x, some y => eq x y
        | some _, none => false) && sub eq l b.left && sub eq r b.right) := rfl

/-- What the first holds, the second does. -/
theorem get_of_sub {eq : α → α → Bool} (heq : ∀ x y, eq x y = true → x = y) :
    ∀ {a b : Trie α} {n : ℕ} {x : α}, sub eq a b = true → a.get n = some x → b.get n = some x
  | nil, _, _, _, _, h => by simp at h
  | node v l r, b, n, x, hs, h => by
    rw [sub_eq] at hs
    simp only [Bool.and_eq_true] at hs
    obtain ⟨⟨hv, hl⟩, hr⟩ := hs
    rw [get_node] at h
    rw [get_eq_node, get_node]
    split_ifs at h ⊢ with h0 h1
    · subst h
      revert hv
      rcases b.val with _ | y
      · simp
      · intro hv
        exact congrArg some (heq _ _ hv).symm
    · exact get_of_sub heq hl h
    · exact get_of_sub heq hr h

end Trie

theorem Sym.beq_eq {a b : Sym} (h : Sym.beq a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [Sym.beq]

end
end LeanVM.Guest.Exec
