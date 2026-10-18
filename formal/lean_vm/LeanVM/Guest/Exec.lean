/-
  LeanVM.Guest.Exec

  The symbolic executor of compiled functions: one pass over a function's code that cuts it into
  segments at the joins of its forward control flow, and turns each into atoms, one per executed
  instruction, along its forward paths, with the exits it leaves by.
-/

module

public import LeanVM.Guest.Bytecode
public import LeanVM.Guest.Logic

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
-/

namespace LeanVM.Guest.Exec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

@[expose] public section

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
  | .gp e => ofK (gpow e)
  | .fpg e => ofK (fp * gpow e)

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
  | .node k e l r => K.ofBits k = gpow e ∧ l.Ok ∧ r.Ok

instance PowTree.decOk : (t : PowTree) → Decidable t.Ok
  | .leaf => isTrue trivial
  | .node k e l r =>
    haveI := PowTree.decOk l
    haveI := PowTree.decOk r
    inferInstanceAs (Decidable (K.ofBits k = gpow e ∧ l.Ok ∧ r.Ok))

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
  /-- The cells whose products by a power of `g` are tracked (a loop's self frame pointer). -/
  scaled : List ℕ := []

/-- What a `SET` immediate is known as. -/
noncomputable def Facts.symOf (F : Facts) (k0 k1 k2 : ℕ) : Option Sym :=
  bif k1 == 0 && k2 == 0 then
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
  `CompressCells` over the operand cells. -/
  | instr (pc : ℕ) (ins : OInstr)
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
  prev : List (ℕ × OInstr)

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
def St.push (st : St) (env : Trie Sym) (mem : List (ℕ × ℕ × Sym)) (pc : ℕ) (ins : OInstr) : St :=
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
noncomputable def rangeFact (env : Trie Sym) (y : ℕ) : List (ℕ × OInstr) → List Atom
  | [(_, .mul x y' z), (_, .deref x' 0 _ .cell)] =>
    if y' = y ∧ x' = x then
      match Sym.expo (env.get z) with
      | some k => if k < 2 ^ 63 then [.range x y (k + 1)] else [.powPair x y z]
      | none => [.powPair x y z]
    else []
  | _ => []

/-- The `!=` gadget ending at `SET fp[p] = 1`: `MUL fp[p] = fp[x]·fp[inv]` just before it, and
`XOR fp[x] = fp[a] + fp[b]` before that for `fp[a] ≠ fp[b]`. -/
def neFacts (p : ℕ) : List (ℕ × OInstr) → List Atom
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
    OInstr → List Atom × Trie Sym × List (ℕ × ℕ × Sym)
  | .xor a b c => (if isZero (st.env.get c) then [.eq a b] else [], st.env, st.mem)
  | .mul a b c => (mulFacts a b c (st.env.get a) (st.env.get b), mulEnv F st.env a b c, st.mem)
  | .set o k0 k1 k2 =>
    (if k0 = 1 ∧ k1 = 0 ∧ k2 = 0 then neFacts o st.prev else [],
      (match F.symOf k0 k1 k2 with
        | some v => st.env.set v envDepth o
        | none => st.env), st.mem)
  | .deref o1 o2 o3 mode =>
    (if o2 = 0 ∧ mode = .cell then rangeFact st.env o1 st.prev else [],
      derefMem pc st o1 o2 o3 mode)
  | .blake2s .. => ([], st.env, st.mem)
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
      | .cell _ => (.jump pt ft, ((F.arms.find? (·.1 == i)).map (·.2)).getD [])
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
noncomputable def stepI (F : Facts) (entry len i : ℕ) (st : St) (ins : OInstr) : Res :=
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

/-- Add an edge into `t` with environment `e`. -/
noncomputable def addEdge (t : ℕ) (e : Trie Sym) : Pend → Pend
  | [] => [(t, e)]
  | (u, a) :: ps =>
    if t < u then (t, e) :: (u, a) :: ps
    else if t = u then (u, Trie.inter Sym.beq a e) :: ps
    else listSeq (addEdge t e ps) fun ps ↦ (u, a) :: ps

/-- Add the edges of an exit. -/
noncomputable def addExit (x : Exit) (p : Pend) : Pend := x.succ.foldl (fun p t ↦ addEdge t x.env p) p

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

/-- `k p`, the head of `p` evaluated first (its producers build the rest evaluated). -/
def headSeq {α β : Type} (p : List α) (k : List α → β) : β :=
  match p with
  | [] => k []
  | a :: as => k (a :: as)

theorem headSeq_eq {α β : Type} (p : List α) (k : List α → β) : headSeq p k = k p := by
  cases p <;> rfl

/-- One offset of the walk, `w` walking the rest. -/
noncomputable def passStep (F : Facts) (entry len : ℕ) (ins : OInstr)
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
noncomputable def pass (F : Facts) (entry len : ℕ) (code : List OInstr) :
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
noncomputable def exec (F : Facts) (f : CompiledFn) : Result :=
  pass F f.entry f.len f.code 0 (some (Cur.init 0 F.entryEnv)) [] [] 0

/-- **A window** of `f`'s code, offsets `a` to `b`, starting a segment at `a` with environment
`env`: the executor on a large function in pieces, each evaluated by the kernel on its own. The
segment live at `b` ends there with `b` its successor, to start the next window with. -/
noncomputable def execWin (F : Facts) (f : CompiledFn) (a : ℕ) (env : List (ℕ × Sym)) (b : ℕ) :
    Result :=
  pass F f.entry f.len ((f.code.drop a).take (b - a)) a (some (Cur.init a (envOf env))) [] [] 0

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


/-! ## Semantics -/

section Semantics

variable {κ : ℕ} (L : MemImage κ) (fp : K)

/-- The environment holds of the frame: every known cell holds its value. -/
def EnvHolds (env : Trie Sym) : Prop :=
  ∀ n v, env.get n = some v → L.read (fp * gpow n) = some (v.val fp)

/-- The stores hold: `L[fp[q]·g^off] = v`, `fp[q]` a word of `K`. -/
def MemHolds (mem : List (ℕ × ℕ × Sym)) : Prop :=
  ∀ q off v, (q, off, v) ∈ mem → ∃ p, L.read (fp * gpow q) = some p ∧ IsInK p ∧
    L.read (p.limb 0 * gpow off) = some (v.val fp)

/-- What is known along a path holds. -/
def St.Holds (st : St) : Prop :=
  EnvHolds L fp st.env ∧ MemHolds L fp st.mem ∧ ∀ x ∈ st.prev, Guest.Holds L x.1 fp x.2

/-- `a` is the register value `t` names. -/
def Tgt.Is (a : K) : Tgt → Prop
  | .gp e => a = gpow e
  | .fpg e => a = fp * gpow e
  | .cell o => ∃ v, L.read (fp * gpow o) = some v ∧ IsInK v ∧ a = v.limb 0

/-- **What an atom means**, of the memory and the frame. -/
def Atom.Holds : Atom → Prop
  | .instr pc ins => Guest.Holds L pc fp ins
  | .jump oc od of => ∃ c d f, L.read (fp * gpow oc) = some c ∧ L.read (fp * gpow od) = some d ∧
      L.read (fp * gpow of) = some f ∧ IsInK c ∧ IsInK d ∧ IsInK f
  | .copy dst src => ∃ v, L.read (fp * gpow src) = some v ∧ L.read (fp * gpow dst) = some v
  | .eq a b => ∃ v, L.read (fp * gpow a) = some v ∧ L.read (fp * gpow b) = some v
  | .nz x => ∃ v, L.read (fp * gpow x) = some v ∧ v ≠ 0
  | .ne a b => ∃ u v, L.read (fp * gpow a) = some u ∧ L.read (fp * gpow b) = some v ∧ u ≠ v
  | .bool x => ∃ v, L.read (fp * gpow x) = some v ∧ (v = 0 ∨ v = 1)
  | .range x y k => ∃ e e', e + e' + 1 = k ∧ L.read (fp * gpow x) = some (ofK (gpow e)) ∧
      L.read (fp * gpow y) = some (ofK (gpow e'))
  | .powPair x y z => ∃ e e', e < 2 ^ κ ∧ e' < 2 ^ κ ∧
      L.read (fp * gpow x) = some (ofK (gpow e)) ∧ L.read (fp * gpow y) = some (ofK (gpow e')) ∧
      L.read (fp * gpow z) = some (ofK (gpow (e + e')))

/-- The registers `r` an exit of a function at `entry` leaves to. -/
def Kind.Regs (entry : ℕ) (r : Semantics.Regs K) : Kind → Prop
  | .next t => r = ⟨gpow (entry + t), fp⟩
  | .ret => retRegs L fp = some r
  | .call pc q _ => ∃ p a, L.read (fp * gpow q) = some p ∧ IsInK p ∧ pc.Is L fp a ∧
      r = ⟨a, p.limb 0⟩
  | .jump pc f => ∃ a b, pc.Is L fp a ∧ f.Is L fp b ∧ r = ⟨a, b⟩

/-- What else holds at an exit: a callee's frame holds the return registers. -/
def Kind.Extra : Kind → Prop
  | .call _ q r => ∃ p, L.read (fp * gpow q) = some p ∧ retRegs L (p.limb 0) = some ⟨gpow r, fp⟩
  | _ => True

/-- **Completeness along a path**: the atoms of `its` hold until the path leaves by a branch
whose exit goes to `r`, or reaches its end with `Q`. -/
def Follows (entry : ℕ) (r : Regs K) (Q : Prop) : List Item → Prop
  | [] => Q
  | .ins a :: its => a.Holds L fp ∧ Follows entry r Q its
  | .fact _ :: its => Follows entry r Q its
  | .branch oc od of x :: its => (Atom.jump oc od of).Holds L fp ∧
      ((L.read (fp * gpow oc) = some 0 ∧ Follows entry r Q its) ∨
        ((∃ v, L.read (fp * gpow oc) = some v ∧ v ≠ 0) ∧ x.kind.Regs L fp entry r))

variable (prog : Program)

/-- An exit is reached with `k` steps left, fewer than the `k₀` the path started with: its
environment and extra facts hold, and the run goes on from its registers. -/
def Exit.Reached (entry k₀ : ℕ) (x : Exit) (k : ℕ) : Prop :=
  k < k₀ ∧ EnvHolds L fp x.env ∧ x.kind.Extra L fp ∧
    ∃ r, x.kind.Regs L fp entry r ∧ Safe prog L k r

/-- **Soundness along a path**: from `k` steps left, every atom of `its` holds on the path the run
takes, each executed instruction a step, and the run leaves by a branch's exit, or reaches the
end with `Q` of the steps left. -/
def RunK (entry k₀ : ℕ) (Q : ℕ → Prop) : List Item → ℕ → Prop
  | [], k => Q k
  | .ins a :: its, k => a.Holds L fp ∧ ∃ k', k = k' + 1 ∧ RunK entry k₀ Q its k'
  | .fact a :: its, k => a.Holds L fp ∧ RunK entry k₀ Q its k
  | .branch oc od of x :: its, k => (Atom.jump oc od of).Holds L fp ∧ ∃ k', k = k' + 1 ∧
      ((L.read (fp * gpow oc) = some 0 ∧ RunK entry k₀ Q its k') ∨
        ((∃ v, L.read (fp * gpow oc) = some v ∧ v ≠ 0) ∧ x.Reached L fp prog entry k₀ k'))

end Semantics

/-- What the soundness of the executor assumes of a frame: the powers are powers, the frame of
`main` is `1`, and the memory has at most `2^32` words. -/
structure Ctx (F : Facts) (κ : ℕ) (fp : K) : Prop where
  pows : F.pows.Ok
  fpOne : F.fpOne = true → fp = 1
  le : κ ≤ 32

/-- The code from pc `pc` is fetched there, before the last slot. -/
def Fetches (prog : Program) (pc : ℕ) (code : List OInstr) : Prop :=
  ∀ j ins, code[j]? = some ins →
    prog.fetch (gpow (pc + j)) = some ins.toInstr ∧ pc + j < 2 ^ prog.logSize - 1

/-! ## Lemmas on values -/

section Values

theorem PowTree.find_ok {t : PowTree} (ht : t.Ok) {k e : ℕ} (h : t.find k = some e) :
    K.ofBits k = gpow e := by
  induction t with
  | leaf => exact absurd h (by simp [PowTree.find])
  | node k' e' l r ihl ihr =>
    have hf : (PowTree.node k' e' l r).find k =
        (bif k == k' then some e' else bif Nat.blt k k' then l.find k else r.find k) := rfl
    rw [hf] at h
    simp only [Bool.cond_eq_ite, beq_iff_eq] at h
    split_ifs at h with h1 h2
    · subst h1
      obtain rfl := Option.some.inj h
      exact ht.1
    · exact ihl ht.2.1 h
    · exact ihr ht.2.2 h

theorem ofK_zero : ofK 0 = 0 := map_zero (algebraMap K E)

theorem ofK_one : ofK 1 = 1 := map_one (algebraMap K E)

theorem imm_zero : OInstr.imm 0 0 0 = 0 := by
  rw [OInstr.imm]
  exact (ofLimbs_eq_zero_iff _).mpr rfl

theorem imm_of_ofBits {k : ℕ} {a : K} (h : K.ofBits k = a) : OInstr.imm k 0 0 = ofK a := by
  rw [OInstr.imm, h, ofK_eq_ofLimbs]
  rfl

theorem gpow_zero' : gpow 0 = 1 := pow_zero g

theorem symOf_val {F : Facts} (hp : F.pows.Ok) {k0 k1 k2 : ℕ} {v : Sym}
    (h : F.symOf k0 k1 k2 = some v) (fp : K) : OInstr.imm k0 k1 k2 = v.val fp := by
  simp only [Facts.symOf, Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq] at h
  split_ifs at h with h12 h0 h1
  · obtain ⟨rfl, rfl⟩ := h12
    subst h0
    obtain rfl := Option.some.inj h
    exact imm_zero
  · obtain ⟨rfl, rfl⟩ := h12
    subst h1
    obtain rfl := Option.some.inj h
    rw [Sym.val, gpow_zero']
    exact imm_of_ofBits rfl
  · obtain ⟨rfl, rfl⟩ := h12
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact imm_of_ofBits (PowTree.find_ok hp he)

theorem expo_val {s : Option Sym} {e : ℕ} (h : Sym.expo s = some e) (fp : K) :
    ∃ v, s = some v ∧ v.val fp = ofK (gpow e) := by
  rcases s with _ | (_ | e' | _) <;> simp [Sym.expo] at h
  exact ⟨_, rfl, by rw [h]; rfl⟩

theorem isOne_val {s : Option Sym} (h : isOne s = true) (fp : K) :
    ∃ v, s = some v ∧ v.val fp = 1 := by
  rcases s with _ | (_ | (_ | e) | _) <;> simp [isOne] at h
  exact ⟨_, rfl, by rw [Sym.val, gpow_zero', ofK_one]⟩

theorem isZero_eq {s : Option Sym} (h : isZero s = true) : s = some .zero := by
  rcases s with _ | (_ | _ | _) <;> simp_all [isZero]

theorem isNonzero_val {s : Option Sym} (h : isNonzero s = true) (fp : K) :
    ∃ v, s = some v ∧ v.val fp ≠ 0 := by
  rcases s with _ | (_ | e | _) <;> simp [isNonzero] at h
  refine ⟨_, rfl, fun h0 ↦ gpow_ne_zero e (ofK_injective ?_)⟩
  rw [ofK_zero]
  exact h0

theorem inK_eq {p : E} (h : IsInK p) : p = ofK (p.limb 0) := by
  rw [ofK_eq_ofLimbs, ofLimbs_of_isInK h]

theorem memFind_mem {m : List (ℕ × ℕ × Sym)} {q off : ℕ} {v : Sym} (h : memFind m q off = some v) :
    (q, off, v) ∈ m := by
  induction m with
  | nil => simp [memFind] at h
  | cons x m ih =>
    obtain ⟨q', off', v'⟩ := x
    simp only [memFind, Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq] at h
    split_ifs at h with hx
    · obtain ⟨rfl, rfl⟩ := hx
      obtain rfl := Option.some.inj h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- Characteristic two: equal sums are equal words. -/
theorem eq_of_add_eq_zero {a b : E} (h : a + b = 0) : a = b := by
  have := congrArg (· + b) h
  simpa [add_assoc, CharTwo.add_self_eq_zero] using this

end Values

section Env

variable {κ : ℕ} {L : MemImage κ} {fp : K}

theorem EnvHolds.set {env : Trie Sym} (h : EnvHolds L fp env) {o : ℕ} {v : Sym} {d : ℕ}
    (hv : L.read (fp * gpow o) = some (v.val fp)) : EnvHolds L fp (env.set v d o) := by
  intro n w hw
  rcases Trie.get_set hw with ⟨rfl, rfl⟩ | hw
  · exact hv
  · exact h n w hw

theorem EnvHolds.learn {env : Trie Sym} (h : EnvHolds L fp env) {o : ℕ} {v : Sym}
    (hv : L.read (fp * gpow o) = some (v.val fp)) : EnvHolds L fp (Exec.learn env o v) := by
  unfold Exec.learn
  split
  · exact h
  · exact h.set hv

theorem EnvHolds.nil : EnvHolds L fp .nil := fun _ _ h ↦ by simp at h

theorem EnvHolds.sub {a b : Trie Sym} (hs : a.sub Sym.beq b = true) (h : EnvHolds L fp b) :
    EnvHolds L fp a :=
  fun n v hv ↦ h n v (Trie.get_of_sub (fun _ _ ↦ Sym.beq_eq) hs hv)

theorem MemHolds.cons {m : List (ℕ × ℕ × Sym)} (h : MemHolds L fp m) {q off : ℕ} {v : Sym}
    (hv : ∃ p, L.read (fp * gpow q) = some p ∧ IsInK p ∧
      L.read (p.limb 0 * gpow off) = some (v.val fp)) : MemHolds L fp ((q, off, v) :: m) := by
  intro q' off' v' hm
  rcases List.mem_cons.mp hm with he | hm
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact hv
  · exact h q' off' v' hm

theorem MemHolds.take {m : List (ℕ × ℕ × Sym)} (h : MemHolds L fp m) (n : ℕ) :
    MemHolds L fp (m.take n) :=
  fun q off v hm ↦ h q off v (List.mem_of_mem_take hm)

theorem tgtOf_is {env : Trie Sym} (he : EnvHolds L fp env) {o : ℕ} {d : E}
    (hd : L.read (fp * gpow o) = some d) (hdK : IsInK d) :
    (tgtOf (env.get o) o).Is L fp (d.limb 0) := by
  unfold tgtOf
  split
  · rename_i e h
    have := (he o _ h).symm.trans hd
    obtain rfl := Option.some.inj this
    simp [Tgt.Is, Sym.val]
  · rename_i e h
    have := (he o _ h).symm.trans hd
    obtain rfl := Option.some.inj this
    simp [Tgt.Is, Sym.val]
  · exact ⟨d, hd, hdK, rfl⟩

theorem Tgt.is_unique {t : Tgt} {a b : K} (ha : t.Is L fp a) (hb : t.Is L fp b) : a = b := by
  cases t with
  | gp e => exact ha.trans hb.symm
  | fpg e => exact ha.trans hb.symm
  | cell o =>
    obtain ⟨v, hv, -, rfl⟩ := ha
    obtain ⟨w, hw, -, rfl⟩ := hb
    rw [Option.some.inj (hv.symm.trans hw)]

theorem self_is {F : Facts} (hfp : F.fpOne = true → fp = 1) {t : Tgt} (hs : F.self t = true)
    {a : K} (ha : t.Is L fp a) : a = fp := by
  unfold Facts.self at hs
  split at hs
  · simpa [Tgt.Is, gpow_zero'] using ha
  · simp only [Tgt.Is] at ha
    rw [ha, gpow_zero', hfp hs]
  · exact absurd hs (by simp)

theorem Kind.regs_unique {entry : ℕ} {k : Kind} {r r' : Semantics.Regs K} (h : k.Regs L fp entry r)
    (h' : k.Regs L fp entry r') : r = r' := by
  cases k with
  | next t => exact h.trans h'.symm
  | ret => exact Option.some.inj (h.symm.trans h')
  | call pc q _ =>
    obtain ⟨p, a, hp, -, ha, rfl⟩ := h
    obtain ⟨p', a', hp', -, ha', rfl⟩ := h'
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    rw [Tgt.is_unique ha ha']
  | jump pc f =>
    obtain ⟨a, b, ha, hb, rfl⟩ := h
    obtain ⟨a', b', ha', hb', rfl⟩ := h'
    rw [Tgt.is_unique ha ha', Tgt.is_unique hb hb']

end Env


/-! ## One instruction: soundness and completeness -/

section Step

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts}

theorem read_addr (hκ : κ ≤ 32) {a : K} {v : E} (h : L.read a = some v) :
    ∃ i < 2 ^ κ, a = gpow i := by
  obtain ⟨i, hi, -⟩ := (MemImage.read_eq_some_iff (by omega) L).mp h
  exact ⟨i, i.isLt, hi⟩

/-- A word of `K` dereferenced at offset `0` is an address. -/
theorem deref0_addr (hκ : κ ≤ 32) {p v : E} (hpK : IsInK p)
    (h : L.read (p.limb 0 * gpow 0) = some v) : ∃ i < 2 ^ κ, p = ofK (gpow i) := by
  rw [gpow_zero', mul_one] at h
  obtain ⟨i, hi, he⟩ := read_addr hκ h
  exact ⟨i, hi, by rw [inK_eq hpK, he]⟩

theorem ofK_gpow_mul (a b : ℕ) : ofK (gpow a) * ofK (gpow b) = ofK (gpow (a + b)) := by
  rw [← ofK_mul, gpow, gpow, gpow, pow_add]

theorem mulFacts_holds {a b c pc : ℕ} {env : Trie Sym} (he : EnvHolds L fp env)
    (hh : Guest.Holds L pc fp (.mul a b c)) :
    ∀ x ∈ mulFacts a b c (env.get a) (env.get b), x.Holds L fp := by
  obtain ⟨vA, vB, hA, hB, hC⟩ := hh
  intro x hx
  simp only [mulFacts, List.mem_append] at hx
  rcases hx with hx | hx
  · split_ifs at hx with hab
    · obtain ⟨rfl, rfl⟩ := hab
      simp only [List.mem_singleton] at hx
      subst hx
      obtain rfl := Option.some.inj (hA.symm.trans hB)
      have hsq := Option.some.inj (hA.symm.trans hC)
      refine ⟨_, hA, ?_⟩
      by_cases h0 : vA = 0
      · exact Or.inl h0
      · exact Or.inr (mul_left_cancel₀ h0 ((mul_one vA).trans hsq)).symm
    · simp at hx
  · split_ifs at hx with h1 h2
    · simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨w, hw, hw1⟩ := isOne_val h1 fp
      have := (he b w hw).symm.trans hB
      rw [hw1] at this
      obtain rfl := Option.some.inj this
      exact ⟨vA, hA, by rw [hC, mul_one]⟩
    · simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨w, hw, hw1⟩ := isOne_val h2 fp
      have := (he a w hw).symm.trans hA
      rw [hw1] at this
      obtain rfl := Option.some.inj this
      exact ⟨vB, hB, by rw [hC, one_mul]⟩
    · simp at hx

theorem mulEnv_holds {a b c pc : ℕ} {env : Trie Sym} (he : EnvHolds L fp env)
    (hh : Guest.Holds L pc fp (.mul a b c)) : EnvHolds L fp (mulEnv F env a b c) := by
  obtain ⟨vA, vB, hA, hB, hC⟩ := hh
  unfold mulEnv
  cases F.scaled.contains a
  · exact he
  · simp only [Bool.cond_true]
    split
    · rename_i e hea
      split
      · rename_i e' heb
        apply he.learn
        obtain ⟨w, hw, hwv⟩ := expo_val heb fp
        obtain rfl := Option.some.inj ((he a _ hea).symm.trans hA)
        obtain rfl := Option.some.inj ((he b w hw).symm.trans hB)
        rw [hC, hwv, Sym.val, Sym.val, ← ofK_mul, mul_assoc, gpow, gpow, gpow, pow_add]
      · exact he
    · exact he

theorem neFacts_holds {o pc : ℕ} {prev : List (ℕ × OInstr)}
    (hprev : ∀ x ∈ prev, Guest.Holds L x.1 fp x.2) (hh : Guest.Holds L pc fp (.set o 1 0 0)) :
    ∀ x ∈ neFacts o prev, x.Holds L fp := by
  have h1 : L.read (fp * gpow o) = some 1 := by
    rw [show (1 : E) = OInstr.imm 1 0 0 from (imm_of_ofBits rfl).trans ofK_one |>.symm]
    exact hh
  unfold neFacts
  split
  next _ x y p' rest =>
    split_ifs with hp
    · subst hp
      obtain ⟨vX, vY, hX, hY, hP⟩ := hprev _ List.mem_cons_self
      have hxy : vX * vY = 1 := Option.some.inj (hP.symm.trans h1)
      have hx0 : vX ≠ 0 := fun h0 ↦ by simp [h0] at hxy
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨vX, hX, hx0⟩
      · split at hz
        next _ a b x' =>
          split_ifs at hz with hx'
          · simp only [List.mem_singleton] at hz
            subst hz hx'
            obtain ⟨vA, vB, hA, hB, hX'⟩ := hprev _ (List.mem_cons_of_mem _ List.mem_cons_self)
            obtain rfl := Option.some.inj (hX.symm.trans hX')
            refine ⟨vA, vB, hA, hB, fun hab ↦ hx0 ?_⟩
            rw [hab, CharTwo.add_self_eq_zero]
          · simp at hz
        next => simp at hz
    · intro z hz
      simp at hz
  next =>
    intro z hz
    simp at hz

theorem rangeFact_holds (hκ : κ ≤ 32) {y t pc : ℕ} {env : Trie Sym} {prev : List (ℕ × OInstr)}
    (he : EnvHolds L fp env) (hprev : ∀ x ∈ prev, Guest.Holds L x.1 fp x.2)
    (hh : Guest.Holds L pc fp (.deref y 0 t .cell)) : ∀ a ∈ rangeFact env y prev, a.Holds L fp := by
  unfold rangeFact
  split
  next _ x y' z _ x' _ =>
    split_ifs with hxy
    · obtain ⟨rfl, rfl⟩ := hxy
      obtain ⟨vX, vY, hX, hY, hZ⟩ := hprev _ List.mem_cons_self
      obtain ⟨p, v3, hp, hpK, -, hp0⟩ := hprev _ (List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨q, w3, hq, hqK, -, hq0⟩ := hh
      obtain ⟨i, hi, rfl⟩ := deref0_addr hκ hpK hp0
      obtain ⟨j, hj, rfl⟩ := deref0_addr hκ hqK hq0
      obtain rfl := Option.some.inj (hX.symm.trans hp)
      obtain rfl := Option.some.inj (hY.symm.trans hq)
      rw [ofK_gpow_mul] at hZ
      split
      · rename_i k hk
        split_ifs with hk63
        · intro a ha
          simp only [List.mem_singleton] at ha
          subst ha
          obtain ⟨w, hw, hwv⟩ := expo_val hk fp
          have := (he z w hw).symm.trans hZ
          rw [hwv] at this
          have hij := gpow_injOn (show k ∈ Set.Iio (2 ^ 64 - 1) by simp only [Set.mem_Iio]; omega)
            (show i + j ∈ Set.Iio (2 ^ 64 - 1) by
              have : 2 ^ κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hκ
              simp only [Set.mem_Iio]; omega)
            (ofK_injective (Option.some.inj this))
          exact ⟨i, j, by omega, hp, hq⟩
        · intro a ha
          simp only [List.mem_singleton] at ha
          subst ha
          exact ⟨i, j, hi, hj, hp, hq, hZ⟩
      · intro a ha
        simp only [List.mem_singleton] at ha
        subst ha
        exact ⟨i, j, hi, hj, hp, hq, hZ⟩
    · intro a ha
      simp at ha
  next =>
    intro a ha
    simp at ha

theorem derefMem_holds {pc o1 o2 o3 : ℕ} {mode : DerefMode} {st : St} (hst : St.Holds L fp st)
    (hh : Guest.Holds L pc fp (.deref o1 o2 o3 mode)) :
    EnvHolds L fp (derefMem pc st o1 o2 o3 mode).1 ∧
      MemHolds L fp (derefMem pc st o1 o2 o3 mode).2 := by
  obtain ⟨p, v3, hp, hpK, h3, hs⟩ := hh
  cases mode with
  | fp =>
    refine ⟨hst.1, (hst.2.1.cons ⟨p, hp, hpK, ?_⟩).take 4⟩
    rw [hs, derefSource_fp, Sym.val, gpow_zero', mul_one]
  | pc =>
    refine ⟨hst.1, (hst.2.1.cons ⟨p, hp, hpK, ?_⟩).take 4⟩
    rw [hs, derefSource_pc]
    rfl
  | cell =>
    simp only [derefMem]
    split
    · rename_i v hv
      obtain ⟨p', hp', -, hs'⟩ := hst.2.1 _ _ _ (memFind_mem hv)
      obtain rfl := Option.some.inj (hp.symm.trans hp')
      have : v3 = v.val fp := Option.some.inj (hs.symm.trans hs')
      exact ⟨hst.1.learn (this ▸ h3), hst.2.1⟩
    · cases o2 == 0
      · exact ⟨hst.1, hst.2.1⟩
      · simp only [Bool.cond_true]
        split
        · rename_i v hv
          have : v3 = v.val fp := Option.some.inj (h3.symm.trans (hst.1 _ _ hv))
          exact ⟨hst.1, (hst.2.1.cons ⟨p, hp, hpK, this ▸ hs⟩).take 4⟩
        · exact ⟨hst.1, hst.2.1⟩

/-- **A non-`JUMP` teaches only what holds.** -/
theorem nonJump_holds (hκ : κ ≤ 32) (hp : F.pows.Ok) {pc : ℕ} {st : St} {ins : OInstr}
    (hst : St.Holds L fp st) (hh : Guest.Holds L pc fp ins) :
    (∀ a ∈ (nonJump F pc st ins).1, a.Holds L fp) ∧ EnvHolds L fp (nonJump F pc st ins).2.1 ∧
      MemHolds L fp (nonJump F pc st ins).2.2 := by
  cases ins with
  | xor a b c =>
    refine ⟨?_, hst.1, hst.2.1⟩
    simp only [nonJump]
    split_ifs with hz
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨vA, vB, hA, hB, hC⟩ := hh
      have := (hst.1 c _ (isZero_eq hz)).symm.trans hC
      exact ⟨vA, hA, by rw [hB, eq_of_add_eq_zero (Option.some.inj this).symm]⟩
    · intro x hx
      simp at hx
  | mul a b c => exact ⟨mulFacts_holds hst.1 hh, mulEnv_holds hst.1 hh, hst.2.1⟩
  | set o k0 k1 k2 =>
    refine ⟨?_, ?_, hst.2.1⟩
    · simp only [nonJump]
      split_ifs with hk
      · obtain ⟨rfl, rfl, rfl⟩ := hk
        exact neFacts_holds hst.2.2 hh
      · intro x hx
        simp at hx
    · simp only [nonJump]
      split
      · rename_i v hv
        exact hst.1.set (by rw [← symOf_val hp hv fp]; exact hh)
      · exact hst.1
  | deref o1 o2 o3 mode =>
    refine ⟨?_, derefMem_holds hst hh⟩
    simp only [nonJump]
    split_ifs with hm
    · obtain ⟨rfl, rfl⟩ := hm
      exact rangeFact_holds hκ hst.1 hst.2.2 hh
    · intro x hx
      simp at hx
  | blake2s => exact ⟨fun x hx ↦ by simp [nonJump] at hx, hst.1, hst.2.1⟩
  | jump => exact absurd hh id

theorem St.Holds.push {st : St} (hst : St.Holds L fp st) {env : Trie Sym}
    {mem : List (ℕ × ℕ × Sym)} (he : EnvHolds L fp env) (hm : MemHolds L fp mem) {pc : ℕ}
    {ins : OInstr} (hh : Guest.Holds L pc fp ins) : St.Holds L fp (st.push env mem pc ins) := by
  refine ⟨he, hm, fun x hx ↦ ?_⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hh
  · exact hst.2.2 x (List.mem_of_mem_take hx)

theorem tgtOf_cell {s : Option Sym} {o q : ℕ} (h : tgtOf s o = .cell q) : q = o := by
  unfold tgtOf at h
  split at h <;> simp_all

/-- **Where a `JUMP` goes is what its exit says.** -/
theorem jumpKind_holds (hfp : F.fpOne = true → fp = 1) {entry len i od of : ℕ} {st : St}
    (hst : St.Holds L fp st) {d f : E} (hd : L.read (fp * gpow od) = some d) (hdK : IsInK d)
    (hf : L.read (fp * gpow of) = some f) (hfK : IsInK f) :
    (jumpKind F entry len i st od of).1.Regs L fp entry ⟨d.limb 0, f.limb 0⟩ ∧
      (jumpKind F entry len i st od of).1.Extra L fp := by
  unfold jumpKind
  split_ifs with h01
  · obtain ⟨rfl, rfl⟩ := h01
    exact ⟨retRegs_eq_some_iff.mpr ⟨d, f, hd, hf, rfl⟩, trivial⟩
  · rw [Tgt.seq_eq, Tgt.seq_eq]
    have hpt := tgtOf_is hst.1 hd hdK
    have hft := tgtOf_is hst.1 hf hfK
    generalize tgtOf (st.env.get od) od = pt at hpt
    generalize hg : tgtOf (st.env.get of) of = ft at hft
    split_ifs with hself
    · have hb := self_is hfp hself hft
      split
      · rename_i e
        split_ifs with hl
        · refine ⟨?_, trivial⟩
          simp only [Kind.Regs, Tgt.Is] at hpt ⊢
          rw [hpt, hb, show entry + (e - entry) = e by omega]
        · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩
      · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩
      · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩
    · split
      · rename_i q
        obtain rfl := tgtOf_cell hg
        split
        · rename_i r v0 h0 h1
          obtain ⟨w, hw, hwv⟩ := expo_val h0 fp
          obtain ⟨p, hp, hpK, hp0⟩ := hst.2.1 _ _ _ (memFind_mem hw)
          obtain ⟨p', hp', -, hp1⟩ := hst.2.1 _ _ _ (memFind_mem h1)
          obtain rfl := Option.some.inj (hp.symm.trans hp')
          obtain rfl := Option.some.inj (hp.symm.trans hf)
          refine ⟨⟨_, _, hp, hpK, hpt, rfl⟩, p, hp, ?_⟩
          rw [hwv] at hp0
          rw [Sym.val, gpow_zero', mul_one] at hp1
          exact retRegs_eq_some_iff.mpr ⟨_, _, hp0, hp1, by simp⟩
        · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩
      · exact ⟨⟨_, _, hpt, hft, rfl⟩, trivial⟩

theorem jumpExit_eq (F : Facts) (entry len i : ℕ) (st : St) (od of : ℕ) :
    jumpExit F entry len i st od of =
      ⟨(jumpKind F entry len i st od of).1, st.env, (jumpKind F entry len i st od of).2⟩ := rfl

end Step


/-! ## One instruction against the run -/

section StepRun

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts} {prog : Program}

/-- What an instruction's result says of the run from it, with `k` steps left: on to the next
offset with one step fewer, or out by an exit. -/
def Res.Sound (L : MemImage κ) (fp : K) (prog : Program) (entry k₀ i k : ℕ) : Res → Prop
  | .go its st => RunK L fp prog entry k₀
      (fun k' ↦ k' + 1 = k ∧ St.Holds L fp st ∧ Safe prog L k' ⟨gpow (entry + i + 1), fp⟩) its k
  | .stop its x => RunK L fp prog entry k₀ (x.Reached L fp prog entry k₀) its k

/-- What an instruction's result gives a run to `r`: from its atoms, the run reaches `r` by an
exit, or the next offset with `Q`. -/
def Res.Comp (L : MemImage κ) (fp : K) (prog : Program) (entry i : ℕ) (r : Semantics.Regs K) :
    Res → Prop
  | .go its st => ∀ Q : Prop, Follows L fp entry r Q its →
      Reach prog L ⟨gpow (entry + i), fp⟩ r ∨
        (Q ∧ St.Holds L fp st ∧ Reach prog L ⟨gpow (entry + i), fp⟩ ⟨gpow (entry + i + 1), fp⟩)
  | .stop its x => Follows L fp entry r (x.kind.Regs L fp entry r) its →
      Reach prog L ⟨gpow (entry + i), fp⟩ r

theorem stepI_of_nonJump {entry len i : ℕ} {st : St} {ins : OInstr} (hj : ins.isJump = false) :
    stepI F entry len i st ins =
      .go (.ins (.instr (entry + i) ins) :: (nonJump F (entry + i) st ins).1.map .fact)
        (st.push (nonJump F (entry + i) st ins).2.1 (nonJump F (entry + i) st ins).2.2 (entry + i)
          ins) := by
  cases ins with
  | jump => simp [OInstr.isJump] at hj
  | _ => rfl

theorem runK_facts {entry k₀ k : ℕ} {Q : ℕ → Prop} {fs : List Atom}
    (h : ∀ a ∈ fs, a.Holds L fp) (hq : Q k) : RunK L fp prog entry k₀ Q (fs.map .fact) k := by
  induction fs with
  | nil => exact hq
  | cons a fs ih =>
    exact ⟨h a List.mem_cons_self, ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)⟩

theorem follows_facts {entry : ℕ} {r : Semantics.Regs K} {Q : Prop} {fs : List Atom} :
    Follows L fp entry r Q (fs.map .fact) ↔ Q := by
  induction fs with
  | nil => rfl
  | cons a fs ih => exact ih

theorem jump_atom {oc od of : ℕ} {c d f : E} (hc : L.read (fp * gpow oc) = some c)
    (hd : L.read (fp * gpow od) = some d) (hf : L.read (fp * gpow of) = some f) (hcK : IsInK c)
    (hdK : IsInK d) (hfK : IsInK f) : (Atom.jump oc od of).Holds L fp :=
  ⟨c, d, f, hc, hd, hf, hcK, hdK, hfK⟩

/-- **One instruction is sound.** -/
theorem stepI_sound (hctx : Ctx F κ fp) {entry len i k k₀ : ℕ} {st : St} {ins : OInstr}
    (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) (hst : St.Holds L fp st) (hk : k ≤ k₀)
    (h : Safe prog L k ⟨gpow (entry + i), fp⟩) :
    (stepI F entry len i st ins).Sound L fp prog entry k₀ i k := by
  cases hj : ins.isJump with
  | false =>
    rw [stepI_of_nonJump hj]
    obtain ⟨k', rfl, hh, hs⟩ := h.fallThrough hf hpc hj
    obtain ⟨hfs, he, hm⟩ := nonJump_holds hctx.le hctx.pows hst hh
    exact ⟨hh, k', rfl, runK_facts hfs ⟨rfl, hst.push he hm hh, hs⟩⟩
  | true =>
    cases ins with
    | jump oc od of =>
      obtain ⟨k', r, rfl, ⟨c, d, f, hc, hd, hf', hcK, hdK, hfK, rfl⟩, hs⟩ := h.jump hf hpc
      have hatom := jump_atom hc hd hf' hcK hdK hfK
      obtain ⟨hreg, hext⟩ := jumpKind_holds (entry := entry) (len := len) (i := i) hctx.fpOne hst hd
        hdK hf' hfK
      have hreach : ∀ x, x = jumpExit F entry len i st od of → c ≠ 0 →
          x.Reached L fp prog entry k₀ k' := by
        rintro x rfl hc0
        rw [ite_eq_right hc0] at hs
        exact ⟨by omega, hst.1, hext, _, hreg, hs⟩
      simp only [stepI, optSeq_eq]
      split_ifs with hz hnz
      · have h0 := (hst.1 oc _ (isZero_eq hz)).symm.trans hc
        obtain rfl : c = 0 := (Option.some.inj h0).symm
        rw [ite_eq_left rfl] at hs
        exact ⟨hatom, k', rfl, rfl, hst, by simpa [Nat.add_assoc] using hs⟩
      · obtain ⟨w, hw, hw0⟩ := isNonzero_val hnz fp
        have hcw : c = w.val fp := Option.some.inj (hc.symm.trans (hst.1 oc w hw))
        exact ⟨hatom, k', rfl, hreach _ rfl (hcw ▸ hw0)⟩
      · refine ⟨hatom, k', rfl, ?_⟩
        by_cases hc0 : c = 0
        · subst hc0
          rw [ite_eq_left rfl] at hs
          exact Or.inl ⟨hc, rfl, hst, by simpa [Nat.add_assoc] using hs⟩
        · exact Or.inr ⟨⟨c, hc, hc0⟩, hreach _ rfl hc0⟩
    | _ => simp [OInstr.isJump] at hj

/-- **One instruction is complete.** -/
theorem stepI_complete (hctx : Ctx F κ fp) {entry len i : ℕ} {st : St} {ins : OInstr}
    (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) (hst : St.Holds L fp st) (r : Semantics.Regs K) :
    (stepI F entry len i st ins).Comp L fp prog entry i r := by
  cases hj : ins.isJump with
  | false =>
    rw [stepI_of_nonJump hj]
    rintro Q ⟨hh, hq⟩
    rw [follows_facts] at hq
    obtain ⟨-, he, hm⟩ := nonJump_holds hctx.le hctx.pows hst hh
    exact Or.inr ⟨hq, hst.push he hm hh, reach_fallThrough hf hpc hj hh⟩
  | true =>
    cases ins with
    | jump oc od of =>
      have hgo : ∀ {c d f : E}, L.read (fp * gpow oc) = some c → L.read (fp * gpow od) = some d →
          L.read (fp * gpow of) = some f → IsInK c → IsInK d → IsInK f → c ≠ 0 →
          (jumpExit F entry len i st od of).kind.Regs L fp entry r →
          Reach prog L ⟨gpow (entry + i), fp⟩ r := by
        intro c d f hc hd hf' hcK hdK hfK hc0 hr
        obtain ⟨hreg, -⟩ := jumpKind_holds (entry := entry) (len := len) (i := i) hctx.fpOne hst
          hd hdK hf' hfK
        rw [jumpExit_eq] at hr
        obtain rfl := Kind.regs_unique hr hreg
        exact reach_jump hf hpc ⟨c, d, f, hc, hd, hf', hcK, hdK, hfK, by rw [ite_eq_right hc0]⟩
      have hnext : ∀ {d f : E}, L.read (fp * gpow oc) = some 0 → L.read (fp * gpow od) = some d →
          L.read (fp * gpow of) = some f → IsInK d → IsInK f →
          Reach prog L ⟨gpow (entry + i), fp⟩ ⟨gpow (entry + i + 1), fp⟩ := by
        intro d f hc hd hf' hdK hfK
        exact reach_jump hf hpc ⟨0, d, f, hc, hd, hf', (isInK_iff _).mpr ⟨0, ofK_zero.symm⟩, hdK,
          hfK, by rw [ite_eq_left rfl]⟩
      simp only [stepI, optSeq_eq]
      split_ifs with hz hnz
      · rintro Q ⟨⟨c, d, f, hc, hd, hf', -, hdK, hfK⟩, hq⟩
        have h0 := (hst.1 oc _ (isZero_eq hz)).symm.trans hc
        obtain rfl : c = 0 := (Option.some.inj h0).symm
        exact Or.inr ⟨hq, hst, hnext hc hd hf' hdK hfK⟩
      · rintro ⟨⟨c, d, f, hc, hd, hf', hcK, hdK, hfK⟩, hr⟩
        obtain ⟨w, hw, hw0⟩ := isNonzero_val hnz fp
        have hcw : c = w.val fp := Option.some.inj (hc.symm.trans (hst.1 oc w hw))
        exact hgo hc hd hf' hcK hdK hfK (hcw ▸ hw0) hr
      · rintro Q ⟨⟨c, d, f, hc, hd, hf', hcK, hdK, hfK⟩, ⟨h0, hq⟩ | ⟨⟨v, hv, hv0⟩, hr⟩⟩
        · obtain rfl : c = 0 := Option.some.inj (hc.symm.trans h0)
          exact Or.inr ⟨hq, hst, hnext hc hd hf' hdK hfK⟩
        · obtain rfl := Option.some.inj (hv.symm.trans hc)
          exact Or.inl (hgo hc hd hf' hcK hdK hfK hv0 hr)
    | _ => simp [OInstr.isJump] at hj

end StepRun


/-! ## Paths: composition -/

section Paths

variable {κ : ℕ} {L : MemImage κ} {fp : K} {prog : Program}

theorem RunK.mono {entry k₀ : ℕ} {Q Q' : ℕ → Prop} (hQ : ∀ k, Q k → Q' k) :
    ∀ {its : List Item} {k : ℕ}, RunK L fp prog entry k₀ Q its k →
      RunK L fp prog entry k₀ Q' its k
  | [], _, h => hQ _ h
  | .ins _ :: _, _, ⟨ha, k', hk, h⟩ => ⟨ha, k', hk, RunK.mono hQ h⟩
  | .fact _ :: _, _, ⟨ha, h⟩ => ⟨ha, RunK.mono hQ h⟩
  | .branch _ _ _ _ :: _, _, ⟨ha, k', hk, h⟩ =>
    ⟨ha, k', hk, h.imp (fun h ↦ ⟨h.1, RunK.mono hQ h.2⟩) id⟩

theorem RunK.append {entry k₀ : ℕ} {Q : ℕ → Prop} :
    ∀ {l₁ l₂ : List Item} {k : ℕ},
      RunK L fp prog entry k₀ (fun k' ↦ RunK L fp prog entry k₀ Q l₂ k') l₁ k →
        RunK L fp prog entry k₀ Q (l₁ ++ l₂) k
  | [], _, _, h => h
  | .ins _ :: _, _, _, ⟨ha, k', hk, h⟩ => ⟨ha, k', hk, RunK.append h⟩
  | .fact _ :: _, _, _, ⟨ha, h⟩ => ⟨ha, RunK.append h⟩
  | .branch _ _ _ _ :: _, _, _, ⟨ha, k', hk, h⟩ =>
    ⟨ha, k', hk, h.imp (fun h ↦ ⟨h.1, RunK.append h.2⟩) id⟩

theorem Follows.append {entry : ℕ} {r : Semantics.Regs K} {Q : Prop} :
    ∀ {l₁ l₂ : List Item}, Follows L fp entry r Q (l₁ ++ l₂) →
      Follows L fp entry r (Follows L fp entry r Q l₂) l₁
  | [], _, h => h
  | .ins _ :: l₁, _, ⟨ha, h⟩ => ⟨ha, Follows.append (l₁ := l₁) h⟩
  | .fact _ :: l₁, _, h => Follows.append (l₁ := l₁) h
  | .branch _ _ _ _ :: l₁, _, ⟨ha, h⟩ =>
    ⟨ha, h.imp (fun h ↦ ⟨h.1, Follows.append (l₁ := l₁) h.2⟩) id⟩

theorem branchExits_append : ∀ (l₁ l₂ : List Item),
    branchExits (l₁ ++ l₂) = branchExits l₁ ++ branchExits l₂
  | [], _ => rfl
  | .ins _ :: l₁, l₂ => branchExits_append l₁ l₂
  | .fact _ :: l₁, l₂ => branchExits_append l₁ l₂
  | .branch _ _ _ x :: l₁, l₂ => congrArg (x :: ·) (branchExits_append l₁ l₂)

theorem mem_branchExits_reverse {x : Exit} : ∀ {l : List Item},
    x ∈ branchExits l.reverse → x ∈ branchExits l
  | [], h => h
  | a :: l, h => by
    rw [List.reverse_cons, branchExits_append, List.mem_append] at h
    rcases h with h | h
    · cases a <;> simp only [branchExits] <;> first | exact List.mem_cons_of_mem _ (mem_branchExits_reverse h) | exact mem_branchExits_reverse h
    · cases a <;> simp_all [branchExits]

theorem branchExits_reverseAux : ∀ (l acc : List Item),
    branchExits (l.reverseAux acc) = (branchExits l).reverseAux (branchExits acc)
  | [], _ => rfl
  | .ins a :: l, acc => branchExits_reverseAux l (.ins a :: acc)
  | .fact a :: l, acc => branchExits_reverseAux l (.fact a :: acc)
  | .branch oc od of x :: l, acc => branchExits_reverseAux l (.branch oc od of x :: acc)

end Paths

/-! ## The pass: soundness and completeness -/

section Pass

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts} {prog : Program} {entry len : ℕ}

/-- **A good segment**: from its start, with its environment, it is sound (`RunK`) and complete
(`Follows`), and `exits` lists its exits. -/
def SegGood (L : MemImage κ) (fp : K) (prog : Program) (entry : ℕ) (s : Seg) : Prop :=
  (∀ k₀, EnvHolds L fp s.env → Safe prog L k₀ ⟨gpow (entry + s.start), fp⟩ →
    RunK L fp prog entry k₀ (s.exit.Reached L fp prog entry k₀) s.items k₀) ∧
  (EnvHolds L fp s.env → ∀ r, Follows L fp entry r (s.exit.kind.Regs L fp entry r) s.items →
    Reach prog L ⟨gpow (entry + s.start), fp⟩ r) ∧
  (∀ x, x = s.exit ∨ x ∈ branchExits s.items → x ∈ s.exits)

/-- A good segment being walked, at offset `i`. -/
def CurGood (L : MemImage κ) (fp : K) (prog : Program) (entry : ℕ) (c : Cur) (i : ℕ) : Prop :=
  c.start ≤ i ∧ branchExits c.acc = c.xs ∧
  (∀ k₀, EnvHolds L fp c.env → Safe prog L k₀ ⟨gpow (entry + c.start), fp⟩ →
    RunK L fp prog entry k₀ (fun k ↦ k + i = k₀ + c.start ∧ St.Holds L fp c.st ∧
      Safe prog L k ⟨gpow (entry + i), fp⟩) c.acc.reverse k₀) ∧
  (EnvHolds L fp c.env → ∀ r Q, Follows L fp entry r Q c.acc.reverse →
    Reach prog L ⟨gpow (entry + c.start), fp⟩ r ∨
      (Q ∧ St.Holds L fp c.st ∧ Reach prog L ⟨gpow (entry + c.start), fp⟩ ⟨gpow (entry + i), fp⟩))

theorem stHolds_init {env : Trie Sym} (he : EnvHolds L fp env) : St.Holds L fp (St.init env) :=
  ⟨he, fun _ _ _ h ↦ by simp [St.init] at h, fun _ h ↦ by simp [St.init] at h⟩

theorem curGood_init (i : ℕ) (env : Trie Sym) : CurGood L fp prog entry (Cur.init i env) i := by
  refine ⟨le_rfl, rfl, fun k₀ he hs ↦ ?_, fun he r Q hq ↦ Or.inr ⟨hq, stHolds_init he, Reach.refl _⟩⟩
  exact ⟨by simp [Cur.init], stHolds_init he, hs⟩

theorem items_close (c : Cur) (its : List Item) :
    ((its.reverseAux c.acc).reverse) = c.acc.reverse ++ its := by
  rw [List.reverseAux_eq, List.reverse_append, List.reverse_reverse]

theorem segGood_close {c : Cur} {i : ℕ} (hc : CurGood L fp prog entry c i) (hlt : c.start < i)
    (succ : List ℕ) : SegGood L fp prog entry (c.close [] ⟨.next i, c.st.env, succ⟩) := by
  obtain ⟨-, hxs, hsound, hcomp⟩ := hc
  refine ⟨fun k₀ he hs ↦ ?_, fun he r hf ↦ ?_, fun x hx ↦ ?_⟩
  · simp only [Cur.close, items_close, List.append_nil]
    refine RunK.mono (fun k ⟨hk, hst, hs'⟩ ↦ ⟨by omega, hst.1, trivial, _, rfl, hs'⟩)
      (hsound k₀ he hs)
  · simp only [Cur.close, items_close, List.append_nil] at hf
    rcases hcomp he r _ hf with h | ⟨rfl, -, h⟩
    · exact h
    · exact h
  · simp only [Cur.close] at hx ⊢
    rcases hx with rfl | hx
    · exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      have := mem_branchExits_reverse hx
      rwa [branchExits_reverseAux, hxs] at this

theorem curGood_go (hctx : Ctx F κ fp) {c : Cur} {i : ℕ} {ins : OInstr}
    (hc : CurGood L fp prog entry c i) (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) {its : List Item} {st : St}
    (hs : stepI F entry len i c.st ins = .go its st) :
    CurGood L fp prog entry
      ⟨c.start, c.env, its.reverseAux c.acc, (branchExits its).reverseAux c.xs, st⟩ (i + 1) := by
  obtain ⟨hle, hxs, hsound, hcomp⟩ := hc
  refine ⟨show c.start ≤ i + 1 by omega, by simp only; rw [branchExits_reverseAux, hxs],
    fun k₀ he h0 ↦ ?_, fun he r Q hq ↦ ?_⟩
  · simp only
    rw [List.reverseAux_eq, List.reverse_append, List.reverse_reverse]
    refine RunK.append (RunK.mono (fun k ⟨hk, hst, hs'⟩ ↦ ?_) (hsound k₀ he h0))
    have := stepI_sound (len := len) (k₀ := k₀) hctx hf hpc hst (by omega) hs'
    rw [hs] at this
    refine RunK.mono (fun k' ⟨hk', hst', hs''⟩ ↦ ⟨by omega, hst', ?_⟩) this
    simpa [Nat.add_assoc] using hs''
  · simp only at hq
    rw [List.reverseAux_eq, List.reverse_append, List.reverse_reverse] at hq
    rcases hcomp he r _ (Follows.append hq) with h | ⟨hq', hst, h⟩
    · exact Or.inl h
    · have := stepI_complete (len := len) hctx hf hpc hst r
      rw [hs] at this
      rcases this Q hq' with h' | ⟨hQ, hst', h'⟩
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨hQ, hst', by simpa [Nat.add_assoc] using h.trans h'⟩

theorem segGood_stop (hctx : Ctx F κ fp) {c : Cur} {i : ℕ} {ins : OInstr}
    (hc : CurGood L fp prog entry c i) (hf : prog.fetch (gpow (entry + i)) = some ins.toInstr)
    (hpc : entry + i < 2 ^ prog.logSize - 1) {its : List Item} {x : Exit}
    (hs : stepI F entry len i c.st ins = .stop its x) : SegGood L fp prog entry (c.close its x) := by
  obtain ⟨hle, hxs, hsound, hcomp⟩ := hc
  refine ⟨fun k₀ he h0 ↦ ?_, fun he r hq ↦ ?_, fun y hy ↦ ?_⟩
  · simp only [Cur.close, items_close]
    refine RunK.append (RunK.mono (fun k ⟨hk, hst, hs'⟩ ↦ ?_) (hsound k₀ he h0))
    have := stepI_sound (len := len) (k₀ := k₀) hctx hf hpc hst (by omega) hs'
    rw [hs] at this
    exact this
  · simp only [Cur.close, items_close] at hq
    rcases hcomp he r _ (Follows.append hq) with h | ⟨hq', hst, h⟩
    · exact h
    · have := stepI_complete (len := len) hctx hf hpc hst r
      rw [hs] at this
      exact h.trans (this hq')
  · simp only [Cur.close] at hy ⊢
    rcases hy with rfl | hy
    · exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      have := mem_branchExits_reverse hy
      rwa [branchExits_reverseAux, hxs] at this

theorem atJoin_good {i : ℕ} {cur : Option Cur} {pend : Pend} {out : List Seg}
    (hcur : ∀ c, cur = some c → CurGood L fp prog entry c i)
    (hout : ∀ s ∈ out, SegGood L fp prog entry s) :
    (∀ c, (atJoin i cur pend out).1 = some c → CurGood L fp prog entry c i) ∧
      ∀ s ∈ (atJoin i cur pend out).2.2, SegGood L fp prog entry s := by
  unfold atJoin
  split
  · rename_i t a ps
    split_ifs with ht
    · cases cur with
      | some c =>
        simp only [Trie.seq_eq]
        split_ifs with hlt
        · refine ⟨fun c' hc' ↦ ?_, fun s hs ↦ ?_⟩
          · obtain rfl := Option.some.inj hc'
            exact curGood_init i _
          · rcases List.mem_cons.mp hs with rfl | hs
            · exact segGood_close (hcur c rfl) hlt [i]
            · exact hout s hs
        · refine ⟨fun c' hc' ↦ ?_, hout⟩
          obtain rfl := Option.some.inj hc'
          exact curGood_init i _
      | none =>
        simp only [Trie.seq_eq]
        refine ⟨fun c' hc' ↦ ?_, hout⟩
        obtain rfl := Option.some.inj hc'
        exact curGood_init i _
    · exact ⟨hcur, hout⟩
  · exact ⟨hcur, hout⟩

theorem Fetches.tail {pc : ℕ} {ins : OInstr} {rest : List OInstr}
    (h : Fetches prog pc (ins :: rest)) : Fetches prog (pc + 1) rest := by
  intro j ins' hj
  have := h (j + 1) ins' (by simpa using hj)
  simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem Fetches.head {pc : ℕ} {ins : OInstr} {rest : List OInstr}
    (h : Fetches prog pc (ins :: rest)) :
    prog.fetch (gpow pc) = some ins.toInstr ∧ pc < 2 ^ prog.logSize - 1 := by
  simpa using h 0 ins rfl

/-- **The walk produces good segments.** -/
theorem pass_good (hctx : Ctx F κ fp) : ∀ (code : List OInstr) (i : ℕ) (cur : Option Cur)
    (pend : Pend) (out : List Seg) (dead : ℕ), Fetches prog (entry + i) code →
    (∀ c, cur = some c → CurGood L fp prog entry c i) →
    (∀ s ∈ out, SegGood L fp prog entry s) →
    ∀ s ∈ (pass F entry len code i cur pend out dead).segs, SegGood L fp prog entry s
  | [], i, cur, pend, out, dead, _, hcur, hout => by
    show ∀ s ∈ (passEnd len i cur out dead).segs, _
    unfold passEnd
    cases cur with
    | none => exact hout
    | some c =>
      simp only
      by_cases hlt : c.start < i
      · rw [ite_eq_left hlt]
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact segGood_close (hcur c rfl) hlt _
        · exact hout s hs
      · rw [ite_eq_right hlt]
        exact hout
  | ins :: rest, i, cur, pend, out, dead, hf, hcur, hout => by
    show ∀ s ∈ (passStep F entry len ins (pass F entry len rest) i cur pend out dead).segs, _
    obtain ⟨hcur', hout'⟩ := atJoin_good (pend := pend) hcur hout
    have hrest : Fetches prog (entry + (i + 1)) rest := by
      simpa [Nat.add_assoc] using hf.tail
    obtain ⟨hfi, hpc⟩ := hf.head
    unfold passStep
    rcases hj : atJoin i cur pend out with ⟨cur', pend', out'⟩
    rw [hj] at hcur' hout'
    cases cur' with
    | none =>
      simp only [natSeq_eq]
      exact pass_good hctx rest (i + 1) none pend' out' (dead + 1) hrest (fun _ h ↦ by cases h)
        hout'
    | some c =>
      have hc := hcur' c rfl
      simp only
      rcases hs : stepI F entry len i c.st ins with ⟨its, st⟩ | ⟨its, x⟩
      · simp only [St.seq_eq, headSeq_eq, natSeq_eq]
        exact pass_good hctx rest (i + 1) _ _ out' dead hrest
          (fun c' h ↦ Option.some.inj h ▸ curGood_go hctx hc hfi hpc hs) hout'
      · simp only [headSeq_eq, natSeq_eq]
        refine pass_good hctx rest (i + 1) none _ _ dead hrest (fun _ h ↦ by cases h) ?_
        intro s hs'
        rcases List.mem_cons.mp hs' with rfl | hs'
        · exact segGood_stop hctx hc hfi hpc hs
        · exact hout' s hs'

end Pass


/-! ## The executor: soundness, completeness, linking -/

section Main

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts} {prog : Program} {f : CompiledFn}

/-- Every segment of `exec F f` is good. -/
theorem exec_good (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) :
    ∀ s ∈ (exec F f).segs, SegGood L fp prog f.entry s :=
  pass_good hctx f.code 0 _ [] [] 0 (by simpa using hf)
    (fun _ h ↦ Option.some.inj h ▸ curGood_init 0 _) (fun _ h ↦ by cases h)

/-- **Soundness**: a halting run entering a segment of `exec F f` at its start, in a frame its
environment holds of, satisfies every atom of the path it takes, one step per instruction, and
leaves by that path's exit (`Exit.Reached`: with fewer steps left, its environment holding,
at the registers its kind names). -/
theorem exec_sound (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) {s : Seg}
    (hs : s ∈ (exec F f).segs) {k : ℕ} (he : EnvHolds L fp s.env)
    (h : Safe prog L k ⟨gpow (f.entry + s.start), fp⟩) :
    RunK L fp prog f.entry k (s.exit.Reached L fp prog f.entry k) s.items k :=
  (exec_good hctx hf s hs).1 k he h

/-- **Completeness**: on a memory satisfying the atoms of a path of a segment, in a frame its
environment holds of, the run from the segment's start reaches the registers the path's exit
names. -/
theorem exec_complete (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) {s : Seg}
    (hs : s ∈ (exec F f).segs) (he : EnvHolds L fp s.env) {r : Semantics.Regs K}
    (h : Follows L fp f.entry r (s.exit.kind.Regs L fp f.entry r) s.items) :
    Reach prog L ⟨gpow (f.entry + s.start), fp⟩ r :=
  (exec_good hctx hf s hs).2.1 he r h

/-- A segment lists its exits: its final one and its branches'. -/
theorem exec_exits (L : MemImage κ) (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) {s : Seg}
    (hs : s ∈ (exec F f).segs) {x : Exit} (hx : x = s.exit ∨ x ∈ branchExits s.items) :
    x ∈ s.exits :=
  (exec_good (L := L) hctx hf s hs).2.2 x hx

theorem index_get {segs : List Seg} {t : ℕ} {s : Seg} (h : (index segs).get t = some s) :
    s ∈ segs := by
  have key : ∀ (l : List Seg) (acc : Trie Seg),
      (l.foldl (fun t s ↦ t.set s indexDepth s.start) acc).get t = some s →
        s ∈ l ∨ acc.get t = some s := by
    intro l
    induction l with
    | nil => exact fun _ h ↦ Or.inr h
    | cons a l ih =>
      intro acc h
      rcases ih _ h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · rcases Trie.get_set h with ⟨-, rfl⟩ | h
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h
  rcases key segs .nil h with h | h
  · exact h
  · simp at h

/-- **Linking**: when the result is linked, every successor of an exit starts a segment whose
entry environment holds wherever the exit's does. -/
theorem Result.linked_spec {R : Result} (hl : R.linked = true) {s : Seg} (hs : s ∈ R.segs)
    {x : Exit} (hx : x ∈ s.exits) {t : ℕ} (ht : t ∈ x.succ) :
    ∃ s' ∈ R.segs, s'.start = t ∧
      ∀ {κ : ℕ} (L : MemImage κ) (fp : K), EnvHolds L fp x.env → EnvHolds L fp s'.env := by
  obtain ⟨segs, dead⟩ := R
  simp only [Result.linked, listSeq_eq, Trie.seq_eq, linkedWith, List.all_eq_true] at hl
  have h := hl s hs x hx t ht
  split at h
  · rename_i s' hs'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨s', index_get hs', h.1, fun L fp he ↦ he.sub h.2⟩
  · exact absurd h (by simp)

/-- The code of a guest function is fetched at its pcs. -/
theorem guest_fetches {f : CompiledFn} (hf : f ∈ Data.functions) : Fetches guest f.entry f.code := by
  intro j ins hj
  have hw := CompiledFn.wellChunked_of_mem hf
  obtain ⟨hjl, -⟩ := List.getElem?_eq_some_iff.mp hj
  rw [CompiledFn.length_code hw] at hjl
  rw [CompiledFn.getElem?_code hw hjl] at hj
  obtain rfl := Option.some.inj hj
  exact ⟨guest_fetch hf hjl, guest_pc_lt hf hjl⟩

end Main


/-! ## Straight segments -/

section Straight

variable {κ : ℕ} {L : MemImage κ} {fp : K} {prog : Program}

/-- The atom of an item, if it has one of its own. -/
def Item.atom? : Item → Option Atom
  | .ins a => some a
  | .fact a => some a
  | .branch .. => none

/-- **A path without branches**: every atom holds, and the end is reached. -/
theorem RunK.straight {entry k₀ : ℕ} {Q : ℕ → Prop} :
    ∀ {its : List Item} {k : ℕ}, branchExits its = [] → RunK L fp prog entry k₀ Q its k →
      (∀ a ∈ its.filterMap Item.atom?, a.Holds L fp) ∧ ∃ k' ≤ k, Q k'
  | [], k, _, h => ⟨fun _ h ↦ by simp at h, k, le_rfl, h⟩
  | .ins a :: its, _, hb, ⟨ha, k', rfl, h⟩ => by
    obtain ⟨hs, k'', hk, hq⟩ := RunK.straight (its := its) hb h
    refine ⟨fun b hb' ↦ ?_, k'', by omega, hq⟩
    simp only [List.filterMap_cons, Item.atom?, List.mem_cons] at hb'
    rcases hb' with rfl | hb'
    · exact ha
    · exact hs b hb'
  | .fact a :: its, k, hb, ⟨ha, h⟩ => by
    obtain ⟨hs, k'', hk, hq⟩ := RunK.straight (its := its) hb h
    refine ⟨fun b hb' ↦ ?_, k'', hk, hq⟩
    simp only [List.filterMap_cons, Item.atom?, List.mem_cons] at hb'
    rcases hb' with rfl | hb'
    · exact ha
    · exact hs b hb'
  | .branch _ _ _ _ :: _, _, hb, _ => by simp [branchExits] at hb

end Straight


/-! ## Windows -/

section Windows

variable {κ : ℕ} {L : MemImage κ} {fp : K} {F : Facts} {prog : Program} {f : CompiledFn}

theorem Fetches.window {pc : ℕ} {code : List OInstr} (h : Fetches prog pc code) (a n : ℕ) :
    Fetches prog (pc + a) ((code.drop a).take n) := by
  intro j ins hj
  rw [List.getElem?_take] at hj
  split_ifs at hj
  rw [List.getElem?_drop] at hj
  simpa [Nat.add_assoc] using h (a + j) ins hj

/-- Every segment of a window is good. -/
theorem execWin_good (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) (a : ℕ)
    (env : List (ℕ × Sym)) (b : ℕ) : ∀ s ∈ (execWin F f a env b).segs, SegGood L fp prog f.entry s :=
  pass_good hctx _ a _ [] [] 0 (hf.window a (b - a))
    (fun _ h ↦ Option.some.inj h ▸ curGood_init a _) (fun _ h ↦ by cases h)

/-- **Soundness** on a window, as `exec_sound`. -/
theorem execWin_sound (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) {a b : ℕ}
    {env : List (ℕ × Sym)} {s : Seg} (hs : s ∈ (execWin F f a env b).segs) {k : ℕ}
    (he : EnvHolds L fp s.env) (h : Safe prog L k ⟨gpow (f.entry + s.start), fp⟩) :
    RunK L fp prog f.entry k (s.exit.Reached L fp prog f.entry k) s.items k :=
  (execWin_good hctx hf a env b s hs).1 k he h

/-- **Completeness** on a window, as `exec_complete`. -/
theorem execWin_complete (hctx : Ctx F κ fp) (hf : Fetches prog f.entry f.code) {a b : ℕ}
    {env : List (ℕ × Sym)} {s : Seg} (hs : s ∈ (execWin F f a env b).segs)
    (he : EnvHolds L fp s.env) {r : Semantics.Regs K}
    (h : Follows L fp f.entry r (s.exit.kind.Regs L fp f.entry r) s.items) :
    Reach prog L ⟨gpow (f.entry + s.start), fp⟩ r :=
  (execWin_good hctx hf a env b s hs).2.1 he r h

/-- **Linking across windows**: every successor of an exit of a window starts one of its
segments, or one of the windows `ext`, with an environment holding where the exit's does. -/
theorem Result.linkedExt_spec {ext : List (ℕ × List (ℕ × Sym))} {R : Result}
    (hl : R.linkedExt ext = true) {s : Seg} (hs : s ∈ R.segs) {x : Exit} (hx : x ∈ s.exits) {t : ℕ}
    (ht : t ∈ x.succ) :
    (∃ s' ∈ R.segs, s'.start = t ∧
      ∀ {κ : ℕ} (L : MemImage κ) (fp : K), EnvHolds L fp x.env → EnvHolds L fp s'.env) ∨
    ∃ e, (t, e) ∈ ext ∧
      ∀ {κ : ℕ} (L : MemImage κ) (fp : K), EnvHolds L fp x.env → EnvHolds L fp (envOf e) := by
  obtain ⟨segs, dead⟩ := R
  simp only [Result.linkedExt, listSeq_eq, Trie.seq_eq, linkedExtWith, List.all_eq_true] at hl
  have h := hl s hs x hx t ht
  split at h
  · rename_i s' hs'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact Or.inl ⟨s', index_get hs', h.1, fun L fp he ↦ he.sub h.2⟩
  · split at h
    · rename_i e he
      have hu := List.find?_some he
      have hmem := List.mem_of_find?_eq_some he
      obtain ⟨⟨u', e0⟩, hm0, rfl⟩ := List.mem_map.mp hmem
      simp only [beq_iff_eq] at hu
      subst hu
      exact Or.inr ⟨e0, hm0, fun L fp hx' ↦ hx'.sub h⟩
    · exact absurd h (by simp)

end Windows

end
end LeanVM.Guest.Exec
