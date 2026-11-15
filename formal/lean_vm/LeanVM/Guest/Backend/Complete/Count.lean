/-
  LeanVM.Guest.Backend.Complete.Count

  Instruction counts of placed code: per instruction, the path maxima of a placed body and the
  separately counted arms, in the form the guest's count tables hold them.
-/

module

public import LeanVM.Guest.Backend.Place
public import LeanVM.Guest.Backend.Sound.Ops

/-!
# Counts of placed code

`pmaxP keyed pf` is the most instructions of each opcode a path through a placed body to a
return runs; for a separately counted function (`keyed`) the arms of its top-level chains are
left out, and `armsP` lists each such stage's arms' counts with its core selector's number, as
`Plumb.pmax` and `Data.cplArms` hold them. They are computable, so the guest checks them against
its tables by evaluation (`lake exe guest-cplcheck`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- The first control statement of a core block and the statements after it: the core statement
the next control `PStmt` of the placed block stands for. -/
def ctrlSplit : List Stmt → Option (Stmt × List Stmt)
  | [] => none
  | .atom _ :: cs => ctrlSplit cs
  | s :: cs => some (s, cs)

/-- The opcode a labelled instruction assembles to. -/
def lopCode : LOp → Opcode
  | .mulNextFrame .. => .mulNative
  | .set .. => .setConstant
  | .xor .. => .xor
  | .mul .. => .mulNative
  | .deref .. => .deref
  | .jump .. => .jump
  | .slot .. => .deref
  | .keccak .. => .keccak

/-- One instruction, counted by opcode. -/
def lopCnt (o : LOp) : Opcode → ℕ := fun op => if op = lopCode o then 1 else 0

/-- Instructions, counted by opcode. -/
def opsCnt (os : List LOp) : Opcode → ℕ := fun op => (os.map (lopCnt · op)).sum

/-- A `JUMP`. -/
def jumpCnt : Opcode → ℕ := fun op => if op = .jump then 1 else 0

/-- A `SET` and a `JUMP`. -/
def setJump : Opcode → ℕ := fun op => (if op = .setConstant then 1 else 0) + jumpCnt op

/-- A chain's head: `SET join`, the table read (a `DEREF`), the `JUMP`. -/
def chainHead : Opcode → ℕ := fun op => setJump op + (if op = .deref then 1 else 0)

/-- The most instructions of each opcode the paths through a block run: over the paths that fall
through it (`fall`) and those that leave by a return (`ret`), `none` for no path. -/
structure PM where
  fall : Option (Opcode → ℕ)
  ret : Option (Opcode → ℕ)

/-- The elementwise greater of two maxima. -/
def omax : Option (Opcode → ℕ) → Option (Opcode → ℕ) → Option (Opcode → ℕ)
  | none, b => b
  | a, none => a
  | some a, some b => some fun op => max (a op) (b op)

/-- Either of two alternatives. -/
def PM.alt (a b : PM) : PM := ⟨omax a.fall b.fall, omax a.ret b.ret⟩

/-- One block after another. -/
def PM.seq (a b : PM) : PM :=
  ⟨a.fall.bind fun x => b.fall.map (x + ·),
    omax a.ret (a.fall.bind fun x => b.ret.map (x + ·))⟩

/-- `c` instructions before. -/
def PM.after (c : Opcode → ℕ) (a : PM) : PM := ⟨a.fall.map (c + ·), a.ret.map (c + ·)⟩

mutual
/-- The path maxima of a placed statement; `keyed` and `top`: a chain at the top of a
separately counted function counts none of its arms (`armsP` does). -/
def pmS (keyed top : Bool) : PStmt → PM
  | .op _ o => ⟨some (lopCnt o), none⟩
  | .ite _ _ _ _ zero hasElse _ _ nonzero =>
      PM.alt
        (PM.after setJump ⟨(pmL keyed false zero).fall.map (· + if hasElse then setJump else 0),
          (pmL keyed false zero).ret⟩)
        (if hasElse then PM.after setJump (pmL keyed false nonzero) else ⟨some setJump, none⟩)
  | .chain _ _ _ _ _ _ _ stages => PM.after chainHead (pmStages keyed (keyed && top) stages)
  | .call _ c =>
      ⟨some (opsCnt (callPre c) + jumpCnt + opsCnt (callRets c.nfp c.args.length c.rets)),
        if c.tail then some (opsCnt (callPre c) + jumpCnt) else none⟩
  | .loopNext _ callee nfp entry _ one args =>
      ⟨some (opsCnt (loopPre callee nfp entry one args) + jumpCnt),
        some (opsCnt (loopPre callee nfp entry one args) + jumpCnt)⟩
  | .dispatch _ _ nfp joinCell x entry _ first args rets =>
      ⟨some (opsCnt (dispatchPre 0 nfp joinCell x entry first args) + jumpCnt +
        opsCnt (callRets nfp args.length rets)), none⟩
  | .ret _ _ => ⟨none, some jumpCnt⟩
  | .halt _ _ _ => ⟨none, some setJump⟩

/-- The path maxima of a placed block. -/
def pmL (keyed top : Bool) : List PStmt → PM
  | [] => ⟨some 0, none⟩
  | s :: ss => PM.seq (pmS keyed top s) (pmL keyed top ss)

/-- The path maxima of a chain's stages; `apart`: the arms are counted separately. -/
def pmStages (keyed apart : Bool) : List (List (List PStmt)) → PM
  | [] => ⟨some 0, none⟩
  | st :: sts => PM.seq (pmArms keyed apart st) (pmStages keyed apart sts)

/-- The path maxima of a stage's arms, one of which runs. -/
def pmArms (keyed apart : Bool) : List (List PStmt) → PM
  | [] => ⟨none, none⟩
  | a :: as =>
      PM.alt
        (if apart then ⟨(pmL keyed false a).fall.map (fun _ => 0), (pmL keyed false a).ret⟩
         else pmL keyed false a)
        (pmArms keyed apart as)
end

/-- **The path maxima of a function's placed body**: the most instructions of each opcode a path
to a return runs, a separately counted function's top-level chains' arms excluded. -/
def pmaxP (keyed : Bool) (pf : Placed) : Opcode → ℕ :=
  ((pmL keyed true pf.fn.body).ret).getD 0

/-- An opcode's position in `Opcode`'s order (`B2C.opIdx`). -/
def opIx : Opcode → ℕ
  | .xor => 0
  | .mulNative => 1
  | .setConstant => 2
  | .deref => 3
  | .jump => 4
  | .keccak => 5

/-- Counts as a list in `Opcode`'s order, as the guest's tables hold them. -/
def ofCnt (c : Opcode → ℕ) : List ℕ :=
  [c .xor, c .mulNative, c .setConstant, c .deref, c .jump, c .keccak]

/-- The arms' counts of a stage: the most each arm runs to its end, none for an arm that does not
fall through. -/
def armCnts (keyed : Bool) (st : List (List PStmt)) : List (List ℕ) :=
  st.map fun a => ofCnt (((pmL keyed false a).fall).getD 0)

/-- A chain's separately counted stages, each with its core `match`'s selector number. -/
def stageCnts (keyed : Bool) : List Stmt → List (List (List PStmt)) → List (ℕ × List (List ℕ))
  | .match_ x _ :: cms, st :: sts => (x.idx, armCnts keyed st) :: stageCnts keyed cms sts
  | _, _ => []

/-- The separately counted `match`es of a placed block, the core block being `cs`: each stage of
a top-level chain with its core selector's number and its arms' counts. -/
def armsGo (keyed : Bool) : List PStmt → List Stmt → List (ℕ × List (List ℕ))
  | [], _ => []
  | .op _ _ :: ps, cs => armsGo keyed ps cs
  | .chain _ _ _ _ _ _ _ stages :: ps, cs =>
      match ctrlSplit cs with
      | some (s, rest) =>
          stageCnts keyed ((s :: rest).take stages.length) stages ++
            armsGo keyed ps ((s :: rest).drop stages.length)
      | none => []
  | _ :: ps, cs =>
      match ctrlSplit cs with
      | some (_, rest) => armsGo keyed ps rest
      | none => []

/-- **The separately counted arms of a function** (`Data.cplArms`' format), none if it is not
separately counted. -/
def armsP (keyed : Bool) (tf : TracedFn) (pf : Placed) : List (ℕ × List (List ℕ)) :=
  if keyed then armsGo keyed pf.fn.body tf.core.body else []

/-! ## Alignment of the placed body with the core body -/

mutual
/-- Whether the placed statement `p` stands for the core statements from the start of `cs` (an
instruction for none, a control statement for the next control statement of `cs`), and `k` holds
of the core statements after it. -/
def alS : PStmt → List Stmt → (List Stmt → Bool) → Bool
  | .op _ _, cs, k => k cs
  | .ite _ _ _ _ zero hasElse _ _ nonzero, cs, k =>
      match ctrlSplit cs with
      | some (.ite _ z n, rest) =>
          alL zero z && (if hasElse then alL nonzero n else (ctrlSplit n).isNone) && k rest
      | _ => false
  | .chain _ _ _ _ _ _ _ stages, cs, k =>
      match ctrlSplit cs with
      | some (s, rest) =>
          decide (stages.length ≤ (s :: rest).length) &&
            alStages stages ((s :: rest).take stages.length) && k ((s :: rest).drop stages.length)
      | none => false
  | .call _ _, cs, k =>
      match ctrlSplit cs with
      | some (.call _ _ _, rest) => k rest
      | some (.callIf _ _ _, rest) => k rest
      | _ => false
  | .loopNext _ _ _ _ _ _ _, cs, k =>
      match ctrlSplit cs with
      | some (.callIf _ _ _, rest) => k rest
      | _ => false
  | .dispatch _ _ _ _ _ _ _ _ _ _, cs, k =>
      match ctrlSplit cs with
      | some (.dispatch _ _ _ _, rest) => k rest
      | _ => false
  | .ret _ _, cs, k =>
      match ctrlSplit cs with
      | some (.ret _, rest) => k rest
      | _ => false
  | .halt _ _ _, cs, k =>
      match ctrlSplit cs with
      | some (.ret _, rest) => k rest
      | _ => false

/-- **Whether a placed block and a core block pair up**: a run of atoms with a run of `PStmt.op`,
each control statement with one control `PStmt`, a run of `k + 1` `match`es with one `chain` of
`k + 1` stages, arm with arm. -/
def alL : List PStmt → List Stmt → Bool
  | [], cs => (ctrlSplit cs).isNone
  | s :: ss, cs => alS s cs (fun cs' => alL ss cs')

/-- A chain's stages and the core `match`es, arm with arm. -/
def alStages : List (List (List PStmt)) → List Stmt → Bool
  | [], _ => true
  | st :: sts, .match_ _ arms :: cms => alArms st arms && alStages sts cms
  | _, _ => false

/-- A stage's arms and the core arms. -/
def alArms : List (List PStmt) → List (List Stmt) → Bool
  | [], [] => true
  | pa :: pas, a :: as => alL pa a && alArms pas as
  | _, _ => false
end

/-- **A placed function pairs up with its core body.** -/
def Aligned (tf : TracedFn) (pf : Placed) : Prop := alL pf.fn.body tf.core.body = true
end
end LeanVM.Guest.Backend.Complete
