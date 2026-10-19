/-
  LeanVM.Guest.B2C.Defs

  The choices B2's completeness rests on: the certificate's cell of each core value, the frame
  sizes, the header of each callee, the cells of each frame of the honest memory, and the
  instruction counts per call tree.
-/

module

public import LeanVM.Guest.Memory
public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.Memory.Fresh
public import LeanVM.Guest.Glob
public import LeanVM.Guest.Frames
public import LeanVM.Guest.Data.Plumb
public import LeanVM.Guest.Data.CplArms

/-!
# The honest memory's frames

`cert f v` is the certificate's cell of value `v` of `f` and `fs f` its frame size (`main`'s
frame also holds the jump table, cells `167 + s`). An instance's cells (`C`) are, first one per
cell (`frameE`): its range checks' temporaries, its frame runs, its fixed cells (`Plumb.stat`:
constants and frame-pointer products), every value its path names (`namedOf`: parameters, the
events' values, the returned values), the callee frame pointer and dispatch target of each call
on its path (`siteE`), the target of each table jump (`armWord`, the jump table's word at the
selector), and in `main` the jump table. A phantom's cells are its parameters and its self frame
pointer cells, which its caller writes. A callee's header (`H`) is the return pc of its call site
and the caller's frame, or, for a loop's tail call, the caller's own header.

`cnt T op` counts, per instance of `T` that runs, the most instructions of opcode `op` a path
through its function's code runs (`pathMax`), plus the jump table's `SET`s.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## Functions by name -/

/-- The compiled index of a core function. -/
noncomputable def idxOf (f : String) : Option ℕ := (coreProgram.indexOf? f).map (· + 1)

/-- The completeness data of compiled function `j`. -/
noncomputable def plumbOf (j : ℕ) : Plumb := nth Data.plumbs j {}

/-- **The certificate's cell** of each value of each function. -/
noncomputable def cert (f : String) (v : V) : ℕ :=
  match idxOf f with
  | some j => (certOf j).locs.getD v.idx 0
  | none => 0

/-- `main`'s frame: its cells and the jump table after them. -/
def mainFrame : ℕ := 167 + 4478

/-- **The frame sizes**: the compiler's (`fsAt`), `main`'s holding the jump table, at least the
header. -/
noncomputable def fs (f : String) : ℕ :=
  match coreProgram.indexOf? f with
  | some 0 => mainFrame
  | some i => max 2 (fsAt (i + 1))
  | none => 2

/-- The frame size of compiled function `j`, `fs` by index. -/
def fsN (j : ℕ) : ℕ := bif Nat.beq j 1 then mainFrame else max 2 (fsAt j)

/-! ## The cells of a frame -/

/-- A fixed cell's word in the frame at `fp`. -/
def PC.word (fp : ℕ) : PC → E
  | .k k0 k1 k2 => OInstr.imm k0 k1 k2
  | .fpg e => ofK (gpow (fp + e))

/-- The cells of values. -/
noncomputable def valE (f : String) (σ : Val) (vs : List V) : List (ℕ × E) := vs.map fun v => (cert f v, σ v)

/-- The cells of the frame runs of a path. -/
noncomputable def runsE (f : String) (σ : Val) (es : List Ev) : List (ℕ × E) :=
  es.flatMap fun
    | .atom (.frameAddr _ (r :: rs)) => (r :: rs).mapIdx fun k v => (cert f r + k, σ v)
    | _ => []

/-- The values a path names: the parameters, the events' values, the returned values. -/
def namedOf (params : List V) (es : List Ev) (vs : List V) : List V :=
  params ++ es.flatMap Ev.uses ++ vs

/-- The values an instance returns along its path. -/
noncomputable def pathRets (t : Tree) : List V :=
  match coreProgram.find? t.name with
  | some fn => match walk t.val fn.body with
    | .ret _ vs => vs
    | _ => []
  | none => []

/-- The call site of a call, by its values. -/
noncomputable def siteOf (j : ℕ) (c : Call) : Option Site :=
  (plumbOf j).sites.find? fun s => s.args == c.args.map (·.idx) && s.rets == c.rets.map (·.idx)

/-- The entry pc of a function, by name. -/
noncomputable def entryOf (f : String) : ℕ :=
  match idxOf f with
  | some j => (fnOf j).entry
  | none => 0

/-- The callee frame pointer and dispatch target of each call on a path. -/
noncomputable def siteE (j : ℕ) (I : Inst) (es : List Ev) : List (ℕ × E) :=
  ((calls es).zip I.kidFps).flatMap fun p => match siteOf j p.1 with
    | some s => (s.q, ofK (gpow p.2)) ::
        (if s.tgt = 0 then [] else [(s.tgt, ofK (gpow (entryOf p.1.f)))])
    | none => []

open Classical in
/-- The jump table's word at the slot of selector `x`, `base` the table's first slot. -/
noncomputable def armWord (σ : Val) (x base : ℕ) : E :=
  if h : ∃ i, i < 2 ^ 64 ∧ σ (V.n x) = ofK (gpow i) then
    ((tableCells.find? fun q => q.1 == base + Nat.find h).map Prod.snd).getD 0
  else 0

/-- One cell per offset, the first, within `[2, n)`. -/
def dedupC : List (ℕ × E) → List (ℕ × E)
  | [] => []
  | q :: qs => q :: (dedupC qs).filter fun q' => !(q'.1 == q.1)

/-- A frame's cells from a list of candidates. -/
def frameE (n : ℕ) (L : List (ℕ × E)) : List (ℕ × E) :=
  dedupC (L.filter fun q => Nat.ble 2 q.1 && Nat.blt q.1 n)

/-- The candidate cells of an instance of function `j` that runs. -/
noncomputable def nodeE (j : ℕ) (f : String) (σ : Val) (I : Inst) : List (ℕ × E) :=
  valE f σ (coreProgram.temps f) ++ runsE f σ (I.t.events coreProgram) ++
    (plumbOf j).stat.map (fun q => (q.1, q.2.word I.fp)) ++
    valE f σ (namedOf (coreOf j).params (I.t.events coreProgram) (pathRets I.t)) ++
    siteE j I (I.t.events coreProgram) ++
    (plumbOf j).arms.map (fun a => (a.2.1, armWord σ a.1 a.2.2)) ++
    (if j = 1 then tableCells else [])

/-- The candidate cells of a phantom of function `j`: what its caller writes. -/
noncomputable def phantomE (j : ℕ) (f : String) (σ : Val) (I : Inst) : List (ℕ × E) :=
  valE f σ (coreOf j).params ++ (certOf j).facts.env.map fun p => (p.1, ofK (gpow I.fp))

/-- **The cells of each frame of the honest memory.** -/
noncomputable def C (I : Inst) : List (ℕ × E) :=
  match I.t, idxOf I.t.name with
  | .node f σ _ _, some j => frameE (fs f) (nodeE j f σ I)
  | .phantom f σ, some j => frameE (fs f) (phantomE j f σ I)
  | _, _ => []

/-- **The header of each callee**: the return pc of its call site and the caller's frame, or the
caller's header for a loop's tail call. -/
noncomputable def H (I : Inst) (i : ℕ) : E × E :=
  match I.t, idxOf I.t.name with
  | .node f _ _ _, some j =>
    match (calls (I.t.events coreProgram))[i]? with
    | some c =>
      if coreProgram.loop f = true ∧ i + 1 = (calls (I.t.events coreProgram)).length then I.hdr
      else match siteOf j c with
        | some s => (ofK (gpow s.r), ofK (gpow I.fp))
        | none => (0, 0)
    | none => (0, 0)
  | _, _ => (0, 0)

/-! ## Instruction counts -/

/-- An opcode's position in `Opcode`'s order. -/
def opIdx : Opcode → ℕ
  | .xor => 0
  | .mulNative => 1
  | .setConstant => 2
  | .deref => 3
  | .jump => 4
  | .blake2s => 5

/-- The most instructions of opcode `op` one path through function `f`'s code runs (the
certificate's, which the completeness check confirms). -/
noncomputable def pathMax (f : String) (op : Opcode) : ℕ :=
  match idxOf f with
  | some j => (plumbOf j).pmax.getD (opIdx op) 0
  | none => 0

/-! ## The counts of a path

A `match` whose arms are counted separately (`Data.cplArms`) adds the count of the arm its
selector picks; the rest of a path is counted by the most any path runs (`pathMax`). -/

/-- The arms' counts of the `match` on `x`, if counted separately. -/
def armRaw (acs : List (ℕ × List (List ℕ))) (x : ℕ) : Option (List (List ℕ)) :=
  (acs.find? fun p ↦ Nat.beq p.1 x).map (·.2)

mutual
/-- The separately counted arms a statement's path passes, under `σ`. -/
noncomputable def cost1 (acs : List (ℕ × List (List ℕ))) (σ : Val) : Stmt → Opcode → ℕ
  | .ite c z n => if σ c = 0 then costW acs σ z else costW acs σ n
  | .match_ x arms => costArms acs σ x (armRaw acs x.idx) 0 arms
  | _ => 0

/-- The separately counted arms a block's path passes, under `σ`. -/
noncomputable def costW (acs : List (ℕ × List (List ℕ))) (σ : Val) : List Stmt → Opcode → ℕ
  | [] => 0
  | s :: ss => cost1 acs σ s + costW acs σ ss

/-- The arm `σ` picks, from arm `k` on (`walkArms`), its count if counted separately. -/
noncomputable def costArms (acs : List (ℕ × List (List ℕ))) (σ : Val) (x : V)
    (key : Option (List (List ℕ))) : ℕ → List (List Stmt) → Opcode → ℕ
  | _, [] => 0
  | k, a :: as => if σ x = ofK (gpow k) then
      (fun op ↦ match key with
        | some cs => (nth cs k []).getD (opIdx op) 0
        | none => 0) + costW acs σ a
    else costArms acs σ x key (k + 1) as
end

/-- **The count of function `j`'s path under `σ`**: the most a path runs, and the separately
counted arms it passes. -/
noncomputable def pathCount (j : ℕ) (σ : Val) (op : Opcode) : ℕ :=
  (plumbOf j).pmax.getD (opIdx op) 0 + costW (nth Data.cplArms j []) σ (coreOf j).body op

/-- `pathCount`, by function name. -/
noncomputable def pathCountN (f : String) (σ : Val) (op : Opcode) : ℕ :=
  match idxOf f with
  | some j => pathCount j σ op
  | none => 0

mutual
/-- The weight of a call tree, each instance weighing `ω f σ` by its function and valuation. -/
def weightV (ω : String → Val → ℕ) : Tree → ℕ
  | .node f σ _ kids => ω f σ + weightVKids ω kids
  | .phantom .. => 0

/-- The weight of a list of call trees. -/
def weightVKids (ω : String → Val → ℕ) : List Tree → ℕ
  | [] => 0
  | k :: ks => weightV ω k + weightVKids ω ks
end

/-- The jump table's `SET`s, run before `main`. -/
def jtSets (op : Opcode) : ℕ := if op = .setConstant then 4478 else 0

/-- **The instructions of opcode `op` a run on the honest memory of `T` executes at most**: its
path's count, per instance that runs, and the jump table. -/
noncomputable def cnt (T : Tree) (op : Opcode) : ℕ := weightV (fun f σ ↦ pathCountN f σ op) T + jtSets op

end
end LeanVM.Guest.B2C
