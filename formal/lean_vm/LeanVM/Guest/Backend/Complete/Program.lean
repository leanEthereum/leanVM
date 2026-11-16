/-
  LeanVM.Guest.Backend.Complete.Program

  Whole-program completeness of the back end, for every program: the honest memory at the back
  end's own frame sizes, cells, frame words and callee headers, the budget summed over the call
  tree from the back end's own path maxima, and the statement `ProgramCompleteStmt`.
-/

module

public import LeanVM.Guest.Backend.Complete.Spec
public import LeanVM.Guest.Memory

/-!
# Whole-program completeness

`FnCompleteStmt`, `FrameConsistentStmt` and `PathOpsStmt` speak of one function at a time. This
file states their composition over a whole run, for any compiled program `W`.

**The run of the core IR** is a call tree `T` of `main` in the form `Memory.HonestAt` takes: valid
on some reader, placed by the bump allocator from word `0`, its `HeapBuf`s those of its paths, its
`frameAddr`s at the back end's cells, at most `2^30` words.

**The honest memory** is `Memory.honest` at the back end's own data:
* the frame size of `f` is its frame in the layout, `World.fsB` (`main`'s with the jump tables);
* the cell of value `v` of `f` is where the back end places it, `World.cellB`;
* an instance of `f` that runs holds in its frame the words of a frame family as
  `FrameConsistentStmt` gives one at its frame, callee frames and header (`World.famB`, chosen once
  for every memory), and `main`'s frame the jump tables' words past its own cells
  (`World.cellsB`); a phantom holds what its caller writes: its arguments and a registered loop
  helper's own pointer;
* the header of a callee is the frame family's (`World.hdrB`).

**The budget** (`World.progCost`): each instance that runs costs its function's placed path
maxima `pmaxP` and the separately counted arms its path passes (`armsCost`), summed over the call
tree. Which functions count their arms separately is a free choice `keyed`; a choice whose arms
are not on distinct selectors is ignored (`World.keyedB`). A function whose placed body does not
pair up with its core body (`alL`; placement is expected always to pair them, `PlaceAlignedStmt`)
costs its path's instructions `pathOps` instead, so that the statement asks no alignment.

**The statement** (`ProgramCompleteStmt`): for a compiled program whose every function passes the
decidable per-function conditions, on the honest memory of every such run, the emitted bytecode
runs from `main`'s entry at frame `g^0` to the final registers within the budget.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

end
end LeanVM.Guest.Backend.Complete

namespace LeanVM.Guest.Backend.World

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Backend.Complete

@[expose] public section

/-! ## The back end's data of a function -/

variable {κ₀ : ℕ} (W : World κ₀)

/-- The traced function named `f` and its placement. -/
def fnOf (f : String) : Option (TracedFn × Placed) :=
  match W.p.find? (·.core.name == f), W.placed.find? (·.fn.name == f) with
  | some tf, some pf => some (tf, pf)
  | _, _ => none

/-- **The back end's frame size** of function `f`: its frame in the layout. -/
def fsB (f : String) : ℕ := W.layout.frame.getD f 0

/-- **The back end's cell** of value `v` of function `f`. -/
def cellB (f : String) (v : V) : ℕ := (cellP (W.locs f) v).getD 0

end
end LeanVM.Guest.Backend.World

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **What `FrameConsistentStmt` gives** function `tf` placed as `pf` at frame `fp`, callee frames
`kfps` and header `hdr`: a frame family `FS`. -/
def FSOk {κ₀ : ℕ} (W : World κ₀) (tf : TracedFn) (pf : Placed) (fp : ℕ) (kfps : List ℕ)
    (hdr : E × E) (FS : Val → FrameSpec) : Prop :=
  FrameCongr tf pf FS ∧
    ∀ (σ : Val) (es : List Ev) (vs : List V), walk σ tf.core.body = .ret es vs →
      (∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + (cellP pf.locs q.2).getD 0))) →
      (∀ rd : Reader, (∀ e ∈ es, e.Holds rd σ) →
        FrameClauses (loopTable W.p) tf pf fp σ es vs hdr (FS σ)) ∧
      ∀ {κ : ℕ} (L : MemoryImage κ) (ck : List (Opcode → ℕ)),
        FrameOK L (loopTable W.p) tf pf.fn.frameSize fp (FS σ) σ es kfps hdr →
        (∀ e ∈ es, e.Holds L.read σ) → JTHolds L W.layout W.slots →
        World.KidsRunP (World.withL W L) σ es kfps ck →
        World.CplBody (World.withL W L) tf pf fp σ (kfps.zip ck)

/-- One cell per offset, the first. -/
def dedupB : List (ℕ × E) → List (ℕ × E)
  | [] => []
  | q :: qs => q :: (dedupB qs).filter fun q' => !(q'.1 == q.1)

/-- A frame's cells from candidates: those in `[2, n)`, one per offset, the first. -/
def frameB (n : ℕ) (L : List (ℕ × E)) : List (ℕ × E) :=
  dedupB (L.filter fun q => Nat.ble 2 q.1 && Nat.blt q.1 n)

mutual
/-- A call tree's cost, each instance that runs costing `ω f σ`. -/
def treeCost (ω : String → Val → ℕ) : Tree → ℕ
  | .node f σ _ kids => ω f σ + treeCostKids ω kids
  | .phantom .. => 0

/-- The cost of a list of call trees. -/
def treeCostKids (ω : String → Val → ℕ) : List Tree → ℕ
  | [] => 0
  | k :: ks => treeCost ω k + treeCostKids ω ks
end

end
end LeanVM.Guest.Backend.Complete

namespace LeanVM.Guest.Backend.World

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Backend.Complete

@[expose] public section

variable {κ₀ : ℕ} (W : World κ₀)

open Classical in
/-- **The frame family** of function `tf` placed as `pf` at frame `fp`, callee frames `kfps`,
header `hdr`: one `FSOk` admits, chosen once for every memory. -/
noncomputable def famB (tf : TracedFn) (pf : Placed) (fp : ℕ) (kfps : List ℕ) (hdr : E × E) :
    Val → FrameSpec :=
  if h : ∃ FS, FSOk W tf pf fp kfps hdr FS then Classical.choose h
  else fun _ => ⟨fun _ => 0, fun _ => (0, 0)⟩

/-- The frame words of an instance that runs, with its function and placement. -/
noncomputable def wordsB (I : Inst) : Option (TracedFn × Placed × FrameSpec) :=
  match I.t with
  | .node f σ _ _ => (W.fnOf f).map fun p => (p.1, p.2, W.famB p.1 p.2 I.fp I.kidFps I.hdr σ)
  | .phantom .. => none

open Classical in
/-- **The header of callee `k`** of an instance: the frame family's, if it is of `K`. -/
noncomputable def hdrB (I : Inst) (k : ℕ) : E × E :=
  match W.wordsB I with
  | some (_, _, FS) => if IsInK (FS.kh k).1 ∧ IsInK (FS.kh k).2 then FS.kh k else (0, 0)
  | none => (0, 0)

/-- The jump tables' cells, in `main`'s frame from `tablesBase`. -/
def tableB : List (ℕ × E) :=
  W.slots.toList.zipIdx.filterMap fun q =>
    (SlotWord W.layout q.1).map fun w => (W.layout.tablesBase + q.2, w)

/-- **The cells of each frame of the honest memory**: an instance that runs, its frame family's
words over its placed frame (`main`: then the jump tables); a phantom, its arguments and a
registered loop helper's own pointer. -/
noncomputable def cellsB (I : Inst) : List (ℕ × E) :=
  match I.t with
  | .node f σ _ _ =>
      match W.fnOf f with
      | some (tf, pf) =>
          frameB (W.fsB f) ((List.range pf.fn.frameSize).map
              (fun n => (n, (W.famB tf pf I.fp I.kidFps I.hdr σ).Ψ n)) ++
            (if f = "main" then W.tableB else []))
      | none => []
  | .phantom f σ =>
      match W.fnOf f with
      | some (tf, _) =>
          frameB (W.fsB f) (tf.core.params.mapIdx (fun k v => (2 + k, σ v)) ++
            (if ((loopTable W.p)[f]?).any (·.registered) then
              [(2 + tf.core.params.length, ofK (addressOfIndex I.fp))] else []))
      | none => []

/-- **The honest memory** of the run `T` with `main`'s header `hdr`, at the back end's frame
sizes, headers and cells. -/
noncomputable abbrev honestB (hdr : E × E) (T : Tree) : MemoryImage (logMem (T.total W.fsB)) :=
  honest W.core W.fsB W.hdrB W.cellsB hdr T

/-! ## The budget -/

/-- Whether function `tf` placed as `pf` counts its arms separately: `keyed` asks it and its
separately counted stages are on distinct selectors. -/
def keyedB (keyed : String → Bool) (tf : TracedFn) (pf : Placed) : Bool :=
  keyed tf.core.name && decide (((armsP true tf pf).map (·.1)).Nodup)

/-- **What an instance of `f` with valuation `σ` costs** of opcode `op`, besides its callees: its
placed path maxima and the separately counted arms its path passes; its path's instructions if
its placed body does not pair up with its core body. -/
noncomputable def fnCost (keyed : String → Bool) (f : String) (σ : Val) (op : Opcode) : ℕ :=
  match W.fnOf f with
  | some (tf, pf) =>
      if alL pf.fn.body tf.core.body then
        pmaxP (keyedB keyed tf pf) pf op +
          armsCost (armsP (keyedB keyed tf pf) tf pf) σ tf.core.body op
      else pathOps σ tf pf op
  | none => 0

/-- **The budget** of opcode `op` for the run `T`. -/
noncomputable def progCost (keyed : String → Bool) (T : Tree) (op : Opcode) : ℕ :=
  treeCost (fun f σ => W.fnCost keyed f σ op) T

end
end LeanVM.Guest.Backend.World

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The statement -/

/-- **The decidable per-function conditions**: scoped, no direct self call, a loop helper exactly
when named one, and its placement's temporaries apart. -/
structure FnConds {κ₀ : ℕ} (W : World κ₀) (tf : TracedFn) : Prop where
  isScoped : Scoped tf
  noSelf : NoSelfCall tf
  loopNamed : isLoopName tf.core.name = tf.core.loop
  tmps : ∀ pf, World.PlacedAs W tf pf → TmpsApart tf pf

/-- **Whole-program completeness**: for a compiled program whose every function passes the
per-function conditions, on the honest memory of every run `T` of `main` at the back end's frame
sizes and cells, the emitted bytecode runs from `main`'s entry at frame `g^0` to the final
registers, executing at most the budget of each opcode. -/
def ProgramCompleteStmt : Prop :=
  ∀ {κ₀ : ℕ} (W : World κ₀), W.Compiled → (∀ tf ∈ W.p, FnConds W tf) →
    ∀ (keyed : String → Bool) (hdr : E × E) (rd : Reader) (T : Tree), T.name = "main" →
      HonestAt W.core W.fsB W.hdrB W.cellsB hdr T W.cellB rd [] [] →
      ∃ c : Opcode → ℕ,
        B2C.RunC W.prog (W.honestB hdr T) ⟨addressOfIndex (W.ent "main"), 1⟩
          (Registers.final W.prog) c ∧
        ∀ op, c op ≤ W.progCost keyed T op

end
end LeanVM.Guest.Backend.Complete
