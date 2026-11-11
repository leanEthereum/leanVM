/-
  LeanVM.Guest.Complete

  The completeness of the aggregation guest, stated, and assembled from its pieces: `NodeRelation`
  within the deployed limits, the caps agreeing, no zero challenge where the guest divides, and
  the node within a budget give a valid execution of the guest that fits the verifier.
-/

module

public import LeanVM.Protocol.LeanVM
public import LeanVM.Guest.Start
public import LeanVM.Guest.Limits
public import LeanVM.Guest.CoreData
public import LeanVM.Guest.ChildShape
public import LeanVM.Guest.Pad
public import Statement.LeanVmGuest
public import LeanVM.Guest.AcceptableChild

/-!
# Completeness

**The statement** (`GuestComplete budget`): for every seed, statement `s` and witness `w` with
`NodeRelation bytecode seed s w`, within the deployed limits (`GuestLimits`), every child one the guest
accepts (`ChildrenOk`: its openings agreeing in the guest's Merkle caps, no zero challenge where
the guest divides, ...) and the node within the budget (`budget s w ≤ 2^28`),
there is a valid execution of the guest on the statement's digest whose committed size is at most
`2^28`, within the `2^30` the verifier admits; the guest has an opening arm for every stack log
the verifier admits of an execution (`20` to `30`), so no lower bound is needed (the memory is
still padded to `2^20` words at least, `padLog`, `Guest/Pad.lean`). The three hypotheses are
`Guest/Limits.lean`'s; the budget
is a seventh limit, the size of the run, which the others do not bound. The deployed budget is
linear in the node's work (`Budget`: the words a run allocates and the instructions of each
opcode it executes, each a constant plus a coefficient per declared claim, coverage slot, raw
signature or blob, blob row, child and child's claim, and a function of each child's announced
stack log and rate, the opening arm its `verify_sub` takes, `work s w`), at
`Execution.committedSize`'s formula (`Budget.size`), so the final statement is
`GuestCompleteWithin b`.

**The pieces** (`CompletePieces`, `guest_complete_of`). The memory is the honest memory of a call
tree (`Memory.honest`) at the certificates' frame sizes `fs`, headers `H` and cells `C`, the tree
placed at the certificates' cells `cert` (`Memory.HonestAt`):

* `honest`: under the hypotheses, a tree of `main`, valid on some memory, satisfying
  `Memory.HonestAt` with the statement's digest as `main`'s header, of cost within the budget
  (B1's completeness of `main` and its callees, at the bump allocator's `HeapBuf` pointers, and
  the discharge of `Honest`);
* `table`: `main`'s cells hold its jump table (`Memory.tableCells`);
* `b2`: on the honest memory, `main` runs from its entry at `fp = 1` to the halting registers
  (the checker's completeness, `exec_complete` and the certificates);
* `size`: that run's committed size is at most the tree's cost.

`CompletePiecesWithin` splits the size at a call tree's instruction counts `cnt T op`, and
`guest_complete_within` gives `GuestCompleteWithin b`. `aggregate_complete_of`
(`LeanVM/Guest/EndRpm.lean`) composes with the protocol's completeness in the random-permutation
model: the honest prover's proof of that execution is rejected with probability at most the bound
of `Completeness`.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open scoped ENNReal

@[expose] public section

/-- `main`'s header: the public input's two words. -/
abbrev hdrOf (d : Digest) : E × E := ((publicInputOf d).word0, (publicInputOf d).word1)

/-! ## The budget -/

/-- A bound linear in the work: a constant and a coefficient per unit, and a charge per child by
its announced stack log and rate. -/
structure Linear where
  base : ℕ
  declared : ℕ
  coverage : ℕ
  rawXmss : ℕ
  rawSphincs : ℕ
  rawDa : ℕ
  rawDaRows : ℕ
  rawDaPad : ℕ
  children : ℕ
  childClaims : ℕ
  childShape : ℕ → ℕ → ℕ

/-- The bound at the work `u`. -/
def Linear.eval (l : Linear) (u : Work) : ℕ :=
  l.base + l.declared * u.declared + l.coverage * u.coverage + l.rawXmss * u.rawXmss +
    l.rawSphincs * u.rawSphincs + l.rawDa * u.rawDa + l.rawDaRows * u.rawDaRows +
    l.rawDaPad * u.rawDaPad + l.children * u.children + l.childClaims * u.childClaims +
    (u.childShapes.map fun p ↦ l.childShape p.1 p.2).sum

/-- **A size budget**: bounds on the words a run allocates and on the instructions of each opcode
it executes. -/
structure Budget where
  /-- The words allocated. -/
  words : Linear
  /-- The instructions of each opcode executed. -/
  instrs : Opcode → Linear

/-- The memory's log-size for a run allocating `words` words, padded to at least `2^20` words so
that the committed size is at least `2^22` (`Guest/Pad.lean`). -/
def padLog (words : ℕ) : ℕ := max (Memory.logMem words) 20

/-- `Execution.committedSize`'s formula for a run of the guest allocating `words` words, on
`2^padLog words` of memory, and executing `instrs op` instructions of each opcode `op`. -/
def sizeOf (words : ℕ) (instrs : Opcode → ℕ) : ℕ :=
  let height (op : Opcode) : ℕ := 2 ^ Nat.clog 2 (instrs op)
  let keccakHeight : ℕ := 2 ^ max (Nat.clog 2 (instrs .keccak)) 9
  4 * 2 ^ padLog words + 2 ^ guestProgram.logSize +
    15 * height .xor + 15 * height .mulNative + 8 * height .setConstant + 15 * height .deref +
    14 * height .jump + 28 * keccakHeight + 2 ^ 6 * keccakHeight

/-- The committed size of a run within the budget at the work `u`. -/
def Budget.size (b : Budget) (u : Work) : ℕ := sizeOf (b.words.eval u) fun op ↦ (b.instrs op).eval u

theorem logMem_mono {m n : ℕ} (h : m ≤ n) : Memory.logMem m ≤ Memory.logMem n :=
  max_le_max le_rfl (Nat.clog_mono_right 2 h)

theorem sizeOf_mono {w w' : ℕ} {i i' : Opcode → ℕ} (hw : w ≤ w') (hi : ∀ op, i op ≤ i' op) :
    sizeOf w i ≤ sizeOf w' i' := by
  have hh : ∀ op, 2 ^ Nat.clog 2 (i op) ≤ 2 ^ Nat.clog 2 (i' op) := fun op ↦
    Nat.pow_le_pow_right (by norm_num) (Nat.clog_mono_right 2 (hi op))
  have hk : 2 ^ max (Nat.clog 2 (i .keccak)) 9 ≤ 2 ^ max (Nat.clog 2 (i' .keccak)) 9 :=
    Nat.pow_le_pow_right (by norm_num) (max_le_max (Nat.clog_mono_right 2 (hi .keccak)) le_rfl)
  have hm : 2 ^ padLog w ≤ 2 ^ padLog w' :=
    Nat.pow_le_pow_right (by norm_num) (max_le_max (logMem_mono hw) le_rfl)
  dsimp only [sizeOf]
  have := hh .xor; have := hh .mulNative; have := hh .setConstant; have := hh .deref
  have := hh .jump
  omega

/-- **A budget's words within its size**: the memory alone commits `4` words per word. -/
theorem words_le_of_size {b : Budget} {u : Work} (h : b.size u ≤ 2 ^ 28) :
    b.words.eval u ≤ 2 ^ 26 := by
  have hm := Memory.le_two_pow_logMem (b.words.eval u)
  have hp : 2 ^ Memory.logMem (b.words.eval u) ≤ 2 ^ padLog (b.words.eval u) :=
    Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have : 4 * 2 ^ padLog (b.words.eval u) ≤ b.size u := by
    unfold Budget.size; dsimp only [sizeOf]; simp only [Nat.add_assoc]; exact Nat.le_add_right _ _
  omega

/-- The committed size of a run on `2^logMem n` words, padded to `2^padLog n`, is `sizeOf n` at
its counts. -/
theorem committedSize_pad_eq {n : ℕ} (L : MemoryImage (Memory.logMem n)) (steps : ℕ)
    (hc : ∀ op, ((⟨_, L, steps⟩ : Execution guestProgram).pad (padLog n)).opcodeCount op =
      (⟨_, L, steps⟩ : Execution guestProgram).opcodeCount op) :
    ((⟨_, L, steps⟩ : Execution guestProgram).pad (padLog n)).committedSize =
      sizeOf n (⟨_, L, steps⟩ : Execution guestProgram).opcodeCount := by
  have h := committedSize_pad (⟨_, L, steps⟩ : Execution guestProgram) (padLog n) hc
  have h2 : (⟨_, L, steps⟩ : Execution guestProgram).committedSize + 4 * 2 ^ padLog n =
      sizeOf n (⟨_, L, steps⟩ : Execution guestProgram).opcodeCount + 4 * 2 ^ Memory.logMem n := by
    unfold Semantics.Execution.committedSize sizeOf
    simp only
    omega
  simp only at h
  omega

/-! ## The statement -/

/-- **Completeness**, the statement: a witness of `NodeRelation` within the deployed limits, its
children's openings agreeing in the caps, no zero challenge where the guest divides, and the node
within the budget give a valid execution of the guest on the statement's digest within the
verifier's committed size. -/
def GuestComplete (budget : NodeStatement → NodeWitness → ℕ) : Prop :=
  ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w → budget s w ≤ 2 ^ 28 →
    ∃ t : Execution guestProgram, ValidExecution guestProgram (publicInputOf (statementDigest seed s)) t ∧
      t.committedSize ≤ 2 ^ 28

/-- **Completeness within a linear budget**, the final statement's form. -/
abbrev GuestCompleteWithin (b : Budget) : Prop := GuestComplete fun s w ↦ b.size (work s w)

/-! ## The pieces -/

/-- **What completeness rests on**, for the certificates' frame sizes `fs`, headers `H`, cells `C`
and value cells `cert`, a cost of a call tree and a budget of a node. -/
structure CompletePieces (fs : String → ℕ) (H : Memory.Inst → ℕ → E × E)
    (C : Memory.Inst → List (ℕ × E)) (cert : String → V → ℕ) (cost : Memory.Tree → ℕ)
    (budget : NodeStatement → NodeWitness → ℕ) : Prop where
  /-- B1 (`main`'s completeness at the bump allocator's `HeapBuf` pointers), `Program.Rel.tree`
  and the discharge of `Honest`: under the hypotheses, a call tree of `main`, honest with the
  statement's digest as `main`'s header, of cost within the node's budget. -/
  honest : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w → budget s w ≤ 2 ^ 28 →
    ∃ (rd : Reader) (T : Memory.Tree), T.name = "main" ∧
      Memory.HonestAt coreProgram fs H C (hdrOf (statementDigest seed s)) T cert rd [] [] ∧
      cost T ≤ budget s w
  /-- `main`'s cells hold its jump table. -/
  table : ∀ (I : Memory.Inst) σ bufs kids, I.t = .node "main" σ bufs kids → Memory.tableCells ⊆ C I
  /-- B2 (the checker's completeness, the certificates): on the honest memory, `main` runs from
  its entry at `fp = 1` to the halting registers. -/
  b2 : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    Memory.HonestAt coreProgram fs H C hdr T cert rd [] [] →
      Reach guestProgram (Memory.honest coreProgram fs H C hdr T) ⟨addressOfIndex mainEntry, 1⟩ (Registers.final guestProgram)
  /-- B2 (counting): a halting run on the honest memory, padded to `2^padLog` words, commits at
  most the tree's cost. -/
  size : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    Memory.HonestAt coreProgram fs H C hdr T cert rd [] [] → ∀ n,
      run guestProgram (Memory.honest coreProgram fs H C hdr T) n Registers.initial = some (Registers.final guestProgram) →
        ((⟨_, Memory.honest coreProgram fs H C hdr T, n⟩ : Execution guestProgram).pad
          (padLog (T.total fs))).committedSize ≤ cost T

/-- **What completeness within the budget `b` rests on**: `CompletePieces` with the size split
at the instruction counts `cnt T op` of a call tree, the run's against the tree's and the tree's
against the budget. -/
structure CompletePiecesWithin (fs : String → ℕ) (H : Memory.Inst → ℕ → E × E)
    (C : Memory.Inst → List (ℕ × E)) (cert : String → V → ℕ) (cnt : Memory.Tree → Opcode → ℕ)
    (b : Budget) : Prop where
  /-- As `CompletePieces.honest`, the tree within the budget's words and instruction counts. -/
  honest : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w → b.size (work s w) ≤ 2 ^ 28 →
    ∃ (rd : Reader) (T : Memory.Tree), T.name = "main" ∧
      Memory.HonestAt coreProgram fs H C (hdrOf (statementDigest seed s)) T cert rd [] [] ∧
      T.total fs ≤ b.words.eval (work s w) ∧ ∀ op, cnt T op ≤ (b.instrs op).eval (work s w)
  /-- `main`'s cells hold its jump table. -/
  table : ∀ (I : Memory.Inst) σ bufs kids, I.t = .node "main" σ bufs kids → Memory.tableCells ⊆ C I
  /-- As `CompletePieces.b2`. -/
  b2 : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    Memory.HonestAt coreProgram fs H C hdr T cert rd [] [] →
      Reach guestProgram (Memory.honest coreProgram fs H C hdr T) ⟨addressOfIndex mainEntry, 1⟩ (Registers.final guestProgram)
  /-- B2 (counting): a halting run on the honest memory executes at most the tree's
  instructions of each opcode. -/
  count : ∀ hdr (rd : Reader) (T : Memory.Tree), T.name = "main" →
    Memory.HonestAt coreProgram fs H C hdr T cert rd [] [] → ∀ n,
      run guestProgram (Memory.honest coreProgram fs H C hdr T) n Registers.initial = some (Registers.final guestProgram) →
        ∀ op, (⟨_, Memory.honest coreProgram fs H C hdr T, n⟩ : Execution guestProgram).opcodeCount op ≤ cnt T op

theorem CompletePiecesWithin.pieces {fs : String → ℕ} {H : Memory.Inst → ℕ → E × E}
    {C : Memory.Inst → List (ℕ × E)} {cert : String → V → ℕ} {cnt : Memory.Tree → Opcode → ℕ}
    {b : Budget} (h : CompletePiecesWithin fs H C cert cnt b) :
    CompletePieces fs H C cert (fun T ↦ sizeOf (T.total fs) (cnt T)) fun s w ↦ b.size (work s w) where
  honest seed s w hrel hlim hok hb := by
    obtain ⟨rd, T, hname, hH, hw, hc⟩ := h.honest seed s w hrel hlim hok hb
    exact ⟨rd, T, hname, hH, sizeOf_mono hw hc⟩
  table := h.table
  b2 := h.b2
  size hdr rd T hname hH n hrun := by
    have h32 := hH.toHonest.logMem_le
    have hc := (run_ext (readExt_padImage (le_max_left _ 20)
      (show padLog (T.total fs) < 64 from
        max_lt (lt_of_le_of_lt h32 (by unfold maxLogMem; omega)) (by omega))
      (Memory.honest coreProgram fs H C hdr T)) n _ _ hrun).2
    rw [committedSize_pad_eq (n := T.total fs) (Memory.honest coreProgram fs H C hdr T) n hc]
    exact sizeOf_mono le_rfl (h.count hdr rd T hname hH n hrun)

/-- The honest memory holds the jump table. -/
theorem jumpTables_honest {fs : String → ℕ} {H : Memory.Inst → ℕ → E × E}
    {C : Memory.Inst → List (ℕ × E)} {hdr : E × E} {T : Memory.Tree} {rd : Reader}
    (hH : Memory.Honest coreProgram fs H C hdr T rd [] []) (hname : T.name = "main")
    (htable : ∀ (I : Memory.Inst) σ bufs kids, I.t = .node "main" σ bufs kids →
      Memory.tableCells ⊆ C I) :
    JumpTables (Memory.honest coreProgram fs H C hdr T) := by
  intro q hq
  obtain ⟨I, hI, hIt, hfp, -⟩ := Memory.root_inst (fs := fs) (H := H) (hdr := hdr) (T := T)
  have hC : (q.1, q.2) ∈ C I := by
    have hv := hH.valid
    cases T with
    | node f σ bufs kids =>
      simp only [Memory.Tree.name] at hname
      exact htable I σ bufs kids (by rw [hIt, hname]) hq
    | phantom => exact (hv : False).elim
  have := hH.read_C hI hC
  rwa [hfp, addressOfIndex, pow_zero, one_mul] at this

/-- **Completeness, from its pieces.** -/
theorem guest_complete_of {fs : String → ℕ} {H : Memory.Inst → ℕ → E × E}
    {C : Memory.Inst → List (ℕ × E)} {cert : String → V → ℕ} {cost : Memory.Tree → ℕ}
    {budget : NodeStatement → NodeWitness → ℕ} (h : CompletePieces fs H C cert cost budget) :
    GuestComplete budget := fun seed s w hrel hlim hok hbudget ↦ by
  obtain ⟨rd, T, hname, hH, hcost⟩ := h.honest seed s w hrel hlim hok hbudget
  have hb := hH.toHonest.publicBoundary (prog := guestProgram)
  have hreach := (reach_jumpTables (jumpTables_honest hH.toHonest hname h.table)).trans
    (h.b2 _ rd T hname hH)
  obtain ⟨n, hv⟩ := validExecution_of_reach hb hreach
  have h32 := hH.toHonest.logMem_le
  obtain ⟨hv', -⟩ := validExecution_pad hv (le_max_left _ 20)
    (show padLog (T.total fs) ≤ maxLogMem from max_le h32 (by unfold maxLogMem; omega))
  exact ⟨_, hv', (h.size _ rd T hname hH n hv.2).trans (hcost.trans hbudget)⟩

/-- **Completeness within the budget `b`, from its pieces.** -/
theorem guest_complete_within {fs : String → ℕ} {H : Memory.Inst → ℕ → E × E}
    {C : Memory.Inst → List (ℕ × E)} {cert : String → V → ℕ} {cnt : Memory.Tree → Opcode → ℕ}
    {b : Budget} (h : CompletePiecesWithin fs H C cert cnt b) : GuestCompleteWithin b :=
  guest_complete_of h.pieces

end
end LeanVM.Guest.End
