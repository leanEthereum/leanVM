/-
  LeanVM.Guest.B2C.CplSpec

  What B2's completeness check of one compiled function (`Cpl.lean`) reads of the memory and gives
  of a run.
-/

module

public import LeanVM.Guest.B2C.Cpl
public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.B2C.Count

/-!
# What the completeness check reads and gives

`FrameHolds L j fp σ es vs kfps hdr` is what the check reads of the memory for one instance of
function `j` at frame `fp` on the path `es` of its valuation `σ` (`walk σ (coreOf j).body =
.ret es vs`), its callees' frames at `kfps` and its header `hdr`: the header, every value the
path names and every range check temporary at its certificate cell, the fixed cells
(`Plumb.stat`), the frame addresses, the table jumps' targets, each call site's callee frame
pointer and dispatch target, and each callee frame's header, arguments, returns and self frame
pointer cells. `KidsRun` is the callees' runs.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

/-! ## What the check reads of the memory -/

/-- The self frame pointer cells of a function, by name. -/
noncomputable def selfCells (f : String) : List ℕ :=
  match idxOf f with
  | some j => (certOf j).facts.env.map (·.1)
  | none => []

/-- The header of the callee of the `i`-th call on a path `es` of function `j` at `fp` with
header `hdr` (`H`'s): the caller's own for a loop's tail call, its last; else its call site's
return pc and the caller's frame. -/
noncomputable def kidHdr (j fp : ℕ) (hdr : E × E) (es : List Ev) (i : ℕ) : E × E :=
  match (calls es)[i]? with
  | some c =>
    if (coreOf j).loop = true ∧ i + 1 = (calls es).length then hdr
    else match siteOf j c with
      | some s => (ofK (addressOfIndex s.r), ofK (addressOfIndex fp))
      | none => (0, 0)
  | none => (0, 0)

/-- **What one instance's frame holds** for the completeness check: an instance of function `j`
at frame `fp` (cells at `g^(fp + o)`) with valuation `σ`, path `es` and returned values `vs`, its
callees' frames at `kfps` (one per call of `es`, in order) and its header `hdr`. -/
structure FrameHolds {κ : ℕ} (L : MemoryImage κ) (j fp : ℕ) (σ : Val) (es : List Ev) (vs : List V)
    (kfps : List ℕ) (hdr : E × E) : Prop where
  /-- The header. -/
  hdr0 : L.read (addressOfIndex (fp + 0)) = some hdr.1
  hdr1 : L.read (addressOfIndex (fp + 1)) = some hdr.2
  /-- A function but `main` returns to registers of `K`. -/
  hdrK : j ≠ 1 → IsInK hdr.1 ∧ IsInK hdr.2
  /-- Every value the path names, at its cell. -/
  val : ∀ v ∈ namedOf (coreOf j).params es vs, 2 ≤ cellJ j v → cellJ j v < fsN j →
    L.read (addressOfIndex (fp + cellJ j v)) = some (σ v)
  /-- The range checks' temporaries, at their cells. -/
  tmp : ∀ e ∈ es, ∀ t ∈ e.tmps, 2 ≤ cellJ j t → cellJ j t < fsN j →
    L.read (addressOfIndex (fp + cellJ j t)) = some (σ t)
  /-- The fixed cells. -/
  stat : ∀ p ∈ (plumbOf j).stat, 2 ≤ p.1 → p.1 < fsN j →
    L.read (addressOfIndex (fp + p.1)) = some (p.2.word fp)
  /-- The frame addresses point into the frame. -/
  addr : ∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + cellJ j q.2))
  /-- The table jumps' targets. -/
  arm : ∀ a ∈ (plumbOf j).arms, 2 ≤ a.2.1 → a.2.1 < fsN j →
    L.read (addressOfIndex (fp + a.2.1)) = some (armWord σ a.1 a.2.2)
  /-- The chained `match`es' table targets, on the arm the path takes: the next selector picks a
  slot of the next table, whose word the target cell holds. -/
  chain : ∀ ch ∈ (plumbOf j).chains, ∀ (k t : ℕ), ch.2.2.1[k]? = some t →
    σ (V.n ch.2.1) = ofK (addressOfIndex k) → ∃ e pc, σ (V.n ch.2.2.2.1) = ofK (addressOfIndex e) ∧
      glob.jt.get (ch.2.2.2.2 + e) = some pc ∧
      (2 ≤ t → t < fsN j → L.read (addressOfIndex (fp + t)) = some (armWord σ ch.2.2.2.1 ch.2.2.2.2))
  /-- One callee frame per call. -/
  len : kfps.length = (calls es).length
  /-- A call site's callee frame pointer and dispatch target. -/
  site : ∀ (i : ℕ) (c : Call) (kfp : ℕ) (s : Site), (calls es)[i]? = some c → kfps[i]? = some kfp → siteOf j c = some s →
    (2 ≤ s.q → s.q < fsN j → L.read (addressOfIndex (fp + s.q)) = some (ofK (addressOfIndex kfp))) ∧
    (s.tgt ≠ 0 → 2 ≤ s.tgt → s.tgt < fsN j →
      L.read (addressOfIndex (fp + s.tgt)) = some (ofK (addressOfIndex (entryOf c.f))))
  /-- Each callee frame's header, arguments and self frame pointer cells. -/
  kid : ∀ (i : ℕ) (c : Call) (kfp : ℕ), (calls es)[i]? = some c → kfps[i]? = some kfp →
    L.read (addressOfIndex (kfp + 0)) = some (kidHdr j fp hdr es i).1 ∧
    L.read (addressOfIndex (kfp + 1)) = some (kidHdr j fp hdr es i).2 ∧
    (∀ k (hk : k < c.args.length), L.read (addressOfIndex (kfp + (2 + k))) = some (σ c.args[k])) ∧
    (∀ o ∈ selfCells c.f, L.read (addressOfIndex (kfp + o)) = some (ofK (addressOfIndex kfp)))
  /-- A loop's tail call, its last, has its frame right after the caller's. -/
  tail : (coreOf j).loop = true → ∀ kfp, kfps.getLast? = some kfp → kfp = fp + fsN j

/-- **The callees on a path run**: each call entered, from its callee's entry at its frame to its
return registers, executing `ck[i] op` instructions of each opcode, its returns left in its frame's
cells after its arguments. -/
def KidsRun {κ : ℕ} (L : MemoryImage κ) (σ : Val) (es : List Ev) (kfps : List ℕ) (ck : List (Opcode → ℕ)) :
    Prop :=
  ck.length = (calls es).length ∧ ∀ (i : ℕ) (c : Call) (kfp : ℕ), (calls es)[i]? = some c → kfps[i]? = some kfp →
    c.taken = true → (∃ r, retRegs L (addressOfIndex kfp) = some r ∧
      RunC guestProgram L ⟨addressOfIndex (entryOf c.f), addressOfIndex kfp⟩ r (ck.getD i 0)) ∧
      ∀ k (hk : k < c.rets.length), L.read (addressOfIndex (kfp + (2 + c.args.length + k))) = some (σ c.rets[k])


/-- **What the completeness check gives of function `j`** (`cpl_run`): on a memory holding the
jump table, from an instance's frame holding what the check reads (`FrameHolds`) and its callees'
runs (`KidsRun`), a counted run from its entry to its return registers (`main`: the final ones),
with at most `pathMax` instructions of each opcode besides its callees', its returned values left
in its frame's cells after its arguments. -/
def CplRun (j : ℕ) : Prop :=
  ∀ {κ : ℕ} (L : MemoryImage κ), κ ≤ 32 → JTHolds glob L →
    (∀ q ∈ Memory.tableCells, L.read (addressOfIndex q.1) = some q.2) → ∀ (fp : ℕ), (j = 1 →
        fp = 0) →
    ∀ (σ : Val) (es : List Ev) (vs : List V), walk σ (coreOf j).body = .ret es vs →
    (∀ e ∈ es, e.Holds L.read σ) → ∀ (kfps : List ℕ) (hdr : E × E),
    FrameHolds L j fp σ es vs kfps hdr → ∀ ck : List (Opcode → ℕ), KidsRun L σ es kfps ck →
    ∃ (r : Registers K) (c : Opcode → ℕ), (if j = 1 then r = Registers.final guestProgram else retRegs L (addressOfIndex fp) = some r) ∧
      RunC guestProgram L ⟨addressOfIndex (fnOf j).entryPc, addressOfIndex fp⟩ r c ∧
      (∀ op, c op ≤ pathCount j σ op + (ck.map (· op)).sum) ∧
      ∀ k (hk : k < vs.length),
        L.read (addressOfIndex (fp + (2 + (coreOf j).params.length + k))) = some (σ vs[k])

end
end LeanVM.Guest.B2C
