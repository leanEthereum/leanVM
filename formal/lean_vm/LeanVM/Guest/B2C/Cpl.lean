/-
  LeanVM.Guest.B2C.Cpl

  B2's completeness check of one compiled function: its code runs from its entry to its return
  on a memory whose frame holds what the honest memory puts there, window by window of its
  soundness certificate.
-/

module

public import LeanVM.Guest.B2C.Defs
public import LeanVM.Guest.B2C.Count

/-!
# The completeness check

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

@[expose] public section

/-! ## What the check reads of the memory -/

/-- The certificate's cell of value `v` of function `j`. -/
noncomputable def cellJ (j : ℕ) (v : V) : ℕ := (certOf j).locs.getD v.idx 0

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
      | some s => (ofK (gpow s.r), ofK (gpow fp))
      | none => (0, 0)
  | none => (0, 0)

/-- **What one instance's frame holds** for the completeness check: an instance of function `j`
at frame `fp` (cells at `g^(fp + o)`) with valuation `σ`, path `es` and returned values `vs`, its
callees' frames at `kfps` (one per call of `es`, in order) and its header `hdr`. -/
structure FrameHolds {κ : ℕ} (L : MemImage κ) (j fp : ℕ) (σ : Val) (es : List Ev) (vs : List V)
    (kfps : List ℕ) (hdr : E × E) : Prop where
  /-- The header. -/
  hdr0 : L.read (gpow (fp + 0)) = some hdr.1
  hdr1 : L.read (gpow (fp + 1)) = some hdr.2
  /-- A function but `main` returns to registers of `K`. -/
  hdrK : j ≠ 1 → IsInK hdr.1 ∧ IsInK hdr.2
  /-- Every value the path names, at its cell. -/
  val : ∀ v ∈ namedOf (coreOf j).params es vs, 2 ≤ cellJ j v → cellJ j v < fsN j →
    L.read (gpow (fp + cellJ j v)) = some (σ v)
  /-- The range checks' temporaries, at their cells. -/
  tmp : ∀ e ∈ es, ∀ t ∈ e.tmps, 2 ≤ cellJ j t → cellJ j t < fsN j →
    L.read (gpow (fp + cellJ j t)) = some (σ t)
  /-- The fixed cells. -/
  stat : ∀ p ∈ (plumbOf j).stat, 2 ≤ p.1 → p.1 < fsN j →
    L.read (gpow (fp + p.1)) = some (p.2.word fp)
  /-- The frame addresses point into the frame. -/
  addr : ∀ q ∈ addrs es, σ q.1 = ofK (gpow (fp + cellJ j q.2))
  /-- The table jumps' targets. -/
  arm : ∀ a ∈ (plumbOf j).arms, 2 ≤ a.2.1 → a.2.1 < fsN j →
    L.read (gpow (fp + a.2.1)) = some (armWord σ a.1 a.2.2)
  /-- One callee frame per call. -/
  len : kfps.length = (calls es).length
  /-- A call site's callee frame pointer and dispatch target. -/
  site : ∀ (i : ℕ) (c : Call) (kfp : ℕ) (s : Site), (calls es)[i]? = some c → kfps[i]? = some kfp → siteOf j c = some s →
    (2 ≤ s.q → s.q < fsN j → L.read (gpow (fp + s.q)) = some (ofK (gpow kfp))) ∧
    (s.tgt ≠ 0 → 2 ≤ s.tgt → s.tgt < fsN j →
      L.read (gpow (fp + s.tgt)) = some (ofK (gpow (entryOf c.f))))
  /-- Each callee frame's header, arguments, returns (a call entered) and self frame pointer
  cells. -/
  kid : ∀ (i : ℕ) (c : Call) (kfp : ℕ), (calls es)[i]? = some c → kfps[i]? = some kfp →
    L.read (gpow (kfp + 0)) = some (kidHdr j fp hdr es i).1 ∧
    L.read (gpow (kfp + 1)) = some (kidHdr j fp hdr es i).2 ∧
    (∀ k (hk : k < c.args.length), L.read (gpow (kfp + (2 + k))) = some (σ c.args[k])) ∧
    (c.taken = true → ∀ k (hk : k < c.rets.length),
      L.read (gpow (kfp + (2 + c.args.length + k))) = some (σ c.rets[k])) ∧
    (∀ o ∈ selfCells c.f, L.read (gpow (kfp + o)) = some (ofK (gpow kfp)))
  /-- A loop's tail call, its last, has its frame right after the caller's. -/
  tail : (coreOf j).loop = true → ∀ kfp, kfps.getLast? = some kfp → kfp = fp + fsN j

/-- **The callees on a path run**: each call entered, from its callee's entry at its frame to its
return registers, executing `ck[i] op` instructions of each opcode. -/
def KidsRun {κ : ℕ} (L : MemImage κ) (es : List Ev) (kfps : List ℕ) (ck : List (Opcode → ℕ)) :
    Prop :=
  ck.length = (calls es).length ∧ ∀ (i : ℕ) (c : Call) (kfp : ℕ), (calls es)[i]? = some c → kfps[i]? = some kfp →
    c.taken = true → ∃ r, retRegs L (gpow kfp) = some r ∧
      RunC guest L ⟨gpow (entryOf c.f), gpow kfp⟩ r (ck.getD i 0)

end
end LeanVM.Guest.B2C
