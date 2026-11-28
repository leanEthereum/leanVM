/-
  LeanVM.Guest.B1.Link.Arith.Section

  The link section's values are `linkTail`'s terms: the section computes the guest's functions
  (`linkSecProgram`, `linkSecRow`), which are the Statement's (the identities).
-/

module

public import LeanVM.Guest.B1.Link.Arith.IR
public import LeanVM.Guest.B1.Link.Arith.Side

/-!
# The link section, against `linkTail`

`linkSecStatement`: on a valuation satisfying the section's atoms whose reads are the Statement's
values (`IRReads` at `tailIn`), for inputs of the right lengths (`TailShape`) and the guest's
program size (`BYTECODE_LOG`), the section's index-side claim is `indexClaim`, its program side,
`y_mem`, `x_bc`, `p_fp` are `tailLets`', and its `coef`, `base`, `rest`, `cert_w`, `cert_w·cert` and
the twelve shift coefficients stored at `shifts` are `tailRowSide`'s (`rest` against
`eq0(q_point)·base`, `cert_w·cert` against `cert_weight·cert`): what `link_terminal`'s
`LtHolds` and `linkTailR`'s terminal check then compare.
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Protocol.Verifier LeanVM.Protocol.Link

@[expose] public section

/-- **The link section's values are `linkTail`'s.** -/
def LinkSecStatement : Prop :=
  ∀ (rd : Reader) (σ : Val) (layout : Layout) (chunks : Chunks) (theta0 : E) (drawn r : List E)
    (m1 : E) (fresh splitv chi qPoint message : List E),
    (∀ a, Stmt.atom a ∈ linkSec → a.Holds rd σ) →
    IRReads rd σ (tailIn layout chunks theta0 drawn r m1 fresh splitv chi qPoint message) →
    TailShape layout drawn fresh splitv qPoint message →
    layout.logBytecode = guest_const% BYTECODE_LOG →
    let L := tailLets layout chunks theta0 drawn r m1 fresh (Split.ofColumns tables splitv) qPoint
    let R := tailRowSide layout chunks theta0 drawn r m1 fresh (Split.ofColumns tables splitv) chi
      qPoint message
    σ (.n 764) = indexClaim layout chunks drawn ∧ σ (.n 967) = L.program ∧
    σ (.n 1044) = L.frameProgram ∧ σ (.n 1049) = L.yMem ∧ σ (.n 1057) = L.xBc ∧
    σ (.n 1058) = L.pFp ∧ σ (.n 2846) = R.coef ∧ σ (.n 2655) = R.base ∧
    σ (.n 2890) = prodE (qPoint.map (1 + ·)) * R.base ∧ σ (.n 2733) = R.certWeight ∧
    σ (.n 2891) = R.certWeight * L.cert ∧ ∀ s < 12, rdw rd (σ (.n 19)) s = R.shifts.getD s 0

theorem gShifts_getD (v : LinkIn E) {s : ℕ} (hs : s < 12) : (gShifts v).getD s 0 = gShift v s := by
  rw [gShifts, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by simpa using hs),
    Option.map_some, Option.getD_some]

theorem linkSecStatement : LinkSecStatement := by
  intro rd σ layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hA hr hs hlb
  have hclaim := claimIdentity layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hlb
  have hprog := programIdentity layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  have hside := sideIdentity layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  have hrow := rowIdentity layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  have hterm := terminalIdentity layout chunks theta0 drawn r m1 fresh splitv chi qPoint message hs
  dsimp only at hprog hside hrow hterm ⊢
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := linkSecProgram rd σ _ hA hr
  have hag : IRAgree rd σ (tailIn layout chunks theta0 drawn r m1 fresh splitv chi qPoint message) :=
    { hr with
      xBc := p5.trans hside.2.1
      pFp := p6.trans hside.2.2
      yMem := p4.trans hside.1 }
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := linkSecRow rd σ _ hA hag
  refine ⟨p1.trans hclaim, p2.trans (congrArg Prod.fst hprog), p3.trans (congrArg Prod.snd hprog),
    p4.trans hside.1, p5.trans hside.2.1, p6.trans hside.2.2, r1.trans hrow.1, r2.trans hrow.2.2.2,
    r3.trans hterm.1, r4.trans hrow.2.2.1, r5.trans (by rw [hrow.2.2.1]; rfl), fun s hsl ↦ ?_⟩
  rw [r6 s hsl, ← hrow.2.1, gShifts_getD _ hsl]

end

end LeanVM.Guest.B1.Link.Arith
