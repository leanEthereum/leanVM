/-
  LeanVM.Guest.B1.Main.MainHonestFull

  **`main`'s completeness on a node's honest run**, every callee discharged but each child's
  `verify_sub` and the signature schemes, with `main`'s tree exposed: its node's valuation holds
  `main`'s honest values, and its children's loop's tree the children's counts.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5T
public import LeanVM.Guest.AcceptableChild

/-!
# `main` on an honest run, its tree exposed

`main_honest_fullT`: for `NodeRelation` within `Limits` and a bytecode of `2^23` words, from the
signature schemes' completeness (B1-e), its non-static callees by trees satisfying their predicates
and each child's `verify_sub` by a tree satisfying `Pvs c` (`VerifySubGoalsT … Pvs`, B1-d): a layout `L` within
`[fp, fp + n)`, above `main`'s frame, pairwise disjoint, containing `main`'s honest words; on every
memory holding `L` and the statement's digest at words `0`, `1`, `main` holds at `fp` by a tree
`.node "main" σ bufs ks` with `MVals rd σ` of the honest oracle (its hinted counts among them) and
its callees' trees satisfying `mTs … (L5Hinted w Pvs)`: the children's loop's iterations hold
each child's counts, child `c`'s `verify_sub` tree `Pvs c`. `main_honest_fullT_true`: from
`VerifySubGoals`, `Pvs` trivial.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within CompleteAtDT Returns CompleteAtD)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

/-- **`main`'s completeness on the honest run, its tree exposed**: its claim lists' digests',
`da_verify`'s and `aggregate_claims`' trees satisfying `Px`, `Ps`, `Pd`, `Pa`, its children's
loop's iterations `L5Hinted w Pxs Pss Pvs` (each child's claim lists' digests' and `verify_sub`'s
trees satisfying `Pxs c`, `Pss c`, `Pvs c`). -/
theorem main_honest_fullT (hbl : bytecode.length = 2 ^ 23) (hr : NodeRelation bytecode seed s w)
    (hl : DeployedLimits s w) (hxc : Sig.verify_lean_xmss_complete_Spec)
    (hsc : Sig.SphincsCompleteSpecs)
    {Px Ps Pd Pa : Tree → Prop} {Pxs Pss Pvs : ℕ → Tree → Prop}
    (hV : VerifySubGoalsT fs cert fp seed s w Pvs) (hX : ChildListGoalsT fs cert fp seed s w Pxs Pss)
    (hclx : CompleteAtDT fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx]
      (Returns (B1.Digest.digestCells (hm fs fp seed s w).xd)) Px)
    (hcls : CompleteAtDT fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
      [(hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls]
      (Returns (B1.Digest.digestCells (hm fs fp seed s w).sd)) Ps)
    (hdv : (hm fs fp seed s w).nd = 1 →
      CompleteAtDT fs cert 20 "da_verify" (hLmain fs fp seed s w) [(hm fs fp seed s w).et]
        (Returns (hm fs fp seed s w).daR) Pd)
    (hag : (hm fs fp seed s w).nc ≠ 0 →
      CompleteAtDT fs cert 20 "aggregate_claims" (hLmain fs fp seed s w)
        [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a394, (hm fs fp seed s w).a400,
          (hm fs fp seed s w).a406, (hm fs fp seed s w).a417] (Returns []) Pa) :
    ∃ (n : ℕ) (L : B1.Main.Layout), Within L fp n ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧ DisjL L ∧
      (∀ q ∈ hLmain fs fp seed s w, q ∈ L) ∧
      ∀ rd, LowDef 20 rd → B1.Main.MemL rd L →
        LoadHolds rd 1 0 (digestHalves (statementDigest seed s)).1 →
        LoadHolds rd gen 0 (digestHalves (statementDigest seed s)).2 →
        RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp n "main" [] []
          (fun t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧ MVals rd σ (hm fs fp seed s w) ∧
            KidsT (mCalls σ (hm fs fp seed s w))
              ((fun _ => True) :: mTs (hm fs fp seed s w) ⟨Px, Ps, Pd, Pa, L5Hinted w Pxs Pss Pvs⟩) ks ∧
            calls (mEvs σ) = mCalls σ (hm fs fp seed s w) ∧ bufs = mSizes (hData seed s w)) :=
  main_honest_relAtInT hbl hr hl hxc hsc ⟨hclx, hcls, hdv, hag, mainGoalL5T hbl hr hl hV hX⟩

end
end LeanVM.Guest.B1.Main
