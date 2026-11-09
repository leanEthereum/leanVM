/-
  LeanVM.Guest.B1.Main.MainHonestT

  `main` placed on a node's honest run, its children's loop by a tree satisfying a predicate
  `T5`: `main`'s node then has a `__loop4` child satisfying `T5`.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestEnd
public import LeanVM.Guest.AcceptableChild

/-!
# `main` on an honest run, the children's loop's tree exposed

`mTs m T5`: the predicates on `main`'s callees' trees, `T5` on `__loop4`'s, none on the others'.
`mainKidsDT`: `MainGoals` and the children's loop complete by trees satisfying `T5` give
`KidsDT`. `main_honest_relAtInT`: `main_honest_end` with `main`'s node's children satisfying
`KidsT (mCalls σ m) (_ :: mTs m T5)`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within Kid CompleteAtD CompleteAtDT KidsDT Returns)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **The predicates on `main`'s callees' trees**: on its claim lists' digests (`Px`, `Ps`),
`da_verify`'s (`Pd`), `aggregate_claims`' (`Pa`), the children's loop's (`T5`). -/
structure MainPreds where
  Px : Tree → Prop
  Ps : Tree → Prop
  Pd : Tree → Prop
  Pa : Tree → Prop
  T5 : Tree → Prop

/-- **The predicates on `main`'s callees' trees**, aligned with `mKids`. -/
def mTs (m : MainIn) (p : MainPreds) : List (Tree → Prop) :=
  [p.Px, p.Ps, fun _ => True, fun _ => True, fun _ => True, fun _ => True] ++
    (if m.nd = 1 then [p.Pd] else []) ++ [p.T5] ++
    (if m.nc = 0 then [] else [p.Pa]) ++ [fun _ => True]

variable {fp : ℕ} {seed : Digest} {s : NodeStatement} {w : NodeWitness} {bytecode : List K}

/-- The children's loop complete by trees satisfying `T5`. -/
def MainGoalL5T (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) (T5 : Tree → Prop) : Prop :=
  (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDT fs cert 16 "__loop4" (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409, (hm fs fp seed s w).a77,
        (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a406, (hm fs fp seed s w).aDa,
        (digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
        (hm fs fp seed s w).a394, (hm fs fp seed s w).et, (hm fs fp seed s w).a400] (Returns []) T5

theorem MainGoalL5T.goal {T5 : Tree → Prop} (h : MainGoalL5T fs cert fp seed s w T5) :
    MainGoalL5 fs cert fp seed s w := fun hn => (h hn).toD

/-- **`main`'s callees complete by trees satisfying `p`**: its claim lists' digests, `da_verify`,
`aggregate_claims`, the children's loop. -/
structure MainGoalsT (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) (p : MainPreds) : Prop where
  clx : CompleteAtDT fs cert 16 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx]
    (Returns (B1.Digest.digestCells (hm fs fp seed s w).xd)) p.Px
  cls : CompleteAtDT fs cert 16 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls]
    (Returns (B1.Digest.digestCells (hm fs fp seed s w).sd)) p.Ps
  dv : (hm fs fp seed s w).nd = 1 →
    CompleteAtDT fs cert 16 "da_verify" (hLmain fs fp seed s w) [(hm fs fp seed s w).et]
      (Returns (hm fs fp seed s w).daR) p.Pd
  ag : (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDT fs cert 16 "aggregate_claims" (hLmain fs fp seed s w)
      [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a394, (hm fs fp seed s w).a400,
        (hm fs fp seed s w).a406, (hm fs fp seed s w).a417] (Returns []) p.Pa
  l5 : MainGoalL5T fs cert fp seed s w p.T5

/-- **`main`'s callees, by trees satisfying `p`.** -/
theorem mainKidsDT {p : MainPreds} (hg : MainGoals fs cert fp seed s w)
    (hT : MainGoalsT fs cert fp seed s w p) :
    KidsDT fs cert 16 (mKids (hm fs fp seed s w) (hLmain fs fp seed s w))
      (mTs (hm fs fp seed s w) p) := by
  unfold mKids mTs
  by_cases hnd : (hm fs fp seed s w).nd = 1 <;> by_cases hnc : (hm fs fp seed s w).nc = 0 <;>
    simp only [hnd, hnc, ↓reduceIte]
  · exact ⟨fun _ => hT.clx, fun _ => hT.cls, fun ht => (hg.l1 (of_decide_eq_true ht)).toT,
      fun ht => (hg.l2 (of_decide_eq_true ht)).toT, fun ht => (hg.l3 (of_decide_eq_true ht)).toT,
      fun ht => (hg.l4 (of_decide_eq_true ht)).toT, fun _ => hT.dv hnd,
      fun ht => by simp at ht, fun _ => hg.st.toT, trivial⟩
  · exact ⟨fun _ => hT.clx, fun _ => hT.cls, fun ht => (hg.l1 (of_decide_eq_true ht)).toT,
      fun ht => (hg.l2 (of_decide_eq_true ht)).toT, fun ht => (hg.l3 (of_decide_eq_true ht)).toT,
      fun ht => (hg.l4 (of_decide_eq_true ht)).toT, fun _ => hT.dv hnd,
      fun ht => hT.l5 (of_decide_eq_true ht), fun _ => hT.ag hnc, fun _ => hg.st.toT, trivial⟩
  · exact ⟨fun _ => hT.clx, fun _ => hT.cls, fun ht => (hg.l1 (of_decide_eq_true ht)).toT,
      fun ht => (hg.l2 (of_decide_eq_true ht)).toT, fun ht => (hg.l3 (of_decide_eq_true ht)).toT,
      fun ht => (hg.l4 (of_decide_eq_true ht)).toT,
      fun ht => by simp at ht, fun _ => hg.st.toT, trivial⟩
  · exact ⟨fun _ => hT.clx, fun _ => hT.cls, fun ht => (hg.l1 (of_decide_eq_true ht)).toT,
      fun ht => (hg.l2 (of_decide_eq_true ht)).toT, fun ht => (hg.l3 (of_decide_eq_true ht)).toT,
      fun ht => (hg.l4 (of_decide_eq_true ht)).toT,
      fun ht => hT.l5 (of_decide_eq_true ht), fun _ => hT.ag hnc, fun _ => hg.st.toT, trivial⟩

/-- **`main` at `fp` on the honest run, its callees' trees satisfying `p`.** -/
theorem main_honest_relAtInT {p : MainPreds} (hbl : bytecode.length = 2 ^ 23)
    (hr : NodeRelation bytecode seed s w) (hl : DeployedLimits s w)
    (hxc : Sig.verify_lean_xmss_complete_Spec)
    (hsc : Sig.SphincsCompleteSpecs)
    (hT : MainGoalsT fs cert fp seed s w p) :
    ∃ (n : ℕ) (L : B1.Main.Layout), Within L fp n ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧ DisjL L ∧
      (∀ q ∈ hLmain fs fp seed s w, q ∈ L) ∧
      ∀ rd, LowDef 16 rd → B1.Main.MemL rd L →
        LoadHolds rd 1 0 (digestHalves (statementDigest seed s)).1 →
        LoadHolds rd gen 0 (digestHalves (statementDigest seed s)).2 →
        RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp n "main" [] []
          (fun t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧ MVals rd σ (hm fs fp seed s w) ∧
            KidsT (mCalls σ (hm fs fp seed s w)) ((fun _ => True) :: mTs (hm fs fp seed s w) p) ks ∧
            calls (mEvs σ) = mCalls σ (hm fs fp seed s w) ∧ bufs = mSizes (hData seed s w)) :=
  main_relAtInT fs cert fp (hData seed s w) (hOwn seed s w) (hOwn_fit (log2_of_length hbl) hr (freshShaped_of hbl hr))
    (hData_bounds hl fs fp) _
    (mainKidsDT (mainGoals_of hbl hr hl hxc hsc (fun hn => (hT.dv hn).toD) hT.l5.goal
      (fun hn => (hT.ag hn).toD)) hT)
    (fun rd hM h0 h1 => hMainMem (log2_of_length hbl) hr (freshShaped_of hbl hr) hl fs fp rd hM h0 h1)

end
end LeanVM.Guest.B1.Main
