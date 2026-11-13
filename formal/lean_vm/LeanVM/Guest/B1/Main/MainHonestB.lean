/-
  LeanVM.Guest.B1.Main.MainHonestB

  `main` placed on a node's honest run within its words, before any memory: from its callees
  within their bounds, `main`'s size at most `mainB` of their bounds.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestT
public import LeanVM.Guest.B1.Main.MainGoalsStaticB
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Data.NameStrings

/-!
# `main` on an honest run, within its words

`MainBs`: the bounds of `main`'s non-static callees (its claim lists' digests, `da_verify`,
`aggregate_claims`, the children's loop). `mBs`: every callee's bound, aligned with `mKids`: the
static ones' (`SB`, the loops' counts times `SK`), then `MainBs`'.
`MainStaticGoalsB`, `MainGoalsTB`: the callees within those bounds. `mainKidsDTB`: `KidsDTB`.
`MainPreds.withTotal`: each non-static callee's predicate with its tree's words within its bound
(`CompleteAtDTB.with_total`). `main_honest_relAtInTB`: `main_relAtInTB` on the honest run.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within Kid CompleteAtD CompleteAtDT CompleteAtDTB KidsDTB Returns
  kidsBoundL)

@[expose] public section

/-- **The bounds of `main`'s non-static callees.** -/
structure MainBs where
  Bx : ℕ
  Bs : ℕ
  Bd : ℕ
  Ba : ℕ
  B5 : ℕ

/-- **Every callee's bound**, aligned with `mKids`. -/
def mBs (fs SB SK : String → ℕ) (m : MainIn) (b : MainBs) : List ℕ :=
  [b.Bx, b.Bs, m.nxd * iterK fs SK name% «main_loop0» + fs name% «main_loop0», m.nsd * iterK fs SK name% «main_loop1» + fs name% «main_loop1»,
    m.nrx * iterK fs SK name% «main_loop2» + fs name% «main_loop2», m.nrs * iterK fs SK name% «main_loop3» + fs name% «main_loop3»] ++ (if m.nd = 1 then [b.Bd] else []) ++ [b.B5] ++
    (if m.nc = 0 then [] else [b.Ba]) ++ [SB "statement_digest"]

/-- **`main`'s words**, its callees within `mBs`. -/
def mainBH (fs : String → ℕ) (SB SK : String → ℕ) (d : MainData) (m : MainIn) (Lin : Layout)
    (b : MainBs) : ℕ :=
  mainB fs d (mKids m Lin) (mBs fs SB SK m b)

/-- Each non-static callee's predicate, its tree's words within its bound. -/
def MainPreds.withTotal (p : MainPreds) (fs : String → ℕ) (b : MainBs) : MainPreds :=
  ⟨fun t => p.Px t ∧ t.total fs ≤ b.Bx, fun t => p.Ps t ∧ t.total fs ≤ b.Bs,
    fun t => p.Pd t ∧ t.total fs ≤ b.Bd, fun t => p.Pa t ∧ t.total fs ≤ b.Ba,
    fun t => p.T5 t ∧ t.total fs ≤ b.B5⟩

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness)

/-- **`main`'s static callees within their bounds.** -/
structure MainStaticGoalsB (SB SK : String → ℕ) : Prop where
  l1 : MainGoalL1B fs cert fp seed s w SK
  l2 : MainGoalL2B fs cert fp seed s w SK
  l3 : MainGoalL3B fs cert fp seed s w SK
  l4 : MainGoalL4B fs cert fp seed s w SK
  st : MainGoalStB fs cert fp seed s w SB

/-- **`main`'s non-static callees within their bounds `b`, by trees satisfying `p`.** -/
structure MainGoalsTB (p : MainPreds) (b : MainBs) : Prop where
  clx : CompleteAtDTB fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx]
    (Returns (B1.Digest.digestCells (hm fs fp seed s w).xd)) p.Px b.Bx
  cls : CompleteAtDTB fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls]
    (Returns (B1.Digest.digestCells (hm fs fp seed s w).sd)) p.Ps b.Bs
  dv : (hm fs fp seed s w).nd = 1 →
    CompleteAtDTB fs cert 20 "da_verify" (hLmain fs fp seed s w) [(hm fs fp seed s w).et]
      (Returns (hm fs fp seed s w).daR) p.Pd b.Bd
  ag : (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTB fs cert 20 "aggregate_claims" (hLmain fs fp seed s w)
      [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a394, (hm fs fp seed s w).a400,
        (hm fs fp seed s w).a406, (hm fs fp seed s w).a417,
          (hm fs fp seed s w).et * word 133823759239872512 0] (Returns []) p.Pa b.Ba
  l5 : (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTB fs cert 23 name% «main_loop4» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409, (hm fs fp seed s w).a77,
        (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a406, (hm fs fp seed s w).aDa,
        (digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
        (hm fs fp seed s w).a394, (hm fs fp seed s w).et, (hm fs fp seed s w).a400] (Returns []) p.T5 b.B5

variable {fs cert fp seed s w}

/-- **The words in the predicates**: each non-static callee's tree within its bound. -/
theorem MainGoalsTB.withTotal {p : MainPreds} {b : MainBs} (h : MainGoalsTB fs cert fp seed s w p b) :
    MainGoalsTB fs cert fp seed s w (p.withTotal fs b) b :=
  ⟨h.clx.with_total, h.cls.with_total, fun hn => (h.dv hn).with_total,
    fun hn => (h.ag hn).with_total, fun hn => (h.l5 hn).with_total⟩

/-- **`main`'s callees within their bounds.** -/
theorem mainKidsDTB {SB SK : String → ℕ} {p : MainPreds} {b : MainBs}
    (hg : MainStaticGoalsB fs cert fp seed s w SB SK) (hT : MainGoalsTB fs cert fp seed s w p b) :
    KidsDTB fs cert 23 (mKids (hm fs fp seed s w) (hLmain fs fp seed s w))
      (mTs (hm fs fp seed s w) p) (mBs fs SB SK (hm fs fp seed s w) b) := by
  unfold mKids mTs mBs
  by_cases hnd : (hm fs fp seed s w).nd = 1 <;> by_cases hnc : (hm fs fp seed s w).nc = 0 <;>
    simp only [hnd, hnc, ↓reduceIte]
  · exact ⟨fun _ => hT.clx.lowMono (by norm_num), fun _ => hT.cls.lowMono (by norm_num), fun ht => (hg.l1 (of_decide_eq_true ht)).lowMono (by norm_num),
      fun ht => (hg.l2 (of_decide_eq_true ht)).lowMono (by norm_num), fun ht => hg.l3 (of_decide_eq_true ht),
      fun ht => hg.l4 (of_decide_eq_true ht), fun _ => (hT.dv hnd).lowMono (by norm_num),
      fun ht => by simp at ht, fun _ => hg.st.lowMono (by norm_num), trivial⟩
  · exact ⟨fun _ => hT.clx.lowMono (by norm_num), fun _ => hT.cls.lowMono (by norm_num), fun ht => (hg.l1 (of_decide_eq_true ht)).lowMono (by norm_num),
      fun ht => (hg.l2 (of_decide_eq_true ht)).lowMono (by norm_num), fun ht => hg.l3 (of_decide_eq_true ht),
      fun ht => hg.l4 (of_decide_eq_true ht), fun _ => (hT.dv hnd).lowMono (by norm_num),
      fun ht => hT.l5 (of_decide_eq_true ht), fun _ => (hT.ag hnc).lowMono (by norm_num), fun _ => hg.st.lowMono (by norm_num), trivial⟩
  · exact ⟨fun _ => hT.clx.lowMono (by norm_num), fun _ => hT.cls.lowMono (by norm_num), fun ht => (hg.l1 (of_decide_eq_true ht)).lowMono (by norm_num),
      fun ht => (hg.l2 (of_decide_eq_true ht)).lowMono (by norm_num), fun ht => hg.l3 (of_decide_eq_true ht),
      fun ht => hg.l4 (of_decide_eq_true ht),
      fun ht => by simp at ht, fun _ => hg.st.lowMono (by norm_num), trivial⟩
  · exact ⟨fun _ => hT.clx.lowMono (by norm_num), fun _ => hT.cls.lowMono (by norm_num), fun ht => (hg.l1 (of_decide_eq_true ht)).lowMono (by norm_num),
      fun ht => (hg.l2 (of_decide_eq_true ht)).lowMono (by norm_num), fun ht => hg.l3 (of_decide_eq_true ht),
      fun ht => hg.l4 (of_decide_eq_true ht),
      fun ht => hT.l5 (of_decide_eq_true ht), fun _ => (hT.ag hnc).lowMono (by norm_num), fun _ => hg.st.lowMono (by norm_num), trivial⟩

variable {bytecode : List K}

/-- **`main` at `fp` on the honest run within its words**: its size at most `mainBH`, its
callees' trees satisfying `p`. -/
theorem main_honest_relAtInTB {SB SK : String → ℕ} {p : MainPreds} {b : MainBs}
    (hbl : bytecode.length = 2 ^ 23) (hr : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    (hg : MainStaticGoalsB fs cert fp seed s w SB SK) (hT : MainGoalsTB fs cert fp seed s w p b) :
    ∃ (n : ℕ) (L : B1.Main.Layout),
      n ≤ mainBH fs SB SK (hData seed s w) (hm fs fp seed s w) (hLmain fs fp seed s w) b ∧
      Within L fp n ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧ DisjL L ∧
      (∀ q ∈ hLmain fs fp seed s w, q ∈ L) ∧
      ∀ rd, LowDef 23 rd → B1.Main.MemL rd L →
        LoadHolds rd 1 0 (digestHalves (statementDigest seed s)).1 →
        LoadHolds rd gen 0 (digestHalves (statementDigest seed s)).2 →
        RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp n "main" [] []
          (fun t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧ MVals rd σ (hm fs fp seed s w) ∧
            KidsT (mCalls σ (hm fs fp seed s w)) ((fun _ => True) :: mTs (hm fs fp seed s w) p) ks ∧
            calls (mEvs σ) = mCalls σ (hm fs fp seed s w) ∧ bufs = mSizes (hData seed s w)) :=
  main_relAtInTB fs cert fp (hData seed s w) (hOwn seed s w)
    (hOwn_fit (log2_of_length hbl) hr (freshShaped_of hbl hr)) (hData_bounds hl fs fp) _ _
    (mainKidsDTB hg hT)
    (fun rd hM h0 h1 => hMainMem (log2_of_length hbl) hr (freshShaped_of hbl hr) hl fs fp rd hM h0 h1)

/-- **The static bounds of `main`'s own static callees** (G7-cnt's certificates). -/
structure MainStaticsMain (fs : String → ℕ) (SB SK : String → ℕ) : Prop where
  l1 : TotalLeOn coreProgram fs name% «main_loop0» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «main_loop0» + fs name% «main_loop0»)
  l2 : TotalLeOn coreProgram fs name% «main_loop1» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «main_loop1» + fs name% «main_loop1»)
  l3 : TotalLeOn coreProgram fs name% «main_loop2» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «main_loop2» + fs name% «main_loop2»)
  l4 : TotalLeOn coreProgram fs name% «main_loop3» LoopPre
    (fun a => logG (a.getD 1 0) * iterK fs SK name% «main_loop3» + fs name% «main_loop3»)
  st : TotalLe coreProgram fs "statement_digest" (fun _ => SB "statement_digest")

/-- **`main`'s static callees on the honest run, within their bounds.** -/
theorem mainStaticGoalsB_of {SB SK : String → ℕ} (hbl : bytecode.length = 2 ^ 23)
    (hr : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    (hxc : Sig.verify_lean_xmss_complete_Spec)
    (hsc : Sig.SphincsCompleteSpecs) (hS : MainStaticsMain fs SB SK) :
    MainStaticGoalsB fs cert fp seed s w SB SK := by
  have hb : MainBounds (2 ^ 23) (hm fs fp seed s w) := hData_bounds hl fs fp
  exact ⟨mainGoalL1B hS.l1 (by have := hb.xd; omega), mainGoalL2B hS.l2 (by have := hb.sd; omega),
    mainGoalL3B hr hl hxc hS.l3, mainGoalL4B hr hl hsc hS.l4, mainGoalStB hr hbl hS.st⟩

end
end LeanVM.Guest.B1.Main
