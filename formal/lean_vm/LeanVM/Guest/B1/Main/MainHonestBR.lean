/-
  LeanVM.Guest.B1.Main.MainHonestBR

  `main` placed on a node's honest run within its words, its callees' trees satisfying predicates of the memory (their pops).
-/

module

public import LeanVM.Guest.B1.Main.MainHonestB
public import LeanVM.Guest.B1.Main.MainAtR

/-!
# `main` on an honest run, its callees' predicates of the memory

`MainPredsR`: a predicate of the memory for each of `main`'s callees after `exponent_tables`; `mTsR`: aligned with `mKids`. `MainGoalsTBR`: each callee within its bound (`mBs`) by trees of its predicate (`CompleteAtDTBR`); `mainKidsDTBR`: `KidsDTBR`. `main_honest_relAtInTBR`: `main_honest_relAtInTB` with them.

`MainPops`: the entries of the callees that pop any; `MainPreds.withPops p q`: `p`'s predicates (none on the static loops) with the trees popping `q`'s entries.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef DisjL Within CompleteAtDTBR KidsDTBR Returns)

@[expose] public section

/-- **Predicates of the memory on `main`'s callees' trees**: its claim lists' digests, the four signature loops, `da_verify`, the children's loop, `aggregate_claims`, `statement_digest`. -/
structure MainPredsR where
  Px : Reader → Tree → Prop
  Ps : Reader → Tree → Prop
  P0 : Reader → Tree → Prop
  P1 : Reader → Tree → Prop
  P2 : Reader → Tree → Prop
  P3 : Reader → Tree → Prop
  Pd : Reader → Tree → Prop
  P5 : Reader → Tree → Prop
  Pa : Reader → Tree → Prop
  Pst : Reader → Tree → Prop

/-- **The predicates on `main`'s callees' trees on the memory `rd`**, aligned with `mKids`. -/
def mTsR (m : MainIn) (p : MainPredsR) (rd : Reader) : List (Tree → Prop) :=
  [p.Px rd, p.Ps rd, p.P0 rd, p.P1 rd, p.P2 rd, p.P3 rd] ++ (if m.nd = 1 then [p.Pd rd] else []) ++ [p.P5 rd] ++
    (if m.nc = 0 then [] else [p.Pa rd]) ++ [p.Pst rd]

/-- **The entries of `main`'s callees that pop any**, on each memory. -/
structure MainPops where
  px : Reader → List Pop
  ps : Reader → List Pop
  p0 : Reader → List Pop
  p1 : Reader → List Pop
  p2 : Reader → List Pop
  p3 : Reader → List Pop
  pd : Reader → List Pop
  p5 : Reader → List Pop
  pa : Reader → List Pop

/-- **`p`'s predicates, the trees popping `q`'s entries.** -/
def MainPreds.withPops (p : MainPreds) (q : MainPops) : MainPredsR :=
  ⟨fun rd t => p.Px t ∧ t.pops coreProgram rd = q.px rd, fun rd t => p.Ps t ∧ t.pops coreProgram rd = q.ps rd,
    fun rd t => t.pops coreProgram rd = q.p0 rd, fun rd t => t.pops coreProgram rd = q.p1 rd,
    fun rd t => t.pops coreProgram rd = q.p2 rd, fun rd t => t.pops coreProgram rd = q.p3 rd,
    fun rd t => p.Pd t ∧ t.pops coreProgram rd = q.pd rd, fun rd t => p.T5 t ∧ t.pops coreProgram rd = q.p5 rd,
    fun rd t => p.Pa t ∧ t.pops coreProgram rd = q.pa rd, fun _ _ => True⟩

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness)

/-- **`main`'s callees within their bounds `b`, by trees of `p`'s predicates of the memory.** -/
structure MainGoalsTBR (SB SK : String → ℕ) (p : MainPredsR) (b : MainBs) : Prop where
  clx : CompleteAtDTBR fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx]
    (Returns (B1.Digest.digestCells (hm fs fp seed s w).xd)) p.Px b.Bx
  cls : CompleteAtDTBR fs cert 20 "claim_list_digest" (hLmain fs fp seed s w)
    [(hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls]
    (Returns (B1.Digest.digestCells (hm fs fp seed s w).sd)) p.Ps b.Bs
  l1 : (hm fs fp seed s w).nxd ≠ 0 →
    CompleteAtDTBR fs cert 20 name% «main_loop0» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nxd, (hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx] (Returns []) p.P0
      ((hm fs fp seed s w).nxd * iterK fs SK name% «main_loop0» + fs name% «main_loop0»)
  l2 : (hm fs fp seed s w).nsd ≠ 0 →
    CompleteAtDTBR fs cert 20 name% «main_loop1» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nsd, (hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls] (Returns []) p.P1
      ((hm fs fp seed s w).nsd * iterK fs SK name% «main_loop1» + fs name% «main_loop1»)
  l3 : (hm fs fp seed s w).nrx ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop2» (hLmain fs fp seed s w)
      ([1, gen ^ (hm fs fp seed s w).nrx, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a117, (hm fs fp seed s w).a77] ++ lxTagWords) (Returns []) p.P2
      ((hm fs fp seed s w).nrx * iterK fs SK name% «main_loop2» + fs name% «main_loop2»)
  l4 : (hm fs fp seed s w).nrs ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop3» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nrs, gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ (hm fs fp seed s w).nrx, (hm fs fp seed s w).a80, (hm fs fp seed s w).a119] (Returns []) p.P3
      ((hm fs fp seed s w).nrs * iterK fs SK name% «main_loop3» + fs name% «main_loop3»)
  dv : (hm fs fp seed s w).nd = 1 →
    CompleteAtDTBR fs cert 20 "da_verify" (hLmain fs fp seed s w) [(hm fs fp seed s w).et]
      (Returns (hm fs fp seed s w).daR) p.Pd b.Bd
  l5 : (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop4» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409, (hm fs fp seed s w).a77,
        (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a406, (hm fs fp seed s w).aDa,
        (digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
        (hm fs fp seed s w).a394, (hm fs fp seed s w).et, (hm fs fp seed s w).a400] (Returns []) p.P5 b.B5
  ag : (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTBR fs cert 20 "aggregate_claims" (hLmain fs fp seed s w)
      [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a394, (hm fs fp seed s w).a400,
        (hm fs fp seed s w).a406, (hm fs fp seed s w).a417,
          (hm fs fp seed s w).et * word 133823759239872512 0] (Returns []) p.Pa b.Ba
  st : CompleteAtDTBR fs cert 20 "statement_digest" (hLmain fs fp seed s w)
    [(digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
      (digestHalves (hm fs fp seed s w).xd).1, (digestHalves (hm fs fp seed s w).xd).2,
      (digestHalves (hm fs fp seed s w).sd).1, (digestHalves (hm fs fp seed s w).sd).2,
      (digestHalves (hm fs fp seed s w).dap).1, (digestHalves (hm fs fp seed s w).dap).2,
      (hm fs fp seed s w).a417] (Returns (B1.Digest.digestCells (hm fs fp seed s w).sdg)) p.Pst
    (SB "statement_digest")

variable {fs cert fp seed s w}

/-- **`main`'s callees within their bounds, by trees of their predicates of the memory.** -/
theorem mainKidsDTBR {SB SK : String → ℕ} {p : MainPredsR} {b : MainBs}
    (hT : MainGoalsTBR fs cert fp seed s w SB SK p b) :
    KidsDTBR fs cert 23 (mKids (hm fs fp seed s w) (hLmain fs fp seed s w))
      (mTsR (hm fs fp seed s w) p) (mBs fs SB SK (hm fs fp seed s w) b) := by
  unfold mKids mTsR mBs
  by_cases hnd : (hm fs fp seed s w).nd = 1 <;> by_cases hnc : (hm fs fp seed s w).nc = 0 <;>
    simp only [hnd, hnc, ↓reduceIte]
  · exact ⟨fun _ => hT.clx.lowMono (by norm_num), fun _ => hT.cls.lowMono (by norm_num),
      fun ht => (hT.l1 (of_decide_eq_true ht)).lowMono (by norm_num),
      fun ht => (hT.l2 (of_decide_eq_true ht)).lowMono (by norm_num), fun ht => hT.l3 (of_decide_eq_true ht),
      fun ht => hT.l4 (of_decide_eq_true ht), fun _ => (hT.dv hnd).lowMono (by norm_num),
      fun ht => by simp at ht, fun _ => hT.st.lowMono (by norm_num), trivial⟩
  · exact ⟨fun _ => hT.clx.lowMono (by norm_num), fun _ => hT.cls.lowMono (by norm_num),
      fun ht => (hT.l1 (of_decide_eq_true ht)).lowMono (by norm_num),
      fun ht => (hT.l2 (of_decide_eq_true ht)).lowMono (by norm_num), fun ht => hT.l3 (of_decide_eq_true ht),
      fun ht => hT.l4 (of_decide_eq_true ht), fun _ => (hT.dv hnd).lowMono (by norm_num),
      fun ht => hT.l5 (of_decide_eq_true ht), fun _ => (hT.ag hnc).lowMono (by norm_num),
      fun _ => hT.st.lowMono (by norm_num), trivial⟩
  · exact ⟨fun _ => hT.clx.lowMono (by norm_num), fun _ => hT.cls.lowMono (by norm_num),
      fun ht => (hT.l1 (of_decide_eq_true ht)).lowMono (by norm_num),
      fun ht => (hT.l2 (of_decide_eq_true ht)).lowMono (by norm_num), fun ht => hT.l3 (of_decide_eq_true ht),
      fun ht => hT.l4 (of_decide_eq_true ht),
      fun ht => by simp at ht, fun _ => hT.st.lowMono (by norm_num), trivial⟩
  · exact ⟨fun _ => hT.clx.lowMono (by norm_num), fun _ => hT.cls.lowMono (by norm_num),
      fun ht => (hT.l1 (of_decide_eq_true ht)).lowMono (by norm_num),
      fun ht => (hT.l2 (of_decide_eq_true ht)).lowMono (by norm_num), fun ht => hT.l3 (of_decide_eq_true ht),
      fun ht => hT.l4 (of_decide_eq_true ht),
      fun ht => hT.l5 (of_decide_eq_true ht), fun _ => (hT.ag hnc).lowMono (by norm_num),
      fun _ => hT.st.lowMono (by norm_num), trivial⟩

variable {bytecode : List K}

/-- **`main` at `fp` on the honest run within its words**, its callees' trees satisfying `p`'s predicates of the
memory. -/
theorem main_honest_relAtInTBR {SB SK : String → ℕ} {p : MainPredsR} {b : MainBs}
    (hbl : bytecode.length = 2 ^ 23) (hr : NodeRelation bytecode seed s w) (hl : GuestLimits s w)
    (hT : MainGoalsTBR fs cert fp seed s w SB SK p b) :
    ∃ (n : ℕ) (L : B1.Main.Layout),
      n ≤ mainBH fs SB SK (hData seed s w) (hm fs fp seed s w) (hLmain fs fp seed s w) b ∧
      Within L fp n ∧ (∀ q ∈ L, fp + fs "main" ≤ q.1) ∧ DisjL L ∧
      (∀ q ∈ hLmain fs fp seed s w, q ∈ L) ∧
      ∀ rd, LowDef 23 rd → B1.Main.MemL rd L →
        LoadHolds rd 1 0 (digestHalves (statementDigest seed s)).1 →
        LoadHolds rd gen 0 (digestHalves (statementDigest seed s)).2 →
        RelAtInT coreProgram fs cert rd (fun i => i < 2) (fun _ => False) fp n "main" [] []
          (fun t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧ MVals rd σ (hm fs fp seed s w) ∧
            KidsT (mCalls σ (hm fs fp seed s w)) ((fun _ => True) :: mTsR (hm fs fp seed s w) p rd) ks ∧
            calls (mEvs σ) = mCalls σ (hm fs fp seed s w) ∧ bufs = mSizes (hData seed s w)) :=
  main_relAtInTBR fs cert fp (hData seed s w) (hOwn seed s w)
    (hOwn_fit (log2_of_length hbl) hr (freshShaped_of hbl hr)) (hData_bounds hl fs fp) _ _
    (mainKidsDTBR hT)
    (fun rd hM h0 h1 => hMainMem (log2_of_length hbl) hr (freshShaped_of hbl hr) hl fs fp rd hM h0 h1)

end
end LeanVM.Guest.B1.Main
