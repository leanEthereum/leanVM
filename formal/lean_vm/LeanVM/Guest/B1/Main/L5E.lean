/-
  LeanVM.Guest.B1.Main.L5E

  `main`'s children loop with its pops, every node exact on the memory, given each child's `verify_sub` call's trees
  exact (`mainGoalsRR_l5E`).
-/

module

public import LeanVM.Guest.B1.Main.L5RPops
public import LeanVM.Guest.B1.Main.MainHonestE
public import LeanVM.Guest.Budget.BoundedE
public import LeanVM.Guest.Exact.Kids
public import LeanVM.Guest.Exact.FreeMain

/-!
# The children loop, every node exact

`main_loop4`'s body has no computed hint (`l5_pinned`); its claim lists' digests and the statement's digest are exact
for free (`child_claim_list_digest_exactFree`). So a valid tree of `L5From` whose `verify_sub` trees are exact is exact
(`l5From_every`), and `mainGoalsRR_l5E` is `mainGoalsRR_l5` with every node of the loop's tree exact, given
`verify_sub`'s trees exact.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

@[expose] public section

theorem child_claim_list_digest_exactFree : ExactFreeG "child_claim_list_digest" :=
  exactFreeG_of (j := idx% «child_claim_list_digest») (by decide +kernel)

end
end LeanVM.Guest.Memory

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (GuestLimits)
open LeanVM.Guest.B1 (LowDef CompleteAtDTB CompleteAtDTBR Returns)

@[expose] public section

/-- `main_loop4`'s own computed hints are pinned by the next atom: it has none. -/
theorem l5_pinned :
    Stmt.blockNextOk isComputed pinsInverse (coreProgram.getD idx% «main_loop4» default).body = true := by
  rw [l5_body]; decide +kernel

/-- **A valid tree of `L5From` is exact** when its `verify_sub` trees are. -/
theorem l5From_every {rd : Reader} {ex es : ℕ → ℕ} {Pxs Pss Pvs : ℕ → Tree → Prop}
    (hPv : ∀ c t, Pvs c t → t.Every (ExactAt coreProgram rd)) :
    ∀ m c (t : Tree) (args rets : List E), t.Valid coreProgram rd args rets →
      L5From ex es Pxs Pss Pvs m c t → t.Every (ExactAt coreProgram rd) := by
  intro m
  induction m with
  | zero => intro _ _ _ _ _ h; exact h.elim
  | succ m ih =>
    intro c t args rets hv hL
    obtain ⟨σ, bufs, ks, rfl, -, -, hcl, hK⟩ := hL
    have hv' := hv
    obtain ⟨fn', hf', -, es', vs, hw, -, -, hkv⟩ := hv'
    rw [find_l5] at hf'
    obtain rfl := Option.some.inj hf'
    have hw' : walk σ (coreProgram.getD idx% «main_loop4» default).body = .ret (l5Evs σ) [] := by
      rw [l5_body, ← l5Body, l5Body_split]
      exact Main.walk_straight σ [] (l5Pre ++ [l5Tail]) l5Pre_straight
    rw [hw'] at hw
    cases hw
    rw [hcl] at hkv
    refine Tree.every_node.mpr ⟨exactAt_of_body find_l5 l5_pinned hv rd, everyKids_of_kidsT hkv
      (by simp [l5CallList, l5Ts, l5Ts4]) hK fun cl T hm _ t hn htv hT => ?_⟩
    simp only [l5CallList, l5Ts, l5Ts4, List.cons_append, List.nil_append, List.zip_cons_cons, List.zip_nil_right,
      List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact every_exact_of_free child_claim_list_digest_exactFree htv hn rd
    · exact every_exact_of_free child_claim_list_digest_exactFree htv hn rd
    · exact every_exact_of_free statement_digest_exactFree htv hn rd
    · exact hPv c t hT
    · exact ih (c + 1) t _ _ htv hT

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

/-- **`MainGoalsRR.l5`, every node exact**: `mainGoalsRR_l5`, each child's `verify_sub` call by a tree also exact on
the memory. -/
theorem mainGoalsRR_l5E (hbl : bytecode.length = 2 ^ 23) (hn : NodeRelation bytecode seed s w)
    (hl : GuestLimits s w) {SB SK : String → ℕ} {Bv : ℕ → ℕ} {Pvs : ℕ → Tree → Prop} {q : MainPops}
    (hS : MainStatics fs SB SK) {px ps pv : ℕ → List Pop}
    (hV : VerifySubGoalsTBR fs cert fp seed s w
      (fun rd c t => (Pvs c t ∧ SameStreams (t.pops coreProgram rd) (pv c)) ∧ t.Every (ExactAt coreProgram rd)) Bv)
    (hX : ChildListGoalsTBR fs cert fp seed s w
      (fun rd c t => ccHonest (hKid s w c).ex (hMonoX s w c) t ∧ t.pops coreProgram rd = px c)
      (fun rd c t => ccHonest (hKid s w c).es (hMonoS s w c) t ∧ t.pops coreProgram rd = ps c)
      (fun c => B1.Digest.ccBM fs SB (hMonoX s w c) (hKid s w c).ex)
      (fun c => B1.Digest.ccBM fs SB (hMonoS s w c) (hKid s w c).es))
    (hq : ∀ rd, q.p5 rd = l5PopsH px ps pv s w) : (hm fs fp seed s w).nc ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop4» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409, (hm fs fp seed s w).a77,
        (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a80,
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a406, (hm fs fp seed s w).aDa,
        (digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
        (hm fs fp seed s w).a394, (hm fs fp seed s w).et, (hm fs fp seed s w).a400] (Returns [])
      (mainPredsHP fs SB SK Bv Pvs s w q).withExact.P5 (mainBsH fs SB SK Bv s w).B5 := by
  intro h0
  have hnc16 := hl.atMostSixteenChildren
  have hV0 : VerifySubGoalsTBR fs cert fp seed s w
      (fun rd c t => Pvs c t ∧ SameStreams (t.pops coreProgram rd) (pv c)) Bv :=
    fun c hc => (hV c hc).mono le_rfl fun _ _ h => h.1
  have hk := fun c (hc : c < w.children.length) => kidOk cert hbl hn hl hV0.goals
    (((hX c hc).1.toDTB (T' := fun _ => True) fun _ _ _ => trivial).toDT.toD)
    (((hX c hc).2.toDTB (T' := fun _ => True) fun _ _ _ => trivial).toDT.toD) hc
  refine (mainGoalL5TBR fs cert SB hS.main.st hbl hn hl hV hX h0).with_total.monoM le_rfl
    fun rd _ hM t rets hv ⟨hT, htot⟩ => ⟨⟨⟨L5From.mono (fun _ _ h => h.1) (fun _ _ h => h.1)
      (fun _ _ h => h.1.1) _ _ t hT, htot⟩, ?_⟩, l5From_every (fun _ _ h => h.2) _ _ t _ _ hv hT⟩
  rw [hq rd, l5PopsH]
  have hv' : t.Valid coreProgram rd (gen ^ 0 :: [gen ^ (hm fs fp seed s w).nc, (hm fs fp seed s w).a409,
      (hm fs fp seed s w).a77, (hm fs fp seed s w).a117, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
      (hm fs fp seed s w).a80,
      (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
      gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
      (hm fs fp seed s w).a406, (hm fs fp seed s w).aDa,
      (digestHalves (hm fs fp seed s w).seed).1, (digestHalves (hm fs fp seed s w).seed).2,
      (hm fs fp seed s w).a394, (hm fs fp seed s w).et, (hm fs fp seed s w).a400]) rets := by
    rw [pow_zero]; exact hv
  exact l5From_popsS (Cr := hP fs fp seed s w 7) (D := hP fs fp seed s w 4) (nk := w.children.length)
    (defer := fun c => (hKid s w c).defer) (da := fun c => (hKid s w c).da)
    (fun _ _ h => h.2) (fun _ _ h => h.2) (fun _ _ h => h.1.2) (by omega) rfl rfl rfl
    (fun c hc => ⟨(hk c hc).defer_len, ((hk c hc).mem rd hM).2.2.2.2.2.2, ((hk c hc).mem rd hM).2.2.1,
      ((hk c hc).mem rd hM).2.2.2.1⟩) _ 0 t rets (by omega) hv' hT

end
end LeanVM.Guest.B1.Main
