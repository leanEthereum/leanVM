/-
  LeanVM.Guest.Budget.Final

  `MainComplete` within a budget from `main`'s bounded completeness (B1-f's `main_honest_budgetB`),
  its callees' static bounds and counts, each child's `verify_sub` within `Bvf` at its announced stack log and rate, and the budget's
  two clauses on the bounds.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Budget.End
public import LeanVM.Guest.Budget.MainCount
public import LeanVM.Guest.B1.Main.MainHonestBudgetB
public import LeanVM.Guest.Budget.Instrs
public import LeanVM.Guest.AcceptableChild

/-!
# `main` within the budget

`mainComplete_of_main`: `End.MainComplete fs cert cnt b` from
* B1-f's `main_honest_budgetB` at `0` (the signature schemes' specs, the frame runs' fit, the
  static callees' words `MainStatics`, each child's `verify_sub` within `Bvf` at its announced stack log and rate);
* the counts within the frame weights `ω op` and the jump table's `jt op` (`hcnt`), `main`'s
  callees' weights `MainCounts (ω op) fs` (`H`), the claim lists' within `Kx op s w`,
  `Ks op s w`, `da_verify`'s within `Kd op s w` and the children's loop's within `K5 op s w` on
  their honest trees (`hx`, `hs`, `hd`, `h5`);
* the budget's clauses: `Bmain` within its words, `mainCount` plus `jt` within its
  instructions.
`mainComplete_budget`: within `mainBudget`, the claim lists and `da_verify` at `H`'s affine bounds
(`clHonest_weight`, `dvNH_weight`), the children's loop at `l5Lin`.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol
open LeanVM.Guest.End (MainComplete Budget work bytecode bytecode_length)
open LeanVM.Guest.B1.Main (Bmain mainBsH hm hData mainPredsH hDvNH VerifySubGoalsTB MainStatics
  main_honest_budgetB hData_bounds childBv)

@[expose] public section

/-- **`main` is complete within the budget `b`**, from its bounded completeness, its callees'
bounds and counts, and the budget's clauses. -/
theorem mainComplete_of_main (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ)
    (b : Budget) {SB SK : String → ℕ} {Pvs : NodeWitness → ℕ → Tree → Prop} {Bvf : ℕ → ℕ → ℕ}
    (ω : Opcode → String → ℕ) (jt : Opcode → ℕ) (H : ∀ op, MainCounts (ω op) fs)
    (hfs : 2 ≤ fs "main") (hxc : B1.Sig.verify_lean_xmss_complete_Spec)
    (hsc : B1.Sig.SphincsCompleteSpecs) (hrf : Lift.RunsFit fs cert)
    (hS : MainStatics fs SB SK)
    (hV : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
      ChildrenOk bytecode seed w →
      VerifySubGoalsTB fs cert 0 seed s w (Pvs w) (childBv Bvf w))
    (hcnt : ∀ (rd : Reader) (t : Tree), t.Valid coreProgram rd [] [] → ∀ op,
      cnt t op ≤ t.weight (ω op) + jt op)
    (Kx Ks Kd K5 : Opcode → NodeStatement → NodeWitness → ℕ)
    (hx : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ op (rd : Reader)
      (t : Tree) (args rets : List E), t.name = "claim_list_digest" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      (mainPredsH s w (hDvNH w) (Pvs w)).Px t → t.weight (ω op) ≤ Kx op s w)
    (hs : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ op (rd : Reader)
      (t : Tree) (args rets : List E), t.name = "claim_list_digest" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      (mainPredsH s w (hDvNH w) (Pvs w)).Ps t → t.weight (ω op) ≤ Ks op s w)
    (hd : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → (hm fs 0 seed s w).nd = 1 →
      ∀ op (rd : Reader) (t : Tree) (args rets : List E), t.name = "da_verify" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      (mainPredsH s w (hDvNH w) (Pvs w)).Pd t → t.weight (ω op) ≤ Kd op s w)
    (h5 : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ op (rd : Reader)
      (t : Tree) (args rets : List E), t.name = (name% main_loop4) → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → (mainPredsH s w (hDvNH w) (Pvs w)).T5 t →
        t.weight (ω op) ≤ K5 op s w)
    (hwords : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
      Bmain fs SB SK (childBv Bvf w) 0 seed s w ≤ b.words.eval (work s w))
    (hinstrs : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ op,
      mainCount (H op) (hm fs 0 seed s w) (Kx op s w) (Ks op s w) (Kd op s w) (K5 op s w) +
        jt op ≤ (b.instrs op).eval (work s w)) :
    MainComplete fs cert cnt b := by
  refine mainComplete_of_bounds fs cert cnt b
    (fun seed s w rd t => ∃ σ bufs ks, t = .node "main" σ bufs ks ∧
      B1.Main.MVals rd σ (hm fs 0 seed s w) ∧
      KidsT (B1.Main.mCalls σ (hm fs 0 seed s w))
        ((fun _ => True) :: B1.Main.mTs (hm fs 0 seed s w)
          ((mainPredsH s w (hDvNH w) (Pvs w)).withTotal fs (mainBsH fs SB SK (childBv Bvf w) s w))) ks ∧
      calls (B1.Main.mEvs σ) = B1.Main.mCalls σ (hm fs 0 seed s w) ∧ bufs = B1.Main.mSizes (hData seed s w))
    (fun seed s w => Bmain fs SB SK (childBv Bvf w) 0 seed s w) hfs ?_ ?_ hwords
  · intro seed s w hrel hlim hok
    obtain ⟨n, L, hn, hW, hab, hD, -, hR⟩ := main_honest_budgetB bytecode_length hrel hlim hxc hsc
      hrf hS (hV seed s w hrel hlim hok)
    exact ⟨n, L, hn, hW, fun q hq => by simpa using hab q hq, hD, hR⟩
  · intro seed s w hrel hlim rd t hTt hv hb op
    obtain ⟨σ, bufs, ks, ht, hMV, hT, hc, -⟩ := hTt
    subst ht
    have hw := main_weight_count (H op) (Kx op s w) (Ks op s w) (Kd op s w) (K5 op s w)
      (hx seed s w hrel hlim op) (hs seed s w hrel hlim op)
      (fun h1 => hd seed s w hrel hlim h1 op) (h5 seed s w hrel hlim op) hv hb hc hMV
      (hData_bounds hlim fs 0) hT
    have := hcnt rd _ hv op
    have := hinstrs seed s w hrel hlim op
    omega

/-- **The budget**: `main`'s words (B1-f's `mainWords`) at the static bounds `SB`, `SK` and
`verify_sub`'s words `Bvf μ r` at a child's announced stack log `μ` and rate `r`, and its
instructions (`mainInstrs`) at the callees' weights `H`, the children's loop's instructions
`l5Lin (c5 op) (s5 op) (v5 op)` and the jump table's `jt`. -/
def mainBudget (fs : String → ℕ) (SB SK : String → ℕ) (Bvf : ℕ → ℕ → ℕ) (ω : Opcode → String → ℕ)
    (H : ∀ op, MainCounts (ω op) fs) (c5 s5 : Opcode → ℕ) (v5 : Opcode → ℕ → ℕ → ℕ)
    (jt : Opcode → ℕ) : Budget :=
  ⟨B1.Main.mainWords fs SB SK Bvf, fun op => mainInstrs (H op) (c5 op) (s5 op) (v5 op) (jt op)⟩

/-- The declared claims of each scheme are held by the raw signatures and the children's claims
(`GuestLimits`), so are fewer than the coverage slots, below `2^23`. -/
theorem claims_lt {s : NodeStatement} {w : NodeWitness} (hl : GuestLimits s w) :
    s.claims.xmss.length < 2 ^ 23 ∧ s.claims.sphincs.length < 2 ^ 23 := by
  have hx := hl.claimsHeldWithMultiplicity.1.length_le
  have hs := hl.claimsHeldWithMultiplicity.2.length_le
  have hc := hl.coverageSlotsBelow2Pow23
  have hx' := List.sum_le_sum (l := w.children)
    (f := fun ch ↦ ch.statement.claims.xmss.length)
    (g := fun ch ↦ ch.statement.claims.xmss.length + ch.statement.claims.sphincs.length)
    fun _ _ ↦ Nat.le_add_right _ _
  have hs' := List.sum_le_sum (l := w.children)
    (f := fun ch ↦ ch.statement.claims.sphincs.length)
    (g := fun ch ↦ ch.statement.claims.xmss.length + ch.statement.claims.sphincs.length)
    fun _ _ ↦ Nat.le_add_left _ _
  simp only [List.length_append, List.length_map, List.length_flatten, List.map_map,
    Function.comp_def] at hx hs
  unfold coverageSlots at hc
  omega

/-- **`main`'s claim lists' instructions** on their honest trees: `clA + clS · n` on `n` claims. -/
theorem clHonest_weight {ω fs : String → ℕ} (H : MainCounts ω fs) {n : ℕ} (hn : n < 2 ^ 23) (rd : Reader) (t : Tree)
    (args rets : List E) (hnm : t.name = "claim_list_digest") (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (hT : B1.Main.clHonest n t) : t.weight ω ≤ H.clA + H.clS * n :=
  H.cl rd t args rets n hnm hv hb hT (by omega)

/-- **`main`'s `da_verify`'s instructions** on its honest tree at the checked blob matrix: `dvA`,
`dvR` per row and `dvP` per padded row. -/
theorem dvNH_weight {ω fs : String → ℕ} (H : MainCounts ω fs) {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hr : NodeRelation bytecode seed s w) (hnd : (hm fs 0 seed s w).nd = 1) (rd : Reader) (t : Tree)
    (args rets : List E) (hnm : t.name = "da_verify") (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (hT : hDvNH w t) :
    t.weight ω ≤ H.dvA + H.dvR * (work s w).rawDaRows + H.dvP * (work s w).rawDaPad := by
  obtain ⟨p, hp, -, hw⟩ := B1.Main.checked_da fs 0 hr hnd
  have er : (work s w).rawDaRows = p.2.rows.length := by
    simp [work, hp]
  have ep : (work s w).rawDaPad = 2 ^ B1.Da.wLog p.2 := by
    simp [work, hp, LeanDa.maxRows, B1.Da.wLog]
  unfold hDvNH at hT
  rw [hp] at hT
  simp only [Option.map_some, Option.getD_some] at hT
  rw [er, ep]
  exact H.dv rd t args rets _ _ hnm hv hb hT hw.1 hw.2.1 rfl

/-- **`main` is complete within `mainBudget`.** -/
theorem mainComplete_budget (fs : String → ℕ) (cert : String → V → ℕ) (cnt : Tree → Opcode → ℕ)
    {SB SK : String → ℕ} {Pvs : NodeWitness → ℕ → Tree → Prop} {Bvf : ℕ → ℕ → ℕ}
    (ω : Opcode → String → ℕ) (jt : Opcode → ℕ) (H : ∀ op, MainCounts (ω op) fs)
    (hfs : 2 ≤ fs "main") (hxc : B1.Sig.verify_lean_xmss_complete_Spec)
    (hsc : B1.Sig.SphincsCompleteSpecs) (hrf : Lift.RunsFit fs cert)
    (hS : MainStatics fs SB SK)
    (hV : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
      ChildrenOk bytecode seed w →
      VerifySubGoalsTB fs cert 0 seed s w (Pvs w) (childBv Bvf w))
    (hcnt : ∀ (rd : Reader) (t : Tree), t.Valid coreProgram rd [] [] → ∀ op,
      cnt t op ≤ t.weight (ω op) + jt op) (c5 s5 : Opcode → ℕ) (v5 : Opcode → ℕ → ℕ → ℕ)
    (h5 : ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ∀ op (rd : Reader)
      (t : Tree) (args rets : List E), t.name = (name% main_loop4) → t.Valid coreProgram rd args rets →
      t.BufsOk coreProgram → (mainPredsH s w (hDvNH w) (Pvs w)).T5 t →
        t.weight (ω op) ≤ l5Lin (c5 op) (s5 op) (v5 op) (work s w)) :
    MainComplete fs cert cnt (mainBudget fs SB SK Bvf ω H c5 s5 v5 jt) :=
  mainComplete_of_main fs cert cnt _ ω jt H hfs hxc hsc hrf hS hV hcnt
    (fun op s _ => (H op).clA + (H op).clS * s.claims.xmss.length)
    (fun op s _ => (H op).clA + (H op).clS * s.claims.sphincs.length)
    (fun op s w => (H op).dvA + (H op).dvR * (work s w).rawDaRows +
      (H op).dvP * (work s w).rawDaPad)
    (fun op s w => l5Lin (c5 op) (s5 op) (v5 op) (work s w))
    (fun _ s _ _ hl op rd t args rets hn hv hb hT =>
      clHonest_weight (H op) (n := s.claims.xmss.length) (claims_lt hl).1 rd t args rets
        hn hv hb hT)
    (fun _ s _ _ hl op rd t args rets hn hv hb hT =>
      clHonest_weight (H op) (n := s.claims.sphincs.length) (claims_lt hl).2 rd t args
        rets hn hv hb hT)
    (fun _ _ _ hr _ hnd op rd t args rets hn hv hb hT =>
      dvNH_weight (H op) hr hnd rd t args rets hn hv hb hT) h5
    (fun _ _ _ hr hl => B1.Main.Bmain_le fs SB SK Bvf hr hl)
    (fun _ _ _ _ hl op => mainCount_le (H op) (c5 op) (s5 op) (v5 op) (jt op) hl)

end
end LeanVM.Guest.Budget
