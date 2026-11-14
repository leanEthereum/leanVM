/-
  LeanVM.Guest.B1.Main.MainLoop3E

  `main_loop3` (leanSPHINCS) on an honest run within its static bound, by trees popping its iterations' entries and
  exact at every node (`mainGoalL4RE`, `mainGoalsRE_l4`).
-/

module

public import LeanVM.Guest.B1.Main.MainPopsSR
public import LeanVM.Guest.B1.Main.MainHonestE

/-!
# `main_loop3`, every node exact

`completeAtDTBR_of_relAtInT_on`: `completeAtDTBR_of_relAtInP_on` for any tree predicate. `main_loop3`'s own body has no
computed hint (`main_loop3_pinned`), so each of its nodes is exact (`main_loop3_exactAt`); its calls of
`verify_sig_lean_sphincs` are exact by `verifySigPE`. `mainGoalL4RE`: `mainGoalL4R` with every node exact;
`mainGoalsRE_l4`: `MainGoalsRE.l4`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (LowDef CompleteAtDTBR Returns disj_nil)

@[expose] public section

/-- **A callee placed by trees of `T rd` in a size fixed before the memory, its valid trees within `B`**, is complete
within `B` by those trees. -/
theorem _root_.LeanVM.Guest.B1.completeAtDTBR_of_relAtInT {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ}
    {f : String} {Lin : Layout} {args rets : List E} {B : ℕ} {T : Reader → Tree → Prop}
    (h : ∀ fp, ∃ n, ∀ rd, LowDef k rd → MemL rd Lin →
      RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL []) fp n f args rets (T rd))
    (hB : ∀ (rd : Reader) (t : Tree) (rets' : List E), t.name = f → t.Valid coreProgram rd args rets' →
      t.BufsOk coreProgram → t.total fs ≤ B) :
    CompleteAtDTBR fs cert k f Lin args (Returns rets) T B := by
  intro fp
  classical
  obtain ⟨n, hn⟩ := h fp
  by_cases hex : ∃ rd, LowDef k rd ∧ MemL rd Lin
  · obtain ⟨rd1, hl1, hL1⟩ := hex
    obtain ⟨t, ⟨hnm, hv, hb, -, ht, -⟩, -⟩ := hn rd1 hl1 hL1
    exact ⟨n, [], rets, [], ht ▸ hB rd1 t rets hnm hv hb, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => hn rd hl (by simpa using hL)⟩
  · exact ⟨0, [], rets, [], Nat.zero_le _, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

/-- `completeAtDTBR_of_relAtInT` on a precondition's bound (`TotalLeOn`). -/
theorem _root_.LeanVM.Guest.B1.completeAtDTBR_of_relAtInT_on {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ}
    {f : String} {Lin : Layout} {args rets : List E} {B : ℕ} {T : Reader → Tree → Prop} {Pre : List E → Prop}
    {Bf : List E → ℕ}
    (h : ∀ fp, ∃ n, ∀ rd, LowDef k rd → MemL rd Lin →
      RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL []) fp n f args rets (T rd))
    (hT : TotalLeOn coreProgram fs f Pre Bf) (hpre : Pre args) (hB : Bf args ≤ B) :
    CompleteAtDTBR fs cert k f Lin args (Returns rets) T B :=
  B1.completeAtDTBR_of_relAtInT h fun rd t rets' hn hv hb => (hT rd t args rets' hn hpre hv hb).trans hB

/-- `main_loop3`'s body has no computed hint. -/
theorem main_loop3_pinned :
    Stmt.blockNextOk isComputed pinsInverse (coreProgram.getD idx% «main_loop3» default).body = true := by
  rw [l4_body]; decide +kernel

theorem main_loop3_exactAt {rd : Reader} {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ (coreProgram.getD idx% «main_loop3» default).body = .ret es vs) (hes : ∀ e ∈ es, e.Holds rd σ) :
    ExactAt coreProgram rd name% «main_loop3» σ :=
  exactAt_of_walk l4_find hw (exact_of_pinned main_loop3_pinned hw hes rd)

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

/-- **`main_loop3` on an honest run, by trees popping its iterations' entries, every node exact.** -/
theorem mainGoalL4RE (hn : NodeRelation bytecode seed s w) (hl : GuestLimits s w) {SK : String → ℕ}
    (hT : TotalLeOn coreProgram fs name% «main_loop3» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «main_loop3» + fs name% «main_loop3»))
    (h0 : (hm fs fp seed s w).nrs ≠ 0) :
    CompleteAtDTBR fs cert 23 name% «main_loop3» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nrs, gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ (hm fs fp seed s w).nrx, (hm fs fp seed s w).a80, (hm fs fp seed s w).a119] (Returns [])
      (fun rd t => t.pops coreProgram rd =
        (List.range' 0 (hRawS s w).length).flatMap (l4Pops (rawSD fs fp hn ((hRawS s w)[0]'(Nat.pos_of_ne_zero h0))))
        ∧ t.Every (ExactAt coreProgram rd))
      ((hm fs fp seed s w).nrs * iterK fs SK name% «main_loop3» + fs name% «main_loop3») := by
  have hpos : 0 < (hRawS s w).length := Nat.pos_of_ne_zero h0
  have hb := regions_lt hl
  have hnl : (hRawS s w).length ≤ rY s w := sRaw_le hl.toDeployedLimits
  have hY : s.claims.sphincs.length ≤ rY s w := Nat.le_add_right _ _
  have hr : (hRawS s w).length < 2 ^ 34 := by omega
  have e : ([gen ^ 0, gen ^ (hRawS s w).length, gen ^ rY s w, gen ^ (hPos seed s w fs fp 2 + rX s w),
      gen ^ (hRawX s w).length, gen ^ hPos seed s w fs fp 1, gen ^ hPos seed s w fs fp 3] : List E) =
      [1, gen ^ (hm fs fp seed s w).nrs, gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ (hm fs fp seed s w).nrx, (hm fs fp seed s w).a80, (hm fs fp seed s w).a119] := by
    rw [pow_zero, pow_add (a := gen) (hPos seed s w fs fp 2)]
    rfl
  rw [← e]
  refine B1.completeAtDTBR_of_relAtInT_on (T := fun rd t => t.pops coreProgram rd =
      (List.range' 0 (hRawS s w).length).flatMap (l4Pops (rawSD fs fp hn (hRawS s w)[0])) ∧
        t.Every (ExactAt coreProgram rd)) (fun fp' => ⟨_, fun rd hlow hL =>
    (rawS_loopPQ fs cert (verifySigPE fs cert) (rawSD fs fp hn (hRawS s w)[0]) (by omega) hr hlow hL
      (fun _ _ _ hw hes => main_loop3_exactAt hw hes) 0 hpos fp'
      (fp' + ((hRawS s w).length - 0 + 1) * fs name% «main_loop3»)).relAtInPE⟩) hT
    (loopPre_pow hpos (by omega) _) ?_
  simp [logG_gen (show (hRawS s w).length < 2 ^ 64 - 1 by omega)]
  rfl

/-- **`MainGoalsRE.l4`**, `q` popping the raw leanSPHINCS signatures' entries. -/
theorem mainGoalsRE_l4 (hn : NodeRelation bytecode seed s w) (hl : GuestLimits s w) {SB SK : String → ℕ}
    {Bv : ℕ → ℕ} {Pvs : ℕ → Tree → Prop} {q : MainPops} (hS : MainStaticsMain fs SB SK)
    (hq : ∀ rd, q.p3 rd = sRawPops s w) : (hm fs fp seed s w).nrs ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop3» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nrs, gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ (hm fs fp seed s w).nrx, (hm fs fp seed s w).a80, (hm fs fp seed s w).a119] (Returns [])
      (mainPredsHP fs SB SK Bv Pvs s w q).withExact.P3
      ((hm fs fp seed s w).nrs * iterK fs SK name% «main_loop3» + fs name% «main_loop3») := fun h0 =>
  (mainGoalL4RE hn hl hS.l4 h0).mono le_rfl fun rd t h => ⟨h.1.trans (by
    rw [hq, sRawPops_eq ((hRawS s w)[0]'(Nat.pos_of_ne_zero h0))]
    rfl), h.2⟩

end
end LeanVM.Guest.B1.Main
