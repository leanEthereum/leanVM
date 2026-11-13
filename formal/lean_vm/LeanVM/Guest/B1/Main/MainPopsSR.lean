/-
  LeanVM.Guest.B1.Main.MainPopsSR

  `main`'s loops' pops for `mainComplete_budgetP`: route S for the duplicate claims' loops, route R for the raw signatures' loops, and their segments of the honest pushes.
-/

module

public import LeanVM.Guest.Budget.FinalP
public import LeanVM.Guest.B1.Main.MainGoalsRawR
public import LeanVM.Guest.B1.Main.SphincsAtP
public import LeanVM.Guest.B1.Main.RawPushes
public import LeanVM.Guest.B1.Main.DupPops
public import LeanVM.Guest.B1.Da.DaPops

/-!
# `main`'s loops with their pops

The honest entries, none depending on the memory (`mainPopsH`): `dupXPops`, `dupSPops` (the duplicate claims' cells), `xRawPops`, `sRawPops` (each raw signature's index and check, `xRawPops_eq`, `sRawPops_eq` against `rawXD`, `rawSD`).

* `mainPopsS_l1`, `mainPopsS_l2`: `MainPopsS`' fields for `main_loop0`, `main_loop1` (`mfL1_pops`, `mfL2_pops`);
* `mainGoalL4R`: `main_loop3` on an honest run within its static bound, by trees popping its iterations' entries;
* `mainGoalsRR_l3`, `mainGoalsRR_l4`: `MainGoalsRR`'s fields for `main_loop2`, `main_loop3` (`mainGoalL3R`, `mainGoalL4R`);
* `mainSegs_d0`, `mainSegs_d1`, `mainSegs_r2`, `mainSegs_r3`: `MainSegs`' fields for the four loops, a loop not entered popping `[]`;
* `mainSegs_da`, `mainSegs_agg`: `MainSegs`' fields for `da_verify` popping `daPopsH` (`dv_pops`' entries on the honest columns) and `aggregate_claims` popping `batchPushes`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (claimCells)
open LeanVM.Guest.B1 (LowDef CompleteAtDTBR Returns completeAtDTBR_of_relAtInP_on)

@[expose] public section

/-! ## The honest entries -/

/-- The duplicate leanXMSS claims' cells. -/
def dupXPops (s : NodeStatement) (w : NodeWitness) : List Pop :=
  (xPlan s w).duplicates.map fun c ↦ ("dup_claims", claimCells c.1.root c.1.parameter c.2)

/-- The duplicate leanSPHINCS claims' cells. -/
def dupSPops (s : NodeStatement) (w : NodeWitness) : List Pop :=
  (sPlan s w).duplicates.map fun c ↦ ("dup_claims", claimCells c.1.publicSeed c.1.root c.2)

/-- Raw leanXMSS signature `i`'s entries, `d0` past the end. -/
def xRawPop (s : NodeStatement) (w : NodeWitness) (d0 : LeanXmssClaim × LeanXmss.Signature) (i : ℕ) : List Pop :=
  ("raw_index", [gen ^ (slotsOf (xPlan s w)).getD i 0]) ::
    Sig.xSegPops ((hRawX s w).getD i d0).1.1 ((hRawX s w).getD i d0).1.2 ((hRawX s w).getD i d0).2

/-- Raw leanSPHINCS signature `j`'s entries, `d0` past the end. -/
def sRawPop (s : NodeStatement) (w : NodeWitness) (d0 : LeanSphincsClaim × Sphincs.Signature) (j : ℕ) : List Pop :=
  ("sp_raw_index", [gen ^ (slotsOf (sPlan s w)).getD j 0]) ::
    Sig.spSegPops ((hRawS s w).getD j d0).1.1 ((hRawS s w).getD j d0).1.2 ((hRawS s w).getD j d0).2

/-- **`da_verify`'s honest entries**: its shape, its challenge, its columns' cells. -/
def daPopsH (w : NodeWitness) : List Pop :=
  (w.daMatrix.map fun p => ("da_shape", [gen ^ p.2.rows.length, gen ^ Da.wLog p.2]) ::
    ("da_challenge", [p.1.membershipChallenge]) :: (List.range 128).flatMap (Da.daColPops p.2)).getD []

/-- **The raw leanXMSS signatures' entries.** -/
def xRawPops (s : NodeStatement) (w : NodeWitness) : List Pop :=
  match hRawX s w with
  | [] => []
  | d0 :: _ => (List.range' 0 (hRawX s w).length).flatMap (xRawPop s w d0)

/-- **The raw leanSPHINCS signatures' entries.** -/
def sRawPops (s : NodeStatement) (w : NodeWitness) : List Pop :=
  match hRawS s w with
  | [] => []
  | d0 :: _ => (List.range' 0 (hRawS s w).length).flatMap (sRawPop s w d0)

/-- **`main`'s callees' honest entries**, the claim lists' digests' and the children's loop's given. -/
def mainPopsH (px ps p5 : Reader → List Pop) (s : NodeStatement) (w : NodeWitness) : MainPops :=
  ⟨px, ps, fun _ => dupXPops s w, fun _ => dupSPops s w, fun _ => xRawPops s w, fun _ => sRawPops s w,
    fun _ => daPopsH w, p5, fun _ => Hints.batchPushes w.batchingHints⟩

variable {fs : String → ℕ} {cert : String → V → ℕ} {fp : ℕ} {seed : Digest} {s : NodeStatement}
  {w : NodeWitness} {bytecode : List K}

theorem xRawPops_eq (d0 : LeanXmssClaim × LeanXmss.Signature) :
    xRawPops s w = (List.range' 0 (hRawX s w).length).flatMap (xRawPop s w d0) := by
  unfold xRawPops
  split
  · next h => rw [h]; rfl
  · refine List.flatMap_congr fun i hi => ?_
    have hi : i < (hRawX s w).length := by simp at hi; omega
    simp only [xRawPop, List.getD_eq_getElem _ _ hi]

theorem sRawPops_eq (d0 : LeanSphincsClaim × Sphincs.Signature) :
    sRawPops s w = (List.range' 0 (hRawS s w).length).flatMap (sRawPop s w d0) := by
  unfold sRawPops
  split
  · next h => rw [h]; rfl
  · refine List.flatMap_congr fun i hi => ?_
    have hi : i < (hRawS s w).length := by simp at hi; omega
    simp only [sRawPop, List.getD_eq_getElem _ _ hi]

/-! ## Route S: the duplicate claims' loops -/

/-- **`MainPopsS.l1`**, `q` popping the duplicate leanXMSS claims. -/
theorem mainPopsS_l1 (hl : GuestLimits s w) {q : MainPops} (hq : ∀ rd, q.p0 rd = dupXPops s w) :
    (hm fs fp seed s w).nxd ≠ 0 → ∀ rd, LowDef 20 rd → MemL rd (hLmain fs fp seed s w) →
      ∀ (t : Tree) rets, t.name = name% «main_loop0» → t.Valid coreProgram rd
        [1, gen ^ (hm fs fp seed s w).nxd, (hm fs fp seed s w).a77, gen ^ (hm fs fp seed s w).nlx] rets →
        t.pops coreProgram rd = q.p0 rd := fun hn rd _ hL t rets htn hv => by
  rw [hq]
  exact mfL1_pops hl hn hL t rets htn hv

/-- **`MainPopsS.l2`**, `q` popping the duplicate leanSPHINCS claims. -/
theorem mainPopsS_l2 (hl : GuestLimits s w) {q : MainPops} (hq : ∀ rd, q.p1 rd = dupSPops s w) :
    (hm fs fp seed s w).nsd ≠ 0 → ∀ rd, LowDef 20 rd → MemL rd (hLmain fs fp seed s w) →
      ∀ (t : Tree) rets, t.name = name% «main_loop1» → t.Valid coreProgram rd
        [1, gen ^ (hm fs fp seed s w).nsd, (hm fs fp seed s w).a80, gen ^ (hm fs fp seed s w).nls] rets →
        t.pops coreProgram rd = q.p1 rd := fun hn rd _ hL t rets htn hv => by
  rw [hq]
  exact mfL2_pops hl hn hL t rets htn hv

/-! ## Route R: the raw signatures' loops -/

/-- **`main_loop3` on an honest run, by trees popping its iterations' entries.** -/
theorem mainGoalL4R (hn : NodeRelation bytecode seed s w) (hl : GuestLimits s w) {SK : String → ℕ}
    (hT : TotalLeOn coreProgram fs name% «main_loop3» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «main_loop3» + fs name% «main_loop3»))
    (h0 : (hm fs fp seed s w).nrs ≠ 0) :
    CompleteAtDTBR fs cert 23 name% «main_loop3» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nrs, gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ (hm fs fp seed s w).nrx, (hm fs fp seed s w).a80, (hm fs fp seed s w).a119] (Returns [])
      (fun rd t => t.pops coreProgram rd =
        (List.range' 0 (hRawS s w).length).flatMap (l4Pops (rawSD fs fp hn ((hRawS s w)[0]'(Nat.pos_of_ne_zero h0)))))
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
  refine completeAtDTBR_of_relAtInP_on (fun fp' => ⟨_, fun rd hlow hL =>
    (rawS_loopP fs cert (verifySigP fs cert) (rawSD fs fp hn (hRawS s w)[0]) (by omega) hr hlow hL 0 hpos fp'
      (fp' + ((hRawS s w).length - 0 + 1) * fs name% «main_loop3»)).relAtInP⟩) hT
    (loopPre_pow hpos (by omega) _) ?_
  simp [logG_gen (show (hRawS s w).length < 2 ^ 64 - 1 by omega)]
  rfl

/-- **`MainGoalsRR.l3`**, `q` popping the raw leanXMSS signatures' entries. -/
theorem mainGoalsRR_l3 (hn : NodeRelation bytecode seed s w) (hl : GuestLimits s w) {SB SK : String → ℕ}
    {Bv : ℕ → ℕ} {Pvs : ℕ → Tree → Prop} {q : MainPops} (hS : MainStaticsMain fs SB SK)
    (hq : ∀ rd, q.p2 rd = xRawPops s w) : (hm fs fp seed s w).nrx ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop2» (hLmain fs fp seed s w)
      ([1, gen ^ (hm fs fp seed s w).nrx, gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        (hm fs fp seed s w).a117, (hm fs fp seed s w).a77] ++ lxTagWords) (Returns [])
      (mainPredsHP fs SB SK Bv Pvs s w q).P2
      ((hm fs fp seed s w).nrx * iterK fs SK name% «main_loop2» + fs name% «main_loop2») := fun h0 =>
  (mainGoalL3R hn hl hS.l3 h0).mono le_rfl fun rd t h => h.trans (by
    rw [hq, xRawPops_eq ((hRawX s w)[0]'(Nat.pos_of_ne_zero h0))]
    rfl)

/-- **`MainGoalsRR.l4`**, `q` popping the raw leanSPHINCS signatures' entries. -/
theorem mainGoalsRR_l4 (hn : NodeRelation bytecode seed s w) (hl : GuestLimits s w) {SB SK : String → ℕ}
    {Bv : ℕ → ℕ} {Pvs : ℕ → Tree → Prop} {q : MainPops} (hS : MainStaticsMain fs SB SK)
    (hq : ∀ rd, q.p3 rd = sRawPops s w) : (hm fs fp seed s w).nrs ≠ 0 →
    CompleteAtDTBR fs cert 23 name% «main_loop3» (hLmain fs fp seed s w)
      [1, gen ^ (hm fs fp seed s w).nrs, gen ^ ((hm fs fp seed s w).nls + (hm fs fp seed s w).nsd),
        (hm fs fp seed s w).a117 * gen ^ ((hm fs fp seed s w).nlx + (hm fs fp seed s w).nxd),
        gen ^ (hm fs fp seed s w).nrx, (hm fs fp seed s w).a80, (hm fs fp seed s w).a119] (Returns [])
      (mainPredsHP fs SB SK Bv Pvs s w q).P3
      ((hm fs fp seed s w).nrs * iterK fs SK name% «main_loop3» + fs name% «main_loop3») := fun h0 =>
  (mainGoalL4R hn hl hS.l4 h0).mono le_rfl fun rd t h => h.trans (by
    rw [hq, sRawPops_eq ((hRawS s w)[0]'(Nat.pos_of_ne_zero h0))]
    rfl)

/-! ## The segments -/

theorem mainSegs_d0 {q : MainPops} (hq : ∀ rd, q.p0 rd = dupXPops s w) (rd : Reader) :
    SameStreams (if (hm fs 0 seed s w).nxd = 0 then [] else q.p0 rd)
      ((xPlan s w).duplicates.map fun c ↦ ("dup_claims", claimCells c.1.root c.1.parameter c.2)) := by
  rw [hq]
  split
  · next h => rw [List.eq_nil_of_length_eq_zero (show (xPlan s w).duplicates.length = 0 from h)]; exact SameStreams.refl _
  · exact SameStreams.refl _

theorem mainSegs_d1 {q : MainPops} (hq : ∀ rd, q.p1 rd = dupSPops s w) (rd : Reader) :
    SameStreams (if (hm fs 0 seed s w).nsd = 0 then [] else q.p1 rd)
      ((sPlan s w).duplicates.map fun c ↦ ("dup_claims", claimCells c.1.publicSeed c.1.root c.2)) := by
  rw [hq]
  split
  · next h => rw [List.eq_nil_of_length_eq_zero (show (sPlan s w).duplicates.length = 0 from h)]; exact SameStreams.refl _
  · exact SameStreams.refl _

theorem mainSegs_r2 (hn : NodeRelation bytecode seed s w) (hl : GuestLimits s w) {q : MainPops}
    (hq : ∀ rd, q.p2 rd = xRawPops s w) (rd : Reader) :
    SameStreams (if (hm fs 0 seed s w).nrx = 0 then [] else q.p2 rd)
      ((w.xmssSignatures.zip (xPlan s w).directSlots).flatMap
        (fun (c, slot) ↦ ("raw_index", [Hints.count slot]) :: Hints.xmssHints c.1.1 c.1.2 c.2)) := by
  split
  · next h =>
    rw [List.eq_nil_of_length_eq_zero (show w.xmssSignatures.length = 0 from h), List.zip_nil_left, List.flatMap_nil]
    exact SameStreams.refl _
  · next h =>
    have hp : 0 < (hRawX s w).length := Nat.pos_of_ne_zero h
    rw [hq, xRawPops_eq ((hRawX s w)[0]'hp)]
    exact rawX_pops_sameStreams fs 0 hn hl _

theorem mainSegs_r3 (hn : NodeRelation bytecode seed s w) (hl : GuestLimits s w) {q : MainPops}
    (hq : ∀ rd, q.p3 rd = sRawPops s w) (rd : Reader) :
    SameStreams (if (hm fs 0 seed s w).nrs = 0 then [] else q.p3 rd)
      ((w.sphincsSignatures.zip (sPlan s w).directSlots).flatMap
        (fun (c, slot) ↦ ("sp_raw_index", [Hints.count slot]) :: Hints.sphincsHints c.1.1 c.1.2 c.2)) := by
  split
  · next h =>
    rw [List.eq_nil_of_length_eq_zero (show w.sphincsSignatures.length = 0 from h), List.zip_nil_left,
      List.flatMap_nil]
    exact SameStreams.refl _
  · next h =>
    have hp : 0 < (hRawS s w).length := Nat.pos_of_ne_zero h
    rw [hq, sRawPops_eq ((hRawS s w)[0]'hp)]
    exact rawS_pops_sameStreams fs 0 hn hl _

theorem mainSegs_da (hn : NodeRelation bytecode seed s w) {q : MainPops} (hq : ∀ rd, q.pd rd = daPopsH w)
    (rd : Reader) : w.daMatrix.isSome → SameStreams (q.pd rd) (daSeg w) := by
  intro hs
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨-, hda, -, -⟩ := hn
  rw [DaDigestHeld, hp] at hda
  have hw := hda.2
  have hr1 := hw.1
  have hr : p.2.rows.length ≤ 1024 := hw.2.1
  have hL : 2 ^ Da.wLog p.2 = LeanDa.paddedRowCount p.2.rows.length := rfl
  have hL10 : Da.wLog p.2 ≤ 10 := by
    obtain ⟨-, hhi⟩ := Da.nPad_bounds hr1
    have hlt : 2 ^ Da.wLog p.2 < 2 ^ 11 := by
      calc 2 ^ Da.wLog p.2 < 2 * p.2.rows.length := hL ▸ hhi
        _ ≤ 2 ^ 11 := by norm_num; omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  rw [hq, daPopsH, daSeg, hp, Option.map_some, Option.map_some, Option.getD_some, Option.getD_some]
  exact Da.daPops_sameStreams p.1 p.2 hr hL10

theorem mainSegs_agg {q : MainPops} (hq : ∀ rd, q.pa rd = Hints.batchPushes w.batchingHints) (rd : Reader) :
    w.children ≠ [] → SameStreams (q.pa rd) (Hints.batchPushes w.batchingHints) := fun _ => by
  rw [hq]
  exact SameStreams.refl _

end
end LeanVM.Guest.B1.Main
