/-
  LeanVM.Guest.B1.Terminal.TermWeight

  `check_opening_terminal` complete, placed, within its bound, by a tree within its weights: its
  callees by name within their words (`completeAt_flatDepRBT`), each callee's weight by its
  certificate or, `check_opening_terminal_loop0`'s and `ring_switch_weight`'s, by its words.
-/

module

public import LeanVM.Guest.B1.Terminal.TermCompleteB
public import LeanVM.Guest.B1.Terminal.KidsDepBT
public import LeanVM.Guest.Budget.Weighs
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.LitRef

/-!
# The terminal within its weights

`termNames D`: the terminal's callees' names, in call order (the column selectors' by the columns'
sizes `D.KC`). `termWs`: their weight bounds. `term_weight_le`: a node of `Budget.FlatShape` for
`termNames`, `termBs` weighs at most its frame's weight and `termWs` at each `ω i`.
`check_opening_terminal_completeAtBW`: `check_opening_terminal_completeAtB` by a tree within those
weights.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **The terminal's callees' names**, in call order. -/
def termNames (D : TermData) : List String :=
  ["eq_prefix_chain", "eq_prefix_chain", name% «check_opening_terminal_loop0», "selector_tables"] ++
    (List.range Tables.nCommittedCols).map (fun c => Tables.lName "column_selector" (D.KC.getD c 0)) ++
    ["eq_prefix_chain", "ring_switch_weight", "eq_prefix_chain"]

/-- **The terminal's callees' weight bounds**, in call order. -/
def termWs {ι : Type} (Weqc W15 Wst Wcs Wrsw : ι → ℕ) (i : ι) : List ℕ :=
  [Weqc i, Weqc i, W15 i, Wst i] ++ List.replicate Tables.nCommittedCols (Wcs i) ++ [Weqc i, Wrsw i, Weqc i]

theorem termKids_names (Lin : Main.Layout) (D : TermData) (b0 : ℕ) :
    List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (termKids Lin D b0) (termNames D) := by
  unfold termKids termNames
  refine List.rel_append (List.rel_append ?_ ?_) ?_
  · exact .cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) .nil)))
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun _ _ _ => rfl
  · exact .cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) .nil))

/-- **The terminal's node weighs at most** its frame's weight and `termWs` at each `ω i`. -/
theorem term_weight_le {ι : Type} (ω : ι → String → ℕ) (Weqc W15 Wst Wcs Wrsw : ι → ℕ)
    (hEqcW : ∀ i, WeightLe coreProgram (ω i) "eq_prefix_chain" fun _ => Weqc i)
    (hStW : ∀ i, WeightLe coreProgram (ω i) "selector_tables" fun _ => Wst i)
    (hCsW : ∀ i, ∀ κ' < 31, WeightLe coreProgram (ω i) (Tables.lName "column_selector" κ')
      fun _ => Wcs i)
    {K15 Brs Beqc Bcs : ℕ}
    (h15W : ∀ i (rd : Reader) (t : Tree) (args rets : List E),
        t.name = name% «check_opening_terminal_loop0» →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ (32 * K15 + fs name% «check_opening_terminal_loop0») → t.weight (ω i) ≤ W15 i)
    (hrswW : ∀ i (rd : Reader) (t : Tree) (args rets : List E), t.name = "ring_switch_weight" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ fs "ring_switch_weight" + lit% termRswChain + Brs → t.weight (ω i) ≤ Wrsw i)
    {D : TermData} (hKC : ∀ c < Tables.nCommittedCols, D.KC.getD c 0 < 31) {t : Tree}
    (h : Budget.FlatShape coreProgram "check_opening_terminal"
      (List.zipWith (Budget.NamedWithin fs) (termNames D) (termBs fs Beqc K15 Bcs Brs)) t)
    {rd : Reader} {args rets : List E} (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (i : ι) :
    t.weight (ω i) ≤ ω i "check_opening_terminal" + (termWs Weqc W15 Wst Wcs Wrsw i).sum := by
  refine Budget.FlatShape.weight_le (ω i) _ h hv hb
    (by simp [termNames, termBs, termWs, Tables.nCommittedCols]) ?_
  intro j hT hW rd' t' args' rets' hv' hb' hTj
  rw [List.getElem_zipWith] at hTj
  obtain ⟨hn, htot⟩ := hTj
  have hj : j < 101 := by simpa [termWs, Tables.nCommittedCols] using hW
  by_cases h4 : j < 4
  · interval_cases j <;>
      simp only [termNames, termBs, termWs, List.append_assoc, List.cons_append,
        List.getElem_cons_zero, List.getElem_cons_succ] at hn htot ⊢
    · exact hEqcW i rd' t' args' rets' hn hv' hb'
    · exact hEqcW i rd' t' args' rets' hn hv' hb'
    · exact h15W i rd' t' args' rets' hn hv' hb' htot
    · exact hStW i rd' t' args' rets' hn hv' hb'
  by_cases h98 : j < 98
  · have e1 : (termNames D)[j]'(by simp [termNames, Tables.nCommittedCols]; omega) =
        Tables.lName "column_selector" (D.KC.getD (j - 4) 0) := by
      simp only [termNames, List.append_assoc]
      rw [List.getElem_append_right (by simp; omega), List.getElem_append_left
        (by simp [Tables.nCommittedCols]; omega)]
      simp
    have e2 : (termWs Weqc W15 Wst Wcs Wrsw i)[j]'hW = Wcs i := by
      simp only [termWs, List.append_assoc]
      rw [List.getElem_append_right (by simp; omega), List.getElem_append_left
        (by simp [Tables.nCommittedCols]; omega)]
      simp
    rw [e1] at hn
    rw [e2]
    exact hCsW i _ (hKC _ (by simp [Tables.nCommittedCols]; omega)) rd' t' args' rets' hn hv' hb'
  · have hj' : j = 98 ∨ j = 99 ∨ j = 100 := by omega
    rcases hj' with rfl | rfl | rfl <;>
      simp [termNames, termBs, termWs, Tables.nCommittedCols, List.getElem_append_right] at hn htot ⊢
    · exact hEqcW i rd' t' args' rets' hn hv' hb'
    · exact hrswW i rd' t' args' rets' hn hv' hb' htot
    · exact hEqcW i rd' t' args' rets' hn hv' hb'

/-- **`check_opening_terminal` is complete, placed, within a bound, by a tree within its weights**
(`check_opening_terminal_completeAtB` by a node of `Budget.FlatShape`): at each `ω i`, its frame's
weight, its four prefix chains' `Weqc i`, `check_opening_terminal_loop0`'s `W15 i`,
`selector_tables`' `Wst i`, each column selector's `Wcs i` and `ring_switch_weight`'s `Wrsw i`, the
last two by their trees'
words (`h15W`, `hrswW`). -/
theorem check_opening_terminal_completeAtBW (κ : ℕ) (hκ : 6 ≤ κ) (B : TermBases)
    (Lin : Main.Layout)
    {layout : Layout} {bus : BusResult} {claims : List ColumnClaim} {out : ColumnClaim} {lam : E}
    {ringPoint coeffs oodPoint x : List E} {rm gmu gzcn glm gtau lamCl inner yr target gm : E} {nc : ℕ}
    (hnc : nc ≤ 40) (hgz : gzcn = gen ^ nc)
    (hpre : ∀ rd, LowDef κ rd → MemL rd Lin → TermPre rd layout bus claims out lam ringPoint coeffs
      oodPoint x (termArgs B rm gmu gzcn glm gtau lamCl inner yr target gm))
    (hreg : ∀ i, TermRegion B bus.point.length nc (layout.tableLogHeights.getD opKeccak 0)
      layout.stackLog i → RegionL Lin i)
    (hbus : bus.point.length ≤ 34)
    (hfin : (inner + stackWeight layout (openedClaims claims [out]) ringPoint coeffs oodPoint lam x) *
      yr = target)
    {Beqc K15 Bcs Brs : ℕ} (hEqc : TotalLe coreProgram fs "eq_prefix_chain" fun _ => Beqc)
    (hL15 : TotalLeOn coreProgram fs name% «check_opening_terminal_loop0» LoopPre
      fun a => logG (a.getD 1 0) * K15 + fs name% «check_opening_terminal_loop0»)
    (hCsF : ∀ κ' < 31, fs (Tables.lName "column_selector" κ') ≤ Bcs)
    (hrs : RsBound fs Brs)
    {ι : Type} (ω : ι → String → ℕ) (Weqc W15 Wst Wcs Wrsw : ι → ℕ)
    (hEqcW : ∀ i, WeightLe coreProgram (ω i) "eq_prefix_chain" fun _ => Weqc i)
    (hStW : ∀ i, WeightLe coreProgram (ω i) "selector_tables" fun _ => Wst i)
    (hCsW : ∀ i, ∀ κ' < 31, WeightLe coreProgram (ω i) (Tables.lName "column_selector" κ')
      fun _ => Wcs i)
    (h15W : ∀ i (rd : Reader) (t : Tree) (args rets : List E),
        t.name = name% «check_opening_terminal_loop0» →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ (32 * K15 + fs name% «check_opening_terminal_loop0») → t.weight (ω i) ≤ W15 i)
    (hrswW : ∀ i (rd : Reader) (t : Tree) (args rets : List E), t.name = "ring_switch_weight" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ fs "ring_switch_weight" + lit% termRswChain + Brs → t.weight (ω i) ≤ Wrsw i) :
    CompleteAtDTB fs cert κ "check_opening_terminal" Lin
      (termArgs B rm gmu gzcn glm gtau lamCl inner yr target gm) (Returns [])
      (fun t => ∀ i, Budget.WeighsLe coreProgram (ω i)
        (ω i "check_opening_terminal" + (termWs Weqc W15 Wst Wcs Wrsw i).sum) t)
      (fs "check_opening_terminal" + 177 + 4 * Beqc + (32 * K15 + fs
          name% «check_opening_terminal_loop0») +
        (fs "selector_tables" + 512) + 94 * Bcs + (fs "ring_switch_weight" + lit% termRswChain + Brs)) := by
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lin
  swap
  · intro fp
    exact ⟨0, [], [], [], Nat.zero_le _, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => absurd ⟨rd, hl, by simpa using hL⟩ hex⟩
  obtain ⟨rd0, hl0, hm0⟩ := hex
  obtain ⟨chis, rfl, hchis, S⟩ := term_setup κ B Lin hnc hgz hpre hreg hbus hl0 hm0
  set D := termD B layout bus out ringPoint coeffs x chis oodPoint rm gmu gzcn glm gtau gm lamCl
  refine (completeAt_flatDepRBT find_term term_not_loop κ Lin _ [] term_body' term_flat term_addrs
    (by decide +kernel) [35, 35, 35, 41, 31] (fun _ => termOwn D) (fun _ => S.own)
    (fun fp => termKids Lin D (fp + fs "check_opening_terminal")) (termNames D)
    (termBs fs Beqc K15 Bcs Brs) (fun fp => termKids_names Lin D _)
    (fun fp => termKids_completeB κ hκ Lin D _ S.reg S.zl S.cl S.xl S.τl S.ol S.rl S.cf S.gmu S.gz
      S.glm S.gtau S.m1 S.m S.KC S.OF S.rd S.odl S.gm S.rdO hEqc hL15 hCsF hrs)
    (fun fp outs _ => termKids_regions Lin D _ S.reg S.τl S.rl S.cf S.xl outs)
    (fun fp outs _ rd hl hB hLin hLo => S.mem _ outs rd hl hB hLin hLo)
    (fun fp outs hlen' ho rd hl hB hLin _ => term_sigma B Lin (fp + fs "check_opening_terminal") outs rd
      (hpre rd hl hLin) (hchis rd hl hLin) hgz S.cl hreg hbus hfin (by rw [hlen', termKids_length]) ho
      hB)).mono (le_of_eq ?_) fun t ht i rd' _ _ hv hb =>
      term_weight_le ω Weqc W15 Wst Wcs Wrsw hEqcW hStW hCsW h15W hrswW S.KC ht hv hb i
  rw [termBs_sum]
  simp only [List.sum_cons, List.sum_nil]
  omega


end
end LeanVM.Guest.B1.VerifySub
