module

public import LeanVM.Guest.Complete.LoopFHA
public import LeanVM.Guest.B1.Sig.PopsKit

/-!
# Loop helpers with heap hints, placed, with their pops

`loopFHP_callAtA`: `loopFH_callAtA` by a tree popping its iterations' entries in order, iteration
`j`'s block popping `ps j` (`loopPopsFrom ps m j`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Digest LeanVM.Protocol.Verifier
open LeanVM.Guest.Value
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- The entries of a loop's iterations `j ..< m`, iteration `i` popping `ps i`. -/
def loopPopsFrom (ps : ℕ → List Pop) (m j : ℕ) : List Pop := (List.range' j (m - j)).flatMap ps

theorem loopPopsFrom_succ {ps : ℕ → List Pop} {m j : ℕ} (h : j < m) :
    loopPopsFrom ps m j = ps j ++ loopPopsFrom ps m (j + 1) := by
  unfold loopPopsFrom
  rw [show m - j = (m - (j + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons]

/-- The callees' entries of a node whose one call is its tail, entered or a phantom. -/
theorem popsKids_tail {rd : Reader} {σ : Val} {c : Call} {ts : List Tree} {Q : Reader → Tree → Prop}
    {kn : List Pop} (hv : Tree.KidsValid coreProgram rd σ [c] ts) (hq : KidsPost rd [Q] [c] ts)
    (hT : c.taken = true → ∀ t, Q rd t → t.pops coreProgram rd = kn) (hF : c.taken = false → kn = []) :
    Tree.popsKids coreProgram rd ts = [kn] := by
  match ts, hv with
  | [t], hv =>
    rw [Tree.KidsValid] at hv
    obtain ⟨-, ht, -⟩ := hv
    simp only [Tree.popsKids, List.cons.injEq, and_true]
    by_cases hc : c.taken = true
    · exact hT hc t ((kidsPost_cons.mp hq).1 hc)
    · have hc' : c.taken = false := by simpa using hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at ht
      obtain ⟨⟨f, σ', rfl⟩, -⟩ := ht
      rw [hF (by simpa using hc), Tree.pops]
  | [], hv => exact absurd hv (by simp [Tree.KidsValid])
  | _ :: _ :: _, hv => exact absurd hv (by simp [Tree.KidsValid])

set_option maxRecDepth 10000 in
/-- **`loopFH_callAtA`, its tree popping its iterations' entries**: iteration `j`'s block pops `ps j`. -/
theorem loopFHP_callAtA {k : ℕ} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShapeF fn f = true) (hlp : coreProgram.loop f = true) (hpl : (loopPre fn).all loopPlainHB = true)
    {m : ℕ} (hm : m < 2 ^ 34) {ps : ℕ → List Pop} {rest : List E} {R : ℕ → Prop} {Pre : Reader → Prop}
    (hblk : ∀ j < m, ∀ rd, LowDef k rd → Pre rd → ∃ σ : Val, fn.params.map σ = gen ^ j :: gen ^ m :: rest ∧
      (∀ s ∈ loopPre fn, SOk rd σ s) ∧
      (∀ q ∈ (loopPre fn).filterMap stmtLoad?, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 = addressOfIndex i ∧ R i) ∧
      (∀ A ∈ heapHintAddrs σ ((loopPre fn).flatMap (slEvs σ)), ∃ i, A = addressOfIndex i ∧ R i) ∧
      evPops rd σ ((loopPre fn).flatMap (slEvs σ)) = ps j) :
    ∀ j < m, ∀ fp c, fp + lpBlk fs f (m - j) ≤ c →
      CallAtA fs al cert k f (gen ^ j :: gen ^ m :: rest) [] R (fun _ => False) (fun _ => True) Pre
        (fun rd t => t.pops coreProgram rd = loopPopsFrom ps m j) (lpBlk fs f (m - j)) fp c c := by
  simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨h2, hpar⟩, hok⟩ := hok
  cases hsl : splitLoopF fn.body with
  | none => simp [hsl] at hok
  | some x =>
  obtain ⟨pre, cv, g, args⟩ := x
  simp only [hsl, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hgf, hlen⟩, htail⟩, hg⟩, hc⟩ := hok
  subst g
  obtain ⟨hbody, -⟩ := splitLoopF_eq hsl
  have hpre : loopPre fn = pre := by simp [loopPre, hsl]
  rw [hpre] at hpl hblk
  cases hpq : addOf (atomsIn pre) cv with
  | none => simp [hpq] at hc
  | some pq =>
  obtain ⟨p, q⟩ := pq
  simp only [hpq, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hp', rfl⟩ := hc
  obtain ⟨n, hn⟩ : ∃ n, fn.params.length = n + 2 := ⟨fn.params.length - 2, by omega⟩
  obtain ⟨a0, rs, rfl⟩ : ∃ a0 rs, args = a0 :: rs := by
    cases args with
    | nil => simp at hlen; omega
    | cons a0 rs => exact ⟨a0, rs, rfl⟩
  simp only [List.headD_cons] at hg
  simp only [List.tail_cons] at htail
  set P := pre ++ [Stmt.callIf cv f (a0 :: rs)] with hP
  have hbP : fn.body = P ++ [.ret []] := by rw [hbody, hP, List.append_assoc]; rfl
  have hpreA : ∀ s ∈ pre, ∃ a, s = .atom a := by
    intro s hs
    have := List.all_eq_true.mp hpl s hs
    cases s with
    | atom a => exact ⟨a, rfl⟩
    | _ => simp [loopPlainHB] at this
  have hsP : P.all Stmt.straight = true := by
    refine List.all_eq_true.mpr fun s hs => ?_
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨a, rfl⟩ := hpreA s hs; rfl
    · simp at hs; subst hs; rfl
  have hpP : P.all plainH = true := by
    refine List.all_eq_true.mpr fun s hs => ?_
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨a, rfl⟩ := hpreA s hs
      have := List.all_eq_true.mp hpl _ hs
      simpa [loopPlainHB] using this
    · simp at hs; subst hs; rfl
  have hloadsP : P.filterMap stmtLoad? = pre.filterMap stmtLoad? := by
    rw [hP, List.filterMap_append]; simp [stmtLoad?]
  -- what a valuation of the block gives
  have hvals : ∀ (j : ℕ) (rd : Reader) (σ : Val), fn.params.map σ = gen ^ j :: gen ^ m :: rest →
      (∀ s ∈ pre, SOk rd σ s) →
      σ cv = gen ^ (j + 1) + gen ^ m ∧ (a0 :: rs).map σ = gen ^ (j + 1) :: gen ^ m :: rest := by
    intro j rd σ hpσ hs
    have hat : ∀ a ∈ atomsIn pre, a.Holds rd σ := by
      intro a ha
      obtain ⟨s, hs', hsa⟩ := List.mem_filterMap.mp ha
      cases s <;> simp only [reduceCtorEq, Option.some.injEq] at hsa
      subst hsa
      exact hs _ hs'
    have hx0 : σ (V.n 0) = gen ^ j := by
      have := congrArg List.head? hpσ
      rw [hpar, hn, List.range_succ_eq_map] at this
      simpa using this
    have hx1 : σ (V.n 1) = gen ^ m := by
      have := congrArg (fun l => l.tail.head?) hpσ
      rw [hpar, hn, List.range_succ_eq_map, List.range_succ_eq_map] at this
      simpa using this
    have hps : fn.params.tail.map σ = gen ^ m :: rest := by
      have := congrArg List.tail hpσ
      rwa [← List.map_tail] at this
    refine ⟨?_, ?_⟩
    · rw [addOf_sound hpq hat, genMul_sound hp' hat, hx0, hx1, gen_pow_mul_gen]
    · rw [List.map_cons, genMul_sound hg hat, hx0, htail, hps, gen_pow_mul_gen]
  have hblkEq : ∀ j, lpBlk fs f (m - j) = fs f + lpBlk fs f (m - (j + 1)) ∨ m ≤ j := by
    intro j
    by_cases hj : j < m
    · left
      obtain ⟨r, hr⟩ : ∃ r, m - j = r + 1 := ⟨m - j - 1, by omega⟩
      rw [lpBlk, lpBlk, hr, show m - (j + 1) = r by omega, Nat.add_mul, one_mul]; ring
    · right; omega
  -- one iteration
  have step : ∀ j < m, (j + 1 < m → ∀ fp c, fp + lpBlk fs f (m - (j + 1)) ≤ c →
      CallAtA fs al cert k f (gen ^ (j + 1) :: gen ^ m :: rest) [] R (fun _ => False) (fun _ => True) Pre
        (fun rd t => t.pops coreProgram rd = loopPopsFrom ps m (j + 1)) (lpBlk fs f (m - (j + 1))) fp c c) →
      ∀ fp c, fp + lpBlk fs f (m - j) ≤ c →
      CallAtA fs al cert k f (gen ^ j :: gen ^ m :: rest) [] R (fun _ => False) (fun _ => True) Pre
        (fun rd t => t.pops coreProgram rd = loopPopsFrom ps m j) (lpBlk fs f (m - j)) fp c c := by
    intro j hj htl fp c hfc
    by_cases hex : ∃ rd0, LowDef k rd0 ∧ Pre rd0
    swap
    · refine ⟨[], ⟨by simp, List.Pairwise.nil⟩, le_rfl, fun _ _ => trivial, fun rd hl _ hp => ?_⟩
      exact absurd ⟨rd, hl, hp⟩ hex
    obtain ⟨rd0, hl0, hp0⟩ := hex
    obtain ⟨σ0, hpσ0, hs0, -, -, -⟩ := hblk j hj rd0 hl0 hp0
    obtain ⟨hcv0, hargs0⟩ := hvals j rd0 σ0 hpσ0 hs0
    have hB : lpBlk fs f (m - j) = fs f + lpBlk fs f (m - (j + 1)) := (hblkEq j).resolve_right (by omega)
    obtain ⟨hd0, ha0, hr0⟩ := plainH_parts (σ := σ0) hsP hpP
    have hc0 := (straight_parts σ0 P hsP).2.2.2
    have hcalls : (P.filterMap Stmt.callS).map (mkCall σ0) =
        [⟨f, a0 :: rs, [], decide (σ0 cv ≠ 0)⟩] := by
      have : P.filterMap Stmt.callS = [(some cv, f, a0 :: rs, [])] := by
        rw [hP, List.filterMap_append]
        have hn : pre.filterMap Stmt.callS = [] := List.filterMap_eq_nil_iff.mpr fun s hs => by
          obtain ⟨a, rfl⟩ := hpreA s hs; rfl
        rw [hn]; rfl
      rw [this]; rfl
    rw [hB] at hfc ⊢
    refine callAtA_nodeLRd hlp hfc ⟨σ0, fn, P.flatMap (slEvs σ0), [], [], [fun rd t => t.pops coreProgram rd = loopPopsFrom ps m (j + 1)],
      fun rd => HoldsWords rd [], fun _ => False, hf, ?_, fun _ h => h.elim, ?_, fun _ _ => trivial, ?_⟩
    · rw [ha0]; exact ⟨by simp, List.Pairwise.nil⟩
    · rw [ha0, hc0, hcalls, List.sum_nil, Nat.add_zero, KidsAtL]
      by_cases hlt : j + 1 < m
      · have htk : decide (σ0 cv ≠ 0) = true := by
          rw [hcv0, gen_guard hm (by omega)]; exact decide_eq_true (by omega)
        simp only [htk, ↓reduceIte]
        refine ⟨R, fun _ => False, fun _ => True, fun i hi => Or.inl (Or.inl hi), ?_, fun _ h _ => h,
          fun _ h => h.elim⟩
        rw [hargs0]
        exact (htl hlt (fp + fs f) c (by omega)).mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
          (fun _ h => h.1) (fun _ _ _ h => h)
      · have htk : decide (σ0 cv ≠ 0) = false := by
          rw [hcv0, gen_guard hm (by omega)]; exact decide_eq_false (by omega)
        simp only [htk, Bool.false_eq_true, ↓reduceIte]
        refine ⟨⟨fun v => (gen ^ (j + 1) :: gen ^ m :: rest).getD v.idx 0, fn, hf, ?_⟩, ?_, by simp, fun _ h => h,
          fun _ h => h.elim⟩
        · rw [hargs0]
          have hl : (gen ^ (j + 1) :: gen ^ m :: rest).length = fn.params.length := by
            rw [← hargs0, List.length_map, hlen]
          rw [hpar, List.map_map]
          refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
          simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
          exact List.getD_eq_getElem _ _ h2
        · rw [show m - (j + 1) = 0 by omega, lpBlk]; simp
    · intro rd hl hp _
      obtain ⟨σ, hpσ, hs, hlo, hhi, hps⟩ := hblk j hj rd hl hp
      obtain ⟨hcv, hargs⟩ := hvals j rd σ hpσ hs
      have hev : P.flatMap (slEvs σ) = P.flatMap (slEvs σ0) := by
        refine slEvs_congr P fun c' g' a' hm' => ?_
        rcases List.mem_append.mp hm' with hm' | hm'
        · obtain ⟨a, ha⟩ := hpreA _ hm'; cases ha
        · simp only [List.mem_singleton, Stmt.callIf.injEq] at hm'
          obtain ⟨rfl, -, -⟩ := hm'
          rw [hcv, hcv0]
      obtain ⟨hd, ha, hr⟩ := plainH_parts (σ := σ) hsP hpP
      have hwσ : walk σ fn.body = .ret (P.flatMap (slEvs σ0)) [] := by rw [hbP, walk_straight σ [] P hsP, hev]
      refine ⟨σ, hpσ, hwσ, rfl, by rw [ha0, ← hev, ha], ?_, ?_, ?_, ?_, ?_, fun ts hv hq => ?_⟩
      · rw [ha0, ← hev]
        exact ⟨by rw [hd]; rfl, fun q hq => by rw [hr] at hq; simp at hq⟩
      · rw [hc0, hcalls]
        intro cc hcc
        simp only [List.mem_singleton] at hcc
        subst hcc
        exact ⟨by rw [hargs0, hargs], rfl⟩
      · intro A hA
        rw [← hev, loadAddrs_straight σ P hsP, hloadsP] at hA
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
        obtain ⟨i, hi, hR⟩ := hlo q hq
        exact ⟨i, hi, Or.inr (Or.inl hR)⟩
      · intro A hA
        rw [← hev, hP, List.flatMap_append, heapHintAddrs_append_callIf] at hA
        obtain ⟨i, hi, hR⟩ := hhi A hA
        exact ⟨i, hi, Or.inr (Or.inl hR)⟩
      · rw [← hev]
        refine events_straight fun s hs' => ?_
        rcases List.mem_append.mp hs' with hs' | hs'
        · exact hs s hs'
        · simp only [List.mem_singleton] at hs'
          subst hs'
          show IsInK (σ cv)
          rw [hcv]; exact gen_pow_add_isInK _ _
      · rw [hc0, hcalls] at hv hq
        have hpk := popsKids_tail hv hq (fun _ t h => h) (fun htk => by
          have : j + 1 = m := by
            rw [hcv0, gen_guard hm (by omega)] at htk; simpa using htk
          simp [loopPopsFrom, show m - (j + 1) = 0 by omega])
        have hpre' : pre.flatMap (slEvs σ0) = pre.flatMap (slEvs σ) := slEvs_congr pre fun c' g' a' hm' => by
          obtain ⟨a, ha⟩ := hpreA _ hm'; cases ha
        have hcpre : calls (pre.flatMap (slEvs σ0)) = [] := List.filterMap_eq_nil_iff.mpr fun e he => by
          obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
          obtain ⟨a, rfl⟩ := hpreA s hs
          simp only [slEvs, List.mem_singleton] at he
          subst he; rfl
        have hsp := splice_append (rd := rd) (σ := σ) (pre.flatMap (slEvs σ0))
          ([Stmt.callIf cv f (a0 :: rs)].flatMap (slEvs σ0)) [] [loopPopsFrom ps m (j + 1)] (by rw [hcpre]; rfl)
        rw [List.nil_append] at hsp
        rw [Tree.pops, events_node hf hwσ, hpk, hP, List.flatMap_append, hsp, splice_nil_of_calls _ hcpre, hpre',
          hps, loopPopsFrom_succ (by omega : j < m)]
        congr 1
        by_cases h0 : σ0 cv = 0 <;> simp [slEvs, splice, h0]
  have key : ∀ t j, j + 1 + t = m → ∀ fp c, fp + lpBlk fs f (m - j) ≤ c →
      CallAtA fs al cert k f (gen ^ j :: gen ^ m :: rest) [] R (fun _ => False) (fun _ => True) Pre
        (fun rd t => t.pops coreProgram rd = loopPopsFrom ps m j) (lpBlk fs f (m - j)) fp c c := by
    intro t
    induction t with
    | zero => intro j hj; exact step j (by omega) fun h' => absurd h' (by omega)
    | succ t ih => intro j hj; exact step j (by omega) fun _ => ih (j + 1) (by omega)
  intro j hj
  exact key (m - j - 1) j (by omega)


end
end LeanVM.Guest.Complete
