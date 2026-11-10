/-
  LeanVM.Guest.B1.Whir.CHonComp

  open_stacked's body at the honest data, its blocks composed: the head, the levels, the closing
  rounds and the finish.
-/

module

public import LeanVM.Guest.B1.Whir.CHonStep
public import LeanVM.Guest.B1.Whir.CTail

/-!
# The body, composed

`body_of`: from each level's step (`QAt l` to `QAt (l + 1)`, its allocations and special calls),
the closing rounds' calls and zeroed entries, and the finish's block (its allocations, returns and
residual loops' calls), the body before its return holds at values fixed before the call relation
and the memory, under `OsH`, with `OsOutF`'s outcome.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Memory LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem allocsAt_flatten (σ : Val) : ∀ L : List (List Stmt), AllocsAt σ L.flatten = (L.map (AllocsAt σ)).flatten
  | [] => rfl
  | a :: L => by rw [List.flatten_cons, allocsAt_append, allocsAt_flatten σ L]; rfl

/-- The head's allocations. -/
theorem head_allocs {c : OsCfg} (hS : BodyStatic c) {σ' : Val} {P : ℕ → E}
    (hv : ∀ j < 26, σ' (.n (10 + j)) = (headVals c P).getD j 0) :
    AllocsAt σ' (osHead c).1 = (List.range 13).map fun i ↦ (P i, (osSizesF c).getD i 0) := by
  obtain ⟨hH, -, -, hlen, -, hHs, -, -, -, -, -, -, -, -, -, hlt⟩ := hS
  simp only [AllocsAt, hH, List.map_map]
  refine List.map_congr_left fun i hi ↦ ?_
  have hi' := List.mem_range.mp hi
  obtain ⟨e1, e2⟩ := headVals_at hv i hi'
  simp only [Function.comp_apply, Sum.elim_inr, e1, e2, hHs i hi']
  rw [logG_gw (by have := hlt i (by omega); rwa [hHs i hi'] at this)]

/-- The finish's state and tail challenges' value after the levels and the closing rounds. -/
abbrev osFinSt (c : OsCfg) : OsSt := (osTail c (osLvsEnd c)).2.1
abbrev osFinTch (c : OsCfg) : ℕ := (osTail c (osLvsEnd c)).2.2

variable {H : CallRel → Reader → Prop}

/-- What the closing rounds leave. -/
def OutT (h : OsHD) (b : ℕ) (tabs cur : E) (xs : List E) (σ' : Val) : Prop :=
  let c := h.c
  let s := osLvsEnd c
  let t := (osTail c s).2.1
  t.Ok σ' ∧ s.k ≤ t.k ∧ (∀ i < 13, σ' (.n (11 + 2 * i)) = osPtrF c b i) ∧ σ' (.n osTabs) = tabs ∧
    σ' (.n s.k) = gw yrLogCap ∧ σ' (.n (osTail c s).2.2) = osPtrF c b (13 + 2 * c.levels.length) ∧
    t.F σ' = ⟨(tailRun h.Lf.fw.pairs (h.capAt c.levels.length) (h.claimAt c.levels.length)).2.2, []⟩ ∧
    σ' (.n t.claim) = (tailRun h.Lf.fw.pairs (h.capAt c.levels.length) (h.claimAt c.levels.length)).2.1 ∧
    t.cur σ' = cur * gen ^ (xs.length - (h.xsAt c.levels.length).length + 2 * c.yrLog)

/-- **The body, composed.** -/
theorem body_of {h : OsHD} {b : ℕ} {args : List E} {cur tabs : E} {xs : List E}
    {tgt inn res : E} {batched : ℕ → E} (hS : BodyStatic h.c)
    (ha0 : [args.getD 0 0, args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0] = h.capAt 0)
    (ha5 : args.getD 5 0 = h.claimAt 0) (ha8 : args.getD 8 0 = cur) (ha9 : args.getD 9 0 = tabs)
    (hx0 : (h.xsAt 0).length = xs.length)
    (hroot : ∀ C rd, H C rd → LoadHolds rd (osPtrF h.c b 3) 0 (args.getD 6 0) ∧
      LoadHolds rd (osPtrF h.c b 3) 1 (args.getD 7 0))
    (hlv : ∀ l < h.c.levels.length, ∀ st σ, QAt h b tabs cur xs l st σ →
      BlkA H σ st.k (osLevel h.c l (osLvAt h.c l) st).2.k (osLevel h.c l (osLvAt h.c l) st).1 (fun σ' ↦
        st.k ≤ (osLevel h.c l (osLvAt h.c l) st).2.k ∧
        QAt h b tabs cur xs (l + 1) (osLevel h.c l (osLvAt h.c l) st).2 σ' ∧ RAt h b tabs l σ' ∧
        RQ h b l (batched l) σ'))
    (hpl : h.Lf.fw.pairs.length = h.c.yrLog)
    (hT : ∀ C rd, H C rd → TailC C rd (osPtrF h.c b (13 + 2 * h.c.levels.length)) tabs 0 h.Lf.fw.pairs
      (h.capAt h.c.levels.length) (h.claimAt h.c.levels.length)
      (cur * gen ^ (xs.length - (h.xsAt h.c.levels.length).length)))
    (hz : ∀ C rd, H C rd → ∀ i < yrLogCap - h.c.yrLog,
      LoadHolds rd (osPtrF h.c b (13 + 2 * h.c.levels.length)) (h.c.yrLog + i) 0)
    (hfin : ∀ σ, (osLvsEnd h.c).Sf → (∀ i < 13, σ (.n (11 + 2 * i)) = osPtrF h.c b i) → σ (.n osTabs) = tabs →
      σ (.n (osFinTch h.c)) = osPtrF h.c b (13 + 2 * h.c.levels.length) →
      σ (.n (osFinSt h.c).claim) = (tailRun h.Lf.fw.pairs (h.capAt h.c.levels.length)
        (h.claimAt h.c.levels.length)).2.1 →
      BlkA H σ (osFinSt h.c).k (finEnd h.c (osFinSt h.c) (osFinTch h.c)) (osFinishA h.c (osFinSt h.c) (osFinTch h.c)).1
        (fun σ' ↦ (osFinSt h.c).k ≤ finEnd h.c (osFinSt h.c) (osFinTch h.c) ∧
          AllocsAt σ' (osFinishA h.c (osFinSt h.c) (osFinTch h.c)).1 =
            bufsAt h.c b (14 + 2 * h.c.levels.length) (6 + h.c.yrLevel) ∧
          (osFinishA h.c (osFinSt h.c) (osFinTch h.c)).2.map σ' =
            [tgt, osPtrF h.c b (osIxPT h.c), osPtrF h.c b (osIxPT1 h.c), inn, res] ∧
          ∀ l < h.c.yrLevel,
            (osResCall h.c l).1.map σ' = some (1 + gen ^ ((osLvAt h.c l).queries / resBatch)) ∧
            (osResCall h.c l).2.2.1.map σ' = [1, gen ^ ((osLvAt h.c l).queries / resBatch),
              osPtrF h.c b 11, osPtrF h.c b (osIxBD h.c), osPtrF h.c b 8, osPtrF h.c b (osIxRC h.c l),
              h.li l])) :
    ∃ kEnd, BlkA H (Val.ofArgs args) 10 kEnd (osBodyA h.c)
      (OsOutF h.c b tabs tgt inn res h.word h.lamInv batched h.li) := by
  set c := h.c with hc
  set n := c.levels.length with hn
  have hS' := hS
  obtain ⟨-, -, hTl, hlen, hyr, -, -, hs13, -, -, -, -, -, -, -, hlt⟩ := hS
  set σ0 := Val.ofArgs args with hσ0
  -- the head
  have b0 := osHead_complete (H := H) c σ0 (osPtrF c b) fun C rd hH ↦ hroot C rd hH
  -- the levels
  have bL := fun σ1 (ha : AgreeBelow 10 σ0 σ1) (ho : ∀ C rd, H C rd → (osHead c).2.Ok σ1 ∧
      (∀ j < 26, σ1 (.n (10 + j)) = (headVals c (osPtrF c b)).getD j 0) ∧ AgreeBelow 10 σ0 σ1) ↦
    BlkA.of_ne (H := H) fun ⟨C0, rd0, hH0⟩ ↦ by
      obtain ⟨hok, hv, -⟩ := ho C0 rd0 hH0
      have hq : QAt h b tabs cur xs 0 (osHead c).2 σ1 := by
        refine ⟨(osStFrom_zero c 0 c.levels _).symm, hok, fun i hi ↦ (headVals_at hv i hi).2, ?_, ?_, ?_, ?_⟩
        · rw [ha _ (by show 9 < 10; omega)]; exact ha9
        · simp only [OsSt.fsv, osHead, List.map_cons, List.map_nil]
          rw [ha 0 (by omega), ha 1 (by omega), ha 2 (by omega), ha 3 (by omega), ha 4 (by omega)]
          exact ha0
        · show σ1 (.n 5) = _
          rw [ha 5 (by omega)]; exact ha5
        · show σ1 (.n 8) * gen ^ 0 = _
          rw [ha 8 (by omega), hx0, Nat.sub_self, pow_zero, mul_one, mul_one]; exact ha8
      exact osLevels_complete (H := H) c (fun l st σ ↦ QAt h b tabs cur xs l st σ)
        (fun l σ' ↦ RAt h b tabs l σ' ∧ RQ h b l (batched l) σ')
        (fun l st σ σ' hq ha ↦ hq.agree ha) c.levels 0 (fun i hi st σ hq ↦ by
          rw [Nat.zero_add] at hq ⊢
          have e : c.levels[i] = osLvAt c i := by simp [osLvAt, List.getElem?_eq_getElem hi]
          rw [e]
          exact (hlv i hi st σ hq).mono fun σ' ⟨a, b', c', d⟩ ↦ ⟨a, b', c', d⟩)
        (osHead c).2 σ1 hq
  have b1 := BlkA.seqK b0 (fun _ _ ↦ by omega) bL (fun σ' ho ↦ ho.1)
  -- the closing rounds
  have bT := fun σ2 (_ : AgreeBelow 10 σ0 σ2) (ho : ∀ C rd, H C rd →
      ((osHead c).2.Ok σ2 ∧ (∀ j < 26, σ2 (.n (10 + j)) = (headVals c (osPtrF c b)).getD j 0) ∧
        AgreeBelow 10 σ0 σ2) ∧ ((osHead c).2.k ≤ (osLevels c 0 c.levels (osHead c).2).2.k ∧
        QAt h b tabs cur xs (0 + c.levels.length) (osLevels c 0 c.levels (osHead c).2).2 σ2 ∧
        ∀ i < c.levels.length, RAt h b tabs (0 + i) σ2 ∧ RQ h b (0 + i) (batched (0 + i)) σ2)) ↦
    show BlkA H σ2 (osLevels c 0 c.levels (osHead c).2).2.k (osTail c (osLvsEnd c)).2.1.k
      (osTail c (osLvsEnd c)).1 (OutT h b tabs cur xs) from
    BlkA.of_ne (H := H) fun ⟨C0, rd0, hH0⟩ ↦ by
      have hq : QAt h b tabs cur xs n (osLevels c 0 c.levels (osHead c).2).2 σ2 := by
        have := (ho C0 rd0 hH0).2.2.1
        rwa [Nat.zero_add] at this
      have hfs := hq.fs
      have hcl := hq.claim
      have hcu := hq.cur
      have h0 := osTail_complete (H := H) (c := c) (st := (osLevels c 0 c.levels (osHead c).2).2) σ2 hq.ok.sf (fun _ _ _ ↦ hq.ok)
        (osPtrF c b (13 + 2 * n)) h.Lf.fw.pairs hpl (fun C rd hH ↦ by
          rw [hfs, hcl, hcu, hq.tabs]; exact hT C rd hH) hz
      refine h0.monoH fun C rd hH σ' _ ⟨hstep, e0, e1, e2, eF, ecl, ecur, _⟩ ↦ ?_
      rw [hfs, hcl] at eF ecl
      rw [hcu] at ecur
      refine ⟨hstep.ok, hstep.le, fun i hi ↦ ?_, ?_, e1, ?_, eF, ecl, ?_⟩
      · rw [hstep.agree _ (by have := hq.ok.sf.k; omega)]; exact hq.ptr i hi
      · rw [hstep.agree _ (by have := hq.ok.sf.k; show 9 < _; omega)]; exact hq.tabs
      · exact (congrArg (fun k ↦ σ' (.n k)) e0).trans e2
      · exact ecur.trans (by rw [mul_assoc, ← pow_add])
  have b2 := BlkA.seqK b1 (fun σ' ho ↦ by
    have := ho.2.1; have e : (osHead c).2.k = 36 := rfl; omega) bT (fun σ' ho ↦ ho.2.1)
  -- the finish
  have b3 := BlkA.seqK b2 (fun σ' ho ↦ by
    have a : 36 ≤ (osLevels c 0 c.levels (osHead c).2).2.k := ho.1.2.1
    have a' : (osLevels c 0 c.levels (osHead c).2).2.k ≤ (osTail c (osLvsEnd c)).2.1.k := ho.2.2.1
    show 10 ≤ (osTail c (osLvsEnd c)).2.1.k
    omega) (fun σ3 _ ho ↦ BlkA.of_ne (H := H) fun ⟨C0, rd0, hH0⟩ ↦ by
      obtain ⟨-, -, hp, ht, -, htc, -, hcl, -⟩ := (ho C0 rd0 hH0).2
      exact hfin σ3 (ho C0 rd0 hH0).1.2.2.1.ok.sf hp ht htc hcl) (fun σ' ho ↦ by exact ho.1)
  refine ⟨_, BlkA.mono b3 fun σ' ⟨⟨⟨⟨_, hv, _⟩, _, _, hR⟩, hOT⟩, _, hFA, hFR, hFC⟩ ↦ ?_⟩
  have hal : AllocsAt σ' (osBodyA c) = bufsAt c b 0 (osSizesF c).length := by
    show AllocsAt σ' ((osHead c).1 ++ (osLevels c 0 c.levels (osHead c).2).1 ++
      (osTail c (osLvsEnd c)).1 ++ (osFinishA c (osFinSt c) (osFinTch c)).1) = _
    rw [allocsAt_append, allocsAt_append, allocsAt_append, hFA, head_allocs hS' hv,
      osLevels_split c 0 c.levels (osHead c).2, allocsAt_flatten, List.map_map]
    have hlv' : ((List.range c.levels.length).map ((AllocsAt σ') ∘ fun i ↦
        (osLevel c (0 + i) (c.levels.getD i default) (osStFrom c 0 c.levels (osHead c).2 i)).1)) =
        (List.range n).map fun l ↦ bufsAt c b (13 + 2 * l) 2 := by
      refine List.map_congr_left fun i hi ↦ ?_
      have := (hR i (List.mem_range.mp hi)).1.1
      simp only [Nat.zero_add] at this ⊢
      exact this
    have htl : AllocsAt σ' (osTail c (osLvsEnd c)).1 = bufsAt c b (13 + 2 * n) 1 := by
      obtain ⟨-, -, -, -, e1, e2, -⟩ := hOT
      simp only [AllocsAt, hTl, List.map_cons, List.map_nil, Sum.elim_inr]
      rw [bufsAt_one, hs13, Nat.add_zero, ← e2, e1, logG_gw (by norm_num)]
      rfl
    rw [hlv', bufsAt_levels, htl, hlen,
      show 20 + 2 * n + c.yrLevel = (13 + 2 * n + 1) + (6 + c.yrLevel) by omega,
      ← bufsAt_add c b 0 (13 + 2 * n + 1) (6 + c.yrLevel), ← bufsAt_add c b 0 (13 + 2 * n) 1,
      ← bufsAt_add c b 0 13 (2 * n)]
    have hb0 : bufsAt c b 0 13 = (List.range 13).map fun i ↦ (osPtrF c b i, (osSizesF c).getD i 0) := by
      simp [bufsAt]
    rw [hb0, show 0 + (13 + 2 * n + 1) = 14 + 2 * n by omega, show 0 + (13 + 2 * n) = 13 + 2 * n by omega,
      show 0 + 13 = 13 by rfl]
  obtain ⟨hsz, hpt⟩ := bufsAt_out c b
  refine ⟨hFR, ?_, ?_, fun l hl ↦ ?_, fun l hl ↦ hFC l hl⟩
  · rw [← hsz, ← hal]; simp [AllocsAt, List.map_map]
  · rw [← hpt, ← hal]; simp [AllocsAt, List.map_map]
  · obtain ⟨⟨-, d, s1, s2⟩, q1, q2⟩ := hR l hl
    simp only [Nat.zero_add] at d s1 s2 q1 q2
    exact ⟨d, s1, s2, q1, q2⟩

end
end LeanVM.Guest.B1.Whir
