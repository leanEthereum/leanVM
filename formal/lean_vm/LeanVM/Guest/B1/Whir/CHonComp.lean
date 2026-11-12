/-
  LeanVM.Guest.B1.Whir.CHonComp

  open_stacked's body at the honest data, its blocks composed: the head, the levels, the closing
  rounds and the finish.
-/

module

public import LeanVM.Guest.B1.Whir.CHonStep
public import LeanVM.Guest.B1.Whir.CHonLvs
public import LeanVM.Guest.B1.Whir.CTail

/-!
# The body, composed

`body_of`: from the levels in sequence (`QAt 0` to `QAt n`, each level's `RAt`), the closing
rounds' calls and zeroed entries, and the finish's block (its allocations, returns and its
dispatches into `level_residual`), the body before its return holds at values fixed before the
call relation and the memory, with `OsOutA`'s outcome at the helpers' data `D`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Memory LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash

@[expose] public section

theorem allocsAt_flatten (σ : Val) : ∀ L : List (List Stmt), AllocsAt σ L.flatten = (L.map (AllocsAt σ)).flatten
  | [] => rfl
  | a :: L => by rw [List.flatten_cons, allocsAt_append, allocsAt_flatten σ L]; rfl

theorem bufsAt_seq (c : OsCfg) (b j : ℕ) : ∀ n : ℕ,
    ((List.range n).map fun l ↦ bufsAt c b (j + l) 1).flatten = bufsAt c b j n
  | 0 => by simp [bufsAt]
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, bufsAt_seq c b j n]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [bufsAt_add]

/-- The head's allocations. -/
theorem head_allocs {c : OsCfg} (hS : BodyStatic c) {σ' : Val} {P : ℕ → E}
    (hv : ∀ j < 22, σ' (.n (11 + j)) = (headVals c P).getD j 0) :
    AllocsAt σ' (osHead c).1 = (List.range 11).map fun i ↦ (P i, (osSizesL c).getD i 0) := by
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
  t.Ok σ' ∧ s.k ≤ t.k ∧ (∀ i < 11, σ' (.n (12 + 2 * i)) = osPtrA c b i) ∧ σ' (.n osTabs) = tabs ∧
    σ' (.n s.k) = gw yrLogCap ∧ σ' (.n (osTail c s).2.2) = osPtrA c b (12 + c.yrLevel) ∧
    t.F σ' = ⟨(tailRun h.Lf.fw.pairs (h.capAt c.levels.length) (h.claimAt c.levels.length)).2.2, []⟩ ∧
    σ' (.n t.claim) = (tailRun h.Lf.fw.pairs (h.capAt c.levels.length) (h.claimAt c.levels.length)).2.1 ∧
    t.cur σ' = cur * gen ^ (xs.length - (h.xsAt c.levels.length).length + 2 * c.yrLog) ∧
    ∀ l < c.levels.length, LvRate σ' c l (c.levels.getD l default)

/-- **The body, composed.** -/
theorem body_of {h : OsHD} {b : ℕ} {args : List E} {cur tabs : E} {xs : List E}
    {tgt inn res : E} {own : List (List E)} {D : ℕ → OsLvData} (hS : BodyStatic h.c)
    (ha0 : [args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0, args.getD 5 0] = h.capAt 0)
    (ha6 : args.getD 6 0 = h.claimAt 0) (ha9 : args.getD 9 0 = cur) (ha10 : args.getD 10 0 = tabs)
    (hx0 : (h.xsAt 0).length = xs.length)
    (hrate : ∀ l < h.c.levels.length, LvRate (Val.ofArgs args) h.c l (h.c.levels.getD l default))
    (hroot : ∀ C rd, H C rd → LoadHolds rd (osPtrA h.c b 1) 0 (args.getD 7 0) ∧
      LoadHolds rd (osPtrA h.c b 1) 1 (args.getD 8 0))
    (hlvs : ∀ st σ, QAt h b tabs cur xs 0 st σ →
      BlkA H σ st.k (osLevels h.c 0 h.c.levels st).2.k (osLevels h.c 0 h.c.levels st).1 (fun σ' ↦
        st.k ≤ (osLevels h.c 0 h.c.levels st).2.k ∧
        QAt h b tabs cur xs h.c.levels.length (osLevels h.c 0 h.c.levels st).2 σ' ∧
        ∀ i < h.c.levels.length, RAt h b tabs i (h.bat i) σ'))
    (hD : ∀ l < h.c.levels.length, (D l).w0 = h.word l 0 ∧ (D l).capL = h.capL l ∧
      (l ≠ h.c.yrLevel → (D l).lam = h.lamAt l ∧ (D l).lamInv = h.li l) ∧ (D l).batched = h.bat l)
    (hrootA : ∀ l < h.c.levels.length, osRootA own l = digestHalves (h.root l))
    (hpl : h.Lf.fw.pairs.length = h.c.yrLog)
    (hT : ∀ C rd, H C rd → TailC C rd (osPtrA h.c b (12 + h.c.yrLevel)) tabs 0 h.Lf.fw.pairs
      (h.capAt h.c.levels.length) (h.claimAt h.c.levels.length)
      (cur * gen ^ (xs.length - (h.xsAt h.c.levels.length).length)))
    (hz : ∀ C rd, H C rd → ∀ i < yrLogCap - h.c.yrLog,
      LoadHolds rd (osPtrA h.c b (12 + h.c.yrLevel)) (h.c.yrLog + i) 0)
    (hfin : ∀ σ, (osLvsEnd h.c).Sf → (osFinSt h.c).Ok σ →
      (∀ l < h.c.levels.length, LvRate σ h.c l (h.c.levels.getD l default)) →
      (∀ i < 11, σ (.n (12 + 2 * i)) = osPtrA h.c b i) →
      σ (.n osTabs) = tabs → σ (.n (osFinTch h.c)) = osPtrA h.c b (12 + h.c.yrLevel) →
      σ (.n (osFinSt h.c).claim) = (tailRun h.Lf.fw.pairs (h.capAt h.c.levels.length)
        (h.claimAt h.c.levels.length)).2.1 →
      BlkA H σ (osFinSt h.c).k (finEnd h.c (osFinSt h.c) (osFinTch h.c)) (osFinishA h.c (osFinSt h.c) (osFinTch h.c)).1
        (fun σ' ↦ (osFinSt h.c).k ≤ finEnd h.c (osFinSt h.c) (osFinTch h.c) ∧
          AllocsAt σ' (osFinishA h.c (osFinSt h.c) (osFinTch h.c)).1 = bufsAt h.c b (13 + h.c.yrLevel) 6 ∧
          (osFinishA h.c (osFinSt h.c) (osFinTch h.c)).2.map σ' =
            [tgt, osPtrA h.c b (osIxPtA h.c), osPtrA h.c b (osIxPt1A h.c), inn, res] ∧
          ∀ l < h.c.yrLevel,
            ((osLrCalls h.c).getD l ([], [])).1.map σ' =
              [osPtrA h.c b osIxQposA * gen ^ (osLvA h.c l).posOff,
                osPtrA h.c b (osIxBdA h.c) * gen ^ (l * ligColsCap),
                osPtrA h.c b osIxHsA * gen ^ (l * hsStride), (D l).mu] ∧
            ((osLrCalls h.c).getD l ([], [])).2.map σ' =
              [(osLrRetA h.c own l (D l).mu).1, (osLrRetA h.c own l (D l).mu).2])) :
    ∃ kEnd, BlkA H (Val.ofArgs args) 11 kEnd (osBodyA h.c) (OsOutA h.c b tabs tgt inn res own D) := by
  set c := h.c with hc
  set n := c.levels.length with hn
  have hS' := hS
  obtain ⟨-, -, hTl, hlen, hyr, -, -, -, hs12, -, -, -, -, -, -, hlt⟩ := hS
  have hyr' : c.yrLevel + 1 = n := hyr
  have hlen' : (osSizesL c).length = 19 + c.yrLevel := hlen
  have hs12' : (osSizesL c).getD (12 + c.yrLevel) 0 = yrLogCap := hs12
  set σ0 := Val.ofArgs args with hσ0
  -- the head
  have b0 := osHead_complete (H := H) c σ0 (osPtrA c b) fun C rd hH ↦ hroot C rd hH
  -- the levels
  have bL := fun σ1 (ha : AgreeBelow 11 σ0 σ1) (ho : ∀ C rd, H C rd → (osHead c).2.Ok σ1 ∧
      (∀ j < 22, σ1 (.n (11 + j)) = (headVals c (osPtrA c b)).getD j 0) ∧ AgreeBelow 11 σ0 σ1) ↦
    BlkA.of_ne (H := H) fun ⟨C0, rd0, hH0⟩ ↦ by
      obtain ⟨hok, hv, -⟩ := ho C0 rd0 hH0
      have hq : QAt h b tabs cur xs 0 (osHead c).2 σ1 := by
        refine ⟨(osStFrom_zero c 0 c.levels _).symm, hok, fun i hi ↦ (headVals_at hv i hi).2, ?_,
          fun l hl ↦ ?_, ?_, ?_, ?_⟩
        · rw [ha _ (by show 10 < 11; omega)]; exact ha10
        · obtain ⟨ri, hri, hx, hlen, hlv⟩ := hrate l hl
          exact ⟨ri, hri, by rw [ha _ (show 0 < 11 by omega)]; exact hx, hlen, hlv⟩
        · simp only [OsSt.fsv, osHead, List.map_cons, List.map_nil]
          rw [ha 1 (by omega), ha 2 (by omega), ha 3 (by omega), ha 4 (by omega), ha 5 (by omega)]
          exact ha0
        · show σ1 (.n 6) = _
          rw [ha 6 (by omega)]; exact ha6
        · show σ1 (.n 9) * gen ^ 0 = _
          rw [ha 9 (by omega), hx0, Nat.sub_self, pow_zero, mul_one, mul_one]; exact ha9
      exact hlvs (osHead c).2 σ1 hq
  have b1 := BlkA.seqK b0 (fun _ _ ↦ by omega) bL (fun σ' ho ↦ ho.1)
  -- the closing rounds
  have bT := fun σ2 (_ : AgreeBelow 11 σ0 σ2) (ho : ∀ C rd, H C rd →
      ((osHead c).2.Ok σ2 ∧ (∀ j < 22, σ2 (.n (11 + j)) = (headVals c (osPtrA c b)).getD j 0) ∧
        AgreeBelow 11 σ0 σ2) ∧ ((osHead c).2.k ≤ (osLevels c 0 c.levels (osHead c).2).2.k ∧
        QAt h b tabs cur xs c.levels.length (osLevels c 0 c.levels (osHead c).2).2 σ2 ∧
        ∀ i < c.levels.length, RAt h b tabs i (h.bat i) σ2)) ↦
    show BlkA H σ2 (osLevels c 0 c.levels (osHead c).2).2.k (osTail c (osLvsEnd c)).2.1.k
      (osTail c (osLvsEnd c)).1 (OutT h b tabs cur xs) from
    BlkA.of_ne (H := H) fun ⟨C0, rd0, hH0⟩ ↦ by
      have hq : QAt h b tabs cur xs n (osLevels c 0 c.levels (osHead c).2).2 σ2 := (ho C0 rd0 hH0).2.2.1
      have hfs := hq.fs
      have hcl := hq.claim
      have hcu := hq.cur
      have h0 := osTail_complete (H := H) (c := c) (st := (osLevels c 0 c.levels (osHead c).2).2) σ2
        hq.ok.sf (fun _ _ _ ↦ hq.ok) (osPtrA c b (12 + c.yrLevel)) h.Lf.fw.pairs hpl (fun C rd hH ↦ by
          rw [hfs, hcl, hcu, hq.tabs]; exact hT C rd hH) hz
      refine h0.monoH fun C rd hH σ' _ ⟨hstep, e0, e1, e2, eF, ecl, ecur, _⟩ ↦ ?_
      rw [hfs, hcl] at eF ecl
      rw [hcu] at ecur
      refine ⟨hstep.ok, hstep.le, fun i hi ↦ ?_, ?_, e1, ?_, eF, ecl, ?_, fun l hl ↦ ?_⟩
      · rw [hstep.agree _ (by have := hq.ok.sf.k; omega)]; exact hq.ptr i hi
      · rw [hstep.agree _ (by have := hq.ok.sf.k; show 10 < _; omega)]; exact hq.tabs
      · exact (congrArg (fun k ↦ σ' (.n k)) e0).trans e2
      · exact ecur.trans (by rw [mul_assoc, ← pow_add])
      · obtain ⟨ri, hri, hx, hlen, hlv⟩ := hq.rate l hl
        exact ⟨ri, hri, by rw [hstep.agree _ (by have := hq.ok.sf.k; show 0 < _; omega)]; exact hx, hlen, hlv⟩
  have b2 := BlkA.seqK b1 (fun σ' ho ↦ by
    have := ho.2.1; have e : (osHead c).2.k = 33 := rfl; omega) bT (fun σ' ho ↦ ho.2.1)
  -- the finish
  have b3 := BlkA.seqK b2 (fun σ' ho ↦ by
    have a : 33 ≤ (osLevels c 0 c.levels (osHead c).2).2.k := ho.1.2.1
    have a' : (osLevels c 0 c.levels (osHead c).2).2.k ≤ (osTail c (osLvsEnd c)).2.1.k := ho.2.2.1
    show 11 ≤ (osTail c (osLvsEnd c)).2.1.k
    omega) (fun σ3 _ ho ↦ BlkA.of_ne (H := H) fun ⟨C0, rd0, hH0⟩ ↦ by
      obtain ⟨hok3, -, hp, ht, -, htc, -, hcl, -, hrt⟩ := (ho C0 rd0 hH0).2
      exact hfin σ3 (ho C0 rd0 hH0).1.2.2.1.ok.sf hok3 hrt hp ht htc hcl) (fun σ' ho ↦ by exact ho.1)
  refine ⟨_, BlkA.mono b3 fun σ' ⟨⟨⟨⟨_, hv, _⟩, _, _, hR⟩, hOT⟩, _, hFA, hFR, hFC⟩ ↦ ?_⟩
  have hal : AllocsAt σ' (osBodyA c) = bufsAt c b 0 (osSizesL c).length := by
    show AllocsAt σ' ((osHead c).1 ++ (osLevels c 0 c.levels (osHead c).2).1 ++
      (osTail c (osLvsEnd c)).1 ++ (osFinishA c (osFinSt c) (osFinTch c)).1) = _
    rw [allocsAt_append, allocsAt_append, allocsAt_append, hFA, head_allocs hS' hv,
      osLevels_split c 0 c.levels (osHead c).2, allocsAt_flatten, List.map_map]
    have hlv' : ((List.range c.levels.length).map ((AllocsAt σ') ∘ fun i ↦
        (osLevel c (0 + i) (c.levels.getD i default) (osStFrom c 0 c.levels (osHead c).2 i)).1)) =
        (List.range n).map fun l ↦ bufsAt c b (11 + l) 1 := by
      refine List.map_congr_left fun i hi ↦ ?_
      have := (hR i (List.mem_range.mp hi)).1
      simp only [Function.comp_apply, Nat.zero_add] at this ⊢
      exact this
    have htl : AllocsAt σ' (osTail c (osLvsEnd c)).1 = bufsAt c b (12 + c.yrLevel) 1 := by
      obtain ⟨-, -, -, -, e1, e2, -⟩ := hOT
      simp only [AllocsAt, hTl, List.map_cons, List.map_nil, Sum.elim_inr]
      rw [bufsAt_one, hs12', ← e2, e1, logG_gw (by norm_num)]
      rfl
    rw [hlv', bufsAt_seq, htl, hlen',
      show 19 + c.yrLevel = (12 + c.yrLevel + 1) + 6 by omega,
      ← bufsAt_add c b 0 (12 + c.yrLevel + 1) 6, ← bufsAt_add c b 0 (12 + c.yrLevel) 1,
      show 12 + c.yrLevel = 11 + n by omega, ← bufsAt_add c b 0 11 n]
    have hb0 : bufsAt c b 0 11 = (List.range 11).map fun i ↦ (osPtrA c b i, (osSizesL c).getD i 0) := by
      simp [bufsAt]
    rw [hb0, show 0 + (11 + n + 1) = 13 + c.yrLevel by omega, show 0 + (11 + n) = 11 + n by omega,
      show 0 + 11 = 11 by rfl]
  obtain ⟨hsz, hpt⟩ := bufsAt_out c b
  refine ⟨hFR, ?_, ?_, fun l hl ↦ ?_⟩
  · rw [← hsz, ← hal]; simp [AllocsAt, List.map_map]
  · rw [← hpt, ← hal]; simp [AllocsAt, List.map_map]
  · obtain ⟨-, pa, pr, qa, qr⟩ := hR l hl
    obtain ⟨dw, dc, dl, db⟩ := hD l hl
    refine ⟨?_, ?_, ?_, ?_, fun hly ↦ hFC l hly⟩
    · rw [pa, dw, dc]
    · rw [pr, dc]
    · rw [qa, ← hc]
      by_cases hy : l = c.yrLevel
      · simp only [hy, ↓reduceIte, osLvA]
      · obtain ⟨e1, e2⟩ := dl hy
        simp only [hy, ↓reduceIte, e1, e2, osLvA]
    · rw [qr, hrootA l hl, db, ← hc]
      by_cases hy : l = c.yrLevel
      · simp only [hy, ↓reduceIte, osLvA]
      · simp only [hy, ↓reduceIte, (dl hy).1, osLvA]

end
end LeanVM.Guest.B1.Whir
