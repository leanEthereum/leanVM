/-
  LeanVM.Guest.B1.Whir.CFinM

  The finish before its return, honestly: its blocks in sequence.
-/

module

public import LeanVM.Guest.B1.Whir.CFinA
public import LeanVM.Guest.B1.Whir.CFinRes

/-!
# The finish, honestly, assembled

`fin0_complete`: `fold_final_msg` and the two point buffers; `finHeaps_complete`: `basis_d`,
`level_scale`, `level_after`; `finIch0_complete`: `inner_chain` started at `0` and the claim;
`finRet_complete`: the returns' loads and copies. `osFinishA_complete`: the finish's blocks in
sequence; `osFinishA_completeR` with its returns, `osFinishA_completeC` with its dispatches into
`level_residual` too (`FinCallV`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- **`fold_final_msg` and the point buffers, honestly.** -/
theorem fin0_complete {f : String} {k tch : ℕ} {σ : Val} {Y PT PT1 : E} (htch : tch < k)
    (hk : 33 ≤ k) (hC : ∀ C rd, H C rd → C f [σ (.n osFmsg), σ (.n tch)] [Y]) :
    BlkA H σ k (k + 3) [.call f [.n osFmsg, .n tch] [.n k], .atom (.hint (.alloc (.n (k + 1)) pointCap)),
      .atom (.hint (.alloc (.n (k + 1 + 1)) pointCap))]
      (fun σ' ↦ σ' (.n k) = Y ∧ σ' (.n (k + 1)) = PT ∧ σ' (.n (k + 1 + 1)) = PT1 ∧
        AllocsAt σ' [.call f [.n osFmsg, .n tch] [.n k],
        .atom (.hint (.alloc (.n (k + 1)) pointCap)), .atom (.hint (.alloc (.n (k + 1 + 1)) pointCap))] =
        [(PT, pointCap), (PT1, pointCap)]) := by
  have hS : Ssa k [.call f [.n osFmsg, .n tch] [.n k], .atom (.hint (.alloc (.n (k + 1)) pointCap)),
      .atom (.hint (.alloc (.n (k + 1 + 1)) pointCap))] (k + 3) :=
    .cons (.call1 (args := [osFmsg, tch]) le_rfl (by
      intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false, osFmsg] at ha; omega))
      (.cons (.alloc (by omega)) (.cons (.alloc (by omega)) .nil))
  refine ssa_blk (Pt := fun i ↦ if i = k then Y else if i = k + 1 then PT else PT1) hS ?_ ?_
  · intro C rd hH σ' ha hr _
    have e0 := hr k le_rfl (by omega)
    have e1 := hr (k + 1) (by omega) (by omega)
    have e2 := hr (k + 2) (by omega) (by omega)
    simp +arith [evalV, stepV, stepW] at e0 e1 e2
    rw [show k + 1 + 1 = k + 2 by ring]
    refine ⟨e0, e1, e2, ?_⟩
    simp only [AllocsAt, List.filterMap_cons, Memory.Stmt.allocSz, List.filterMap_nil, List.map_cons,
      List.map_nil, Sum.elim_inl, id]
    rw [e1, e2]
  · intro C rd hH σ' ha hr
    simp only [SidesOk, Side, List.map_cons, List.map_nil, ↓reduceIte, and_true]
    rw [ha _ (by show 12 < k; omega), ha _ htch]
    exact hC C rd hH

/-- **`basis_d`, `level_scale`, `level_after` allocated**, at `BD`, `LS`, `LA`. -/
theorem finHeaps_complete {n p : ℕ} {σ : Val} {BD LS LA : E} (hn6 : n ≤ 6) :
    BlkA H σ p (p + 6) (osHeap (n * ligColsCap) p ++ osHeap n (p + 2) ++ osHeap n (p + 4))
      (fun σ' ↦ σ' (.n (p + 1)) = BD ∧ σ' (.n (p + 3)) = LS ∧ σ' (.n (p + 5)) = LA ∧
        AllocsAt σ' (osHeap (n * ligColsCap) p ++ osHeap n (p + 2) ++ osHeap n (p + 4)) =
          [(BD, n * ligColsCap), (LS, n), (LA, n)]) := by
  have hS : Ssa p (osHeap (n * ligColsCap) p ++ osHeap n (p + 2) ++ osHeap n (p + 4)) (p + 6) :=
    .cons (.const le_rfl) (.cons (.allocDyn (by omega) (by omega)) (.cons (.const (by omega))
      (.cons (.allocDyn (by omega) (by omega)) (.cons (.const (by omega))
        (.cons (.allocDyn (by omega) (by omega)) .nil)))))
  refine ssa_blk (Pt := fun i ↦ if i = p + 1 then BD else if i = p + 3 then LS else LA) hS ?_
    fun _ _ _ _ _ _ ↦ by simp [SidesOk, Side, osHeap]
  intro C rd hH σ' ha hr _
  have e0 := hr p le_rfl (by omega)
  have e1 := hr (p + 1) (by omega) (by omega)
  have e2 := hr (p + 2) (by omega) (by omega)
  have e3 := hr (p + 3) (by omega) (by omega)
  have e4 := hr (p + 4) (by omega) (by omega)
  have e5 := hr (p + 5) (by omega) (by omega)
  simp +arith [evalV, stepV, stepW, osHeap] at e0 e1 e2 e3 e4 e5
  refine ⟨e1, e3, e5, ?_⟩
  rw [allocsAt_append, allocsAt_append, allocsAt_heap σ' _ _ (by show n * 24 < _; omega) e0,
    allocsAt_heap σ' _ _ (by omega) e2, allocsAt_heap σ' _ _ (by omega) e4, e1, e3, e5]
  rfl

/-- **`inner_chain` allocated at `ICH` and started**: `0` and the claim. -/
theorem finIch0_complete {n b cl : ℕ} {σ : Val} {ICH : E} (hn : 2 * n < 2 ^ 64 - 1) (hcl : cl < b) (hm : ∀ C rd, H C rd → LoadHolds rd ICH 0 0 ∧ LoadHolds rd ICH 1 (σ (.n cl))) :
    BlkA H σ b (b + 3) (osHeap (2 * n) b ++ [osCst (b + 2) (word 0 0), osLd (b + 2) (b + 1) 0,
        osLd cl (b + 1) 1])
      (fun σ' ↦ σ' (.n (b + 1)) = ICH ∧ AllocsAt σ' (osHeap (2 * n) b ++ [osCst (b + 2) (word 0 0),
        osLd (b + 2) (b + 1) 0, osLd cl (b + 1) 1]) = [(ICH, 2 * n)]) := by
  have hS1 : Ssa b (osHeap (2 * n) b ++ [osCst (b + 2) (word 0 0)]) (b + 3) :=
    .cons (.const le_rfl) (.cons (.allocDyn (by omega) (by omega)) (.cons (.const (by omega)) .nil))
  have hS2 : Ssa (b + 3) [osLd (b + 2) (b + 1) 0, osLd cl (b + 1) 1] (b + 3) :=
    .cons (.store (by omega) (by omega)) (.cons (.store (by omega) (by omega)) .nil)
  have hS := hS1.append hS2
  have e : osHeap (2 * n) b ++ [osCst (b + 2) (word 0 0), osLd (b + 2) (b + 1) 0, osLd cl (b + 1) 1] =
      (osHeap (2 * n) b ++ [osCst (b + 2) (word 0 0)]) ++ [osLd (b + 2) (b + 1) 0, osLd cl (b + 1) 1] := by
    simp [osHeap]
  rw [e]
  have hv : ∀ σ', RangeVals σ' b (b + 3) (evalV (memOf H) (fun _ ↦ ICH) b (fun i ↦ σ (.n i))
      ((osHeap (2 * n) b ++ [osCst (b + 2) (word 0 0)]) ++ [osLd (b + 2) (b + 1) 0, osLd cl (b + 1) 1])) →
      σ' (.n b) = gw (2 * n) ∧ σ' (.n (b + 1)) = ICH ∧ σ' (.n (b + 2)) = word 0 0 := by
    intro σ' hr
    have e0 := (hr b le_rfl (by omega)).trans (hS1.evalV_lt hS2 _ (show b < b + 3 by omega))
    have e1 := (hr (b + 1) (by omega) (by omega)).trans (hS1.evalV_lt hS2 _ (show b + 1 < b + 3 by omega))
    have e2 := (hr (b + 2) (by omega) (by omega)).trans (hS1.evalV_lt hS2 _ (show b + 2 < b + 3 by omega))
    simp +arith [evalV, stepV, stepW, osHeap] at e0 e1 e2
    exact ⟨e0, e1, e2⟩
  refine ssa_blk (Pt := fun _ ↦ ICH) hS ?_ ?_
  · intro C rd hH σ' ha hr _
    obtain ⟨e0, e1, -⟩ := hv σ' hr
    refine ⟨e1, ?_⟩
    rw [allocsAt_append, allocsAt_append, allocsAt_heap σ' _ _ hn e0, e1]
    rfl
  · intro C rd hH σ' ha hr
    obtain ⟨-, e1, e2⟩ := hv σ' hr
    rw [sidesOk_append hS1]
    refine ⟨by simp [SidesOk, Side, osHeap], ?_⟩
    simp only [SidesOk, Side, stepW, show ¬ b + 3 ≤ b + 2 by omega, show ¬ b + 3 ≤ cl by omega,
      ↓reduceIte, and_true]
    rw [e1, e2, word_zero, ha _ hcl]
    exact hm C rd hH

/-- **The returns' loads and copies, honestly**: the inner chain's last two entries, the point
buffers, the sum and the final lane's value. -/
theorem finRet_complete {k ich pt yat acc : ℕ} {σ : Val} (hich : ich < k) (hpt : pt + 1 < k)
    (hyat : yat < k) (hacc : acc < k) {i0 i1 : E} {y : ℕ}
    (hm : ∀ C rd, H C rd → LoadHolds rd (σ (.n ich)) (2 * y + 1) i1 ∧ LoadHolds rd (σ (.n ich)) (2 * y) i0) :
    BlkA H σ k (k + 6) [osLd k ich (2 * y + 1), osCp (k + 1) pt, osCp (k + 2) (pt + 1),
      osLd (k + 3) ich (2 * y), osAdd (k + 4) (k + 3) acc, osCp (k + 5) yat]
      (fun σ' ↦ σ' (.n k) = i1 ∧ σ' (.n (k + 1)) = σ' (.n pt) ∧ σ' (.n (k + 2)) = σ' (.n (pt + 1)) ∧
        σ' (.n (k + 4)) = i0 + σ' (.n acc) ∧ σ' (.n (k + 5)) = σ' (.n yat)) := by
  have hS : SsaP k [osLd k ich (2 * y + 1), osCp (k + 1) pt, osCp (k + 2) (pt + 1),
      osLd (k + 3) ich (2 * y), osAdd (k + 4) (k + 3) acc, osCp (k + 5) yat] (k + 6) :=
    .load le_rfl hich (.copy (by omega) (by omega) (.copy (by omega) (by omega) (.load (by omega) (by omega)
      (.add (by omega) (by omega) (by omega) (.copy (by omega) (by omega) .nil)))))
  refine ssa_blk (Pt := fun _ ↦ 0) hS.toSsa (fun C rd hH σ' ha _ hok ↦ ?_)
    fun C rd hH σ' ha _ ↦ hS.sidesOk fun p o hpo ↦ ?_
  · simp only [allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load, holds_copy, holds_add, osLd,
      osCp, osAdd] at hok
    obtain ⟨l0, c1, c2, l3, a4, c5⟩ := hok
    rw [ha _ hich] at l0 l3
    exact ⟨loadHolds_unique l0 (hm C rd hH).1, c1, c2, by rw [a4, loadHolds_unique l3 (hm C rd hH).2], c5⟩
  · simp only [loadsOf, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hpo
    rw [ha _ (by rcases hpo with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact hich)]
    rcases hpo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [memOf_eq (fun C rd hH ↦ (hm C rd hH).1) hH]; exact (hm C rd hH).1
    · rw [memOf_eq (fun C rd hH ↦ (hm C rd hH).2) hH]; exact (hm C rd hH).2

/-- A block's statements hold wherever `H` does, beside its outcome. -/
theorem BlkA.okOut {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out : Val → Prop} (h : BlkA H σ k k' ss Out) :
    BlkA H σ k k' ss (fun σ' ↦ Out σ' ∧ ∀ C rd, H C rd → AllOk C rd σ' ss) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun C rd hH σ' ha hr ↦ ⟨(hf C rd hH σ' ha hr).1, (hf C rd hH σ' ha hr).2,
    fun C' rd' hH' ↦ (hf C' rd' hH' σ' ha hr).1⟩⟩

/-! ## No allocations -/

theorem osPtBlks_allocs (σ : Val) (c : OsCfg) (pt pt1 tch : ℕ) :
    ∀ n i k, AllocsAt σ (osPtBlks c pt pt1 tch i n k).1 = []
  | 0, _, _ => rfl
  | n + 1, i, k => by
    simp only [osPtBlks, allocsAt_append, osPtBlks_allocs σ c pt pt1 tch n, List.append_nil]
    unfold osPtBlk; split <;> rfl

theorem osBasisRow_allocs (σ : Val) (bd : ℕ) :
    ∀ cs sc after k, AllocsAt σ (osBasisRow bd cs sc after k).1 = []
  | [], _, _, _ => rfl
  | (slot, src, inv) :: rest, sc, after, k => by
    simp only [osBasisRow, allocsAt_append, osBasisRow_allocs σ bd rest, List.append_nil]
    unfold osBasisBlk; dsimp only
    split_ifs <;> rcases after with _ | x <;> rfl

theorem osBases_allocs (σ : Val) (c : OsCfg) (tch bd ls la : ℕ) :
    ∀ lvl lvs k, AllocsAt σ (osBases c tch bd ls la lvl lvs k).1 = []
  | _, [], _ => rfl
  | lvl, lv :: rest, k => by
    simp only [osBases]
    simp only [allocsAt_append]
    rw [allocsAt_cons, osBasisRow_allocs, osBases_allocs σ c tch bd ls la (lvl + 1) rest]
    rfl

/-! ## The out-of-domain weights' words -/

/-- **The words the out-of-domain weights read are fixed**: each level's scalars and points
(its record), and its coordinates' sources. -/
theorem oodLoads_pinned {c : OsCfg} {tch k : ℕ} {σ : Val} {G T : List E} {recs : List OsRec}
    {li : ℕ → E} {cl Y PT PT1 BD LS LA ICH : E} (hS : FinStatic c G T recs)
    (htch : tch < k) (hk : 33 ≤ k)
    (hm : ∀ C rd, H C rd → FinMem C rd σ c tch G T recs li cl Y PT PT1 BD LS LA ICH) {p o : ℕ} :
    ∀ (lvs : List OsLv) (ol : ℕ), 1 ≤ ol → lvs = c.levels.drop ol →
      OodLoads c tch (finLv c (ol - 1)).logCols ol lvs p o →
      p < k ∧ ∃ v, ∀ C rd, H C rd → LoadHolds rd (σ (.n p)) o v
  | [], _, _, _, h => h.elim
  | lv :: rest, ol, h1, hl, h => by
    have hol : ol < c.levels.length := by
      by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at hl; simp at hl
    have hlv : lv = finLv c ol := by
      have h2 : (c.levels.drop ol)[0]? = some lv := by rw [← hl]; rfl
      rw [List.getElem?_drop, Nat.add_zero] at h2
      simp [finLv, List.getD_eq_getElem?_getD, h2]
    have hy := hS.yr
    have hi : ol - 1 < c.yrLevel := by omega
    have hL := hS.lv (ol - 1) hi
    rw [show ol - 1 + 1 = ol by omega] at hL
    simp only [OodLoads] at h
    rcases h with hh | h
    · rcases hh with ⟨rfl, ho⟩ | ⟨rfl, x, hx, rfl⟩ | ⟨x, hx, he⟩
      · refine ⟨by show 28 < k; omega, (recs.getD (ol - 1) default).lam, fun C rd hH ↦ ?_⟩
        have hR := (hm C rd hH).stored (ol - 1) hi
        rw [ho]
        simpa [show ol - 1 + 1 = ol by omega] using hR.lam1
      · simp only [oodCoords, List.mem_map, List.mem_range] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        have hcl : (finLv c (ol - 1)).logCols - c.yrLog + c.yrLog = (finLv c (ol - 1)).logCols := by
          have := hL.pre; omega
        rw [hcl] at ht
        refine ⟨by show 26 < k; omega, (recs.getD (ol - 1) default).z0.getD t 0, fun C rd hH ↦ ?_⟩
        have hR := (hm C rd hH).stored (ol - 1) hi
        have := readsAt_getD' hR.z0 (by rw [hR.z0len]; exact ht)
        rw [loadHolds_mul_gen_pow] at this
        convert this using 2
        rw [show ol - 1 + 1 = ol by omega]
      · simp only [oodCoords, List.mem_map, List.mem_range] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        have hcl : (finLv c (ol - 1)).logCols - c.yrLog + c.yrLog = (finLv c (ol - 1)).logCols := by
          have := hL.pre; omega
        rw [hcl] at ht
        have hp1 := hL.pre
        have hp2 := hL.cols
        have hnx := hL.next
        have hG := hS.Gl
        have hT := hS.Tl
        split_ifs at he with h1
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          refine ⟨by show 16 < k; omega, G.getD (lv.foldsOff + t) 0, fun C rd hH ↦ ?_⟩
          have hj : lv.foldsOff + t < G.length := by rw [hlv]; omega
          have := (hm C rd hH).fch _ hj
          rwa [List.getD_eq_getElem _ _ hj]
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          refine ⟨htch, T.getD (t - ((finLv c (ol - 1)).logCols - c.yrLog)) 0, fun C rd hH ↦ ?_⟩
          exact readsAt_getD' (hm C rd hH).tchs (by omega)
    · rw [hlv] at h
      refine oodLoads_pinned hS htch hk hm rest (ol + 1) (by omega) ?_ (by simpa using h)
      rw [← List.drop_drop, ← hl]; simp

/-! ## The finish -/

theorem take_getD {c : OsCfg} {i : ℕ} (hi : i < c.yrLevel) :
    (c.levels.take c.yrLevel).getD i default = finLv c i := by
  simp only [finLv, List.getD_eq_getElem?_getD, List.getElem?_take, hi, ↓reduceIte]

theorem take_getElem {c : OsCfg} {i : ℕ} (hi : i < (c.levels.take c.yrLevel).length) :
    (c.levels.take c.yrLevel)[i] = finLv c i := by
  have hi' : i < c.yrLevel := by simp at hi; omega
  rw [← List.getD_eq_getElem _ default hi]
  simp only [finLv, List.getD_eq_getElem?_getD, List.getElem?_take, hi', ↓reduceIte]

/-- The finish's `basis_d` value. -/
def finBdV (c : OsCfg) (st : OsSt) (tch : ℕ) : ℕ :=
  (osPtBlks c (st.k + 1) (st.k + 1 + 1) tch 0 pointCap (st.k + 1 + 2)).2 + 1

/-- The finish's dispatches into `level_residual`, their arguments and returns. -/
def finResCalls (c : OsCfg) (st : OsSt) (tch : ℕ) : List (List V × List V) :=
  let pt := st.k + 1
  let pts := osPtBlks c pt (pt + 1) tch 0 pointCap (pt + 2)
  let bs := osBases c tch (pts.2 + 1) (pts.2 + 3) (pts.2 + 5) 0 (c.levels.take c.yrLevel) (pts.2 + 6)
  osResCallsL c (bs.2 + 1) (pts.2 + 1) (pts.2 + 3) (pts.2 + 5) 0 (c.levels.take c.yrLevel) st.mats (bs.2 + 3)

/-- The values the finish's dispatches into `level_residual` take and return under `σ'`. -/
def FinCallV (c : OsCfg) (st : OsSt) (tch : ℕ) (σ σ' : Val) (G T : List E) (recs : List OsRec) (li : ℕ → E)
    (BD : E) : Prop :=
  σ' (.n (finBdV c st tch)) = BD ∧
    ∀ l < c.yrLevel, ((finResCalls c st tch).getD l ([], [])).1.map σ' =
      [σ (.n osQpos) * gen ^ (finLv c l).posOff, BD * gen ^ (l * ligColsCap),
        σ (.n osHs) * gen ^ (l * hsStride), li l] ∧
      ((finResCalls c st tch).getD l ([], [])).2.map σ' =
        [(finRes c G T recs li l).1, (finRes c G T recs li l).2]

/-- **The finish before its return, honestly, what it returns and its loop calls' values**: its
statements hold at values fixed before the memory and the callees, allocating its buffers at the
given pointers; the returns are the closing claim plus the deficit times the closing challenges,
the point buffers, the glued weight at the terminal point and `fold_final_msg`'s value
(`osFinish_sound`'s). -/
theorem osFinishA_completeC {c : OsCfg} {st : OsSt} {tch : ℕ} {σ : Val} {G T : List E}
    {recs : List OsRec} {li : ℕ → E} {Y PT PT1 BD LS LA ICH : E}
    (hS : FinStatic c G T recs) (htch : tch < st.k) (hcl : st.claim < st.k) (hk : 33 ≤ st.k)
    (hmb : MatsBelow st.k st.mats) (hmo : ∀ C rd, H C rd → MatsOk σ st.mats)
    (hm : ∀ C rd, H C rd → FinMem C rd σ c tch G T recs li (σ (.n st.claim)) Y PT PT1 BD LS LA ICH) :
    BlkA H σ st.k (finEnd c st tch) (osFinishA c st tch).1
      (fun σ' ↦ (AllocsAt σ' (osFinishA c st tch).1 = finAllocs c PT PT1 BD LS LA ICH ∧
        (osFinishA c st tch).2.map σ' = [σ (.n st.claim) + T.prod * recsDeficit recs G, PT, PT1,
          (recs.flatMap recGlued).foldl (fun w g ↦ w + g.scalar * g.weightAt ((G ++ T).drop g.foldStart)) 0,
          Y]) ∧ FinCallV c st tch σ σ' G T recs li BD) := by
  set n := c.levels.length with hn
  set y := c.yrLevel with hy
  set mid := c.levels.take y with hmid
  set k0 := st.k with hk0
  set pts := osPtBlks c (k0 + 1) (k0 + 1 + 1) tch 0 pointCap (k0 + 1 + 2) with hpts
  set P2 := pts.2 with hP2
  set bs := osBases c tch (P2 + 1) (P2 + 3) (P2 + 5) 0 mid (P2 + 6) with hbs
  set B := bs.2 with hB
  set rs := osResiduals c (B + 1) (P2 + 1) (P2 + 3) (P2 + 5) 0 mid st.mats (B + 3) with hrs
  set od := osOodWeights c tch (c.levels.headD default).logCols 1 c.levels.tail none rs.2 with hod
  set K := od.2.2 with hK
  have hyn : y = n - 1 := hS.yr
  have hn2 := hS.n2
  have hn6 := hS.n6
  have hmidl : mid.length = y := by rw [hmid, List.length_take]; omega
  -- the watermarks
  have w1 : k0 + 1 + 2 ≤ P2 := osPtBlks_next c _ _ tch pointCap 0 _
  have w2 : P2 + 6 ≤ B := osBases_next c tch _ _ _ mid 0 _
  have w3 : B + 3 ≤ rs.2 := osResiduals_next c _ _ _ _ mid 0 st.mats (B + 3)
  obtain ⟨o1, o2, o3⟩ := osOodWeights_ssa c tch (c.levels.headD default).logCols 1 c.levels.tail none
    rs.2 (by omega) (by omega) (by simp)
  have w4 : rs.2 ≤ K := o1.le
  -- the blocks
  have b0 := fin0_complete (H := H) (f := "fold_final_msg__L" ++ natStr c.yrLog) (k := k0) (tch := tch)
    (σ := σ) (Y := Y) (PT := PT) (PT1 := PT1) htch hk fun C rd hH ↦ (hm C rd hH).ffm
  have s1 := BlkA.seq (H := H) (by omega) (show k0 + 1 + 2 ≤ P2 from w1) b0 fun σ1 ha1 hO1 ↦
    osPtBlks_complete (H := H) (c := c) (pt := k0 + 1) (pt1 := k0 + 1 + 1) (tch := tch)
      (fun i ↦ (rotPt G T (c.levels.headD default).folds).getD i 0) pointCap 0 (k0 + 1 + 2) σ1
      (by omega) (by omega) (by show 16 < k0 + 1 + 2; omega) (by omega) fun j hj C rd hH ↦ by
        obtain ⟨-, e1, e2, -⟩ := hO1 C rd hH
        have hM := hm C rd hH
        refine ⟨?_, ?_, ?_⟩
        · have := ptSrc_ok (rd := rd) (σ := σ1) (c := c) (tch := tch) hS.Gl hS.Tl hS.lane
            (by rw [ha1 _ (by show 16 < k0; omega)]; exact hM.fch)
            (by rw [ha1 _ htch]; exact hM.tchs) (0 + j)
          exact this
        · rw [e1, ← finPtC_getD hS]
          exact readsAt_getD' hM.pt (by rw [finPtC_length c hS]; omega)
        · rw [e2, ← finPt1C_getD hS (by omega)]
          exact readsAt_getD' hM.pt1 (by rw [finPt1C_length c hS]; omega)
  have s2 := BlkA.seq (H := H) (show k0 ≤ P2 by omega) (show P2 ≤ P2 + 6 by omega) s1 fun σ2 _ _ ↦
    finHeaps_complete (H := H) (n := n) (p := P2) (σ := σ2) (BD := BD) (LS := LS) (LA := LA) hn6
  have hpos : ∀ lv : OsLv, 1 ≤ lv.prefixLen + c.yrLog := fun _ ↦ by have := hS.ylog; omega
  have hyl : y < n := by omega
  have s3 := BlkA.seq (H := H) (show k0 ≤ P2 + 6 by omega) w2 s2 fun σ3 ha3 hO3 ↦
    osBases_complete (H := H) (c := c) (tch := tch) (bd := P2 + 1) (ls := P2 + 3) (la := P2 + 5)
      (finBeta c recs) (finX G T recs) hpos mid 0 (P2 + 6) σ3 (by omega) (by omega) (by omega) (by omega)
      (by omega) (fun i hi t ht ↦ by
        rw [take_getElem hi] at ht ⊢
        rw [Nat.zero_add]
        exact finX_ne hS (by omega) (hS.recF i (by omega)) t ht)
      fun i hi C rd hH ↦ by
        have hi' : i < y := by rw [← hmidl]; exact hi
        obtain ⟨-, e1, e3, e5, -⟩ := hO3 C rd hH
        have hM := hm C rd hH
        have hL := hS.lv i hi'
        have hR := hM.stored i hi'
        rw [take_getElem hi, Nat.zero_add]
        refine ⟨⟨?_, fun t ht ↦ ⟨invW_ne hL.mu64 hL.inv t (by have := hL.pre; omega), ?_⟩⟩,
          fun t ht ↦ ⟨finX_ne hS hi' (hS.recF i hi') t ht, ?_⟩, ?_, ?_⟩
        · rw [ha3 osBetas (by show 20 < k0; omega)]; exact hR.beta
        · have := finX_src hS hM.fch hM.tchs hi' (hS.recF i hi') t ht
          rwa [ha3 _ (coordSrc_lt (by show 16 < k0; omega) htch)]
        · obtain ⟨-, eb⟩ := finBdC_get (G := G) (T := T) (recs := recs) hi' (by omega) ht
            (by have := hS.cols i hi'; have := hL.pre; omega)
          rw [e1]
          have := readsAt_getD' hM.bd (j := i * ligColsCap + t) (by
            rw [(finBdC_get (G := G) (T := T) (recs := recs) hi' (by omega) ht
              (by have := hS.cols i hi'; have := hL.pre; omega)).1]
            have : (i + 1) * ligColsCap ≤ n * ligColsCap := Nat.mul_le_mul_right _ (by omega)
            rw [Nat.add_mul, Nat.one_mul] at this
            have := hS.cols i hi'; have := hL.pre; unfold ligColsCap at *; omega)
          rw [eb] at this
          exact this
        · obtain ⟨hl, eb⟩ := finLsC_get (G := G) (T := T) (recs := recs) hi' (by omega)
          rw [e3]
          have := readsAt_getD' hM.ls (j := i) (by rw [hl]; omega)
          rwa [eb] at this
        · obtain ⟨hl, eb⟩ := finLaC_get (G := G) (T := T) (recs := recs) hi' (by omega)
          rw [e5]
          have := readsAt_getD' hM.la (j := i) (by rw [hl]; omega)
          rwa [eb] at this
  have s4 := BlkA.seq (H := H) (show k0 ≤ B by omega) (show B ≤ B + 3 by omega) s3 fun σ4 ha4 _ ↦
    finIch0_complete (H := H) (n := n) (b := B) (cl := st.claim) (ICH := ICH) (σ := σ4)
      (by omega) (by omega) fun C rd hH ↦ by
        have hM := hm C rd hH
        obtain ⟨hl, g0, g1⟩ := finIchC_get (c := c) (G := G) (T := T) (recs := recs) (li := li)
          (cl := σ (.n st.claim)) (j := 0) (by omega)
        simp only [Nat.mul_zero, Nat.zero_add, finIch, Finset.range_zero, Finset.sum_empty, add_zero] at g0 g1
        rw [ha4 _ hcl]
        refine ⟨?_, ?_⟩
        · have := readsAt_getD' hM.ich (j := 0) (by rw [hl]; omega)
          rwa [g0] at this
        · have := readsAt_getD' hM.ich (j := 1) (by rw [hl]; omega)
          rwa [g1] at this
  have s5 := BlkA.seq (H := H) (show k0 ≤ B + 3 by omega) w3 s4
    (B := rs.1) (OutB := fun σ' ↦ AllocsAt σ' rs.1 = [] ∧ ∀ i < mid.length,
      ((osResCallsL c (B + 1) (P2 + 1) (P2 + 3) (P2 + 5) 0 mid st.mats (B + 3)).getD i ([], [])).1.map σ' =
        [σ (.n osQpos) * gen ^ (mid.getD i default).posOff, BD * gen ^ ((0 + i) * ligColsCap),
          σ (.n osHs) * gen ^ ((0 + i) * hsStride), li (0 + i)] ∧
      ((osResCallsL c (B + 1) (P2 + 1) (P2 + 3) (P2 + 5) 0 mid st.mats (B + 3)).getD i ([], [])).2.map σ' =
        [(finRes c G T recs li (0 + i)).1, (finRes c G T recs li (0 + i)).2]) fun σ5 ha5 hO5 ↦
    BlkA.of_ne (H := H) fun ⟨C0, rd0, hH0⟩ ↦ by
    obtain ⟨⟨⟨⟨-, -⟩, e1, -, -, -⟩, -⟩, -, -⟩ := hO5 C0 rd0 hH0
    have q5 : σ5 (.n osQpos) = σ (.n osQpos) := ha5 osQpos (by show 30 < k0; omega)
    have h5 : σ5 (.n osHs) = σ (.n osHs) := ha5 osHs (by show 24 < k0; omega)
    have h := osResiduals_complete (H := H) (c := c) (ich := B + 1) (bd := P2 + 1) (ls := P2 + 3) (la := P2 + 5)
      li (fun i ↦ (finIch c G T recs li (σ (.n st.claim)) i).1)
      (fun i ↦ (finIch c G T recs li (σ (.n st.claim)) i).2)
      (fun i ↦ (finLsC c G T recs).getD i 0) (finBeta c recs) (fun i ↦ (finLaC c G T recs).getD i 0)
      (fun i ↦ (finRes c G T recs li i).1) (fun i ↦ (finRes c G T recs li i).2)
      mid 0 st.mats (B + 3) σ5 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun m hm' ↦ by obtain ⟨x, y, z⟩ := hmb m hm'; exact ⟨by omega, by omega, by omega⟩)
      (fun C rd hH ↦ matsOk_agree (hmo C rd hH) hmb fun i hi ↦ ha5 i hi)
      (fun i hi ↦ by
        have hi' : i < y := by rw [← hmidl]; exact hi
        rw [Nat.zero_add, take_getD hi']
        have := hS.n6
        exact ⟨(hS.lv i hi').posOff, by unfold u128Bound ligColsCap; omega,
          by unfold u128Bound hsStride; omega⟩)
      (fun i hi C rd hH ↦ by
        have hi' : i < y := by rw [← hmidl]; exact hi
        obtain ⟨ri, hri, hx, hlen, hlv⟩ := (hm C rd hH).rate i hi'
        rw [Nat.zero_add, take_getD hi']
        exact ⟨ri, hri, by rw [ha5 _ (show 0 < k0 by omega)]; exact hx, hlen, hlv⟩)
      (fun i hi C rd hH ↦ by
        have hi' : i < y := by rw [← hmidl]; exact hi
        obtain ⟨⟨⟨⟨-, -⟩, e1, e3, e5, -⟩, -⟩, eI, -⟩ := hO5 C rd hH
        have hM := hm C rd hH
        have hR := hM.stored i hi'
        rw [Nat.zero_add]
        obtain ⟨hl, g0, g1⟩ := finIchC_get (c := c) (G := G) (T := T) (recs := recs) (li := li)
          (cl := σ (.n st.claim)) (j := i) (by omega)
        obtain ⟨-, g2, g3⟩ := finIchC_get (c := c) (G := G) (T := T) (recs := recs) (li := li)
          (cl := σ (.n st.claim)) (j := i + 1) (by omega)
        have hich : ∀ j < 2 * n, LoadHolds rd (σ5 (.n (B + 1))) j
            ((finIchC c G T recs li (σ (.n st.claim))).getD j 0) := fun j hj ↦ by
          rw [eI]; exact readsAt_getD' hM.ich (by rw [hl]; exact hj)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [ha5 osMus (by show 22 < k0; omega)]; exact hM.mus i hi'
        · have := hich (2 * i) (by omega); rwa [g0] at this
        · have := hich (2 * i + 1) (by omega); rwa [g1] at this
        · rw [e3]; exact readsAt_getD' hM.ls (by rw [(finLsC_get (G := G) (T := T) (recs := recs) hi' (by omega)).1]; omega)
        · rw [ha5 osBetas (by show 20 < k0; omega)]; exact hR.beta
        · rw [e5]; exact readsAt_getD' hM.la (by rw [(finLaC_get (G := G) (T := T) (recs := recs) hi' (by omega)).1]; omega)
        · have := hich (2 * i + 2) (by omega)
          rw [show 2 * i + 2 = 2 * (i + 1) by ring, g2] at this
          convert this using 2
          simp only [finIch, Finset.sum_range_succ, finRes]
        · have := hich (2 * i + 3) (by omega)
          rw [show 2 * i + 3 = 2 * (i + 1) + 1 by ring, g3] at this
          convert this using 2
          simp only [finIch, Finset.sum_range_succ, finRes, add_assoc])
      (fun i hi C rd hH ↦ by
        have hi' : i < y := by rw [← hmidl]; exact hi
        rw [Nat.zero_add, take_getD hi', e1, q5, h5]
        exact (hm C rd hH).res i hi')
    refine h.mono fun σ' hv ↦ ⟨by
      show AllocsAt σ' (osResiduals c (B + 1) (P2 + 1) (P2 + 3) (P2 + 5) 0 mid st.mats (B + 3)).1 = []
      simp only [AllocsAt, osResiduals_allocs, List.map_nil], fun i hi ↦ ?_⟩
    obtain ⟨v1, v2⟩ := hv i hi
    rw [q5, h5, e1] at v1
    exact ⟨v1, v2⟩
  have s6 := BlkA.seq (H := H) (show k0 ≤ rs.2 by omega) w4 s5 fun σ6 ha6 _ ↦
    BlkA.okOut <| pure_blk (H := H) o1 fun p o hpo ↦ by
      have hhead : (c.levels.headD default).logCols = (finLv c (1 - 1)).logCols := by
        simp [finLv, List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getD_eq_getElem?_getD]
      have hp := oodLoads_pinned (k := k0) hS htch hk hm c.levels.tail 1 le_rfl (by simp)
        (by rw [← hhead]; exact o3 p o hpo)
      obtain ⟨hpk, v, hv⟩ := hp
      exact ⟨by omega, v, fun C rd hH ↦ by rw [ha6 _ hpk]; exact hv C rd hH⟩
  have hacc : od.2.1.getD 0 < K := by
    rcases h : od.2.1 with _ | x
    · simp only [Option.getD_none]; omega
    · simp only [Option.getD_some]; exact o2 x h
  have s7 := BlkA.seq (H := H) (show k0 ≤ K by omega) (show K ≤ K + 6 by omega) s6 fun σ7 ha7 hO7 ↦
    finRet_complete (H := H) (k := K) (ich := B + 1) (pt := k0 + 1) (yat := k0) (acc := od.2.1.getD 0)
      (σ := σ7) (y := y) (i0 := (finIch c G T recs li (σ (.n st.claim)) y).1)
      (i1 := (finIch c G T recs li (σ (.n st.claim)) y).2) (by omega) (by omega) (by omega) hacc
      fun C rd hH ↦ by
        obtain ⟨⟨⟨-, eI, -⟩, -⟩, -⟩ := hO7 C rd hH
        have hM := hm C rd hH
        obtain ⟨hl, g0, g1⟩ := finIchC_get (c := c) (G := G) (T := T) (recs := recs) (li := li)
          (cl := σ (.n st.claim)) (j := y) (by omega)
        rw [eI]
        refine ⟨?_, ?_⟩
        · have := readsAt_getD' hM.ich (j := 2 * y + 1) (by rw [hl]; omega); rwa [g1] at this
        · have := readsAt_getD' hM.ich (j := 2 * y) (by rw [hl]; omega); rwa [g0] at this
  have e : (osFinishA c st tch).1 = [.call ("fold_final_msg__L" ++ natStr c.yrLog) [.n osFmsg, .n tch] [.n k0],
      .atom (.hint (.alloc (.n (k0 + 1)) pointCap)), .atom (.hint (.alloc (.n (k0 + 1 + 1)) pointCap))] ++
      pts.1 ++ (osHeap (n * ligColsCap) P2 ++ osHeap n (P2 + 2) ++ osHeap n (P2 + 4)) ++ bs.1 ++
      (osHeap (2 * n) B ++ [osCst (B + 2) (word 0 0), osLd (B + 2) (B + 1) 0, osLd st.claim (B + 1) 1]) ++
      rs.1 ++ od.1 ++ [osLd K (B + 1) (2 * y + 1), osCp (K + 1) (k0 + 1), osCp (K + 2) (k0 + 1 + 1),
        osLd (K + 3) (B + 1) (2 * y), osAdd (K + 4) (K + 3) (od.2.1.getD 0), osCp (K + 5) k0] := by
    simp only [osFinishA, List.append_assoc]
    rfl
  have hend : finEnd c st tch = K + 6 := rfl
  rw [hend, e]
  refine s7.monoH fun C rd hH σ' ha hσ' ↦ ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -, -, a0⟩, -⟩, ⟨-, -, -, a2⟩⟩, -⟩, ⟨-, a4⟩⟩, a5, -⟩, ⟨a6, -⟩⟩, -⟩ := hσ'
    have p1 : AllocsAt σ' pts.1 = [] := osPtBlks_allocs σ' c _ _ tch pointCap 0 _
    have p3 : AllocsAt σ' bs.1 = [] := osBases_allocs σ' c tch _ _ _ 0 mid _
    have p5 : AllocsAt σ' rs.1 = [] := a5
    have p6 : AllocsAt σ' od.1 = [] := a6
    simp only [allocsAt_append, a0, a2, a4, p1, p3, p5, p6]
    rw [show AllocsAt σ' [osLd K (B + 1) (2 * y + 1), osCp (K + 1) (k0 + 1), osCp (K + 2) (k0 + 1 + 1),
        osLd (K + 3) (B + 1) (2 * y), osAdd (K + 4) (K + 3) (od.2.1.getD 0), osCp (K + 5) k0] = [] from rfl]
    simp only [finAllocs, List.nil_append, List.append_nil, List.cons_append, hn]
  · obtain ⟨⟨⟨⟨⟨⟨⟨⟨y0, e1, e2, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, ⟨-, okod⟩⟩, r0, r1, r2, r4, r5⟩ := hσ'
    have hM := hm C rd hH
    have hok := okod C rd hH
    -- the levels' facts
    set r : ℕ → OsRec := fun i ↦ recs.getD i default with hr
    have hRS : ∀ i < y, RecStored rd σ i (finLv c i) (r i) := hM.stored
    have hLF : ∀ i < y, LvFin c (finLv c i) (finLv c (i + 1)) := hS.lv
    have hli : ∀ i < y, (r i).lam * li i = 1 := fun i hi ↦ by
      obtain ⟨l', hl1, hl2⟩ := (hRS i hi).mus
      rw [loadHolds_unique (hM.mus i hi) hl1]; exact hl2
    have hrl : recs.length = y := hS.recl
    -- the out-of-domain weights
    have htl : c.levels.tail.length = y := by simp [hy, hS.yr]
    have htail : ∀ i, c.levels.tail.getD i default = finLv c (i + 1) := fun i ↦ by
      simp only [finLv, List.getD_eq_getElem?_getD, List.getElem?_tail]
    set W : ℕ → E := fun i ↦ (r i).lam *
      ∏ t ∈ Finset.range (finLv c i).logCols, (1 + (r i).z0.getD t 0 + finX G T recs i t) with hW
    have hhead : (c.levels.headD default).logCols = (fun i ↦ (finLv c i).logCols) 0 := by
      simp only [finLv, List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getD_eq_getElem?_getD]
    have hok' : AllOk C rd σ' (osOodWeights c tch ((fun i ↦ (finLv c i).logCols) 0) 1 c.levels.tail none
        rs.2).1 := by rw [← hhead]; exact hok
    have hOd := osOodWeights_val (C := C) (rd := rd) (σ := σ') (c := c) (tch := tch) c.levels.tail
      (fun i ↦ (finLv c i).logCols) 1 none rs.2 W (fun i hi k hok'' ↦ by
        rw [htl] at hi
        have hL := hLF i hi
        have hR := hRS i hi
        rw [htail] at hok'' ⊢
        have hcl : (finLv c i).logCols - c.yrLog + c.yrLog = (finLv c i).logCols := by
          have := hL.pre; omega
        have hv := osOodWeight_val (lam := (r i).lam) (z := fun t ↦ (r i).z0.getD t 0)
          (p := finX G T recs i) (C := C) ?_ ?_ ?_ hok''
        · rw [hv, hcl]
        · rw [ha osOodSc (by show 28 < k0; omega)]
          simpa [add_comm 1 i] using hR.lam1
        · intro t ht
          rw [hcl] at ht
          rw [ha osOodz (by show 26 < k0; omega)]
          have := hR.z0 t (by rw [hR.z0len]; exact ht)
          rw [loadHolds_mul_gen_pow] at this
          simp only [List.getD_eq_getElem _ _ (show t < (r i).z0.length by rw [hR.z0len]; exact ht)]
          convert this using 2
          ring
        · intro t ht
          rw [hcl] at ht
          have hx := finX_src hS hM.fch hM.tchs hi (hS.recF i hi) t (by rw [hL.pre]; exact ht)
          have hpre : (finLv c i).logCols - c.yrLog = (finLv c i).prefixLen := by have := hL.pre; omega
          simp only [coordSrc] at hx
          rw [hpre, hL.next, ← hL.rfo]
          split_ifs at hx ⊢
          · rw [ha osFch (by show 16 < k0; omega)]; exact hx
          · rw [ha _ htch]; exact hx)
      (fun i hi ↦ by rw [htail]) hok'
    obtain ⟨x, hx⟩ := osOodWeights_some (c := c) (tch := tch) c.levels.tail ((fun i ↦ (finLv c i).logCols) 0) 1
      none rs.2 (by intro h; rw [h] at htl; simp at htl; omega)
    have hacc : σ' (.n (od.2.1.getD 0)) = ∑ i ∈ Finset.range y, W i := by
      have := hOd
      have hodd : od = osOodWeights c tch ((fun i ↦ (finLv c i).logCols) 0) 1 c.levels.tail none rs.2 := by
        rw [hod, hhead]
      rw [hodd, hx]
      rw [hx] at this
      simp only [accVal, zero_add, htl] at this
      exact this
    -- each level's terms
    have hterms : ∀ i < y,
        (finLsC c G T recs).getD i 0 * (finRes c G T recs li i).1 + W i =
          (r i).lam * eqEval (r i).z0 ((G ++ T).drop (r i).F) +
          (r i).lam * (r i).lam *
            inducedWeight (r i).mu (r i).qs (powers (r i).lam (r i).qs.length) ((G ++ T).drop (r i).F) ∧
        finBeta c recs i * (finLaC c G T recs).getD i 0 * (finRes c G T recs li i).2 =
          T.prod * ((r i).lam ^ 2 * recH (r i) * (G.drop (r i).F).prod) := by
      intro i hi
      have hL := hLF i hi
      have hR := hRS i hi
      have h := lvl_terms hL hS.Gl hS.Tl hR.F hR.mu hR.qlen hR.hlen hR.z0len (hli i hi)
        (fun t ht ↦ finX_ne hS hi (hS.recF i hi) t (by rw [hL.pre]; exact ht))
      obtain ⟨-, el⟩ := finLsC_get (G := G) (T := T) (recs := recs) hi (by omega)
      obtain ⟨-, ea⟩ := finLaC_get (G := G) (T := T) (recs := recs) hi (by omega)
      rw [el, ea, hL.pre]
      have w0 : W i = (r i).lam * eqEval (r i).z0 ((G ++ T).drop (r i).F) := h.2.2
      refine ⟨?_, h.2.1⟩
      rw [w0]
      have h1 := h.1
      delta finX finBeta finRes finD
      simp only [hr] at h1 ⊢
      rw [h1]
      ring
    have er : (osFinishA c st tch).2 = [V.n K, V.n (K + 1), V.n (K + 2), V.n (K + 4), V.n (K + 5)] := rfl
    rw [er]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨?_, by rw [r1, e1], by rw [r2, e2], ?_, by rw [r5, y0]⟩
    · rw [r0]
      simp only [finIch]
      rw [recsDeficit, sum_list_range, hrl, Finset.mul_sum]
      exact congrArg (_ + ·) (Finset.sum_congr rfl fun i hi ↦ (hterms i (Finset.mem_range.mp hi)).2)
    · rw [r4, hacc, inner_sum, hrl]
      simp only [finIch]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      exact (hterms i (Finset.mem_range.mp hi)).1
  · obtain ⟨⟨⟨⟨⟨⟨-, eBD, -⟩, -⟩, -⟩, -, hcalls⟩, -⟩, -⟩ := hσ'
    refine ⟨eBD, fun l hl ↦ ?_⟩
    have := hcalls l (by omega)
    rw [Nat.zero_add, take_getD (by omega)] at this
    exact this

/-- **The finish before its return, honestly, and what it returns.** -/
theorem osFinishA_completeR {c : OsCfg} {st : OsSt} {tch : ℕ} {σ : Val} {G T : List E}
    {recs : List OsRec} {li : ℕ → E} {Y PT PT1 BD LS LA ICH : E}
    (hS : FinStatic c G T recs) (htch : tch < st.k) (hcl : st.claim < st.k) (hk : 33 ≤ st.k)
    (hmb : MatsBelow st.k st.mats) (hmo : ∀ C rd, H C rd → MatsOk σ st.mats)
    (hm : ∀ C rd, H C rd → FinMem C rd σ c tch G T recs li (σ (.n st.claim)) Y PT PT1 BD LS LA ICH) :
    BlkA H σ st.k (finEnd c st tch) (osFinishA c st tch).1
      (fun σ' ↦ AllocsAt σ' (osFinishA c st tch).1 = finAllocs c PT PT1 BD LS LA ICH ∧
        (osFinishA c st tch).2.map σ' = [σ (.n st.claim) + T.prod * recsDeficit recs G, PT, PT1,
          (recs.flatMap recGlued).foldl (fun w g ↦ w + g.scalar * g.weightAt ((G ++ T).drop g.foldStart)) 0,
          Y]) :=
  (osFinishA_completeC hS htch hcl hk hmb hmo hm).mono fun _ h ↦ h.1

/-- **The finish before its return, honestly**: its statements hold at values fixed before the
memory and the callees, allocating its buffers at the given pointers. -/
theorem osFinishA_complete {c : OsCfg} {st : OsSt} {tch : ℕ} {σ : Val} {G T : List E}
    {recs : List OsRec} {li : ℕ → E} {Y PT PT1 BD LS LA ICH : E}
    (hS : FinStatic c G T recs) (htch : tch < st.k) (hcl : st.claim < st.k) (hk : 33 ≤ st.k)
    (hmb : MatsBelow st.k st.mats) (hmo : ∀ C rd, H C rd → MatsOk σ st.mats)
    (hm : ∀ C rd, H C rd → FinMem C rd σ c tch G T recs li (σ (.n st.claim)) Y PT PT1 BD LS LA ICH) :
    BlkA H σ st.k (finEnd c st tch) (osFinishA c st tch).1
      (fun σ' ↦ AllocsAt σ' (osFinishA c st tch).1 = finAllocs c PT PT1 BD LS LA ICH) :=
  (osFinishA_completeC hS htch hcl hk hmb hmo hm).mono fun _ h ↦ h.1.1

end
end LeanVM.Guest.B1.Whir
