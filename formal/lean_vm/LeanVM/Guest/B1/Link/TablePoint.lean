/-
  LeanVM.Guest.B1.Link.TablePoint

  B1 for `table_point` (row logs `0` to `24`): a table's row weight, `LT_rows` and `eq(τ, χ)`.
-/

module

public import LeanVM.Guest.B1.Link.IndexSide

/-!
# `table_point`

`table_point(theta, tau, chi, bits, h)` (G) runs over the coordinates `k < h`: `hi = t·x`,
`e = 1 + t + x`, `low = hi + e`, `high = hi`, `full[k + 1] = full[k]·e`, and the pad
`c·x + (c + x)·pad` from the complement bit `c = bits[k]`; then from `top = bits[h]` the walk
from the top (`tpStep`, `j = h - 1` down to `0`, the bit `1 + bits[j]`); it returns `θ·total`,
`1 + (1 + top)·pad` and `full[h]`. Its specialization `table_point__L{h}` is `tpBody h`: the
forward block `k` from value `14 k + 4` (`tpFwd`, the first with the pad's start folded in),
`top` (`tpTop`), the walk's block `jj` (`tpWalkBlk`, the first with the prefix's start folded in),
the end (`tpEnd`). `Forms.lean` makes the three `omegaAt`, `lessThan` and `eqEval`.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The meaning -/

/-- `table_point`'s coordinate terms from the lists `ts` (`τ`), `xs` (`χ`). -/
def tpLow (ts xs : List E) (j : ℕ) : E :=
  ts.getD j 0 * xs.getD j 0 + (1 + ts.getD j 0 + xs.getD j 0)

def tpHigh (ts xs : List E) (j : ℕ) : E := ts.getD j 0 * xs.getD j 0

def tpFullAt (ts xs : List E) (j : ℕ) : E :=
  prodE ((List.range j).map fun i ↦ 1 + ts.getD i 0 + xs.getD i 0)

/-- `table_point`'s total before `θ`, from the complement bits `cs` and `top`. -/
def tpTotalG (ts xs cs : List E) (top : E) (h : ℕ) : E :=
  tpTotal (tpLow ts xs) (tpHigh ts xs) (tpFullAt ts xs) (fun j ↦ 1 + cs.getD j 0) top h

/-- **`table_point(theta, tau, chi, bits, h)`**: the `h` words `ts` at `tau`, `xs` at `chi` and
`cs` at `bits`, `top` at `bits[h]`; it returns `θ·tpTotalG`, `1 + (1 + top)·tpPad cs xs` and
`tpFullAt ts xs h`. -/
def MeaningTablePoint (h : ℕ) (rd : Reader) : List E → List E → Prop
  | [theta, tau, chi, bits], rets => ∃ ts xs cs : List E, ∃ top : E, ts.length = h ∧
      xs.length = h ∧ cs.length = h ∧ ReadsAt rd tau ts ∧ ReadsAt rd chi xs ∧ ReadsAt rd bits cs ∧
      LoadHolds rd bits h top ∧
      rets = [theta * tpTotalG ts xs cs top h, 1 + (1 + top) * tpPad cs xs, tpFullAt ts xs h]
  | _, _ => False

/-- The specializations' names, `table_point__L{h}`, `h ≤ 24` (`N_ROW_LOGS`). -/
def tpNames : List String := ["table_point__L0", "table_point__L1", "table_point__L2", "table_point__L3", "table_point__L4", "table_point__L5", "table_point__L6", "table_point__L7", "table_point__L8", "table_point__L9", "table_point__L10", "table_point__L11", "table_point__L12", "table_point__L13", "table_point__L14", "table_point__L15", "table_point__L16", "table_point__L17", "table_point__L18", "table_point__L19", "table_point__L20", "table_point__L21", "table_point__L22", "table_point__L23", "table_point__L24"]

/-- `table_point__L{h}`'s core IR implies its meaning. -/
def table_point_SoundP (P : Program) : Prop :=
  ∀ h ≤ 24, ∀ (rd : Reader) (args rets : List E),
    P.Rel rd (tpNames.getD h "") args rets → MeaningTablePoint h rd args rets

/-! ## The template -/

/-- The forward pass's values: `t`, `x`, `low`, `high`, `c`, `pad` at coordinate `k`, and
`full[j]`. -/
def tpT (k : ℕ) : ℕ := if k = 0 then 5 else 14 * k + 4
def tpX (k : ℕ) : ℕ := if k = 0 then 6 else 14 * k + 5
def tpLo (k : ℕ) : ℕ := if k = 0 then 11 else 14 * k + 10
def tpHi (k : ℕ) : ℕ := if k = 0 then 12 else 14 * k + 11
def tpC (k : ℕ) : ℕ := if k = 0 then 14 else 14 * k + 13
def tpPd (k : ℕ) : ℕ := 14 * k + 17
def tpFu (j : ℕ) : ℕ := if j = 0 then 4 else if j = 1 then 13 else 14 * j - 2

/-- Forward block `k`. -/
def tpFwd (k : ℕ) : List Stmt :=
  if k = 0 then
    [.atom (.load (.n 5) (.n 1) 0), .atom (.load (.n 6) (.n 2) 0), .atom (.mul (.n 7) (.n 5) (.n 6)),
      .atom (.const (.n 8) (word 1 0)), .atom (.add (.n 9) (.n 8) (.n 5)),
      .atom (.add (.n 10) (.n 9) (.n 6)), .atom (.add (.n 11) (.n 7) (.n 10)),
      .atom (.copy (.n 12) (.n 7)), .atom (.mul (.n 13) (.n 4) (.n 10)),
      .atom (.load (.n 14) (.n 3) 0), .atom (.mul (.n 15) (.n 14) (.n 6)),
      .atom (.add (.n 16) (.n 14) (.n 6)), .atom (.add (.n 17) (.n 15) (.n 16))]
  else
    let b := 14 * k + 4
    [.atom (.load (.n b) (.n 1) k), .atom (.load (.n (b + 1)) (.n 2) k),
      .atom (.mul (.n (b + 2)) (.n b) (.n (b + 1))), .atom (.const (.n (b + 3)) (word 1 0)),
      .atom (.add (.n (b + 4)) (.n (b + 3)) (.n b)), .atom (.add (.n (b + 5)) (.n (b + 4)) (.n (b + 1))),
      .atom (.add (.n (b + 6)) (.n (b + 2)) (.n (b + 5))), .atom (.copy (.n (b + 7)) (.n (b + 2))),
      .atom (.mul (.n (b + 8)) (.n (tpFu k)) (.n (b + 5))), .atom (.load (.n (b + 9)) (.n 3) k),
      .atom (.mul (.n (b + 10)) (.n (b + 9)) (.n (b + 1))),
      .atom (.add (.n (b + 11)) (.n (b + 9)) (.n (b + 1))),
      .atom (.mul (.n (b + 12)) (.n (b + 11)) (.n (tpPd (k - 1)))),
      .atom (.add (.n (b + 13)) (.n (b + 10)) (.n (b + 12)))]

/-- `top`'s value. -/
def tpTopV (h : ℕ) : ℕ := if h = 0 then 5 else 14 * h + 4

/-- The walk's block `jj` (coordinate `h - 1 - jj`): its first value, its total and prefix. -/
def tpWB (h jj : ℕ) : ℕ := if jj = 0 then tpTopV h + 2 else tpTopV h + 11 * jj

def tpTot (h jj : ℕ) : ℕ := if jj = 0 then tpTopV h + 7 else tpTopV h + 11 * jj + 6

def tpPre (h jj : ℕ) : ℕ := if jj = 0 then tpTopV h + 10 else tpTopV h + 11 * jj + 10

/-- The walk's block `jj`. -/
def tpWalkBlk (h jj : ℕ) : List Stmt :=
  let j := h - 1 - jj
  let b := tpWB h jj
  if jj = 0 then
    [.atom (.const (.n b) (word 1 0)), .atom (.load (.n (b + 1)) (.n 3) j),
      .atom (.add (.n (b + 2)) (.n b) (.n (b + 1))), .atom (.mul (.n (b + 3)) (.n (b + 2)) (.n (tpLo j))),
      .atom (.mul (.n (b + 4)) (.n (b + 3)) (.n (tpFu j))),
      .atom (.add (.n (b + 5)) (.n (tpTopV h + 1)) (.n (b + 4))),
      .atom (.add (.n (b + 6)) (.n (tpHi j)) (.n (tpLo j))),
      .atom (.mul (.n (b + 7)) (.n (b + 2)) (.n (b + 6))),
      .atom (.add (.n (b + 8)) (.n (tpLo j)) (.n (b + 7)))]
  else
    [.atom (.const (.n b) (word 1 0)), .atom (.load (.n (b + 1)) (.n 3) j),
      .atom (.add (.n (b + 2)) (.n b) (.n (b + 1))),
      .atom (.mul (.n (b + 3)) (.n (b + 2)) (.n (tpPre h (jj - 1)))),
      .atom (.mul (.n (b + 4)) (.n (b + 3)) (.n (tpLo j))),
      .atom (.mul (.n (b + 5)) (.n (b + 4)) (.n (tpFu j))),
      .atom (.add (.n (b + 6)) (.n (tpTot h (jj - 1))) (.n (b + 5))),
      .atom (.add (.n (b + 7)) (.n (tpHi j)) (.n (tpLo j))),
      .atom (.mul (.n (b + 8)) (.n (b + 2)) (.n (b + 7))),
      .atom (.add (.n (b + 9)) (.n (tpLo j)) (.n (b + 8))),
      .atom (.mul (.n (b + 10)) (.n (tpPre h (jj - 1))) (.n (b + 9)))]

/-- The end's first value. -/
def tpE0 (h : ℕ) : ℕ := tpTopV h + 11 * h

/-- The expansion of `table_point__L{h}`, `h ≥ 1`. -/
def tpBody (h : ℕ) : List Stmt :=
  [.atom (.const (.n 4) (word 1 0))] ++ ((List.range h).map tpFwd).flatten ++
    [.atom (.load (.n (tpTopV h)) (.n 3) h),
      .atom (.mul (.n (tpTopV h + 1)) (.n (tpTopV h)) (.n (tpFu h)))] ++
    ((List.range h).map (tpWalkBlk h)).flatten ++
    [.atom (.mul (.n (tpE0 h)) (.n 0) (.n (tpTot h (h - 1)))),
      .atom (.const (.n (tpE0 h + 1)) (word 1 0)), .atom (.const (.n (tpE0 h + 2)) (word 1 0)),
      .atom (.add (.n (tpE0 h + 3)) (.n (tpE0 h + 2)) (.n (tpTopV h))),
      .atom (.mul (.n (tpE0 h + 4)) (.n (tpE0 h + 3)) (.n (tpPd (h - 1)))),
      .atom (.add (.n (tpE0 h + 5)) (.n (tpE0 h + 1)) (.n (tpE0 h + 4))),
      .atom (.copy (.n (tpE0 h + 6)) (.n (tpFu h))),
      .ret [.n (tpE0 h), .n (tpE0 h + 5), .n (tpE0 h + 6)]]

theorem tpFwd_noRet (k : ℕ) : Stmt.noRetList (tpFwd k) = true := by
  unfold tpFwd; split <;> rfl

theorem tpWalkBlk_noRet (h jj : ℕ) : Stmt.noRetList (tpWalkBlk h jj) = true := by
  unfold tpWalkBlk; split <;> rfl

/-! ## The forward pass -/

/-- What forward block `k` asks. -/
def TpFwdOk (rd : Reader) (σ : Val) (k : ℕ) : Prop :=
  LoadHolds rd (σ (.n 1)) k (σ (.n (tpT k))) ∧ LoadHolds rd (σ (.n 2)) k (σ (.n (tpX k))) ∧
    LoadHolds rd (σ (.n 3)) k (σ (.n (tpC k))) ∧
    σ (.n (tpLo k)) = σ (.n (tpT k)) * σ (.n (tpX k)) + (1 + σ (.n (tpT k)) + σ (.n (tpX k))) ∧
    σ (.n (tpHi k)) = σ (.n (tpT k)) * σ (.n (tpX k)) ∧
    σ (.n (tpFu (k + 1))) = σ (.n (tpFu k)) * (1 + σ (.n (tpT k)) + σ (.n (tpX k))) ∧
    σ (.n (tpPd k)) = σ (.n (tpC k)) * σ (.n (tpX k)) +
      (σ (.n (tpC k)) + σ (.n (tpX k))) * (if k = 0 then 1 else σ (.n (tpPd (k - 1))))

theorem holds_tpFwd {C : CallRel} {rd : Reader} {σ : Val} (k : ℕ) (kret : List E → Prop)
    (h4 : σ (.n 4) = 1) (h : Stmt.HoldsList C rd σ (tpFwd k) True kret) : TpFwdOk rd σ k := by
  unfold tpFwd at h
  split_ifs at h with hk
  · subst hk
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at h
    obtain ⟨l5, l6, h7, h8, h9, h10, h11, h12, h13, l14, h15, h16, h17⟩ := h
    refine ⟨l5, l6, l14, ?_, ?_, ?_, ?_⟩ <;>
      simp only [tpT, tpX, tpC, tpLo, tpHi, tpPd, tpFu, ↓reduceIte, Nat.zero_add,
        show (0 + 1 = 0) = False by decide]
    · rw [h11, h10, h9, h8, h7]
    · rw [h12, h7]
    · rw [h13, h10, h9, h8, h4, one_mul]
    · rw [show 14 * 0 + 17 = 17 from rfl, h17, h16, h15, mul_one]
  · have eT : tpT k = 14 * k + 4 := by simp [tpT, hk]
    have eX : tpX k = 14 * k + 4 + 1 := by simp [tpX, hk]
    have eC : tpC k = 14 * k + 4 + 9 := by simp [tpC, hk]
    have eLo : tpLo k = 14 * k + 4 + 6 := by simp [tpLo, hk]
    have eHi : tpHi k = 14 * k + 4 + 7 := by simp [tpHi, hk]
    have ePd : tpPd k = 14 * k + 4 + 13 := by simp [tpPd]
    have eFu : tpFu (k + 1) = 14 * k + 4 + 8 := by simp [tpFu, hk]; omega
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at h
    obtain ⟨l0, l1, h2, h3, h4', h5, h6, h7, h8, l9, h10, h11, h12, h13⟩ := h
    refine ⟨by rw [eT]; exact l0, by rw [eX]; exact l1, by rw [eC]; exact l9, ?_, ?_, ?_, ?_⟩
    · rw [eLo, eT, eX, h6, h2, h5, h4', h3]
    · rw [eHi, eT, eX, h7, h2]
    · rw [eFu, eT, eX, h8, h5, h4', h3]
    · rw [ePd, eC, eX, h13, h10, h12, h11]
      simp only [hk, ↓reduceIte]

/-! ## The walk -/

/-- What the walk's block `jj` asks, on coordinate `j = h - 1 - jj`. -/
def TpWalkOk (rd : Reader) (σ : Val) (h jj : ℕ) : Prop :=
  let j := h - 1 - jj
  ∃ c : E, LoadHolds rd (σ (.n 3)) j c ∧
    (σ (.n (tpTot h jj)), σ (.n (tpPre h jj))) =
      tpStep (fun _ ↦ σ (.n (tpLo j))) (fun _ ↦ σ (.n (tpHi j))) (fun _ ↦ σ (.n (tpFu j)))
        (fun _ ↦ 1 + c)
        (if jj = 0 then (σ (.n (tpTopV h + 1)), 1) else (σ (.n (tpTot h (jj - 1))), σ (.n (tpPre h (jj - 1))))) j

theorem holds_tpWalkBlk {C : CallRel} {rd : Reader} {σ : Val} (h jj : ℕ) (kret : List E → Prop)
    (hw : Stmt.HoldsList C rd σ (tpWalkBlk h jj) True kret) : TpWalkOk rd σ h jj := by
  unfold tpWalkBlk at hw
  split_ifs at hw with hk
  · subst hk
    have eT : tpTot h 0 = tpWB h 0 + 5 := by simp [tpTot, tpWB]
    have eP : tpPre h 0 = tpWB h 0 + 8 := by simp [tpPre, tpWB]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at hw
    obtain ⟨h0, l1, h2, h3, h4, h5, h6, h7, h8⟩ := hw
    refine ⟨_, l1, ?_⟩
    rw [eT, eP]
    simp only [↓reduceIte, tpStep, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [h5, h4, h3, h2, h0]; ring
    · rw [h8, h7, h6, h2, h0]; ring
  · have eT : tpTot h jj = tpWB h jj + 6 := by simp [tpTot, tpWB, hk]
    have eP : tpPre h jj = tpWB h jj + 10 := by simp [tpPre, tpWB, hk]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one] at hw
    obtain ⟨h0, l1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hw
    refine ⟨_, l1, ?_⟩
    rw [eT, eP]
    simp only [hk, ↓reduceIte, tpStep, Prod.mk.injEq]
    exact ⟨by rw [h6, h5, h4, h3, h2, h0], by rw [h10, h9, h8, h7, h2, h0]⟩

/-! ## The specification's side, unfolded -/

theorem range_reverse_eq (h : ℕ) : (List.range h).reverse = (List.range h).map fun i ↦ h - 1 - i := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_reverse, List.getElem_range, List.getElem_map, List.length_range]

theorem tpTotal_congr {low high full b low' high' full' b' : ℕ → E} {top : E} {h : ℕ}
    (hl : ∀ j < h, low j = low' j) (hh : ∀ j < h, high j = high' j) (hf : ∀ j ≤ h, full j = full' j)
    (hb : ∀ j < h, b j = b' j) : tpTotal low high full b top h = tpTotal low' high' full' b' top h := by
  unfold tpTotal
  rw [hf h le_rfl]
  exact congrArg Prod.fst (List.foldl_ext _ _ _ fun acc j hj ↦ by
    have hj' : j < h := List.mem_range.mp (List.mem_reverse.mp hj)
    simp only [tpStep, hl j hj', hh j hj', hf j hj'.le, hb j hj'])

/-- **The template's relation implies its meaning**, `h ≥ 1`. -/
theorem tp_sound (h : ℕ) (hh : 1 ≤ h) {f : Fn}
    (hfind : coreProgram.find? (tpNames.getD h "") = some f)
    (hparams : f.params = [.n 0, .n 1, .n 2, .n 3]) (hbody : f.body = tpBody h) (rd : Reader)
    (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD h "") args rets → MeaningTablePoint h rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams, tpBody]
  simp only [holdsList_append]
  rintro ⟨σ, rfl, hw⟩
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one] at hw
  obtain ⟨h4, hw⟩ := hw
  rw [holdsList_range_flatten h tpFwd tpFwd_noRet] at hw
  obtain ⟨hfwd, ltop, htop1, hw⟩ := hw
  rw [holdsList_range_flatten h (tpWalkBlk h) (tpWalkBlk_noRet h)] at hw
  obtain ⟨hwalk, hw⟩ := hw
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, hret⟩ := hw
  simp only [List.map_cons, List.map_nil] at hret
  have hf := fun k (hk : k < h) ↦ holds_tpFwd (C := coreProgram.Rel rd) k _ h4 (hfwd k hk)
  have hk := fun jj (hj : jj < h) ↦ holds_tpWalkBlk (C := coreProgram.Rel rd) h jj _ (hwalk jj hj)
  let ts : List E := (List.range h).map fun k ↦ σ (.n (tpT k))
  let xs : List E := (List.range h).map fun k ↦ σ (.n (tpX k))
  let cs : List E := (List.range h).map fun k ↦ σ (.n (tpC k))
  have gts : ∀ k < h, ts.getD k 0 = σ (.n (tpT k)) := fun k hk ↦ by simp [ts, hk]
  have gxs : ∀ k < h, xs.getD k 0 = σ (.n (tpX k)) := fun k hk ↦ by simp [xs, hk]
  have gcs : ∀ k < h, cs.getD k 0 = σ (.n (tpC k)) := fun k hk ↦ by simp [cs, hk]
  -- the forward pass
  have hfu : ∀ j ≤ h, σ (.n (tpFu j)) = tpFullAt ts xs j := by
    intro j hj
    induction j with
    | zero => show σ (.n 4) = _; rw [h4]; rfl
    | succ j ih =>
      rw [(hf j (by omega)).2.2.2.2.2.1, ih (by omega), tpFullAt, tpFullAt, List.range_succ,
        List.map_append, prodE_append]
      simp only [List.map_cons, List.map_nil, prodE_cons, prodE_nil, mul_one, gts j (by omega),
        gxs j (by omega)]
  have hpd : ∀ k < h, σ (.n (tpPd k)) =
      tpPad ((List.range (k + 1)).map fun i ↦ cs.getD i 0) ((List.range (k + 1)).map fun i ↦ xs.getD i 0) := by
    intro k hk
    induction k with
    | zero =>
      rw [(hf 0 hk).2.2.2.2.2.2, ← gcs 0 hk, ← gxs 0 hk]
      simp [tpPad]
    | succ k ih =>
      rw [(hf (k + 1) hk).2.2.2.2.2.2]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih (by omega), tpPad, tpPad,
        show List.range (k + 1 + 1) = List.range (k + 1) ++ [k + 1] from List.range_succ,
        List.map_append, List.map_append, List.zip_append (by simp), List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right,
        List.foldl_cons, List.foldl_nil, gcs (k + 1) hk, gxs (k + 1) hk]
  -- the walk
  let low : ℕ → E := tpLow ts xs
  let high : ℕ → E := tpHigh ts xs
  let full : ℕ → E := tpFullAt ts xs
  let bb : ℕ → E := fun j ↦ 1 + cs.getD j 0
  have hwk : ∀ jj < h, (σ (.n (tpTot h jj)), σ (.n (tpPre h jj))) =
      ((List.range (jj + 1)).map fun i ↦ h - 1 - i).foldl (tpStep low high full bb)
        (σ (.n (tpTopV h)) * full h, 1) := by
    intro jj hj
    have hstep : ∀ jj < h, ∀ acc : E × E, ∃ c, LoadHolds rd (σ (.n 3)) (h - 1 - jj) c ∧
        tpStep (fun _ ↦ σ (.n (tpLo (h - 1 - jj)))) (fun _ ↦ σ (.n (tpHi (h - 1 - jj))))
          (fun _ ↦ σ (.n (tpFu (h - 1 - jj)))) (fun _ ↦ 1 + c) acc (h - 1 - jj) =
        tpStep low high full bb acc (h - 1 - jj) := by
      intro jj hj acc
      obtain ⟨c, lc, -⟩ := hk jj hj
      refine ⟨c, lc, ?_⟩
      have j_lt : h - 1 - jj < h := by omega
      have ec : c = cs.getD (h - 1 - jj) 0 := by
        rw [gcs _ j_lt]; exact loadHolds_unique lc (hf _ j_lt).2.2.1
      simp only [tpStep, low, high, full, bb, tpLow, tpHigh, ← ec, (hf _ j_lt).2.2.2.1,
        (hf _ j_lt).2.2.2.2.1, hfu _ j_lt.le, gts _ j_lt, gxs _ j_lt]
    induction jj with
    | zero =>
      obtain ⟨c, lc, e⟩ := hk 0 hj
      obtain ⟨c', lc', e'⟩ := hstep 0 hj (σ (.n (tpTopV h + 1)), 1)
      have : c = c' := loadHolds_unique lc lc'
      subst this
      simp only [↓reduceIte] at e
      rw [e, e', htop1, hfu h le_rfl]
      rfl
    | succ jj ih =>
      obtain ⟨c, lc, e⟩ := hk (jj + 1) hj
      obtain ⟨c', lc', e'⟩ := hstep (jj + 1) hj (σ (.n (tpTot h jj)), σ (.n (tpPre h jj)))
      have : c = c' := loadHolds_unique lc lc'
      subst this
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at e
      rw [e, e', List.range_succ (n := jj + 1), List.map_append, List.foldl_append,
        ← ih (by omega)]
      rfl
  have hwf := hwk (h - 1) (by omega)
  rw [Nat.sub_add_cancel hh, ← range_reverse_eq] at hwf
  refine ⟨ts, xs, cs, σ (.n (tpTopV h)), by simp [ts], by simp [xs], by simp [cs],
    readsAt_range_map fun k hk ↦ (hf k hk).1, readsAt_range_map fun k hk ↦ (hf k hk).2.1,
    readsAt_range_map fun k hk ↦ (hf k hk).2.2.1, ltop, ?_⟩
  rw [← hret, e0, e5, e1, e4, e3, e2, e6, hfu h le_rfl, hpd (h - 1) (by omega),
    Nat.sub_add_cancel hh]
  have hcs : (List.range h).map (fun i ↦ cs.getD i 0) = cs := by
    apply List.ext_getElem (by simp [cs]); intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, gcs i h1]; simp [cs]
  have hxs : (List.range h).map (fun i ↦ xs.getD i 0) = xs := by
    apply List.ext_getElem (by simp [xs]); intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, gxs i h1]; simp [xs]
  rw [hcs, hxs, tpTotalG, tpTotal, ← hwf]

/-- `h = 0`: no coordinate. -/
theorem table_point_L0_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 0 "") args rets → MeaningTablePoint 0 rd args rets := by
  rw [rel_iff_sem (coreProgram_find?_at (j := idx% «table_point__L0») rfl),
    show Fn.body (fn% «table_point__L0») =
      [.atom (.const (.n 4) (word 1 0)), .atom (.load (.n 5) (.n 3) 0), .atom (.mul (.n 6) (.n 5) (.n 4)),
        .atom (.mul (.n 7) (.n 0) (.n 6)), .atom (.const (.n 8) (word 1 0)),
        .atom (.const (.n 9) (word 1 0)), .atom (.add (.n 10) (.n 9) (.n 5)),
        .atom (.add (.n 11) (.n 8) (.n 10)), .atom (.copy (.n 12) (.n 4)),
        .ret [.n 7, .n 11, .n 12]] from stmtsEqb_sound (by decide +kernel),
    show Fn.params (fn% «table_point__L0») = [.n 0, .n 1, .n 2, .n 3] from rfl]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one, List.map_cons, List.map_nil]
  rintro ⟨σ, rfl, h4, l5, h6, h7, h8, h9, h10, h11, h12, hret⟩
  refine ⟨[], [], [], σ (.n 5), rfl, rfl, rfl, readsAt_nil _ _, readsAt_nil _ _, readsAt_nil _ _, l5, ?_⟩
  rw [← hret, h7, h6, h11, h10, h9, h8, h12, h4]
  simp [tpTotalG, tpTotal, tpPad, tpFullAt, prodE]

/-! ## The Statement's forms -/

theorem zipWith_eq_range {α : Type} (f : E → E → α) (ts xs : List E) (h : ℕ) (hts : ts.length = h)
    (hxs : xs.length = h) : List.zipWith f ts xs = (List.range h).map fun i ↦ f (ts.getD i 0) (xs.getD i 0) := by
  apply List.ext_getElem (by simp [hts, hxs])
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < ts.length by omega),
    List.getElem?_eq_getElem (show i < xs.length by omega)]

/-- **`table_point`'s returns are the Statement's forms**, from the complement bits of `rows ≤ 2^h`
below `h` and its bit `h`: `omegaAt`, `lessThan`, `eqEval`. -/
theorem tablePoint_forms (theta : E) (ts xs : List E) (rows h : ℕ) (hts : ts.length = h)
    (hxs : xs.length = h) (hr : rows ≤ 2 ^ h) :
    theta * tpTotalG ts xs (cbitsE rows h) (bitE rows h) h = omegaAt theta ts xs rows ∧
      1 + (1 + bitE rows h) * tpPad (cbitsE rows h) xs = lessThan xs rows ∧
      tpFullAt ts xs h = eqEval ts xs := by
  refine ⟨?_, ?_, ?_⟩
  · let low : List E := List.zipWith (fun t x ↦ (1 + t) * (1 + x)) ts xs
    let high : List E := List.zipWith (fun t x ↦ t * x) ts xs
    have hl : low.length = h := by simp [low, hts, hxs]
    have hlow : ∀ j < h, low.getD j 0 = (1 + ts.getD j 0) * (1 + xs.getD j 0) := fun j hj ↦ by
      simp only [low, zipWith_eq_range _ ts xs h hts hxs]; simp [hj]
    have hhigh : ∀ j < h, high.getD j 0 = ts.getD j 0 * xs.getD j 0 := fun j hj ↦ by
      simp only [high, zipWith_eq_range _ ts xs h hts hxs]; simp [hj]
    rw [omegaAt, prefixSum_eq_tp low high rows (by rw [hl]; exact hr), hl, tpTotalG]
    refine congrArg (theta * ·) ?_
    refine tpTotal_congr (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun j hj ↦ ?_)
    · rw [hlow j hj, tpLow]; ring
    · rw [hhigh j hj, tpHigh]
    · rw [tpFullAt]
      refine congrArg prodE (List.map_congr_left fun i hi ↦ ?_)
      have hi' : i < h := by have := List.mem_range.mp hi; omega
      rw [hlow i hi', hhigh i hi']
      linear_combination (-(ts.getD i 0 * xs.getD i 0)) * two_eq_zero_E
    · rw [show cbitsE rows h = (List.range h).map (cbitE rows) from rfl]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
        Option.map_some, Option.getD_some, cbitE]
      linear_combination two_eq_zero_E
  · rw [lessThan_eq_tp, hxs]
  · rw [tpFullAt, eqEval, ← zipWith_eq_range (fun t x ↦ 1 + t + x) ts xs h hts hxs]
    rfl

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem table_point_L1_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 1 "") args rets → MeaningTablePoint 1 rd args rets :=
  tp_sound 1 (by omega) (f := fn% «table_point__L1»)
    (coreProgram_find?_at (j := idx% «table_point__L1») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L2_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 2 "") args rets → MeaningTablePoint 2 rd args rets :=
  tp_sound 2 (by omega) (f := fn% «table_point__L2»)
    (coreProgram_find?_at (j := idx% «table_point__L2») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L3_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 3 "") args rets → MeaningTablePoint 3 rd args rets :=
  tp_sound 3 (by omega) (f := fn% «table_point__L3»)
    (coreProgram_find?_at (j := idx% «table_point__L3») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L4_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 4 "") args rets → MeaningTablePoint 4 rd args rets :=
  tp_sound 4 (by omega) (f := fn% «table_point__L4»)
    (coreProgram_find?_at (j := idx% «table_point__L4») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L5_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 5 "") args rets → MeaningTablePoint 5 rd args rets :=
  tp_sound 5 (by omega) (f := fn% «table_point__L5»)
    (coreProgram_find?_at (j := idx% «table_point__L5») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L6_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 6 "") args rets → MeaningTablePoint 6 rd args rets :=
  tp_sound 6 (by omega) (f := fn% «table_point__L6»)
    (coreProgram_find?_at (j := idx% «table_point__L6») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L7_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 7 "") args rets → MeaningTablePoint 7 rd args rets :=
  tp_sound 7 (by omega) (f := fn% «table_point__L7»)
    (coreProgram_find?_at (j := idx% «table_point__L7») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L8_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 8 "") args rets → MeaningTablePoint 8 rd args rets :=
  tp_sound 8 (by omega) (f := fn% «table_point__L8»)
    (coreProgram_find?_at (j := idx% «table_point__L8») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L9_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 9 "") args rets → MeaningTablePoint 9 rd args rets :=
  tp_sound 9 (by omega) (f := fn% «table_point__L9»)
    (coreProgram_find?_at (j := idx% «table_point__L9») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L10_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 10 "") args rets → MeaningTablePoint 10 rd args rets :=
  tp_sound 10 (by omega) (f := fn% «table_point__L10»)
    (coreProgram_find?_at (j := idx% «table_point__L10») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L11_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 11 "") args rets → MeaningTablePoint 11 rd args rets :=
  tp_sound 11 (by omega) (f := fn% «table_point__L11»)
    (coreProgram_find?_at (j := idx% «table_point__L11») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L12_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 12 "") args rets → MeaningTablePoint 12 rd args rets :=
  tp_sound 12 (by omega) (f := fn% «table_point__L12»)
    (coreProgram_find?_at (j := idx% «table_point__L12») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L13_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 13 "") args rets → MeaningTablePoint 13 rd args rets :=
  tp_sound 13 (by omega) (f := fn% «table_point__L13»)
    (coreProgram_find?_at (j := idx% «table_point__L13») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L14_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 14 "") args rets → MeaningTablePoint 14 rd args rets :=
  tp_sound 14 (by omega) (f := fn% «table_point__L14»)
    (coreProgram_find?_at (j := idx% «table_point__L14») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L15_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 15 "") args rets → MeaningTablePoint 15 rd args rets :=
  tp_sound 15 (by omega) (f := fn% «table_point__L15»)
    (coreProgram_find?_at (j := idx% «table_point__L15») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L16_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 16 "") args rets → MeaningTablePoint 16 rd args rets :=
  tp_sound 16 (by omega) (f := fn% «table_point__L16»)
    (coreProgram_find?_at (j := idx% «table_point__L16») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L17_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 17 "") args rets → MeaningTablePoint 17 rd args rets :=
  tp_sound 17 (by omega) (f := fn% «table_point__L17»)
    (coreProgram_find?_at (j := idx% «table_point__L17») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L18_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 18 "") args rets → MeaningTablePoint 18 rd args rets :=
  tp_sound 18 (by omega) (f := fn% «table_point__L18»)
    (coreProgram_find?_at (j := idx% «table_point__L18») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L19_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 19 "") args rets → MeaningTablePoint 19 rd args rets :=
  tp_sound 19 (by omega) (f := fn% «table_point__L19»)
    (coreProgram_find?_at (j := idx% «table_point__L19») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L20_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 20 "") args rets → MeaningTablePoint 20 rd args rets :=
  tp_sound 20 (by omega) (f := fn% «table_point__L20»)
    (coreProgram_find?_at (j := idx% «table_point__L20») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L21_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 21 "") args rets → MeaningTablePoint 21 rd args rets :=
  tp_sound 21 (by omega) (f := fn% «table_point__L21»)
    (coreProgram_find?_at (j := idx% «table_point__L21») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L22_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 22 "") args rets → MeaningTablePoint 22 rd args rets :=
  tp_sound 22 (by omega) (f := fn% «table_point__L22»)
    (coreProgram_find?_at (j := idx% «table_point__L22») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L23_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 23 "") args rets → MeaningTablePoint 23 rd args rets :=
  tp_sound 23 (by omega) (f := fn% «table_point__L23»)
    (coreProgram_find?_at (j := idx% «table_point__L23») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem table_point_L24_sound (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (tpNames.getD 24 "") args rets → MeaningTablePoint 24 rd args rets :=
  tp_sound 24 (by omega) (f := fn% «table_point__L24»)
    (coreProgram_find?_at (j := idx% «table_point__L24») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

/-- **`table_point`'s core IR implies its meaning**, every specialization. -/
theorem table_point_sound : table_point_SoundP coreProgram := by
  intro h hh
  interval_cases h
  exacts [table_point_L0_sound, table_point_L1_sound, table_point_L2_sound, table_point_L3_sound, table_point_L4_sound, table_point_L5_sound, table_point_L6_sound, table_point_L7_sound, table_point_L8_sound, table_point_L9_sound, table_point_L10_sound, table_point_L11_sound, table_point_L12_sound, table_point_L13_sound, table_point_L14_sound, table_point_L15_sound, table_point_L16_sound, table_point_L17_sound, table_point_L18_sound, table_point_L19_sound, table_point_L20_sound, table_point_L21_sound, table_point_L22_sound, table_point_L23_sound, table_point_L24_sound]

end
end LeanVM.Guest.B1.Link
