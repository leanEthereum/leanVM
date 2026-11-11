/-
  LeanVM.Guest.B1.Whir.BrFin2

  The finish's residual sums and out-of-domain weights from the buffers' honest words.
-/

module

public import LeanVM.Guest.B1.Whir.BrFin1

/-!
# The residual sums and the out-of-domain weights

`ownerOf_eq`: in a buffer split at increasing offsets, a word in level `i`'s slots is level `i`'s.
`qpos_get`: the positions buffer holds each level's query positions. `fin_res`: level `i`'s
residual's memory (`ResMemP`) at the finish's honest data (the chain `rcC`, `μ = λ⁻¹`). `fin_ood`: the out-of-domain weights'
memory (`OodAllP`) at the soundness proof's choices.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Buffers split by levels -/

section Owner

variable {off span : ℕ → ℕ} {n e : ℕ}
  (h : ∀ i < n, off i + span i ≤ if i + 1 < n then off (i + 1) else e)
include h

theorem off_lt : ∀ (d i : ℕ), i + 1 + d < n → off i + span i ≤ off (i + 1 + d)
  | 0, i, hd => by have := h i (by omega); simp only [show i + 1 < n by omega, ↓reduceIte] at this; simpa using this
  | d + 1, i, hd => by
    have h1 := off_lt d i (by omega)
    have h2 := h (i + 1 + d) (by omega)
    simp only [show i + 1 + d + 1 < n by omega, ↓reduceIte] at h2
    rw [show i + 1 + (d + 1) = i + 1 + d + 1 by ring]
    omega

theorem off_end : ∀ (d i : ℕ), i + 1 + d = n → off i + span i ≤ e
  | 0, i, hd => by have := h i (by omega); simpa [show ¬ i + 1 < n by omega] using this
  | d + 1, i, hd => by
    have h1 := off_end d (i + 1) (by omega)
    have h2 := h i (by omega)
    simp only [show i + 1 < n by omega, ↓reduceIte] at h2
    omega

theorem ownerOf_eq {i k : ℕ} (h1 : off i ≤ k) (h2 : k < off i + span i) :
    ∀ d, i + 1 + d ≤ n → ownerOf off (i + 1 + d) k = i
  | 0, _ => by
    rw [Nat.add_zero, ownerOf]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [ownerOf]
    · simp [show 1 ≤ i by omega, h1]
  | d + 1, hd => by
    rw [show i + 1 + (d + 1) = (i + 1 + d) + 1 by ring, ownerOf]
    have := off_lt h d i (by omega)
    simp only [show ¬ off (i + 1 + d) ≤ k by omega, and_false, ↓reduceIte]
    exact ownerOf_eq h1 h2 d (by omega)

end Owner

variable {c : OsCfg} {tr : OsTr}

theorem ceilDiv_mul_ge {a b : ℕ} (hb : 1 ≤ b) : a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rw [show a + b - 1 = (a - 1) + b by omega, Nat.add_div_right _ (by omega), Nat.add_mul, one_mul]
    have := Nat.div_add_mod' (a - 1) b
    have := Nat.mod_lt (a - 1) (by omega : 0 < b)
    omega

theorem posAt_eq (h : TrFit c tr)
    {i : ℕ} (hi : i < c.levels.length) {j : ℕ} (hj : j < (lvAt c i).queries) :
    posAt c tr i j = Pof tr.rs i j := by
  have hb := h.lvb i hi
  have hfit := h.fit i hi
  have hD : (tr.L i).D = (lvAt c i).depth := by rw [SpLv.D, hfit.ml, hb.depth]
  have hq : (tr.L i).level.queries = (lvAt c i).queries := hb.queries
  rw [Pof, rs_get h hi]
  simp only [recOf, SpLv.qs, queriesOf, hD, hq]
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  rfl

/-- **The positions buffer holds each level's query positions.** -/
theorem qpos_get (h : TrFit c tr)
    (hs : OsSizes c) {rd : Reader} {P : OsPtrs} (hm : FixedMem rd P c tr) {i : ℕ}
    (hi : i < c.levels.length) {j : ℕ} (hj : j < (lvAt c i).queries) :
    LoadHolds rd P.qpos ((lvAt c i).posOff + j) (Pof tr.rs i j) := by
  have hb := h.lvb i hi
  have hper : 1 ≤ 192 / (lvAt c i).depth := hb.per
  have hspan : (lvAt c i).queries ≤ (lvAt c i).squeezes * (192 / (lvAt c i).depth) := by
    rw [hb.squeezes]; exact ceilDiv_mul_ge hper
  have hpos := hs.pos
  have hend := off_end (off := fun i ↦ (lvAt c i).posOff)
    (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hpos (c.levels.length - 1 - i) i
    (by omega)
  have hown : ownerOf (fun i ↦ (lvAt c i).posOff) c.levels.length ((lvAt c i).posOff + j) = i := by
    have := ownerOf_eq (off := fun i ↦ (lvAt c i).posOff)
      (span := fun i ↦ (lvAt c i).squeezes * (192 / (lvAt c i).depth)) hpos (i := i)
      (k := (lvAt c i).posOff + j) (by omega) (by
      show (lvAt c i).posOff + j < (lvAt c i).posOff + (lvAt c i).squeezes * (192 / (lvAt c i).depth)
      omega) (c.levels.length - 1 - i) (by omega)
    rwa [show i + 1 + (c.levels.length - 1 - i) = c.levels.length by omega] at this
  have := readsAt_map_range hm.qpos (k := (lvAt c i).posOff + j) (by
    show (lvAt c i).posOff + j < c.levels.length * ligPosCap
    have : (lvAt c i).posOff + (lvAt c i).squeezes * (192 / (lvAt c i).depth) ≤
      c.levels.length * ligPosCap := hend
    omega)
  simp only [hown, Nat.add_sub_cancel_left, show j < (lvAt c i).squeezes * (192 / (lvAt c i).depth) by
    omega, ↓reduceIte] at this
  rwa [posAt_eq h hi hj] at this

/-- **Level `i`'s residual's memory**, its dispatch's call given. -/
theorem fin_res {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr)
    {C : CallRel} {rd : Reader} {P : OsPtrs} {R : E} (hm : FixedMem rd P c tr)
    {BD LS ICH : E} (hLS : ReadsAt rd LS (lsC c tr))
    (hICH : ReadsAt rd ICH (ichC c tr)) {i : ℕ} (hi : i < c.levels.length)
    (hcall : DispC C rd R ((c.lvAt i).map osResidualName)
      [P.qpos * gen ^ (lvAt c i).posOff, BD * gen ^ (i * ligColsCap), finM tr i] [finH c tr i]) :
    ResMemP C rd P R BD ICH LS c i c.levels[i] (finM tr i) (finH c tr i) (finI c tr i)
      (finL c tr i) := by
  have hst := hF.lv i hi
  have hg : c.levels[i] = lvAt c i := (List.getD_eq_getElem _ _ hi).symm
  rw [hg]
  refine ⟨hst.posOff, hst.lc, ?_, hcall, ?_, ?_, ?_⟩
  · have := readsAt_map_range hm.mus hi
    rw [finM, rs_get h hi]
    simpa [recOf, OsTr.L] using this
  · exact readsAt_map_range hICH (k := i) (by omega)
  · exact readsAt_map_range hLS hi
  · exact readsAt_map_range hICH (k := i + 1) (by omega)

/-! ## The out-of-domain weights -/

/-- What one out-of-domain weight reads, its pointers named. -/
def OodInP (rd : Reader) (P : OsPtrs) (T : E) (c : OsCfg) (prevCols ol : ℕ) (lv : OsLv) (lam : E)
    (Z Y : ℕ → E) : Prop :=
  LoadHolds rd P.ood (ol * oodSlots) lam ∧
    ∀ t < prevCols - c.yrLog + c.yrLog,
      LoadHolds rd P.oodz (ol * ligColsCap + t) (Z t) ∧
      LoadHolds rd (oodPtr P T (prevCols - c.yrLog) t) (oodSrc 0 (prevCols - c.yrLog) lv t).2 (Y t)

theorem oodAllP_of {rd : Reader} {P : OsPtrs} {T : E} {Λ : ℕ → E} {Z Y : ℕ → ℕ → E} :
    ∀ (L : List OsLv) (prev ol : ℕ),
      (∀ i < L.length, OodInP rd P T c (if i = 0 then prev else (L.getD (i - 1) default).logCols)
        (ol + i) (L.getD i default) (Λ (ol + i)) (Z (ol + i)) (Y (ol + i))) →
      OodAllP rd P T c Λ Z Y prev ol L
  | [], _, _, _ => trivial
  | lv :: rest, prev, ol, h => by
    refine ⟨by simpa [OodInP] using h 0 (by simp), oodAllP_of rest lv.logCols (ol + 1) fun i hi ↦ ?_⟩
    have := h (i + 1) (by simp; omega)
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, List.getD_cons_succ,
      show ol + (i + 1) = ol + 1 + i by ring] at this
    rcases i with _ | i
    · simpa using this
    · simpa using this

/-- **The out-of-domain weights' memory.** -/
theorem fin_ood {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr)
    (hs : OsSizes c) {rd : Reader} {P : OsPtrs} (hm : FixedMem rd P c tr) {T : E}
    (hT : ReadsAt rd T (tailC tr.Lf tr.xsR)) :
    OodAllP rd P T c (Λof tr.rs) (Zof tr.rs) (Yof tr.rs tr.Fall tr.Tc)
      ((c.levels.headD default).logCols) 1 c.levels.tail := by
  have hn := hF.n2
  refine oodAllP_of _ _ _ fun i hi ↦ ?_
  have hi' : i + 1 < c.levels.length := by simp at hi; omega
  have hst := hF.lv i (by omega)
  have hnf : i ≠ c.yrLevel := by rw [hF.yr]; omega
  have hfit := h.fit i (by omega)
  have hfin : (tr.L i).fin = false := by
    cases e : (tr.L i).fin
    · rfl
    · exact absurd (hfit.fin.mp e) hnf
  have hprev : (if i = 0 then (c.levels.headD default).logCols
      else (c.levels.tail.getD (i - 1) default).logCols) = (lvAt c i).logCols := by
    rcases i with _ | i
    · simp only [↓reduceIte, List.headD_eq_head?_getD, List.head?_eq_getElem?, lvAt,
        List.getD_eq_getElem?_getD]
    · simp [List.getD_eq_getElem?_getD, lvAt]
  have htl : c.levels.tail.getD i default = lvAt c (i + 1) := by
    simp [List.getD_eq_getElem?_getD, lvAt]
  rw [hprev, htl, Nat.add_comm 1 i]
  have hcols : c.nFolds - ((lvAt c i).foldsOff + (lvAt c i).folds) + c.yrLog = (lvAt c i).logCols :=
    hst.cols
  have hpre : (lvAt c i).prefixLen + c.yrLog = (lvAt c i).logCols := hst.pre
  have hrfo : (lvAt c i).resFoldOff = (lvAt c i).foldsOff + (lvAt c i).folds := hst.rfo
  have hle : (lvAt c i).foldsOff + (lvAt c i).folds ≤ c.nFolds := hst.le
  have hnext : (lvAt c (i + 1)).foldsOff = (lvAt c i).foldsOff + (lvAt c i).folds := hF.next i hi'
  have hzf : (lvAt c i).logCols - c.yrLog = (lvAt c i).prefixLen := by omega
  have hc : (lvAt c i).logCols ≤ 26 := hs.cols i (by omega)
  refine ⟨?_, fun t ht ↦ ⟨?_, ?_⟩⟩
  · have := readsAt_map_range hm.ood (k := (i + 1) * oodSlots) (by simp only [oodSlots]; nlinarith)
    simp only [oodSlots] at this ⊢
    simp only [show (i + 1) * 4 / 4 = i + 1 by omega, show (i + 1) * 4 % 4 = 0 by omega,
      Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, List.getD_cons_zero] at this
    rw [Λof, Nat.add_sub_cancel, rs_get h (by omega)]
    exact this
  · have := readsAt_map_range hm.oodz (k := (i + 1) * ligColsCap + t) (by
      simp only [ligColsCap]; nlinarith)
    simp only [ligColsCap] at this ⊢
    simp only [show ((i + 1) * 26 + t) / 26 = i + 1 by omega, show ((i + 1) * 26 + t) % 26 = t by omega,
      Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel] at this
    rw [Zof, Nat.add_sub_cancel, rs_get h (by omega)]
    simpa [recOf, hfin] using this
  · rw [Yof, Nat.add_sub_cancel, xof_getD hF h (by omega) t, hzf]
    unfold oodPtr oodSrc
    split_ifs with h1
    · rw [hnext, ← hrfo]; exact fch_get hm (by omega)
    · exact tailC_get h hs hT (by omega)

end
end LeanVM.Guest.B1.Whir
