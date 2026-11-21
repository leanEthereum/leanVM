module

public import NativeVm.Code.Phase4.Step

/-!
# The tables' weights

`weightsC_spec`: `weightsC` writes `tableWeights heights eqp point` at `oWT`, from the tables'
log-heights at `layoutR` (words `4 ..`), the point at `oPT` (its size, the rounds' count, at `oNR`)
and the bus's GKR point `eqp` at `busR` (`busPointOff`).

The model folds over the point's coordinates, updating the six weights at each; the code computes
each table's weight in turn (`weightC_spec`), a product over the coordinates of `wtFac`
(`factorC_spec`); `tableWeights_get` is the model's weight `i` as that product (`wtPre`).
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {env : Env} {s : QState} {E : QState → Prop}

/-- Coordinate `c`'s factor of a table of log-height `h`, the point's entry `ch`. -/
def wtFac (eqp : Array EW) (h : Nat) (ch : EW) (c : Nat) : EW :=
  if c < h then 1 + eqp.getD c 0 + ch else ch

/-- A table's weight over the point's first `k` coordinates. -/
def wtPre (eqp point : Array EW) (h k : Nat) : EW :=
  ((point.toList.zipIdx).take k).foldl (fun acc p ↦ acc * wtFac eqp h p.1 p.2) 1

theorem wtPre_succ (eqp point : Array EW) (h : Nat) {k : Nat} (hk : k < point.size) :
    wtPre eqp point h (k + 1) = wtPre eqp point h k * wtFac eqp h point[k] k := by
  unfold wtPre
  rw [List.take_add_one, List.foldl_append]
  have : (point.toList.zipIdx)[k]? = some (point[k], k) := by
    rw [List.getElem?_zipIdx]; simp [hk]
  rw [this]
  rfl

theorem wtPre_zero (eqp point : Array EW) (h : Nat) : wtPre eqp point h 0 = 1 := rfl

theorem wt_foldl_weights (heights : Array Nat) (eqp : Array EW) (L : List (EW × Nat)) :
    ∀ (ws : Array EW), ws.size = heights.size →
      (L.foldl (fun weights (p : EW × Nat) ↦ Array.zipWith (fun weight height ↦
        weight * if p.2 < height then 1 + eqp.getD p.2 0 + p.1 else p.1) weights heights) ws).size
        = heights.size ∧
      ∀ i (h1 : i < (L.foldl (fun weights (p : EW × Nat) ↦ Array.zipWith (fun weight height ↦
        weight * if p.2 < height then 1 + eqp.getD p.2 0 + p.1 else p.1) weights heights) ws).size)
        (h2 : i < ws.size) (h3 : i < heights.size),
        (L.foldl (fun weights (p : EW × Nat) ↦ Array.zipWith (fun weight height ↦
          weight * if p.2 < height then 1 + eqp.getD p.2 0 + p.1 else p.1) weights heights) ws)[i]
          = L.foldl (fun acc p ↦ acc * wtFac eqp heights[i] p.1 p.2) ws[i] := by
  induction L with
  | nil => intro ws hs; exact ⟨hs, fun i _ _ _ ↦ rfl⟩
  | cons p L ih =>
    intro ws hs
    have hz : (Array.zipWith (fun weight height ↦
        weight * if p.2 < height then 1 + eqp.getD p.2 0 + p.1 else p.1) ws heights).size =
        heights.size := by simp [hs]
    obtain ⟨ih1, ih2⟩ := ih _ hz
    refine ⟨ih1, fun i h1 h2 h3 ↦ ?_⟩
    simp only [List.foldl_cons]
    refine (ih2 i h1 (by simp; omega) h3).trans ?_
    rw [Array.getElem_zipWith]
    rfl

theorem tableWeights_get (heights : Array Nat) (eqp point : Array EW) :
    (tableWeights heights eqp point).size = heights.size ∧
      ∀ i (h1 : i < (tableWeights heights eqp point).size) (h3 : i < heights.size),
        (tableWeights heights eqp point)[i] = wtPre eqp point heights[i] point.size := by
  have H := wt_foldl_weights heights eqp point.toList.zipIdx (heights.map fun _ ↦ 1) (by simp)
  have e : tableWeights heights eqp point = point.toList.zipIdx.foldl (fun weights (p : EW × Nat) ↦
      Array.zipWith (fun weight height ↦
        weight * if p.2 < height then 1 + eqp.getD p.2 0 + p.1 else p.1) weights heights)
      (heights.map fun _ ↦ 1) := by
    unfold tableWeights
    rw [← Array.foldl_toList, Array.toList_zipIdx]
  rw [e]
  refine ⟨H.1, fun i h1 h3 ↦ ?_⟩
  rw [H.2 i h1 (by simp; omega) h3]
  unfold wtPre
  rw [List.take_of_length_le (by simp)]
  simp

theorem tableWeights_size (heights : Array Nat) (eqp point : Array EW) :
    (tableWeights heights eqp point).size = heights.size :=
  (tableWeights_get heights eqp point).1

theorem wtFac_in (eqp : Array EW) {h c : Nat} (ch : EW) (hh : c < h) (he : c < eqp.size) :
    wtFac eqp h ch c = ⟨ch.c0 ^^^ 1 ^^^ eqp[c].c0, ch.c1 ^^^ eqp[c].c1⟩ := by
  unfold wtFac
  simp only [hh, ↓reduceIte]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem he, Option.getD_some]
  show EW.add (EW.add ⟨1, 0⟩ eqp[c]) ch = _
  simp only [EW.add, EW.mk.injEq, UInt64.zero_xor]
  constructor <;> ac_rfl

theorem wtFac_out (eqp : Array EW) {h c : Nat} (ch : EW) (hh : c < h) (he : ¬ c < eqp.size) :
    wtFac eqp h ch c = ⟨ch.c0 ^^^ 1, ch.c1⟩ := by
  unfold wtFac
  simp only [hh, ↓reduceIte]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
  show EW.add (EW.add ⟨1, 0⟩ ⟨0, 0⟩) ch = _
  simp only [EW.add, EW.mk.injEq, UInt64.zero_xor, UInt64.xor_zero]
  exact ⟨UInt64.xor_comm _ _, trivial⟩

theorem wtFac_ge (eqp : Array EW) {h c : Nat} (ch : EW) (hh : ¬ c < h) : wtFac eqp h ch c = ch := by
  unfold wtFac
  simp only [hh, ↓reduceIte]

theorem wt_shl4_add {w : UInt64} {j n : Nat} :
    n.toUInt64 <<< (4 : UInt64) + wd w j = wd w (j + 2 * n) := shl4_add

theorem factorC_spec {w : UInt64} {eqp : Array EW} {h c : Nat} {ch : EW}
    (hbp : s.reg .rbp = wd w 0) (h14 : s.reg .r14 = c.toUInt64) (h15 : s.reg .r15 = h.toUInt64)
    (hc : c < 64) (hh : h < 64) (hesz : eqp.size ≤ 63)
    (hp0 : s.mem (wd w (oPT + 2 * c)) = some ch.c0)
    (hp1 : s.mem (wd w (oPT + 2 * c + 1)) = some ch.c1)
    (hcnt : s.mem (wd w oBP) = some eqp.size.toUInt64)
    (he : ∀ j (hj : j < eqp.size), s.mem (wd w (oBP + 1 + 2 * j)) = some eqp[j].c0 ∧
      s.mem (wd w (oBP + 2 + 2 * j)) = some eqp[j].c1) :
    WP factorC s (fun s' ↦ regB s' = wtFac eqp h ch c ∧ s'.mem = s.mem ∧
      RegsFrame [.rax, .rcx, .r11, .r12] s s') E := by
  unfold factorC
  fstep [h14]
  fstep
  fstep [hbp]
  rw [wt_shl4_add]
  refine wp_ldA (w := w) (j := 0 + 2 * c) (k := oPT) (by rsimp) (by
    rsimp; rw [show 0 + 2 * c + oPT = oPT + 2 * c by omega]; exact hp0) ?_
  refine wp_ldA (w := w) (j := 0 + 2 * c) (k := oPT + 1) (by rsimp) (by
    rsimp; rw [show 0 + 2 * c + (oPT + 1) = oPT + 2 * c + 1 by omega]; exact hp1) ?_
  apply WP.blk_cons
  by_cases hlt : c < h
  · refine wp_ite_true (by
      rw [cond_ltu, rhs_reg]; rsimp; rw [h14, h15]
      exact decide_eq_true ((toUInt64_lt (by omega) (by omega)).mpr hlt)) ?_
    fstep
    refine wp_ldA (j := 0) (k := oBP) (by rsimp; exact hbp) (by rsimp; exact hcnt) ?_
    apply WP.blk_cons
    by_cases hin : c < eqp.size
    · refine wp_ite_true (by
        rw [cond_ltu, rhs_reg]; rsimp; rw [h14]
        exact decide_eq_true ((toUInt64_lt (by omega) (by omega)).mpr hin)) ?_
      fstep [h14]
      fstep
      fstep [hbp]
      rw [wt_shl4_add]
      refine wp_ldA (w := w) (j := 0 + 2 * c) (k := oBP + 1) (by rsimp) (by
        rsimp; rw [show 0 + 2 * c + (oBP + 1) = oBP + 1 + 2 * c by omega]; exact (he c hin).1) ?_
      fstep
      refine wp_ldA (w := w) (j := 0 + 2 * c) (k := oBP + 2) (by rsimp) (by
        rsimp; rw [show 0 + 2 * c + (oBP + 2) = oBP + 2 + 2 * c by omega]; exact (he c hin).2) ?_
      fstep
      apply WP.blk_nil; apply WP.blk_nil; apply WP.blk_nil
      refine ⟨?_, by rsimp, by rf_tac⟩
      rw [wtFac_in eqp ch hlt hin]
      unfold regB
      rsimp
    · refine wp_ite_false (by
        rw [cond_ltu, rhs_reg]; rsimp; rw [h14]
        exact decide_eq_false (mt (toUInt64_lt (by omega) (by omega)).mp hin)) ?_
      apply WP.skip; apply WP.blk_nil; apply WP.blk_nil
      refine ⟨?_, by rsimp, by rf_tac⟩
      rw [wtFac_out eqp ch hlt hin]
      unfold regB
      rsimp
  · refine wp_ite_false (by
      rw [cond_ltu, rhs_reg]; rsimp; rw [h14, h15]
      exact decide_eq_false (mt (toUInt64_lt (by omega) (by omega)).mp hlt)) ?_
    apply WP.skip; apply WP.blk_nil
    refine ⟨?_, by rsimp, by rf_tac⟩
    rw [wtFac_ge eqp ch hlt]
    unfold regB
    rsimp

/-- **Table `i`'s weight** at `oWT + 2 i`. -/
theorem weightC_spec {w : UInt64} {eqp point : Array EW} {i hgt : Nat}
    (hbp : s.reg .rbp = wd w 0) (h13 : s.reg .r13 = i.toUInt64)
    (hsi : s.reg .rsi = point.size.toUInt64) (hi : i < 6) (hpsz : point.size ≤ 30) (hh : hgt < 64)
    (hesz : eqp.size ≤ 63) (hhw : s.mem (wd w (oL + 4 + i)) = some hgt.toUInt64)
    (hpt : ∀ c (hc : c < point.size), s.mem (wd w (oPT + 2 * c)) = some point[c].c0 ∧
      s.mem (wd w (oPT + 2 * c + 1)) = some point[c].c1)
    (hcnt : s.mem (wd w oBP) = some eqp.size.toUInt64)
    (he : ∀ j (hj : j < eqp.size), s.mem (wd w (oBP + 1 + 2 * j)) = some eqp[j].c0 ∧
      s.mem (wd w (oBP + 2 + 2 * j)) = some eqp[j].c1)
    (hd0 : (s.mem (wd w (oWT + 2 * i))).isSome) (hd1 : (s.mem (wd w (oWT + 2 * i + 1))).isSome) :
    WP weightC s (fun s' ↦ s'.mem (wd w (oWT + 2 * i)) = some (wtPre eqp point hgt point.size).c0 ∧
      s'.mem (wd w (oWT + 2 * i + 1)) = some (wtPre eqp point hgt point.size).c1 ∧
      Wr w (fun k ↦ k = oWT + 2 * i ∨ k = oWT + 2 * i + 1) s s' ∧
      (∀ a, (s.mem a).isSome → (s'.mem a).isSome) ∧ s'.reg .r13 = (i + 1).toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s') E := by
  unfold weightC
  refine wp_load (eval_idx64 hbp h13 (oL + 4)) (v := hgt.toUInt64)
    (by rw [show 0 + i + (oL + 4) = oL + 4 + i by omega]; exact hhw) ?_
  fstep; fstep; fstep
  apply WP.blk_cons
  refine WP.loop (fun u ↦ ∃ k ≤ point.size, u.reg .r14 = k.toUInt64 ∧
      regA u = wtPre eqp point hgt k ∧ u.reg .r15 = hgt.toUInt64 ∧ u.mem = s.mem ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r14, .r15] s u)
    (fun u ↦ point.size - (u.reg .r14).toNat) ⟨0, by omega, by rsimp; rfl, by unfold regA; rsimp; rfl,
      by rsimp, by rsimp, by rfw⟩ ?_ ?_
  · rintro u ⟨k, hk, h14, hA, h15, hm, hf⟩ hc
    rw [cond_ltu, rhs_reg, h14, hf .rsi (by decide), hsi] at hc
    have hkn : k < point.size := (toUInt64_lt (by omega) (by omega)).mp (of_decide_eq_true hc)
    have hbp' : u.reg .rbp = wd w 0 := by rw [hf .rbp (by decide), hbp]
    refine wp_then (factorC_spec (w := w) (eqp := eqp) (h := hgt) (c := k) (ch := point[k]) hbp' h14
      h15 (by omega) hh hesz (by rw [hm]; exact (hpt k hkn).1) (by rw [hm]; exact (hpt k hkn).2)
      (by rw [hm]; exact hcnt) (fun j hj ↦ by rw [hm]; exact he j hj))
      fun u1 ⟨hB, hm1, hf1⟩ ↦ wp_then (emulW u1) fun u2 ⟨hA2, hm2, hf2⟩ ↦ ?_
    have hA1 : regA u1 = regA u := by
      simp only [regA, hf1 .r9 (by decide), hf1 .r10 (by decide)]
    have r14 : u2.reg .r14 = k.toUInt64 := by
      rw [hf2 .r14 (by decide), hf1 .r14 (by decide), h14]
    fstep [r14]
    fdone
    refine ⟨⟨k + 1, by omega, by rw [toUInt64_succ], ?_, ?_, ?_, ?_⟩, ?_⟩
    · unfold regA; rsimp
      rw [wtPre_succ eqp point hgt hkn, ← hB, ← hA, ← hA1, ← hA2]
    · rw [hf2 .r15 (by decide), hf1 .r15 (by decide), h15]
    · rw [hm2, hm1, hm]
    · refine rf_setReg ?_ (by decide) _
      exact rf_trans (l'' := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r14, .r15])
        (rf_trans (l'' := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .r14, .r15])
          hf hf1 (by decide) (by decide)) hf2 (by decide) (by decide)
    · rw [h14, toUInt64_succ, Transcript.toNat_toUInt64 (by omega), Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro u ⟨k, hk, h14, hA, h15, hm, hf⟩ hc
    rw [cond_ltu, rhs_reg, h14, hf .rsi (by decide), hsi] at hc
    have hkn : k = point.size := by
      have := mt (toUInt64_lt (by omega) (by omega)).mpr (of_decide_eq_false hc)
      omega
    subst hkn
    have hbp' : u.reg .rbp = wd w 0 := by rw [hf .rbp (by decide), hbp]
    have h13' : u.reg .r13 = i.toUInt64 := by rw [hf .r13 (by decide), h13]
    fstep [h13']
    fstep
    fstep [hbp']
    rw [wt_shl4_add]
    refine wp_stA (w := w) (j := 0 + 2 * i) (k := oWT) (by rsimp) (by
      rsimp; rw [hm, show 0 + 2 * i + oWT = oWT + 2 * i by omega]; exact hd0) ?_
    refine wp_stA (w := w) (j := 0 + 2 * i) (k := oWT + 1) (by rsimp) (by
      refine NativeVm.Code.P4.isSome_setMem _ _ _ ?_
      rsimp; rw [hm, show 0 + 2 * i + (oWT + 1) = oWT + 2 * i + 1 by omega]; exact hd1) ?_
    fstep
    fdone
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_setMem_ne _ (by omega) (by simp only [oWT, oS]; omega) (by simp only [oWT, oS]; omega),
        mem_setMem_eq _ (by omega)]
      exact congrArg (some ∘ EW.c0) hA
    · rw [mem_setMem_eq _ (by omega)]
      exact congrArg (some ∘ EW.c1) hA
    · wr_tac
      exact fun a _ ↦ by rw [hm]
    · intro a ha
      refine NativeVm.Code.P4.isSome_setMem _ _ _ (NativeVm.Code.P4.isSome_setMem _ _ _ ?_)
      rsimp; rw [hm]; exact ha
    · rw [h13', toUInt64_succ]
    · repeat (first
        | with_reducible refine rf_setMem ?_ _ _
        | with_reducible refine rf_setReg ?_ (by decide) _)
      exact rf_mono hf (by decide)

theorem wt_foldl_max_le (l : List Nat) (a b : Nat) (ha : a ≤ b) (hl : ∀ x ∈ l, x ≤ b) :
    l.foldl max a ≤ b := by
  induction l generalizing a with
  | nil => exact ha
  | cons x l ih =>
    exact ih _ (Nat.max_le.mpr ⟨ha, hl x List.mem_cons_self⟩) fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)

theorem wt_getD_eq {α : Type} (xs : Array α) (d : α) {i : Nat} (h : i < xs.size) :
    xs.getD i d = xs[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]

/-- **The tables' weights** at `oWT`. -/
theorem weightsC_spec (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) (hws : WS env s)
    (heights : Array Nat) (hh : heights.size = 6)
    (hhw : ∀ i < 6, s.mem (wd env.work (oL + 4 + i)) = some (heights.getD i 0).toUInt64)
    (hhb : ∀ i < 6, heights.getD i 0 ≤ 30)
    (point : Array EW) (hpsz : point.size = heights.foldl max 0)
    (hnr : s.mem (wd env.work oNR) = some point.size.toUInt64)
    (hpt : EWArr s.mem (wd env.work oPT) point)
    (eqp : Array EW) (heq : EVec s.mem (wd env.work oBP) busPointCap eqp) :
    WP weightsC s (fun s' ↦ EWArr s'.mem (wd env.work oWT) (tableWeights heights eqp point) ∧
      Wr env.work (fun k ↦ oWT ≤ k ∧ k < oWT + 12) s s' ∧ RegsFrame arrRegs s s') E := by
  have hps : point.size ≤ 30 := by
    rw [hpsz, ← Array.foldl_toList]
    refine wt_foldl_max_le _ 0 30 (by omega) fun x hx ↦ ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have := hhb i (by simp at hi; omega)
    rwa [wt_getD_eq _ _ (by simp at hi; omega)] at this
  have hesz : eqp.size ≤ 63 := heq.1
  obtain ⟨-, hcnt⟩ := heq.2.1
  have he : ∀ j (hj : j < eqp.size), s.mem (wd env.work (oBP + 1 + 2 * j)) = some eqp[j].c0 ∧
      s.mem (wd env.work (oBP + 2 + 2 * j)) = some eqp[j].c1 := fun j hj ↦ by
    have := heq.2.2 j hj
    unfold EWAt at this
    simp only [wd_wd] at this
    refine ⟨this.1, ?_⟩
    rw [show oBP + 2 + 2 * j = oBP + 1 + 2 * j + 1 by omega]
    exact this.2
  have hp : ∀ c (hc : c < point.size), s.mem (wd env.work (oPT + 2 * c)) = some point[c].c0 ∧
      s.mem (wd env.work (oPT + 2 * c + 1)) = some point[c].c1 := fun c hc ↦ by
    have := hpt c hc
    unfold EWAt at this
    simp only [wd_wd] at this
    exact this
  have hT := tableWeights_get heights eqp point
  unfold weightsC
  wst
  refine wp_ldA (w := env.work) (j := 0) (k := oNR) (by rsimp) (by rw [Nat.zero_add]; rsimp; exact hnr) ?_
  fstep
  apply WP.blk_cons
  refine WP.loop (fun u ↦ ∃ i ≤ 6, u.reg .r13 = i.toUInt64 ∧ u.reg .rbp = wd env.work 0 ∧
      u.reg .rsi = point.size.toUInt64 ∧ Wr env.work (fun k ↦ oWT ≤ k ∧ k < oWT + 12) s u ∧
      (∀ a, (s.mem a).isSome → (u.mem a).isSome) ∧
      (∀ j (hj : j < i) (hj6 : j < heights.size),
        u.mem (wd env.work (oWT + 2 * j)) = some (wtPre eqp point heights[j] point.size).c0 ∧
        u.mem (wd env.work (oWT + 2 * j + 1)) = some (wtPre eqp point heights[j] point.size).c1) ∧
      RegsFrame arrRegs s u)
    (fun u ↦ 6 - (u.reg .r13).toNat) ⟨0, by omega, by rsimp; rfl, by rsimp, by rsimp,
      by wr_tac, fun a ha ↦ by rsimp; exact ha, fun j hj ↦ absurd hj (by omega), by rfw⟩ ?_ ?_
  · rintro u ⟨i, hi, h13, hbp, hsi, hW, hiso, hval, hf⟩ hc
    rw [cond_ltu, rhs_imm, h13, show ((6 : Int64).toUInt64) = (6 : Nat).toUInt64 from rfl] at hc
    have hi6 : i < 6 := (toUInt64_lt (by omega) (by omega)).mp (of_decide_eq_true hc)
    have hmem : ∀ j < oWT, u.mem (wd env.work j) = s.mem (wd env.work j) := fun j hj ↦
      hW.word (by simp only [oWT, oS] at hj ⊢; omega) fun k hk ↦ by
        simp only [oWT, oS] at hk hj ⊢; omega
    have hih : i < heights.size := by omega
    have hhw' := hhw i hi6
    have hhb' := hhb i hi6
    rw [wt_getD_eq _ _ hih] at hhw' hhb'
    refine WP.mono (weightC_spec (w := env.work) (eqp := eqp) (point := point) (i := i)
      (hgt := heights[i]) hbp h13 hsi hi6 hps (by omega) hesz
      (by rw [hmem _ (by simp only [oL, oWT, oS]; omega)]; exact hhw')
      (fun c hc ↦ by
        rw [hmem _ (by simp only [oPT, oWT, oS]; omega), hmem _ (by simp only [oPT, oWT, oS]; omega)]
        exact hp c hc)
      (by rw [hmem _ (by simp only [oBP, oB, oWT, oS]; omega)]; exact hcnt)
      (fun j hj ↦ by
        rw [hmem _ (by simp only [oBP, oB, oWT, oS]; omega),
          hmem _ (by simp only [oBP, oB, oWT, oS]; omega)]
        exact he j hj)
      (hiso _ (hws _ (by simp only [oWT, oS]; omega) (by simp only [oWT, oS]; omega)))
      (hiso _ (hws _ (by simp only [oWT, oS]; omega) (by simp only [oWT, oS]; omega))))
      ?_ fun _ h ↦ h
    rintro u1 ⟨hv0, hv1, hW1, hiso1, h13', hf1⟩
    refine ⟨⟨i + 1, by omega, h13', by rw [hf1 .rbp (by decide), hbp],
      by rw [hf1 .rsi (by decide), hsi], hW.trans (hW1.mono fun k hk ↦ by
        simp only [oWT, oS] at hk ⊢; omega), fun a ha ↦ hiso1 a (hiso a ha), fun j hj hj6 ↦ ?_,
      rf_trans (l'' := arrRegs) hf hf1 (by decide) (by decide)⟩, ?_⟩
    · rcases Nat.lt_or_ge j i with hji | hji
      · rw [hW1.word (by simp only [oWT, oS]; omega) fun k hk ↦ by
            simp only [oWT, oS] at hk ⊢; omega,
          hW1.word (by simp only [oWT, oS]; omega) fun k hk ↦ by
            simp only [oWT, oS] at hk ⊢; omega]
        exact hval j hji hj6
      · obtain rfl : j = i := by omega
        exact ⟨hv0, hv1⟩
    · rw [h13, h13', Transcript.toNat_toUInt64 (by omega), Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro u ⟨i, hi, h13, hbp, hsi, hW, hiso, hval, hf⟩ hc
    rw [cond_ltu, rhs_imm, h13, show ((6 : Int64).toUInt64) = (6 : Nat).toUInt64 from rfl] at hc
    have hi6 : i = 6 := by
      have := mt (toUInt64_lt (by omega) (by omega)).mpr (of_decide_eq_false hc)
      omega
    subst hi6
    apply WP.blk_nil
    refine ⟨fun j hj ↦ ?_, hW, hf⟩
    have hj6 : j < heights.size := by rw [← hT.1]; exact hj
    rw [hT.2 j hj hj6]
    unfold EWAt
    rw [wd_wd, wd_wd]
    exact hval j (by omega) hj6

end NativeVm.Code.P4
