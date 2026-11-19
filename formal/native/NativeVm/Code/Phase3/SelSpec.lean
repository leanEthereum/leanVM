module

public import NativeVm.Code.Phase3.SelLoops
public import NativeVm.Code.Phase3.LayoutSide

/-!
# Phase 3's selectors and padding weights: the contract

`sel_spec`: at the GKR point, a side's framework selectors into `fselR side`, its table blocks'
selectors into `tselR side` and their padding weights into `padWR side`, from the side's placements
(`SidesAt`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript

/-- A table placement's variable count is its block's log-rows. -/
theorem tables_vc (layout : LayoutW) (side : Nat) :
    ∀ k (h : k < (sideLayout layout side).tables.size) (h' : k < (sideBlocks layout side).size),
      (sideLayout layout side).tables[k].variableCount = (sideBlocks layout side)[k].logRows := by
  intro k h h'
  have hg := busLayout_get (sideFr layout side) (sideBlocks layout side)
  have hf := (busLayout_all (sideFr layout side) (sideBlocks layout side)).1
  rw [← sideLayout_eq] at hg hf
  have := hg ((sideLayout layout side).framework.size + k) (by rw [Array.size_append]; omega)
  rw [Array.getElem_append_right (by omega)] at this
  simp only [Nat.add_sub_cancel_left] at this
  rw [this, hf, sizes_blk h']

theorem fselR_off (side : Nat) : (fselR side).off = 52670 + 716 + 512 * side := by
  simp [fselR, sreg, scratchR_off]; omega

theorem tselR_off (side : Nat) : (tselR side).off = 52670 + 512 + 512 * side := by
  simp [tselR, sreg, scratchR_off]; omega

theorem padWR_off (side : Nat) : (padWR side).off = 52670 + 614 + 512 * side := by
  simp [padWR, sreg, scratchR_off]; omega

theorem lay_depthR_off : depthR.off = 52670 + 209 := by simp [depthR, sreg, scratchR_off]

theorem lay_pointR_off : pointR.off = 52670 + 34 := by simp [pointR, sreg, scratchR_off]

theorem sideFw_eq (side : Nat) : sideFw side = (if side = 2 then 0 else 3) := rfl

/-- **A side's selectors and padding weights** at the GKR point. -/
theorem sel_spec {env : Env} {inp : Input} {s : QState} {layout : LayoutW} {rate side : Nat}
    {point : Array EW} (hside : side < 3) (hrdi : s.reg .rdi = env.ctx)
    (hwp : s.mem (wd env.ctx ctxWork) = some env.work) (hi : Inputs env inp s.mem)
    (hl : LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate)
    (hsa : SidesAt s.mem env.work layout) (hdw : NatAt s.mem (depthR.at env.work) point.size)
    (hps : point.size < 64) (hp : EWArr s.mem (pointR.at env.work) point) :
    WP (selCode side) s (fun s' ↦
        EWArr s'.mem ((tselR side).at env.work)
          ((sideLayout layout side).tables.map (eqAbove · point)) ∧
        EWArr s'.mem ((padWR side).at env.work) (padWeights (sideBlocks layout side) point) ∧
        EWArr s'.mem ((fselR side).at env.work)
          ((sideLayout layout side).framework.map (eqAbove · point)) ∧
        Wrote env [tselR side, padWR side, fselR side, tmpR] s s') (fun _ ↦ False) := by
  obtain ⟨rows, -, -, hbb⟩ := hl.rows
  obtain ⟨hP64, hB128, hPw, hRw⟩ := hsa side hside
  set L := sideLayout layout side with hL
  set B := sideBlocks layout side with hBd
  obtain ⟨hTs, hFs⟩ := sideLayout_sizes layout side
  rw [← sideFw_eq] at hFs
  have hBs : B.size = sideNb side := sideBlocks_size hbb hside
  have hFs' : L.framework.size = sideFw side := hFs
  have hTs' : L.tables.size = sideNb side := hTs.trans hBs
  have hnb := sideNb_le side
  have hfw := sideFw_le side
  have hpo := placeR_off side
  have hfo := fselR_off side
  have hto := tselR_off side
  have hwo := padWR_off side
  have hdo := lay_depthR_off
  have hpto := lay_pointR_off
  set po := (placeR side).off
  set fo := (fselR side).off
  set tso := (tselR side).off
  set wo := (padWR side).off
  have hpt : PointAt s.mem env.work point := fun t ht ↦ by
    have := hp t ht
    unfold EWAt at this
    simp only [Region.at, wd_wd] at this
    exact this
  have hn : s.mem (wd env.work depthR.off) = some point.size.toUInt64 := hdw.2
  unfold selCode
  refine wp_load (eval_cw hrdi ctxWork) hwp ?_
  -- the framework selectors
  have hplF : ∀ j (h : j < L.framework.size),
      (s.setReg .r15 env.work).mem (wd env.work (po + 2 * j)) =
        some L.framework[j].variableCount.toUInt64 ∧
      (s.setReg .r15 env.work).mem (wd env.work (po + 2 * j + 1)) =
        some L.framework[j].index.toUInt64 ∧
      L.framework[j].variableCount < 2 ^ 64 ∧ L.framework[j].index < 2 ^ 64 := fun j h ↦ by
    have hj : j < (L.framework ++ L.tables).size := by rw [Array.size_append]; omega
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hPw j hj
    rw [Array.getElem_append_left h] at a1 a2 b1 b2
    rw [Region.at, wd_wd] at a2 b2
    exact ⟨a2, b2, a1, b1⟩
  refine wp_then (selFw_spec (p := env.work) (po := po) (fo := fo) (fw := sideFw side) (point := point)
    hFs (by omega) (by omega) (by rsimp) hplF hn hps hpt (by omega)
    (fun w hw ↦ hi.ok3_some (r := fselR side) (ok3_sreg (by omega)) (by simp [fselR, sreg]; omega)))
    fun s₁ ⟨a, ak, ad, ao, af⟩ ↦ ?_
  have k1 : ∀ w < 2 ^ 61, (w < fo ∨ fo + 2 * sideFw side ≤ w) →
      s₁.mem (wd env.work w) = s.mem (wd env.work w) := fun w hw ho ↦ ak w hw ho
  have hplT : ∀ k (h : k < L.tables.size),
      s₁.mem (wd env.work (po + 2 * sideFw side + 2 * k)) = some L.tables[k].variableCount.toUInt64 ∧
      s₁.mem (wd env.work (po + 2 * sideFw side + 2 * k + 1)) = some L.tables[k].index.toUInt64 ∧
      L.tables[k].variableCount < 2 ^ 64 ∧ L.tables[k].index < 2 ^ 64 := fun k h ↦ by
    have hj : sideFw side + k < (L.framework ++ L.tables).size := by rw [Array.size_append]; omega
    obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hPw (sideFw side + k) hj
    rw [Array.getElem_append_right (by omega)] at a1 a2 b1 b2
    simp only [hFs', Nat.add_sub_cancel_left] at a1 a2 b1 b2
    rw [Region.at, wd_wd, show po + 2 * (sideFw side + k) = po + 2 * sideFw side + 2 * k by omega] at a2
    rw [Region.at, wd_wd, show po + (2 * (sideFw side + k) + 1) = po + 2 * sideFw side + 2 * k + 1 by omega] at b2
    rw [k1 _ (by omega) (by omega), k1 _ (by omega) (by omega)]
    exact ⟨a2, b2, a1, b1⟩
  have hrows : ∀ k (h : k < B.size), s₁.mem (wd env.work (po + 128 + k)) = some B[k].rows.toUInt64 ∧
      B[k].rows < 2 ^ 64 := fun k h ↦ by
    obtain ⟨r1, r2⟩ := hRw k h
    rw [Region.at, wd_wd, ← Nat.add_assoc] at r2
    rw [k1 _ (by omega) (by omega)]
    exact ⟨r2, r1⟩
  have hn₁ : s₁.mem (wd env.work depthR.off) = some point.size.toUInt64 := by
    rw [k1 _ (by omega) (by omega)]; exact hn
  have hpt₁ : PointAt s₁.mem env.work point := hpt.keeps ak (by omega) (by omega) (by omega)
  refine WP.blk_cons (WP.mono (selTb_spec (p := env.work) (po := po + 2 * sideFw side) (ro := po + 128)
    (tso := tso) (wo := wo) (nb := sideNb side) (pl := L.tables) (B := B) (point := point)
    (by omega) hBs (by omega) (by omega) (by omega) (by rw [af .r15 (by decide)]; rsimp) hplT hrows
    (tables_vc layout side) hn₁ hps hpt₁ (by omega)
    (fun w hw ↦ show (s₁.mem (wd env.work (tso + w))).isSome from by
      rw [ad]; exact hi.ok3_some (r := tselR side) (ok3_sreg (by omega)) (by simp [tselR, sreg]; omega))
    (fun w hw ↦ show (s₁.mem (wd env.work (wo + w))).isSome from by
      rw [ad]; exact hi.ok3_some (r := padWR side) (ok3_sreg (by omega)) (by simp [padWR, sreg]; omega)))
    (fun s₂ ⟨b1, b2, bd, bo, bf⟩ ↦ WP.blk_nil ?_) fun _ h ↦ h)
  refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_, fun j hj ↦ ?_, ⟨?_, fun x hx ↦ ?_, fun x ↦ (bd x).trans (ad x)⟩⟩
  · rw [Array.size_map] at hk
    obtain ⟨c0, c1⟩ := b1 k hk
    simp only [Array.getElem_map]
    refine ⟨?_, ?_⟩
    · rw [Region.at, wd_wd]; exact c0
    · rw [Region.at, wd_wd, wd_wd]; exact c1
  · simp only [padWeights, Array.size_map] at hk
    obtain ⟨c0, c1⟩ := b2 k hk
    simp only [padWeights, Array.getElem_map]
    refine ⟨?_, ?_⟩
    · rw [Region.at, wd_wd]; exact c0
    · rw [Region.at, wd_wd, wd_wd]; exact c1
  · rw [Array.size_map] at hj
    obtain ⟨c0, c1⟩ := a j hj
    simp only [Array.getElem_map]
    refine ⟨?_, ?_⟩
    · rw [Region.at, wd_wd, bo _ fun w hw1 hw2 e ↦ by
        rw [wd_inj (by omega) (by omega)] at e; omega]
      exact c0
    · rw [Region.at, wd_wd, wd_wd, bo _ fun w hw1 hw2 e ↦ by
        rw [wd_inj (by omega) (by omega)] at e; omega]
      exact c1
  · rw [bf .rdi (by decide), af .rdi (by decide)]; rsimp
  · rw [bo x fun w hw1 hw2 e ↦ ?_, ao x fun w hw1 hw2 e ↦ ?_]
    · rfl
    · exact hx (fselR side) (by simp) ⟨w - fo, by simp [fselR, sreg] at *; omega, by rw [e]; congr 1; omega⟩
    · by_cases hw : w < wo
      · exact hx (tselR side) (by simp) ⟨w - tso, by simp [tselR, sreg] at *; omega, by rw [e]; congr 1; omega⟩
      · exact hx (padWR side) (by simp) ⟨w - wo, by simp [padWR, sreg] at *; omega, by rw [e]; congr 1; omega⟩

end NativeVm.Code.P3
