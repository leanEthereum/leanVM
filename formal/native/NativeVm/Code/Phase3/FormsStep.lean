module

public import NativeVm.Code.Phase3.FormsLoopDefs

/-!
# The bus forms of a side: one block

`blockStep`: from the invariant after `i` blocks, `blockCode` (the block form, the padding rows'
term, the owner's form) establishes it after `i + 1`, the blocks left in `rax`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript

theorem formOff_eq (t side : Nat) : formOff t side = 741 * (3 * t + side) := by
  unfold formOff; rw [show formWords = 741 from rfl]

theorem formCap_eq : formCap = 148 := rfl

theorem fs_wR_off : wR.off = 52670 := by show scratchR.off + 0 = _; rw [scratchR_off]
theorem betaR_off : betaR.off = 52702 := by show scratchR.off + 32 = _; rw [scratchR_off]

theorem wSrc_lt (side : Nat) : wSrc side + 32 ≤ fOff ∨ vG < wSrc side := by
  unfold wSrc; split
  · right; rw [wvOff_val, vG_val]; omega
  · left; rw [fs_wR_off, fOff_val]; omega

theorem wSrc_le (side : Nat) : 52670 ≤ wSrc side ∧ wSrc side ≤ 61182 := by
  unfold wSrc; split
  · rw [wvOff_val]; omega
  · rw [fs_wR_off]; omega

theorem wSrc_cases (side : Nat) :
    (wSrc side = 52670 ∧ slotN side = 16) ∨ (wSrc side = 61182 ∧ slotN side = 1) := by
  unfold wSrc slotN; split
  · right; rw [wvOff_val]; exact ⟨rfl, rfl⟩
  · left; rw [fs_wR_off]; exact ⟨rfl, rfl⟩

theorem bSrc_cases (side : Nat) : bSrc side = 52702 ∨ bSrc side = 61214 := by
  unfold bSrc; split
  · right; rw [bvOff_val]
  · left; rw [betaR_off]

theorem bSrc_le (side : Nat) : 52702 ≤ bSrc side ∧ bSrc side ≤ 61214 ∧
    (bSrc side + 2 ≤ fOff ∨ vG < bSrc side) := by
  unfold bSrc; split
  · rw [bvOff_val, vG_val, fOff_val]; omega
  · rw [betaR_off, vG_val, fOff_val]; omega

variable {w ctx : UInt64} {side : Nat} {D : List DBlk} {blocks : Array BusBlockW}
  {sels pws ws : Array EW} {β : EW} {forms : Array (Array FormW)} {mem0 : UInt64 → Option UInt64}
  {i : Nat} {s : QState} {E : QState → Prop}

/-- **One block.** -/
theorem blockStep (hside : side < 3) (hD : dOk side D = true)
    (hcw : ∀ k < dataEnd, wd ctx ctxWork ≠ wd w k)
    (hbl : blocks.toList.map (fun b ↦ (b.owner, blockEnts b)) = D.map fun b ↦ (b.1, entsW b.2))
    (hs : sels.size = blocks.size) (hp : pws.size = blocks.size)
    (hI : FLInv w ctx side D blocks sels pws ws β forms mem0 i s) (hi : i < D.length) :
    WP (blockCode side (wSrc side) (bSrc side)) s (fun s' ↦
      FLInv w ctx side D blocks sels pws ws β forms mem0 (i + 1) s' ∧
      s'.reg .rax = (D.length - (i + 1)).toUInt64) E := by
  have hlen : blocks.size = D.length := by simpa using congrArg List.length hbl
  have hbi : i < blocks.size := by omega
  have hb2 : (blocks[i].owner, blockEnts blocks[i]) = (D[i].1, entsW D[i].2) := by
    have := congrArg (·[i]?) hbl
    simp only [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hbi,
      List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] at this
    exact this
  obtain ⟨hown, hents⟩ := Prod.mk.inj hb2
  obtain ⟨hOK, hD51, hDsh, hDenc⟩ := dOk_spec hD
  have hbk := hOK _ (List.getElem_mem hi)
  obtain ⟨ho6, hn31, hent⟩ := blkOk_spec hbk
  have hform : blockForm blocks[i] ws β = buildF D[i].2 ws β := blockForm_eq_buildF hents ws β
  have he1 := encode_take_succ side D hi
  have he2 := encode_take_le side D (i + 1)
  have hbl' := encBlk_length side D[i]
  have v1 := fOff_val
  have v2 := vG_val
  have v3 := vCur_val
  have v4 := dataEnd_eq
  have v5 := dOff_val
  have v6 := vSel_val
  have v7 := vRem_val
  have v8 := padOff_val
  have v9 := sumR_off side
  have v10 := fs_tselR_off side
  have v11 := busR_off
  have v12 := formOff_eq D[i].1 side
  have v13 := formCap_eq
  have v14 := wSrc_le side
  have v15 := bSrc_le side
  have v16 := wvOff_val
  have v17 := bvOff_val
  have v18 := fCap_val
  have hsl := hs ▸ hbi
  have hpl := hp ▸ hbi
  set q := dOff + (encode side (D.take i)).length with hq
  set o := D[i].1 with ho
  set go := busR.off + formOff o side with hgo
  set sp := (tselR side).off + 2 * i with hsp
  set acc := accI forms side blocks sels pws ws β i with hacc
  set F := buildF D[i].2 ws β with hF
  set row := (tablesW.getD o default).padding with hrow
  unfold blockCode
  -- the block form
  refine wp_then' (buildCode_spec (E := E) (w := w) (side := side) (q := q) (b := D[i]) (ws := ws)
    (β := β) hI.rdi hI.wp hcw hI.cur (dataAt_get D dOff i hi hI.data) hbk
    (fun e he ↦ hI.hws e.1 (hent e he).1) hI.hbeta (fun k h1 h2 ↦ hI.dom k (by omega))
    (by omega) (by omega) (wSrc_lt side) (by omega) v15.2.2 (by omega))
    fun s1 ⟨r1, F1, c1, g1, k1⟩ d1 ↦ ?_
  have kw1 : ∀ k, k < dataEnd → ¬ (SF k ∨ k = vCur ∨ k = vG) → s1.mem (wd w k) = s.mem (wd w k) :=
    fun k hk hn ↦ k1.word (by omega) fun j hj ↦ ⟨by unfold SF at hj; omega, fun e ↦ hn (e ▸ hj)⟩
  -- the padding rows' term
  have hrow' : ∀ t ∈ F, ∀ a ∈ t.cols, a < 92 ∧ row.getD a 0 = kE (Pv a) := fun t ht a ha ↦ by
    obtain ⟨e, he, hae⟩ := buildF_cols ht a ha
    have := (hent e he).2.2.1 a hae
    exact ⟨this.1, padding_getD (by omega) this.1 this.2⟩
  have hpad1 : PadAt s1.mem w := fun a ha ↦ by
    rw [kw1 _ (by omega) (by unfold SF; omega)]; exact hI.pad a ha
  have hwp1 : s1.mem (wd ctx ctxWork) = some w := by
    rw [k1 _ fun k hk ↦ hcw k (by unfold SF at hk; omega)]; exact hI.wp
  have hsl' : 2 * i + 2 ≤ 102 := by omega
  refine wp_then' (evalCode_spec (E := E) (w := w) (side := side) (sp := sp) (F := F) (row := row)
    (sel := sels[i]) (pw := pws[i]) (S := acc.2) r1 hwp1 F1 hpad1 hrow'
    (by rw [kw1 _ (by omega) (by unfold SF; omega)]; exact hI.sel)
    ((hI.hsel i hsl).congr fun k hk ↦ kw1 _ (by omega) (by unfold SF; omega))
    (by
      have := (hI.hpw i hpl).congr (mem' := s1.mem) fun k hk ↦ kw1 _ (by omega) (by unfold SF; omega)
      rwa [show (tselR side).off + 102 + 2 * i = sp + 102 by omega] at this)
    ((hI.sum).congr fun k hk ↦ kw1 _ (by omega) (by unfold SF; omega)) hside)
    fun s2 ⟨r2, S2, k2⟩ d2 ↦ ?_
  have kw2 : ∀ k, k < dataEnd → ¬ (SF k ∨ k = vCur ∨ k = vG ∨ k = (sumR side).off ∨
      k = (sumR side).off + 1) → s2.mem (wd w k) = s.mem (wd w k) := fun k hk hn ↦ by
    rw [k2.word (by omega) fun j hj ↦ ⟨by omega, fun e ↦ hn (by omega)⟩]
    exact kw1 k hk (by unfold SF at hn ⊢; omega)
  have hwp2 : s2.mem (wd ctx ctxWork) = some w := by
    rw [k2 _ fun k hk ↦ hcw k (by omega)]; exact hwp1
  -- the owner's form
  have hroom : ((shape F).foldl addMono (shape ((acc.1.getD o #[]).getD side #[]))).length ≤ formCap := by
    rw [hF, shape_buildF, hI.shp o (by unfold nTables; omega)]
    have : (blockShape D[i].2).foldl addMono (ownerShape (D.take i) o) = ownerShape (D.take (i + 1)) o := by
      rw [ownerShape_succ hi, shapeStep, iteT rfl]
    rw [this]
    exact (ownerShape_prefix D (i + 1) o).length_le.trans (hDsh o (by omega))
  refine WP.mono (WP.frame (accCode_spec (E := E) (w := w) (go := go) (sp := sp) (rem := D.length - i)
    (g := (acc.1.getD o #[]).getD side #[]) (F := F) (sel := sels[i]) r2 hwp2 hcw
    (by rw [k2.word (by omega) fun j hj ↦ ⟨by omega, by omega⟩]; exact g1)
    (by rw [kw2 _ (by omega) (by unfold SF; omega)]; exact hI.sel)
    (by rw [kw2 _ (by omega) (by unfold SF; omega)]; exact hI.rem) (by omega)
    ((hI.fz o (by unfold nTables; omega)).congr fun k hk ↦ kw2 _ (by omega) (by unfold SF; omega))
    (F1.congr fun k hk ↦ k2.word (by omega) fun j hj ↦ ⟨by omega, by omega⟩)
    ((hI.hsel i hsl).congr fun k hk ↦ kw2 _ (by omega) (by unfold SF; omega)) hroom
    (fun k hk ↦ by rw [d2, d1]; exact hI.dom _ (by omega)) (by omega) (.inr (by omega)) (by omega)))
    (fun s3 ⟨⟨r3, G3, sel3, rem3, rax3, k3⟩, d3, _⟩ ↦ ?_) (fun _ h ↦ h.1)
  have v19 := ftOff_val
  have kw3 : ∀ k, k < dataEnd → ¬ (SF k ∨ k = vCur ∨ k = vG ∨ k = (sumR side).off ∨
      k = (sumR side).off + 1 ∨ (go ≤ k ∧ k < go + 1 + 5 * formCap) ∨ k = vSel ∨ k = vRem) →
      s3.mem (wd w k) = s.mem (wd w k) := fun k hk hn ↦ by
    rw [k3.word (by omega) fun j hj ↦ ⟨by omega, fun e ↦ hn (by subst e; omega)⟩]
    exact kw2 k hk (by unfold SF at hn ⊢; omega)
  have hacc1 : accI forms side blocks sels pws ws β (i + 1) =
      sfStep side ws β acc ((sels[i], pws[i]), blocks[i]) := accI_succ hs hp hbi
  have hown6 : blocks[i].owner < nTables := by rw [hown]; unfold nTables; omega
  refine ⟨⟨by omega, r3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [k3 _ fun k hk ↦ hcw k (by omega)]; exact hwp2
  · intro a ha; rw [kw3 _ (by omega) (by unfold SF; omega)]; exact hI.pad a ha
  · exact dataAt_congr D dOff (fun k h1 h2 ↦ kw3 k (by omega) (by unfold SF; omega)) hI.data
  · rw [k3.word (by omega) fun j hj ↦ ⟨by omega, by omega⟩,
      k2.word (by omega) fun j hj ↦ ⟨by omega, by omega⟩, c1, he1, Nat.add_assoc]
  · rw [sel3, show sp + 2 = (tselR side).off + 2 * (i + 1) by omega]
  · rw [rem3, Nat.sub_sub]
  · intro j hj
    exact (hI.hsel j hj).congr fun k hk ↦ kw3 _ (by omega) (by unfold SF; omega)
  · intro j hj
    exact (hI.hpw j hj).congr fun k hk ↦ kw3 _ (by omega) (by unfold SF; omega)
  · intro j hj
    have hc := wSrc_cases side
    exact (hI.hws j hj).congr fun k hk ↦ kw3 _ (by omega) (by unfold SF; omega)
  · have hc := bSrc_cases side
    exact hI.hbeta.congr fun k hk ↦ kw3 _ (by omega) (by unfold SF; omega)
  · rw [hacc1, sfStep_snd]
    have : (tablesW.getD blocks[i].owner default).padding = row := by rw [hrow, hown]
    rw [hform, this]
    exact S2.congr fun k hk ↦ k3.word (by omega) fun j hj ↦ ⟨by omega, by omega⟩
  · intro t ht
    rw [hacc1, sfStep_getD hI.ok hown6 hside]
    simp only [hown, and_true]
    by_cases htt : o = t
    · rw [iteT htt, ← htt, hform]
      exact G3
    · rw [iteF htt]
      have := formOff_eq t side
      exact (hI.fz t ht).congr fun k hk ↦ kw3 _ (by unfold nTables at ht; omega)
        (by unfold SF nTables at *; omega)
  · intro t ht
    rw [hacc1, sfStep_getD hI.ok hown6 hside, ownerShape_succ hi, shapeStep]
    simp only [hown, and_true]
    by_cases htt : o = t
    · rw [iteT htt, iteT htt, ← htt, hform, shape_addScaled, shape_buildF, hI.shp o (by omega)]
    · rw [iteF htt, iteF htt]
      exact hI.shp t ht
  · rw [hacc1]; exact sfStep_ok hI.ok hown6
  · intro t s' hs'
    rw [hacc1, sfStep_getD hI.ok hown6 hside, iteF (fun e ↦ hs' e.2)]
    exact hI.other t s' hs'
  · refine hI.keep.trans (show KeepS w _ s.mem s3.mem from fun a ha ↦ ?_) (fun k h ↦ h)
      (fun k (hk : SF k ∨ k = vCur ∨ k = vG ∨ k = (sumR side).off ∨
        k = (sumR side).off + 1 ∨ (go ≤ k ∧ k < go + 1 + 5 * formCap) ∨ k = vSel ∨ k = vRem) ↦ ?_)
    · rw [k3 a fun k hk ↦ ha k (by omega), k2 a fun k hk ↦ ha k (by omega), k1 a fun k hk ↦ ha k (by rcases hk with h | h | h <;> simp [h])]
    · unfold W SF at *
      rcases hk with h | h | h | h | h | h | h | h
      · exact .inr (.inr (.inr ⟨by omega, by omega⟩))
      · exact .inr (.inr (.inr ⟨by omega, by omega⟩))
      · exact .inr (.inr (.inr ⟨by omega, by omega⟩))
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inl ⟨o, by unfold nTables; omega, h⟩
      · exact .inr (.inr (.inr ⟨by omega, by omega⟩))
      · exact .inr (.inr (.inr ⟨by omega, by omega⟩))
  · intro k hk
    rw [d3, d2, d1]; exact hI.dom k hk
  · rw [rax3, Nat.sub_sub]

end NativeVm.Code.P3
