module

public import NativeVm.Code.Phase3.FormsStep

/-!
# The bus forms of a side: the whole run on words

`loopCode_spec`: the blocks' loop takes the invariant from `0` blocks to all. `formsWith_spec`: the
padding row, the data and the loop's state establish the invariant at `0` blocks.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript

variable {w ctx : UInt64} {side : Nat} {D : List DBlk} {blocks : Array BusBlockW}
  {sels pws ws : Array EW} {β : EW} {forms : Array (Array FormW)} {mem0 : UInt64 → Option UInt64}
  {s : QState} {E : QState → Prop}

/-- **The blocks' loop.** -/
theorem loopCode_spec (hside : side < 3) (hD : dOk side D = true)
    (hcw : ∀ k < dataEnd, wd ctx ctxWork ≠ wd w k)
    (hbl : blocks.toList.map (fun b ↦ (b.owner, blockEnts b)) = D.map fun b ↦ (b.1, entsW b.2))
    (hs : sels.size = blocks.size) (hp : pws.size = blocks.size)
    (hI : FLInv w ctx side D blocks sels pws ws β forms mem0 0 s) :
    WP (loopCode side (wSrc side) (bSrc side)) s
      (fun s' ↦ FLInv w ctx side D blocks sels pws ws β forms mem0 D.length s') E := by
  have hD51 := (dOk_spec hD).2.1
  unfold loopCode
  refine wk_wp hI.rdi hI.wp ?_
  refine ldw0 (w := w) (k := vRem) (by rsimp) hI.rem ?_
  refine WP.blk_cons (WP.loop (fun t ↦ ∃ i, FLInv w ctx side D blocks sels pws ws β forms mem0 i t ∧
      t.reg .rax = (D.length - i).toUInt64) (fun t ↦ (t.reg .rax).toNat)
    ⟨0, ⟨hI.le, by rsimp; exact hI.rdi, hI.wp, hI.pad, hI.data, hI.cur, hI.sel, hI.rem, hI.hsel,
      hI.hpw, hI.hws, hI.hbeta, hI.sum, hI.fz, hI.shp, hI.ok, hI.other, hI.keep, hI.dom⟩,
      by rsimp⟩ ?_ ?_)
  · rintro t ⟨i, hI', hax⟩ hc
    have hi : i < D.length := by
      rw [cond_ne, hax, rhs_imm, fs_toUInt64_ne_zero (by omega)] at hc
      simp only [decide_eq_true_eq] at hc
      omega
    refine WP.mono (blockStep hside hD hcw hbl hs hp hI' hi) (fun t' ⟨h1, h2⟩ ↦
      ⟨⟨i + 1, h1, h2⟩, ?_⟩) (fun _ h ↦ h)
    rw [h2, hax, NativeVm.Transcript.toNat_toUInt64 (by omega),
      NativeVm.Transcript.toNat_toUInt64 (by omega)]
    omega
  · rintro t ⟨i, hI', hax⟩ hc
    have hi : i = D.length := by
      have := hI'.le
      rw [cond_ne, hax, rhs_imm, fs_toUInt64_ne_zero (by omega)] at hc
      simp only [decide_eq_false_iff_not, not_not] at hc
      omega
    exact WP.skip (hi ▸ hI')

/-- **The forms of a side** on words: from the initial values, the invariant after every block. -/
theorem formsWith_spec (hside : side < 3) (hD : dOk side D = true)
    (hcw : ∀ k < dataEnd, wd ctx ctxWork ≠ wd w k)
    (hbl : blocks.toList.map (fun b ↦ (b.owner, blockEnts b)) = D.map fun b ↦ (b.1, entsW b.2))
    (hs : sels.size = blocks.size) (hp : pws.size = blocks.size)
    (hrdi : s.reg .rdi = ctx) (hwp : s.mem (wd ctx ctxWork) = some w)
    (hdom : ∀ k < dataEnd, (s.mem (wd w k)).isSome)
    (hsel : ∀ j (h : j < sels.size), EAtI s.mem w ((tselR side).off + 2 * j) sels[j])
    (hpw : ∀ j (h : j < pws.size), EAtI s.mem w ((tselR side).off + 102 + 2 * j) pws[j])
    (hws : side ≠ 2 → ∀ j < 16, EAtI s.mem w (wR.off + 2 * j) (ws.getD j 0))
    (hws2 : side = 2 → ws.getD 0 0 = 1)
    (hβ : side ≠ 2 → EAtI s.mem w betaR.off β) (hβ2 : side = 2 → β = 0)
    (hfz : ∀ t < nTables, s.mem (wd w (busR.off + formOff t side)) = some (0 : Nat).toUInt64 ∧
      (forms.getD t #[]).getD side #[] = #[])
    (hok : FormsOk forms) :
    WP (formsWith side D) s
      (fun s' ↦ FLInv w ctx side D blocks sels pws ws β forms s.mem D.length s') E := by
  have hlen : blocks.size = D.length := by simpa using congrArg List.length hbl
  have hD51 := (dOk_spec hD).2.1
  have hDenc := (dOk_spec hD).2.2.2
  have v1 := padOff_val
  have v2 := dataEnd_eq
  have v3 := dOff_val
  have v4 := sumR_off side
  have v5 := fs_tselR_off side
  have v6 := wvOff_val
  have v7 := bvOff_val
  have v8 := vCur_val
  have v9 := vSel_val
  have v10 := vRem_val
  have v11 := busR_off
  have v12 := ftOff_val
  have v13 := fs_wR_off
  have v14 := betaR_off
  have v15 := wSrc_cases side
  have v16 := bSrc_cases side
  unfold formsWith
  refine wp_then' (padCode_spec (E := E) hrdi hwp hcw fun k hk ↦ hdom _ (by omega))
    fun s1 ⟨r1, pad1, k1⟩ d1 ↦ ?_
  have wp1 : s1.mem (wd ctx ctxWork) = some w := by rw [k1 _ fun k hk ↦ hcw k (by omega)]; exact hwp
  have dm1 : ∀ k < dataEnd, (s1.mem (wd w k)).isSome := fun k hk ↦ by rw [d1]; exact hdom k hk
  refine wp_then' (dataCode_spec (E := E) (side := side) (D := D) r1 wp1 hDenc dm1)
    fun s2 ⟨r2, dat2, k2⟩ d2 ↦ ?_
  have wp2 : s2.mem (wd ctx ctxWork) = some w := by rw [k2 _ fun k hk ↦ hcw k (by omega)]; exact wp1
  have dm2 : ∀ k < dataEnd, (s2.mem (wd w k)).isSome := fun k hk ↦ by rw [d2]; exact dm1 k hk
  refine wp_then' (initCode_spec (E := E) (D := D) r2 wp2 hside dm2)
    fun s3 ⟨r3, sum3, wv3, bv3, cur3, sel3, rem3, k3⟩ d3 ↦ ?_
  have kw : ∀ k, k < dataEnd → ¬ ((padOff ≤ k ∧ k < padOff + 124) ∨ (dOff ≤ k ∧ k < dOff + 4096) ∨
      k = (sumR side).off ∨ k = (sumR side).off + 1 ∨ k = wvOff ∨ k = wvOff + 1 ∨
      k = bvOff ∨ k = bvOff + 1 ∨ k = vCur ∨ k = vSel ∨ k = vRem) →
      s3.mem (wd w k) = s.mem (wd w k) := fun k hk hn ↦ by
    rw [k3.word (by omega) fun j hj ↦ ⟨by omega, by omega⟩,
      k2.word (by omega) fun j hj ↦ ⟨by omega, by omega⟩,
      k1.word (by omega) fun j hj ↦ ⟨by omega, by omega⟩]
  refine loopCode_spec hside hD hcw hbl hs hp ⟨by omega, r3, ?_, ?_, ?_, ?_, sel3, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, hok, fun _ _ _ ↦ rfl, ?_, ?_⟩
  · rw [k3 _ fun k hk ↦ hcw k (by omega)]; exact wp2
  · intro a ha
    rw [k3.word (by omega) fun j hj ↦ ⟨by omega, by omega⟩,
      k2.word (by omega) fun j hj ↦ ⟨by omega, by omega⟩]
    exact pad1 a ha
  · exact dataAt_congr D dOff (fun k h1 h2 ↦ k3.word (by omega) fun j hj ↦ ⟨by omega, by omega⟩) dat2
  · rw [cur3]; rfl
  · rw [rem3]; rfl
  · intro j hj
    exact (hsel j hj).congr fun k hk ↦ kw _ (by omega) (by omega)
  · intro j hj
    exact (hpw j hj).congr fun k hk ↦ kw _ (by omega) (by omega)
  · intro j hj
    by_cases h2 : side = 2
    · have : j = 0 := by unfold slotN at hj; rw [iteT h2] at hj; omega
      subst this
      rw [hws2 h2]
      unfold wSrc; rw [iteT h2, Nat.mul_zero, Nat.add_zero]; exact wv3
    · have hj' : j < 16 := by unfold slotN at hj; rw [iteF h2] at hj; exact hj
      unfold wSrc; rw [iteF h2]
      exact (hws h2 j hj').congr fun k hk ↦ kw _ (by omega) (by omega)
  · by_cases h2 : side = 2
    · rw [hβ2 h2]; unfold bSrc; rw [iteT h2]; exact bv3
    · unfold bSrc; rw [iteF h2]
      exact (hβ h2).congr fun k hk ↦ kw _ (by omega) (by omega)
  · exact sum3
  · intro t ht
    obtain ⟨h0, he⟩ := hfz t ht
    rw [accI_zero]
    simp only
    rw [he]
    have := formOff_eq t side
    refine ⟨by simp, by rw [kw _ (by unfold nTables at ht; omega) (by unfold nTables at ht; omega)]; exact h0,
      fun i hi ↦ absurd hi (by simp)⟩
  · intro t ht
    rw [accI_zero]
    simp only
    rw [(hfz t ht).2]
    rfl
  · have kA := k1.trans k2 (U := fun k ↦ (padOff ≤ k ∧ k < padOff + 124) ∨ (dOff ≤ k ∧ k < dOff + 4096))
      (fun k h ↦ .inl h) (fun k h ↦ .inr h)
    refine kA.trans k3 (fun k h ↦ ?_) (fun k h ↦ ?_)
    · unfold W
      exact .inr (.inr (.inr (by omega)))
    · unfold W
      rcases h with h | h | h | h | h | h | h | h | h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      all_goals exact .inr (.inr (.inr (by omega)))
  · intro k hk; rw [d3]; exact dm2 k hk

end NativeVm.Code.P3
