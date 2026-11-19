module

public import NativeVm.Code.Phase3.FormsPad

/-!
# The bus forms of a side: the data and the loop's state

`storeL_spec`: the stores of a list of words. `dataAt_of_words`: the data's words are its blocks
(`DataAt`). `dataCode_spec`: the data stored from word `dOff`. `initCode_spec`: the sum `0`, the
count side's weight `1` and `β = 0`, the loop's state.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript

variable {w ctx : UInt64} {E : QState → Prop}

theorem storeL_cons (k w0 : Nat) (ws : List Nat) :
    storeL k (w0 :: ws) = I (.storei (aw k) (Int64.ofNat w0)) :: storeL (k + 1) ws := rfl

/-- **The stores of `ws` from word `k`.** -/
theorem storeL_spec {P : QState → Prop} {xs : List Stmt} :
    ∀ (ws : List Nat) (k : Nat) (s : QState), s.reg .r11 = w → k + ws.length < 2 ^ 61 →
      (∀ i < ws.length, (s.mem (wd w (k + i))).isSome) →
      (∀ s' : QState, s'.reg = s.reg →
        (∀ i (h : i < ws.length), s'.mem (wd w (k + i)) = some ws[i].toUInt64) →
        KeepS w (fun j ↦ k ≤ j ∧ j < k + ws.length) s.mem s'.mem → WP (blk xs) s' P E) →
      WP (blk (storeL k ws ++ xs)) s P E
  | [], k, s, _, _, _, h => h s rfl (fun i hi ↦ absurd hi (Nat.not_lt_zero _)) (KeepS.refl _ _)
  | w0 :: ws, k, s, h11, hb, hd, h => by
    rw [storeL_cons, List.cons_append]
    refine stiw0 (w := w) (k := k) h11 (by have := hd 0 (by simp); rwa [Nat.add_zero] at this) ?_
    refine storeL_spec ws (k + 1) _ h11 (by simp at hb; omega) (fun i hi ↦ ?_) fun s' hr hw hk ↦ ?_
    · rw [QState.setMem_mem]
      split
      · rfl
      · have := hd (i + 1) (by simp; omega)
        rwa [show k + (i + 1) = k + 1 + i by omega] at this
    · refine h s' hr (fun i hi ↦ ?_) ?_
      · rcases i with _ | i
        · rw [hk.word (by simp at hb; omega) fun j hj ↦ ⟨by simp at hb; omega, by omega⟩]
          simp [Int64.toUInt64_ofNat']
        · have := hw i (by simp at hi; omega)
          rw [show k + 1 + i = k + (i + 1) by omega] at this
          simpa using this
      · exact (KeepS.setMem (KeepS.refl _ _) (k := k) ⟨le_rfl, by simp⟩ _).trans hk (fun j h ↦ h)
          (fun j h ↦ ⟨by omega, by simp; omega⟩)

theorem encEnts_getD : ∀ (es : List DEnt) (j k : Nat), j < es.length → k < 5 →
    (es.flatMap encEnt).getD (5 * j + k) 0 = (encEnt es[j]!).getD k 0
  | e :: es, 0, k, _, hk => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show k < (encEnt e).length by simp [encEnt]; omega)]
    rfl
  | e :: es, j + 1, k, hj, hk => by
    simp only [List.flatMap_cons, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp [encEnt]; omega)]
    have := encEnts_getD es j k (by simp at hj; omega) hk
    simp only [List.getD_eq_getElem?_getD] at this
    rw [show 5 * (j + 1) + k - (encEnt e).length = 5 * j + k by simp [encEnt]; omega, this]
    rfl

/-- **The data's words are its blocks.** -/
theorem dataAt_of_words {mem : UInt64 → Option UInt64} {side : Nat} :
    ∀ (D : List DBlk) (q : Nat),
      (∀ i < (encode side D).length, mem (wd w (q + i)) = some ((encode side D).getD i 0).toUInt64) →
      DataAt mem w side q D
  | [], _, _ => trivial
  | b :: D, q, h => by
    have he : encode side (b :: D) = encBlk side b ++ encode side D := by
      simp [encode, List.flatMap_cons]
    have hl := encBlk_length side b
    have g : ∀ i < (encBlk side b).length, mem (wd w (q + i)) = some ((encBlk side b).getD i 0).toUInt64 :=
      fun i hi ↦ by
        have := h i (by rw [he]; simp; omega)
        rwa [he, List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
          ← List.getD_eq_getElem?_getD] at this
    refine ⟨⟨?_, ?_, fun j hj ↦ ?_⟩, dataAt_of_words D _ fun i hi ↦ ?_⟩
    · have := g 0 (by omega)
      rw [Nat.add_zero] at this
      rw [this]; rfl
    · rw [g 1 (by omega)]; rfl
    · have ge : ∀ k < 5, mem (wd w (q + 2 + 5 * j + k)) = some ((encEnt b.2[j]!).getD k 0).toUInt64 :=
        fun k hk ↦ by
          rw [show q + 2 + 5 * j + k = q + (5 * j + k + 1 + 1) by omega, g _ (by omega)]
          simp only [encBlk, List.getD_cons_succ]
          rw [encEnts_getD _ _ _ hj hk]
      have e : b.2[j]! = b.2[j] := by simp [hj]
      rw [e] at ge
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := ge 0 (by omega); rw [Nat.add_zero] at this; rw [this]; rfl
      · rw [ge 1 (by omega)]; rfl
      · rw [ge 2 (by omega)]; rfl
      · rw [ge 3 (by omega)]; rfl
      · rw [ge 4 (by omega)]; rfl
    · have := h ((encBlk side b).length + i) (by rw [he]; simp; omega)
      rw [he, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD] at this
      rw [← Nat.add_assoc] at this
      exact this

theorem fs_tselR_off (side : Nat) : (tselR side).off = 53182 + 512 * side := by
  show scratchR.off + (512 + 512 * side) = _
  rw [scratchR_off]; omega

theorem fs_padWR_off (side : Nat) : (padWR side).off = (tselR side).off + 102 := by
  show scratchR.off + (614 + 512 * side) = scratchR.off + (512 + 512 * side) + 102
  omega

variable {s : QState}

/-- **The data** from word `dOff`. -/
theorem dataCode_spec {side : Nat} {D : List DBlk} (hrdi : s.reg .rdi = ctx)
    (hwp : s.mem (wd ctx ctxWork) = some w) (hlen : (encode side D).length ≤ 4096)
    (hdom : ∀ k < dataEnd, (s.mem (wd w k)).isSome) :
    WP (dataCode side D) s (fun s' ↦ s'.reg .rdi = ctx ∧ DataAt s'.mem w side dOff D ∧
      KeepS w (fun k ↦ dOff ≤ k ∧ k < dOff + 4096) s.mem s'.mem) E := by
  have v1 := dOff_val
  have v2 := dataEnd_eq
  unfold dataCode
  refine wk_wp hrdi hwp ?_
  rw [← List.append_nil (storeL dOff (encode side D))]
  refine storeL_spec (w := w) _ dOff _ (by rsimp) (by omega) (fun i hi ↦ by rsimp; exact hdom _ (by omega))
    fun s' hr hw hk ↦ wp_done ⟨?_, ?_, ?_⟩
  · rw [hr]; rsimp; exact hrdi
  · refine dataAt_of_words D dOff fun i hi ↦ ?_
    rw [hw i hi, List.getD_eq_getElem _ _ hi]
  · exact hk.mono fun k h ↦ ⟨h.1, by omega⟩

/-- **The loop's state**: the sum `0`, the count side's weight `1` and `β = 0`, the first block,
the first selector, the blocks left. -/
theorem initCode_spec {side : Nat} {D : List DBlk} (hrdi : s.reg .rdi = ctx)
    (hwp : s.mem (wd ctx ctxWork) = some w) (hside : side < 3)
    (hdom : ∀ k < dataEnd, (s.mem (wd w k)).isSome) :
    WP (initCode side D) s (fun s' ↦ s'.reg .rdi = ctx ∧ EAtI s'.mem w (sumR side).off 0 ∧
      EAtI s'.mem w wvOff 1 ∧ EAtI s'.mem w bvOff 0 ∧ s'.mem (wd w vCur) = some (wd w dOff) ∧
      s'.mem (wd w vSel) = some (wd w (tselR side).off) ∧
      s'.mem (wd w vRem) = some D.length.toUInt64 ∧
      KeepS w (fun k ↦ k = (sumR side).off ∨ k = (sumR side).off + 1 ∨ k = wvOff ∨ k = wvOff + 1 ∨
        k = bvOff ∨ k = bvOff + 1 ∨ k = vCur ∨ k = vSel ∨ k = vRem) s.mem s'.mem) E := by
  have v1 := wvOff_val
  have v2 := bvOff_val
  have v3 := vCur_val
  have v4 := vSel_val
  have v5 := vRem_val
  have v6 := sumR_off side
  have v7 := dataEnd_eq
  have v8 := dOff_val
  have v9 := fs_tselR_off side
  unfold initCode
  refine wk_wp hrdi hwp ?_
  refine stiw0 (w := w) (k := (sumR side).off) (by rsimp) (hdom _ (by omega)) ?_
  refine stiw0 (w := w) (k := (sumR side).off + 1) (by rsimp)
    (by mem_simp; exact hdom _ (by omega)) ?_
  refine stiw0 (w := w) (k := wvOff) (by rsimp) (by mem_simp; exact hdom _ (by omega)) ?_
  refine stiw0 (w := w) (k := wvOff + 1) (by rsimp) (by mem_simp; exact hdom _ (by omega)) ?_
  refine stiw0 (w := w) (k := bvOff) (by rsimp) (by mem_simp; exact hdom _ (by omega)) ?_
  refine stiw0 (w := w) (k := bvOff + 1) (by rsimp) (by mem_simp; exact hdom _ (by omega)) ?_
  refine lea0 (w := w) (k := dOff) (by rsimp) ?_
  refine stw0 (w := w) (k := vCur) (by rsimp) (by mem_simp; exact hdom _ (by omega)) ?_
  refine lea0 (w := w) (k := (tselR side).off) (by rsimp) ?_
  refine stw0 (w := w) (k := vSel) (by rsimp) (by mem_simp; exact hdom _ (by omega)) ?_
  refine stiw0 (w := w) (k := vRem) (by rsimp) (by mem_simp; exact hdom _ (by omega)) ?_
  refine wp_done ⟨by rsimp; exact hrdi, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (mem_simp; done)
    | (mem_simp; rfl)
    | (mem_simp; rw [Int64.toUInt64_ofNat']; done)
    | keep_tac

end NativeVm.Code.P3
