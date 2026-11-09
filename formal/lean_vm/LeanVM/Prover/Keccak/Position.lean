/-
  LeanVM.Prover.Keccak.Position

  The executable position rounds make the moves of the specification's `hSumcheck 4 (FX …)`.
-/

module

public import LeanVM.Prover.Keccak.Pack

/-!
# The position rounds

`PosInv T P s w c pre st`: the four tables of `st` are the folded tables of `T_0, T_1, T_2`
(`Tk T P s c k`, the packs' states at the pack point `c`, `k` columns along) and of the position
weights (`Wt w`) over the `11` position bits, at the challenges `pre`.

* `posInv_start`: the tables from the last pack row;
* `posRound_eval`: the round polynomial evaluates as `FX T P s w c scale (pre ++ [x])`;
* `corr_pos`: **the rounds make the moves of `hSumcheck 4 (FX …)`**, ending in tables whose
  entries are `T_0, T_1, T_2` at the position point (`posInv_full`).
-/

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Protocol.EndToEnd.Complete (hSumcheck)

@[expose] public section

theorem affine_Tk (T : States) (P : ℕ) (s : E) (c : List E) (k : ℕ) : Affine (Tk T P s c k) :=
  affine_mle 1600 fun j ↦ Shat T P s (keccakAlong j k) c

theorem affine_Wt (w : List E) : Affine (Wt w) := affine_mle 1600 fun j ↦ w.getD j 0

/-- The position rounds' invariant at the challenges `pre`. -/
def PosInv (T : States) (P : ℕ) (s : E) (w c : List E) (pre : List E) (st : PosState) : Prop :=
  TabInv st.t0 (Tk T P s c 0) 11 pre ∧ TabInv st.t1 (Tk T P s c 1) 11 pre ∧
    TabInv st.t2 (Tk T P s c 2) 11 pre ∧ TabInv st.wt (Wt w) 11 pre

variable {T : States} {P : ℕ} {s : E} {w c : List E}

theorem polyEval_posCoeffs (κ wl wd l0 d0 l1 d1 l2 d2 x : E) :
    polyEval (posCoeffs κ wl wd l0 d0 l1 d1 l2 d2) x =
      (wl + x * wd) * (κ * (l0 + x * d0) + (κ + (l1 + x * d1)) * (l2 + x * d2)) := by
  simp only [posCoeffs, polyEval_cons', polyEval_nil']
  ring

theorem length_posRound (κ scale : E) (st : PosState) : (posRound κ scale st).length = 4 := by
  rw [posRound, length_scaleCoeffs]
  exact (polyEval_sumCoeffs 4 _ _ (fun _ _ ↦ rfl) 0).1

/-- **A position round's polynomial** evaluates as the specification's family. -/
theorem posRound_eval {pre : List E} {st : PosState} (h : PosInv T P s w c pre st)
    (hlt : pre.length < 11) (scale x : E) :
    polyEval (posRound (kappaAt s) scale st) x = FX T P s w c scale (pre ++ [x]) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hsz : st.t0.size / 2 = 2 ^ (11 - (pre.length + 1)) := by
    rw [h0.2.1, show 11 - pre.length = 11 - (pre.length + 1) + 1 by omega, pow_succ]; omega
  rw [posRound, polyEval_scaleCoeffs, (polyEval_sumCoeffs 4 _ _ (fun _ _ ↦ rfl) x).2, FX,
    List.length_append, List.length_singleton, hsz]
  refine congrArg (scale * ·) (Finset.sum_congr rfl fun u hu ↦ ?_)
  have hu' := Finset.mem_range.1 hu
  rw [polyEval_posCoeffs, phi, List.append_assoc, List.singleton_append,
    tabInv_split (affine_Wt w) h3 hlt hu', tabInv_split (affine_Tk T P s c 0) h0 hlt hu',
    tabInv_split (affine_Tk T P s c 1) h1 hlt hu', tabInv_split (affine_Tk T P s c 2) h2 hlt hu']

theorem posInv_fold {pre : List E} {st : PosState} (h : PosInv T P s w c pre st)
    (hlt : pre.length < 11) (r : E) : PosInv T P s w c (pre ++ [r]) (posFold st r) :=
  ⟨tabInv_fold (affine_Tk T P s c 0) h.1 hlt r, tabInv_fold (affine_Tk T P s c 1) h.2.1 hlt r,
    tabInv_fold (affine_Tk T P s c 2) h.2.2.1 hlt r, tabInv_fold (affine_Wt w) h.2.2.2 hlt r⟩

theorem tabInv_start (F : List E → E) (f : ℕ → E) (hF : ∀ u < 2048, F (bitsE u 11) = f u) :
    TabInv (Array.ofFn (n := 2048) fun u ↦ f u.val) F 11 [] := by
  refine ⟨by simp, by simp, fun u hu ↦ ?_⟩
  simp only [List.length_nil, Nat.sub_zero, List.nil_append] at hu ⊢
  rw [array_getD_ofFn_lt _ (by simpa using hu), hF u (by simpa using hu)]

/-- **The tables before the position rounds**, from the last pack row. -/
theorem posInv_start {r acc : List E} {stP : PackState} (hpk : PackInv T P s r acc stP)
    (hacc : acc.length = P + 1) : PosInv T P s w acc [] (posStart (stP.get 0) w.toArray) := by
  have hrow : ∀ j < 1600, stP.get 0 j = Shat T P s j acc := by
    intro j hj
    have := hpk.2.2 0 (by rw [hacc, Nat.sub_self]; norm_num) j hj
    rw [this, hacc, Nat.sub_self]
    simp [bitsE]
  have hT : ∀ k, ∀ u < 2048, Tk T P s acc k (bitsE u 11) =
      if u < 1600 then Shat T P s (keccakAlong u k) acc else 0 :=
    fun k u hu ↦ by rw [Tk]; exact sum1600_bitsE (show u < 2 ^ 11 from hu) _
  dsimp only [PosInv, posStart]
  refine ⟨tabInv_start _ (fun u ↦ if u < 1600 then stP.get 0 u else 0) fun u hu ↦ ?_,
    tabInv_start _ (fun u ↦ if u < 1600 then stP.get 0 (keccakAlong u 1) else 0) fun u hu ↦ ?_,
    tabInv_start _ (fun u ↦ if u < 1600 then stP.get 0 (keccakAlong u 2) else 0) fun u hu ↦ ?_,
    tabInv_start _ (fun u ↦ if u < 1600 then w.toArray.getD u 0 else 0) fun u hu ↦ ?_⟩
  · rw [hT 0 u hu]
    split_ifs with h
    · rw [keccakAlong_zero h, hrow u h]
    · rfl
  · rw [hT 1 u hu]
    split_ifs with h
    · rw [hrow _ (keccakAlong_lt 1 h)]
    · rfl
  · rw [hT 2 u hu]
    split_ifs with h
    · rw [hrow _ (keccakAlong_lt 2 h)]
    · rfl
  · rw [Wt, sum1600_bitsE (show u < 2 ^ 11 from hu)]
    split_ifs with h
    · rw [array_getD_toArray]
    · rfl

/-- **The position rounds make the moves of `hSumcheck 4 (FX …)`.** -/
theorem corr_pos {r acc : List E} {stP : PackState} (hpk : PackInv T P s r acc stP)
    (hacc : acc.length = P + 1) (scale : E) :
    Corr (fun a b ↦ a.1 = b.1 ∧ PosInv T P s w acc a.1 a.2 ∧
        b.2 = FX T P s w acc scale b.1 ∧ a.1.length = 11)
      (sumcheckBy (posRound (kappaAt s) scale) posFold (List.replicate keccakLocalBits none)
        (posStart (stP.get 0) w.toArray))
      (hSumcheck 4 (FX T P s w acc scale) (List.replicate keccakLocalBits none) []) := by
  refine Corr.mono (fun a b h ↦ ?_) _ _ (corr_sumcheckBy_lt 4 (by norm_num) (by norm_num)
    (FX T P s w acc scale) (posRound (kappaAt s) scale) posFold (PosInv T P s w acc) 11
    (fun pre st h hlt ↦ ⟨length_posRound _ _ _, fun x ↦ posRound_eval h hlt scale x⟩)
    (fun pre st r h hlt ↦ posInv_fold h hlt r) _ [] _ (posInv_start hpk hacc)
    (by simp [keccakLocalBits]))
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [List.nil_append] at h2 h3
  exact ⟨h1, h2, h3, by simpa [keccakLocalBits] using h4⟩

/-- The tables' entries after the eleven rounds. -/
theorem posInv_full {pre : List E} {st : PosState} (h : PosInv T P s w c pre st)
    (hl : pre.length = 11) :
    st.t0.getD 0 0 = Tk T P s c 0 pre ∧ st.t1.getD 0 0 = Tk T P s c 1 pre ∧
      st.t2.getD 0 0 = Tk T P s c 2 pre :=
  ⟨tabInv_full h.1 hl, tabInv_full h.2.1 hl, tabInv_full h.2.2.1 hl⟩

end
end LeanVM.Prover.KeccakGkr
