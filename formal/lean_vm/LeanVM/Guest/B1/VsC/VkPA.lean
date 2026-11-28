/-
  LeanVM.Guest.B1.VsC.VkPA

  `verify_keccak`'s honest data, read (the archive's `VkCG`, `VkCH` on Hotwire's layers).
-/

module

public import LeanVM.Guest.B1.VsC.VkCChain
public import LeanVM.Guest.B1.VsC.KLayerA
public import LeanVM.Guest.B1.VsC.KLMain
public import LeanVM.Guest.B1.KeccakGkr.VkOut

/-!
# The honest data, read

* `eqLevels rs n`: an equality tree's levels, `eqKernel` of the first `t` coordinates for
  `t = 1 … n`, as `eqtree` stores them (`eqLevels_getD`).
* For a `VkData` `D` with `D.Ok`: `D.xs` split (`xs_reads`: the committed word, layer `s`'s words
  at `lcur s`, the openings' rounds, the word and the slices after them); the sponges after the
  layers and after each opening, empty (`L_ok`, `O_ok`, …).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.VerifySub.KL

@[expose] public section

/-- An equality tree's levels: `eqKernel` of the first `t` coordinates, `t = 1 … n`. -/
def eqLevels (rs : List E) (n : ℕ) : List E :=
  ((List.range n).map fun t ↦ eqKernel (rs.take (t + 1))).flatten

theorem eqLevels_succ (rs : List E) (n : ℕ) :
    eqLevels rs (n + 1) = eqLevels rs n ++ eqKernel (rs.take (n + 1)) := by
  simp [eqLevels, List.range_succ]

theorem eqLevels_length {rs : List E} : ∀ {n : ℕ}, n ≤ rs.length →
    (eqLevels rs n).length = 2 ^ (n + 1) - 2
  | 0, _ => rfl
  | n + 1, h => by
    rw [eqLevels_succ, List.length_append, eqLevels_length (by omega), eqKernel_length,
      List.length_take, Nat.min_eq_left h, pow_succ 2 (n + 1)]
    have : 2 ≤ 2 ^ (n + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- **An equality tree's levels**: level `t` from `2^t - 2`. -/
theorem eqLevels_getD {rs : List E} : ∀ {n : ℕ}, n ≤ rs.length → ∀ t, 1 ≤ t → t ≤ n →
    ∀ i < 2 ^ t, (eqLevels rs n).getD (2 ^ t - 2 + i) 0 = (eqKernel (rs.take t)).getD i 0
  | 0, _, t, h1, h2, _, _ => by omega
  | n + 1, h, t, h1, h2, i, hi => by
    rw [eqLevels_succ]
    have hl := eqLevels_length (rs := rs) (n := n) (by omega)
    rcases Nat.lt_or_ge t (n + 1) with ht | ht
    · have hlt : 2 ^ t - 2 + i < (eqLevels rs n).length := by
        have h2 : 2 ≤ 2 ^ t := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) h1
        rw [hl]
        have : 2 ^ (t + 1) ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at this
        omega
      rw [List.getD_append _ _ _ _ hlt]
      exact eqLevels_getD (by omega) t h1 (by omega) i hi
    · obtain rfl : t = n + 1 := by omega
      have h2 : 2 ≤ 2 ^ (n + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [List.getD_append_right _ _ _ _ (by omega), hl]
      congr 1
      omega

/-- `ptr b · g^j` is `ptr (b + j)`. -/
theorem ptr_mul_gen (b j : ℕ) : VsC.ptrAtV b * gen ^ j = VsC.ptrAtV (b + j) := by
  rw [gen_pow_eq_ofK, ← ofK_mul]
  unfold Parameters.addressOfIndex
  rw [← pow_add]

theorem readsAt_mid {rd : Reader} {p : E} {A B C : List E} (h : ReadsAt rd p (A ++ B ++ C)) :
    ReadsAt rd (p * gen ^ A.length) B :=
  (readsAt_append.1 (readsAt_append.1 h).1).2

theorem flatMap_range_split (f : ℕ → List E) {s n : ℕ} (hs : s < n) :
    (List.range n).flatMap f =
      (List.range s).flatMap f ++ f s ++ (List.range' (s + 1) (n - s - 1)).flatMap f := by
  rw [List.range_eq_range', List.range_eq_range',
    show n = s + (1 + (n - s - 1)) by omega, ← List.range'_append, ← List.range'_append]
  simp [List.flatMap_append]

theorem flatMap_range_length (f : ℕ → List E) {c : ℕ} : ∀ {s : ℕ}, (∀ k < s, (f k).length = c) →
    ((List.range s).flatMap f).length = s * c
  | 0, _ => by simp
  | s + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.length_append, flatMap_range_length f
      (fun k hk ↦ h k (by omega))]
    simp [h s (by omega)]
    ring

theorem flatMap_eq_range {α : Type} [Inhabited α] (l : List α) (f : α → List E) :
    l.flatMap f = (List.range l.length).flatMap fun k ↦ f (l.getD k default) := by
  conv_lhs => rw [show l = (List.range l.length).map (fun k ↦ l.getD k default) from
    List.ext_getElem (by simp) (fun k h1 h2 ↦ by simp [List.getElem?_eq_getElem h1])]
  rw [List.flatMap_map]

/-- A word of a run read at its index. -/
theorem readsAt_getD {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ}
    (hk : k < xs.length) : LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

namespace VkData

variable {D : VkData}

theorem layer_xs (s : ℕ) : (D.layer s).xs = ltXs (D.T s) := rfl

theorem ltXs_length (h : D.Ok) {s : ℕ} (hs : s < 12) :
    (ltXs (D.T s)).length = 48 + 2 * (D.τ - 3) + 36 := by
  rw [← layer_xs]
  obtain ⟨hpl, -, hpm, hlm, -, -⟩ := D.layer_facts h hs
  rw [KL.xs_length hpl hpm hlm, D.layer_y h (by omega)]
  omega

/-- Where layer `s` reads, past the cursor. -/
def lcur (D : VkData) (s : ℕ) : ℕ := 1 + s * (48 + 2 * (D.τ - 3) + 36)

theorem xs_eq (h : D.Ok) : D.xs = [D.committed] ++ (List.range 12).flatMap (fun s ↦ ltXs (D.T s)) ++
    (D.mO.flatMap (fun m ↦ [m.1, m.2]) ++ [D.word] ++ D.mI.flatMap (fun m ↦ [m.1, m.2]) ++
      D.mS.flatMap (fun m ↦ [m.1, m.2]) ++ D.slices) := by
  rw [xs, flatMap_eq_range D.Ts ltXs, ok_Ts h]
  simp only [List.append_assoc]
  rfl

theorem xs_len (h : D.Ok) : D.xs.length = D.lcur 12 + 97 := by
  obtain ⟨-, -, -, -, -, -, hmO, hmI, hmS, hsl, -, -⟩ := id h
  rw [xs_eq h]
  simp only [List.length_append, List.length_singleton, length_flatMap_pairs, hmO, hmI, hmS, hsl,
    flatMap_range_length _ (fun k hk ↦ ltXs_length h hk), lcur]

/-- **The stream, split.** -/
theorem xs_reads (h : D.Ok) {rd : Reader} {curE : ℕ} (hr : ReadsAt rd (VsC.ptrAtV curE) D.xs) :
    LoadHolds rd (VsC.ptrAtV curE) 0 D.committed ∧
      (∀ s < 12, ReadsAt rd (VsC.ptrAtV (curE + D.lcur s)) (ltXs (D.T s))) ∧
      ReadsAt rd (VsC.ptrAtV (curE + D.lcur 12)) (D.mO.flatMap fun m ↦ [m.1, m.2]) ∧
      LoadHolds rd (VsC.ptrAtV (curE + D.lcur 12 + 12)) 0 D.word ∧
      ReadsAt rd (VsC.ptrAtV (curE + D.lcur 12 + 13)) (D.mI.flatMap fun m ↦ [m.1, m.2]) ∧
      ReadsAt rd (VsC.ptrAtV (curE + D.lcur 12 + 21)) (D.mS.flatMap fun m ↦ [m.1, m.2]) ∧
      ReadsAt rd (VsC.ptrAtV (curE + D.lcur 12 + 33)) D.slices := by
  obtain ⟨-, -, -, -, -, -, hmO, hmI, hmS, -, -, -⟩ := id h
  have hc : ∀ k < 12, (ltXs (D.T k)).length = 48 + 2 * (D.τ - 3) + 36 :=
    fun k hk ↦ ltXs_length h hk
  rw [xs_eq h] at hr
  refine ⟨?_, fun s hs ↦ ?_, ?_⟩
  · have := (readsAt_append.1 (readsAt_append.1 hr).1).1 0 (by simp)
    simpa using this
  · rw [flatMap_range_split _ hs] at hr
    have := readsAt_mid (A := [D.committed] ++ (List.range s).flatMap fun s ↦ ltXs (D.T s))
      (by simpa only [List.append_assoc] using hr)
    rw [ptr_mul_gen, List.length_append, flatMap_range_length _ (fun k hk ↦ hc k (by omega))] at this
    simpa [lcur, Nat.add_assoc, Nat.add_comm] using this
  · have h1 := (readsAt_append.1 hr).2
    rw [ptr_mul_gen, List.length_append, flatMap_range_length _ hc] at h1
    simp only [List.length_singleton] at h1
    rw [show curE + (1 + 12 * (48 + 2 * (D.τ - 3) + 36)) = curE + D.lcur 12 by simp [lcur]]
      at h1
    simp only [readsAt_append, length_flatMap_pairs, hmO, hmI, List.length_append,
      List.length_singleton, ptr_mul_gen] at h1
    obtain ⟨⟨⟨⟨r1, r2⟩, r3⟩, r4⟩, r5⟩ := h1
    refine ⟨r1, by simpa using r2 0 (by simp), by simpa using r3, ?_, ?_⟩
    · simpa [Nat.add_assoc] using r4
    · simpa [Nat.add_assoc, hmS] using r5

theorem chain_zero : D.chain 0 = (D.c0, D.S0) := rfl

theorem layer_zero_c : (D.layer 0).c = D.c0 := rfl

theorem rl_length : D.rl.length = 5 := squeezeN_fst_length _ _

theorem seg_length : D.seg.length = 1 := squeezeN_fst_length _ _

theorem inst4 (h : D.Ok) : (D.inst.take 4).length = 4 := by
  have := h.2.2.1; have := h.1
  simp [inst]; omega

theorem inst_length (h : D.Ok) : D.inst.length = D.τ := by
  have := h.2.2.1
  simp [inst]; omega

theorem c0_mu (h : D.Ok) : D.c0.mu.length = 16 := by
  simp only [c0, vkFirst, eqKernel_length, inst4 h]; rfl

theorem c0_mu_eq (h : D.Ok) : D.c0.mu = eqKernel (D.chis.take 4) := by
  have := h.1
  simp only [c0, vkFirst, inst, List.take_take, show min 4 D.τ = 4 by omega]

theorem c0_point_eq : D.c0.point = D.inst.drop 4 ++ D.seg := rfl

theorem c0_point_seg (h : D.Ok) : D.c0.point.getD (D.τ - 4) 0 = D.seg.getD 0 0 := by
  have hl := inst_length h
  rw [c0_point_eq, List.getD_append_right _ _ _ _ (by simp; omega)]
  simp [hl]

theorem locPt_length (h : D.Ok) {s : ℕ} (hs : s < 12) :
    ((D.layer s).locPt (firstOf s)).length = 11 := by
  obtain ⟨-, -, -, hlm, -, -⟩ := D.layer_facts h hs
  rw [LayerData.locPt, LayerData.loc, layerLocal, localRunF_length, hlm]

/-- A squeezed sponge: nothing waiting, five capacity cells. -/
theorem sq_ok (t : Fs) : t.squeeze.2 = ⟨t.squeeze.2.cap, []⟩ ∧ t.squeeze.2.cap.length = 5 :=
  ⟨squeeze_snd_eq t, by simp [Fs.squeeze, capOf]⟩

theorem plainRun_sq : ∀ (ms : List (E × E)) (v : E) (s : Fs), ms ≠ [] →
    ∃ t : Fs, (plainRun ms v s).2.2 = t.squeeze.2
  | [], _, _, h => absurd rfl h
  | [(c0, c2)], _, s, _ => ⟨(s.absorb c0 dsObserve).absorb c2 dsObserve, by simp only [plainRun]⟩
  | m :: m' :: ms, v, s, _ => by
    obtain ⟨c0, c2⟩ := m
    rw [plainRun_cons_snd]
    exact plainRun_sq (m' :: ms) _ _ (by simp)

theorem plainRun_ok (ms : List (E × E)) (v : E) (s : Fs) (h : ms ≠ []) :
    (plainRun ms v s).2.2 = ⟨(plainRun ms v s).2.2.cap, []⟩ ∧
      (plainRun ms v s).2.2.cap.length = 5 := by
  obtain ⟨t, ht⟩ := plainRun_sq ms v s h
  rw [ht]; exact sq_ok t

theorem L_eq (h : D.Ok) : D.L = D.chain 12 := by
  simp only [chain, L, keccakDepth]
  rw [List.take_of_length_le (by simp), List.take_of_length_le (by rw [ok_Ts h])]

theorem L_ok (h : D.Ok) : D.L.2 = ⟨D.L.2.cap, []⟩ ∧ D.L.2.cap.length = 5 := by
  rw [L_eq h, D.layer_succ h (by norm_num : 11 < 12)]
  exact sq_ok _

theorem O_ok (h : D.Ok) : D.O.2.2 = ⟨D.O.2.2.cap, []⟩ ∧ D.O.2.2.cap.length = 5 :=
  plainRun_ok _ _ _ (by rw [← List.length_pos_iff_ne_nil, h.2.2.2.2.2.2.1]; norm_num)

theorem I_ok (h : D.Ok) : D.I.2.2 = ⟨D.I.2.2.cap, []⟩ ∧ D.I.2.2.cap.length = 5 :=
  plainRun_ok _ _ _ (by rw [← List.length_pos_iff_ne_nil, h.2.2.2.2.2.2.2.1]; norm_num)

theorem S_ok (h : D.Ok) : D.S.2.2 = ⟨D.S.2.2.cap, []⟩ ∧ D.S.2.2.cap.length = 5 :=
  plainRun_ok _ _ _ (by rw [← List.length_pos_iff_ne_nil, h.2.2.2.2.2.2.2.2.1]; norm_num)

theorem O_run (h : D.Ok) (w : E) : plainRun D.mO D.committed (plainStart 0 D.L.2.cap w) = D.O := by
  simp only [plainStart, show ¬ ((0 : ℕ) = 1) by decide, ↓reduceIte, O]
  rw [← (L_ok h).1]

theorem I_run (h : D.Ok) : plainRun D.mI D.L.1.value (plainStart 1 D.O.2.2.cap D.word) = D.I := by
  simp only [plainStart, ↓reduceIte, I]
  congr 1
  conv_rhs => rw [(O_ok h).1]
  simp [Fs.absorb, rateScalars]

theorem S_run (h : D.Ok) (w : E) : plainRun D.mS D.I.2.1 (plainStart 0 D.I.2.2.cap w) = D.S := by
  simp only [plainStart, show ¬ ((0 : ℕ) = 1) by decide, ↓reduceIte, S]
  rw [← (I_ok h).1]

theorem inst_getD (h : D.Ok) {i : ℕ} (hi : i < D.τ) : D.inst.getD i 0 = D.chis.getD i 0 := by
  have := h.2.2.1
  simp [inst, List.getD_eq_getElem?_getD, hi]

theorem O1_length (h : D.Ok) : D.O.1.length = 6 := by
  rw [O, plainRun_length, h.2.2.2.2.2.2.1]

theorem I1_length (h : D.Ok) : D.I.1.length = 4 := by
  rw [I, plainRun_length, h.2.2.2.2.2.2.2.1]

theorem S1_length (h : D.Ok) : D.S.1.length = 6 := by
  rw [S, plainRun_length, h.2.2.2.2.2.2.2.2.1]

theorem L_point (h : D.Ok) : D.L.1.point.length = D.τ - 3 := by
  rw [L_eq h]; exact D.chain_point h le_rfl

theorem op_eq : D.op = (D.inst.take 4 ++ D.inst.drop 4) ++ D.O.1 := rfl

theorem op_length (h : D.Ok) : D.op.length = D.τ + 6 := by
  rw [op_eq, List.take_append_drop, List.length_append, inst_length h, O1_length h]

theorem point_length (h : D.Ok) : D.point.length = D.τ + 6 := by
  have := h.1
  simp only [point, List.length_append, I1_length h, List.length_take, L_point h, S1_length h]
  omega

theorem op_getD (h : D.Ok) {i : ℕ} (hi : i < D.τ) : D.op.getD i 0 = D.chis.getD i 0 := by
  rw [op_eq, List.take_append_drop, List.getD_append _ _ _ _ (by rw [inst_length h]; exact hi),
    inst_getD h hi]

theorem c0_point_length (h : D.Ok) : D.c0.point.length = D.τ - 3 := c0_point h

theorem c0_point_getD (h : D.Ok) {j : ℕ} (hj : j < D.τ - 4) :
    D.c0.point.getD j 0 = D.chis.getD (4 + j) 0 := by
  have hl := inst_length h
  rw [c0_point_eq, List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
    List.getElem?_drop, ← List.getD_eq_getElem?_getD, inst_getD h (by omega)]

/-! ## The callees' honest words -/

variable (D)

/-- The cursor after the layers. -/
def cL (curE : ℕ) : E := VsC.ptrAtV (curE + D.lcur 12)

/-- The committed outputs' rounds' arguments and returns. -/
def oArgs (curE zvE tbE : ℕ) : List E :=
  D.L.2.cap ++ [0, 0, D.cL curE, D.committed, VsC.ptrAtV zvE * gen ^ D.τ, VsC.ptrAtV tbE]
def oRets (curE : ℕ) : List E := D.O.2.2.cap ++ [D.cL curE * gen ^ (2 * 6), D.O.2.1]

/-- The inputs' rounds' arguments and returns. -/
def iArgs (curE zvE tbE : ℕ) : List E :=
  D.O.2.2.cap ++ [(Keccak.scalarCells D.word dsObserve).1, (Keccak.scalarCells D.word dsObserve).2,
    D.cL curE * gen ^ (2 * 6) * gen, D.L.1.value, VsC.ptrAtV zvE * gen ^ 39, VsC.ptrAtV tbE]
def iRets (curE : ℕ) : List E := D.I.2.2.cap ++ [D.cL curE * gen ^ (2 * 6) * gen * gen ^ (2 * 4), D.I.2.1]

/-- The inputs' opening's rounds' arguments and returns. -/
def sArgs (curE zvE tbE : ℕ) : List E :=
  D.I.2.2.cap ++ [0, 0, D.cL curE * gen ^ (2 * 6) * gen * gen ^ (2 * 4), D.I.2.1,
    VsC.ptrAtV zvE * gen ^ 39 * gen ^ D.τ, VsC.ptrAtV tbE]
def sRets (curE : ℕ) : List E :=
  D.S.2.2.cap ++ [D.cL curE * gen ^ (2 * 6) * gen * gen ^ (2 * 4) * gen ^ (2 * 6), D.S.2.1]

/-- The rate cells layer `s` starts with: the committed word's for the first. -/
def cells (s : ℕ) : E × E := if s = 0 then Keccak.scalarCells D.committed dsObserve else (0, 0)

variable {D}

theorem cL_eq (curE : ℕ) : D.cL curE = VsC.ptrAtV curE * gen ^ D.lcur 12 := (ptr_mul_gen _ _).symm

end VkData

end
end LeanVM.Guest.B1.VerifySub
