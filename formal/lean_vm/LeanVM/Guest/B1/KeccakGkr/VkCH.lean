/-
  LeanVM.Guest.B1.KeccakGkr.VkCH

  `verify_keccak`'s honest data: where each part of the stream is, the openings' sponges, the
  claims' records.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCG

/-!
# The honest data, read

For a `VkData` `D` with `D.Ok`:

* `D.xs` split (`xs_reads`): the committed word, layer `s`'s words at `lcur s`, the openings'
  rounds, the word and the slices after them.
* The sponges: after the layers, after each opening, empty (`L_snd`, `O_snd`, …).
* `CL_ok`: claim `s`'s record and buffers (`CL`) hold what `ClaimLay.Ok` asks, wherever the
  layers' buffers are.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

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

namespace VkData

variable {D : VkData}

theorem layer_xs (s : ℕ) : (D.layer s).xs = ltXs (D.T s) := rfl

theorem ltXs_length (h : D.Ok) {s : ℕ} (hs : s < 12) :
    (ltXs (D.T s)).length = 48 + 2 * (D.τ - 3) + 36 := by
  rw [← layer_xs]
  obtain ⟨hpl, -, hpm, hlm, -, -⟩ := D.layer_facts h hs
  rw [LayerData.xs_length hpl hpm hlm, D.layer_y h (by omega)]

theorem xs_eq (h : D.Ok) : D.xs = [D.committed] ++ (List.range 12).flatMap (fun s ↦ ltXs (D.T s)) ++
    (D.mO.flatMap (fun m ↦ [m.1, m.2]) ++ [D.word] ++ D.mI.flatMap (fun m ↦ [m.1, m.2]) ++
      D.mS.flatMap (fun m ↦ [m.1, m.2]) ++ D.slices) := by
  rw [xs, flatMap_eq_range D.Ts ltXs, ok_Ts h]
  simp only [List.append_assoc]
  rfl

/-- **The stream, split.** -/
theorem xs_reads (h : D.Ok) {rd : Reader} {curE : ℕ} (hr : ReadsAt rd (ptr curE) D.xs) :
    LoadHolds rd (ptr curE) 0 D.committed ∧
      (∀ s < 12, ReadsAt rd (ptr (curE + D.lcur s)) (ltXs (D.T s))) ∧
      ReadsAt rd (ptr (curE + D.lcur 12)) (D.mO.flatMap fun m ↦ [m.1, m.2]) ∧
      LoadHolds rd (ptr (curE + D.lcur 12 + 12)) 0 D.word ∧
      ReadsAt rd (ptr (curE + D.lcur 12 + 13)) (D.mI.flatMap fun m ↦ [m.1, m.2]) ∧
      ReadsAt rd (ptr (curE + D.lcur 12 + 21)) (D.mS.flatMap fun m ↦ [m.1, m.2]) ∧
      ReadsAt rd (ptr (curE + D.lcur 12 + 33)) D.slices := by
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
    simp only [readsAt_append, flatMap_pairs_length, hmO, hmI, List.length_append,
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

theorem c0_mu (h : D.Ok) : D.c0.mu.length = 16 := by
  simp only [c0, vkFirst, eqKernel_length, inst4 h]; rfl

theorem locPt_length (h : D.Ok) {s : ℕ} (hs : s < 12) :
    ((D.layer s).locPt (firstOf s)).length = 11 := by
  obtain ⟨-, -, -, hlm, -, -⟩ := D.layer_facts h hs
  rw [LayerData.locPt, LayerData.loc, layerLocal, localRunF_length, hlm]

/-- **Claim `s`'s record and buffers hold what `ClaimLay.Ok` asks.** -/
theorem CL_ok (h : D.Ok) (B : ℕ) (ls : ℕ → ℕ) {s : ℕ} (hs : s ≤ 12) :
    (D.CL B ls s).Ok (firstOf s) (D.layer s).c (D.layer s).y := by
  rcases s with _ | k
  · have hmu := c0_mu h
    simp only [CL, ClaimLay.Ok, layer_zero_c, firstOf, ↓reduceIte, cw0]
    refine ⟨by simp [hmu], hmu, rfl, rfl, by simp [c0, vkFirst, sumE_eqKernel], rfl, rfl,
      fun i hi ↦ by simp [show 6 + i = i + 1 + 1 + 1 + 1 + 1 + 1 by omega], ?_, ?_⟩
    · simp [eqKernel_length, rl_length]
    · simp only [c0, vkFirst, firstWeights]
      refine List.map_congr_left fun j hj ↦ ?_
      have : j / 64 < 25 := by
        have := List.mem_range.1 hj; simp only [keccakBits] at this; omega
      simp [List.getD_eq_getElem?_getD, this]
  · have hk : k < 12 := by omega
    have hsucc := D.layer_succ h hk
    have hc : (D.layer (k + 1)).c = (D.layer k).next (firstOf k) := by
      show (D.chain (k + 1)).1 = _
      rw [hsucc]
    have hlocL := locPt_length h hk
    have hmu : ((D.layer k).next (firstOf k)).mu.length = 16 := keccakInstanceWeights_length _
    have hf : firstOf (k + 1) = 0 := rfl
    simp only [CL, ClaimLay.Ok, hf, hc, outWs, LayerData.outW]
    refine ⟨by simp [hmu], hmu, ?_, by simp, by simp, by simp, by simp,
      fun i hi ↦ by simp [show 6 + i = i + 1 + 1 + 1 + 1 + 1 + 1 by omega], lanesOut_length _ _, ?_⟩
    · simp only [LayerData.y, hc]
    · simp only [show (0 : ℕ) = 1 ↔ False by decide, ↓reduceIte]
      refine ⟨by simp, by simp, hlocL, ?_⟩
      simp only [LayerData.next, layerClaim]
      rw [laterWeights]
      exact congrArg keccakLinearTranspose (batch_factor _ hlocL _)

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

end VkData

end
end LeanVM.Guest.B1.VerifySub
