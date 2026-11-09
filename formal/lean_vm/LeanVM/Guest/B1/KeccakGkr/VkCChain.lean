/-
  LeanVM.Guest.B1.KeccakGkr.VkCChain

  `verify_keccak`'s twelve layers, honestly: each one's data, its checks, and how it starts from
  the previous one's end.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCHon

/-!
# The layers' chain

From `ChainOk`, layer `k`'s words have their lengths and its two checks hold (`chainOk_at`), and
the claim and sponge after layer `k` are its `layerClaim` and `layerBeta` (`chainEnd_succ`). For a
`VkData` with its run's facts: every claim's point has `τ - 3` coordinates (`chain_point`), the
sponge before layer `k` is `(layer k).s0` (`chain_s0`), and layer `k` has the facts
`layer_completeAtF` takes (`layer_facts`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

theorem chainOk_length {L : ℕ} : ∀ {steps : List ℕ} {c : KeccakClaim} {s : Fs} {Ts : List LT},
    ChainOk L steps c s Ts → Ts.length = steps.length
  | _ :: _, _, _, _ :: _, h => by simp [chainOk_length h.2.2.2.2.2]
  | [], _, _, [], _ => rfl
  | [], _, _, _ :: _, h => h.elim
  | _ :: _, _, _, [], h => h.elim

/-- **Layer `k` of a chain**: its lengths and its two checks, at the claim and the sponge before
it; and the claim and sponge after it. -/
theorem chainOk_at {L : ℕ} : ∀ {steps : List ℕ} {c : KeccakClaim} {s : Fs} {Ts : List LT},
    ChainOk L steps c s Ts → ∀ k < steps.length,
      let ck := (chainEnd (steps.take k) c s (Ts.take k)).1
      let sk := (chainEnd (steps.take k) c s (Ts.take k)).2
      let T := Ts.getD k default
      T.1.length = productBits ∧ T.2.1.length = ck.point.length ∧
        T.2.2.1.length = keccakLocalBits ∧
        projectedOf ck T.1 + keccakIota L (steps.getD k 0) ck * sumE ck.mu = ck.value ∧
        LayerFinal ck sk T.1 T.2.1 T.2.2.1 T.2.2.2 ∧
        chainEnd (steps.take (k + 1)) c s (Ts.take (k + 1)) =
          (layerClaim ck sk T.1 T.2.1 T.2.2.1 T.2.2.2, (layerBeta ck sk T.1 T.2.1 T.2.2.1 T.2.2.2).2)
  | a :: steps, c, s, T :: Ts, h, 0, _ => by
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
    exact ⟨h1, h2, h3, h4, h5, rfl⟩
  | a :: steps, c, s, T :: Ts, h, k + 1, hk => by
    have := chainOk_at h.2.2.2.2.2 k (by simpa using hk)
    simpa [chainEnd] using this
  | [], _, _, _, _, _, hk => absurd hk (by simp)
  | _ :: _, _, _, [], h, _, _ => h.elim

theorem chainOk_point {L : ℕ} : ∀ {steps : List ℕ} {c : KeccakClaim} {s : Fs} {Ts : List LT},
    ChainOk L steps c s Ts → ∀ k ≤ steps.length,
      (chainEnd (steps.take k) c s (Ts.take k)).1.point.length = c.point.length
  | _, _, _, _, _, 0, _ => by simp [chainEnd]
  | a :: steps, c, s, T :: Ts, h, k + 1, hk => by
    have ih := chainOk_point h.2.2.2.2.2 k (by simpa using hk)
    simp only [List.take_succ_cons, chainEnd]
    rw [ih]
    exact packRunF_chs_length _ _ _ _ _ h.2.1
  | [], _, _, _, _, k + 1, hk => absurd hk (by simp)
  | _ :: _, _, _, [], h, _ + 1, _ => h.elim

theorem squeeze_snd_eq (s : Fs) : s.squeeze.2 = ⟨s.squeeze.2.cap, []⟩ := by
  have hp : s.squeeze.2.pend = [] := rfl
  generalize s.squeeze.2 = t at hp ⊢
  cases t; simp_all

theorem squeezeN_snd_succ (n : ℕ) (s : Fs) :
    (s.squeezeN (n + 1)).2 = (s.squeeze.2.squeezeN n).2 := by
  simp only [Fs.squeezeN]

theorem squeezeN_ok (n : ℕ) : ∀ (s : Fs),
    (s.squeezeN (n + 1)).2 = ⟨(s.squeezeN (n + 1)).2.cap, []⟩ ∧
      (s.squeezeN (n + 1)).2.cap.length = 5 ∧ AllCanonical (s.squeezeN (n + 1)).2.cap := by
  induction n with
  | zero =>
    intro s
    rw [squeezeN_snd_succ]
    simp only [Fs.squeezeN]
    exact ⟨squeeze_snd_eq s, by simp [Fs.squeeze, capOf], squeeze_cap_canonical _⟩
  | succ n ih =>
    intro s
    rw [squeezeN_snd_succ]
    exact ih _

theorem squeezeN_fst_length : ∀ (n : ℕ) (s : Fs), (s.squeezeN n).1.length = n
  | 0, _ => rfl
  | n + 1, s => by
    show ((s.squeeze.1 :: (s.squeeze.2.squeezeN n).1)).length = n + 1
    rw [List.length_cons, squeezeN_fst_length n]

namespace VkData

variable {D : VkData}

theorem ok_Ts (h : D.Ok) : D.Ts.length = 12 := chainOk_length h.2.2.2.2.2.2.1

theorem chain_at (h : D.Ok) {k : ℕ} (hk : k < 12) :
    let T := D.T k
    T.1.length = productBits ∧ T.2.1.length = (D.chain k).1.point.length ∧
      T.2.2.1.length = keccakLocalBits ∧
      projectedOf (D.chain k).1 T.1 + keccakIota D.τ k (D.chain k).1 * sumE (D.chain k).1.mu =
        (D.chain k).1.value ∧
      LayerFinal (D.chain k).1 (D.chain k).2 T.1 T.2.1 T.2.2.1 T.2.2.2 ∧
      D.chain (k + 1) = (layerClaim (D.chain k).1 (D.chain k).2 T.1 T.2.1 T.2.2.1 T.2.2.2,
        (layerBeta (D.chain k).1 (D.chain k).2 T.1 T.2.1 T.2.2.1 T.2.2.2).2) := by
  have := chainOk_at h.2.2.2.2.2.2.1 k (by simpa [keccakDepth] using hk)
  have hg : (List.range keccakDepth).getD k 0 = k := by
    rw [List.getD_eq_getElem _ _ (by simpa [keccakDepth] using hk), List.getElem_range]
  rw [hg] at this
  exact this

theorem c0_point (h : D.Ok) : D.c0.point.length = D.τ - 3 := by
  simp only [c0, vkFirst, inst, seg, sq1, List.length_append, List.length_drop, List.length_take,
    squeezeN_fst_length]
  have h1 := h.1
  have h2 := h.2.2.1
  rw [keccakSegmentBits_eq]
  omega

/-- The specialization layer `k` runs: the first, or a later one. -/
def firstOf (k : ℕ) : ℕ := if k = 0 then 1 else 0

theorem chain_s0 (h : D.Ok) {k : ℕ} (hk : k < 12) :
    (D.chain k).2 = (D.layer k).s0 (firstOf k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hs := (squeezeN_ok 4 D.sq1.2).1
    simp only [chain, List.take_zero, chainEnd, LayerData.s0, layer, firstOf, ↓reduceIte,
      plainStart, S0]
    rw [show D.sq2 = D.sq1.2.squeezeN 5 from rfl, hs]
    simp [Fs.absorb, rateScalars]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨-, -, -, -, -, he⟩ := D.chain_at h (k := j) (by omega)
    have hne : j + 1 ≠ 0 := by omega
    simp only [LayerData.s0, layer, firstOf, hne, ↓reduceIte, plainStart]
    rw [he]
    simp only [layerBeta]
    exact squeeze_snd_eq _

theorem chain_point (h : D.Ok) {k : ℕ} (hk : k ≤ 12) : (D.chain k).1.point.length = D.τ - 3 := by
  have := chainOk_point h.2.2.2.2.2.2.1 k (by simpa [keccakDepth] using hk)
  rw [chain, this, c0_point h]

theorem layer_y (h : D.Ok) {k : ℕ} (hk : k ≤ 12) : (D.layer k).y = D.τ - 3 :=
  D.chain_point h hk

theorem layer_cap (h : D.Ok) {k : ℕ} (hk : k < 12) :
    (D.layer k).cap.length = 5 ∧ AllCanonical (D.layer k).cap := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hs := squeezeN_ok 4 D.sq1.2
    simp only [layer, chain, List.take_zero, chainEnd, S0]
    rw [show D.sq2 = D.sq1.2.squeezeN 5 from rfl, hs.1]
    simp only [Fs.absorb, rateScalars, List.length_nil, OfNat.zero_ne_ofNat, ↓reduceIte]
    exact ⟨hs.2.1, hs.2.2⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨-, -, -, -, -, he⟩ := D.chain_at h (k := j) (by omega)
    simp only [layer, he, layerBeta]
    exact ⟨by simp [Fs.squeeze, capOf], squeeze_cap_canonical _⟩

/-- **Layer `k`'s facts**: what `layer_completeAtF` takes of its data. -/
theorem layer_facts (h : D.Ok) {k : ℕ} (hk : k < 12) :
    (D.layer k).product.length = 47 ∧ (D.layer k).packMsgs.length = (D.layer k).y ∧
      (D.layer k).localMsgs.length = 11 ∧
      projectedOf (D.layer k).c (D.layer k).product +
        keccakIota D.τ k (D.layer k).c * sumE (D.layer k).c.mu = (D.layer k).c.value ∧
      LayerFinal (D.layer k).c ((D.layer k).s0 (firstOf k)) (D.layer k).product
        (D.layer k).packMsgs (D.layer k).localMsgs (D.layer k).t := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := D.chain_at h hk
  rw [← D.chain_s0 h hk]
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **The next layer starts where layer `k` ends.** -/
theorem layer_succ (h : D.Ok) {k : ℕ} (hk : k < 12) :
    D.chain (k + 1) = ((D.layer k).next (firstOf k), ((D.layer k).beta (firstOf k)).2) := by
  obtain ⟨-, -, -, -, -, he⟩ := D.chain_at h hk
  rw [he, D.chain_s0 h hk]
  rfl

end VkData

end
end LeanVM.Guest.B1.VerifySub
