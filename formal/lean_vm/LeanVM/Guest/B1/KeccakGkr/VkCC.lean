/-
  LeanVM.Guest.B1.KeccakGkr.VkCC

  `verify_keccak`'s steps, completely: the claim's segment weights, the flips, the `ι` term.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCCK

/-!
# A step's core, completely

`stepCore_of_flips`: with the claim's point in memory and the flips holding with their values
(`flips0_complete`, `flipsL_complete`: a later claim's read from its record), the `ι` term is the
claim's and the core holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Fwd Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {w : ℕ → E} {σ : Val}

theorem mem_stepCoreF {s b : ℕ} {st : Stmt} (h : st ∈ flipsT s (b + 6)) : st ∈ stepCore s b :=
  List.mem_append_left _ (List.mem_append_right _ h)

/-- **A step's core, completely**, given its flips. -/
theorem stepCore_of_flips {s b : ℕ} (hs : s < 12) (hb : 18 ≤ b) (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ st ∈ stepCore s b, GoodS rd vkSt w σ st) (hk : stepKer s b)
    {τ : ℕ} (hτ1 : 9 ≤ τ) (h17 : σ (.n 18) = gen ^ (τ - 4)) {c : KeccakClaim} {pp : E}
    (hpp : LoadHolds rd (σ (.n 161)) (22 * s + 2) pp) (hpt : ReadsAt rd pp c.point)
    (hptL : c.point.length = τ - 3)
    (hF : ∀ i ∈ iotaUsed s, σ (.n (flipOf s (b + 6) i)) = c.weights.getD (2 ^ i - 1) 0)
    (HF : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (flipsT s (b + 6)) next kret) :
    σ (.n (stepT0 s b - 1)) = keccakIota τ s c ∧
      ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ (stepCore s b) next kret := by
  obtain ⟨k1, -, -, -, k7, k9⟩ := hk
  have gA : ∀ a, Stmt.atom a ∈ stepCore s b → Good rd vkSt w σ a := fun a h ↦ hg _ h
  have mA : ∀ st ∈ [Stmt.atom (.load (.n b) (.n 161) (22 * s + 2)),
      .atom (.mul (.n (b + 1)) (.n b) (.n 18))] ++ eqfLevel0T (.n (b + 1)) 0 (b + 2),
      st ∈ stepCore s b := fun st h ↦
    List.mem_append_left _ (List.mem_append_left _ h)
  have e0 : σ (.n b) = pp :=
    load_val (gA _ (mA _ (by simp))) (not_mem_of_noneIn k1 _ (by simp)) hpp
  have m1 := mulG (by omega) (by omega)
    (gA (.mul (.n (b + 1)) (.n b) (.n 18)) (mA _ (by simp)))
  -- the segment weights
  have hr : LoadHolds rd (σ (.n (b + 1))) 0 (c.point.getD (τ - 4) 0) := by
    rw [m1, e0, h17, loadHolds_mul_gen_pow, List.getD_eq_getElem _ _ (by omega)]
    exact hpt _ (by omega)
  have e2 : σ (.n (b + 2)) = c.point.getD (τ - 4) 0 :=
    load_val (gA _ (mA _ (by simp [eqfLevel0T]))) (not_mem_of_noneIn k1 _ (by simp)) hr
  have c3 : σ (.n (b + 3)) = word 1 0 :=
    gA (.const (.n (b + 3)) (word 1 0)) (mA _ (by simp [eqfLevel0T]))
  have a4 : σ (.n (b + 4)) = σ (.n (b + 3)) + σ (.n (b + 2)) :=
    gA (.add (.n (b + 4)) (.n (b + 3)) (.n (b + 2))) (mA _ (by simp [eqfLevel0T]))
  have p5 : σ (.n (b + 5)) = σ (.n (b + 2)) :=
    gA (.copy (.n (b + 5)) (.n (b + 2))) (mA _ (by simp [eqfLevel0T]))
  have HA : ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ
      ([Stmt.atom (.load (.n b) (.n 161) (22 * s + 2)), .atom (.mul (.n (b + 1)) (.n b) (.n 18))] ++
        eqfLevel0T (.n (b + 1)) 0 (b + 2)) next kret := by
    intro next kret hn
    simp only [eqfLevel0T, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds,
      Atom.Holds]
    exact ⟨by rw [e0]; exact hpp, m1, by rw [e2]; exact hr, c3, a4, p5, hn⟩
  obtain ⟨⟨g0, g1⟩, -⟩ := stepSeg_holds (C := C) (by omega) hptL hpt h17 hpp
    (HA (next := True) (kret := fun _ ↦ True) trivial)
  -- the `ι` term
  have HI : ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ
      (iotaSegT s (b + 6) (b + 6 + flipSz s * (iotaUsed s).length) (b + 4) (b + 5)) next kret :=
    fun hn ↦ block_holds k7 hσ (fun st h ↦ hg st (List.mem_append_right _ h))
      (fun a ha ↦ by rw [k9] at ha; simp at ha) hn
  obtain ⟨hio, -⟩ := iotaSegT_holds (F := fun i ↦ c.weights.getD (2 ^ i - 1) 0) hs hF g0 g1
    (HI (next := True) (kret := fun _ ↦ True) trivial)
  rw [← keccakIota_eq hs (by omega) hptL] at hio
  refine ⟨hio, fun {next kret} hn ↦ ?_⟩
  rw [stepCore, holdsList_append, holdsList_append]
  exact HA (HF (HI hn))

/-- A load of a block is residual. -/
theorem load_mem_resid {B : List Stmt} {d p : V} {off : ℕ} (h : Stmt.atom (.load d p off) ∈ B) :
    Atom.load d p off ∈ resid (atomsL B) :=
  List.mem_filter.mpr ⟨mem_atomsL.mpr h, by simp [needsSide, inkB]⟩

/-- **The first claim's flips, completely.** -/
theorem flips0_complete {b : ℕ} (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ st ∈ stepCore 0 b, GoodS rd vkSt w σ st) (hk : stepKer 0 b) {L0 : E}
    (hL0 : LoadHolds rd (σ (.n 234)) 30 L0) {c : KeccakClaim}
    (hw0 : ∀ z < 64, c.weights.getD z 0 = L0 * gen ^ z) :
    (∀ i ∈ iotaUsed 0, σ (.n (flipOf 0 (b + 6) i)) = c.weights.getD (2 ^ i - 1) 0) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ (flipsT 0 (b + 6)) next kret := by
  obtain ⟨-, k3, k5, k6, -⟩ := hk
  have HF : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (flipsT 0 (b + 6)) next kret :=
    fun hn ↦ loads_complete k3 hσ (fun st h ↦ hg st (mem_stepCoreF h)) k5 k6
      (fun q hq off h1 h2 ↦ by
        simp only [flipPs, ↓reduceIte, List.mem_singleton] at hq
        subst hq
        obtain rfl : off = 30 := by simp only at h1 h2; omega
        exact ⟨_, hL0⟩) hn
  obtain ⟨hfl, -⟩ := flipsT_holds0 (C := C) (fun v hv ↦ loadHolds_unique hv hL0)
    (HF (next := True) (kret := fun _ ↦ True) trivial)
  refine ⟨fun i hi ↦ ?_, HF⟩
  have hi7 := List.mem_range.1 (List.mem_filter.1 hi).1
  have hz : 2 ^ i - 1 < 64 := by
    have : 2 ^ i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hfl i hi, hw0 _ hz]

/-- **A later claim's flips, completely**: read from the claim's record (`KC_FLIPS`). -/
theorem flipsL_complete {s b : ℕ} (hs1 : 1 ≤ s) (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ st ∈ stepCore s b, GoodS rd vkSt w σ st) (hk : stepKer s b) {fl : E}
    {c : KeccakClaim} (hfl : LoadHolds rd (σ (.n 161)) (22 * s + 5) fl)
    (hws : ReadsAt rd fl (flipsOf c.weights)) :
    (∀ i ∈ iotaUsed s, σ (.n (flipOf s (b + 6) i)) = c.weights.getD (2 ^ i - 1) 0) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ (flipsT s (b + 6)) next kret := by
  obtain ⟨-, k3, k5, k6, -⟩ := hk
  have hs0 : s ≠ 0 := by omega
  -- the pointer each flip loads
  have hptr : ∀ j < (iotaUsed s).length, σ (.n (b + 6 + 2 * j)) = fl := by
    intro j hj
    have m0 : Stmt.atom (.load (.n (b + 6 + 2 * j)) (.n 161) (22 * s + 5)) ∈ flipsT s (b + 6) := by
      simp only [flipsT, List.mem_flatten, List.mem_map, List.mem_range]
      exact ⟨_, ⟨j, hj, rfl⟩, by simp [flipT, hs0, flipSz]⟩
    exact load_val (w := w) (hg _ (mem_stepCoreF m0)) (not_mem_of_noneIn k6 _ (load_mem_resid m0))
      hfl
  have HF : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (flipsT s (b + 6)) next kret :=
    fun hn ↦ loads_complete k3 hσ (fun st h ↦ hg st (mem_stepCoreF h)) k5 k6
      (fun q hq off h1 h2 ↦ by
        simp only [flipPs, hs0, ↓reduceIte, List.mem_cons, List.mem_map, List.mem_range] at hq
        rcases hq with rfl | ⟨j, hj, rfl⟩
        · simp only at h1 h2 ⊢
          obtain rfl : off = 22 * s + 5 := by omega
          exact ⟨_, hfl⟩
        · simp only at h2 ⊢
          rw [hptr j hj]
          exact ⟨_, hws off (by simp [flipsOf]; omega)⟩) hn
  obtain ⟨hfl', -⟩ := flipsT_holdsL (C := C) hs0 hfl hws (HF (next := True) (kret := fun _ ↦ True) trivial)
  exact ⟨hfl', HF⟩

/-- **The first step's call, completely.** -/
theorem tail0_complete {T : ℕ} (hT : 162 ≤ T) {cap : List ℕ} {cur cb pn io : ℕ}
    (hg : ∀ st ∈ stepTailT 0 T cap cur cb pn io, GoodS rd vkSt w σ st) {τ : ℕ}
    (h17 : σ (.n 18) = gen ^ (τ - 4)) (hτ : 4 ≤ τ) :
    σ (.n (T + 1)) = σ (.n 5) * gen ∧ σ (.n (T + 3)) = gen ^ (τ - 3) ∧
      σ (.n (T + 5)) = σ (.n 161) * gen ^ (22 * 1) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ (stepTailT 0 T cap cur cb pn io) next kret := by
  have gA : ∀ a, Stmt.atom a ∈ stepTailT 0 T cap cur cb pn io → Good rd vkSt w σ a :=
    fun a h ↦ hg _ h
  have c0 : σ (.n T) = word 2 0 := gA (.const (.n T) (word 2 0)) (by simp [stepTailT])
  have m1 := mulG (by omega) (by omega) (gA (.mul (.n (T + 1)) (.n 5) (.n T)) (by simp [stepTailT]))
  have c2 : σ (.n (T + 2)) = word 2 0 := gA (.const (.n (T + 2)) (word 2 0)) (by simp [stepTailT])
  have m3 := mulG (by omega) (by omega)
    (gA (.mul (.n (T + 3)) (.n 18) (.n (T + 2))) (by simp [stepTailT]))
  have c4 : σ (.n (T + 4)) = word 4194304 0 :=
    gA (.const (.n (T + 4)) (word 4194304 0)) (by simp [stepTailT])
  have m5 := mulG (by omega) (by omega)
    (gA (.mul (.n (T + 5)) (.n 161) (.n (T + 4))) (by simp [stepTailT]))
  have e1 : σ (.n (T + 1)) = σ (.n 5) * gen := by rw [m1, c0, word_gen]
  have e3 : σ (.n (T + 3)) = gen ^ (τ - 3) := by
    rw [m3, h17, c2, word_gen, ← pow_succ]; congr 1; omega
  have e5 : σ (.n (T + 5)) = σ (.n 161) * gen ^ (22 * 1) := by rw [m5, c4, word_g22]
  refine ⟨e1, e3, e5, fun {next kret} hn ↦ ?_⟩
  simp only [stepTailT, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  exact ⟨c0, m1, c2, m3, c4, m5, trivial, hn⟩

/-- **A later step's call, completely.** -/
theorem tailL_complete {s T : ℕ} (hs1 : 1 ≤ s) (hT : 19 ≤ T) {cap : List ℕ}
    {cur cb pn io : ℕ} (hcb : cb < T) (hpn : pn < T)
    (hg : ∀ st ∈ stepTailT s T cap cur cb pn io, GoodS rd vkSt w σ st) {τ : ℕ}
    (h17 : σ (.n 18) = gen ^ (τ - 4)) (hτ : 4 ≤ τ) :
    σ (.n T) = 0 ∧ σ (.n (T + 1)) = 0 ∧ σ (.n (T + 3)) = gen ^ (τ - 3) ∧
      σ (.n (T + 5)) = σ (.n cb) * gen ^ 22 ∧ σ (.n (T + 7)) = σ (.n pn) * gen ^ 22 ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ (stepTailT s T cap cur cb pn io) next kret := by
  have hs0 : s ≠ 0 := by omega
  have gA : ∀ a, Stmt.atom a ∈ stepTailT s T cap cur cb pn io → Good rd vkSt w σ a :=
    fun a h ↦ hg _ h
  have c0 : σ (.n T) = word 0 0 := gA (.const (.n T) (word 0 0)) (by simp [stepTailT, hs0])
  have c1 : σ (.n (T + 1)) = word 0 0 :=
    gA (.const (.n (T + 1)) (word 0 0)) (by simp [stepTailT, hs0])
  have c2 : σ (.n (T + 2)) = word 2 0 :=
    gA (.const (.n (T + 2)) (word 2 0)) (by simp [stepTailT, hs0])
  have m3 := mulG (by omega) (by omega)
    (gA (.mul (.n (T + 3)) (.n 18) (.n (T + 2))) (by simp [stepTailT, hs0]))
  have c4 : σ (.n (T + 4)) = word 4194304 0 :=
    gA (.const (.n (T + 4)) (word 4194304 0)) (by simp [stepTailT, hs0])
  have m5 := mulG (by omega) (by omega)
    (gA (.mul (.n (T + 5)) (.n cb) (.n (T + 4))) (by simp [stepTailT, hs0]))
  have c6 : σ (.n (T + 6)) = word 4194304 0 :=
    gA (.const (.n (T + 6)) (word 4194304 0)) (by simp [stepTailT, hs0])
  have m7 := mulG (by omega) (by omega)
    (gA (.mul (.n (T + 7)) (.n pn) (.n (T + 6))) (by simp [stepTailT, hs0]))
  have e3 : σ (.n (T + 3)) = gen ^ (τ - 3) := by
    rw [m3, h17, c2, word_gen, ← pow_succ]; congr 1; omega
  refine ⟨by rw [c0, word_zero], by rw [c1, word_zero], e3, by rw [m5, c4, word_g22],
    by rw [m7, c6, word_g22], fun {next kret} hn ↦ ?_⟩
  simp only [stepTailT, hs0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  exact ⟨c0, c1, c2, m3, c4, m5, c6, m7, trivial, hn⟩

end
end LeanVM.Guest.B1.VerifySub
