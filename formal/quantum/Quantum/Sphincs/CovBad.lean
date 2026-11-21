module

public import Quantum.Xmss.Events
public import Quantum.Sphincs.Keccak
public import Quantum.Sphincs.Coverage

@[expose] public section

/-!
# The FORS coverage event of leanSPHINCS

The coverage component of leanSPHINCS's event (plan v2, 3.4): a call-0 `H_msg` tail of a pair
`(R, M)` that is not exempted reaches an output `y` that is half covered by a static disclosure
set `S` (`HalfCov S (hiOf y, leavesOf y)`, `Quantum.Sphincs.Coverage`). In the security proof `S`
is the disclosure set of the presampled digest stream, so it does not change along a run.

The event is a target event of the hardwired register (`HwTargetBad` of `Quantum.Xmss.Events`)
with one bit of output: `covOut S x` says that the `out256` output of the rate `x` is half
covered, and every call-0 tail of a pair outside the exemption has the target `true`
(`covTgt`). The exemption `ex W m` (the honest pairs, hardwired at their signature) is a parameter
that grows with the hardwired cells (`ExMono`), so the targets shrink as cells are hardwired.

* `mem_covBad_iff`, `mem_covBad_of`: the event in terms of `out256` and `HalfCov`.
* `not_mem_covBad_empty`, `upClosed_slice_covBad`: the start is outside, every slice is upward
  closed.
* `card_covTargetBad_updateH_le`: a fresh `h` cell flips a database for at most
  `2^838 · coverMass S` values (one head-tail per fresh capacity, `2^832` rates per output and
  `2^6` outputs per half view), a fraction `2^16 · price S` (`covRate_eq`).
  `card_covTargetBad_updateK_le`, `card_covTargetBad_updateK'_le`: the capacity-scale counts of
  `preimageRateBound` for `k` and `k'`; `freshBound_slice_covBad` collects the three.
* Program ports: `card_flip_programH_covBad_le` (`2^838 · coverMass S` values of an `h` cell),
  `covBad_progUpdate` (hardwiring an `h` cell whose head-tail is exempted, or no call-0 tail,
  flips nothing), and the capacity-scale counts for `k`, `k'`.
* Read ports and memory updates that only grow the exemption flip nothing
  (`not_mem_covBad_readH`, `not_mem_covBad_memory`).

The generic lemmas of the first section are `Quantum.Sponge.Target`'s and `Quantum.Xmss.Events`'
with fiber bounds required only at the targets: here the target `true` has a small fiber, its
complement a large one.
-/

open Finset Quantum Quantum.Sponge Sphincs
open HashSig (HashOutput Message Randomizer)
open scoped ENNReal

namespace Quantum.Sphincs

/-! ## Target events with fiber bounds at the targets -/

section Generic

variable {X Z Y M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] {π : Equiv.Perm (X × Z)} {out : X → Y}

omit [Fintype Z] [DecidableEq X] in
open scoped Classical in
/-- `card_targetBad_updateH_le` with fiber bounds at the targets only: the flipping values of a
fresh `h` cell lie in one translate of the fiber of the target of the cell's head-tail. -/
theorem card_targetBad_updateH_le_of_tgt [DecidableEq Y] {tgt : List X → Option Y} {F : ℕ}
    (hF : ∀ t y, tgt t = some y → (Finset.univ.filter fun x ↦ out x = y).card ≤ F)
    {D : Dbs X Z} (hD : D ∉ TargetBad π out tgt) {z : Z} (hz : D.h z = none) :
    (Finset.univ.filter fun u : X ↦
      { D with h := Function.update D.h z (some u) } ∈ TargetBad π out tgt).card ≤ F := by
  obtain ⟨hG, hT⟩ := not_mem_targetBad_iff.1 hD
  have key : ∀ u, { D with h := Function.update D.h z (some u) } ∈ TargetBad π out tgt →
      ∃ s xi y, IsHeadTail π D s z xi ∧ tgt s = some y ∧ y = out (xi + u) := by
    rintro u (h | ⟨s, y, hs, hr⟩)
    · exact absurd ((good_update_h_iff _).2 hG) h
    rcases (reaches_updateH_iff hz).1 hr with hr | ⟨xi, hi, he⟩
    · exact absurd hr (hT s y hs)
    · exact ⟨s, xi, y, hi, hs, he⟩
  rcases Finset.eq_empty_or_nonempty (Finset.univ.filter fun u : X ↦
      { D with h := Function.update D.h z (some u) } ∈ TargetBad π out tgt) with he | ⟨u0, hu0⟩
  · simp [he]
  obtain ⟨s0, xi0, y0, hi0, hs0, -⟩ := key u0 (Finset.mem_filter.1 hu0).2
  have hsub : ∀ u ∈ (Finset.univ.filter fun u : X ↦
      { D with h := Function.update D.h z (some u) } ∈ TargetBad π out tgt),
      out (xi0 + u) = y0 := by
    intro u hu
    obtain ⟨s, xi, y, hi, hs, he⟩ := key u (Finset.mem_filter.1 hu).2
    obtain ⟨rfl, rfl⟩ := hG.isHeadTail_unique hi hi0
    obtain rfl := Option.some_injective _ (hs.symm.trans hs0)
    exact he.symm
  exact (Finset.card_le_card_of_injOn (xi0 + ·) (fun u hu ↦ by simp [hsub u hu])
    fun _ _ _ _ he ↦ add_left_cancel he).trans (hF s0 y0 hs0)

open scoped Classical in
/-- `freshBound_targetBad` with fiber bounds at the targets only. -/
theorem freshBound_targetBad_of_tgt [DecidableEq Y] {tgt : List X → Option Y} {G F : ℕ}
    (hπ : PermGood π G)
    (hF : ∀ t y, tgt t = some y → (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (T : ℕ) :
    FreshBound (TargetBad π out tgt) T (preimageRateBound (X := X) (Z := Z) T G F) where
  h D hD _ _ _ z hz := by
    refine le_trans ?_ (le_max_left _ _)
    gcongr
    exact_mod_cast card_targetBad_updateH_le_of_tgt hF hD hz
  k D hD _ hk hk' x hx := by
    refine le_trans ?_ ((le_max_left _ _).trans (le_max_right _ _))
    gcongr
    exact_mod_cast card_targetBad_updateK_le hπ hD hk.le hk'.le hx
  k' D hD hh hk hk' x hx := by
    refine le_trans ?_ ((le_max_right _ _).trans (le_max_right _ _))
    gcongr
    exact_mod_cast card_targetBad_updateK'_le hπ hD hh.le hk.le hk'.le hx

open scoped Classical in
/-- `freshBound_slice_hwTargetBad` with fiber bounds at the targets only. -/
theorem freshBound_slice_hwTargetBad_of_tgt [DecidableEq Y]
    {tgt : Hw X Z → M → List X → Option Y} {N : ℕ}
    [DecidablePred (· ∈ HwTargetBad π out tgt N)] {G F : ℕ} (hπ : PermGood π G)
    (hF : ∀ W m t y, tgt W m t = some y → (Finset.univ.filter fun x ↦ out x = y).card ≤ F)
    (T : ℕ) (W : Hw X Z) (m : M) :
    FreshBound (slice (HwTargetBad π out tgt N) W m) T
      (preimageRateBound (X := X) (Z := Z) (N + T) G F) := by
  have fb := freshBound_targetBad_of_tgt (tgt := tgt W m) hπ (hF W m) (N + T)
  by_cases hN : dbGrade W ≤ N
  swap
  · have hE : ∀ D, D ∉ slice (HwTargetBad π out tgt N) W m := fun D hD ↦ hN hD.1
    refine ⟨fun D _ _ _ _ z _ ↦ ?_, fun D _ _ _ _ x _ ↦ ?_, fun D _ _ _ _ x _ ↦ ?_⟩ <;>
    · rw [Finset.filter_false_of_mem fun u _ ↦ hE _]
      simp
  have hWh : W.1.size ≤ N := by simp only [dbGrade] at hN; omega
  have hWk : W.2.1.size ≤ N := by simp only [dbGrade] at hN; omega
  have hWk' : W.2.2.size ≤ N := by simp only [dbGrade] at hN; omega
  refine ⟨fun D hD hh hk hk' z hz ↦ ?_, fun D hD hh hk hk' x hx ↦ ?_, fun D hD hh hk hk' x hx ↦ ?_⟩
  · have hU : union W (D.h, D.k, D.k') ∉ TargetBad π out (tgt W m) := fun h ↦ hD ⟨hN, h⟩
    rcases hWz : W.1 z with _ | w
    · have hUz : (union W (D.h, D.k, D.k')).h z = none := by
        change (W.1 z).or (D.h z) = none
        rw [hWz, hz]
        rfl
      refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2
        (Finset.card_le_card fun u hu ↦ ?_)) _) (fb.h _ hU ((size_or_le W.1 D.h).trans_lt
          (by omega)) ((size_or_le W.2.1 D.k).trans_lt (by omega))
          ((size_or_le W.2.2 D.k').trans_lt (by omega)) z hUz)
      have h2 : union W (Function.update D.h z (some u), D.k, D.k') ∈
          TargetBad π out (tgt W m) := (Finset.mem_filter.1 hu).2.2
      rw [union_updateH W hWz] at h2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩
    · rw [Finset.filter_false_of_mem fun u _ hu ↦ hU ?_]
      · simp
      have h2 : union W (Function.update D.h z (some u), D.k, D.k') ∈
          TargetBad π out (tgt W m) := hu.2
      rwa [union_updateH_of_hw W hWz] at h2
  · have hU : union W (D.h, D.k, D.k') ∉ TargetBad π out (tgt W m) := fun h ↦ hD ⟨hN, h⟩
    rcases hWx : W.2.1 x with _ | w
    · have hUx : (union W (D.h, D.k, D.k')).k x = none := by
        change (W.2.1 x).or (D.k x) = none
        rw [hWx, hx]
        rfl
      refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2
        (Finset.card_le_card fun u hu ↦ ?_)) _) (fb.k _ hU ((size_or_le W.1 D.h).trans_lt
          (by omega)) ((size_or_le W.2.1 D.k).trans_lt (by omega))
          ((size_or_le W.2.2 D.k').trans_lt (by omega)) x hUx)
      have h2 : union W (D.h, Function.update D.k x (some u), D.k') ∈
          TargetBad π out (tgt W m) := (Finset.mem_filter.1 hu).2.2
      rw [union_updateK W hWx] at h2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩
    · rw [Finset.filter_false_of_mem fun u _ hu ↦ hU ?_]
      · simp
      have h2 : union W (D.h, Function.update D.k x (some u), D.k') ∈
          TargetBad π out (tgt W m) := hu.2
      rwa [union_updateK_of_hw W hWx] at h2
  · have hU : union W (D.h, D.k, D.k') ∉ TargetBad π out (tgt W m) := fun h ↦ hD ⟨hN, h⟩
    rcases hWx : W.2.2 x with _ | w
    · have hUx : (union W (D.h, D.k, D.k')).k' x = none := by
        change (W.2.2 x).or (D.k' x) = none
        rw [hWx, hx]
        rfl
      refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2
        (Finset.card_le_card fun u hu ↦ ?_)) _) (fb.k' _ hU ((size_or_le W.1 D.h).trans_lt
          (by omega)) ((size_or_le W.2.1 D.k).trans_lt (by omega))
          ((size_or_le W.2.2 D.k').trans_lt (by omega)) x hUx)
      have h2 : union W (D.h, D.k, Function.update D.k' x (some u)) ∈
          TargetBad π out (tgt W m) := (Finset.mem_filter.1 hu).2.2
      rw [union_updateK' W hWx] at h2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩
    · rw [Finset.filter_false_of_mem fun u _ hu ↦ hU ?_]
      · simp
      have h2 : union W (D.h, D.k, Function.update D.k' x (some u)) ∈
          TargetBad π out (tgt W m) := hu.2
      rwa [union_updateK'_of_hw W hWx] at h2

omit [DecidableEq X] in
open scoped Classical in
/-- `card_flip_programH_le` with fiber bounds at the targets only. -/
theorem card_flip_programH_le_of_tgt [DecidableEq Y] {tgt : Hw X Z → M → List X → Option Y}
    {N : ℕ} (hanti : TgtAnti tgt) {F : ℕ}
    (hF : ∀ W m t y, tgt W m t = some y → (Finset.univ.filter fun x ↦ out x = y).card ≤ F)
    {D : DbReg X Z} {W : Hw X Z} {m : M} (hs : (D, W, m) ∉ HwTargetBad π out tgt N) {z : Z}
    (hW : W.1 z = none) :
    (Finset.univ.filter fun v : X ↦
      ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∈
        HwTargetBad π out tgt N).card ≤ F := by
  by_cases hN : dbGrade W ≤ N
  swap
  · rw [Finset.filter_false_of_mem fun v _ hv ↦ hN ((hwLe_programH hW v).dbGrade_le.trans hv.1)]
    simp
  have hU0 : ({ union W D with h := Function.update (union W D).h z none } : Dbs X Z) ∉
      TargetBad π out (tgt W m) :=
    fun h ↦ hs ⟨hN, TargetBad.mono (extendsAll_eraseH _ z) h⟩
  refine le_trans (Finset.card_le_card fun v hv ↦ ?_)
    (card_targetBad_updateH_le_of_tgt (hF W m) hU0 (z := z) (by simp))
  have h2 : union (Function.update W.1 z (some v), W.2) (Function.update D.1 z none, D.2) ∈
      TargetBad π out (tgt (Function.update W.1 z (some v), W.2) m) := (Finset.mem_filter.1 hv).2.2
  rw [union_programH] at h2
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
    targetBad_mono (hanti _ _ _ (hwLe_programH hW v)) h2⟩

end Generic

open Quantum.Xmss (X Z out256 card_X)

/-! ## The coverage bit and the coverage targets -/

/-- **The coverage bit of a rate**: its `out256` output is half covered by `S`. -/
def covOut (S : Disclosures) (x : X) : Bool :=
  decide (HalfCov S (hiOf (out256 x), leavesOf (out256 x)))

open scoped Classical in
/-- The coverage target of a slot: `true` at call 0 of a pair outside the exemption `Ex`. -/
noncomputable def covSlot (Ex : Set (Randomizer × Message)) : Slot → Option Bool
  | .hmsg R msg c => if c = 0 ∧ (R, msg) ∉ Ex then some true else none
  | _ => none

/-- **The coverage target of a tail** for the key `pk`: `true` at a call-0 `H_msg` tail of a pair
outside the exemption `Ex`, none elsewhere. -/
noncomputable def covTgt (pk : PublicKey) (Ex : Set (Randomizer × Message)) (t : List X) :
    Option Bool :=
  (slotOf pk t).bind (covSlot Ex)

section Targets

variable {S : Disclosures} {pk : PublicKey} {Ex Ex' : Set (Randomizer × Message)}

theorem covSlot_eq_some_iff {s : Slot} {b : Bool} :
    covSlot Ex s = some b ↔ b = true ∧ ∃ R msg, s = .hmsg R msg 0 ∧ (R, msg) ∉ Ex := by
  cases s with
  | hmsg R msg c =>
    constructor
    · intro h
      simp only [covSlot] at h
      by_cases hc : c = 0 ∧ (R, msg) ∉ Ex
      · rw [ite_eq_left hc] at h
        exact ⟨(Option.some_injective _ h).symm, R, msg, by rw [hc.1], hc.2⟩
      · rw [ite_eq_right hc] at h
        cases h
    · rintro ⟨rfl, R', msg', he, hn⟩
      obtain ⟨rfl, rfl, rfl⟩ := Slot.hmsg.inj he
      simp only [covSlot]
      rw [ite_eq_left (show (0 : DigestCall) = 0 ∧ (R, msg) ∉ Ex from ⟨rfl, hn⟩)]
  | _ => simp [covSlot]

theorem covTgt_eq_some_iff {t : List X} {b : Bool} :
    covTgt pk Ex t = some b ↔
      b = true ∧ ∃ R msg, slotOf pk t = some (.hmsg R msg 0) ∧ (R, msg) ∉ Ex := by
  unfold covTgt
  cases slotOf pk t with
  | none => simp
  | some s =>
    rw [Option.bind_some, covSlot_eq_some_iff]
    simp only [Option.some.injEq]

/-- A call-0 tail of a pair outside the exemption has the target `true`. -/
theorem covTgt_of_not_mem {t : List X} {R : Randomizer} {msg : Message}
    (hs : slotOf pk t = some (.hmsg R msg 0)) (h : (R, msg) ∉ Ex) : covTgt pk Ex t = some true :=
  covTgt_eq_some_iff.2 ⟨rfl, R, msg, hs, h⟩

/-- **A tail without a target**: every pair whose call-0 slot the tail is lies in the exemption. -/
theorem covTgt_eq_none {t : List X}
    (h : ∀ R msg, slotOf pk t = some (.hmsg R msg 0) → (R, msg) ∈ Ex) : covTgt pk Ex t = none := by
  rcases ht : covTgt pk Ex t with _ | b
  · rfl
  obtain ⟨-, R, msg, hs, hn⟩ := covTgt_eq_some_iff.1 ht
  exact absurd (h R msg hs) hn

/-- More exempted pairs, fewer targets. -/
theorem covTgt_mono (h : Ex ⊆ Ex') {t : List X} {b : Bool} (ht : covTgt pk Ex' t = some b) :
    covTgt pk Ex t = some b := by
  obtain ⟨hb, R, msg, hs, hn⟩ := covTgt_eq_some_iff.1 ht
  exact covTgt_eq_some_iff.2 ⟨hb, R, msg, hs, fun hm ↦ hn (h hm)⟩

/-- A path reaches the bit `true` exactly when its `out256` output is half covered. -/
theorem reaches_covOut_iff {π : Equiv.Perm (X × Z)} {U : Dbs X Z} {t : List X} :
    Reaches π U (covOut S) t true ↔
      ∃ y, Reaches π U out256 t y ∧ HalfCov S (hiOf y, leavesOf y) := by
  constructor
  · rintro ⟨z, xi, w, hi, hw, hy⟩
    exact ⟨_, ⟨z, xi, w, hi, hw, rfl⟩, by simpa [covOut] using hy.symm⟩
  · rintro ⟨_, ⟨z, xi, w, hi, hw, rfl⟩, hc⟩
    exact ⟨z, xi, w, hi, hw, by simp [covOut, hc]⟩

/-- **The coverage databases**: bad, or a call-0 tail of a pair outside the exemption reaches a
half-covered output. -/
theorem mem_targetBad_covTgt_iff {π : Equiv.Perm (X × Z)} {U : Dbs X Z} :
    U ∈ TargetBad π (covOut S) (covTgt pk Ex) ↔ ¬ Good π U ∨
      ∃ R msg t y, slotOf pk t = some (.hmsg R msg 0) ∧ (R, msg) ∉ Ex ∧
        Reaches π U out256 t y ∧ HalfCov S (hiOf y, leavesOf y) := by
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨t, b, hb, hr⟩
    obtain ⟨rfl, R, msg, hs, hn⟩ := covTgt_eq_some_iff.1 hb
    obtain ⟨y, hr', hc⟩ := reaches_covOut_iff.1 hr
    exact ⟨R, msg, t, y, hs, hn, hr', hc⟩
  · rintro ⟨R, msg, t, y, hs, hn, hr, hc⟩
    exact ⟨t, true, covTgt_of_not_mem hs hn, reaches_covOut_iff.2 ⟨y, hr, hc⟩⟩

end Targets

/-! ## Fibers of the coverage bit -/

/-- **The rates whose output is half covered**: at most `2^838 · coverMass S`, `2^832` rates per
output and `2^6` outputs per half view. -/
theorem card_covOut_le (S : Disclosures) :
    #(univ.filter fun x : X ↦ covOut S x = true) ≤ 2 ^ 838 * coverMass S := by
  have e : (univ.filter fun x : X ↦ covOut S x = true) =
      univ.filter fun x : X ↦ HalfCov S (hiOf (out256 x), leavesOf (out256 x)) :=
    Finset.filter_congr fun x _ ↦ by simp [covOut]
  have h := card_halfCov_comp_le S (fun y : HashOutput ↦ (hiOf y, leavesOf y)) (2 ^ 6)
    fun v ↦ (card_fiber_hiLeaves v).le
  calc #(univ.filter fun x : X ↦ covOut S x = true)
      = #(univ.filter fun y : HashOutput ↦ HalfCov S (hiOf y, leavesOf y)) * 2 ^ 832 := by
        rw [e]
        exact card_filter_out256 (fun y ↦ HalfCov S (hiOf y, leavesOf y))
    _ ≤ 2 ^ 6 * coverMass S * 2 ^ 832 := Nat.mul_le_mul_right _ h
    _ = 2 ^ 838 * coverMass S := by rw [Nat.mul_right_comm, ← pow_add]

/-- The fiber bound at every coverage target. -/
theorem card_covOut_tgt_le (S : Disclosures) (pk : PublicKey) (Ex : Set (Randomizer × Message))
    (t : List X) (b : Bool) (h : covTgt pk Ex t = some b) :
    #(univ.filter fun x : X ↦ covOut S x = b) ≤ 2 ^ 838 * coverMass S := by
  obtain ⟨rfl, -⟩ := covTgt_eq_some_iff.1 h
  exact card_covOut_le S

/-- `2^a c / 2^(a + b) = 2^d (c / 2^(d + b))`, with the exponents left abstract. -/
theorem cast_two_pow_mul_div (c a b d n k : ℕ) (hn : a + b = n) (hk : d + b = k) :
    ((2 ^ a * c : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ) = 2 ^ d * ((c : ℝ) / 2 ^ k) := by
  subst hn hk
  push_cast
  rw [pow_add, pow_add, ← mul_div_assoc, mul_div_mul_left _ _ (pow_ne_zero d two_ne_zero),
    mul_div_mul_left _ _ (pow_ne_zero a two_ne_zero)]

/-- **The `h` rate of coverage**: `2^838 · coverMass S / |X| = 2^16 · price S`. -/
theorem covRate_eq (S : Disclosures) :
    ((2 ^ 838 * coverMass S : ℕ) : ℝ≥0∞) / Fintype.card X =
      ENNReal.ofReal ((2 ^ 16 * price S : ℚ) : ℝ) := by
  have e : ((2 ^ 16 * price S : ℚ) : ℝ) =
      ((2 ^ 838 * coverMass S : ℕ) : ℝ) / ((2 ^ 1088 : ℕ) : ℝ) := by
    rw [cast_two_pow_mul_div (coverMass S) 838 250 16 1088 266 rfl rfl, price, Rat.cast_mul,
      Rat.cast_div, Rat.cast_pow, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat]
  rw [e, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, card_X]

/-! ## Fresh cells -/

section Fresh

variable {S : Disclosures} {pk : PublicKey} {Ex : Set (Randomizer × Message)}
  {π : Equiv.Perm (X × Z)} {D : Dbs X Z}

open scoped Classical in
/-- **A fresh `h` cell**: at most `2^838 · coverMass S` values flip a database outside the
coverage databases into them, a fraction `2^16 · price S` (`covRate_eq`). -/
theorem card_covTargetBad_updateH_le (hD : D ∉ TargetBad π (covOut S) (covTgt pk Ex)) {z : Z}
    (hz : D.h z = none) :
    (Finset.univ.filter fun u : X ↦
      { D with h := Function.update D.h z (some u) } ∈ TargetBad π (covOut S) (covTgt pk Ex)).card ≤
        2 ^ 838 * coverMass S :=
  card_targetBad_updateH_le_of_tgt (card_covOut_tgt_le S pk Ex) hD hz

open scoped Classical in
/-- **A fresh `k` cell**: the capacity-scale count of `preimageRateBound`. -/
theorem card_covTargetBad_updateK_le {G t : ℕ} (hπ : PermGood π G)
    (hD : D ∉ TargetBad π (covOut S) (covTgt pk Ex)) (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t)
    {x : X} (hx : D.k x = none) :
    (Finset.univ.filter fun y : Z ↦
      { D with k := Function.update D.k x (some y) } ∈ TargetBad π (covOut S) (covTgt pk Ex)).card ≤
        (t + 1) * ((t + 1) * t + 2 * t) * G :=
  card_targetBad_updateK_le hπ hD hk hk' hx

open scoped Classical in
/-- **A fresh `k'` cell**: the capacity-scale count of `preimageRateBound`. -/
theorem card_covTargetBad_updateK'_le {G t : ℕ} (hπ : PermGood π G)
    (hD : D ∉ TargetBad π (covOut S) (covTgt pk Ex)) (hh : D.h.size ≤ t) (hk : D.k.size ≤ t)
    (hk' : D.k'.size ≤ t) {x' : X} (hx' : D.k' x' = none) :
    (Finset.univ.filter fun y : Z ↦
      { D with k' := Function.update D.k' x' (some y) } ∈
        TargetBad π (covOut S) (covTgt pk Ex)).card ≤
        (t + 1) + t * ((t + 1) * t + t + 1) * G + t * t * G + t :=
  card_targetBad_updateK'_le hπ hD hh hk hk' hx'

end Fresh

/-! ## The coverage event of the hardwired register -/

/-- Exemptions that grow with the hardwired cells. -/
def ExMono {M : Type} (ex : Hw X Z → M → Set (Randomizer × Message)) : Prop :=
  ∀ W W' m, HwLe W W' → ex W m ⊆ ex W' m

/-- **The coverage event of the hardwired register**: at most `N` hardwired cells per function, and
in the union of the hardwired and database cells a call-0 `H_msg` tail of a pair outside the
exemption `ex W m` reaches an output half covered by `S` (or the union is bad). -/
abbrev CovBad {M : Type} (π : Equiv.Perm (X × Z)) (pk : PublicKey) (S : Disclosures)
    (ex : Hw X Z → M → Set (Randomizer × Message)) (N : ℕ) : Set (HwReg X Z M) :=
  HwTargetBad π (covOut S) (fun W m ↦ covTgt pk (ex W m)) N

section Event

variable {M : Type} {π : Equiv.Perm (X × Z)} {pk : PublicKey} {S : Disclosures}
  {ex : Hw X Z → M → Set (Randomizer × Message)} {N : ℕ}

theorem tgtAnti_covTgt (hex : ExMono ex) : TgtAnti fun W m ↦ covTgt pk (ex W m) :=
  fun W W' m h _ _ ht ↦ covTgt_mono (hex W W' m h) ht

theorem mem_covBad_iff {D : DbReg X Z} {W : Hw X Z} {m : M} :
    (D, W, m) ∈ CovBad π pk S ex N ↔ dbGrade W ≤ N ∧ (¬ Good π (union W D) ∨
      ∃ R msg t y, slotOf pk t = some (.hmsg R msg 0) ∧ (R, msg) ∉ ex W m ∧
        Reaches π (union W D) out256 t y ∧ HalfCov S (hiOf y, leavesOf y)) :=
  and_congr Iff.rfl mem_targetBad_covTgt_iff

/-- **A covered call-0 tail is in the event**: a pair outside the exemption whose call-0 tail
reaches a half-covered output in the union, with few hardwired cells. -/
theorem mem_covBad_of {D : DbReg X Z} {W : Hw X Z} {m : M} (hN : dbGrade W ≤ N)
    {R : Randomizer} {msg : Message} {t : List X} {y : HashOutput}
    (hs : slotOf pk t = some (.hmsg R msg 0)) (hn : (R, msg) ∉ ex W m)
    (hr : Reaches π (union W D) out256 t y) (hc : HalfCov S (hiOf y, leavesOf y)) :
    (D, W, m) ∈ CovBad π pk S ex N :=
  mem_covBad_iff.2 ⟨hN, .inr ⟨R, msg, t, y, hs, hn, hr, hc⟩⟩

/-- **The start is outside the event**: no database and no hardwired cell. -/
theorem not_mem_covBad_empty (m : M) :
    ((Database.empty, Database.empty, Database.empty), (Database.empty, Database.empty,
      Database.empty), m) ∉ CovBad π pk S ex N :=
  empty_not_mem_hwTargetBad m

/-- **Every slice of the event is upward closed.** -/
theorem upClosed_slice_covBad (W : Hw X Z) (m : M) : UpClosed (slice (CovBad π pk S ex N) W m) :=
  upClosed_slice_hwTargetBad W m

open scoped Classical in
/-- **The fresh bound of every slice** below `T` database entries: the rates of
`preimageRateBound (N + T) G (2^838 · coverMass S)`; on `h`, `2^16 · price S` (`covRate_eq`). -/
theorem freshBound_slice_covBad [DecidablePred (· ∈ CovBad π pk S ex N)] {G : ℕ}
    (hπ : PermGood π G) (T : ℕ) (W : Hw X Z) (m : M) :
    FreshBound (slice (CovBad π pk S ex N) W m) T
      (preimageRateBound (X := X) (Z := Z) (N + T) G (2 ^ 838 * coverMass S)) :=
  freshBound_slice_hwTargetBad_of_tgt hπ (fun W m ↦ card_covOut_tgt_le S pk (ex W m)) T W m

/-- **A memory update that only grows the exemption flips nothing.** -/
theorem not_mem_covBad_memory {D : DbReg X Z} {W : Hw X Z} {m m' : M}
    (hs : (D, W, m) ∉ CovBad π pk S ex N) (hm : ex W m ⊆ ex W m') :
    (D, W, m') ∉ CovBad π pk S ex N :=
  fun ⟨hN, h⟩ ↦ hs ⟨hN, targetBad_mono (fun _ _ ht ↦ covTgt_mono hm ht) h⟩

/-! ### Program ports -/

open scoped Classical in
/-- **Programming an `h` cell** that is not hardwired: at most `2^838 · coverMass S` values flip a
state outside the event into it. -/
theorem card_flip_programH_covBad_le (hex : ExMono ex) {D : DbReg X Z} {W : Hw X Z} {m : M}
    (hs : (D, W, m) ∉ CovBad π pk S ex N) {z : Z} (hW : W.1 z = none) :
    (Finset.univ.filter fun v : X ↦
      ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∈
        CovBad π pk S ex N).card ≤ 2 ^ 838 * coverMass S :=
  card_flip_programH_le_of_tgt (tgtAnti_covTgt hex) (fun W m ↦ card_covOut_tgt_le S pk (ex W m))
    hs hW

/-- **`covBad_progUpdate`: programming an `h` cell whose head-tail has no coverage target flips
nothing.** In the good union the head-tail `t₀` of the cell is unique; if every pair whose call-0
slot `t₀` is lies in the exemption once the cell is hardwired (an honest call-0 tail hardwired at
its signature, or a tail at another slot), the programmed state is outside the event. -/
theorem covBad_progUpdate (hex : ExMono ex) {D : DbReg X Z} {W : Hw X Z} {m : M}
    (hs : (D, W, m) ∉ CovBad π pk S ex N) {z : Z} (hW : W.1 z = none) (v : X) {t₀ : List X}
    {xi₀ : X} (hhead : IsHeadTail π (union W D) t₀ z xi₀)
    (hex₀ : ∀ R msg, slotOf pk t₀ = some (.hmsg R msg 0) →
      (R, msg) ∈ ex (Function.update W.1 z (some v), W.2) m) :
    ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∉
      CovBad π pk S ex N :=
  not_mem_programH (tgtAnti_covTgt hex) hs hW v fun hG _ _ hi ↦ by
    obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hhead
    exact covTgt_eq_none hex₀

open scoped Classical in
/-- `covBad_progUpdate` as a flip count: no value flips. -/
theorem card_flip_programH_covBad_eq_zero (hex : ExMono ex) {D : DbReg X Z} {W : Hw X Z}
    {m : M} (hs : (D, W, m) ∉ CovBad π pk S ex N) {z : Z} (hW : W.1 z = none) {t₀ : List X}
    {xi₀ : X} (hhead : IsHeadTail π (union W D) t₀ z xi₀)
    (hex₀ : ∀ v R msg, slotOf pk t₀ = some (.hmsg R msg 0) →
      (R, msg) ∈ ex (Function.update W.1 z (some v), W.2) m) :
    (Finset.univ.filter fun v : X ↦
      ((Function.update D.1 z none, D.2), (Function.update W.1 z (some v), W.2), m) ∈
        CovBad π pk S ex N).card = 0 :=
  card_programH_eq_zero fun v ↦ covBad_progUpdate hex hs hW v hhead (hex₀ v)

open scoped Classical in
/-- **Programming a `k` cell** that is not hardwired: the capacity-scale count of
`preimageRateBound`, for at most `T ≥ N + dbGrade D` entries. -/
theorem card_flip_programK_covBad_le (hex : ExMono ex) {G T : ℕ} (hπ : PermGood π G)
    {D : DbReg X Z} {W : Hw X Z} {m : M} (hs : (D, W, m) ∉ CovBad π pk S ex N)
    (hT : N + dbGrade D ≤ T) {x : X} (hW : W.2.1 x = none) :
    (Finset.univ.filter fun v : Z ↦
      ((D.1, Function.update D.2.1 x none, D.2.2), (W.1, Function.update W.2.1 x (some v), W.2.2),
        m) ∈ CovBad π pk S ex N).card ≤ (T + 1) * ((T + 1) * T + 2 * T) * G :=
  card_flip_programK_le (tgtAnti_covTgt hex) hπ hs hT hW

open scoped Classical in
/-- **Programming a `k'` cell** that is not hardwired: the capacity-scale count of
`preimageRateBound`, for at most `T ≥ N + dbGrade D` entries. -/
theorem card_flip_programK'_covBad_le (hex : ExMono ex) {G T : ℕ} (hπ : PermGood π G)
    {D : DbReg X Z} {W : Hw X Z} {m : M} (hs : (D, W, m) ∉ CovBad π pk S ex N)
    (hT : N + dbGrade D ≤ T) {x : X} (hW : W.2.2 x = none) :
    (Finset.univ.filter fun v : Z ↦
      ((D.1, D.2.1, Function.update D.2.2 x none), (W.1, W.2.1, Function.update W.2.2 x (some v)),
        m) ∈ CovBad π pk S ex N).card ≤
      (T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T :=
  card_flip_programK'_le (tgtAnti_covTgt hex) hπ hs hT hW

/-! ### Read ports -/

/-- **A read of an `h` cell** that is neither hardwired nor recorded, with memory `m'` after the
read whose exemption contains the old one: whatever the read leaves in the cell, the state is
outside the event if, in a good union, the head-tails of the cell have no coverage target. -/
theorem not_mem_covBad_readH {D : DbReg X Z} {W : Hw X Z} {m m' : M}
    (hs : (D, W, m) ∉ CovBad π pk S ex N) {z : Z} (hW : W.1 z = none) (hD : D.1 z = none)
    (hm : ex W m ⊆ ex W m')
    (hhead : Good π (union W D) → ∀ t xi, IsHeadTail π (union W D) t z xi →
      ∀ R msg, slotOf pk t = some (.hmsg R msg 0) → (R, msg) ∈ ex W m')
    (u : Option X) : ((Function.update D.1 z u, D.2), W, m') ∉ CovBad π pk S ex N :=
  not_mem_readH hs hW hD (Q := fun _ _ ↦ False) (fun _ _ ht ↦ .inl (covTgt_mono hm ht))
    (fun _ _ h ↦ h.elim) (fun hG t xi hi ↦ covTgt_eq_none (hhead hG t xi hi)) u

end Event

end Quantum.Sphincs

end
