module

public import NativeVm.Code.Phase6.Blocks
public import NativeVm.Code.Phase6.Facts

/-!
# Phase 6's constant tables

The words the layers look up by index, as literal lists (`tRC`, the lane tables, the embedding's),
each equal entry by entry to what it stands for (`tA4_spec`, ...); `initT o ws` writes the list `ws`
from the element `o`, a word `w` as `EW.ofK w` (`pure_initT`), and `initAll` all of them. `Cn g`:
the scratch `g` holds them.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters
open NativeVm.Transcript (Env)

/-- `KECCAK_RC`'s words. -/
def tRC : List Nat := keccakRCLit.toList.map UInt64.toNat

/-- Per lane, `64 ·` the lane `4` columns along in its row. -/
def tA4 : List Nat := [256, 0, 64, 128, 192, 576, 320, 384, 448, 512, 896, 640, 704, 768, 832, 1216,
  960, 1024, 1088, 1152, 1536, 1280, 1344, 1408, 1472]

/-- Per lane, `64 ·` the lane `3` columns along in its row. -/
def tA3 : List Nat := [192, 256, 0, 64, 128, 512, 576, 320, 384, 448, 832, 896, 640, 704, 768, 1152,
  1216, 960, 1024, 1088, 1472, 1536, 1280, 1344, 1408]

/-- Per lane, `64 · π(lane)`. -/
def tPi : List Nat := [0, 640, 1280, 320, 960, 1024, 64, 704, 1344, 384, 448, 1088, 128, 768, 1408,
  1472, 512, 1152, 192, 832, 896, 1536, 576, 1216, 256]

/-- Per lane, `ρ(lane)`. -/
def tRho : List Nat :=
  [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- Per lane, `64 ·` its column one along. -/
def tC1 : List Nat := [64, 128, 192, 256, 0, 64, 128, 192, 256, 0, 64, 128, 192, 256, 0, 64, 128,
  192, 256, 0, 64, 128, 192, 256, 0]

/-- Per lane, `64 ·` its column four along. -/
def tC4 : List Nat := [256, 0, 64, 128, 192, 256, 0, 64, 128, 192, 256, 0, 64, 128, 192, 256, 0, 64,
  128, 192, 256, 0, 64, 128, 192]

theorem tA4_spec : ∀ l < 25, tA4.getD l 0 = 64 * ((l % 5 + 4) % 5 + 5 * (l / 5)) := by decide
theorem tA3_spec : ∀ l < 25, tA3.getD l 0 = 64 * ((l % 5 + 3) % 5 + 5 * (l / 5)) := by decide
theorem tPi_spec : ∀ l < 25, tPi.getD l 0 = 64 * keccakPi l := by decide
theorem tRho_spec : ∀ l < 25, tRho.getD l 0 = keccakRho.getD l 0 := by decide
theorem tC1_spec : ∀ l < 25, tC1.getD l 0 = 64 * ((l % 5 + 1) % 5) := by decide
theorem tC4_spec : ∀ l < 25, tC4.getD l 0 = 64 * ((l % 5 + 4) % 5) := by decide
theorem tRho_lt : ∀ l < 25, tRho.getD l 0 < 64 := by decide

theorem tRC_spec : ∀ i < 24, (tRC.getD i 0).toUInt64 = keccakRCLit.getD i 0 := by
  intro i hi
  simp only [tRC, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_getElem (by simpa [keccakRCLit] using hi)]
  simp

theorem tEmbed_spec : ∀ i < 16, (NativeVm.Equiv.rmfeEmbedLit.getD i 0).toUInt64 =
    NativeVm.Equiv.rmfeEmbedWLit.getD i 0 := by decide

theorem tProject_spec : ∀ i < 16, (NativeVm.Equiv.rmfeProjectLit.getD i 0).toUInt64 =
    NativeVm.Equiv.rmfeProjectWLit.getD i 0 := by decide

/-- The list `ws` from the element `o`. -/
def initT (o : Nat) : List Nat → List Stmt
  | [] => []
  | w :: ws => blk (setW o w) :: initT (o + 1) ws

/-- The table `ws` at `o`. -/
def tab_at (g : Nat → EW) (o : Nat) (ws : List Nat) : Prop :=
  ∀ i < ws.length, g (o + i) = EW.ofK (ws.getD i 0).toUInt64

variable {env : Env} {inp : Input} {s0 : QState}

theorem pure_initT (hin : Inputs env inp s0.mem) :
    ∀ (ws : List Nat) (o : Nat) (g : Nat → EW), o + ws.length ≤ scrN →
      ∃ g', Pure6 env s0 (blk (initT o ws)) g g' ∧ tab_at g' o ws ∧
        ∀ i, (i < o ∨ o + ws.length ≤ i) → g' i = g i
  | [], o, g, _ => ⟨g, Pure6.nil, fun i hi ↦ absurd hi (by simp), fun _ _ ↦ rfl⟩
  | w :: ws, o, g, h => by
    simp only [List.length_cons] at h
    obtain ⟨g', h1, h2, h3⟩ := pure_initT hin ws (o + 1)
      (Function.update g o (EW.ofK w.toUInt64)) (by omega)
    refine ⟨g', Pure6.cons (pure_setW hin (by omega)) h1, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · rcases i with _ | i
      · rw [h3 _ (by omega), Nat.add_zero, Function.update_self]; rfl
      · rw [show o + (i + 1) = o + 1 + i by omega, h2 i (by simpa using hi)]; rfl
    · rw [h3 _ (by simp only [List.length_cons] at hi; omega),
        Function.update_of_ne (by simp only [List.length_cons] at hi; omega)]

/-- **The constants**: every table at its place. -/
def Cn (g : Nat → EW) : Prop :=
  tab_at g eRC tRC ∧ tab_at g eA4 tA4 ∧ tab_at g eA3 tA3 ∧ tab_at g ePi tPi ∧ tab_at g eRho tRho ∧
    tab_at g eC1 tC1 ∧ tab_at g eC4 tC4 ∧ tab_at g eEmbed NativeVm.Equiv.rmfeEmbedLit ∧
    tab_at g eProject NativeVm.Equiv.rmfeProjectLit

/-- Every table, in order. -/
def initAll : List Stmt :=
  [blk (initT eRC tRC), blk (initT eA4 tA4), blk (initT eA3 tA3), blk (initT ePi tPi),
    blk (initT eRho tRho), blk (initT eC1 tC1), blk (initT eC4 tC4),
    blk (initT eEmbed NativeVm.Equiv.rmfeEmbedLit), blk (initT eProject NativeVm.Equiv.rmfeProjectLit)]

theorem tab_at_congr {g g' : Nat → EW} {o : Nat} {ws : List Nat} (h : tab_at g o ws)
    (he : ∀ i, o ≤ i → i < o + ws.length → g' i = g i) : tab_at g' o ws :=
  fun i hi ↦ by rw [he _ (by omega) (by omega), h i hi]

theorem Cn.congr {g g' : Nat → EW} (h : Cn g) (he : ∀ i, eRC ≤ i → i < eProject + 16 → g' i = g i) :
    Cn g' := by
  have lRC : tRC.length = 24 := rfl
  have l25 : tA4.length = 25 ∧ tA3.length = 25 ∧ tPi.length = 25 ∧ tRho.length = 25 ∧
      tC1.length = 25 ∧ tC4.length = 25 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have l16 : NativeVm.Equiv.rmfeEmbedLit.length = 16 ∧ NativeVm.Equiv.rmfeProjectLit.length = 16 :=
    ⟨rfl, rfl⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨tab_at_congr h1 ?_, tab_at_congr h2 ?_, tab_at_congr h3 ?_, tab_at_congr h4 ?_,
    tab_at_congr h5 ?_, tab_at_congr h6 ?_, tab_at_congr h7 ?_, tab_at_congr h8 ?_,
    tab_at_congr h9 ?_⟩ <;> intro i h1 h2 <;> exact he i (by p6_omega) (by p6_omega)

theorem pure_initAll (hin : Inputs env inp s0.mem) (g : Nat → EW) :
    ∃ g', Pure6 env s0 (blk initAll) g g' ∧ Cn g' ∧ ∀ i, (i < eRC ∨ eProject + 16 ≤ i) → g' i = g i := by
  have l : tRC.length = 24 ∧ tA4.length = 25 ∧ tA3.length = 25 ∧ tPi.length = 25 ∧
      tRho.length = 25 ∧ tC1.length = 25 ∧ tC4.length = 25 ∧
      NativeVm.Equiv.rmfeEmbedLit.length = 16 ∧ NativeVm.Equiv.rmfeProjectLit.length = 16 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := l
  obtain ⟨g1, p1, t1, k1⟩ := pure_initT hin tRC eRC g (by p6_omega)
  obtain ⟨g2, p2, t2, k2⟩ := pure_initT hin tA4 eA4 g1 (by p6_omega)
  obtain ⟨g3, p3, t3, k3⟩ := pure_initT hin tA3 eA3 g2 (by p6_omega)
  obtain ⟨g4, p4, t4, k4⟩ := pure_initT hin tPi ePi g3 (by p6_omega)
  obtain ⟨g5, p5, t5, k5⟩ := pure_initT hin tRho eRho g4 (by p6_omega)
  obtain ⟨g6, p6, t6, k6⟩ := pure_initT hin tC1 eC1 g5 (by p6_omega)
  obtain ⟨g7, p7, t7, k7⟩ := pure_initT hin tC4 eC4 g6 (by p6_omega)
  obtain ⟨g8, p8, t8, k8⟩ := pure_initT hin NativeVm.Equiv.rmfeEmbedLit eEmbed g7 (by p6_omega)
  obtain ⟨g9, p9, t9, k9⟩ := pure_initT hin NativeVm.Equiv.rmfeProjectLit eProject g8 (by p6_omega)
  refine ⟨g9, p1.cons (p2.cons (p3.cons (p4.cons (p5.cons (p6.cons (p7.cons (p8.cons p9.single))))))),
    ⟨tab_at_congr t1 fun i _ _ ↦ by rw [k9 i (by p6_omega), k8 i (by p6_omega), k7 i (by p6_omega), k6 i (by p6_omega), k5 i (by p6_omega), k4 i (by p6_omega), k3 i (by p6_omega), k2 i (by p6_omega)],
    tab_at_congr t2 fun i _ _ ↦ by rw [k9 i (by p6_omega), k8 i (by p6_omega), k7 i (by p6_omega), k6 i (by p6_omega), k5 i (by p6_omega), k4 i (by p6_omega), k3 i (by p6_omega)],
    tab_at_congr t3 fun i _ _ ↦ by rw [k9 i (by p6_omega), k8 i (by p6_omega), k7 i (by p6_omega), k6 i (by p6_omega), k5 i (by p6_omega), k4 i (by p6_omega)],
    tab_at_congr t4 fun i _ _ ↦ by rw [k9 i (by p6_omega), k8 i (by p6_omega), k7 i (by p6_omega), k6 i (by p6_omega), k5 i (by p6_omega)],
    tab_at_congr t5 fun i _ _ ↦ by rw [k9 i (by p6_omega), k8 i (by p6_omega), k7 i (by p6_omega), k6 i (by p6_omega)],
    tab_at_congr t6 fun i _ _ ↦ by rw [k9 i (by p6_omega), k8 i (by p6_omega), k7 i (by p6_omega)],
    tab_at_congr t7 fun i _ _ ↦ by rw [k9 i (by p6_omega), k8 i (by p6_omega)],
    tab_at_congr t8 fun i _ _ ↦ by rw [k9 i (by p6_omega)],
    t9⟩, fun i hi ↦ by rw [k9 i (by p6_omega), k8 i (by p6_omega), k7 i (by p6_omega), k6 i (by p6_omega), k5 i (by p6_omega), k4 i (by p6_omega), k3 i (by p6_omega), k2 i (by p6_omega), k1 i (by p6_omega)]⟩

end NativeVm.Code.P6
