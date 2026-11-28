/-
  LeanVM.Guest.B1.VsC.Os.LeftLqMem

  A level's `level_queries` windows from its `level_positions` decoders' runs.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftLq
public import LeanVM.Guest.B1.VsC.LpA
public import LeanVM.Guest.B1.VsC.SlowA
public import LeanVM.Guest.B1.VsC.Os.LeftNode

/-!
# A level's windows

`level_positions`' decoder `j` writes its run `qwRunList d cd (w j)` at `F j` (its frame past
`cert dq (.n 5)`); query `k`'s window, of `qwN d cd` words, starts `k % P` windows into decoder
`k / P`'s run, `P = 128 / d`. `lqWin_of_runs`: those words are `level_queries`' window words of
query `k`'s position (`qwRunW_at`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- Query `k`'s window pointer, decoder `j`'s run at `F j`, `128 / d` windows of `qwN d cd` words a run. -/
def lqWp (d cd : ℕ) (F : ℕ → ℕ) (k : ℕ) : ℕ := F (k / (128 / d)) + k % (128 / d) * qwN d cd

/-- **Query `k`'s window holds its position's window words**, from its decoder's run. -/
theorem lqWin_of_runs {rd : Reader} {d cd : ℕ} {F : ℕ → ℕ} {w : ℕ → E} {S : ℕ}
    (hwin : ∀ j < S, ReadsAt rd (ptrAt (F j)) (qwRunList d cd (w j))) {k : ℕ} (hk : k / (128 / d) < S)
    (hP : 0 < 128 / d) :
    ∀ i < qwN d cd, LoadHolds rd (ptrAt (lqWp d cd F k)) i
      (gen ^ qwVal d cd (qwPosOf d (w (k / (128 / d))) (k % (128 / d))) i) := by
  intro i hi
  have hm : k % (128 / d) + 1 ≤ 128 / d := Nat.succ_le_of_lt (Nat.mod_lt _ hP)
  have hb : k % (128 / d) * qwN d cd + i < (qwRunList d cd (w (k / (128 / d)))).length := by
    simp only [qwRunList, List.length_map, List.length_range]
    calc k % (128 / d) * qwN d cd + i < (k % (128 / d) + 1) * qwN d cd := by rw [Nat.add_one_mul]; omega
      _ ≤ 128 / d * qwN d cd := Nat.mul_le_mul_right _ hm
  have h := hwin _ hk _ hb
  simp only [qwRunList, List.getElem_map, List.getElem_range] at h
  rw [qwRunW_at _ hi] at h
  rw [lqWp, ← ptrAt_mul_gen]
  exact (loadHolds_mul_gen_pow rd _ _ _ _).mpr h

/-- An arm's levels' positions fit their squeezes and `query_positions`. -/
def OsPosOk (m : ℕ) : Bool :=
  (List.range 4).all fun ri => (osCfgR m ri).levels.all fun lv =>
    0 < 128 / lv.depth && lv.queries ≤ lv.squeezes * (128 / lv.depth) && lv.posOff + lv.queries ≤ osPosTotal (osCfgR m ri)

set_option maxRecDepth 100000 in
theorem osPosOk_all : (List.range 15).all OsPosOk = true := by decide +kernel

theorem osPos_le {m ri l : ℕ} (hm : m < 15) (hri : ri < 4) (hl : l < (osCfgR m ri).levels.length) :
    0 < 128 / (osLvA (osCfgR m ri) l).depth ∧
      (osLvA (osCfgR m ri) l).queries ≤ (osLvA (osCfgR m ri) l).squeezes * (128 / (osLvA (osCfgR m ri) l).depth) ∧
      (osLvA (osCfgR m ri) l).posOff + (osLvA (osCfgR m ri) l).queries ≤ osPosTotal (osCfgR m ri) := by
  have h := List.all_eq_true.mp osPosOk_all m (List.mem_range.mpr hm)
  simp only [OsPosOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  have hmem : (osCfgR m ri).levels.getD l default ∈ (osCfgR m ri).levels := by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl
  obtain ⟨⟨h1, h2⟩, h3⟩ := h ri hri _ hmem
  exact ⟨h1, h2, h3⟩

end
end LeanVM.Guest.B1.VsC

namespace LeanVM.Guest.B1.Whir.HonRun

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.Value LeanVM.Guest.B1.VsC LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **Level `l`'s positions in `query_positions` are its openings' leaf indices**, on every memory
holding the buffers. -/
theorem lqPos_os {cur tabs : E} {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) {b : ℕ}
    {rd : Reader} (hmem : OsMemA rd (osCfgR (μ - minOpenLog) (r - 1)) b (hR.osHonest (cur := cur) (tabs := tabs)).own) :
    ∀ k < (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).queries,
      LoadHolds rd (osPtrA (osCfgR (μ - minOpenLog) (r - 1)) b osIxQposA * gen ^ (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).posOff)
        k (eOfNat (opAt (os.getD l []) k).leafIndex) := by
  intro k hk
  obtain ⟨hP, hqs, hpt⟩ := osPos_le hR.m11 hR.r4 hl
  obtain ⟨hlen, hqo⟩ := hR.qs_os (cur := cur) (tabs := tabs) hl
  have hk' : k < oqQA (osCfgR (μ - minOpenLog) (r - 1)) l := by rw [← hlen, hR.phase_len_os hl]; exact hk
  have hj : k / (128 / (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth) < (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).squeezes :=
    (Nat.div_lt_iff_lt_mul hP).mpr (by omega)
  have hpw := (hR.osHonest (cur := cur) (tabs := tabs)).posW l hl
    (k / (128 / (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth)) hj
    (k % (128 / (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth)) (Nat.mod_lt _ hP)
  rw [← (hR.osHonest (cur := cur) (tabs := tabs)).qs_eq l hl k hk', hqo k hk',
    show (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).posOff + k / osPerA (osCfgR (μ - minOpenLog) (r - 1)) l *
      osPerA (osCfgR (μ - minOpenLog) (r - 1)) l + k % osPerA (osCfgR (μ - minOpenLog) (r - 1)) l =
      (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).posOff + k by rw [Nat.add_assoc, Nat.div_add_mod']] at hpw
  have h10 : osIxQposA < (osSizesL (osCfgR (μ - minOpenLog) (r - 1))).length := by
    simp [osSizesL, osIxQposA]
  have hrd := hmem osIxQposA h10 (by decide)
  have hlen10 : (osOwnA (hR.osHonest (cur := cur) (tabs := tabs)).own osIxQposA).length =
      osPosTotal (osCfgR (μ - minOpenLog) (r - 1)) :=
    (forall₂_getD (hR.osHonest (cur := cur) (tabs := tabs)).own_len osIxQposA).trans rfl
  have hb : (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).posOff + k <
      (osOwnA (hR.osHonest (cur := cur) (tabs := tabs)).own osIxQposA).length := by rw [hlen10]; omega
  have h := hrd _ hb
  rw [← List.getD_eq_getElem _ 0 hb] at h
  unfold osOwnA at h hpw
  rw [hpw] at h
  exact (loadHolds_mul_gen_pow rd _ _ _ _).mpr h

end
end LeanVM.Guest.B1.Whir.HonRun
