/-
  LeanVM.Guest.B1.Da.CompleteAt

  `da_verify` complete in the uniform placed form (`CompleteRel`): its honest memory as a layout of
  its own words, and the squares-table word it loads within the caller's words.
-/

module

public import LeanVM.Guest.B1.Da.VerifyAt
public import LeanVM.Guest.B1.Digest.Forced

/-!
# `da_verify`, uniformly placed

* `dvLayout`: `da_verify`'s own words at `fp`, `DaMem` as a layout (`daMem_of_memL`), within its
  `dvTot` words (`dvLayout_within`) when the certificate's frame runs fit their frames.
* `da_verify_completeRel`: `CompleteRel` on `DaPre`, the squares table and a witness opening the
  returned claim.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value LeanVM.Node
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteAt CompleteAtD CompleteRel CompleteRelD DisjL disj_nil Within Returns)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- A tree's nodes from `base`, as `TreeAt` reads them. -/
def treeL (base k : ℕ) (leaf : ℕ → Digest) : Layout :=
  (List.range (k + 1)).flatMap fun l => (List.range (2 ^ (k - l))).map fun j =>
    (base + (lvOff k l + 2 * j), [(digestScalars (nodeD leaf l j)).1, (digestScalars (nodeD leaf l j)).2])

theorem treeAt_of_memL {rd : Reader} {L : Layout} (h : MemL rd L) {base k : ℕ} {leaf : ℕ → Digest}
    (hs : ∀ q ∈ treeL base k leaf, q ∈ L) : TreeAt rd (gen ^ base) k leaf := fun l hl j hj => by
  rw [← pow_add]
  exact cells_of_memL h (hs _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr (by omega),
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩))

theorem lvOff_add {k l j : ℕ} (hl : l ≤ k) (hj : j < 2 ^ (k - l)) : lvOff k l + 2 * j + 2 ≤ 4 * 2 ^ k := by
  have : 2 ^ (k - l) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold lvOff; omega

theorem treeL_within {base k : ℕ} {leaf : ℕ → Digest} :
    ∀ q ∈ treeL base k leaf, base ≤ q.1 ∧ q.1 + q.2.length ≤ base + 4 * 2 ^ k := by
  intro q hq
  obtain ⟨l, hl, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
  have := lvOff_add (Nat.lt_succ_iff.mp (List.mem_range.mp hl)) (List.mem_range.mp hj)
  simp only [List.length_cons, List.length_nil]
  omega

/-! ## `da_verify`'s own words -/

section Layout
variable (fs : String → ℕ) (cert : String → V → ℕ) (w : Da.Witness) (fp : ℕ)

/-- The exponents of `dvPtrs`' buffers and runs. -/
def dvDx : ℕ := fp + fs "da_verify"
def dvPx : ℕ := dvDx fs fp + 128 * LeanDa.nPad w.rows.length
def dvHx : ℕ := dvPx fs w fp + w.rows.length
def dvAx : ℕ := dvHx fs w fp + 258
def dvBx : ℕ := dvAx fs w fp + 129 * w.rows.length
def dvTx : ℕ := dvBx fs w fp + w.rows.length
def dvWx : ℕ := dvTx fs w fp + 512
def dvCx : ℕ := fp + cert "da_verify" (.n 20)
def dvNode (b : ℕ) : ℕ :=
  dvColPos fs fp w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length) b +
    fs (colName (decide (b < 64)))
def dvLv (b : ℕ) : ℕ :=
  dvNode fs w fp b + 4 * LeanDa.nPad w.rows.length + fs "da_vector_dispatch" +
    cert (vxName (decide (b = 127))) (.n 4)

/-- **`da_verify`'s honest words at `fp`**: `DaMem` at `dvPtrs`, entry by entry. -/
def dvLayout : Layout :=
  let r := w.rows.length
  let lp := LeanDa.logPad r
  (List.range r).map (fun i => (dvPx fs w fp + i, [gen ^ dvDx fs fp * gen ^ (128 * i)])) ++
  (List.range r).flatMap (fun i => (List.range 64).map fun b => (dvDx fs fp + (128 * i + 2 * b),
    [(digestScalars (cellDOf (daSym w) b i)).1, (digestScalars (cellDOf (daSym w) b i)).2])) ++
  (List.range 129).map (fun b => (dvHx fs w fp + 2 * b, [(digestScalars (daS w b)).1, (digestScalars (daS w b)).2])) ++
  [(dvCx cert fp, (List.range 385).map fun k => word (k * 2048) 0 0)] ++
  (List.range r).map (fun i => (dvBx fs w fp + i, [gen ^ dvAx fs w fp * gen ^ (129 * i)])) ++
  (List.range r).map (fun i => (dvAx fs w fp + 129 * i, (List.range 129).map (daA w i))) ++
  treeL (dvTx fs w fp) 7 (fun b => nodeD (colLeafOf r (daSym w) b) lp 0) ++
  treeL (dvWx fs w fp) lp (rowLeafOf r (daSym w)) ++
  (List.range 128).flatMap (fun b => treeL (dvNode fs w fp b) lp (colLeafOf r (daSym w) b)) ++
  (List.range 128).map (fun b => (dvLv fs cert w fp b, daWs w b))

end Layout

theorem dvPtrs_eq (fs : String → ℕ) (cert : String → V → ℕ) (w : Da.Witness) (fp : ℕ) :
    dvPtrs fs cert w.rows.length fp = ⟨gen ^ dvPx fs w fp, gen ^ dvDx fs fp, gen ^ dvHx fs w fp,
      gen ^ dvCx cert fp, gen ^ dvAx fs w fp, gen ^ dvBx fs w fp, gen ^ dvTx fs w fp, gen ^ dvWx fs w fp,
      fun b => gen ^ dvNode fs w fp b, fun b => gen ^ dvLv fs cert w fp b⟩ := rfl

/-- **The layout is the honest memory.** -/
theorem daMem_of_memL {fs : String → ℕ} {cert : String → V → ℕ} {w : Da.Witness} {fp : ℕ} {rd : Reader}
    {L : Layout} (h : MemL rd L) (hs : ∀ q ∈ dvLayout fs cert w fp, q ∈ L) :
    DaMem rd (dvPtrs fs cert w.rows.length fp) w := by
  rw [dvPtrs_eq]
  have m : ∀ {q}, q ∈ dvLayout fs cert w fp → q ∈ L := fun hq => hs _ hq
  simp only [dvLayout, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_singleton] at m
  refine ⟨fun i hi => ?_, fun i hi b hb => ?_, fun b hb => ?_, ?_, fun i hi => ?_, fun i hi b hb => ?_,
    treeAt_of_memL h fun q hq => m (Or.inl (Or.inl (Or.inl (Or.inr (hq))))),
    treeAt_of_memL h fun q hq => m (Or.inl (Or.inl (Or.inr (hq)))),
    fun b hb => treeAt_of_memL h fun q hq => m (Or.inl (Or.inr (⟨b, hb, hq⟩))), fun b hb => ?_⟩
  · rw [← pow_add]
    exact load_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (⟨i, hi, rfl⟩)))))))))))
  · rw [← pow_add]
    exact cells_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨i, hi, b, hb, rfl⟩)))))))))))
  · rw [← pow_add]
    exact cells_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨b, by omega, rfl⟩))))))))))
  · exact cells_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (rfl)))))))))
  · rw [← pow_add]
    exact load_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨i, hi, rfl⟩))))))))
  · rw [← pow_add]
    have := cells_of_memL h (m (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨i, hi, rfl⟩))))))) b (by simp; omega)
    simpa using this
  · exact cells_of_memL h (m (Or.inr (⟨b, hb, rfl⟩)))

/-! ## Within `da_verify`'s words -/

theorem clTot_ge (fs : String → ℕ) (store : Bool) (r N lp : ℕ) :
    ∀ d j, j = clLo store + d → j < clHi store →
      (j - clLo store) * fs (colLoopName store) + clTot fs store r N lp j ≤ clTot fs store r N lp (clLo store)
  | 0, j, hj, _ => by subst hj; simp
  | d + 1, j, hj, hlt => by
    have ih := clTot_ge fs store r N lp d (clLo store + d) rfl (by omega)
    have h := clTot_succ fs store r N lp (clLo store + d) (by omega)
    rw [ite_pos' (show clLo store + d + 1 < clHi store by omega), show clLo store + d + 1 = j by omega] at h
    rw [show j - clLo store = (clLo store + d - clLo store) + 1 by omega, Nat.add_mul, Nat.one_mul]
    omega

theorem colPos_add_le (fs : String → ℕ) (store : Bool) (r N lp fp0 b : ℕ) (h1 : clLo store ≤ b)
    (h2 : b < clHi store) :
    colPos fs store r N lp fp0 b + colTot fs store b r N lp ≤ fp0 + clTot fs store r N lp (clLo store) := by
  have h := clTot_succ fs store r N lp b h2
  have hg := clTot_ge fs store r N lp (b - clLo store) b (by omega) h2
  unfold colPos
  omega

/-- **`da_verify`'s words lie in its `dvTot` words**, when its counters' run and the vector cells'
weight runs fit their frames. -/
theorem dvLayout_within (fs : String → ℕ) (cert : String → V → ℕ) {w : Da.Witness} (fp : ℕ)
    (hr1 : 1 ≤ w.rows.length) (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify")
    (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) :
    Within (dvLayout fs cert w fp) fp (dvTot fs w.rows.length) := by
  have hrN : w.rows.length ≤ LeanDa.nPad w.rows.length := ((logPad_iff hr1).mp rfl).1
  have hN2 : 2 ^ LeanDa.logPad w.rows.length = LeanDa.nPad w.rows.length := rfl
  have h7 : 4 * 2 ^ 7 = 512 := by norm_num
  have hT : fs "da_verify" + (dvSizes w.rows.length (LeanDa.nPad w.rows.length)).sum ≤
      dvTot fs w.rows.length := by unfold dvTot; omega
  simp only [dvSizes, List.sum_cons, List.sum_nil] at hT
  have hcol : ∀ b < 128, dvColPos fs fp w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length) b +
      colTot fs (decide (b < 64)) b w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length) ≤
      fp + dvTot fs w.rows.length := by
    intro b hb
    have hk : dvPos91 fs fp w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length) +
        clTot fs false w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length) 64 ≤
        fp + dvTot fs w.rows.length := by
      simp only [dvTot, dvKids, dvPos91, dvPos90, dvK0, List.foldr]; omega
    by_cases h64 : b < 64
    · have := colPos_add_le fs true w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length)
        (dvPos90 fs fp w.rows.length (LeanDa.nPad w.rows.length)) b (Nat.zero_le _) h64
      simp only [dvColPos, h64, decide_true, ↓reduceIte]
      simp only [clLo, ↓reduceIte] at this
      unfold dvPos91 at hk; omega
    · have := colPos_add_le fs false w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length)
        (dvPos91 fs fp w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length)) b
        (by simp [clLo]; omega) (by simp [clHi]; omega)
      simp only [dvColPos, h64, decide_false, ↓reduceIte]
      simp only [clLo, Bool.false_eq_true, ↓reduceIte] at this
      omega
  have hcol' : ∀ b < 128, fp ≤ dvColPos fs fp w.rows.length (LeanDa.nPad w.rows.length)
      (LeanDa.logPad w.rows.length) b := fun b _ => by
    unfold dvColPos colPos dvPos91 dvPos90 dvK0; split <;> omega
  intro q hq
  simp only [dvLayout, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range,
    List.mem_singleton] at hq
  rcases hq with ((((((((⟨i, hi, rfl⟩ | ⟨i, hi, b, hb, rfl⟩) | ⟨b, hb, rfl⟩) | rfl) | ⟨i, hi, rfl⟩) |
    ⟨i, hi, rfl⟩) | hq) | hq) | ⟨b, hb, hq⟩) | ⟨b, hb, rfl⟩
  · simp only [dvPx, dvDx, List.length_cons, List.length_nil]; omega
  · simp only [dvDx, List.length_cons, List.length_nil]
    have : 128 * i + 2 * b + 2 ≤ 128 * LeanDa.nPad w.rows.length := by nlinarith
    omega
  · simp only [dvHx, dvPx, dvDx, List.length_cons, List.length_nil]; omega
  · simp only [dvCx, List.length_map, List.length_range]; omega
  · simp only [dvBx, dvAx, dvHx, dvPx, dvDx, List.length_cons, List.length_nil]; omega
  · simp only [dvAx, dvHx, dvPx, dvDx, List.length_map, List.length_range]
    have : 129 * i + 129 ≤ 129 * w.rows.length := by nlinarith
    omega
  · have := treeL_within q hq
    simp only [dvTx, dvBx, dvAx, dvHx, dvPx, dvDx] at this
    omega
  · have := treeL_within q hq
    rw [hN2] at this
    simp only [dvWx, dvTx, dvBx, dvAx, dvHx, dvPx, dvDx] at this
    omega
  · have := treeL_within q hq
    have := hcol b hb
    have := hcol' b hb
    rw [hN2] at *
    unfold dvNode colTot at *
    omega
  · have := hcol b hb
    have := hcol' b hb
    have := hc4 (decide (b = 127))
    have hl : (daWs w b).length ≤ 256 := by unfold daWs; simp
    dsimp only
    unfold dvLv dvNode colTot at *
    omega

/-! ## The words are pairwise disjoint -/

theorem treeL_disj {base k : ℕ} {leaf : ℕ → Digest} : DisjL (treeL base k leaf) := by
  unfold DisjL treeL
  rw [List.pairwise_flatMap]
  refine ⟨fun l hl => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_range (n := 2 ^ (k - l))).imp fun {a b} h =>
      Or.inl (by simp only [List.length_cons, List.length_nil]; omega)
  · refine (List.pairwise_lt_range (n := k + 1)).imp_of_mem fun {l l'} hl hl' hll x hx y hy => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hy
    have hj := List.mem_range.mp hj
    have hl := List.mem_range.mp hl
    have hl' := List.mem_range.mp hl'
    left
    simp only [lvOff, List.length_cons, List.length_nil]
    have h1 : 2 * 2 ^ (k - l') ≤ 2 ^ (k - l) := by
      calc 2 * 2 ^ (k - l') = 2 ^ (k - l' + 1) := by ring
        _ ≤ 2 ^ (k - l) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (k - l) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem colPos_ge (fs : String → ℕ) (store : Bool) (r N lp fp0 b : ℕ) :
    fp0 ≤ colPos fs store r N lp fp0 b := by
  unfold colPos; omega

/-- Consecutive columns of a loop are adjacent: column `j + 1` ends where column `j` begins. -/
theorem colPos_succ_eq (fs : String → ℕ) (store : Bool) (r N lp fp0 j : ℕ) (hlo : clLo store ≤ j)
    (hj : j + 1 < clHi store) :
    colPos fs store r N lp fp0 (j + 1) + colTot fs store (j + 1) r N lp = colPos fs store r N lp fp0 j := by
  have h := clTot_succ fs store r N lp (j + 1) hj
  unfold colPos
  rw [ite_pos' hj, show j + 1 - clLo store = (j - clLo store) + 1 by omega, Nat.add_mul, Nat.one_mul]
  omega

theorem colPos_sep (fs : String → ℕ) (store : Bool) (r N lp fp0 b b' : ℕ) (hlo : clLo store ≤ b)
    (hb : b < b') (hb' : b' < clHi store) :
    colPos fs store r N lp fp0 b' + colTot fs store b' r N lp ≤ colPos fs store r N lp fp0 b := by
  obtain ⟨d, rfl⟩ : ∃ d, b' = b + d + 1 := ⟨b' - b - 1, by omega⟩
  clear hb
  induction d with
  | zero => exact (colPos_succ_eq fs store r N lp fp0 b hlo hb').le
  | succ d ih =>
    rw [show b + (d + 1) + 1 = b + d + 1 + 1 by omega] at hb' ⊢
    have := colPos_succ_eq fs store r N lp fp0 (b + d + 1) (by omega) hb'
    have := ih (by omega)
    omega

/-- Two distinct columns of `da_verify` have disjoint words. -/
theorem dvCol_sep (fs : String → ℕ) (fp r N lp : ℕ) {b b' : ℕ} (hb : b < b') (hb' : b' < 128) :
    dvColPos fs fp r N lp b' + colTot fs (decide (b' < 64)) b' r N lp ≤ dvColPos fs fp r N lp b ∨
    dvColPos fs fp r N lp b + colTot fs (decide (b < 64)) b r N lp ≤ dvColPos fs fp r N lp b' := by
  by_cases h' : b' < 64
  · have h : b < 64 := by omega
    left
    simp only [dvColPos, h, h', decide_true, ↓reduceIte]
    exact colPos_sep fs true r N lp _ b b' (by simp [clLo]) hb (by simp [clHi]; omega)
  · by_cases h : b < 64
    · right
      have h1 := colPos_add_le fs true r N lp (dvPos90 fs fp r N) b (by simp [clLo])
        (by simp [clHi]; omega)
      have h2 := colPos_ge fs false r N lp (dvPos91 fs fp r N lp) b'
      have h91 : dvPos91 fs fp r N lp = dvPos90 fs fp r N + clTot fs true r N lp 0 := rfl
      simp only [clLo, ↓reduceIte] at h1
      simp only [dvColPos, h, h', decide_true, decide_false, ↓reduceIte]
      omega
    · left
      simp only [dvColPos, h, h', decide_false, ↓reduceIte]
      exact colPos_sep fs false r N lp _ b b' (by simp [clLo]; omega) hb (by simp [clHi]; omega)

theorem dvColPos_ge (fs : String → ℕ) (fp r N lp b : ℕ) : dvPos90 fs fp r N ≤ dvColPos fs fp r N lp b := by
  by_cases h : b < 64
  · simp only [dvColPos, h, decide_true, ↓reduceIte]
    exact colPos_ge ..
  · simp only [dvColPos, h, decide_false, ↓reduceIte]
    have := colPos_ge fs false r N lp (dvPos91 fs fp r N lp) b
    have h91 : dvPos91 fs fp r N lp = dvPos90 fs fp r N + clTot fs true r N lp 0 := rfl
    omega

theorem disjL_append2 {L L' : Layout} (h : DisjL L) (h' : DisjL L')
    (hx : ∀ q ∈ L, ∀ q' ∈ L', q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1) : DisjL (L ++ L') :=
  List.pairwise_append.mpr ⟨h, h', hx⟩


def dvPc1 (fs : String → ℕ) (w : Da.Witness) (fp : ℕ) : Layout :=
  (List.range w.rows.length).map (fun i => (dvPx fs w fp + i, [gen ^ dvDx fs fp * gen ^ (128 * i)]))

def dvPc2 (fs : String → ℕ) (w : Da.Witness) (fp : ℕ) : Layout :=
  (List.range w.rows.length).flatMap (fun i => (List.range 64).map fun b => (dvDx fs fp + (128 * i + 2 * b),
    [(digestScalars (cellDOf (daSym w) b i)).1, (digestScalars (cellDOf (daSym w) b i)).2]))

def dvPc3 (fs : String → ℕ) (w : Da.Witness) (fp : ℕ) : Layout :=
  (List.range 129).map (fun b => (dvHx fs w fp + 2 * b, [(digestScalars (daS w b)).1, (digestScalars (daS w b)).2]))

def dvPc4 (cert : String → V → ℕ) (fp : ℕ) : Layout :=
  [(dvCx cert fp, (List.range 385).map fun k => word (k * 2048) 0 0)]

def dvPc5 (fs : String → ℕ) (w : Da.Witness) (fp : ℕ) : Layout :=
  (List.range w.rows.length).map (fun i => (dvBx fs w fp + i, [gen ^ dvAx fs w fp * gen ^ (129 * i)]))

def dvPc6 (fs : String → ℕ) (w : Da.Witness) (fp : ℕ) : Layout :=
  (List.range w.rows.length).map (fun i => (dvAx fs w fp + 129 * i, (List.range 129).map (daA w i)))

def dvPc7 (fs : String → ℕ) (w : Da.Witness) (fp : ℕ) : Layout :=
  treeL (dvTx fs w fp) 7 (fun b => nodeD (colLeafOf w.rows.length (daSym w) b) (LeanDa.logPad w.rows.length) 0)

def dvPc8 (fs : String → ℕ) (w : Da.Witness) (fp : ℕ) : Layout :=
  treeL (dvWx fs w fp) (LeanDa.logPad w.rows.length) (rowLeafOf w.rows.length (daSym w))

def dvPc9 (fs : String → ℕ) (w : Da.Witness) (fp : ℕ) : Layout :=
  (List.range 128).flatMap (fun b => treeL (dvNode fs w fp b) (LeanDa.logPad w.rows.length) (colLeafOf w.rows.length (daSym w) b))

def dvPc10 (fs : String → ℕ) (cert : String → V → ℕ) (w : Da.Witness) (fp : ℕ) : Layout :=
  (List.range 128).map (fun b => (dvLv fs cert w fp b, daWs w b))

theorem dvLayout_eq (fs : String → ℕ) (cert : String → V → ℕ) (w : Da.Witness) (fp : ℕ) :
    dvLayout fs cert w fp = dvPc1 fs w fp ++ dvPc2 fs w fp ++ dvPc3 fs w fp ++ dvPc4 cert fp ++ dvPc5 fs w fp ++ dvPc6 fs w fp ++ dvPc7 fs w fp ++ dvPc8 fs w fp ++ dvPc9 fs w fp ++ dvPc10 fs cert w fp := rfl


section Pieces
variable (fs : String → ℕ) (w : Da.Witness) (fp : ℕ)

theorem dvPc1_bound : ∀ q ∈ dvPc1 fs w fp, dvPx fs w fp ≤ q.1 ∧ q.1 + q.2.length ≤ dvPx fs w fp + w.rows.length := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  have := List.mem_range.mp hi
  simp only [List.length_cons, List.length_nil]; omega

theorem dvPc1_disj : DisjL (dvPc1 fs w fp) := by
  unfold DisjL dvPc1
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp fun {a b} h => Or.inl (by simp only [List.length_cons, List.length_nil]; omega)

theorem dvPc2_bound (hrN : w.rows.length ≤ LeanDa.nPad w.rows.length) : ∀ q ∈ dvPc2 fs w fp, dvDx fs fp ≤ q.1 ∧ q.1 + q.2.length ≤ dvDx fs fp + 128 * LeanDa.nPad w.rows.length := by
  intro q hq
  obtain ⟨i, hi, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
  have := List.mem_range.mp hi
  have := List.mem_range.mp hb
  simp only [List.length_cons, List.length_nil]; omega

theorem dvPc2_disj : DisjL (dvPc2 fs w fp) := by
  unfold DisjL dvPc2
  rw [List.pairwise_flatMap]
  refine ⟨fun i hi => ?_, List.pairwise_lt_range.imp_of_mem fun {i i'} hi hi' hii x hx y hy => ?_⟩
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun {a b} h => Or.inl (by simp only [List.length_cons, List.length_nil]; omega)
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hy
    have := List.mem_range.mp hb
    simp only [List.length_cons, List.length_nil]
    omega

theorem dvPc3_bound : ∀ q ∈ dvPc3 fs w fp, dvHx fs w fp ≤ q.1 ∧ q.1 + q.2.length ≤ dvHx fs w fp + 258 := by
  intro q hq
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
  have := List.mem_range.mp hb
  simp only [List.length_cons, List.length_nil]; omega

theorem dvPc3_disj : DisjL (dvPc3 fs w fp) := by
  unfold DisjL dvPc3
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp fun {a b} h => Or.inl (by simp only [List.length_cons, List.length_nil]; omega)

theorem dvPc4_bound (cert : String → V → ℕ) (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify") :
    ∀ q ∈ dvPc4 cert fp, fp ≤ q.1 ∧ q.1 + q.2.length ≤ fp + fs "da_verify" := by
  intro q hq
  rw [dvPc4, List.mem_singleton] at hq
  subst hq
  simp only [dvCx, List.length_map, List.length_range]; omega

theorem dvPc4_disj (cert : String → V → ℕ) : DisjL (dvPc4 cert fp) := List.pairwise_singleton _ _

theorem dvPc5_bound : ∀ q ∈ dvPc5 fs w fp, dvBx fs w fp ≤ q.1 ∧ q.1 + q.2.length ≤ dvBx fs w fp + w.rows.length := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  have := List.mem_range.mp hi
  simp only [List.length_cons, List.length_nil]; omega

theorem dvPc5_disj : DisjL (dvPc5 fs w fp) := by
  unfold DisjL dvPc5
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp fun {a b} h => Or.inl (by simp only [List.length_cons, List.length_nil]; omega)

theorem dvPc6_bound : ∀ q ∈ dvPc6 fs w fp, dvAx fs w fp ≤ q.1 ∧ q.1 + q.2.length ≤ dvAx fs w fp + 129 * w.rows.length := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  have := List.mem_range.mp hi
  simp only [List.length_map, List.length_range]; omega

theorem dvPc6_disj : DisjL (dvPc6 fs w fp) := by
  unfold DisjL dvPc6
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp fun {a b} h => Or.inl (by simp only [List.length_map, List.length_range]; omega)

theorem dvPc7_bound : ∀ q ∈ dvPc7 fs w fp, dvTx fs w fp ≤ q.1 ∧ q.1 + q.2.length ≤ dvTx fs w fp + 512 := by
  intro q hq
  have := treeL_within q hq
  have h7 : 4 * 2 ^ 7 = 512 := by norm_num
  omega

theorem dvPc7_disj : DisjL (dvPc7 fs w fp) := treeL_disj

theorem dvPc8_bound : ∀ q ∈ dvPc8 fs w fp, dvWx fs w fp ≤ q.1 ∧ q.1 + q.2.length ≤ dvWx fs w fp + 4 * LeanDa.nPad w.rows.length := by
  intro q hq
  have := treeL_within q hq
  have hN2 : 2 ^ LeanDa.logPad w.rows.length = LeanDa.nPad w.rows.length := rfl
  rw [hN2] at this
  exact this

theorem dvPc8_disj : DisjL (dvPc8 fs w fp) := treeL_disj
end Pieces

section Cols
variable (fs : String → ℕ) (cert : String → V → ℕ) (w : Da.Witness) (fp : ℕ)

/-- The position of column `b`'s words. -/
def dvColStart (b : ℕ) : ℕ :=
  dvColPos fs fp w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length) b

/-- The end of column `b`'s words. -/
def dvColEnd (b : ℕ) : ℕ :=
  dvColStart fs w fp b +
    colTot fs (decide (b < 64)) b w.rows.length (LeanDa.nPad w.rows.length) (LeanDa.logPad w.rows.length)

theorem dvColEnd_sep {b b' : ℕ} (hb : b < b') (hb' : b' < 128) :
    dvColEnd fs w fp b' ≤ dvColStart fs w fp b ∨ dvColEnd fs w fp b ≤ dvColStart fs w fp b' :=
  dvCol_sep fs fp _ _ _ hb hb'

theorem dvColStart_ge (b : ℕ) :
    dvPos90 fs fp w.rows.length (LeanDa.nPad w.rows.length) ≤ dvColStart fs w fp b :=
  dvColPos_ge ..

theorem dvCol_node (b : ℕ) :
    dvColStart fs w fp b ≤ dvNode fs w fp b ∧
      dvNode fs w fp b + 4 * LeanDa.nPad w.rows.length ≤ dvColEnd fs w fp b := by
  unfold dvNode dvColEnd dvColStart colTot at *
  omega

theorem dvCol_lv (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) (b : ℕ) :
    dvNode fs w fp b + 4 * LeanDa.nPad w.rows.length ≤ dvLv fs cert w fp b ∧
      dvLv fs cert w fp b + 256 ≤ dvColEnd fs w fp b := by
  have := hc4 (decide (b = 127))
  unfold dvLv dvNode dvColEnd dvColStart colTot at *
  omega

theorem dvPc9_mem {q : ℕ × List E} (hq : q ∈ dvPc9 fs w fp) :
    ∃ b < 128, dvNode fs w fp b ≤ q.1 ∧ q.1 + q.2.length ≤ dvNode fs w fp b + 4 * LeanDa.nPad w.rows.length := by
  obtain ⟨b, hb, hq⟩ := List.mem_flatMap.mp hq
  have := treeL_within q hq
  have hN2 : 2 ^ LeanDa.logPad w.rows.length = LeanDa.nPad w.rows.length := rfl
  rw [hN2] at this
  exact ⟨b, List.mem_range.mp hb, this⟩

theorem dvPc10_mem {q : ℕ × List E} (hq : q ∈ dvPc10 fs cert w fp) :
    ∃ b < 128, q.1 = dvLv fs cert w fp b ∧ q.2.length ≤ 256 := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hq
  refine ⟨b, List.mem_range.mp hb, rfl, ?_⟩
  unfold daWs; simp

theorem dvPc9_disj : DisjL (dvPc9 fs w fp) := by
  unfold DisjL dvPc9
  rw [List.pairwise_flatMap]
  refine ⟨fun b hb => treeL_disj, List.pairwise_lt_range.imp_of_mem fun {b b'} hb hb' hbb x hx y hy => ?_⟩
  have hb'' := List.mem_range.mp hb'
  have hN2 : 2 ^ LeanDa.logPad w.rows.length = LeanDa.nPad w.rows.length := rfl
  have h1 := treeL_within x hx
  have h2 := treeL_within y hy
  rw [hN2] at h1 h2
  have c1 := dvCol_node fs w fp b
  have c2 := dvCol_node fs w fp b'
  rcases dvColEnd_sep fs w fp hbb hb'' with h | h
  · right; omega
  · left; omega

theorem dvPc10_disj (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) :
    DisjL (dvPc10 fs cert w fp) := by
  unfold DisjL dvPc10
  rw [List.pairwise_map]
  refine List.pairwise_lt_range.imp_of_mem fun {b b'} hb hb' hbb => ?_
  have hb'' := List.mem_range.mp hb'
  have hl : (daWs w b).length ≤ 256 := by unfold daWs; simp
  have hl' : (daWs w b').length ≤ 256 := by unfold daWs; simp
  have c1 := dvCol_lv fs cert w fp hc4 b
  have c2 := dvCol_lv fs cert w fp hc4 b'
  show (dvLv fs cert w fp b) + (daWs w b).length ≤ dvLv fs cert w fp b' ∨
    dvLv fs cert w fp b' + (daWs w b').length ≤ dvLv fs cert w fp b
  have n1 := dvCol_node fs w fp b
  have n2 := dvCol_node fs w fp b'
  rcases dvColEnd_sep fs w fp hbb hb'' with h | h
  · right; omega
  · left; omega

theorem dvPc9_lv (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) :
    ∀ q ∈ dvPc9 fs w fp, ∀ q' ∈ dvPc10 fs cert w fp,
      q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1 := by
  intro q hq q' hq'
  obtain ⟨b, hb, hq1, hq2⟩ := dvPc9_mem fs w fp hq
  obtain ⟨b', hb', hq1', hq2'⟩ := dvPc10_mem fs cert w fp hq'
  have c1 := dvCol_node fs w fp b
  have c2 := dvCol_lv fs cert w fp hc4 b'
  have n2 := dvCol_node fs w fp b'
  rcases lt_trichotomy b b' with h | rfl | h
  · rcases dvColEnd_sep fs w fp h hb' with h | h <;> omega
  · omega
  · rcases dvColEnd_sep fs w fp h hb with h | h <;> omega
end Cols

section Assemble
variable (fs : String → ℕ) (cert : String → V → ℕ) (w : Da.Witness) (fp : ℕ)

/-- **`da_verify`'s own words are pairwise disjoint.** -/
theorem dvLayout_disj (hr1 : 1 ≤ w.rows.length) (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify")
    (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) : DisjL (dvLayout fs cert w fp) := by
  rw [dvLayout_eq]
  have hrN : w.rows.length ≤ LeanDa.nPad w.rows.length := ((logPad_iff hr1).mp rfl).1
  have hDx : dvDx fs fp = fp + fs "da_verify" := rfl
  have hPx : dvPx fs w fp = dvDx fs fp + 128 * LeanDa.nPad w.rows.length := rfl
  have hHx : dvHx fs w fp = dvPx fs w fp + w.rows.length := rfl
  have hAx : dvAx fs w fp = dvHx fs w fp + 258 := rfl
  have hBx : dvBx fs w fp = dvAx fs w fp + 129 * w.rows.length := rfl
  have hTx : dvTx fs w fp = dvBx fs w fp + w.rows.length := rfl
  have hWx : dvWx fs w fp = dvTx fs w fp + 512 := rfl
  have h90 : dvWx fs w fp + 4 * LeanDa.nPad w.rows.length ≤
      dvPos90 fs fp w.rows.length (LeanDa.nPad w.rows.length) := by
    unfold dvPos90 dvK0
    simp only [dvSizes, List.sum_cons, List.sum_nil]
    omega
  have b1 := dvPc1_bound fs w fp
  have b2 := dvPc2_bound fs w fp hrN
  have b3 := dvPc3_bound fs w fp
  have b4 := dvPc4_bound fs fp cert hc20
  have b5 := dvPc5_bound fs w fp
  have b6 := dvPc6_bound fs w fp
  have b7 := dvPc7_bound fs w fp
  have b8 := dvPc8_bound fs w fp
  have b9 : ∀ q ∈ dvPc9 fs w fp, dvPos90 fs fp w.rows.length (LeanDa.nPad w.rows.length) ≤ q.1 := by
    intro q hq
    obtain ⟨b, hb, h1, -⟩ := dvPc9_mem fs w fp hq
    have := dvCol_node fs w fp b
    have := dvColStart_ge fs w fp b
    omega
  have b10 : ∀ q ∈ dvPc10 fs cert w fp, dvPos90 fs fp w.rows.length (LeanDa.nPad w.rows.length) ≤ q.1 := by
    intro q hq
    obtain ⟨b, hb, h1, -⟩ := dvPc10_mem fs cert w fp hq
    have := dvCol_node fs w fp b
    have := dvCol_lv fs cert w fp hc4 b
    have := dvColStart_ge fs w fp b
    omega

  have d1 := dvPc1_disj fs w fp
  have d2 := dvPc2_disj fs w fp
  have d3 := dvPc3_disj fs w fp
  have d4 := dvPc4_disj fp cert
  have d5 := dvPc5_disj fs w fp
  have d6 := dvPc6_disj fs w fp
  have d7 := dvPc7_disj fs w fp
  have d8 := dvPc8_disj fs w fp
  have d9 := dvPc9_disj fs w fp
  have d10 := dvPc10_disj fs cert w fp hc4

  have x1 : ∀ q ∈ dvPc1 fs w fp, ∀ q' ∈ dvPc2 fs w fp,
      q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1 := by
    intro q hq q' hq'
    have h' := b2 q' hq'
    have := b1 q hq; omega
  have x2 : ∀ q ∈ dvPc1 fs w fp ++ dvPc2 fs w fp, ∀ q' ∈ dvPc3 fs w fp,
      q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1 := by
    intro q hq q' hq'
    have h' := b3 q' hq'
    simp only [List.mem_append] at hq
    rcases hq with h1 | h2
    · have := b1 q h1; omega
    · have := b2 q h2; omega
  have x3 : ∀ q ∈ dvPc1 fs w fp ++ dvPc2 fs w fp ++ dvPc3 fs w fp, ∀ q' ∈ dvPc4 cert fp,
      q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1 := by
    intro q hq q' hq'
    have h' := b4 q' hq'
    simp only [List.mem_append] at hq
    rcases hq with (h1 | h2) | h3
    · have := b1 q h1; omega
    · have := b2 q h2; omega
    · have := b3 q h3; omega
  have x4 : ∀ q ∈ dvPc1 fs w fp ++ dvPc2 fs w fp ++ dvPc3 fs w fp ++ dvPc4 cert fp, ∀ q' ∈ dvPc5 fs w fp,
      q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1 := by
    intro q hq q' hq'
    have h' := b5 q' hq'
    simp only [List.mem_append] at hq
    rcases hq with ((h1 | h2) | h3) | h4
    · have := b1 q h1; omega
    · have := b2 q h2; omega
    · have := b3 q h3; omega
    · have := b4 q h4; omega
  have x5 : ∀ q ∈ dvPc1 fs w fp ++ dvPc2 fs w fp ++ dvPc3 fs w fp ++ dvPc4 cert fp ++ dvPc5 fs w fp, ∀ q' ∈ dvPc6 fs w fp,
      q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1 := by
    intro q hq q' hq'
    have h' := b6 q' hq'
    simp only [List.mem_append] at hq
    rcases hq with (((h1 | h2) | h3) | h4) | h5
    · have := b1 q h1; omega
    · have := b2 q h2; omega
    · have := b3 q h3; omega
    · have := b4 q h4; omega
    · have := b5 q h5; omega
  have x6 : ∀ q ∈ dvPc1 fs w fp ++ dvPc2 fs w fp ++ dvPc3 fs w fp ++ dvPc4 cert fp ++ dvPc5 fs w fp ++ dvPc6 fs w fp, ∀ q' ∈ dvPc7 fs w fp,
      q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1 := by
    intro q hq q' hq'
    have h' := b7 q' hq'
    simp only [List.mem_append] at hq
    rcases hq with ((((h1 | h2) | h3) | h4) | h5) | h6
    · have := b1 q h1; omega
    · have := b2 q h2; omega
    · have := b3 q h3; omega
    · have := b4 q h4; omega
    · have := b5 q h5; omega
    · have := b6 q h6; omega
  have x7 : ∀ q ∈ dvPc1 fs w fp ++ dvPc2 fs w fp ++ dvPc3 fs w fp ++ dvPc4 cert fp ++ dvPc5 fs w fp ++ dvPc6 fs w fp ++ dvPc7 fs w fp, ∀ q' ∈ dvPc8 fs w fp,
      q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1 := by
    intro q hq q' hq'
    have h' := b8 q' hq'
    simp only [List.mem_append] at hq
    rcases hq with (((((h1 | h2) | h3) | h4) | h5) | h6) | h7
    · have := b1 q h1; omega
    · have := b2 q h2; omega
    · have := b3 q h3; omega
    · have := b4 q h4; omega
    · have := b5 q h5; omega
    · have := b6 q h6; omega
    · have := b7 q h7; omega
  have x8 : ∀ q ∈ dvPc1 fs w fp ++ dvPc2 fs w fp ++ dvPc3 fs w fp ++ dvPc4 cert fp ++ dvPc5 fs w fp ++ dvPc6 fs w fp ++ dvPc7 fs w fp ++ dvPc8 fs w fp, ∀ q' ∈ dvPc9 fs w fp,
      q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1 := by
    intro q hq q' hq'
    have h' := b9 q' hq'
    simp only [List.mem_append] at hq
    rcases hq with ((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8
    · have := b1 q h1; omega
    · have := b2 q h2; omega
    · have := b3 q h3; omega
    · have := b4 q h4; omega
    · have := b5 q h5; omega
    · have := b6 q h6; omega
    · have := b7 q h7; omega
    · have := b8 q h8; omega
  have x9 : ∀ q ∈ dvPc1 fs w fp ++ dvPc2 fs w fp ++ dvPc3 fs w fp ++ dvPc4 cert fp ++ dvPc5 fs w fp ++ dvPc6 fs w fp ++ dvPc7 fs w fp ++ dvPc8 fs w fp ++ dvPc9 fs w fp, ∀ q' ∈ dvPc10 fs cert w fp,
      q.1 + q.2.length ≤ q'.1 ∨ q'.1 + q'.2.length ≤ q.1 := by
    intro q hq q' hq'
    have h' := b10 q' hq'
    simp only [List.mem_append] at hq
    rcases hq with (((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9
    · have := b1 q h1; omega
    · have := b2 q h2; omega
    · have := b3 q h3; omega
    · have := b4 q h4; omega
    · have := b5 q h5; omega
    · have := b6 q h6; omega
    · have := b7 q h7; omega
    · have := b8 q h8; omega
    · exact dvPc9_lv fs cert w fp hc4 q h9 q' hq'
  exact (disjL_append2 (disjL_append2 (disjL_append2 (disjL_append2 (disjL_append2 (disjL_append2 (disjL_append2 (disjL_append2 (disjL_append2 d1 d2 x1) d3 x2) d4 x3) d5 x4) d6 x5) d7 x6) d8 x7) d9 x8) d10 x9)
end Assemble

/-! ## `da_verify`, complete uniformly -/

/-- `da_verify`'s precondition: the squares table, and a witness opening the returned claim. -/
def DaPre (rd : Reader) : List E → List E → Prop
  | [gsq], [r0, r1, v0, v1] => SquaresAt rd gsq ∧ ∃ (root vd : Digest) (w : Da.Witness),
      w.Opens root vd ∧ (r0, r1) = digestScalars root ∧ (v0, v1) = digestScalars vd
  | _, _ => False

theorem daPre_shape {rd : Reader} {args rets : List E} (h : DaPre rd args rets) :
    ∃ gsq r0 r1 v0 v1, args = [gsq] ∧ rets = [r0, r1, v0, v1] := by
  unfold DaPre at h
  split at h
  · exact ⟨_, _, _, _, _, rfl, rfl⟩
  · exact h.elim

/-- **`da_verify` is complete, uniformly placed**, on a memory defined below `2^κ`, `κ ≥ 16`, when
its counters' run and the vector cells' weight runs fit their frames. -/
theorem da_verify_completeRel (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify")
    (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) :
    CompleteRel fs cert κ "da_verify" DaPre := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨gsq, r0, r1, v0, v1, rfl, rfl⟩ := daPre_shape (hpre rd1 hl1 hL1)
  obtain ⟨-, root, vd, w, hw, hr, hv⟩ := hpre rd1 hl1 hL1
  have hlp : LeanDa.logPad w.rows.length < 16 := by have := logPad_le hw.2.1; omega
  have hR := forced_load (p := gsq * gen ^ LeanDa.logPad w.rows.length) (k := 0)
    (v := gen ^ 2 ^ LeanDa.logPad w.rows.length) (fun rd hl hL => by
      have := (hpre rd hl hL).1 _ hlp
      exact (LeanVM.Guest.B1.Digest.loadHolds_mul_gen_pow _ _ _ _).mpr (by rwa [Nat.add_zero])) hl1 hL1
  refine ⟨dvTot fs w.rows.length, dvLayout fs cert w fp, _, [], ⟨rfl, rfl⟩,
    by rw [List.nil_append]; exact dvLayout_within fs cert fp hw.1 hc20 hc4, fun rd hl hL => ?_⟩
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLi⟩ := Main.memL_append.mp hL
  have hlow : Low16 rd := fun i hi => hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  have h := (dv_relAtIn fs cert hlow (hpre rd hl hLi).1 hw hR fp (daMem_of_memL hLo fun q hq => hq)).toRelAtIn
  rw [show r0 = (digestScalars root).1 from congrArg Prod.fst hr,
    show r1 = (digestScalars root).2 from congrArg Prod.snd hr,
    show v0 = (digestScalars vd).1 from congrArg Prod.fst hv,
    show v1 = (digestScalars vd).2 from congrArg Prod.snd hv]
  exact LeanVM.Guest.B1.relAtIn_dmono h fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq

/-- **`da_verify` is complete, uniformly placed**, on a memory defined below `2^κ`, `κ ≥ 16`, when
its counters' run and the vector cells' weight runs fit their frames. -/
theorem da_verify_completeRelD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify")
    (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) :
    CompleteRelD fs cert κ "da_verify" DaPre := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨gsq, r0, r1, v0, v1, rfl, rfl⟩ := daPre_shape (hpre rd1 hl1 hL1)
  obtain ⟨-, root, vd, w, hw, hr, hv⟩ := hpre rd1 hl1 hL1
  have hlp : LeanDa.logPad w.rows.length < 16 := by have := logPad_le hw.2.1; omega
  have hR := forced_load (p := gsq * gen ^ LeanDa.logPad w.rows.length) (k := 0)
    (v := gen ^ 2 ^ LeanDa.logPad w.rows.length) (fun rd hl hL => by
      have := (hpre rd hl hL).1 _ hlp
      exact (LeanVM.Guest.B1.Digest.loadHolds_mul_gen_pow _ _ _ _).mpr (by rwa [Nat.add_zero])) hl1 hL1
  refine ⟨dvTot fs w.rows.length, dvLayout fs cert w fp, _, [], ⟨rfl, rfl⟩,
    by rw [List.nil_append]; exact dvLayout_within fs cert fp hw.1 hc20 hc4,
    by rw [List.nil_append]; exact dvLayout_disj fs cert w fp hw.1 hc20 hc4, fun rd hl hL => ?_⟩
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLi⟩ := Main.memL_append.mp hL
  have hlow : Low16 rd := fun i hi => hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  have h := (dv_relAtIn fs cert hlow (hpre rd hl hLi).1 hw hR fp (daMem_of_memL hLo fun q hq => hq)).toRelAtIn
  rw [show r0 = (digestScalars root).1 from congrArg Prod.fst hr,
    show r1 = (digestScalars root).2 from congrArg Prod.snd hr,
    show v0 = (digestScalars vd).1 from congrArg Prod.fst hv,
    show v1 = (digestScalars vd).2 from congrArg Prod.snd hv]
  exact LeanVM.Guest.B1.relAtIn_dmono h fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq

/-- `da_verify`'s precondition returning `root` and `vd`. -/
def DaPreAt (root vd : Digest) (rd : Reader) : List E → List E → Prop
  | [gsq], [r0, r1, v0, v1] => SquaresAt rd gsq ∧ (r0, r1) = digestScalars root ∧ (v0, v1) = digestScalars vd
  | _, _ => False

/-- **`da_verify` is complete, uniformly placed**, returning the claim a witness opens. -/
theorem da_verify_completeRelAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify")
    (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) (wt : Da.Witness) (root vd : Digest)
    (hw : wt.Opens root vd) : CompleteRel fs cert κ "da_verify" (DaPreAt root vd) :=
  completeRel_mono (da_verify_completeRel fs cert hκ hc20 hc4) fun rd args rets h => by
    unfold DaPreAt at h
    split at h
    · obtain ⟨hT, hr, hv⟩ := h
      exact ⟨hT, root, vd, wt, hw, hr, hv⟩
    · exact h.elim

/-- **`da_verify` is complete, uniformly placed**, returning the claim a witness opens. -/
theorem da_verify_completeRelAtD (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify")
    (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) (wt : Da.Witness) (root vd : Digest)
    (hw : wt.Opens root vd) : CompleteRelD fs cert κ "da_verify" (DaPreAt root vd) :=
  completeRel_monoD (da_verify_completeRelD fs cert hκ hc20 hc4) fun rd args rets h => by
    unfold DaPreAt at h
    split at h
    · obtain ⟨hT, hr, hv⟩ := h
      exact ⟨hT, root, vd, wt, hw, hr, hv⟩
    · exact h.elim

/-- **`da_verify` is complete, uniformly placed**, returning the claim a witness opens, by a tree of
`dvTot` words weighing at most its words at every frame weight. -/
theorem da_verify_completeRelAtW (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 16 ≤ κ)
    (hc20 : cert "da_verify" (.n 20) + 385 ≤ fs "da_verify")
    (hc4 : ∀ f, cert (vxName f) (.n 4) + 256 ≤ fs (vxName f)) (w : Da.Witness) (root vd : Digest)
    (hw : w.Opens root vd) :
    ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef κ rd → MemL rd Lin → DaPreAt root vd rd args rets) →
      LeanVM.Guest.B1.Main.CompleteAtW fs cert wId κ "da_verify" Lin args (Returns rets) (dvTot fs w.rows.length)
        fun θ => dvTot θ w.rows.length := by
  intro args rets Lin hpre fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  have hsh : ∃ gsq r0 r1 v0 v1, args = [gsq] ∧ rets = [r0, r1, v0, v1] := by
    have h := hpre rd1 hl1 hL1
    unfold DaPreAt at h
    split at h
    · exact ⟨_, _, _, _, _, rfl, rfl⟩
    · exact h.elim
  obtain ⟨gsq, r0, r1, v0, v1, rfl, rfl⟩ := hsh
  obtain ⟨-, hr, hv⟩ := hpre rd1 hl1 hL1
  have hlp : LeanDa.logPad w.rows.length < 16 := by have := logPad_le hw.2.1; omega
  have hR := forced_load (p := gsq * gen ^ LeanDa.logPad w.rows.length) (k := 0)
    (v := gen ^ 2 ^ LeanDa.logPad w.rows.length) (fun rd hl hL => by
      have := (hpre rd hl hL).1 _ hlp
      exact (LeanVM.Guest.B1.Digest.loadHolds_mul_gen_pow _ _ _ _).mpr (by rwa [Nat.add_zero])) hl1 hL1
  refine ⟨dvTot fs w.rows.length, dvLayout fs cert w fp, _, [], ⟨rfl, rfl⟩,
    by rw [List.nil_append]; exact dvLayout_within fs cert fp hw.1 hc20 hc4,
    by rw [List.nil_append]; exact dvLayout_disj fs cert w fp hw.1 hc20 hc4, le_rfl, fun rd hl hL => ?_⟩
  rw [List.nil_append] at hL
  obtain ⟨hLo, hLi⟩ := Main.memL_append.mp hL
  have hlow : Low16 rd := fun i hi => hl i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hκ))
  have h := dv_relAtIn fs cert hlow (hpre rd hl hLi).1 hw hR fp (daMem_of_memL hLo fun q hq => hq)
  rw [show r0 = (digestScalars root).1 from congrArg Prod.fst hr,
    show r1 = (digestScalars root).2 from congrArg Prod.snd hr,
    show v0 = (digestScalars vd).1 from congrArg Prod.fst hv,
    show v1 = (digestScalars vd).2 from congrArg Prod.snd hv]
  exact h.dmono fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq

end
end LeanVM.Guest.B1.Digest
