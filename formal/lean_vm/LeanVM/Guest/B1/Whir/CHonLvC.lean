/-
  LeanVM.Guest.B1.Whir.CHonLvC

  A non-final level's calls and memory at the honest data, from `OsHA`.
-/

module

public import LeanVM.Guest.B1.Whir.CHonCall
public import LeanVM.Guest.B1.Whir.CHonLvP
public import LeanVM.Guest.B1.Whir.CHonMemLv
public import LeanVM.Guest.B1.Fs.Templates

/-!
# A non-final level's calls, honestly

`midC_of`: under `OsHA` at the honest buffers, level `l < yr`'s calls and memory `MidC` at the
honest data (`LvAt.midW`), from the level's step of the run (`LvAt.NextStep`), the
configuration's facts (`HonStatic`, `HonNames`) and the run facts named as hypotheses.

The pieces: the cursor's words of the level (`segR`, `segF`), the buffers' fixed words
(`fixedAt_own`), the grinds' lanes (`grind_lane`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem rdCell_one (S : KeccakState) : rdCell S 1 = cellsOfState S false 1 := rfl

/-- **A grind's lane** from its proof of work. -/
theorem grind_lane {s : Fs} {bits : ℕ} (hb : bits ≠ 0) {n : E}
    (h : powOk bits (Keccak.lane (s.nonceState n) 2) = true) :
    ((cellsOfState (s.nonceState n) false 1).limb 0).lane.toNat % 2 ^ bits = 0 :=
  (grindOk_iff hb n).mp (Or.inr h)

theorem roundsTr_length : ∀ (n : ℕ) (fs : List E) (cl : E) (xs : List E), fs.length = 5 →
    (roundsTr n fs cl xs).1.length = 5
  | 0, _, _, _, h => h
  | n + 1, _, _, _, _ => roundsTr_length n _ _ _ (roundRets_take_length _ _ _ _)

/-! ## The cursor's words -/

section Cursor

variable {rd : Reader} {c : OsCfg} {b : ℕ} {own : List (List E)} {cur tabs : E} {xs ys : List E}

/-- The words `ys`, a suffix of the cursor's, from their offset. -/
theorem readsAt_suffix (h : ReadsAt rd cur xs) (hs : ys <:+ xs) :
    ReadsAt rd (cur * gen ^ (xs.length - ys.length)) ys := by
  obtain ⟨pre, rfl⟩ := hs
  have := readsAt_shift h pre.length ys.length (by simp)
  rw [List.length_append, Nat.add_sub_cancel]
  rwa [List.drop_left', List.take_of_length_le le_rfl] at this

/-- **`m` words of the suffix `ys` from `k`**, at the cursor. -/
theorem segR (h : ReadsAt rd cur xs) (hs : ys <:+ xs) {k m : ℕ} (hkm : k + m ≤ ys.length) :
    ReadsAt rd (cur * gen ^ (xs.length - ys.length + k)) ((ys.drop k).take m) := by
  have := readsAt_shift (readsAt_suffix h hs) k m hkm
  rwa [mul_gen_pow_add] at this

/-- **`m` words of the suffix `ys` from `k` are fixed.** -/
theorem segF (hs : ys <:+ xs) {k m : ℕ} (hkm : k + m ≤ ys.length) :
    FixedAt c b own cur tabs xs (cur * gen ^ (xs.length - ys.length + k)) m :=
  fixedAt_cur (by have := hs.length_le; omega)

end Cursor

/-! ## The buffers' fixed words -/

namespace OsHD

variable (h : OsHD) {rd : Reader} {b : ℕ} {cur tabs : E} {xs : List E}

theorem own_length {j : ℕ} (hj : j < (osSizesL h.c).length) :
    (h.own.getD j []).length = (osSizesL h.c).getD j 0 := by
  rw [h.own_getD hj, ownAt, fitTo_length]

/-- **A buffer's words are fixed.** -/
theorem fixedAt_own {j o m : ℕ} (hj : j < (osSizesL h.c).length) (hne : j ≠ osIxQbpA)
    (hom : o + m ≤ (osSizesL h.c).getD j 0) :
    FixedAt h.c b h.own cur tabs xs (osPtrA h.c b j * gen ^ o) m :=
  fixedAt_buf hj hne (by rw [h.own_length hj]; exact hom)

theorem fixedAt_own0 {j m : ℕ} (hj : j < (osSizesL h.c).length) (hne : j ≠ osIxQbpA)
    (hom : m ≤ (osSizesL h.c).getD j 0) :
    FixedAt h.c b h.own cur tabs xs (osPtrA h.c b j) m := by
  have := h.fixedAt_own (b := b) (cur := cur) (tabs := tabs) (xs := xs) (o := 0) (m := m) hj hne (by omega)
  simpa using this

/-- The levels' folds within every fold. -/
theorem foldsEnd_le (hS : HonStatic h.c) {l : ℕ} (hl : l < h.c.levels.length) :
    ((h.c.levels.getD l default)).foldsOff + ((h.c.levels.getD l default)).folds ≤ h.c.nFolds := by
  have hyr := hS.yr
  have key : ∀ d, l + d ≤ h.c.yrLevel →
      ((h.c.levels.getD l default)).foldsOff + ((h.c.levels.getD l default)).folds ≤
        ((h.c.levels.getD (l + d) default)).foldsOff + ((h.c.levels.getD (l + d) default)).folds := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      have := ih (by omega)
      rw [show l + (d + 1) = l + d + 1 by omega, hS.fo (l := l + d) (by omega)]
      omega
  have := key (h.c.yrLevel - l) (by omega)
  rw [show l + (h.c.yrLevel - l) = h.c.yrLevel by omega, hS.foT] at this
  exact this

/-! ## The levels' honest values -/

/-- Sample `j` of level `l`'s positions. -/
def word (l j : ℕ) : E := (h.L l).word h.logN j

/-- `λ⁻¹` the queries of level `l` take, `0` at the final level. -/
def lamInv (l : ℕ) : E := if l = h.c.yrLevel then 0 else h.li l

/-- The carried capacity before level `l`, the closing rounds' after the levels. -/
def capAt (l : ℕ) : List E := if l ≤ h.c.yrLevel then (h.L l).cap else (h.Lf.F3 h.logN).cap

/-- The guest's claim before level `l`, after the final level's folds after the levels. -/
def claimAt (l : ℕ) : E := if l ≤ h.c.yrLevel then h.gclAt l else h.cl1F

/-- The words from level `l` on, the closing rounds' after the levels. -/
def xsAt (l : ℕ) : List E := if l ≤ h.c.yrLevel then (h.L l).xs else tailWords h.Lf.fw.pairs


end OsHD

end
end LeanVM.Guest.B1.Whir
