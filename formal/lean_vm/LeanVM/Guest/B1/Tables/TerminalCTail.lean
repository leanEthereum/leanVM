/-
  LeanVM.Guest.B1.Tables.TerminalCTail

  `check_opening_terminal`'s ring switch and check, complete.
-/

module

public import LeanVM.Guest.B1.Tables.TerminalCClaims

/-!
# The ring switch and the check, complete

`c_tpostA` checks `q_flock`'s size and allocates the rows, `c_rinit` checks their first entries,
`c_tpostB` runs `rs_eq_run`, `c_rs` sums the coefficients against the last row, `c_tend` checks
the terminal.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig

@[expose] public section

/-- `x` squared `k` times. -/
def sqI (x : E) : ℕ → E
  | 0 => x
  | k + 1 => sqI x k * sqI x k

theorem sqI_gen (a : ℕ) : ∀ k, sqI (gen ^ a) k = gen ^ (2 ^ k * a)
  | 0 => by simp [sqI]
  | k + 1 => by rw [sqI, sqI_gen a k, ← pow_add, pow_succ]; congr 1; ring

section
variable {C : CallRel} {rd : Reader}

/-- **`q_flock`'s size checked, the rows allocated** (G:2057-2060). -/
theorem c_tpostA (σ : Val) {a6 a10 p1750 : E} (h6 : σ (.n 6) = a6) (h10 : σ (.n 10) = a10)
    (lk : LoadHolds rd a10 5 (a6 * word 256 0 0)) :
    Completes C rd 1737 1751 tPostA σ (fun σ' => σ' (.n 1750) = p1750) := by
  refine completes_upds [(1737, word 256 0 0), (1738, a6 * word 256 0 0), (1739, a6 * word 256 0 0),
    (1740, word 256 0 0), (1741, a6 * word 256 0 0), (1742, word 2 0 0),
    (1743, sqI (a6 * word 256 0 0 * word 2 0 0) 0), (1744, sqI (a6 * word 256 0 0 * word 2 0 0) 1),
    (1745, sqI (a6 * word 256 0 0 * word 2 0 0) 2), (1746, sqI (a6 * word 256 0 0 * word 2 0 0) 3),
    (1747, sqI (a6 * word 256 0 0 * word 2 0 0) 4), (1748, sqI (a6 * word 256 0 0 * word 2 0 0) 5),
    (1749, sqI (a6 * word 256 0 0 * word 2 0 0) 6), (1750, p1750)] (by simp)
    (fun next kret hn => ?_) (by vs_ev)
  simp only [tPostA, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  vs_ev
  rw [h6, h10]
  simp only [true_and]
  exact ⟨lk, e_add_self _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hn⟩

theorem rinit_below : ∀ k < 64, numBelowB (1751 + (k + 1)) (Stmt.valsList (rinitBlk k)) = true := by
  decide +kernel

/-- **The rows' first entries** (G:2059-2060). -/
theorem c_rinit (σ : Val) {p1750 : E} (h : σ (.n 1750) = p1750)
    (h1 : ∀ k < 64, LoadHolds rd p1750 k 1) :
    Completes C rd 1751 1815 ((List.range 64).map rinitBlk).flatten σ (fun _ => True) := by
  have := Completes.flatten (C := C) (rd := rd) (blk := rinitBlk) (st := fun k => 1751 + k)
    (Inv := fun _ σ => σ (.n 1750) = p1750) 64 (fun _ _ => by omega)
    (fun k hk => numBelow_of_B (rinit_below k hk)) (fun k hk σ hσ => ?_) σ h
  · exact this.mono le_rfl le_rfl fun _ _ => trivial
  · refine completes_upds [(1751 + k, word 1 0 0)] (by simp) (fun next kret hn => ?_)
      (by rw [upds_lt (lo := 1751 + k) (by simp) (by omega)]; exact hσ)
    simp only [rinitBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    rw [upds_lt (lo := 1751 + k) (j := 1750) (by simp) (by omega), hσ]
    vs_ev
    rw [word_one]
    exact ⟨trivial, h1 k hk, hn⟩

/-- **`rs_eq_run` and the last row** (G:2061-2062). -/
theorem c_tpostB (σ : Val) {a6 a11 a13 p1750 : E} (h6 : σ (.n 6) = a6) (h11 : σ (.n 11) = a11)
    (h13 : σ (.n 13) = a13) (h1750 : σ (.n 1750) = p1750)
    (hrs : MeaningRsEqRun rd [p1750, a11, a13, a6 * gen ^ 8] []) :
    Completes (coreProgram.Rel rd) rd 1815 1826 tPostB σ
      (fun σ' => σ' (.n 1825) = p1750 * sqI (a6 * word 256 0 0) 6) := by
  refine completes_upds [(1815, word 256 0 0), (1816, a6 * word 256 0 0), (1817, word 256 0 0),
    (1818, sqI (a6 * word 256 0 0) 0), (1819, sqI (a6 * word 256 0 0) 1),
    (1820, sqI (a6 * word 256 0 0) 2), (1821, sqI (a6 * word 256 0 0) 3),
    (1822, sqI (a6 * word 256 0 0) 4), (1823, sqI (a6 * word 256 0 0) 5),
    (1824, sqI (a6 * word 256 0 0) 6), (1825, p1750 * sqI (a6 * word 256 0 0) 6)] (by simp)
    (fun next kret hn => ?_) (by vs_ev)
  simp only [tPostB, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  vs_ev
  rw [h6, h11, h13, h1750]
  simp only [true_and]
  exact ⟨(rs_eq_run_iff _ _ _).mpr (by rw [word_g8]; exact hrs), rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    hn⟩

def rsSt (k : ℕ) : ℕ := if k = 0 then 1826 else 1825 + 4 * k

theorem rs_below : ∀ k < 64, numBelowB (rsSt (k + 1)) (Stmt.valsList (rsBlk k)) = true := by
  decide +kernel

/-- **`Σ c_k · row_k`** (G:2063-2065), over the coefficients and the last row's words. -/
theorem c_rs (σ : Val) {a12 r : E} {cs R : ℕ → E} (h12 : σ (.n 12) = a12) (h1825 : σ (.n 1825) = r)
    (hcs : ∀ k < 64, LoadHolds rd a12 k (cs k)) (hR : ∀ k < 64, LoadHolds rd r k (R k)) :
    Completes C rd 1826 2081 ((List.range 64).map rsBlk).flatten σ (fun _ => True) := by
  have := Completes.flatten (C := C) (rd := rd) (blk := rsBlk) (st := rsSt)
    (Inv := fun _ σ => σ (.n 12) = a12 ∧ σ (.n 1825) = r) 64
    (fun k _ => by unfold rsSt; split <;> split <;> omega)
    (fun k hk => numBelow_of_B (rs_below k hk)) (fun k hk σ ⟨g12, g25⟩ => ?_) σ ⟨h12, h1825⟩
  · exact this.mono le_rfl le_rfl fun _ _ => trivial
  · rcases Nat.eq_zero_or_pos k with rfl | hpos
    · refine completes_upds [(1826, cs 0), (1827, R 0), (1828, cs 0 * R 0)] (by simp [rsSt])
        (fun next kret hn => ?_) ⟨by vs_ev; exact g12, by vs_ev; exact g25⟩
      simp only [rsBlk, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      vs_ev
      rw [g12, g25]
      exact ⟨hcs 0 (by omega), hR 0 (by omega), trivial, hn⟩
    · have hk0 : ¬ k = 0 := by omega
      rw [show rsSt k = 1825 + 4 * k by simp [rsSt, hk0],
        show rsSt (k + 1) = 1825 + 4 * k + 4 by simp [rsSt]; omega]
      set P := σ (.n (if k = 1 then 1828 else 1824 + 4 * k))
      have hl : ∀ p ∈ [(1825 + 4 * k, cs k), (1826 + 4 * k, R k), (1827 + 4 * k, cs k * R k),
          (1828 + 4 * k, P + cs k * R k)], 1825 + 4 * k ≤ p.1 ∧ p.1 < 1825 + 4 * k + 4 := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false]
        rintro p (rfl | rfl | rfl | rfl) <;> dsimp only <;> omega
      refine completes_upds _ hl (fun next kret hn => ?_)
        ⟨by rw [upds_lt (j := 12) (fun p hp => (hl p hp).1) (by omega)]; exact g12,
          by rw [upds_lt (j := 1825) (fun p hp => (hl p hp).1) (by omega)]; exact g25⟩
      simp only [rsBlk, hk0, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      rw [upds_lt (j := 12) (fun p hp => (hl p hp).1) (by omega),
        upds_lt (j := 1825) (fun p hp => (hl p hp).1) (by omega),
        upds_lt (j := if k = 1 then 1828 else 1824 + 4 * k) (fun p hp => (hl p hp).1)
          (by split <;> omega), g12, g25]
      fl_ev
      exact ⟨hcs k hk, hR k hk, trivial, rfl, hn⟩

/-- **The terminal's check** (G:2066-2067). -/
theorem c_tend (σ : Val) {a15 a16 : E} (h15 : σ (.n 15) = a15) (h16 : σ (.n 16) = a16)
    (hv : (σ (.n 1736) + σ (.n 2080) * σ (.n 53)) * a15 = a16) :
    Completes C rd 2081 2084 tEnd σ (fun _ => True) := by
  refine completes_upds [(2081, σ (.n 2080) * σ (.n 53)),
    (2082, σ (.n 1736) + σ (.n 2080) * σ (.n 53)),
    (2083, (σ (.n 1736) + σ (.n 2080) * σ (.n 53)) * a15)] (by simp) (fun next kret hn => ?_) trivial
  simp only [tEnd, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  vs_ev
  rw [h15, h16, hv]
  exact ⟨trivial, trivial, rfl, e_add_self _, hn⟩

end

end
end LeanVM.Guest.B1
