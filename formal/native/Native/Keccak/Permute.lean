module

public import Native.Keccak.Round

/-!
# `Keccak.hash`'s proof: the permutation

`Keccak.permute` writes the round constants at `sRC`, then runs 24 rounds, round `i` with
`rcx = i`: the lanes at `sA` become `keccakF1600` of theirs, and no word outside the scratch area
changes.
-/

@[expose] public section

namespace Native.Keccak.Proof

open LeanVM.Semantics LeanVM.Parameters LeanVM.Fast.Keccak

variable {E : QState → Prop}

/-- Round constant `i`'s piece of `writeRoundConstants`. -/
def rcP (i : Nat) : List Stmt :=
  [I (.movi .rax (keccakRC.getD i 0).toInt64), I (.store (atDi (sRC + 8 * i.toInt64)) .rax)]

theorem writeRoundConstants_eq : writeRoundConstants = blk ((List.range 24).flatMap rcP) := (rfl)

theorem rcP_spec {base : UInt64} {i : Nat} {s : QState} (hrdi : s.reg .rdi = base)
    (hS : (s.mem (scratchAddr base (60 + i))).isSome) :
    WP (blk (rcP i)) s (fun s' ↦
      s'.mem = Function.update s.mem (scratchAddr base (60 + i)) (some (keccakRC.getD i 0)) ∧
      RegsFrame [.rax] s s') E := by
  refine wp_op rfl ?_
  refine wp_store_scr (k := 60 + i) (by simp [hrdi]) (by addr_tac) hS ?_
  refine WP.blk_nil ⟨?_, ?_⟩
  · simp [QState.setMem]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp [hr]

theorem take_foldl_succ (A : KeccakState) {j : Nat} (hj : j < 24) :
    (keccakRC.take (j + 1)).foldl roundLanes A =
      roundLanes ((keccakRC.take j).foldl roundLanes A) (keccakRC.getD j 0) := by
  have hl : j < keccakRC.length := by simpa [keccakRC] using hj
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hl]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- **The permutation**: the lanes at `sA` become `keccakF1600` of theirs. -/
theorem permute_spec {base : UInt64} {A : KeccakState} {s : QState} (hrdi : s.reg .rdi = base)
    (hok : ScrOk s.mem base) (hA : Words s.mem base 0 25 (Keccak.lane A)) :
    WP permute s (fun s' ↦ ScrOk s'.mem base ∧ RegsFrame [.rax, .rcx, .r8] s s' ∧
      ScrFrame base 0 84 s.mem s'.mem ∧ Words s'.mem base 0 25 (Keccak.lane (keccakF1600 A)))
      E := by
  apply WP.blk_cons
  rw [writeRoundConstants_eq]
  refine WP.mono (phase_run rcP 60 24 (fun i ↦ keccakRC.getD i 0) [.rax] (by omega) (by simp)
    (fun j hj s' h1 h2 h3 _ ↦ rcP_spec h1 (h3.isSome (by omega))) hrdi hok) ?_ (fun _ h ↦ h)
  rintro s1 ⟨hok1, hR1, hF1, hRC1⟩
  refine wp_op rfl ?_
  have hA1 := hA.frame hF1 (by omega) (by omega) (by omega)
  refine WP.loop (fun s' ↦ ∃ j ≤ 24, s'.reg .rcx = j.toUInt64 ∧ ScrOk s'.mem base ∧
      RegsFrame [.rax, .rcx, .r8] s s' ∧ ScrFrame base 0 84 s.mem s'.mem ∧
      Words s'.mem base 0 25 (Keccak.lane ((keccakRC.take j).foldl roundLanes A)) ∧
      Words s'.mem base 60 24 (fun i ↦ keccakRC.getD i 0))
    (fun s' ↦ 24 - (s'.reg .rcx).toNat) ?_ ?_ ?_
  · refine ⟨0, by omega, by simp; rfl, hok1, ?_, hF1.widen (by omega) (by omega),
      by simpa using hA1, hRC1⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [QState.setReg_reg, hr.2.1, ↓reduceIte]
    exact hR1 r (by simp [hr.1])
  · rintro s' ⟨j, hj, hrcx, hok', hR', hF', hA', hRC'⟩ hc
    have hj24 : j < 24 := by
      simp only [Cond.eval, Rhs.eval, hrcx, decide_eq_true_eq] at hc
      have := UInt64.lt_iff_toNat_lt.mp hc
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat'] at this
      simp only [i64_lit, UInt64.reduceToNat] at this
      omega
    have hrdi' : s'.reg .rdi = base := (hR' _ (by simp)).trans hrdi
    apply WP.blk_cons
    refine WP.mono (round_spec (rc := keccakRC.getD j 0) hrdi' hok' hA' hrcx
      (by simpa using hRC' j hj24) (by omega)) ?_ (fun _ h ↦ h)
    rintro s3 ⟨hok3, hR3, hF3, hA3⟩
    have hnew : (s3.setReg .rcx (s3.reg .rcx + Int64.toUInt64 1)).reg .rcx = (j + 1).toUInt64 := by
      simp [hR3 .rcx (by simp), hrcx]
      rfl
    refine wp_op rfl (WP.blk_nil ⟨⟨j + 1, by omega, hnew, hok3, ?_, ?_, ?_, ?_⟩, ?_⟩)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [QState.setReg_reg, hr.2.1, ↓reduceIte]
      rw [hR3 r (by simp [hr.1, hr.2.2])]
      exact hR' r (by simp [hr.1, hr.2.1, hr.2.2])
    · exact hF'.trans hF3 (by omega) (by omega)
    · rw [take_foldl_succ A hj24]
      exact hA3
    · exact hRC'.frame hF3 (by omega) (by omega) (by omega)
    · rw [hnew, hrcx, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · rintro s' ⟨j, hj, hrcx, hok', hR', hF', hA', -⟩ hc
    have hj24 : j = 24 := by
      simp only [Cond.eval, Rhs.eval, hrcx, decide_eq_false_iff_not] at hc
      have := mt UInt64.lt_iff_toNat_lt.mpr hc
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat'] at this
      simp only [i64_lit, UInt64.reduceToNat] at this
      omega
    subst hj24
    refine ⟨hok', hR', hF', ?_⟩
    have : keccakRC.take 24 = keccakRC := List.take_of_length_le (by simp [keccakRC])
    rw [this] at hA'
    rw [keccakF1600, round_eq_roundLanes]
    exact hA'

end Native.Keccak.Proof
