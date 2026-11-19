module

public import NativeVm.Code.Phase3.FormsEval

/-!
# The bus forms of a side: the padding row

`zeroLoop_spec`: `rcx` words from `rax` zeroed. `padCode_spec`: the padding row's lanes from word
`padOff` (`PadAt`): `124` words zeroed, `Keccak.permute` run on the `84` from word `padOff + 40` (the
zero state's lanes become `keccakF1600`'s, `padOut`), its other scratch words zeroed again.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript Native.Keccak Native.Keccak.Proof
  LeanVM.Semantics

variable {w ctx : UInt64} {s : QState} {E : QState → Prop}

/-- **`n` words from word `a` zeroed.** -/
theorem zeroLoop_spec {a n : Nat} (hax : s.reg .rax = wd w a) (hcx : s.reg .rcx = n.toUInt64)
    (hb : a + n < 2 ^ 61) (hdom : ∀ k < n, (s.mem (wd w (a + k))).isSome) :
    WP zeroLoop s (fun s' ↦ (∀ k < n, s'.mem (wd w (a + k)) = some 0) ∧
      KeepS w (fun k ↦ a ≤ k ∧ k < a + n) s.mem s'.mem ∧ RegsFrame [.rax, .rcx] s s') E := by
  unfold zeroLoop
  refine WP.loop (fun t ↦ ∃ j ≤ n, t.reg .rax = wd w (a + j) ∧ t.reg .rcx = (n - j).toUInt64 ∧
      (∀ k < j, t.mem (wd w (a + k)) = some 0) ∧ KeepS w (fun k ↦ a ≤ k ∧ k < a + n) s.mem t.mem ∧
      RegsFrame [.rax, .rcx] s t ∧ ∀ k < n, (t.mem (wd w (a + k))).isSome)
    (fun t ↦ (t.reg .rcx).toNat)
    ⟨0, by omega, by rw [hax]; rfl, by rw [hcx]; rfl, fun k hk ↦ absurd hk (by omega), KeepS.refl _ _,
      fun _ _ ↦ rfl, hdom⟩ ?_ ?_
  · rintro t ⟨j, hj, a1, a2, a3, aK, aR, aD⟩ hc
    have hjn : j < n := by
      rw [cond_ne, a2, rhs_imm, fs_toUInt64_ne_zero (by omega)] at hc
      simp only [decide_eq_true_eq] at hc
      omega
    refine stiw (w := w) (j := a + j) (k := 0) a1 (by rw [Nat.add_zero]; exact aD j hjn) ?_
    refine wp_reg rfl (wp_reg rfl (wp_done ⟨⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩))
    · rsimp; rw [a1, wd_add8, Nat.add_assoc]
    · rsimp; rw [a2, sub_one_toUInt64 (by omega), Nat.sub_sub]
    · intro k hk
      mem_simp
      rcases (show k < j ∨ k = j by omega) with h | rfl
      · rw [setMem_wd_ne _ _ (by omega) (by omega) (by omega)]; exact a3 k h
      · rw [setMem_wd_eq _ _ (by omega)]
    · exact KeepS.setMem aK (k := a + j + 0) ⟨by omega, by omega⟩ _
    · rfx; exact aR
    · intro k hk
      rsimp
      rw [QState.setMem_mem]
      split
      · rfl
      · exact aD k hk
    · rsimp
      rw [a2, sub_one_toUInt64 (by omega), NativeVm.Transcript.toNat_toUInt64 (by omega),
        NativeVm.Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro t ⟨j, hj, -, a2, a3, aK, aR, -⟩ hc
    have hjn : j = n := by
      rw [cond_ne, a2, rhs_imm, fs_toUInt64_ne_zero (by omega)] at hc
      simp only [decide_eq_false_iff_not, not_not] at hc
      omega
    subst hjn
    exact ⟨a3, aK, aR⟩

theorem lane_zero (i : Nat) : Keccak.lane (Vector.replicate 25 0) i = 0 := by
  rw [Keccak.lane, Vector.toArray_replicate, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem scratchAddr_wd (a k : Nat) : scratchAddr (wd w a) k = wd w (a + k) := wd_add w a k

theorem keep_of_scrFrame {m m' : UInt64 → Option UInt64} {a : Nat} (h : ScrFrame (wd w a) 0 84 m m') :
    KeepS w (fun k ↦ a ≤ k ∧ k < a + 84) m m' :=
  fun x hx ↦ h x fun k _ hk e ↦ hx (a + k) ⟨by omega, by omega⟩ (e.trans (scratchAddr_wd a k))

/-- **The padding row**, from word `padOff`. -/
theorem padCode_spec (hrdi : s.reg .rdi = ctx) (hwp : s.mem (wd ctx ctxWork) = some w)
    (hcw : ∀ k < dataEnd, wd ctx ctxWork ≠ wd w k)
    (hdom : ∀ k < 124, (s.mem (wd w (padOff + k))).isSome) :
    WP padCode s (fun s' ↦ s'.reg .rdi = ctx ∧ PadAt s'.mem w ∧
      KeepS w (fun k ↦ padOff ≤ k ∧ k < padOff + 124) s.mem s'.mem) E := by
  have v1 := padOff_val
  have v2 := dataEnd_eq
  unfold padCode
  refine wk_wp hrdi hwp ?_
  refine lea0 (w := w) (k := padOff) (by rsimp) ?_
  refine wp_reg rfl ?_
  refine wp_then' (zeroLoop_spec (E := E) (w := w) (a := padOff) (n := 124) (by rsimp) (by rsimp)
    (by omega) hdom) fun s1 ⟨z1, k1, r1⟩ d1 ↦ ?_
  have r1di : s1.reg .rdi = ctx := by rw [r1 .rdi (by decide)]; rsimp; exact hrdi
  have r1w : s1.reg .r11 = w := by rw [r1 .r11 (by decide)]; rsimp
  refine wp_reg rfl ?_
  refine lea0 (w := w) (k := padOff + 40) (by rsimp; exact r1w) ?_
  refine wp_then' (permute_spec (base := wd w (padOff + 40)) (A := Vector.replicate 25 0) (by rsimp)
    (fun k hk ↦ by
      have hk' : k < 84 := hk
      rw [scratchAddr_wd]; rsimp; rw [d1, Nat.add_assoc]; exact hdom (40 + k) (by omega))
    (fun t ht ↦ by
      rw [scratchAddr_wd, lane_zero, Nat.zero_add, Nat.add_assoc]
      exact z1 (40 + t) (by omega))) fun s2 ⟨_, r2, f2, w2⟩ d2 ↦ ?_
  have k2 := keep_of_scrFrame f2
  have r2di : s2.reg .r15 = ctx := by rw [r2 .r15 (by decide)]; rsimp; exact r1di
  have c2 : s2.mem (wd ctx ctxWork) = some w := by
    exact (k2 _ fun k hk ↦ hcw k (by omega)).trans ((k1 _ fun k hk ↦ hcw k (by omega)).trans hwp)
  refine wp_reg rfl ?_
  refine wk_wp (by rsimp; exact r2di) c2 ?_
  refine lea0 (w := w) (k := padOff + 65) (by rsimp) ?_
  refine wp_reg rfl ?_
  refine WP.mono (zeroLoop_spec (E := E) (w := w) (a := padOff + 65) (n := 59) (by rsimp) (by rsimp)
    (by omega) (fun k hk ↦ by
      rsimp
      exact (d2 _).trans ((d1 _).trans (by rw [Nat.add_assoc]; exact hdom (65 + k) (by omega)))))
    (fun s3 ⟨z3, k3, r3⟩ ↦ ⟨?_, fun a ha ↦ ?_, ?_⟩) (fun _ h ↦ h)
  · rw [r3 .rdi (by decide)]; rsimp; exact r2di
  · unfold Pv
    by_cases h65 : 65 ≤ a
    · have := z3 (a - 65) (by omega)
      rw [show padOff + 65 + (a - 65) = padOff + a by omega] at this
      rw [this, iteF (by omega)]
    · rw [k3.word (by omega) fun j hj ↦ ⟨by omega, by omega⟩]
      rsimp
      by_cases h40 : 40 ≤ a
      · have := w2 (a - 40) (by omega)
        rw [Nat.zero_add, scratchAddr_wd, show padOff + 40 + (a - 40) = padOff + a by omega] at this
        rw [this, iteT ⟨h40, by omega⟩]
        rfl
      · have e1 := k2.word (k := padOff + a) (by omega) fun j hj ↦ ⟨by omega, by omega⟩
        rw [iteF (by omega)]
        exact e1.trans (z1 a (by omega))
  · have k2' : KeepS w (fun k ↦ padOff + 40 ≤ k ∧ k < padOff + 40 + 84) s1.mem s2.mem := k2
    have k3' : KeepS w (fun k ↦ padOff + 65 ≤ k ∧ k < padOff + 65 + 59) s2.mem s3.mem := k3
    exact (k1.trans k2' (fun k h ↦ h) (fun k h ↦ ⟨by omega, by omega⟩)).trans k3' (fun k h ↦ h)
      (fun k h ↦ ⟨by omega, by omega⟩)

end NativeVm.Code.P3
