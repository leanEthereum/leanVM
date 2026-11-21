module

public import NativeVm.Code.Phase3.LayoutFill
public import NativeVm.Code.Phase3.LayoutMath

/-!
# Phase 3's placements: the offsets

`offsInner_spec`: `r8 := cSum sz kr n`, the sizes `2^sz j` of the placements whose key exceeds `kr`
(in `rbx`); `offsC_spec`: each placement's offset at word `po + 2 i + 1`, and the total in `rsi`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript

variable {s : QState} {E : QState → Prop}

theorem key_word {a j : Nat} (ha : a ≤ 30) (hj : j < 64) (x : UInt64) (hx : x = (2 * j).toUInt64) :
    a.toUInt64 <<< (10 : UInt64) + 1023 - x = (a * 1024 + 1023 - 2 * j).toUInt64 := by
  rw [hx, show (10 : UInt64) = (10 : Nat).toUInt64 from rfl, key_eq (by omega) (by omega)]

theorem offsInner_spec {p : UInt64} {po n kr : Nat} {sz : Nat → Nat}
    (hn : n ≤ 64) (hkr : kr < 2 ^ 64) (h15 : s.reg .r15 = p) (hbx : s.reg .rbx = kr.toUInt64)
    (hsz : ∀ j < n, s.mem (wd p (po + 2 * j)) = some (sz j).toUInt64) (hb : ∀ j < n, sz j ≤ 30) :
    WP (offsInner po n) s (fun s' ↦ s'.reg .r8 = (cSum sz kr n).toUInt64 ∧ s'.mem = s.mem ∧
      RegsFrame [.rax, .rcx, .rdx, .r8, .r13] s s') E := by
  have htot : ∀ m ≤ n, cSum sz kr m < 2 ^ 37 := fun m hm ↦ by
    have := cSum_le sz kr m
    have h2 := tSum_le (fun j ↦ if j < n then sz j else 0) 30
      (fun j ↦ by split; exact hb j ‹_›; omega) m
    have e : tSum (fun j ↦ if j < n then sz j else 0) m = tSum sz m := by
      unfold tSum
      exact List.foldl_ext _ _ _ fun acc j hj ↦ by
        have : j < n := by have := List.mem_range.mp hj; omega
        simp only [this, ↓reduceIte]
    omega
  simp only [offsInner, keyC, List.cons_append, List.nil_append]
  fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun u ↦ ∃ j ≤ n, u.reg .r13 = (2 * j).toUInt64 ∧
      u.reg .r8 = (cSum sz kr j).toUInt64 ∧ u.mem = s.mem ∧ RegsFrame [.rax, .rcx, .rdx, .r8, .r13] s u)
    (fun u ↦ n - (u.reg .r13).toNat / 2)
  · exact ⟨0, by omega, by rsimp; rfl, by rsimp; rfl, by rsimp, by rf_tac⟩
  · rintro u ⟨j, hj, h13, h8, hm, hf⟩ hc
    rw [cmp_ne_lit (a := 2 * j) (by omega) (by omega) h13] at hc
    have hjn : j < n := by simp at hc; omega
    have h15' : u.reg .r15 = p := by rw [hf .r15 (by decide)]; exact h15
    have hbx' : u.reg .rbx = kr.toUInt64 := by rw [hf .rbx (by decide)]; exact hbx
    have a1 := eval_aI (s := u) (k := po) h15' h13
    rw [show 2 * j + po = po + 2 * j by omega] at a1
    refine wp_load a1 (by rw [hm]; exact hsz j hjn) ?_
    fstep; fstep; fstep; fstep
    have hkey : (sz j).toUInt64 <<< 10 + 1023 - u.reg .r13 = (keyS sz j).toUInt64 :=
      key_word (hb j hjn) (by omega) _ h13
    have hkb : keyS sz j < 2 ^ 64 := by unfold keyS; have := hb j hjn; omega
    have hs := htot (j + 1) (by omega)
    rw [cSum_succ] at hs
    have hpow := one_shl (a := sz j) (by have := hb j hjn; omega)
    refine WP.blk_cons (wp_ite_of (cmp_ltu_reg hkr hkb (by rsimp; exact hbx') (by rsimp; exact hkey))
      (fun ht ↦ ?_) (fun he ↦ ?_))
    · have hlt : kr < keyS sz j := of_decide_eq_true ht
      fstep; fstep; fstep; fstep
      apply WP.blk_nil
      fstep; fdone
      refine ⟨⟨j + 1, by omega, ?_, ?_, hm, ?_⟩, ?_⟩
      · rw [h13, toUInt64_add_two]; congr 1
      · rw [hpow, h8, toUInt64_add, cSum_succ, cStep]; simp only [hlt, ↓reduceIte]
      · rf_tac; exact hf
      · rw [h13, toUInt64_add_two, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
        omega
    · have hlt : ¬ kr < keyS sz j := of_decide_eq_false he
      apply WP.blk_nil
      fstep; fdone
      refine ⟨⟨j + 1, by omega, ?_, ?_, hm, ?_⟩, ?_⟩
      · rw [h13, toUInt64_add_two]; congr 1
      · rw [h8, cSum_succ, cStep]; simp only [hlt, ↓reduceIte]
      · rf_tac; exact hf
      · rw [h13, toUInt64_add_two, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
        omega
  · rintro u ⟨j, hj, h13, h8, hm, hf⟩ hc
    rw [cmp_ne_lit (a := 2 * j) (by omega) (by omega) h13] at hc
    have hjn : j = n := by simp at hc; omega
    subst hjn
    exact WP.blk_nil ⟨h8, hm, hf⟩

theorem tSum_lt {sz : Nat → Nat} {n : Nat} (hn : n ≤ 64) (hb : ∀ j < n, sz j ≤ 30) :
    ∀ m ≤ n, tSum sz m < 2 ^ 37 := fun m hm ↦ by
  have h2 := tSum_le (fun j ↦ if j < n then sz j else 0) 30
    (fun j ↦ by split; exact hb j ‹_›; omega) m
  have e : tSum (fun j ↦ if j < n then sz j else 0) m = tSum sz m := by
    unfold tSum
    exact List.foldl_ext _ _ _ fun acc j hj ↦ by
      have : j < n := by have := List.mem_range.mp hj; omega
      simp only [this, ↓reduceIte]
  omega

/-- The words `offsC` writes: the offsets. -/
def offsW (po n w : Nat) : Prop := ∃ i < n, w = po + 2 * i + 1

theorem offsC_spec {p : UInt64} {po n : Nat} {sz : Nat → Nat} (hpo : po + 256 < 2 ^ 61)
    (hn : n ≤ 64) (h15 : s.reg .r15 = p)
    (hsz : ∀ j < n, s.mem (wd p (po + 2 * j)) = some (sz j).toUInt64) (hb : ∀ j < n, sz j ≤ 30)
    (hdom : ∀ w < 256, (s.mem (wd p (po + w))).isSome) :
    WP (offsC po n) s (fun s' ↦ s'.reg .r15 = p ∧ s'.reg .rsi = (tSum sz n).toUInt64 ∧
      (∀ i < n, s'.mem (wd p (po + 2 * i + 1)) = some (cSum sz (keyS sz i) n).toUInt64) ∧
      Only (offsW po n) p s.mem s'.mem ∧ (∀ a, (s'.mem a).isSome = (s.mem a).isSome) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r12, .r13] s s') E := by
  have htot := tSum_lt hn hb
  simp only [offsC, keyC, List.cons_append, List.nil_append]
  fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun u ↦ ∃ i ≤ n, u.reg .r12 = (2 * i).toUInt64 ∧
      u.reg .rsi = (tSum sz i).toUInt64 ∧ u.reg .r15 = p ∧
      (∀ i' < i, u.mem (wd p (po + 2 * i' + 1)) = some (cSum sz (keyS sz i') n).toUInt64) ∧
      Only (offsW po i) p s.mem u.mem ∧ (∀ a, (u.mem a).isSome = (s.mem a).isSome) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r12, .r13] s u)
    (fun u ↦ n - (u.reg .r12).toNat / 2)
  · exact ⟨0, by omega, by rsimp; rfl, by rsimp; rfl, by rsimp; exact h15,
      fun i hi ↦ absurd hi (by omega), fun _ _ ↦ rfl, fun _ ↦ rfl, by rf_tac⟩
  · rintro u ⟨i, hi, h12, hsi, h15', hw, ho, hd, hf⟩ hc
    rw [cmp_ne_lit (a := 2 * i) (by omega) (by omega) h12] at hc
    have hin : i < n := by simp at hc; omega
    have hsz' : ∀ j < n, u.mem (wd p (po + 2 * j)) = some (sz j).toUInt64 := fun j hj ↦ by
      rw [ho.word (by omega) fun w ⟨i', hi', e⟩ ↦ ⟨by omega, by omega⟩]; exact hsz j hj
    have a1 := eval_aI (s := u) (k := po) h15' h12
    rw [show 2 * i + po = po + 2 * i by omega] at a1
    refine wp_load a1 (hsz' i hin) ?_
    fstep; fstep; fstep; fstep
    have hkey : (sz i).toUInt64 <<< 10 + 1023 - u.reg .r12 = (keyS sz i).toUInt64 :=
      key_word (hb i hin) (by omega) _ h12
    have hkb : keyS sz i < 2 ^ 64 := by unfold keyS; have := hb i hin; omega
    refine wp_then (offsInner_spec (n := n) (kr := keyS sz i) hn hkb (by rsimp; exact h15')
      (by rsimp; exact hkey) (fun j hj ↦ by rsimp; exact hsz' j hj) hb) fun u₁ ⟨e8, em, ef⟩ ↦ ?_
    have r12 : u₁.reg .r12 = (2 * i).toUInt64 := by rw [ef .r12 (by decide)]; rsimp; exact h12
    have r15 : u₁.reg .r15 = p := by rw [ef .r15 (by decide)]; rsimp; exact h15'
    have rsi : u₁.reg .rsi = (tSum sz i).toUInt64 := by rw [ef .rsi (by decide)]; rsimp; exact hsi
    have a2 := eval_aI (s := u₁) (k := po + 1) r15 r12
    rw [show 2 * i + (po + 1) = po + 2 * i + 1 by omega] at a2
    have hdi : (u₁.mem (wd p (po + 2 * i + 1))).isSome := by
      rw [em]; rsimp; rw [hd]; have := hdom (2 * i + 1) (by omega); rwa [← Nat.add_assoc] at this
    refine wp_store a2 hdi ?_
    have a3 := eval_aI (s := u₁.setMem (wd p (po + 2 * i + 1)) (u₁.reg .r8)) (k := po)
      (by rsimp; exact r15) (by rsimp; exact r12)
    rw [show 2 * i + po = po + 2 * i by omega] at a3
    refine wp_load a3 (by p3wsimp; rw [em]; rsimp; exact hsz' i hin) ?_
    have hpow := one_shl (a := sz i) (by have := hb i hin; omega)
    fstep; fstep; fstep; fstep; fdone
    have hs := htot (i + 1) (by omega)
    rw [tSum_succ] at hs
    refine ⟨⟨i + 1, by omega, ?_, ?_, r15, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [r12, toUInt64_add_two]; congr 1
    · rw [hpow, rsi, toUInt64_add, tSum_succ]
    · intro i' hi'
      by_cases e : i' = i
      · subst e; p3wsimp; rw [e8]
      · p3wsimp; rw [em]; rsimp; exact hw i' (by omega)
    · refine Only.setMem (fun a ha ↦ ?_) ⟨i, by omega, rfl⟩ _
      rw [em]; rsimp; exact ho a fun w ⟨i', hi', e⟩ ↦ ha w ⟨i', by omega, e⟩
    · intro a; rw [dom_setMem hdi, em]; rsimp; exact hd a
    · intro r hr
      have hr' := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8'⟩ := hr'
      have hx : r ∉ [Reg64.rax, Reg64.rcx, Reg64.rdx, Reg64.r8, Reg64.r13] := by simp [*]
      simp only [QState.setReg_reg, QState.setMem_reg, h4, h3, h5, h7, ↓reduceIte, ef r hx, h1, h2]
      exact hf r hr
    · rw [r12, toUInt64_add_two, toNat_toUInt64 (by omega), h12, toNat_toUInt64 (by omega)]
      omega
  · rintro u ⟨i, hi, h12, hsi, h15', hw, ho, hd, hf⟩ hc
    rw [cmp_ne_lit (a := 2 * i) (by omega) (by omega) h12] at hc
    have hin : i = n := by simp at hc; omega
    subst hin
    exact WP.blk_nil ⟨h15', hsi, hw, ho, hd, hf⟩

end NativeVm.Code.P3
