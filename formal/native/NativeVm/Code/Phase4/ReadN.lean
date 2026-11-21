module

public import NativeVm.Code.Phase4.Base

/-!
# `readN`: scalars read into memory

`readN_refines`: `readN` refines `readScalars n`, the scalars at consecutive pairs of words from
`r12`, `n` in `r13`; whatever survives a frame of those words and of the registers it writes
(`readRegs`) is kept.
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript LeanVM.Parameters

/-- The registers `readN` writes. -/
abbrev readRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11, .r12, .r13]

theorem clobbers_sub_readRegs : ∀ r ∈ clobbers, r ∈ readRegs := by decide

variable {env : Env}

/-- One element appended to an array in memory. -/
theorem EWArr.push {mem : UInt64 → Option UInt64} {p : UInt64} {xs : Array EW} {x : EW}
    (h : EWArr mem p xs) (hx : EWAt mem (wd p (2 * xs.size)) x) : EWArr mem p (xs.push x) := by
  intro i hi
  rw [Array.size_push] at hi
  rcases Nat.lt_or_ge i xs.size with h' | h'
  · rw [Array.getElem_push_lt h']; exact h i h'
  · have : i = xs.size := by omega
    subst this
    rw [Array.getElem_push_eq]; exact hx

/-- An array in memory through a store outside it. -/
theorem EWArr.setMem {s : QState} {w : UInt64} {a : Nat} {xs : Array EW}
    (h : EWArr s.mem (wd w a) xs) {k : Nat} (hk : k < 2 ^ 61) (ha : a + 2 * xs.size ≤ 2 ^ 61)
    (hout : k < a ∨ a + 2 * xs.size ≤ k) (v : UInt64) :
    EWArr (s.setMem (wd w k) v).mem (wd w a) xs := by
  intro i hi
  have := h i hi
  unfold EWAt at this ⊢
  rw [wd_wd, wd_wd] at this ⊢
  rw [mem_setMem_wd _ (by omega) hk (by omega), mem_setMem_wd _ (by omega) hk (by omega)]
  exact this

/-- An array of phase 4's words through a transcript gadget. -/
theorem EWArr.keeps (h4 : Env4 env) {s s' : QState} (hk : Keeps clobbers (Foot env) s s') {a : Nat}
    {xs : Array EW} (ha : Transcript.workWords ≤ a) (hb : a + 2 * xs.size ≤ dataEnd)
    (h : EWArr s.mem (wd env.work a) xs) : EWArr s'.mem (wd env.work a) xs := by
  intro i hi
  have := h i hi
  unfold EWAt at this ⊢
  rw [wd_wd, wd_wd] at this ⊢
  rw [hk.mem _ (h4.notFoot _ (by omega) (by omega)), hk.mem _ (h4.notFoot _ (by omega) (by omega))]
  exact this

/-- The body's stores and counters. -/
theorem readN_tail {s : QState} {w : UInt64} {a k n : Nat} (h12 : s.reg .r12 = wd w (a + 2 * k))
    (h13 : s.reg .r13 = (n - k).toUInt64) (hk : k < n) (hl : a + 2 * n < 2 ^ 61)
    (hs0 : (s.mem (wd w (a + 2 * k))).isSome) (hs1 : (s.mem (wd w (a + 2 * k + 1))).isSome) :
    WP (blk [I (.store (at_ .r12 0) .r9), I (.store (at_ .r12 8) .r10), I (.addi .r12 16),
        I (.subi .r13 1)]) s
      (fun s' ↦ s'.mem = ((s.setMem (wd w (a + 2 * k)) (s.reg .r9)).setMem
          (wd w (a + 2 * k + 1)) (s.reg .r10)).mem ∧
        s'.reg .r12 = wd w (a + 2 * (k + 1)) ∧ s'.reg .r13 = (n - (k + 1)).toUInt64)
      fun _ ↦ False := by
  refine wp_store (eval_at0 h12) hs0 ?_
  refine wp_store (eval_at8 (by rw [QState.setMem_reg]; exact h12))
    (by rw [mem_setMem_wd _ (by omega) (by omega) (by omega)]; exact hs1) ?_
  apply WP.blk_cons; apply WP.ins'
  simp only [QInstr.step, QState.setMem_reg]
  apply WP.blk_cons; apply WP.ins'
  simp only [QInstr.step, QState.setReg_reg, QState.setMem_reg, reduceCtorEq, ite_false]
  refine WP.blk_nil ⟨rfl, ?_, ?_⟩
  · simp only [QState.setReg_reg, reduceCtorEq, ite_false, ite_true, h12]
    rw [wd_add16]; congr 1
  · simp only [QState.setReg_reg, reduceCtorEq, ite_false, ite_true, h13]
    exact natSub_toUInt64 hk

/-- **`readN` reads `n` scalars to the words from `a`.** -/
theorem readN_refines (h4 : Env4 env) {a n : Nat} (hm : Mine [⟨a, 2 * n⟩]) {X : QState → Prop}
    (hX : Stab env [⟨a, 2 * n⟩] readRegs X) :
    Refines (fun t s ↦ CodeRel env t s ∧ X s ∧ WS env s ∧ s.reg .r12 = wd env.work a ∧
        s.reg .r13 = n.toUInt64)
      readN (readScalars n)
      (fun xs t s ↦ CodeRel env t s ∧ X s ∧ WS env s ∧ xs.size = n ∧
        EWArr s.mem (wd env.work a) xs) X := by
  rintro t s ⟨hrel, hx, hws, h12, h13⟩
  have hl := dataEnd_lt
  have hma := hm _ (List.mem_singleton_self _)
  simp only [Region.stop] at hma
  rw [tWorkWords_val, dataEnd_val] at hma
  have hn : n < 2 ^ 64 := by omega
  let R : Nat → Array EW → QState → Prop := fun k acc s' ↦
    Fr env [⟨a, 2 * n⟩] readRegs s s' ∧ WS env s' ∧ acc.size = k ∧ k ≤ n ∧
      EWArr s'.mem (wd env.work a) acc ∧ s'.reg .r12 = wd env.work (a + 2 * k) ∧
      s'.reg .r13 = (n - k).toUInt64
  have H := Refines.foldlM (l := List.range n)
    (f := fun acc _ ↦ Model.readScalar >>= fun x ↦ pure (acc.push x))
    (cond := .test false .r13 (.reg .r13))
    (Inv := fun k acc t' s' ↦ CodeRel env t' s' ∧ R k acc s')
    (E := fun s' ↦ Fr env [⟨a, 2 * n⟩] readRegs s s') (init := #[])
    (body := blk [readScalar, I (.store (at_ .r12 0) .r9), I (.store (at_ .r12 8) .r10),
      I (.addi .r12 16), I (.subi .r13 1)])
    (fun k acc t' s' ⟨_, hR⟩ ↦ by rw [List.length_range]; exact test_count hR.2.2.2.2.2.2 hn)
    (fun k hk acc ↦ by
      rw [List.length_range] at hk
      refine Refines.mono (Refines.blk_cons (readScalar_fr (R := R k acc) ?_) fun x ↦
        Refines.pure fun t1 s1 ⟨hc1, hR1, h9, h10⟩ ↦ ?_) (fun _ _ h ↦ h) (fun _ _ _ h ↦ h)
        (fun _ h ↦ h.1)
      · rintro s1 s2 ⟨hf, hw, hsz, hkn, harr, h12', h13'⟩ hk' hd
        have hf2 : Fr env [⟨a, 2 * n⟩] readRegs s1 s2 := Fr.ofKeeps hk' hd clobbers_sub_readRegs
        refine ⟨hf.trans hf2, Stab.wsome _ _ s1 s2 hw hf2, hsz, hkn,
          EWArr.keeps h4 hk' (by rw [tWorkWords_val]; omega) (by rw [dataEnd_val]; omega) harr, ?_, ?_⟩
        · rw [hk'.regs .r12 (by decide), h12']
        · rw [hk'.regs .r13 (by decide), h13']
      · obtain ⟨hf, hw, hsz, hkn, harr, h12', h13'⟩ := hR1
        refine WP.mono (WP.frame (readN_tail h12' h13' hk (by omega)
          (hw _ (by omega) (by omega)) (hw _ (by omega) (by omega)))) ?_ fun _ h ↦ h.1
        rintro s3 ⟨⟨hm3, h12'', h13''⟩, hd, hr⟩
        have hrdi : s3.reg .rdi = s1.reg .rdi := hr .rdi (by decide)
        have hon : Only env [⟨a, 2 * n⟩] s1 s3 := fun b hb ↦ by
          rw [hm3, QState.setMem_mem, ite_eq_right, QState.setMem_mem, ite_eq_right]
          · rintro rfl; exact hb _ (List.mem_singleton_self _)
              (Region.in_wd (by dsimp only; omega) (by simp only [Region.stop]; omega))
          · rintro rfl; exact hb _ (List.mem_singleton_self _)
              (Region.in_wd (by dsimp only; omega) (by simp only [Region.stop]; omega))
        have hf3 : Fr env [⟨a, 2 * n⟩] readRegs s1 s3 :=
          hon.fr hrdi (fun r hr' ↦ hr r (by
            cases r <;> first | rfl | exact absurd (by decide) hr')) hd
        refine ⟨CodeRel.only hc1 h4 hm hon hd hrdi, hf.trans hf3, Stab.wsome _ _ s1 s3 hw hf3,
          by rw [Array.size_push, hsz], by omega, ?_, h12'', h13''⟩
        rw [hm3]
        refine EWArr.push (EWArr.setMem (EWArr.setMem harr (by omega) (by omega) (by omega) _)
          (by omega) (by omega) (by omega) _) ?_
        unfold EWAt
        rw [wd_wd, wd_wd, hsz, mem_setMem_wd _ (by omega) (by omega) (by omega), mem_setMem_self,
          show a + 2 * k + 1 = a + (2 * k + 1) by omega, mem_setMem_self, h9, h10]
        exact ⟨rfl, rfl⟩)
  refine WP.mono (H t s ⟨hrel, Fr.refl _ _ s, hws, rfl, Nat.zero_le _, fun i hi ↦ absurd hi
    (Nat.not_lt_zero _), by rw [Nat.mul_zero, Nat.add_zero]; exact h12, by rw [Nat.sub_zero]; exact h13⟩)
    ?_ fun s' ⟨hr, hf⟩ ↦ ⟨hr, hX s s' hx hf⟩
  rintro s' ⟨xs, t', hr, hc, hf, hw, hsz, -, harr, -⟩
  rw [List.length_range] at hsz
  exact ⟨xs, t', hr, hc, hX s s' hx hf, hw, hsz, harr⟩

end NativeVm.Code.P4
