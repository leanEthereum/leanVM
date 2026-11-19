module

public import NativeVm.Code.Phase6.Gad
public import NativeVm.Code.Phase5.Zero

/-!
# Copies from phase 6's scratch into its result regions

A region of the phase's results below the scratch (`OutR`: `claimsR`, `keccakR`) takes stores that
keep the phase's state `StA` (`StA.setMem`, `wp_store_st`). `cpLoop`: while `rdx ≠ 0`, the element
at `r8` copied to the two words at `rcx`, both pointers two words on, `rdx` down by one; from element
`o` of the scratch to word `j0` of such a region, `n` elements copied and nothing else written
(`cpLoop_spec`). `ClaimsAt.push`: the column claims with one appended.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code
open NativeVm.Transcript (wd wd_inj wdisp wdisp_toUInt64 Env rf_refl rf_setReg rf_setMem wp_done
  setMem_wd_ne setMem_wd_eq)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-- A region of the phase's, below the scratch. -/
structure OutR (q : Region) : Prop where
  mem : q ∈ rsAll
  reg : q ∈ regions
  below : q.stop ≤ scratchR.off

theorem outR_claims : OutR claimsR := ⟨by simp [rsAll], by decide +kernel, by decide⟩

theorem outR_keccak : OutR keccakR := ⟨by simp [rsAll], by decide +kernel, by decide⟩

theorem OutR.lt (hin : Inputs env inp s0.mem) {q : Region} (hq : OutR q) {j : Nat}
    (hj : j < q.size) : q.off + j < 2 ^ 61 := by
  have := region_lt (inp := inp) hq.reg hj
  have := workWords_lt hin
  omega

theorem OutR.not_inScr (hin : Inputs env inp s0.mem) {q : Region} (hq : OutR q) {j : Nat}
    (hj : j < q.size) : ¬ InScr (sb env) (wd env.work (q.off + j)) := by
  rintro ⟨k, hk, e⟩
  rw [sb_wd] at e
  have h1 := region_lt (inp := inp) hq.reg hj
  have h2 := scratch_in_work (inp := inp) hk
  have h3 := workWords_lt hin
  have h4 := (wd_inj (by omega) (by omega)).mp e
  have h5 := hq.below
  unfold Region.stop at h5
  omega

/-- **A store into such a region** keeps the phase's state. -/
theorem StA.setMem (hin : Inputs env inp s0.mem) (h : StA env s0 g t s) {q : Region} (hq : OutR q)
    {j : Nat} (hj : j < q.size) (v : UInt64) :
    StA env s0 g t (s.setMem (wd env.work (q.off + j)) v) := by
  have hs := hin.region_some h.2.1 hq.reg hj
  exact ⟨h.1.setMem hin hq.reg hj rfl hs v, h.2.1.setMem hq.mem hj rfl hs v,
    by rw [QState.setMem_reg]; exact h.2.2.1, h.2.2.2.congr fun a ha ↦ by
      rw [QState.setMem_mem, NativeVm.Transcript.ite_of_not
        (fun (e : a = _) ↦ hq.not_inScr hin hj (by rw [← e]; exact ha))]⟩

theorem StA.setReg (h : StA env s0 g t s) {r : Reg64} (h1 : r ≠ .rdi) (h2 : r ≠ .rbp) (v : UInt64) :
    StA env s0 g t (s.setReg r v) :=
  ⟨h.1.setReg h1 v, h.2.1.setReg h1 v, by
    rw [QState.setReg_reg, NativeVm.Transcript.ite_of_not (Ne.symm h2)]; exact h.2.2.1,
    h.2.2.2.congr fun _ _ ↦ rfl⟩

section Steps

variable {xs : List Stmt} {P E : QState → Prop}

theorem wp_store_st (hin : Inputs env inp s0.mem) (h : StA env s0 g t s) {q : Region} (hq : OutR q)
    {j : Nat} (hj : j < q.size) {a : Addr} {r : Reg64} (ha : a.eval s = wd env.work (q.off + j))
    (k : StA env s0 g t (s.setMem (wd env.work (q.off + j)) (s.reg r)) →
      WP (blk xs) (s.setMem (wd env.work (q.off + j)) (s.reg r)) P E) :
    WP (blk (I (.store a r) :: xs)) s P E :=
  NativeVm.Transcript.wp_store ha (hin.region_some h.2.1 hq.reg hj) (k (h.setMem hin hq hj _))

theorem wp_storei_st (hin : Inputs env inp s0.mem) (h : StA env s0 g t s) {q : Region} (hq : OutR q)
    {j : Nat} (hj : j < q.size) {a : Addr} {n : Int64} (ha : a.eval s = wd env.work (q.off + j))
    (k : StA env s0 g t (s.setMem (wd env.work (q.off + j)) n.toUInt64) →
      WP (blk xs) (s.setMem (wd env.work (q.off + j)) n.toUInt64) P E) :
    WP (blk (I (.storei a n) :: xs)) s P E :=
  NativeVm.Transcript.wp_storei ha (hin.region_some h.2.1 hq.reg hj) (k (h.setMem hin hq hj _))

theorem wp_reg_st {i : QInstr} {d : Reg64} {v : UInt64} (hs : i.step s = some (s.setReg d v))
    (h : StA env s0 g t s) (hd : d ≠ .rdi) (hp : d ≠ .rbp)
    (k : StA env s0 g t (s.setReg d v) → WP (blk xs) (s.setReg d v) P E) :
    WP (blk (I i :: xs)) s P E :=
  NativeVm.Transcript.wp_reg hs (k (h.setReg hd hp v))

theorem wp_load_st {d : Reg64} {a : Addr} {x v : UInt64} (ha : a.eval s = x)
    (hv : s.mem x = some v) (h : StA env s0 g t s) (hd : d ≠ .rdi) (hp : d ≠ .rbp)
    (k : StA env s0 g t (s.setReg d v) → WP (blk xs) (s.setReg d v) P E) :
    WP (blk (I (.load d a) :: xs)) s P E :=
  NativeVm.Transcript.wp_load ha hv (k (h.setReg hd hp v))

/-- The state named, with its phase's state. -/
theorem StA.name {c : Stmt} (h : StA env s0 g t s)
    (k : ∀ s', StA env s0 g t s' → s' = s → WP c s' P E) : WP c s P E :=
  k s h rfl

end Steps

/-- An element of the scratch at `r8`, limb by limb through `rax`, into the two words at `rcx`; both
pointers two words on, `rdx` down by one. -/
def cpPair : Stmt := blk [
  I (.load .rax (at_ .r8 (wdisp 0))), I (.store (at_ .rcx (wdisp 0)) .rax),
  I (.load .rax (at_ .r8 (wdisp 1))), I (.store (at_ .rcx (wdisp 1)) .rax),
  I (.addi .rcx (wdisp 2)), I (.addi .r8 (wdisp 2)), I (.subi .rdx 1)]

/-- `rdx` elements from `r8` to `rcx`. -/
def cpLoop : Stmt := .loop (.cmp .ne .rdx (.imm 0)) cpPair

/-- **`cpLoop`**: the elements `o + k`, `k < n`, of the scratch into the words `j0 + 2 k`,
`j0 + 2 k + 1` of the region `q`; nothing else written. -/
theorem cpLoop_spec (hin : Inputs env inp s0.mem) {q : Region} (hq : OutR q) {j0 n o : Nat}
    (hm : j0 + 2 * n ≤ q.size) (ho : o + n ≤ scrN) (h : StA env s0 g t s)
    (hrcx : s.reg .rcx = wd env.work (q.off + j0)) (hr8 : s.reg .r8 = wd (sb env) (2 * o))
    (hrdx : s.reg .rdx = n.toUInt64) {E : QState → Prop} :
    WP cpLoop s (fun s' ↦ StA env s0 g t s' ∧ RegsFrame [.rax, .rcx, .rdx, .r8] s s' ∧
      s'.reg .rcx = wd env.work (q.off + (j0 + 2 * n)) ∧
      (∀ k < n, EWAt s'.mem (wd env.work (q.off + (j0 + 2 * k))) (g (o + k))) ∧
      ∀ a, (∀ k < 2 * n, a ≠ wd env.work (q.off + (j0 + k))) → s'.mem a = s.mem a) E := by
  have hlt : ∀ k, k < q.size → q.off + k < 2 ^ 61 := fun k hk ↦ hq.lt hin hk
  have hn : n < 2 ^ 20 := by have := scrN_lt; omega
  refine WP.loop (fun s' ↦ ∃ j ≤ n, StA env s0 g t s' ∧ RegsFrame [.rax, .rcx, .rdx, .r8] s s' ∧
      s'.reg .rcx = wd env.work (q.off + (j0 + 2 * j)) ∧ s'.reg .r8 = wd (sb env) (2 * (o + j)) ∧
      s'.reg .rdx = (n - j).toUInt64 ∧
      (∀ k < j, EWAt s'.mem (wd env.work (q.off + (j0 + 2 * k))) (g (o + k))) ∧
      ∀ a, (∀ k < 2 * j, a ≠ wd env.work (q.off + (j0 + k))) → s'.mem a = s.mem a)
    (fun s' ↦ (s'.reg .rdx).toNat)
    ⟨0, Nat.zero_le _, h, rf_refl _ _, by simpa using hrcx, by simpa using hr8, by simpa using hrdx,
      fun k hk ↦ absurd hk (by omega), fun _ _ ↦ rfl⟩ ?_ ?_
  · rintro s1 ⟨j, hj, h1, hf1, hx1, h81, hd1, hz1, hk1⟩ hcond
    have hjn : j < n := by
      rw [cond_ne_zero hd1 (by omega)] at hcond
      omega
    have hA := hlt (j0 + 2 * j) (by omega)
    have hA' := hlt (j0 + 2 * j + 1) (by omega)
    unfold cpPair
    refine wp_load_st (eval_work h81 0)
      (by rw [NativeVm.Code.wd_wd, Nat.add_zero]; exact h1.2.2.2.word0 (by omega)) h1
      (by decide) (by decide) fun h2 ↦ ?_
    refine wp_store_st hin h2 hq (j := j0 + 2 * j + 0) (by omega)
      (eval_region (by reg_simp; exact hx1) 0) fun h3 ↦ ?_
    refine wp_load_st (eval_work (by reg_simp; exact h81) 1)
      (by rw [NativeVm.Code.wd_wd]; exact h3.2.2.2.word1 (by omega)) h3
      (by decide) (by decide) fun h4 ↦ ?_
    refine wp_store_st hin h4 hq (j := j0 + 2 * j + 1) (by omega)
      (eval_region (by reg_simp; exact hx1) 1) fun h5 ↦ ?_
    refine wp_reg_st rfl h5 (by decide) (by decide) fun h6 ↦ ?_
    refine wp_reg_st rfl h6 (by decide) (by decide) fun h7 ↦ ?_
    refine wp_reg_st rfl h7 (by decide) (by decide) fun h8 ↦ ?_
    refine wp_done ⟨⟨j + 1, by omega, h8, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact rf_setReg (rf_setReg (rf_setReg (rf_setMem (rf_setReg (rf_setMem (rf_setReg hf1
        (by simp) _) _ _) (by simp) _) _ _) (by simp) _) (by simp) _) (by simp) _
    · reg_simp
      rw [hx1, wdisp_toUInt64, NativeVm.Transcript.wd_add]
      congr 1
    · reg_simp
      rw [h81, wdisp_toUInt64, NativeVm.Transcript.wd_add]
      congr 1
    · reg_simp
      rw [hd1, toUInt64_sub1 (by omega)]
      congr 1
    · intro k hk
      have hq61 : q.off + q.size ≤ 2 ^ 61 := by have := hlt (q.size - 1) (by omega); omega
      simp only [EWAt, NativeVm.Code.wd_wd]
      simp (disch := omega) only [QState.setReg_mem, setMem_wd_ne, QState.setReg_reg,
        QState.setMem_reg, reduceCtorEq, ↓reduceIte]
      by_cases hk' : k < j
      · have := hz1 k hk'
        rw [EWAt, NativeVm.Code.wd_wd] at this
        simp (disch := omega) only [setMem_wd_ne, QState.setReg_mem]
        exact this
      · obtain rfl : k = j := by omega
        simp (disch := omega) only [setMem_wd_eq, and_self]
    · intro a ha
      simp only [QState.setReg_mem, QState.setMem_mem]
      rw [NativeVm.Transcript.ite_of_not (fun e ↦ ha (2 * j + 1) (by omega) (e.trans (by
          congr 2))),
        NativeVm.Transcript.ite_of_not (fun e ↦ ha (2 * j) (by omega) (e.trans (by congr 2)))]
      exact hk1 a fun k hk ↦ ha k (by omega)
    · reg_simp
      rw [hd1, toUInt64_sub1 (by omega), NativeVm.Transcript.toNat_toUInt64 (by omega),
        NativeVm.Transcript.toNat_toUInt64 (by omega)]
      omega
  · rintro s1 ⟨j, hj, h1, hf1, hx1, -, hd1, hz1, hk1⟩ hcond
    have hjn : j = n := by
      have := (cond_ne_zero hd1 (by omega)).not.mp (by rw [hcond]; decide)
      omega
    subst hjn
    exact ⟨h1, hf1, hx1, hz1, hk1⟩

/-! ## The results' shapes -/

/-- An element at word `y` through a run that keeps words `y`, `y + 1`. -/
theorem EWAt.keep {m m' : UInt64 → Option UInt64} {w : UInt64} {y : Nat} {x : EW}
    (h : EWAt m (wd w y) x) (h0 : m' (wd w y) = m (wd w y))
    (h1 : m' (wd w (y + 1)) = m (wd w (y + 1))) : EWAt m' (wd w y) x := by
  refine ⟨h0.trans h.1, ?_⟩
  rw [NativeVm.Code.wd_wd, h1, ← NativeVm.Code.wd_wd]
  exact h.2

/-- An element at word `o + y` through a run that keeps words `o + y`, `o + (y + 1)`. -/
theorem EWAt.keepI {m m' : UInt64 → Option UInt64} {w : UInt64} {o y : Nat} {x : EW}
    (h : EWAt m (wd w (o + y)) x)
    (h0 : ∀ z, y ≤ z → z ≤ y + 1 → m' (wd w (o + z)) = m (wd w (o + z))) :
    EWAt m' (wd w (o + y)) x :=
  EWAt.keep h (h0 y (Nat.le_refl _) (Nat.le_succ _)) (by
    rw [Nat.add_assoc]
    exact h0 (y + 1) (Nat.le_succ _) (Nat.le_refl _))

/-- An element at word `y`, from an equation of its index. -/
theorem EWAt.idx {m : UInt64 → Option UInt64} {w : UInt64} {x y : Nat} {v : EW} (h : x = y)
    (hy : EWAt m (wd w y) v) : EWAt m (wd w x) v := h ▸ hy

/-- A store into a region keeps the words outside it. -/
theorem mem_setMem_out {s : QState} {w a : UInt64} {q : Region} (ha : ¬ q.In w a) {j : Nat}
    (hj : j < q.size) (v : UInt64) : (s.setMem (wd w (q.off + j)) v).mem a = s.mem a := by
  rw [QState.setMem_mem, NativeVm.Transcript.ite_of_not fun e ↦ ha ⟨j, hj, e⟩]

/-- A word outside a copy's range survives it. -/
theorem frame_idx {m m' : UInt64 → Option UInt64} {w : UInt64} {o j0 n x : Nat}
    (hfr : ∀ a, (∀ k < n, a ≠ wd w (o + (j0 + k))) → m' a = m a) (hb : o + x < 2 ^ 61)
    (hb' : o + (j0 + n) ≤ 2 ^ 61) (hx : x < j0 ∨ j0 + n ≤ x) :
    m' (wd w (o + x)) = m (wd w (o + x)) :=
  hfr _ fun k hk e ↦ by
    have := (wd_inj hb (by omega)).mp e
    omega

/-- A word outside a region survives a copy into it. -/
theorem frame_out {m m' : UInt64 → Option UInt64} {w a : UInt64} {q : Region} {j0 n : Nat}
    (hfr : ∀ a, (∀ k < n, a ≠ wd w (q.off + (j0 + k))) → m' a = m a) (ha : ¬ q.In w a)
    (hn : j0 + n ≤ q.size) : m' a = m a :=
  hfr a fun k hk e ↦ ha ⟨j0 + k, by omega, e⟩

/-- **A claim appended** to the column claims: the count up by one, the words before the new slot
kept, the claim in it. -/
theorem ClaimsAt.push {m m' : UInt64 → Option UInt64} {p : UInt64} {acc : Array ColumnClaimW}
    {c : ColumnClaimW} (h : ClaimsAt m p acc) (hsz : acc.size < claimCap)
    (hcnt : m' p = some (acc.size + 1).toUInt64)
    (hold : ∀ k, 0 < k → k < 1 + claimWords * acc.size → m' (wd p k) = m (wd p k))
    (hnew : ColumnClaimAt m' (wd p (1 + claimWords * acc.size)) c) :
    ClaimsAt m' p (acc ++ #[c]) := by
  have hcw : claimWords = 76 := by decide
  have hcc : claimCap = 160 := by decide
  have hs : (acc ++ #[c]).size = acc.size + 1 := by simp
  refine ⟨by omega, ⟨by omega, by rw [hs]; exact hcnt⟩, fun i hi ↦ ?_⟩
  by_cases h1 : i < acc.size
  · rw [Array.getElem_append_left h1]
    refine (h.2.2 i h1).congr fun k hk ↦ ?_
    rw [NativeVm.Code.wd_wd]
    rw [hcw] at hk ⊢
    exact hold _ (by omega) (by nlinarith)
  · obtain rfl : i = acc.size := by omega
    rw [Array.getElem_append_right (by omega)]
    simpa using hnew

end NativeVm.Code.P6
