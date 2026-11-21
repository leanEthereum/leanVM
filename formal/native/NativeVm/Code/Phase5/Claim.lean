module

public import NativeVm.Code.Phase5.Zero
public import NativeVm.Field.E
public import NativeVm.Equiv.Field

/-!
# One of the public input's column claims

`pubClaim l` writes the column claim of memory column `l` into the claim slot at `r12`
(`ColumnClaimAt`'s words): limb `l`'s value `w[l] + c·(w[l] + w[2 + l])`, the line through `w[l]`
and `w[2 + l]` at the challenge `c` (`r14`, `r15`), by `escale` (`publicLimb_eq`); the column `l`;
the point `(c, 0, …, 0)` of `r13` coordinates, its zeros by `zeroLoop`. It writes nothing outside
the slot (`pubClaim_spec`).
-/

@[expose] public section

namespace NativeVm.Code

open Native NativeVm.Model NativeVm.Transcript LeanVM.Parameters

variable {env : Env} {inp : Input} {rs : List Region} {s0 s : QState}

/-! ## The value -/

theorem mle_two (x y c : EW) : multilinearEval #[x, y] #[c] = x * (1 + c) + y * c := by
  simp [multilinearEval, foldPairs]

/-- **A limb's value**: `escale`'s product by `w[l] + w[2 + l]`, plus `w[l]`. -/
theorem publicLimb_eq {a b r9 r10 : UInt64} {c : EW}
    (h : Field.eOf r9 r10 = Field.eOf c.c0 c.c1 * ofK (K.ofLane (a ^^^ b))) :
    multilinearEval #[EW.ofK a, EW.ofK b] #[c] = ⟨r9 ^^^ a, r10⟩ := by
  apply Equiv.EW.toE_injective
  have e1 : (⟨r9 ^^^ a, r10⟩ : EW).toE = Field.eOf r9 r10 + ofK (K.ofLane a) := by
    have := Field.eOf_add r9 r10 a 0
    rw [UInt64.xor_zero] at this
    rw [show (⟨r9 ^^^ a, r10⟩ : EW).toE = Field.eOf (r9 ^^^ a) r10 from rfl, this, Field.eOf,
      Field.eOf, Field.ofLane_zero, ← ofK_eq_ofLimbs]
  rw [e1, h, mle_two]
  simp only [Equiv.EW.toE_add, Equiv.EW.toE_mul, Equiv.EW.toE_one, Equiv.EW.toE_ofK]
  rw [show c.toE = Field.eOf c.c0 c.c1 from rfl, Field.ofLane_xor, ofK_add]
  ring

/-! ## The code -/

/-- **Column claim `l`** into the slot at `r12`: the value, the column, the point's count `r13`,
its first coordinate `(r14, r15)` and its zeros. -/
def pubClaim (l : Nat) : Stmt := blk [
  I (.load .r11 (cw (ctxPublic + l))), I (.load .rax (cw (ctxPublic + 2 + l))),
  I (.xor .r11 .rax), I (.mov .r9 .r14), I (.mov .r10 .r15), Field.escale,
  I (.load .rax (cw (ctxPublic + l))), I (.xor .r9 .rax),
  I (.store (at_ .r12 (wdisp (1 + vecWords pointCap))) .r9),
  I (.store (at_ .r12 (wdisp (2 + vecWords pointCap))) .r10),
  I (.storei (at_ .r12 (wdisp 0)) (Int64.ofNat l)),
  I (.store (at_ .r12 (wdisp 1)) .r13),
  I (.store (at_ .r12 (wdisp 2)) .r14), I (.store (at_ .r12 (wdisp 3)) .r15),
  I (.mov .rdx .r13), I (.subi .rdx 1), I (.lea .rcx (at_ .r12 (wdisp 4))),
  zeroLoop]

/-! ## Numbers -/

theorem claimWords_val : claimWords = 76 := by decide
theorem claimsR_size : claimsR.size = 12161 := by decide
theorem claimsR_off : claimsR.off = 15569 := by decide
theorem vecWords_pointCap : vecWords pointCap = 73 := by decide
theorem claimsR_mem : claimsR ∈ regions := by decide +kernel

/-- A word read through an equation of its index. -/
theorem mem_congr_idx {m : UInt64 → Option UInt64} {w : UInt64} {x y : Nat} {v : Option UInt64}
    (h : x = y) (hy : m (wd w y) = v) : m (wd w x) = v := h ▸ hy

/-- The point `(c, 0, …, 0)` of `P` coordinates. -/
theorem point_get {c : EW} {P e : Nat} (he : e < (#[c] ++ Array.replicate (P - 1) (0 : EW)).size) :
    (#[c] ++ Array.replicate (P - 1) (0 : EW))[e] = if e = 0 then c else 0 := by
  rw [Array.getElem_append]
  split
  · rename_i h
    have : e = 0 := by simpa using h
    subst this
    rfl
  · rename_i h
    simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add] at h
    rw [Array.getElem_replicate, ite_of_not (by omega)]

/-! ## The spec -/

/-- **`pubClaim l`** writes column claim `l` into the slot at `r12` (word `j0` of `claimsR`), and
nothing else. -/
theorem pubClaim_spec {t : TState} {l : Nat} (hlv : (Int64.ofNat l).toUInt64 = l.toUInt64)
    (hl : l < 2) {j0 P : Nat} (hj0 : j0 + claimWords ≤ claimsR.size) (hP1 : 1 ≤ P)
    (hP : P ≤ pointCap) {c : EW} {a b : UInt64} (hq : claimsR ∈ rs)
    (hin : Inputs env inp s0.mem) (hc : CodeRel env t s) (hb : Base env rs s0 s)
    (h12 : s.reg .r12 = wd env.work (claimsR.off + j0)) (h13 : s.reg .r13 = P.toUInt64)
    (h14 : s.reg .r14 = c.c0) (h15 : s.reg .r15 = c.c1)
    (ha : s.mem (wd env.ctx (ctxPublic + l)) = some a)
    (hb' : s.mem (wd env.ctx (ctxPublic + 2 + l)) = some b) {E : QState → Prop} :
    WP (pubClaim l) s (fun s' ↦ CodeRel env t s' ∧ Base env rs s0 s' ∧
      s'.reg .r12 = s.reg .r12 ∧ s'.reg .r13 = s.reg .r13 ∧ s'.reg .r14 = s.reg .r14 ∧
      s'.reg .r15 = s.reg .r15 ∧
      ColumnClaimAt s'.mem (wd env.work (claimsR.off + j0))
        ⟨l, #[c] ++ Array.replicate (P - 1) 0, multilinearEval #[EW.ofK a, EW.ofK b] #[c]⟩ ∧
      ∀ k < claimsR.size, (k < j0 ∨ j0 + claimWords ≤ k) →
        s'.mem (wd env.work (claimsR.off + k)) = s.mem (wd env.work (claimsR.off + k))) E := by
  have hcw := claimWords_val
  have hcs := claimsR_size
  have hvp := vecWords_pointCap
  have hpc := pointCap_val
  have hlt : ∀ k, k < claimsR.size → claimsR.off + k < 2 ^ 61 := fun k hk ↦ by
    have := region_lt (inp := inp) claimsR_mem hk
    have := workWords_lt hin
    omega
  have hrdi : s.reg .rdi = env.ctx := hb.1.1
  unfold pubClaim
  refine wp_load (eval_cw hrdi _) ha ?_
  refine wp_load (eval_cw (by reg_simp; exact hrdi) _) (by simp only [QState.setReg_mem]; exact hb')
    ?_
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl ?_))
  refine wp_then (Field.escale_spec _) fun s1 ⟨he, hm1, hf1⟩ ↦ ?_
  simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, h14, h15] at he
  simp only [QState.setReg_mem] at hm1
  have g1 : ∀ r ∉ Field.sqRegs, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .rax → s1.reg r = s.reg r :=
    fun r hr h9 h10 h11 hax ↦ by rw [hf1 r hr]; simp [h9, h10, h11, hax]
  have hrdi1 : s1.reg .rdi = env.ctx := (g1 .rdi (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans hrdi
  have hc1 : CodeRel env t s1 := hc.of_mem hm1 (by rw [hrdi1, hrdi])
  have hb1 : Base env rs s0 s1 := hb.of_mem hm1 (by rw [hrdi1, hrdi])
  have h12' : s1.reg .r12 = wd env.work (claimsR.off + j0) :=
    (g1 .r12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12
  have h13' := (g1 .r13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13
  have h14' := (g1 .r14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14
  have h15' := (g1 .r15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h15
  refine wp_load (eval_cw hrdi1 _) (by rw [hm1]; exact ha) ?_
  refine wp_reg rfl ?_
  have hv := publicLimb_eq (a := a) (b := b) (c := c) he
  have hO := claimsR_off
  -- the stores
  refine wp_store_rel hq claimsR_mem hin (j := j0 + (1 + vecWords pointCap)) (by omega)
    (eval_region (by reg_simp; exact h12') _) ((hc1.setReg (by decide) _).setReg (by decide) _)
    ((hb1.setReg (by decide) _).setReg (by decide) _) fun hc2 hb2 ↦ ?_
  refine wp_store_rel hq claimsR_mem hin (j := j0 + (2 + vecWords pointCap)) (by omega)
    (eval_region (by reg_simp; exact h12') _) hc2 hb2 fun hc3 hb3 ↦ ?_
  refine wp_storei_rel hq claimsR_mem hin (j := j0 + 0) (by omega)
    (eval_region (by reg_simp; exact h12') _) hc3 hb3 fun hc4 hb4 ↦ ?_
  refine wp_store_rel hq claimsR_mem hin (j := j0 + 1) (by omega)
    (eval_region (by reg_simp; exact h12') _) hc4 hb4 fun hc5 hb5 ↦ ?_
  refine wp_store_rel hq claimsR_mem hin (j := j0 + 2) (by omega)
    (eval_region (by reg_simp; exact h12') _) hc5 hb5 fun hc6 hb6 ↦ ?_
  refine wp_store_rel hq claimsR_mem hin (j := j0 + 3) (by omega)
    (eval_region (by reg_simp; exact h12') _) hc6 hb6 fun hc7 hb7 ↦ ?_
  refine wp_reg_rel rfl (by decide) hc7 hb7 fun hc8 hb8 ↦ ?_
  refine wp_reg_rel rfl (by decide) hc8 hb8 fun hc9 hb9 ↦ ?_
  refine wp_reg_rel rfl (by decide) hc9 hb9 fun hc10 hb10 ↦ ?_
  -- the zeros
  refine wp_then (zeroLoop_spec hq claimsR_mem (j0 := j0 + 4) (m := P - 1) (by omega) hin hc10
    hb10 ?_ ?_) fun s' ⟨hcf, hbf, hff, hzf, hkf⟩ ↦ ?_
  · reg_simp
    exact eval_region (by reg_simp; exact h12') _
  · reg_simp
    rw [h13', toUInt64_sub1 hP1]
  -- the end
  have hloop : ∀ x, x < claimsR.size → (x < j0 + 4 ∨ j0 + 4 + 2 * (P - 1) ≤ x) →
      ∀ k < 2 * (P - 1), wd env.work (claimsR.off + x) ≠ wd env.work (claimsR.off + (j0 + 4 + k)) :=
    fun x hx hx' k hk ↦ wd_ne_work (by omega) (by omega) (by omega)
  have hfr : ∀ r, r ≠ .rcx → r ≠ .rdx → r ≠ .r9 → r ≠ .rax → s'.reg r = s1.reg r :=
    fun r h1 h2 h3 h4 ↦ by
      rw [hff r (by simp [h1, h2])]
      reg_simp
      simp only [h1, h2, h3, h4, ↓reduceIte]
  have hps : (#[c] ++ Array.replicate (P - 1) (0 : EW)).size = P := by simp; omega
  refine wp_done ⟨hcf, hbf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr .r12 (by decide) (by decide) (by decide) (by decide), h12', h12]
  · rw [hfr .r13 (by decide) (by decide) (by decide) (by decide), h13', h13]
  · rw [hfr .r14 (by decide) (by decide) (by decide) (by decide), h14', h14]
  · rw [hfr .r15 (by decide) (by decide) (by decide) (by decide), h15', h15]
  · refine ⟨⟨show l < 2 ^ 64 by omega, ?_⟩,
      ⟨show (#[c] ++ Array.replicate (P - 1) (0 : EW)).size ≤ pointCap by omega,
        ⟨show (#[c] ++ Array.replicate (P - 1) (0 : EW)).size < 2 ^ 64 by omega, ?_⟩,
        fun e he' ↦ ?_⟩, ?_⟩
    · show s'.mem _ = some l.toUInt64
      refine mem_congr_idx (y := claimsR.off + j0) rfl ?_
      rw [hkf _ (hloop j0 (by omega) (by omega))]
      simp (disch := omega) only [setMem_wd_ne, setMem_wd_eq, QState.setReg_mem]
      rw [hlv]
    · show s'.mem _ = some (#[c] ++ Array.replicate (P - 1) (0 : EW)).size.toUInt64
      simp only [wd_wd]
      refine mem_congr_idx (y := claimsR.off + (j0 + 1)) (by omega) ?_
      rw [hkf _ (hloop (j0 + 1) (by omega) (by omega))]
      simp (disch := omega) only [setMem_wd_ne, setMem_wd_eq, QState.setReg_mem]
      reg_simp
      rw [h13', hps]
    · rw [point_get he']
      have hsz : e < P := by rw [hps] at he'; exact he'
      simp only [EWAt, wd_wd]
      split
      · rename_i h0
        subst h0
        refine ⟨mem_congr_idx (y := claimsR.off + (j0 + 2)) (by omega) ?_,
          mem_congr_idx (y := claimsR.off + (j0 + 3)) (by omega) ?_⟩
        · rw [hkf _ (hloop (j0 + 2) (by omega) (by omega))]
          simp (disch := omega) only [setMem_wd_ne, setMem_wd_eq, QState.setReg_mem]
          reg_simp
          rw [h14']
        · rw [hkf _ (hloop (j0 + 3) (by omega) (by omega))]
          simp (disch := omega) only [setMem_wd_eq, QState.setReg_mem]
          reg_simp
          rw [h15']
      · rename_i h0
        exact ⟨mem_congr_idx (y := claimsR.off + (j0 + 4 + (2 * e - 2))) (by omega)
            (hzf _ (by omega)),
          mem_congr_idx (y := claimsR.off + (j0 + 4 + (2 * e - 1))) (by omega) (hzf _ (by omega))⟩
    · rw [hv]
      simp only [EWAt, wd_wd]
      refine ⟨mem_congr_idx (y := claimsR.off + (j0 + (1 + vecWords pointCap))) (by omega) ?_,
        mem_congr_idx (y := claimsR.off + (j0 + (2 + vecWords pointCap))) (by omega) ?_⟩
      · rw [hkf _ (hloop _ (by omega) (by omega))]
        simp (disch := omega) only [setMem_wd_ne, setMem_wd_eq, QState.setReg_mem]
        reg_simp
      · rw [hkf _ (hloop _ (by omega) (by omega))]
        simp (disch := omega) only [setMem_wd_ne, setMem_wd_eq, QState.setReg_mem]
        reg_simp
  · intro k hk hk'
    rw [hkf _ (hloop k hk (by omega))]
    simp (disch := omega) only [setMem_wd_ne, QState.setReg_mem]
    rw [hm1]

end NativeVm.Code
