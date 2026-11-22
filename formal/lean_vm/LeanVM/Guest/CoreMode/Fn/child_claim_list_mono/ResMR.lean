/-
  LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.ResMR

  The gap walk's table reads at the honest frames: each claim's entry below the caller's bound,
  from its frame's gaps and the walk's records.
-/

module

public import LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.ResM
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono_last__L»

/-!
# The gap walk's reads

At an honest frame of a frame loop (or of the last claims), the body's atoms hold on the reference
and name their values (`atoms_on_path'`). The walk (`monoWalk_vals`) puts the gaps at `g^(e_i)`,
`e_i < 2^32`, the coverage pointer after `j` claims at `cov0 · g^(Σ_{i<j} e_i)` and the table
pointer at `ent0 · g^(4 Σ_{i<j} e_i)`. With the record's pointers at offset `O` (`MonoQ`), claim
`jj` reads from `entries · g^(4 o)`, `o = O + Σ_{i ≤ jj} e_i + jj`; the walk ends at
`O + Σ e_i + m`, which a frame loop writes into the next record, at an offset `O' ≤ L` (`MonoQ`,
the two equal: no wrap, `region ≠ 0` where a claim is marked), and which the last claims bound by
their range check, so `o < L`, the exponent of the caller's `limit` (`mlOk_parts`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (idxOf FrameHolds fsN fn_of_idx cellJ namedOf)
open LeanVM.Guest.Value (gen_pow_eq_ofK gen_pow_inj)
open LeanVM.Guest.B1 (loadHolds_unique loadHolds_mul_gen_pow word_two_pow)
open LeanVM.Guest.B1.Digest
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

/-! ## Sums of gaps -/

/-- The gaps' exponents below `j`, summed. -/
def gsum (es : ℕ → ℕ) (j : ℕ) : ℕ := ((List.range j).map es).sum

theorem gsum_succ (es : ℕ → ℕ) (j : ℕ) : gsum es (j + 1) = gsum es j + es j := by
  simp [gsum, List.range_succ]

theorem gsum_mono (es : ℕ → ℕ) {j k : ℕ} (h : j ≤ k) : gsum es j ≤ gsum es k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [gsum_succ]; omega

theorem gsum_le {es : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, es i < 2 ^ 32) : ∀ j ≤ n, gsum es j ≤ j * 2 ^ 32
  | 0, _ => by simp [gsum]
  | j + 1, hj => by
    rw [gsum_succ, Nat.succ_mul]
    have := gsum_le h j (by omega)
    have := h j (by omega)
    omega

theorem prod_gaps {σ : Core.Val} {g0 n : ℕ} {es : ℕ → ℕ} (hes : ∀ i < n, σ (.n (g0 + 10 * i)) = gen ^ es i) :
    ∀ j ≤ n, ((List.range j).map fun i => σ (.n (g0 + 10 * i)) ^ 4).prod = gen ^ (4 * gsum es j)
  | 0, _ => by simp [gsum]
  | j + 1, hj => by
    rw [List.range_succ, List.map_append, List.prod_append, prod_gaps hes j (by omega), gsum_succ]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hes j (by omega)]
    rw [← pow_mul, ← pow_add]
    ring_nf

/-! ## The walk at a frame -/

/-- **The walk's values at a valuation**: the gaps `g^(e_i)`, named by atoms; the pointers after `j`
claims; the coverage pointer nonzero once a claim is marked. -/
theorem monoWalk_vals {rd : Reader} (hm : MemOk rd) {σ : Core.Val} {atoms : List Atom}
    {p0 g0 cov0 ent0 : ℕ} {mark : V} {n : ℕ}
    (h : monoRecs atoms p0 g0 cov0 ent0 mark n 0 n = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∃ es : ℕ → ℕ, (∀ i < n, es i < 2 ^ 32 ∧ σ (.n (g0 + 10 * i)) = gen ^ es i ∧
        ∃ a ∈ atoms, .n (g0 + 10 * i) ∈ atomUses a) ∧
      (∀ j ≤ n, σ (.n (mCov g0 cov0 j)) = σ (.n cov0) * gen ^ gsum es j ∧
        σ (.n (mEnt g0 ent0 j)) = σ (.n ent0) * gen ^ (4 * gsum es j)) ∧
      (0 < n → σ (.n cov0) ≠ 0) := by
  simp only [monoRecs, List.all_eq_true, List.mem_range', Bool.or_eq_true, decide_eq_true_eq] at h
  have hok : ∀ i < n, monoClaimOk (monoWin atoms p0 i) i (g0 + 10 * i) (mCov g0 cov0 i)
      (mEnt g0 ent0 i) mark = true := fun i hi ↦ by
    rcases h i ⟨i, by omega, by omega⟩ with h' | h'
    · omega
    · exact h'
  have hwin : ∀ i, ∀ a ∈ monoWin atoms p0 i, a ∈ atoms :=
    fun i a ha ↦ List.mem_of_mem_drop (List.mem_of_mem_take ha)
  have hex : ∀ i, i < n → ∃ e, e < 2 ^ 32 ∧ σ (.n (g0 + 10 * i)) = gen ^ e ∧
      ∃ a ∈ atoms, .n (g0 + 10 * i) ∈ atomUses a := fun i hi ↦ by
    have hc := hok i hi
    simp only [monoClaimOk, Bool.and_eq_true] at hc
    obtain ⟨a, ha, hd⟩ := List.any_eq_true.mp hc.1.1.1.1.1.1
    have := monoWin_holds hat p0 i a ha
    cases a <;> simp only [isDerefOf, Bool.false_eq_true, decide_eq_true_eq] at hd
    subst hd
    obtain ⟨e, he, hg⟩ := load_gpow hm this
    exact ⟨e, he, hg, _, hwin i _ ha, by simp [atomUses]⟩
  choose! es hes using hex
  refine ⟨es, hes, fun j ↦ ?_, fun h0 ↦ ?_⟩
  · induction j with
    | zero => intro _; simp [mCov, mEnt, gsum]
    | succ j ih =>
      intro hj
      obtain ⟨hcv, hev⟩ := ih (by omega)
      have hc := hok j (by omega)
      simp only [monoClaimOk, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, h4⟩, h5⟩, -⟩, -⟩ := hc
      have hw := monoWin_holds hat p0 j
      obtain ⟨-, hg, -⟩ := hes j (by omega)
      rw [mCov_succ, mEnt_succ, gsum_succ]
      refine ⟨by rw [mulOf_sound h2 hw, hcv, hg, pow_add, mul_assoc], ?_⟩
      rw [mulOf_sound h5 hw, mulOf_sound h4 hw, mulOf_sound h3 hw, hev, hg]
      ring
  · have hc := hok 0 h0
    simp only [monoClaimOk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨-, h2⟩, -⟩, -⟩, -⟩, hmk⟩, -⟩ := hc
    have hw := monoWin_holds hat p0 0
    have hl := load_sound hmk hw
    rw [mulOf_sound h2 hw] at hl
    intro hz
    apply Res.ne_zero_of_load hm hl
    simp [mCov, hz]

/-- Atoms heading a block are on its path. -/
theorem atoms_on_path' {σ : Core.Val} : ∀ (bs : List Atom) {ps : List Stmt} {es : List Ev} {vs : List V},
    Memory.walk σ (bs.map Stmt.atom ++ ps) = .ret es vs → ∀ a ∈ bs, Ev.atom a ∈ es
  | [], _, _, _, _, a, ha => absurd ha List.not_mem_nil
  | b :: bs, ps, es, vs, hw, a, ha => by
    rw [List.map_cons, List.cons_append, Memory.walk] at hw
    simp only [walk1, Out.seq] at hw
    cases h2 : Memory.walk σ (bs.map Stmt.atom ++ ps) with
    | fall _ => rw [h2] at hw; simp [Out.pre] at hw
    | ret es2 vs2 =>
      rw [h2] at hw
      simp only [Out.pre, Out.ret.injEq] at hw
      obtain ⟨rfl, -⟩ := hw
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (atoms_on_path' bs h2 a ha)
    | stuck => rw [h2] at hw; simp [Out.pre] at hw

/-! ## At the honest frames -/

section

variable {A : String → Bridge.FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- The parts of `mlOk` the reads use. -/
theorem mlOk_parts {k : ℕ} (hk0 : k ≠ 0) {F : Fn} (h : mlOk k F = true) :
    F.params = [.n (valf% «child_claim_list_mono_last» "rec"), .n (valf% «child_claim_list_mono_last» "region"), .n (valf% «child_claim_list_mono_last» "mark"), .n (valf% «child_claim_list_mono_last» "limit_g")] ∧ ∃ (atoms : List Atom) (r0 r1 : V),
      F.body = atoms.map Stmt.atom ++ [.ret [r0, r1]] ∧
      atoms.any (isLoadAt (.n 4) (.n (valf% «child_claim_list_mono_last» "rec")) 13) = true ∧ atoms.any (isLoadAt (.n 5) (.n (valf% «child_claim_list_mono_last» "rec")) 14) = true ∧
      monoRecs atoms 2 6 4 5 (.n (valf% «child_claim_list_mono_last» "mark")) k 0 k = true ∧
      (∃ c, mulOf atoms (.n (mlEnd k)) = some (.n (mCov 6 4 k), c) ∧ atoms.any (isConstAt c (2 ^ k) 0) = true) ∧
      ∃ tv, endOf atoms (.n (mlEnd k)) = some tv ∧ rcOf atoms tv = some (.n (valf% «child_claim_list_mono_last» "limit_g")) := by
  simp only [mlOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hpar, h⟩ := h
  refine ⟨hpar, ?_⟩
  split at h
  · rename_i atoms r0 r1 hsb
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨-, -⟩, -⟩, hwalk⟩, hend⟩ := h
    simp only [hk0, ↓reduceIte, Bool.and_eq_true] at hwalk
    obtain ⟨⟨⟨hl4, hl5⟩, hrec⟩, hmul⟩ := hwalk
    refine ⟨atoms, r0, r1, splitBody_eq hsb, hl4, hl5, hrec, ?_, ?_⟩
    · split at hmul
      · rename_i a c hac
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hmul
        obtain ⟨rfl, hc⟩ := hmul
        exact ⟨c, hac, hc⟩
      · exact absurd hmul (by simp)
    · split at hend
      · rename_i tv ht
        simp only [decide_eq_true_eq] at hend
        exact ⟨tv, ht, hend⟩
      · exact absurd hend (by simp)
  · exact absurd h (by simp)

end

end

end LeanVM.Guest.EndExec
