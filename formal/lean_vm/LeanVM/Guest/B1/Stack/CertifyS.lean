/-
  LeanVM.Guest.B1.Stack.CertifyS

  `certify_stack`, in the guest's terms: a ranking of the groups by falling keys, each group placed
  at its rank's running total, and the stack's log.
-/

module

public import LeanVM.Guest.B1.Stack.CertifyO
import LeanVM.Guest.Value.FieldBits

/-!
# `certify_stack`, in the guest's terms

`certify_stack_guest`: on a memory image of `2^κ` words, `11 ≤ κ ≤ 32`, the exponent tables at
`g_squares` and the kappa sources `g^(kv i)` (`kv i ≤ 30`) at `kappa_base`, a call returning `rets`
gives a ranking `ρ` of the eight groups whose keys `csN kv (ρ r) = 53 κ + 52 - b0` fall strictly,
and `rets = [g^max(16, log2Ceil T), outs, outs·g^52]`, where group `ρ r`'s block `b0 + j` holds
`g^(csTot r + j·2^κ)` at `outs[b0 + j]` and `g^κ` at `outs[52 + b0 + j]`; `csTot r` is the sum of the
sizes `len·2^κ` of the groups ranked before `r`, `T = csTot 8`.
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Group `gi`'s rank key's exponent, shifted to be a natural number: `53 κ + 52 - b0`. -/
def csN (kv : ℕ → ℕ) (gi : ℕ) : ℕ := 53 * csKap kv gi + 52 - (csG gi).b0

/-- Group `gi`'s size: `len·2^κ`. -/
def csSize (kv : ℕ → ℕ) (gi : ℕ) : ℕ := (csG gi).len * 2 ^ csKap kv gi

/-- The total of the groups ranked before `r`. -/
def csTot (kv : ℕ → ℕ) (ρ : ℕ → ℕ) (r : ℕ) : ℕ := ∑ r' ∈ Finset.range r, csSize kv (ρ r')

/-- `certify_stack`'s statements before its return. -/
def csBodyA : List Stmt :=
  let ks := csKeys 0 8 12
  let ord := ks.2
  let at_ := ord + 1
  let s0 := ord + 2
  let tot := s0 + 11 + 18 * 6 + 17
  let gmv := tot + 1
  let out := tot + 2
  let os := csOuts out at_ 0 8 (tot + 3)
  csLoads ++ ks.1 ++
    [.atom (.hint (.alloc (.n ord) 8)), .atom (.hint (.witness "stk_group_order" (.heap (.n ord) 0 8))),
      .atom (.hint (.alloc (.n at_) 8))] ++
    csRanks ord at_ s0 ++
    [.call "log2_ceil_in_the_exponent__L16_L34" [.n tot, .n 1] [.n gmv],
      .atom (.hint (.alloc (.n out) 104))] ++ os.1 ++
    [.atom (.copy (.n os.2) (.n gmv)), .atom (.copy (.n (os.2 + 1)) (.n out)),
      osCst (os.2 + 2) (csW 52), osMul (os.2 + 3) out (os.2 + 2)]

theorem csBody_split : csBody = csBodyA ++ [.ret [.n 374, .n 375, .n 377]] := by
  simp only [csBody, csBodyA, List.append_assoc, List.cons_append, List.nil_append]
  rfl

set_option maxRecDepth 100000 in
theorem csBodyA_flat : csBodyA.all Stmt.flat = true := by decide +kernel

theorem csKeys_end : (csKeys 0 8 12).2 = 163 := by decide

theorem csOuts_end : (csOuts 303 164 0 8 304).2 = 374 := by decide

theorem csKey_shift {kv : ℕ → ℕ} {gi : ℕ} (hgi : gi < 8) {key : E}
    (h : key * gen ^ (csG gi).b0 = gen ^ (53 * csKap kv gi)) : key * gen ^ 52 = gen ^ csN kv gi := by
  have hb : (csG gi).b0 ≤ 48 := by
    have : ∀ gi < 8, (csG gi).b0 ≤ 48 := by decide
    exact this gi hgi
  rw [show (52 : ℕ) = (csG gi).b0 + (52 - (csG gi).b0) by omega, pow_add, ← mul_assoc, h, ← pow_add]
  unfold csN; congr 1; omega

theorem csSize_le {kv : ℕ → ℕ} {gi : ℕ} (hgi : gi < 8) (hk : csKap kv gi < 34) :
    csSize kv gi ≤ 14 * 2 ^ 33 := by
  unfold csSize
  have := (csGroups_facts gi hgi).2.2.2.1
  exact Nat.mul_le_mul this (Nat.pow_le_pow_right (by decide) (by omega))

theorem csTot_succ (kv : ℕ → ℕ) (ρ : ℕ → ℕ) (r : ℕ) :
    csTot kv ρ (r + 1) = csTot kv ρ r + csSize kv (ρ r) := Finset.sum_range_succ _ _

/-- **`certify_stack`, in the guest's terms.** -/
theorem certify_stack_guest {κ : ℕ} (hκ11 : 11 ≤ κ) (hκ : κ ≤ 32) (L : MemoryImage κ)
    (kv : ℕ → ℕ) (hkv : ∀ i < 8, kv i ≤ 30) (kb gsq : E) (rets : List E)
    (hrel : coreProgram.Rel L.read "certify_stack" [kb, gsq] rets)
    (hkb : ∀ i < 8, LoadHolds L.read kb i (gen ^ kv i)) (ht : ExpTables L.read gsq) :
    ∃ ρ : ℕ → ℕ, (∀ r < 8, ρ r < 8) ∧ (∀ r < 7, csN kv (ρ (r + 1)) < csN kv (ρ r)) ∧
      (∀ r < 8, csKap kv (ρ r) < 34) ∧
      ∃ out : E, rets = [gen ^ max 16 (log2Ceil (csTot kv ρ 8)), out, out * gen ^ 52] ∧
        ∀ r < 8, ∀ j < (csG (ρ r)).len,
          LoadHolds L.read out ((csG (ρ r)).b0 + j) (gen ^ (csTot kv ρ r + j * 2 ^ csKap kv (ρ r))) ∧
          LoadHolds L.read out (52 + (csG (ρ r)).b0 + j) (gen ^ csKap kv (ρ r)) := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_certify_stack _ _).mp hrel
  rw [certify_stack_params] at hp
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨hp0, hp1⟩ := hp
  rw [certify_stack_body, csBody_split, holdsList_flat_ret _ csBodyA_flat] at hb
  obtain ⟨hA, hret⟩ := hb
  rw [← hp1] at ht
  simp only [csBodyA, csKeys_end, allOk_append] at hA
  obtain ⟨⟨⟨⟨⟨⟨hL, hK⟩, -⟩, hR⟩, hcall⟩, hO⟩, hfin⟩ := hA
  simp only [Nat.reduceAdd, Nat.reduceMul] at hR hcall hO hfin
  rw [csOuts_end] at hfin
  -- the kappa sources
  have hload : ∀ i < 8, σ (.n (2 + i)) = gen ^ kv i := fun i hi ↦ by
    have := hL (.atom (.load (.n (2 + i)) (.n 0) i))
      (List.mem_append.2 (Or.inl (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))
    simp only [StmtOk, Atom.Holds] at this
    rw [hp0] at this
    exact loadHolds_unique this (hkb i hi)
  have hkv' : ∀ i < 8, kv i < 2 ^ 40 := fun i hi ↦ by have := hkv i hi; omega
  -- the groups
  have hgrp : ∀ gi < 8, csKap kv gi < 34 ∧
      (∃ key, LoadHolds L.read (σ (.n 10)) gi key ∧ key * gen ^ (csG gi).b0 = gen ^ (53 * csKap kv gi)) ∧
      LoadHolds L.read (σ (.n 11)) gi (gen ^ csSize kv gi) := fun gi hgi ↦ by
    obtain ⟨s', hs'⟩ := csKeys_each 8 0 12 hK gi hgi
    rw [Nat.zero_add] at hs'
    exact csKey_sound hκ (by omega) L kv hkv' hload ht hgi s' hs'
  choose! keyF hkeyF using fun gi hgi ↦ (hgrp gi hgi).2.1
  -- the ranks
  simp only [csRanks, allOk_append, allOk_flatten, List.mem_map, List.mem_range,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hR
  obtain ⟨hR0, hRr⟩ := hR
  obtain ⟨ρ0, hρ0, -, hk0, hat0, hsz0⟩ := csRank0_sound hκ (by omega) L 163 164 165 hR0
  have hRr' := fun r (hr : r < 7) ↦ csRank_sound hκ hκ11 L 163 164 (165 + 11 + 18 * r)
    (if r = 0 then 165 + 6 else 165 + 11 + 18 * (r - 1) + 6)
    (if r = 0 then 165 + 10 else 165 + 11 + 18 * (r - 1) + 17) (r + 1) (hRr r hr)
  choose! ρs hρs _hord hks hdesc hats hszs htots using hRr'
  set ρ : ℕ → ℕ := fun r ↦ if r = 0 then ρ0 else ρs (r - 1) with hρdef
  have hρlt : ∀ r < 8, ρ r < 8 := fun r hr ↦ by
    rcases r with _ | r
    · exact hρ0
    · exact hρs r (by omega)
  have hkap : ∀ r < 8, csKap kv (ρ r) < 34 := fun r hr ↦ (hgrp _ (hρlt r hr)).1
  -- each rank's key is its group's
  have hkeyR : ∀ r < 8, σ (.n (if r = 0 then 165 + 6 else 165 + 11 + 18 * (r - 1) + 6)) = keyF (ρ r) :=
    fun r hr ↦ by
    rcases r with _ | r
    · exact loadHolds_unique hk0 (hkeyF ρ0 hρ0).1
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      exact loadHolds_unique (hks r (by omega)) (hkeyF _ (hρs r (by omega))).1
  -- the descent
  have hdes : ∀ r < 7, csN kv (ρ (r + 1)) < csN kv (ρ r) := fun r hr ↦ by
    obtain ⟨e, he, hpk⟩ := hdesc r hr
    rw [hkeyR r (by omega)] at hpk
    have h1 := csKey_shift (hρlt r (by omega)) (hkeyF _ (hρlt r (by omega))).2
    have h2 := csKey_shift (hρlt (r + 1) (by omega)) (hkeyF _ (hρlt (r + 1) (by omega))).2
    have hs : ∀ gi < 8, csN kv gi < 2 ^ 12 := fun gi hgi ↦ by
      have := (hgrp gi hgi).1; unfold csN; omega
    have hk1 := hkeyR (r + 1) (by omega)
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hk1
    have key : gen ^ csN kv (ρ r) = gen ^ (e + 1 + csN kv (ρ (r + 1))) := by
      rw [← h1, hpk, hk1, mul_assoc, h2, ← pow_add]
    have := gen_pow_inj (by have := hs _ (hρlt r (by omega)); omega)
      (by have := hs _ (hρlt (r + 1) (by omega)); omega) key
    omega
  -- the totals
  have hsize : ∀ r < 8, σ (.n (if r = 0 then 165 + 10 else 165 + 11 + 18 * (r - 1) + 16)) =
      gen ^ csSize kv (ρ r) := fun r hr ↦ by
    rcases r with _ | r
    · exact loadHolds_unique hsz0 (hgrp ρ0 hρ0).2.2
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      exact loadHolds_unique (hszs r (by omega)) (hgrp _ (hρs r (by omega))).2.2
  have htot : ∀ r < 8, σ (.n (if r = 0 then 165 + 10 else 165 + 11 + 18 * (r - 1) + 17)) =
      gen ^ csTot kv ρ (r + 1) := by
    intro r
    induction r with
    | zero =>
      intro _
      have := hsize 0 (by decide)
      simp only [↓reduceIte] at this ⊢
      rw [this, csTot_succ]; simp [csTot]
    | succ r ih =>
      intro hr
      have := htots r (by omega)
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at this ⊢
      rw [show 165 + 11 + 18 * r + 17 = 165 + 11 + 18 * r + 17 from rfl, this, ih (by omega),
        csTot_succ kv ρ (r + 1), pow_add]
      congr 1
      have := hsize (r + 1) (by omega)
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at this
      exact this
  have hatR : ∀ r < 8, LoadHolds L.read (σ (.n 164)) (ρ r) (gen ^ csTot kv ρ r) := fun r hr ↦ by
    rcases r with _ | r
    · simp only [hρdef, ↓reduceIte, csTot, Finset.range_zero, Finset.sum_empty, pow_zero]
      exact hat0
    · have := hats r (by omega)
      have ht' := htot r (by omega)
      rw [ht'] at this
      simpa [hρdef] using this
  -- the stack's log
  have hT : σ (.n 301) = gen ^ csTot kv ρ 8 := by
    have := htot 7 (by decide)
    simpa using this
  have hTlt : csTot kv ρ 8 < 2 ^ 60 := by
    have : csTot kv ρ 8 ≤ 8 * (14 * 2 ^ 33) := by
      unfold csTot
      calc ∑ r' ∈ Finset.range 8, csSize kv (ρ r') ≤ ∑ _r' ∈ Finset.range 8, 14 * 2 ^ 33 :=
            Finset.sum_le_sum fun r' hr' ↦ csSize_le (hρlt r' (Finset.mem_range.1 hr'))
              (hkap r' (Finset.mem_range.1 hr'))
        _ = 8 * (14 * 2 ^ 33) := by simp
    omega
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, List.map_cons, List.map_nil] at hcall
  have hlog := (log2_holds hκ (by omega) L _ _ ht _).1 hcall.1
  rw [hT] at hlog
  obtain ⟨-, hgmv⟩ := (meaningLog2CeilExp_pow (by decide) hTlt _ _).1 hlog
  simp only [List.cons.injEq, and_true] at hgmv
  -- the returns
  simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, osCst, osMul, Nat.reduceAdd] at hfin
  obtain ⟨c1, c2, c3, c4⟩ := hfin
  simp only [List.map_cons, List.map_nil] at hret
  refine ⟨ρ, hρlt, hdes, hkap, σ (.n 303), ?_, fun r hr ↦ ?_⟩
  · rw [← hret, c1, c2, c4, c3, csW_eq (by decide), hgmv]
  · obtain ⟨s', hs'⟩ := csOuts_each 303 164 8 0 304 hO (ρ r) (hρlt r hr)
    rw [Nat.zero_add] at hs'
    exact csOut_sound kv hload ht (hρlt r hr) (hkap r hr) (hatR r hr) s' hs'

end
end LeanVM.Guest.B1.Stack
