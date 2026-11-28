/-
  LeanVM.Guest.B1.Stack.CertifyO

  What `certify_stack`'s outputs hold: per block, `g^offset` and `g^κ`.
-/

module

public import LeanVM.Guest.B1.Stack.CertifyR
import LeanVM.Guest.Value.FieldBits

/-!
# `certify_stack`'s outputs

Group `gi`'s blocks (`csOut_sound`): from `group_at[gi] = g^A`, block `b0 + j`, `j < len`, holds
`g^(A + j·2^κ)` at `outs[b0 + j]` and `g^κ` at `outs[52 + b0 + j]`. `csKeys_each`, `csOuts_each`: the
groups' statement lists of the template's recursions, each at some start.
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem csKeys_each : ∀ (n gi s : ℕ), AllOk C rd σ (csKeys gi n s).1 →
    ∀ j < n, ∃ s', AllOk C rd σ (csKey (gi + j) s').1
  | 0, _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, gi, s, h, j, hj => by
    simp only [csKeys, allOk_append] at h
    rcases j with _ | j
    · exact ⟨s, h.1⟩
    · obtain ⟨s', hs'⟩ := csKeys_each n (gi + 1) _ h.2 j (by omega)
      exact ⟨s', by rw [show gi + (j + 1) = gi + 1 + j by omega]; exact hs'⟩

theorem csOuts_each (out at_ : ℕ) : ∀ (n gi s : ℕ), AllOk C rd σ (csOuts out at_ gi n s).1 →
    ∀ j < n, ∃ s', AllOk C rd σ (csOut out at_ (gi + j) s').1
  | 0, _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, gi, s, h, j, hj => by
    simp only [csOuts, allOk_append] at h
    rcases j with _ | j
    · exact ⟨s, h.1⟩
    · obtain ⟨s', hs'⟩ := csOuts_each out at_ n (gi + 1) _ h.2 j (by omega)
      exact ⟨s', by rw [show gi + (j + 1) = gi + 1 + j by omega]; exact hs'⟩

/-- **Group `gi`'s blocks**: from `group_at[gi] = g^A`, `g^(A + j·2^κ)` at `outs[b0 + j]` and
`g^κ` at `outs[52 + b0 + j]`, `j < len`. -/
theorem csOut_sound (kv : ℕ → ℕ) (hkb : ∀ i < 8, σ (.n (2 + i)) = gen ^ kv i)
    (ht : ExpTables rd (σ (.n 1))) {out at_ gi : ℕ} (hgi : gi < 8) (hk : csKap kv gi < 34)
    {A : ℕ} (hA : LoadHolds rd (σ (.n at_)) gi (gen ^ A)) (s : ℕ)
    (h : AllOk C rd σ (csOut out at_ gi s).1) :
    ∀ j < (csG gi).len, LoadHolds rd (σ (.n out)) ((csG gi).b0 + j) (gen ^ (A + j * 2 ^ csKap kv gi)) ∧
      LoadHolds rd (σ (.n out)) (52 + (csG gi).b0 + j) (gen ^ csKap kv gi) := by
  obtain ⟨hsrc, hadj, hl1, -, -⟩ := csGroups_facts gi hgi
  unfold csOut at h
  simp only [allOk_append, allOk_cons, allOk_nil, and_true, allOk_flatten, List.mem_map,
    List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  obtain ⟨⟨hkp, hm, hld, hat, hst, hsk⟩, hbl⟩ := h
  have hv : σ (.n (csKappa (csG gi) s).2.1) = gen ^ csKap kv gi :=
    csKappa_val kv hkb hsrc (by omega) s hkp
  simp only [StmtOk, Atom.Holds] at hm hld hat hst hsk
  rw [hm, hv, loadHolds_mul_gen_pow, Nat.add_zero] at hld
  have hsq := loadHolds_unique hld (ht.1 _ (show csKap kv gi < sizeBits from hk))
  have ha := loadHolds_unique hat hA
  set s' := (csKappa (csG gi) s).2.2 with hs'
  -- the running offsets
  have hrun : ∀ j < (csG gi).len, σ (.n (s' + 2 + j)) = gen ^ (A + j * 2 ^ csKap kv gi) := by
    intro j
    induction j with
    | zero => intro _; rw [Nat.add_zero, ha, Nat.zero_mul, Nat.add_zero]
    | succ j ih =>
      intro hj
      have := hbl j (by omega)
      simp only [StmtOk, Atom.Holds] at this
      rw [show s' + 2 + (j + 1) = s' + 3 + j by omega, this.1, ih (by omega), hsq, ← pow_add]
      congr 1; unfold csKap; ring
  intro j hj
  rcases j with _ | j
  · refine ⟨by rw [Nat.add_zero, ← hrun 0 hl1]; exact hst, ?_⟩
    rw [Nat.add_zero, ← hv]; exact hsk
  · have := hbl j (by omega)
    simp only [StmtOk, Atom.Holds] at this
    obtain ⟨-, l1, l2⟩ := this
    refine ⟨?_, ?_⟩
    · rw [← hrun (j + 1) hj, show s' + 2 + (j + 1) = s' + 3 + j by omega,
        show (csG gi).b0 + (j + 1) = (csG gi).b0 + 1 + j by omega]
      exact l1
    · rw [show 52 + (csG gi).b0 + (j + 1) = 52 + (csG gi).b0 + 1 + j by omega, ← hv]
      exact l2

end
end LeanVM.Guest.B1.Stack
