/-
  LeanVM.Guest.B1.VsC.VsOrcPhC

  Shared pieces of the honest phases `Ph7` to `Ph11`: the eq tensors' closed form, index regions for
  a callee's arrays, the honest oracle's constant returns.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcTail
public import LeanVM.Guest.B1.VsC.VsOrcHonest
public import LeanVM.Guest.B1.VsC.VsOrcSpec

/-!
# The honest phases' shared pieces

* `eqLevels rs n`: an `eqtree`'s buffer, the levels `eqKernel (rs.take t)` for `t = 1 ..= n` one after
  the other; `eqLevels_lev` is the phases' `hlev`.
* `idxRegion`: a list of index arrays' cells. A callee's placed statement loads from `ptrRegion` of its
  pointer arrays, closed under the address's period; `CallAtA.addrR` narrows it to the arrays' own
  indices (`ptrRegion_idx`), as the phases' `hRc` asks. `ptrsBelow_idx`: `PtrsBelow` from the indices.
* `vsPlain i`: word `i` of the honest oracle `vsW` is `ret`'s (`vsW_retC`: a constant return).
* `chainLast_ne`: a nonempty chain's last state does not depend on its start.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The eq tensors' closed form -/

theorem eqLevels_succ (rs : List E) (n : ℕ) : eqLevels rs (n + 1) = eqLevels rs n ++ eqKernel (rs.take (n + 1)) := by
  simp [eqLevels, List.range_succ, List.flatMap_append]

theorem eqLevels_length {rs : List E} : ∀ {n : ℕ}, n ≤ rs.length → (eqLevels rs n).length = 2 ^ (n + 1) - 2
  | 0, _ => by simp [eqLevels]
  | n + 1, h => by
    rw [eqLevels_succ, List.length_append, eqLevels_length (by omega), length_eqKernel_eq', List.length_take,
      min_eq_left h]
    have : 2 ≤ 2 ^ (n + 1) := Nat.le_self_pow (by omega) 2
    rw [show 2 ^ (n + 1 + 1) = 2 ^ (n + 1) + 2 ^ (n + 1) by ring]
    omega

theorem eqLevels_prefix (rs : List E) {t : ℕ} : ∀ {n : ℕ}, t ≤ n → ∃ m, eqLevels rs n = eqLevels rs t ++ m
  | n, h => by
    induction n with
    | zero => exact ⟨[], by rw [Nat.le_zero.mp h, List.append_nil]⟩
    | succ n ih =>
      rcases Nat.lt_or_ge n t with h' | h'
      · exact ⟨[], by rw [show t = n + 1 by omega, List.append_nil]⟩
      · obtain ⟨m, hm⟩ := ih h'
        exact ⟨m ++ eqKernel (rs.take (n + 1)), by rw [eqLevels_succ, hm, List.append_assoc]⟩

/-- **The eq buffer's levels**: word `2^t - 2 + i` of `eqLevels rs n` is level `t`'s word `i`. -/
theorem eqLevels_lev {rs : List E} {n : ℕ} (hn : n ≤ rs.length) :
    ∀ t, 1 ≤ t → t ≤ n → ∀ i < 2 ^ t, (eqLevels rs n)[2 ^ t - 2 + i]? = some ((eqKernel (rs.take t)).getD i 0) := by
  intro t h1 h2 i hi
  obtain ⟨m, hm⟩ := eqLevels_prefix rs h2
  have ht : t = (t - 1) + 1 := by omega
  have hl : (eqLevels rs (t - 1)).length = 2 ^ t - 2 := by
    rw [eqLevels_length (by omega), ← ht]
  have hk : (eqKernel (rs.take t)).length = 2 ^ t := by
    rw [length_eqKernel_eq', List.length_take, min_eq_left (by omega)]
  have e : eqLevels rs t = eqLevels rs (t - 1) ++ eqKernel (rs.take t) := by
    conv_lhs => rw [ht]
    rw [eqLevels_succ, ← ht]
  rw [hm, e, List.append_assoc, List.getElem?_append_right (by omega), hl, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by omega), List.getD_eq_getElem _ _ (by omega), List.getElem?_eq_getElem]

theorem eqLevels_length_le {rs : List E} {n m : ℕ} (hn : n ≤ rs.length) (hm : m ≤ 2 ^ (n + 1) - 2) :
    m ≤ (eqLevels rs n).length := by
  rw [eqLevels_length hn]; exact hm

/-! ## Index regions -/

/-- The cells of index arrays `(base, length)`. -/
def idxRegion (arrs : List (ℕ × ℕ)) (i : ℕ) : Prop := ∃ q ∈ arrs, ∃ t < q.2, i = q.1 + t

/-- A cell of pointer arrays has the address of a cell of the index arrays. -/
theorem ptrRegion_idx {arrs : List (ℕ × ℕ)} {i : ℕ}
    (h : ptrRegion (arrs.map fun q => (ptrAt q.1, q.2)) i) :
    ∃ j, addressOfIndex j = addressOfIndex i ∧ idxRegion arrs j := by
  obtain ⟨q', hq', t, ht, he⟩ := h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
  exact ⟨q.1 + t, by rw [← he, Main.addr_ofK], q, hq, t, ht, rfl⟩

theorem ptrsBelow_idx {arrs : List (ℕ × ℕ)} {fp : ℕ} (h : ∀ q ∈ arrs, q.1 + q.2 ≤ fp) :
    PtrsBelow (arrs.map fun q => (ptrAt q.1, q.2)) fp := by
  intro q' hq' t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hq'
  exact ⟨q.1 + t, by have := h q hq; simp only at ht; omega, Main.addr_ofK _ _⟩

section
variable {P : Core.Program} {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

mutual
/-- `loadsInA_mono` up to the address: each cell of `R` has the address of a cell of `R'`. -/
theorem loadsInA_addr : ∀ (t : Tree) {R R' : ℕ → Prop} (p : ℕ × ℕ),
    (∀ i, R i → ∃ j, addressOfIndex j = addressOfIndex i ∧ R' j) →
    t.LoadsInA P fs al cert R p → t.LoadsInA P fs al cert R' p
  | .node f σ bufs kids, R, R', p, hR, h => by
      rw [loadsInA_node] at h ⊢
      refine ⟨fun A hA => ?_, loadsInKidsA_addr kids _ (fun i hi => ?_) h.2⟩
      · obtain ⟨i, hi, h'⟩ := h.1 A hA
        rcases h' with h' | h'
        · exact ⟨i, hi, Or.inl h'⟩
        · obtain ⟨j, hj, hj'⟩ := hR i h'
          exact ⟨j, hi.trans hj.symm, Or.inr hj'⟩
      · rcases hi with hi | hi
        · exact ⟨i, rfl, Or.inl hi⟩
        · obtain ⟨j, hj, hj'⟩ := hR i hi
          exact ⟨j, hj, Or.inr hj'⟩
  | .phantom .., _, _, _, _, _ => loadsInA_phantom

/-- `loadsInA_addr` for the callees. -/
theorem loadsInKidsA_addr : ∀ (ks : List Tree) {R R' : ℕ → Prop} (ps : List (ℕ × ℕ)),
    (∀ i, R i → ∃ j, addressOfIndex j = addressOfIndex i ∧ R' j) →
    Tree.LoadsInKidsA P fs al cert R ps ks → Tree.LoadsInKidsA P fs al cert R' ps ks
  | [], _, _, _, _, _ => loadsInKidsA_nil
  | _ :: _, _, _, [], _, _ => by rw [Tree.LoadsInKidsA]; trivial
  | k :: ks, R, R', p :: ps, hR, h => by
      rw [loadsInKidsA_cons] at h ⊢
      exact ⟨loadsInA_addr k p hR h.1, loadsInKidsA_addr ks ps hR h.2⟩
end

mutual
/-- `hintsIn_mono` up to the address. -/
theorem hintsIn_addr : ∀ (t : Tree) {R R' : ℕ → Prop} (p : ℕ × ℕ),
    (∀ i, R i → ∃ j, addressOfIndex j = addressOfIndex i ∧ R' j) →
    t.HintsIn P fs al cert R p → t.HintsIn P fs al cert R' p
  | .node f σ bufs kids, R, R', p, hR, h => by
      rw [hintsIn_node] at h ⊢
      refine ⟨fun A hA => ?_, hintsInKids_addr kids _ (fun i hi => ?_) h.2⟩
      · obtain ⟨i, hi, h'⟩ := h.1 A hA
        rcases h' with h' | h'
        · exact ⟨i, hi, Or.inl h'⟩
        · obtain ⟨j, hj, hj'⟩ := hR i h'
          exact ⟨j, hi.trans hj.symm, Or.inr hj'⟩
      · rcases hi with hi | hi
        · exact ⟨i, rfl, Or.inl hi⟩
        · obtain ⟨j, hj, hj'⟩ := hR i hi
          exact ⟨j, hj, Or.inr hj'⟩
  | .phantom .., _, _, _, _, _ => hintsIn_phantom

/-- `hintsIn_addr` for the callees. -/
theorem hintsInKids_addr : ∀ (ks : List Tree) {R R' : ℕ → Prop} (ps : List (ℕ × ℕ)),
    (∀ i, R i → ∃ j, addressOfIndex j = addressOfIndex i ∧ R' j) →
    Tree.HintsInKids P fs al cert R ps ks → Tree.HintsInKids P fs al cert R' ps ks
  | [], _, _, _, _, _ => hintsInKids_nil
  | _ :: _, _, _, [], _, _ => by rw [Tree.HintsInKids]; trivial
  | k :: ks, R, R', p :: ps, hR, h => by
      rw [hintsInKids_cons] at h ⊢
      exact ⟨hintsIn_addr k p hR h.1, hintsInKids_addr ks ps hR h.2⟩
end

end

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **A call's region up to the address**: each cell of `R` has the address of a cell of `R'`. -/
theorem CallAtA.addrR {k : ℕ} {f : String} {args rets : List E} {R R' D : ℕ → Prop}
    {Out Pre : Reader → Prop} {Post : Reader → Tree → Prop} {B fp c e : ℕ}
    (h : CallAtA fs al cert k f args rets R D Out Pre Post B fp c e)
    (hR : ∀ i, R i → ∃ j, addressOfIndex j = addressOfIndex i ∧ R' j) :
    CallAtA fs al cert k f args rets R' D Out Pre Post B fp c e := by
  obtain ⟨W, hW, hce, hO', hr⟩ := h
  refine ⟨W, hW, hce, hO', fun rd hl hw hp => ?_⟩
  obtain ⟨t, hn, hv, hb, hB, he, hpl, hlo, hhi, hd, hq⟩ := hr rd hl hw hp
  exact ⟨t, hn, hv, hb, hB, he, hpl, loadsInA_addr t (fp, c) hR hlo, hintsIn_addr t (fp, c) hR hhi, hd, hq⟩

/-- A call on pointer arrays, its region narrowed to the arrays' indices. -/
theorem CallAtA.idxR {k : ℕ} {f : String} {args rets : List E} {arrs : List (ℕ × ℕ)} {D : ℕ → Prop}
    {Out Pre : Reader → Prop} {Post : Reader → Tree → Prop} {B fp c e : ℕ}
    (h : CallAtA fs al cert k f args rets (ptrRegion (arrs.map fun q => (ptrAt q.1, q.2))) D Out Pre Post B fp c e) :
    CallAtA fs al cert k f args rets (idxRegion arrs) D Out Pre Post B fp c e :=
  CallAtA.addrR h fun _ hi => ptrRegion_idx hi

end

/-! ## The honest oracle's constant returns -/

/-- Word `i` of the honest oracle is `ret`'s: no allocation, not the chunk count, no grind window. -/
abbrev vsPlain (i : ℕ) : Prop :=
  i ∉ vsAllocIdx ∧ i ≠ 42 ∧ ¬(512 ≤ i ∧ i ≤ 516) ∧ ¬(581 ≤ i ∧ i ≤ 586) ∧ ¬(2943 ≤ i ∧ i ≤ 2947)

/-- **A constant return of the honest oracle.** -/
theorem vsW_retC {rd1 : Reader} {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E} (ha : args.length = 6)
    (hr : CausalRule ret) {i : ℕ} (hi : vsPlain i) {c : E} (hc : ∀ σ, ret i σ = c) :
    vsW rd1 args cur p ret i = c := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hi
  rw [vsW_ret ha hr h1 h2 h3 h4 h5, hc]

/-! ## Chains -/

/-- A nonempty chain's last state does not depend on its start. -/
theorem chainLast_ne {l : List (E × RSt)} (hl : l ≠ []) (a b : RSt) : chainLast a l = chainLast b l := by
  rcases l with _ | ⟨⟨y, s⟩, l⟩
  · exact absurd rfl hl
  · rfl

end
end LeanVM.Guest.B1.VsC
