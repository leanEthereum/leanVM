/-
  LeanVM.Guest.B1.Main.AggEqtree

  The inlined `eqtree` of `aggregate_claims` (G:762-777): its last layer is the equality kernel of
  the six coordinates it reads.
-/

module

public import LeanVM.Guest.B1.Main.AggTemplate

/-!
# `eqtree`

`eqtreeT pt off out b` reads `r_t = pt[off + t]`, `t < 6`, and writes layer `t` of the doubling at
`out[2^(t+1) - 2 ..)`; each entry of layer `t ≥ 1` reads its parent back from `out` before it
multiplies it. So, forward, the layer is `eqKernel (r_0 .. r_t)` (V:676), and the last one, at
`out[62 ..)`, is `eqKernel` of the six coordinates (`eqtree_sound`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The equality kernel -/

theorem eqKernel_append_one (rs : List E) (r : E) :
    eqKernel (rs ++ [r]) = (eqKernel rs).map (· * (1 + r)) ++ (eqKernel rs).map (· * r) := by
  simp [eqKernel, List.foldl_append]

theorem length_eqKernel (rs : List E) : (eqKernel rs).length = 2 ^ rs.length := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [eqKernel_append_one, List.length_append, List.length_map, List.length_map, ih,
      List.length_append, List.length_singleton, pow_succ]
    ring

theorem eqKernel_take_succ (rs : List E) (t : ℕ) (ht : t < rs.length) :
    eqKernel (rs.take (t + 1)) = (eqKernel (rs.take t)).map (· * (1 + rs.getD t 0)) ++
      (eqKernel (rs.take t)).map (· * rs.getD t 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, eqKernel_append_one,
    List.getD_eq_getElem _ _ ht]

theorem eqKernel_getD_lo (l : List E) (r : E) {i : ℕ} (hi : i < 2 ^ l.length) :
    ((eqKernel l).map (· * (1 + r)) ++ (eqKernel l).map (· * r)).getD i 0 =
      (eqKernel l).getD i 0 * (1 + r) := by
  have hl := length_eqKernel l
  rw [List.getD_eq_getElem _ _ (by simp [hl]; omega), List.getElem_append_left (by simp [hl, hi]),
    List.getElem_map, List.getD_eq_getElem _ _ (by omega)]

theorem eqKernel_getD_hi (l : List E) (r : E) {i : ℕ} (hi : i < 2 ^ l.length) :
    ((eqKernel l).map (· * (1 + r)) ++ (eqKernel l).map (· * r)).getD (2 ^ l.length + i) 0 =
      (eqKernel l).getD i 0 * r := by
  have hl := length_eqKernel l
  rw [List.getD_eq_getElem _ _ (by simp [hl]; omega), List.getElem_append_right (by simp [hl]),
    List.getElem_map, List.getD_eq_getElem _ _ (by omega)]
  simp [hl]

/-! ## The block -/

theorem noRetList_append (a b : List Stmt) :
    Stmt.noRetList (a ++ b) = (Stmt.noRetList a && Stmt.noRetList b) := by
  induction a with
  | nil => simp [Stmt.noRetList]
  | cons s a ih => simp [Stmt.noRetList, ih, Bool.and_assoc]

theorem noRetList_flatten : ∀ (bs : List (List Stmt)), (∀ b ∈ bs, Stmt.noRetList b = true) →
    Stmt.noRetList bs.flatten = true
  | [], _ => rfl
  | b :: bs, h => by
    rw [List.flatten_cons, noRetList_append, h b (by simp), noRetList_flatten bs fun c hc =>
      h c (by simp [hc])]
    rfl

theorem noRetList_etLayer (pt : V) (off : ℕ) (out : V) (b t : ℕ) :
    Stmt.noRetList (etLayer pt off out b t) = true := by
  rw [etLayer, noRetList_append, noRetList_flatten _ (by simp [etEntry, Stmt.noRetList, Stmt.noRet])]
  rfl

/-- The coordinate `eqtree` reads at layer `t`. -/
def etR (σ : Val) (b t : ℕ) : E := σ (.n (if t = 0 then b else etBase b t))

/-- The six coordinates. -/
def etRs (σ : Val) (b : ℕ) : List E := (List.range 6).map (etR σ b)

theorem length_etRs (σ : Val) (b : ℕ) : (etRs σ b).length = 6 := by simp [etRs]

theorem etRs_getD (σ : Val) (b t : ℕ) (ht : t < 6) : (etRs σ b).getD t 0 = etR σ b t := by
  simp [etRs, List.getD_eq_getElem?_getD, ht]

/-- **`eqtree`, forward**: the six coordinates it reads at `pt·g^off`, and the equality kernel of
them at `out·g^62`. -/
theorem eqtree_sound (pt out : V) (off b : ℕ) (kret : List E → Prop)
    (h : Stmt.HoldsList C rd σ (eqtreeT pt off out b) True kret) :
    (∀ t < 6, LoadHolds rd (σ pt) (off + t) ((etRs σ b).getD t 0)) ∧
      ∀ i < 64, LoadHolds rd (σ out) (62 + i) ((eqKernel (etRs σ b)).getD i 0) := by
  rw [eqtreeT, holdsList_append,
    holdsList_range_flatten 5 (fun t => etLayer pt off out b (t + 1)) (fun _ => noRetList_etLayer ..)] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one] at h
  obtain ⟨l0, c1, a2, s0, s1, hL, -⟩ := h
  have hL' : ∀ t < 5, LoadHolds rd (σ pt) (off + (t + 1)) (σ (.n (etBase b (t + 1)))) ∧
      σ (.n (etBase b (t + 1) + 2)) = 1 + σ (.n (etBase b (t + 1))) ∧
      ∀ i < 2 ^ (t + 1),
        LoadHolds rd (σ out) (2 ^ (t + 1) - 2 + i) (σ (.n (etBase b (t + 1) + 3 + 3 * i))) ∧
        LoadHolds rd (σ out) (2 ^ (t + 1 + 1) - 2 + i)
          (σ (.n (etBase b (t + 1) + 3 + 3 * i)) * σ (.n (etBase b (t + 1) + 2))) ∧
        LoadHolds rd (σ out) (2 ^ (t + 1 + 1) - 2 + 2 ^ (t + 1) + i)
          (σ (.n (etBase b (t + 1) + 3 + 3 * i)) * σ (.n (etBase b (t + 1)))) := by
    intro t ht
    have := hL t ht
    rw [etLayer, holdsList_append,
      holdsList_range_flatten _ (etEntry out b (t + 1)) (fun _ => rfl)] at this
    simp only [etEntry, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_one] at this
    obtain ⟨lr, c, a, he, -⟩ := this
    refine ⟨lr, by rw [a, c], fun i hi => ?_⟩
    obtain ⟨p0, m1, p1, m2, p2, -⟩ := he i hi
    refine ⟨p0, ?_, ?_⟩
    · rw [← m1]; exact p1
    · rw [← m2]; exact p2
  have hR : ∀ t < 6, LoadHolds rd (σ pt) (off + t) ((etRs σ b).getD t 0) := by
    intro t ht
    rw [etRs_getD σ b t ht, etR]
    rcases t with _ | t
    · simpa using l0
    · simp only [Nat.add_one_ne_zero, ↓reduceIte]; exact (hL' t (by omega)).1
  refine ⟨hR, ?_⟩
  -- layer `t`, by induction
  have key : ∀ t < 6, ∀ i < 2 ^ (t + 1), LoadHolds rd (σ out) (2 ^ (t + 1) - 2 + i)
      ((eqKernel ((etRs σ b).take (t + 1))).getD i 0) := by
    intro t
    induction t with
    | zero =>
      intro _ i hi
      have e : eqKernel ((etRs σ b).take 1) = [1 * (1 + σ (.n b)), 1 * σ (.n b)] := by
        simp only [etRs, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl, List.map_cons,
          List.take_succ_cons, List.take_zero, etR, ↓reduceIte]
        rfl
      rw [e]
      interval_cases i
      · simpa [a2, c1] using s0
      · simpa using s1
    | succ t ih =>
      intro ht i hi
      obtain ⟨-, h2, hent⟩ := hL' t (by omega)
      have hlen : ((etRs σ b).take (t + 1)).length = t + 1 := by
        rw [List.length_take, length_etRs]; omega
      rw [eqKernel_take_succ _ _ (by rw [length_etRs]; omega), etRs_getD σ b _ (by omega)]
      simp only [etR, Nat.add_one_ne_zero, ↓reduceIte]
      rcases Nat.lt_or_ge i (2 ^ (t + 1)) with hlo | hhi
      · obtain ⟨p0, p1, -⟩ := hent i hlo
        have := loadHolds_unique p0 (ih (by omega) i hlo)
        rw [eqKernel_getD_lo _ _ (by rw [hlen]; exact hlo), ← this, ← h2]
        exact p1
      · obtain ⟨p0, -, p2⟩ := hent (i - 2 ^ (t + 1)) (by rw [pow_succ] at hi; omega)
        have := loadHolds_unique p0 (ih (by omega) _ (by rw [pow_succ] at hi; omega))
        have hi' : i = 2 ^ ((etRs σ b).take (t + 1)).length + (i - 2 ^ (t + 1)) := by
          rw [hlen]; omega
        rw [hi', eqKernel_getD_hi _ _ (by rw [hlen, pow_succ] at *; omega), ← this, ← hi']
        rw [show 2 ^ (t + 1 + 1) - 2 + 2 ^ (t + 1) + (i - 2 ^ (t + 1)) = 2 ^ (t + 1 + 1) - 2 + i by
          rw [pow_succ 2 (t + 1)]; omega] at p2
        exact p2
  intro i hi
  have := key 5 (by omega) i hi
  rwa [List.take_of_length_le (by rw [length_etRs])] at this

end
end LeanVM.Guest.B1.Main
