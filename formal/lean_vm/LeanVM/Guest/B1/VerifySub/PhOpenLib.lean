/-
  LeanVM.Guest.B1.VerifySub.PhOpenLib

  The pure lemmas the opening phase uses: the merged ring claim's target, the values of the stacked
  column claims, Horner's chain.
-/

module

public import LeanVM.Guest.B1.Stack.TermPure
public import LeanVM.Guest.B1.Stack.TermRing

/-!
# The opening phase's pure lemmas

* `ringMerge_two_snd`: the target of two merged ring claims is `ringTarget` of their slices summed,
  the second scaled by `rho`.
* `onStack_vals`, `filter_zip_take`, `lcc_values`: the values of the link's column claims with a
  placement are the first `55` sent values (`SENT_TARGET` holds every lane up to `55`, none after).
* `uL`, `horner_chain`: Horner's chain in `lam`, one step a sent value.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The merged ring claim's target -/

theorem mergeStep_fst (rho : E) (s : List E) (gs : List RingPointGroup) (ps : List (List E)) (r : E)
    (c : RingClaim) :
    (Stack.mergeStep rho (s, gs, ps, r) c).1 = s.zipIdx.map (fun (sum, i) ↦
        match c.slices[i]? with
        | some x => sum + r * x
        | none => sum) ∧
      (Stack.mergeStep rho (s, gs, ps, r) c).2.2.2 = r * rho := by
  unfold Stack.mergeStep
  generalize List.foldl (Stack.pieceStep r) (gs, ps) c.pieces = q
  obtain ⟨a, b⟩ := q
  exact ⟨rfl, rfl⟩

/-- **Two ring claims merged**: the target of the slices `s_k + rho · s_l`. -/
theorem ringMerge_two_snd (qp : Placement) (kp ks : List E) (ring : RingClaim) (f g : List E) (rho : E)
    (hks : ks.length = kBits) (hls : ring.slices.length = kBits) :
    (ringMerge [keccakRingClaim qp kp ks, ring] f g rho).2 =
      ringTarget ((List.range kBits).map fun i ↦ ks.getD i 0 + rho * ring.slices.getD i 0) f g := by
  show ringTarget ([keccakRingClaim qp kp ks, ring].foldl (Stack.mergeStep rho)
    (List.replicate kBits 0, [], [], 1)).1 f g = _
  congr 1
  rw [List.foldl_cons, List.foldl_cons, List.foldl_nil]
  obtain ⟨hs1, hr1⟩ := mergeStep_fst rho (List.replicate kBits 0) [] [] 1 (keccakRingClaim qp kp ks)
  generalize Stack.mergeStep rho (List.replicate kBits 0, [], [], 1) (keccakRingClaim qp kp ks) = st at hs1 hr1
  obtain ⟨s1, g1, p1, r1⟩ := st
  simp only at hs1 hr1
  rw [(mergeStep_fst rho s1 g1 p1 r1 ring).1, hs1, hr1]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_zipIdx, List.length_replicate] at h1
  have hk : i < ks.length := by omega
  have hl : i < ring.slices.length := by omega
  simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_replicate, List.getElem_range,
    keccakRingClaim, List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hl, Nat.zero_add]
  rw [List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hk]
  ring

/-! ## The column claims' values -/

/-- **A filter by a prefix**: where `P` holds exactly on the first `n` of `Z`, filtering the pairs of
`A` and `Z` by `P` keeps the first `n` of `A`. -/
theorem filter_zip_take {α β γ : Type} (f : α → γ) (P : β → Bool) :
    ∀ (A : List α) (Z : List β) (n : ℕ), A.length = Z.length →
      (∀ i (h : i < Z.length), (P Z[i] = true ↔ i < n)) →
      ((A.zip Z).filter (fun p ↦ P p.2)).map (fun p ↦ f p.1) = (A.map f).take n
  | [], _, n, _, _ => by simp
  | _ :: _, [], _, h, _ => by simp at h
  | a :: A, z :: Z, n, hl, hP => by
    have hl' : A.length = Z.length := by simpa using hl
    have hP' : ∀ i (h : i < Z.length), (P Z[i] = true ↔ i + 1 < n) := by
      intro i h
      have := hP (i + 1) (by simp; omega)
      simpa only [List.getElem_cons_succ] using this
    rcases n with _ | m
    · have hz : P z = false := by
        have := hP 0 (by simp)
        simpa using this
      rw [List.zip_cons_cons, List.filter_cons_of_neg (by simp [hz]),
        filter_zip_take f P A Z 0 hl' (fun i h ↦ by rw [hP' i h]; omega)]
      simp
    · have hz : P z = true := by
        have := hP 0 (by simp)
        simpa using this
      rw [List.zip_cons_cons, List.filter_cons_of_pos (by simp [hz]), List.map_cons,
        filter_zip_take f P A Z m hl' (fun i h ↦ by rw [hP' i h]; omega)]
      simp

/-- **The values of the claims with a placement**: those whose kind is not `1000`. -/
theorem onStack_vals {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hbl : buildLayout bytecode lm rows = some layout) :
    ∀ (Lc : List ColumnClaim) (Z : List ((ℕ × ℕ) × ℕ)), (∀ z ∈ Z, Stack.KindOk z.1.1 z.1.2 z.2) →
      Lc.map (·.column) = Z.map (·.1.2) →
      (Lc.filterMap (·.onStack layout)).map (·.2) =
        ((Lc.zip Z).filter (fun p ↦ p.2.2 != 1000)).map (fun p ↦ p.1.value)
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => by simp at h
  | c :: Lc, ((t, col), k) :: Z, hZ, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hc, h⟩ := h
    have ih := onStack_vals hbl Lc Z (fun z hz ↦ hZ z (List.mem_cons_of_mem _ hz)) h
    obtain ⟨-, hcl, -, hblk, hslot, hnone, hk⟩ := hZ _ List.mem_cons_self
    simp only at hcl hblk hslot hnone hc hk
    rw [List.filterMap_cons, List.zip_cons_cons, List.filter_cons]
    rcases Nat.lt_or_ge k 1000 with hk1 | hk1
    · obtain ⟨p, hp⟩ : ∃ p, layout.placements.getD col none = some p := by
        rcases Nat.lt_or_ge k 52 with hk52 | hk52
        · exact ⟨_, (hblk hk52) ▸ (Stack.block_placed hbl hk52).1⟩
        · obtain ⟨hs, -, -⟩ := hslot hk52 hk1
          obtain ⟨p2, -, hp⟩ := Stack.layout_slot hbl hcl hs
          exact ⟨_, hp⟩
      have hcs : c.onStack layout =
          some (fun y ↦ eqEval (p.stackPoint c.point layout.stackLog) y, c.value) := by
        simp only [ColumnClaim.onStack, hc, hp, Option.map_some]
      have hne : (k != 1000) = true := by simp; omega
      rw [hcs]
      simp only [hne, ite_true, List.map_cons, ih]
    · have hk1000 : k = 1000 := by omega
      obtain ⟨hs, hnb⟩ := hnone hk1000
      have hcs : c.onStack layout = none := by
        simp only [ColumnClaim.onStack, hc, Stack.layout_none hbl hcl hs hnb, Option.map_none]
      rw [hcs, hk1000]
      simpa using ih

theorem lcc_values_aux : ∀ (bases : List ℕ) (cols : List (List E × List (ℕ × E))),
    cols.length ≤ bases.length →
    ((bases.zip cols).flatMap fun (bpv : ℕ × List E × List (ℕ × E)) ↦
        bpv.2.2.map fun cv ↦ (⟨bpv.1 + cv.1, bpv.2.1, cv.2⟩ : ColumnClaim)).map (·.value) =
      cols.flatMap fun c ↦ c.2.map (·.2)
  | _, [], _ => by simp
  | [], _ :: _, h => by simp at h
  | b :: bases, c :: cols, h => by
    rw [List.zip_cons_cons, List.flatMap_cons, List.map_append,
      lcc_values_aux bases cols (by simp at h; omega), List.flatMap_cons, List.map_map]
    rfl

/-- **The link's column claims' values** are its columns' values, in order. -/
theorem lcc_values (link : LinkEnd) (h : link.columns.length ≤ globalColumnBases.length) :
    (linkColumnClaims link).map (·.value) = link.columns.flatMap fun c ↦ c.2.map (·.2) := by
  unfold linkColumnClaims
  exact lcc_values_aux globalColumnBases link.columns h

/-! ## Horner's chain -/

/-- The values a chain added, the last first: `uL sv m = [sv (m - 1), …, sv 0]`. -/
def uL (sv : ℕ → E) : ℕ → List E
  | 0 => []
  | m + 1 => sv m :: uL sv m

theorem uL_length (sv : ℕ → E) : ∀ m, (uL sv m).length = m
  | 0 => rfl
  | m + 1 => by simp [uL, uL_length sv m]

theorem uL_getElem (sv : ℕ → E) : ∀ m i (h : i < (uL sv m).length), (uL sv m)[i] = sv (m - 1 - i)
  | 0, _, h => absurd h (by simp [uL])
  | m + 1, 0, _ => by simp [uL]
  | m + 1, i + 1, h => by
    simp only [uL, List.getElem_cons_succ]
    rw [uL_getElem sv m i (by simp [uL] at h; omega)]
    congr 1
    omega

/-- **Horner's chain**: `acc_{j+1} = (acc_j + sv j) · lam` from `acc_0 = lam · hornerL tail`. -/
theorem horner_chain (acc sv : ℕ → E) (lam : E) (tail : List E) (n : ℕ)
    (h0 : acc 0 = lam * Stack.hornerL lam tail) (hstep : ∀ j < n, acc (j + 1) = (acc j + sv j) * lam) :
    ∀ m ≤ n, acc m = lam * Stack.hornerL lam (uL sv m ++ tail)
  | 0, _ => by simpa [uL] using h0
  | m + 1, hm => by
    rw [hstep m (by omega), horner_chain acc sv lam tail n h0 hstep m (by omega)]
    simp only [uL, List.cons_append, Stack.hornerL]
    ring

end
end LeanVM.Guest.B1.VerifySub
