/-
  LeanVM.Guest.B1.Whir.CCaps

  A level's honest Merkle cap on f128: the cells and flags one query step's openings give, when
  they agree wherever they meet (`Limits.OpeningsAgree`).
-/

module

public import LeanVM.Guest.B1.Merkle.Climb
public import LeanVM.Guest.B1.Opening.Interface
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Protocol.WithHashBridge

/-!
# The honest cap

A query step's openings `batch` (positions below `2^depth`, each climbing to `root`), agreeing
wherever they meet, give every node of the tree they touch one digest (`nodeD`). The honest cap of
depth `cd`:

* `capCell k`: node `k / 2`'s cell `k % 2` (its digest's two halves);
* `capFl k`: `1` on the nodes strictly between the cap's leaves and its root on some opening's
  climb, `0` elsewhere.

`cap_meaning`: on a memory holding them, `verify_merkle_cap`'s meaning holds, returning the root's
cells. `cap_writes`: every opening's cap leaf holds its climb's digest there, its parent flagged.

At a phase accepted at the positions `ps`: `capCellH`, `capFlH`, `capH_meaning`, `capH_query`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Value.Keccak

@[expose] public section

/-! ## Openings that pass `openOne` -/

/-- **An opening that passes `openOne`** has its shape and climbs from its leaf's digest to the
root. -/
theorem openOne_facts {root : Digest} {height width q : ℕ} {o : Opening}
    (h : Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width q o) = true) :
    o.leaf.length = width ∧ o.path.length = height ∧ climbD (merkleLeafDigest o.leaf) q o.path = root := by
  unfold Compile.openOneWithHash at h
  split at h
  · rename_i hs
    refine ⟨hs.1, hs.2, ?_⟩
    have h' : decide ((climbD (merkleLeafDigest o.leaf) q o.path).toList = root.toList) = true := h
    exact Vector.toList_inj.mp (of_decide_eq_true h')
  · simp [Id.run, pure] at h

/-- `Limits.climbTo` is `climbD`. -/
theorem climbTo_eq (node : Digest) (q : ℕ) (path : List Digest) :
    Guest.Limits.climbTo node q path = climbD node q path := by
  rw [Guest.Limits.climbTo, climb_eq_withHash, keccak256With_keccakF1600]
  rfl

/-- A parent's cells hash its children's. -/
theorem hashesPair_of (dl dr : Digest) :
    HashesPair (digestHalves dl).1 (digestHalves dl).2 (digestHalves dr).1 (digestHalves dr).2
      (digestHalves (hashPair dl dr)).1 (digestHalves (hashPair dl dr)).2 := by
  show _ = _
  rw [hashPair, ← cellsBytes_digestScalars, ← cellsBytes_digestScalars, ← cellsBytes_append]
  rfl

/-! ## The tree's nodes -/

/-- The heap index of an opening's node `l` levels up. -/
abbrev heapNode (depth q l : ℕ) : ℕ := Guest.Limits.merkleHeapIndex depth q l

theorem heapNode_parent {depth q l : ℕ} (hl : l < depth) :
    heapNode depth q (l + 1) = heapNode depth q l / 2 := by
  unfold heapNode Guest.Limits.merkleHeapIndex
  have e : 2 ^ (depth - l) = 2 * 2 ^ (depth - (l + 1)) := by
    rw [show depth - l = depth - (l + 1) + 1 by omega, pow_succ]; ring
  rw [e, pow_succ, ← Nat.div_div_eq_div_mul]
  omega

theorem heapNode_child {depth q l : ℕ} (hl : l < depth) :
    heapNode depth q l = 2 * heapNode depth q (l + 1) + q / 2 ^ l % 2 := by
  unfold heapNode Guest.Limits.merkleHeapIndex
  have e : 2 ^ (depth - l) = 2 * 2 ^ (depth - (l + 1)) := by
    rw [show depth - l = depth - (l + 1) + 1 by omega, pow_succ]; ring
  rw [e, pow_succ, ← Nat.div_div_eq_div_mul]
  omega

theorem sibNode_eq {depth q l : ℕ} :
    Guest.Limits.siblingHeapIndex depth q l = 2 * heapNode depth q (l + 1) + (1 - q / 2 ^ l % 2) := by
  unfold Guest.Limits.siblingHeapIndex
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (q / 2 ^ l) with h | h <;> simp [h]

theorem heapNode_bounds {depth q l : ℕ} (hq : q < 2 ^ depth) (hl : l ≤ depth) :
    2 ^ (depth - l) ≤ heapNode depth q l ∧ heapNode depth q l < 2 * 2 ^ (depth - l) := by
  have : q / 2 ^ l < 2 ^ (depth - l) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos l), ← pow_add, Nat.sub_add_cancel hl]
    exact hq
  unfold heapNode Guest.Limits.merkleHeapIndex
  generalize q / 2 ^ l = t at this ⊢
  omega

theorem heapNode_top {depth q : ℕ} (hq : q < 2 ^ depth) : heapNode depth q depth = 1 := by
  unfold heapNode Guest.Limits.merkleHeapIndex; rw [Nat.sub_self, pow_zero, Nat.div_eq_of_lt hq]

/-! ## The honest digests -/

instance : Nonempty Digest := ⟨Vector.replicate 4 0⟩

variable (depth : ℕ) (batch : List (ℕ × Opening))

open Classical in
/-- **The digest the openings give the node `v`** (any, when none touches it). -/
noncomputable def nodeD (v : ℕ) : Digest :=
  Classical.epsilon fun d ↦ ∃ a ∈ batch, Guest.Limits.OpeningGivesNode depth a v d

/-- The honest cap's cell `k`: node `k / 2`'s cell `k % 2`. -/
noncomputable def capCell (k : ℕ) : E :=
  if k % 2 = 0 then (digestHalves (nodeD depth batch (k / 2))).1
  else (digestHalves (nodeD depth batch (k / 2))).2

open Classical in
/-- The honest cap's flag of node `k` (cap depth `cd`): `1` strictly between the cap's leaves and
its root on an opening's climb. -/
noncomputable def capFl (cd k : ℕ) : E :=
  if ∃ a ∈ batch, ∃ l, depth - cd + 1 ≤ l ∧ l < depth ∧ k = heapNode depth a.1 l then 1 else 0

variable {depth batch}

theorem nodeD_eq (hag : Guest.Limits.OpeningsAgree depth batch) {a : ℕ × Opening} (ha : a ∈ batch)
    {v : ℕ} {d : Digest} (h : Guest.Limits.OpeningGivesNode depth a v d) : nodeD depth batch v = d := by
  have hex : ∃ d, ∃ a ∈ batch, Guest.Limits.OpeningGivesNode depth a v d := ⟨d, a, ha, h⟩
  obtain ⟨a', ha', h'⟩ := Classical.epsilon_spec hex
  exact hag a' ha' a ha v _ _ h' h

theorem capCell_even (k : ℕ) :
    capCell depth batch (2 * k) = (digestHalves (nodeD depth batch k)).1 := by
  unfold capCell; simp

theorem capCell_odd (k : ℕ) :
    capCell depth batch (2 * k + 1) = (digestHalves (nodeD depth batch k)).2 := by
  unfold capCell
  simp only [show (2 * k + 1) % 2 ≠ 0 by omega, ↓reduceIte, show (2 * k + 1) / 2 = k by omega]

/-- The climb's node of an opening `l` levels up. -/
theorem nodeIs_climb {a : ℕ × Opening} {l : ℕ} (hl : l ≤ depth) :
    Guest.Limits.OpeningGivesNode depth a (heapNode depth a.1 l)
      (climbD (merkleLeafDigest a.2.leaf) a.1 (a.2.path.take l)) :=
  Or.inl ⟨l, hl, rfl, by rw [climbTo_eq]⟩

theorem nodeIs_sib {a : ℕ × Opening} {l : ℕ} (hl : l < depth) :
    Guest.Limits.OpeningGivesNode depth a (Guest.Limits.siblingHeapIndex depth a.1 l)
      (a.2.path.getD l default) :=
  Or.inr ⟨l, hl, rfl, rfl⟩

/-- **A node on an opening's climb hashes its children.** -/
theorem climb_hashes (hag : Guest.Limits.OpeningsAgree depth batch) {a : ℕ × Opening} (ha : a ∈ batch)
    (hlen : a.2.path.length = depth) {l : ℕ} (hl : l < depth) :
    let k := heapNode depth a.1 (l + 1)
    HashesPair (capCell depth batch (4 * k)) (capCell depth batch (4 * k + 1))
      (capCell depth batch (4 * k + 2)) (capCell depth batch (4 * k + 3))
      (capCell depth batch (2 * k)) (capCell depth batch (2 * k + 1)) := by
  intro k
  have hk : nodeD depth batch k = climbD (merkleLeafDigest a.2.leaf) a.1 (a.2.path.take (l + 1)) :=
    nodeD_eq hag ha (nodeIs_climb (by omega))
  have hc : nodeD depth batch (heapNode depth a.1 l) =
      climbD (merkleLeafDigest a.2.leaf) a.1 (a.2.path.take l) := nodeD_eq hag ha (nodeIs_climb (by omega))
  have hs : nodeD depth batch (Guest.Limits.siblingHeapIndex depth a.1 l) = a.2.path.getD l default :=
    nodeD_eq hag ha (nodeIs_sib hl)
  have htake : a.2.path.take (l + 1) = a.2.path.take l ++ [a.2.path.getD l default] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
    rfl
  have hlen' : (a.2.path.take l).length = l := by rw [List.length_take]; omega
  rw [htake, climbD_snoc, hlen'] at hk
  rw [capCell_even, capCell_odd, show 4 * k + 3 = 2 * (2 * k + 1) + 1 by ring,
    show 4 * k + 2 = 2 * (2 * k + 1) by ring, show 4 * k + 1 = 2 * (2 * k) + 1 by ring,
    show 4 * k = 2 * (2 * k) by ring, capCell_even, capCell_odd, capCell_even, capCell_odd]
  have hch := heapNode_child (q := a.1) hl
  have hsb := sibNode_eq (depth := depth) (q := a.1) (l := l)
  rcases Nat.mod_two_eq_zero_or_one (a.1 / 2 ^ l) with hb | hb
  · rw [hb, Nat.add_zero] at hch
    rw [hb, Nat.sub_zero] at hsb
    rw [← hsb, ← hch, hc, hs, hk]
    simp only [hb, ↓reduceIte]
    exact hashesPair_of _ _
  · rw [hb] at hch
    rw [hb, Nat.sub_self, Nat.add_zero] at hsb
    rw [← hch, ← hsb, hc, hs, hk]
    simp only [hb, one_ne_zero, ↓reduceIte]
    exact hashesPair_of _ _

theorem capFl_cases (cd k : ℕ) :
    (capFl depth batch cd k = 1 ∧ ∃ a ∈ batch, ∃ l, depth - cd + 1 ≤ l ∧ l < depth ∧
        k = heapNode depth a.1 l) ∨
      (capFl depth batch cd k = 0 ∧ ¬ ∃ a ∈ batch, ∃ l, depth - cd + 1 ≤ l ∧ l < depth ∧
        k = heapNode depth a.1 l) := by
  unfold capFl
  by_cases h : ∃ a ∈ batch, ∃ l, depth - cd + 1 ≤ l ∧ l < depth ∧ k = heapNode depth a.1 l
  · left; exact ⟨by simp only [h, ↓reduceIte], h⟩
  · right; exact ⟨by simp only [h, ↓reduceIte], h⟩

theorem isInK_zero : IsInK (0 : E) := by simpa using ofK_isInK 0

theorem isInK_one : IsInK (1 : E) := by
  have := gen_pow_isInK 0
  rwa [pow_zero] at this

/-- The openings of a query step, each at a position below `2^depth` climbing to `root`. -/
def BatchOpens (depth : ℕ) (root : Digest) (batch : List (ℕ × Opening)) : Prop :=
  ∀ a ∈ batch, a.1 < 2 ^ depth ∧ a.2.path.length = depth ∧
    climbD (merkleLeafDigest a.2.leaf) a.1 a.2.path = root

theorem nodeD_root {root : Digest} (hq : BatchOpens depth root batch)
    (hag : Guest.Limits.OpeningsAgree depth batch) {a : ℕ × Opening} (ha : a ∈ batch) :
    nodeD depth batch 1 = root := by
  obtain ⟨hlt, hlen, hcl⟩ := hq a ha
  have := nodeD_eq hag ha (nodeIs_climb (a := a) (l := depth) le_rfl)
  rw [heapNode_top hlt, List.take_of_length_le (by omega), hcl] at this
  exact this

/-- **The honest cap is checked**: on a memory holding the honest cells at `cap` and flags at
`flags`, `verify_merkle_cap`'s meaning holds, its returns the root's cells. -/
theorem cap_meaning {cd : ℕ} (hcd : 2 ≤ cd) (hcdd : cd ≤ depth) {root : Digest}
    (hq : BatchOpens depth root batch) (hag : Guest.Limits.OpeningsAgree depth batch) (hne : batch ≠ [])
    {rd : Reader} {cap flags : E}
    (hcap : ∀ k, 2 ≤ k → k < 2 ^ (cd + 2) → LoadHolds rd cap k (capCell depth batch k))
    (hfl : ∀ k, 2 ≤ k → k < 2 ^ cd → LoadHolds rd flags k (capFl depth batch cd k)) :
    MeaningVerifyMerkleCap cd rd [cap, flags] [(digestHalves root).1, (digestHalves root).2] := by
  obtain ⟨a0, ha0⟩ := List.exists_mem_of_ne_nil batch hne
  have hroot := nodeD_root hq hag ha0
  refine ⟨capCell depth batch, capFl depth batch cd, hcap, fun k h1 h2 ↦ ⟨hfl k h1 h2, ?_⟩,
    fun k hk1 hk2 hor ↦ ?_, fun k hk1 hk2 hf0 ↦ ?_, ?_⟩
  · rcases capFl_cases (depth := depth) (batch := batch) cd k with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
    · exact isInK_one
    · exact isInK_zero
  · obtain ⟨a, ha, l, hl, rfl⟩ : ∃ a ∈ batch, ∃ l, l < depth ∧ k = heapNode depth a.1 (l + 1) := by
      rcases hor with rfl | hf
      · refine ⟨a0, ha0, depth - 1, by omega, ?_⟩
        rw [show depth - 1 + 1 = depth by omega, heapNode_top (hq a0 ha0).1]
      · rcases capFl_cases (depth := depth) (batch := batch) cd k with ⟨-, a, ha, l', h1, h2, e⟩ |
          ⟨e, -⟩
        · exact ⟨a, ha, l' - 1, by omega, by rw [show l' - 1 + 1 = l' by omega]; exact e⟩
        · exact absurd e hf
    exact climb_hashes hag ha (hq a ha).2.1 hl
  · have zero : ∀ c, k = c / 2 → 2 ≤ c → capFl depth batch cd c = 0 := by
      intro c hc hc2
      rcases capFl_cases (depth := depth) (batch := batch) cd c with ⟨-, a, ha, l', h1, h2, e⟩ |
        ⟨e, -⟩
      · exfalso
        have hp : heapNode depth a.1 (l' + 1) = k := by rw [heapNode_parent h2, ← e, hc]
        rcases Nat.lt_or_ge (l' + 1) depth with hlt | hge
        · rcases capFl_cases (depth := depth) (batch := batch) cd k with ⟨e', -⟩ | ⟨-, hn⟩
          · rw [e'] at hf0; exact one_ne_zero hf0
          · exact hn ⟨a, ha, l' + 1, by omega, hlt, hp.symm⟩
        · have : heapNode depth a.1 (l' + 1) = 1 := by
            rw [show l' + 1 = depth by omega]; exact heapNode_top (hq a ha).1
          omega
      · exact e
    have hD : 2 * k + 1 < 2 ^ cd := by
      have : 2 ^ cd = 2 * 2 ^ (cd - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    refine ⟨?_, ?_⟩
    · have := hfl (2 * k) (by omega) hk2
      rwa [zero (2 * k) (by omega) (by omega)] at this
    · have := hfl (2 * k + 1) (by omega) hD
      rwa [zero (2 * k + 1) (by omega) (by omega)] at this
  · rw [show (2 : ℕ) = 2 * 1 by rfl, capCell_even, show (3 : ℕ) = 2 * 1 + 1 by rfl, capCell_odd,
      hroot]

/-- **The queries' cap writes agree with the honest cap**: an opening's cap leaf holds its climb's
digest, its parent is flagged. -/
theorem cap_writes {cd : ℕ} (hcd : 2 ≤ cd) (hcdd : cd ≤ depth) {a : ℕ × Opening} (ha : a ∈ batch)
    (hag : Guest.Limits.OpeningsAgree depth batch) :
    capCell depth batch (2 * (2 ^ cd + a.1 / 2 ^ (depth - cd))) =
        (digestHalves (climbD (merkleLeafDigest a.2.leaf) a.1 (a.2.path.take (depth - cd)))).1 ∧
      capCell depth batch (2 * (2 ^ cd + a.1 / 2 ^ (depth - cd)) + 1) =
        (digestHalves (climbD (merkleLeafDigest a.2.leaf) a.1 (a.2.path.take (depth - cd)))).2 ∧
      capFl depth batch cd (2 ^ (cd - 1) + a.1 / 2 ^ (depth - cd + 1)) = 1 := by
  have hv : 2 ^ cd + a.1 / 2 ^ (depth - cd) = heapNode depth a.1 (depth - cd) := by
    unfold heapNode Guest.Limits.merkleHeapIndex; rw [show depth - (depth - cd) = cd by omega]
  have hnd := nodeD_eq hag ha (nodeIs_climb (a := a) (l := depth - cd) (by omega))
  refine ⟨by rw [hv, capCell_even, hnd], by rw [hv, capCell_odd, hnd], ?_⟩
  have hw : 2 ^ (cd - 1) + a.1 / 2 ^ (depth - cd + 1) = heapNode depth a.1 (depth - cd + 1) := by
    unfold heapNode Guest.Limits.merkleHeapIndex; rw [show depth - (depth - cd + 1) = cd - 1 by omega]
  rcases capFl_cases (depth := depth) (batch := batch) cd
      (2 ^ (cd - 1) + a.1 / 2 ^ (depth - cd + 1)) with ⟨e, -⟩ | ⟨-, hn⟩
  · exact e
  · exact absurd ⟨a, ha, depth - cd + 1, le_rfl, by omega, hw⟩ hn

/-! ## At an accepted phase -/

/-- The honest cap cells of the phase `phase` at the positions `ps`. -/
noncomputable def capCellH (height : ℕ) (ps : List ℕ) (phase : List Opening) : ℕ → E :=
  capCell height (ps.zip phase)

/-- The honest cap flags of the phase `phase` at the positions `ps`, cap depth `cd`. -/
noncomputable def capFlH (height cd : ℕ) (ps : List ℕ) (phase : List Opening) : ℕ → E :=
  capFl height (ps.zip phase) cd

/-- What an accepted phase gives: one opening per position, each passing `openOne`. -/
theorem batchOpens_of {root : Digest} {height width : ℕ} {ps : List ℕ} {phase : List Opening}
    (hlen : phase.length = ps.length)
    (hok : ∀ k (hk : k < ps.length) (ho : k < phase.length),
      Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width ps[k] phase[k]) = true)
    (hps : ∀ q ∈ ps, q < 2 ^ height) :
    BatchOpens height root (ps.zip phase) := by
  intro a ha
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  have hk' : k < ps.length := by simp at hk; omega
  have hk'' : k < phase.length := by omega
  rw [List.getElem_zip]
  obtain ⟨-, h2, h3⟩ := openOne_facts (hok k hk' hk'')
  exact ⟨hps _ (List.getElem_mem hk'), h2, h3⟩

/-- **`verify_merkle_cap`'s meaning on the honest cap** of an accepted phase. -/
theorem capH_meaning {root : Digest} {height width cd : ℕ} {ps : List ℕ} {phase : List Opening}
    (hlen : phase.length = ps.length)
    (hok : ∀ k (hk : k < ps.length) (ho : k < phase.length),
      Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width ps[k] phase[k]) = true)
    (hps : ∀ q ∈ ps, q < 2 ^ height) (hag : Guest.Limits.OpeningsAgree height (ps.zip phase))
    (hcd : 2 ≤ cd) (hcdd : cd ≤ height) (hne : 0 < ps.length) {rd : Reader} {cp fp : E}
    (hc : ∀ k, 2 ≤ k → k < 2 ^ (cd + 2) → LoadHolds rd cp k (capCellH height ps phase k))
    (hf : ∀ k, 2 ≤ k → k < 2 ^ cd → LoadHolds rd fp k (capFlH height cd ps phase k)) :
    MeaningVerifyMerkleCap cd rd [cp, fp] [(digestHalves root).1, (digestHalves root).2] :=
  cap_meaning hcd hcdd (batchOpens_of hlen hok hps) hag
    (List.ne_nil_of_length_pos (by simp; omega)) hc hf

/-- **A query's cap leaf and flag in the honest cap.** -/
theorem capH_query {root : Digest} {height width cd : ℕ} {ps : List ℕ} {phase : List Opening}
    (hlen : phase.length = ps.length)
    (hok : ∀ k (hk : k < ps.length) (ho : k < phase.length),
      Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width ps[k] phase[k]) = true)
    (hps : ∀ q ∈ ps, q < 2 ^ height) (hag : Guest.Limits.OpeningsAgree height (ps.zip phase))
    (hcd : 2 ≤ cd) (hcdd : cd ≤ height) (k : ℕ) (hk : k < ps.length) :
    capCellH height ps phase (2 * (2 ^ cd + ps[k] / 2 ^ (height - cd))) =
        (digestHalves (climbD (merkleLeafDigest (phase[k]'(by omega)).leaf) ps[k]
          ((phase[k]'(by omega)).path.take (height - cd)))).1 ∧
      capCellH height ps phase (2 * (2 ^ cd + ps[k] / 2 ^ (height - cd)) + 1) =
        (digestHalves (climbD (merkleLeafDigest (phase[k]'(by omega)).leaf) ps[k]
          ((phase[k]'(by omega)).path.take (height - cd)))).2 ∧
      capFlH height cd ps phase (2 ^ (cd - 1) + ps[k] / 2 ^ (height - cd + 1)) = 1 ∧
      ps[k] < 2 ^ height ∧ ((phase[k]'(by omega)).path.take (height - cd)).length = height - cd ∧
      (phase[k]'(by omega)).leaf.length = width := by
  have hk' : k < (ps.zip phase).length := by simp; omega
  have hmem : (ps[k], phase[k]'(by omega)) ∈ ps.zip phase := by
    have := List.getElem_mem hk'
    rwa [List.getElem_zip] at this
  have hlt := hps _ (List.getElem_mem hk)
  obtain ⟨hw, hpl, -⟩ := openOne_facts (hok k hk (by omega))
  obtain ⟨e1, e2, e3⟩ := cap_writes (depth := height) hcd hcdd hmem hag
  exact ⟨e1, e2, e3, hlt, by rw [List.length_take, hpl]; omega, hw⟩

end
end LeanVM.Guest.B1.Whir
