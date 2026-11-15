/-
  LeanVM.Guest.B1.Main.MainHonestFit

  `main`'s honest run fits its buffers and its bounds: each honest buffer has its `HeapBuf`'s
  size, the oracle's counts are within `main`'s bounds under the deployed limits, and the running
  counts end at the coverage table's size.
-/

module

public import LeanVM.Guest.B1.Main.MainGoals
public import LeanVM.Guest.B1.Main.Basic
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.Batch.Node

/-!
# `main`'s honest run fits

`hOwn_lengths`: the honest buffers' lengths are `mSizes`, for a statement of the bytecode's
shape (`Nat.log2 bytecode.length = 23`) and children whose fresh claims are at points of `23`
coordinates; `hOwn_fit` the `Forall₂` `main_relAtIn` takes. `hData_bounds`: `MainBounds` under
`Limits`. `hW_total`: the running count after the last child is the coverage table's size.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (claimCells cellsOfBytes daPick)
open LeanVM.Guest.Coverage (coveragePlan planSlots)
open LeanVM.Guest.Value.Keccak (cellsBytes)

@[expose] public section

/-- **The children's fresh claims are at points of `23` coordinates**, as the deferring
verifier's bus point is. -/
def FreshShaped (w : NodeWitness) : Prop := ∀ c ∈ w.children, c.freshClaim.bytecodePoint.length = 23

theorem forall₂_of_map_length : ∀ (l : List (List E)) (ss : List ℕ), l.map List.length = ss →
    List.Forall₂ (fun c s => c.length ≤ s) l ss
  | [], [], _ => .nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, s :: ss, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1.le (forall₂_of_map_length l ss h.2)

theorem length_daCells (c : DaClaim) : (daCells c).length = 3 := by
  simp [daCells, B1.Digest.digestCells]

theorem length_claimCells (r p : BitVec 128) (m : BitVec 256) : (claimCells r p m).length = 4 := by
  simp [claimCells, cellsOfBytes, claimBytesOf, HashSig.littleEndianBytes]

theorem length_flatMap_const {α : Type} (l : List α) (f : α → List E) (k : ℕ)
    (h : ∀ a ∈ l, (f a).length = k) : (l.flatMap f).length = k * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, h a (by simp),
      ih fun b hb => h b (List.mem_cons_of_mem _ hb), List.length_cons]
    ring

variable {bytecode : List K} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

theorem length_hCover : (hCover s w).length = (hData seed s w).T := by
  simp only [hCover, hData, MainData.T, MainData.X, MainData.Y, List.length_append,
    List.length_map, List.length_range]

/-- **The honest buffers have their sizes.** -/
theorem hOwn_lengths (hlog : Nat.log2 bytecode.length = 23) (hr : NodeRelation bytecode seed s w)
    (hf : FreshShaped w) : (hOwn seed s w).map List.length = mSizes (hData seed s w) := by
  have hsd := hr.hasBytecodeShape
  obtain ⟨-, -, hch, -⟩ := hr
  simp only [hOwn, mSizes, List.map_cons, List.map_nil, List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · rw [length_flatMap_const _ (fun c : LeanXmssClaim => claimCells c.1.root c.1.parameter c.2) 4
      fun c _ => length_claimCells _ _ _]
    simp [hData, MainData.X]
  · rw [length_flatMap_const _ (fun c : LeanSphincsClaim => claimCells c.1.publicSeed c.1.root c.2) 4
      fun c _ => length_claimCells _ _ _]
    simp [hData, MainData.Y]
  · exact length_hCover
  · simp
  · rw [length_flatMap_const _ _ 2 fun c _ => by simp [B1.Digest.digestCells]]
    simp [hData]
  · rw [length_flatMap_const _ _ 2 fun c _ => by simp [B1.Digest.digestCells]]
    simp [hData]
  · rw [length_flatMap_const _ _ 24 fun c hc => by simp [DeferredBytecodeClaim.cells, hf c hc]]
    simp [hData]
  · rw [length_flatMap_const _ _ 24 fun c hc => by
      simp [DeferredBytecodeClaim.cells, Eq.trans (hch c hc).1 hlog]]
    simp [hData]
  · simp [hData]
  · simp [DeferredBytecodeClaim.cells, Eq.trans hsd hlog]

theorem hOwn_fit (hlog : Nat.log2 bytecode.length = 23) (hr : NodeRelation bytecode seed s w)
    (hf : FreshShaped w) :
    List.Forall₂ (fun c s => c.length ≤ s) (hOwn seed s w) (mSizes (hData seed s w)) :=
  forall₂_of_map_length _ _ (hOwn_lengths hlog hr hf)

/-! ## The counts -/

theorem length_made {α : Type} (R : List α) (Cs : List (List α)) :
    (made R Cs).length = R.length + (Cs.map List.length).sum := by
  simp [made, List.length_flatten]

/-- The running count before child `c`: the raw claims, then the first `c` children's. -/
theorem hW_eq (c : ℕ) : hW s w c = (hRawX s w).length + (hRawS s w).length +
    (((w.children.take c).map (·.statement.claims.xmss.length)).sum +
      ((w.children.take c).map (·.statement.claims.sphincs.length)).sum) := by
  induction c with
  | zero => simp [hW]
  | succ c ih =>
    rw [hW, ih, List.take_add_one]
    simp only [hEx, hEs, List.map_append, List.sum_append, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    rcases w.children[c]? with _ | ch
    · simp
    · simp; ring

theorem length_raw {α W : Type} (l : List (α × W)) : (l.map (·.1)).length = l.length := by simp

/-- **After the last child, the running count is the coverage table's size.** -/
theorem hW_total (hl : GuestLimits s w) : hW s w w.children.length = planSlots s w := by
  rw [hW_eq, List.take_length, coverage_made hl.toDeployedLimits, length_made, length_made]
  simp only [hRawX, hRawS, length_raw, List.map_map]
  simp only [Function.comp_def]
  omega

theorem raw_le_table {α W : Type} [BEq α] [LawfulBEq α] (D : List α) (R : List (α × W))
    (Cs : List (List α)) (hc : ∀ x, D.count x ≤ (made (R.map (·.1)) Cs).count x) :
    R.length ≤ (D ++ (coveragePlan D (R.map (·.1)) Cs).duplicates).length := by
  rw [plan_table_length _ _ _ hc, length_made, length_raw]; omega

/-! ## The published DA digest -/

theorem digestCells_zero : B1.Digest.digestCells zeroDigest = [0, 0] := by
  simp [B1.Digest.digestCells, digestHalves, zeroDigest]
  exact zero_eq_ofLimbs.symm

theorem daPick_le : daPick s w ≤ w.children.length := by
  unfold daPick
  split
  · exact le_rfl
  · cases h : w.children.findIdx? (fun c ↦ c.statement.claims.daDigest == s.claims.daDigest) with
    | none => exact le_rfl
    | some i => exact (List.findIdx?_eq_some_iff_getElem.mp h).1.le

theorem daPick_da (h : w.daMatrix.isSome = true) : daPick s w = w.children.length := by
  simp [daPick, h]

/-- **The picked slot holds the published digest**: the children's DA digests, then the own. -/
theorem daPick_digest (hr : NodeRelation bytecode seed s w) :
    (w.children.map (·.statement.claims.daDigest) ++ [hOwnDa w]).getD (daPick s w) 0 = s.claims.daDigest := by
  obtain ⟨-, hda, -, -⟩ := hr
  have hown : daPick s w = w.children.length →
      (w.children.map (·.statement.claims.daDigest) ++ [hOwnDa w]).getD (daPick s w) 0 = hOwnDa w := by
    intro e
    rw [e, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
    simp
  unfold daPick at hown ⊢
  cases hw : w.daMatrix with
  | some p =>
    rw [DaDigestHeld, hw] at hda
    simp only [hw, Option.isSome_some, Bool.true_or, ↓reduceIte] at hown ⊢
    rw [hown (by simp), hOwnDa, hw, hda.1]
  | none =>
    rw [DaDigestHeld, hw] at hda
    simp only [hw, Option.isSome_none, Bool.false_or] at hown ⊢
    by_cases hz : (s.claims.daDigest == zeroDigest) = true
    · simp only [hz, ↓reduceIte] at hown ⊢
      rw [hown (by simp), hOwnDa, hw, (beq_iff_eq.mp hz)]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hown ⊢
      cases hf : w.children.findIdx? (fun c ↦ c.statement.claims.daDigest == s.claims.daDigest) with
      | none =>
        exfalso
        rcases hda with h | ⟨c, hc, hcd⟩
        · exact hz (beq_iff_eq.mpr h)
        · have := List.findIdx?_eq_none_iff.mp hf c hc
          simp [hcd] at this
      | some i =>
        obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        rw [Option.getD_some, List.getD_eq_getElem _ _ (by simp; omega),
          List.getElem_append_left (by simp; omega), List.getElem_map]
        exact beq_iff_eq.mp hp

theorem daCells_bytes (c : DaClaim) :
    cellsBytes (daCells c ++ [0]) = digestBytes c.daRoot ++ E.toBytes c.membershipChallenge ++
      List.replicate 16 0 := by
  have e0 : Keccak.cellBytes (0 : E) = List.replicate 16 0 := by decide +kernel
  rw [digestBytes_eq_cells]
  simp only [daCells, B1.Digest.digestCells, cellsBytes, List.cons_append, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, e0, List.append_assoc]
  rfl

/-- A run of digests' cells: digest `k`'s at `2k`. -/
theorem readsAt_digests {rd : Reader} {p : E} {L : List Digest}
    (h : ReadsAt rd p (L.flatMap B1.Digest.digestCells)) {k : ℕ} (hk : k < L.length) :
    ReadsAt rd (p * gen ^ (2 * k)) (B1.Digest.digestCells (L.getD k 0)) := by
  have hL : L = L.take k ++ L[k] :: L.drop (k + 1) := by simp
  rw [hL, List.flatMap_append, List.flatMap_cons, B1.Digest.readsAt_append,
    B1.Digest.readsAt_append] at h
  have hlen : ((L.take k).flatMap B1.Digest.digestCells).length = 2 * k := by
    rw [length_flatMap_const _ _ 2 fun c _ => by simp [B1.Digest.digestCells]]
    simp; omega
  rw [List.getD_eq_getElem _ _ hk, ← hlen]
  exact h.2.1

/-- **`main`'s honest counts are within its bounds**, under the deployed limits. -/
theorem hData_bounds (hl : GuestLimits s w) (fs : String → ℕ) (fp : ℕ) :
    MainBounds (2 ^ 23) ((hData seed s w).toIn fs fp) := by
  have hc := hl.planSlotsBelow2Pow23
  rw [coverage_eq] at hc
  have hx : w.xmssSignatures.length ≤ (s.claims.xmss ++ (xPlan s w).duplicates).length :=
    raw_le_table s.claims.xmss w.xmssSignatures _ (xPlan_held hl.toDeployedLimits)
  have hs : w.sphincsSignatures.length ≤
      (s.claims.sphincs ++ (sPlan s w).duplicates).length :=
    raw_le_table s.claims.sphincs w.sphincsSignatures _ (sPlan_held hl.toDeployedLimits)
  simp only [List.length_append] at hc hx hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hl.atMostSixteenChildren, ?_, ?_, daPick_le, fun h => ?_, fun h => ?_⟩
  · show s.claims.xmss.length < 2 ^ 23; omega
  · show (xPlan s w).duplicates.length < 2 ^ 23; omega
  · show w.xmssSignatures.length < 2 ^ 23; omega
  · show s.claims.sphincs.length < 2 ^ 23; omega
  · show (sPlan s w).duplicates.length < 2 ^ 23; omega
  · show w.sphincsSignatures.length < 2 ^ 23; omega
  · show (w.daMatrix.map fun _ => 1).getD 0 ≤ 1
    cases w.daMatrix <;> simp
  · show s.claims.xmss.length + (xPlan s w).duplicates.length +
      (s.claims.sphincs.length + (sPlan s w).duplicates.length) < 2 ^ 23
    omega
  · have h' : (w.daMatrix.map fun _ => 1).getD 0 = 1 := h
    show daPick s w = w.children.length
    cases hw : w.daMatrix with
    | none => simp [hw] at h'
    | some p => exact daPick_da (by simp [hw])
  · have h' : (w.daMatrix.map fun _ => 1).getD 0 = 1 := h
    show ((w.daMatrix.map fun p => daCells p.1).getD [0, 0, 0]).length = 3
    cases hw : w.daMatrix with
    | none => simp [hw] at h'
    | some p => exact length_daCells _

/-! ## `main`'s words on an honest memory -/

theorem mem_bufL_getD {b : ℕ} {sizes : List ℕ} {own : List (List E)} (hlen : own.length = sizes.length)
    {i : ℕ} (hi : i < sizes.length) :
    ((bases b sizes).getD i 0, own.getD i []) ∈ bufL b sizes own := by
  have h1 : i < (bases b sizes).length := by rw [length_bases]; exact hi
  have h2 : i < own.length := by omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
  have h3 : i < ((bases b sizes).zip own).length := by simp [List.length_zip]; omega
  have := List.getElem_mem h3
  rwa [List.getElem_zip] at this

/-- **`main`'s header-free reads hold on a memory holding its honest buffers.** -/
theorem hMainMem (hlog : Nat.log2 bytecode.length = 23) (hr : NodeRelation bytecode seed s w)
    (hf : FreshShaped w) (hl : GuestLimits s w) (fs : String → ℕ) (fp : ℕ) (rd : Reader)
    (hM : B1.Main.MemL rd (bufL (fp + fs "main") (mSizes (hData seed s w)) (hOwn seed s w)))
    (h0 : LoadHolds rd 1 0 (digestHalves (statementDigest seed s)).1)
    (h1 : LoadHolds rd gen 0 (digestHalves (statementDigest seed s)).2) :
    MainMem rd ((hData seed s w).toIn fs fp) := by
  have hlen : (hOwn seed s w).length = (mSizes (hData seed s w)).length := by
    rw [← hOwn_lengths hlog hr hf, List.length_map]
  have hR : ∀ i < 10, ReadsAt rd (gen ^ ((mPos (hData seed s w) (fp + fs "main")).getD i 0))
      ((hOwn seed s w).getD i []) := fun i hi =>
    by rw [gen_pow_eq_ofK]; exact hM _ (mem_bufL_getD hlen (by simp [mSizes]; omega))
  have hD : ReadsAt rd (gen ^ ((mPos (hData seed s w) (fp + fs "main")).getD 4 0))
      ((w.children.map (·.statement.claims.daDigest) ++ [hOwnDa w]).flatMap B1.Digest.digestCells) :=
    hR 4 (by omega)
  have hdig := daPick_digest hr
  obtain ⟨-, hda, -, hz⟩ := hr
  refine ⟨hR 3 (by omega), ?_, ?_, ?_, ?_, ?_, h0, h1⟩
  · have := hR 8 (by omega) 0 (by simp [hOwn])
    simpa [hOwn, MainData.toIn, hData, hW] using this
  · have := hR 8 (by omega) w.children.length (by simp [hOwn])
    simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero, List.getElem_map,
      List.getElem_range] at this
    rw [hW_total hl, coverage_eq] at this
    show LoadHolds rd (gen ^ ((mPos (hData seed s w) (fp + fs "main")).getD 8 0) * gen ^ w.children.length) 0
      (gen ^ (s.claims.xmss.length + (xPlan s w).duplicates.length + (s.claims.sphincs.length +
        (sPlan s w).duplicates.length)))
    rw [loadHolds_mul_gen_pow, Nat.add_zero]
    simp only [List.length_append] at this
    exact this
  · have := readsAt_digests hD (k := w.children.length) (by simp)
    have e : (w.children.map (·.statement.claims.daDigest) ++ [hOwnDa w]).getD w.children.length 0 =
        hOwnDa w := by
      simp [List.getD_eq_getElem?_getD]
    rw [e] at this
    show ReadsAt rd (gen ^ _ * gen ^ (2 * w.children.length)) (MainIn.ownDa _)
    cases hw : w.daMatrix with
    | some p =>
      have e1 : hOwnDa w = daClaimDigest p.1 := by simp [hOwnDa, hw]
      have e2 : MainIn.ownDa ((hData seed s w).toIn fs fp) =
          B1.Digest.digestCells (keccak256 (cellsBytes (daCells p.1 ++ [0]))) := by
        simp [MainIn.ownDa, hData, MainData.toIn, hw]
      rw [e1, daClaimDigest, ← daCells_bytes] at this
      rw [e2]; exact this
    | none =>
      have e1 : hOwnDa w = zeroDigest := by simp [hOwnDa, hw]
      have e2 : MainIn.ownDa ((hData seed s w).toIn fs fp) = [0, 0] := by
        simp [MainIn.ownDa, hData, MainData.toIn, hw]
      rw [e1, digestCells_zero] at this
      rw [e2]; exact this
  · have := readsAt_digests hD (k := daPick s w) (by simp; have := daPick_le (s := s) (w := w); omega)
    rw [hdig] at this
    exact this
  · intro hnc
    have hc : w.children = [] := List.eq_nil_of_length_eq_zero hnc
    simp only [DeferredClaimBatched, hc, ↓reduceIte] at hz
    have hz' : s.deferredClaim.bytecodePoint = List.replicate (Nat.log2 bytecode.length) 0 := hz
    rw [hlog] at hz'
    have := hR 9 (by omega)
    simp only [hOwn, List.getD_cons_succ, List.getD_cons_zero, DeferredBytecodeClaim.cells, hz'] at this
    exact this
end
end LeanVM.Guest.B1.Main
