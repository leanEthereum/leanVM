module

public import LeanVM.Guest.Complete.Claims.Digest
public import LeanVM.Guest.Complete.Claims.Ends
public import LeanVM.Guest.Complete.Claims.Cover
public import LeanVM.Guest.Complete.MainWords
public import LeanVM.Guest.Complete.MainOrc
import LeanVM.Guest.B1.Sig.Bytes
import LeanVM.Guest.B1.Sig.XmssLayer
import LeanVM.Guest.B1.Sig.XmssSegCoreC
import LeanVM.Guest.ValRef

/-!
# `main`'s two claim lists, placed

`claimList_atEvery`: `claim_list_digest` on a list's cells at `e`, at every frame and cursor past its
block, popping the list's honest pushes (`listPushes "claims"`, by `cl_valid_pops`), every node
exact (`claim_list_digest` is exact for free). `cellsBytes_xCells`, `cellsBytes_sCells`: a claim's
cells are its `64` bytes, so the digest is `claimListDigest`. `mainClx`, `mainCsp`: the fields
`clx` and `csp` of `MainCalleesOpenAt`, the slots below `2^19` (`slots_lt`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Digest LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## A claim's cells are its bytes -/

theorem claimBytesOf_cells (a b : BitVec 128) (m : BitVec 256) :
    claimBytesOf a b m = cellsBytes [Sig.cellOf128 a, Sig.cellOf128 b, Sig.cellOf128 (m.extractLsb' 0 128),
      Sig.cellOf128 (m.extractLsb' 128 128)] := by
  have h1 : ∀ v : BitVec 128, HashSig.littleEndianBytes 16 v = cellBytes (Sig.cellOf128 v) := fun v => by
    rw [← Sig.bytesLE_cellVal, Sig.cellVal_cellOf128]
  have h3 : HashSig.littleEndianBytes 32 m = cellBytes (Sig.cellOf128 (m.extractLsb' 0 128)) ++
      cellBytes (Sig.cellOf128 (m.extractLsb' 128 128)) := by
    conv_lhs => rw [← Sig.cellPairVal_cellOf128 m]
    exact Sig.bytesLE_cellPairVal _ _
  rw [claimBytesOf, h1 a, h1 b, h3]
  simp [cellsBytes, List.append_assoc]

theorem cellOfBytes_cellsBytes (x : E) (xs : List E) : Prover.cellOfBytes (cellsBytes (x :: xs)) = x := by
  conv_rhs => rw [eq_ofLimbs x]
  rw [Prover.cellOfBytes, leLane_cellsBytes, leLane_cellsBytes]
  simp

theorem cellsOfBytes_cellsBytes (xs : List E) : Prover.cellsOfBytes (cellsBytes xs) = xs := by
  refine List.ext_getElem (by simp [Prover.cellsOfBytes]) fun i h1 h2 => ?_
  simp only [Prover.cellsOfBytes, List.getElem_map, List.getElem_range]
  rw [← cellsBytes_drop]
  obtain ⟨ys, hys⟩ : ∃ ys, xs.drop i = xs[i] :: ys := ⟨xs.drop (i + 1), List.drop_eq_getElem_cons h2⟩
  rw [hys, cellOfBytes_cellsBytes]

theorem cellsBytes_claimCells (a b : BitVec 128) (m : BitVec 256) :
    cellsBytes (Prover.cellsOfBytes (claimBytesOf a b m)) = claimBytesOf a b m := by
  rw [claimBytesOf_cells, cellsOfBytes_cellsBytes]

theorem cellsBytes_xCells (c : LeanXmssClaim) : cellsBytes (xCells c) = claimBytes xmssPublicKeyBytes c :=
  cellsBytes_claimCells c.1.root c.1.parameter c.2

theorem cellsBytes_sCells (c : LeanSphincsClaim) : cellsBytes (sCells c) = claimBytes Sphincs.PublicKey.toBytes c :=
  cellsBytes_claimCells c.1.publicSeed c.1.root c.2

theorem cellsBytes_flatMap {α : Type} (f : α → List E) : ∀ L : List α,
    cellsBytes (L.flatMap f) = L.flatMap fun a => cellsBytes (f a)
  | [] => rfl
  | a :: L => by rw [List.flatMap_cons, cellsBytes_append, cellsBytes_flatMap f L, List.flatMap_cons]

theorem xDigest (L : List LeanXmssClaim) :
    keccak256 (cellsBytes (L.flatMap xCells)) = claimListDigest xmssPublicKeyBytes L := by
  rw [claimListDigest, claimListPreimage, cellsBytes_flatMap]
  simp only [cellsBytes_xCells]

theorem sDigest (L : List LeanSphincsClaim) :
    keccak256 (cellsBytes (L.flatMap sCells)) = claimListDigest Sphincs.PublicKey.toBytes L := by
  rw [claimListDigest, claimListPreimage, cellsBytes_flatMap]
  simp only [cellsBytes_sCells]

/-! ## The pops -/

theorem claimPops_of_reads' {α : Type} {f : α → List E} {L : List α} (hf : ∀ c, (f c).length = 4)
    {rd : Reader} {e : ℕ} (hr : ReadsAt rd (ptrAt e) (L.flatMap f)) :
    (List.range L.length).map (claimPop rd e) = L.map fun a => ("claims", f a) := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  have hj : j < L.length := by simpa using h1
  rw [List.getElem_map, List.getElem_map, List.getElem_range, claimPop]
  congr 1
  have hs := Main.readsAt_flatMap_of L (fun a _ => hf a) hr j hj
  rw [ptrAt_mul_gpow] at hs
  refine List.ext_getElem (by simp [hf]) fun c hc1 hc2 => ?_
  have hc4 : c < 4 := by simpa using hc1
  obtain ⟨-, h⟩ := hs c (by rw [hf]; exact hc4)
  rw [Main.addr_ofK] at h
  simp only [List.getElem_map, List.getElem_range]
  rw [h]
  rfl

set_option maxRecDepth 100000 in
theorem claim_list_digest_exact : ExactFreeG "claim_list_digest" :=
  exactFreeG_of (j := idx% «claim_list_digest») (by decide +kernel)

theorem loadHolds_of_isSome {rd : Reader} {i : ℕ} (h : (rd (addressOfIndex i)).isSome) :
    ∃ t, LoadHolds rd (gen ^ i) 0 t := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp h
  refine ⟨w, ?_⟩
  rw [gen_pow_eq_ofK]
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  simp only [limb_ofK, Fin.isValue, addressOfIndex, pow_zero, mul_one]
  simpa [addressOfIndex] using hw

/-! ## The claim lists, at every position -/

/-- `AtEvery` with the end within `2^40` of a cursor below `2^60` (the iface's `AtEveryB … (2^60) (2^40)`). -/
def AtEveryE (al : String → Bool) (k : ℕ) (f : String) (args rets : List E) (R : ℕ → Prop)
    (Pre : Reader → Prop) (Post : Reader → Tree → Prop) (B lo : ℕ) : Prop :=
  ∀ fp cur, lo ≤ fp → fp + B ≤ cur → ∃ e, (cur < 2 ^ 60 → e ≤ cur + 2 ^ 40) ∧
    CallAtA B2C.fs al B2C.cert k f args rets R (fun _ => False) (fun _ => True) Pre Post B fp cur e

theorem AtEveryE.toAtEvery {al : String → Bool} {k : ℕ} {f : String} {args rets : List E} {R : ℕ → Prop}
    {Pre : Reader → Prop} {Post : Reader → Tree → Prop} {B lo : ℕ} (h : AtEveryE al k f args rets R Pre Post B lo) :
    AtEvery al k f args rets R Pre Post B lo :=
  fun fp cur h1 h2 => let ⟨e, _, he⟩ := h fp cur h1 h2; ⟨e, he⟩

/-- **`claim_list_digest` on a list's cells completes placed at every position**, popping the list's
honest pushes, every node exact. -/
theorem claimList_atEvery {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) {α : Type} {f : α → List E}
    (hf : ∀ c, (f c).length = 4) {L : List α} {e : ℕ} (hn : L.length < 2 ^ 19) {R : ℕ → Prop}
    (hR : ∀ i, e ≤ i → i < e + 4 * L.length → R i) {Pre : Reader → Prop}
    (hP : ∀ rd, Pre rd → ReadsAt rd (ptrAt e) (L.flatMap f))
    (hdefN : ∀ rd, LowDef k rd → Pre rd → ∃ t, LoadHolds rd (gen ^ L.length) 0 t)
    {d : Digest} (hd : keccak256 (cellsBytes (L.flatMap f)) = d) (lo : ℕ) :
    AtEveryE al k "claim_list_digest" [ptrAt e, gen ^ L.length] (Prover.digestCells d) R Pre
      (PopsPost (Prover.listPushes "claims" (L.map f))) (B2C.fs "claim_list_digest") lo := by
  intro fp cur _ hfc
  refine ⟨clEnd B2C.fs al L.length cur, fun _ => (clEnd_le al hn).trans (by omega), ?_⟩
  have hl : (L.flatMap f).length = 4 * L.length := flatMap_length_const fun c _ => hf c
  have hdef : ∀ rd, LowDef k rd → Pre rd → ∀ i, (i = L.length / 136 ∨ i = L.length % 136 / 17 ∨
      i = L.length % 17 ∨ i = L.length) → ∃ t, LoadHolds rd (gen ^ i) 0 t := by
    intro rd hl' hp i hi
    rcases hi with h | h | h | h
    all_goals first
      | (subst h; exact hdefN rd hl' hp)
      | exact loadHolds_of_isSome (hl' i (lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by norm_num) hk)))
  have h := digest_callAtA (fs := B2C.fs) (al := al) (cert := B2C.cert) coreProgram_wf hk hn hl hR hP hdef hfc
  rw [hd, show B1.Digest.digestCells d = Prover.digestCells d from rfl] at h
  refine h.withValid fun rd t _ hp hnm hv _ hH => ⟨SameStreams.of_eq ?_,
    every_exact_of_free claim_list_digest_exact hv hnm rd⟩
  rw [ptrAt_eq_gpow] at hv
  rw [cl_valid_pops (by simp only [claimBig, bigFramesCap]; omega) hv hH, claimPops_of_reads' hf (hP rd hp),
    Prover.listPushes, List.map_map]
  by_cases h0 : L = []
  · subst h0; rfl
  · have hn0 : L.length ≠ 0 := fun h => h0 (List.eq_nil_of_length_eq_zero h)
    have hm0 : L.map f ≠ [] := fun h => h0 (List.map_eq_nil_iff.mp h)
    simp only [hn0, hm0, ↓reduceIte, List.length_map, Prover.listSplit]
    simp only [Prover.claimBig, Prover.claimGroup, Prover.count, LeanVM.Protocol.Verifier.gpow]
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 17 ∣ 17 * 8)]
    rfl

/-! ## `main`'s fields -/

theorem nlx_def {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) {s : NodeStatement} {w : NodeWitness}
    {cover : List E} {rd : Reader} (hl : LowDef k rd) (hp : MainPreA al s w cover rd) :
    ∃ t, LoadHolds rd (gen ^ s.claims.xmss.length) 0 t := by
  set n := s.claims.xmss.length
  by_cases hs : n < 2 ^ 17
  · exact loadHolds_of_isSome (hl n (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num) hk)))
  · refine loadHolds_of_isSome (isSome_of_inW hp.1 ⟨_, List.mem_cons_self, ?_, ?_⟩)
    · rw [mBase_zero]; have := fs_main_lt; omega
    · rw [mBase_zero, xFlat_length, List.length_append]
      have := fs_main_lt
      show n < B2C.fs "main" + 4 * (n + _)
      omega

theorem nls_def {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) {s : NodeStatement} {w : NodeWitness}
    {cover : List E} {rd : Reader} (hl : LowDef k rd) (hp : MainPreA al s w cover rd) :
    ∃ t, LoadHolds rd (gen ^ s.claims.sphincs.length) 0 t := by
  set n := s.claims.sphincs.length
  by_cases hs : n < 2 ^ 17
  · exact loadHolds_of_isSome (hl n (lt_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num) hk)))
  · have hf := fs_main_lt
    have hx := xFlat_length (s.claims.xmss ++ (xPlan s w).duplicates)
    have hy := sFlat_length (s.claims.sphincs ++ (sPlan s w).duplicates)
    rw [List.length_append] at hx hy
    by_cases h0 : n < mBase (mainCounts s w) 1
    · refine loadHolds_of_isSome (isSome_of_inW hp.1 ⟨_, List.mem_cons_self, ?_, ?_⟩)
      · rw [mBase_zero]; omega
      · rw [mBase_zero, hx]
        rw [mBase_one] at h0
        exact h0
    · refine loadHolds_of_isSome (isSome_of_inW hp.1 ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩)
      · omega
      · rw [mBase_one, hy]
        show n < B2C.fs "main" + 4 * (mainCounts s w).sx + 4 * (n + _)
        omega

/-- **`MainCalleesOpenAt.clx`**: the leanXMSS claim list, the slots below `2^19`. -/
theorem mainClx {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) {s : NodeStatement} {w : NodeWitness}
    {cover : List E} (hn : (mainCounts s w).sx + (mainCounts s w).ss < 2 ^ 19) :
    AtEveryE al k "claim_list_digest" [mPtr (mainCounts s w) 0 0, gen ^ (mainCounts s w).nlx]
      (Prover.digestCells (claimListDigest xmssPublicKeyBytes s.claims.xmss)) (mainR al (mainCounts s w))
      (MainPreA al s w cover) (PopsPost (Prover.listPushes "claims" (s.claims.xmss.map xCells)))
      (B2C.fs "claim_list_digest") (mLo al (mainCounts s w)) := by
  rw [show mPtr (mainCounts s w) 0 0 = ptrAt (mBase (mainCounts s w) 0) by simp [mPtr]]
  refine claimList_atEvery hk xCells_length (L := s.claims.xmss)
    (lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt (Nat.le_add_right _ _) hn) :
      (mainCounts s w).nlx < 2 ^ 19)
    (fun i h1 h2 => Or.inl ?_) (fun rd hp => ?_) (fun rd hl hp => nlx_def hk hl hp) (xDigest _) _
  · have := mTop_ge (mainCounts s w)
    rw [mBase_zero] at h1 h2
    exact ⟨h1, by simp only [MainCounts.sx, mainCounts] at this h2 ⊢; omega⟩
  · have := mainWords_x hp
    rw [List.flatMap_append] at this
    have h := readsAt_take' this (s.claims.xmss.flatMap xCells).length
    rwa [List.take_left] at h

/-- **`MainCalleesOpenAt.csp`**: the leanSPHINCS claim list, the slots below `2^19`. -/
theorem mainCsp {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) {s : NodeStatement} {w : NodeWitness}
    {cover : List E} (hn : (mainCounts s w).sx + (mainCounts s w).ss < 2 ^ 19) :
    AtEveryE al k "claim_list_digest" [mPtr (mainCounts s w) 1 0, gen ^ (mainCounts s w).nls]
      (Prover.digestCells (claimListDigest Sphincs.PublicKey.toBytes s.claims.sphincs))
      (mainR al (mainCounts s w)) (MainPreA al s w cover)
      (PopsPost (Prover.listPushes "claims" (s.claims.sphincs.map sCells)))
      (B2C.fs "claim_list_digest") (mLo al (mainCounts s w)) := by
  rw [show mPtr (mainCounts s w) 1 0 = ptrAt (mBase (mainCounts s w) 1) by simp [mPtr]]
  refine claimList_atEvery hk sCells_length (L := s.claims.sphincs)
    (lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt (Nat.le_add_left _ _) hn) :
      (mainCounts s w).nls < 2 ^ 19)
    (fun i h1 h2 => Or.inl ?_) (fun rd hp => ?_) (fun rd hl hp => nls_def hk hl hp) (sDigest _) _
  · have := mTop_ge (mainCounts s w)
    rw [mBase_one] at h1 h2
    exact ⟨by omega, by simp only [MainCounts.sx, MainCounts.ss, mainCounts] at this h2 ⊢; omega⟩
  · have := mainWords_s hp
    rw [List.flatMap_append] at this
    have h := readsAt_take' this (s.claims.sphincs.flatMap sCells).length
    rwa [List.take_left] at h


/-! ## The children's claim lists, left -/

/-- **The children's claim lists**: `MainCalleesOpenAt`'s fields `kidx` and `kids` on every node, for a
coverage table carrying the children's marks, their ends within `2^40` of a cursor below `2^60`. -/
def KidsListsOpen (al : String → Bool) (k : ℕ) : Prop :=
  ∀ (s : NodeStatement) (w : NodeWitness) (cover : List E), NodeRelation guestBytecode guestSeed s w →
    DeployedLimits s w → ChildrenOk guestBytecode guestSeed w →
    cover.length = (mainCounts s w).sx + (mainCounts s w).ss → KidCover s w cover →
    (∀ c (hc : c < w.children.length), AtEveryB al k "child_claim_list_digest"
      [mPtr (mainCounts s w) 0 0, mPtr (mainCounts s w) 2 0, gen ^ kidBase w c, gen ^ (mainCounts s w).sx,
        gen ^ w.children[c].statement.claims.xmss.length]
      (Prover.digestCells (claimListDigest xmssPublicKeyBytes w.children[c].statement.claims.xmss))
      (mainR al (mainCounts s w)) (MainPreA al s w cover)
      (PopsPost (Prover.childSlotPushes ((xPlan s w).childSlots.getD c [])))
      (B2C.fs "child_claim_list_digest") (mLo al (mainCounts s w)) (2 ^ 60) (2 ^ 40)) ∧
    (∀ c (hc : c < w.children.length), AtEveryB al k "child_claim_list_digest"
      [mPtr (mainCounts s w) 1 0, mPtr (mainCounts s w) 2 (mainCounts s w).sx,
        gen ^ kidBase w c * gen ^ w.children[c].statement.claims.xmss.length, gen ^ (mainCounts s w).ss,
        gen ^ w.children[c].statement.claims.sphincs.length]
      (Prover.digestCells (claimListDigest Sphincs.PublicKey.toBytes w.children[c].statement.claims.sphincs))
      (mainR al (mainCounts s w)) (MainPreA al s w cover)
      (PopsPost (Prover.childSlotPushes ((sPlan s w).childSlots.getD c [])))
      (B2C.fs "child_claim_list_digest") (mLo al (mainCounts s w)) (2 ^ 60) (2 ^ 40))

/-- **`clx`, `csp` on every node**: the slots below `2^19` from `NodeRelation` and the memory budget. -/
theorem mainClaimLists {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) {s : NodeStatement} {w : NodeWitness}
    (hr : NodeRelation guestBytecode guestSeed s w) (hl : DeployedLimits s w) (cover : List E) :
    AtEvery al k "claim_list_digest" [mPtr (mainCounts s w) 0 0, gen ^ (mainCounts s w).nlx]
        (Prover.digestCells (claimListDigest xmssPublicKeyBytes s.claims.xmss)) (mainR al (mainCounts s w))
        (MainPreA al s w cover) (PopsPost (Prover.listPushes "claims" (s.claims.xmss.map xCells)))
        (B2C.fs "claim_list_digest") (mLo al (mainCounts s w)) ∧
      AtEvery al k "claim_list_digest" [mPtr (mainCounts s w) 1 0, gen ^ (mainCounts s w).nls]
        (Prover.digestCells (claimListDigest Sphincs.PublicKey.toBytes s.claims.sphincs))
        (mainR al (mainCounts s w)) (MainPreA al s w cover)
        (PopsPost (Prover.listPushes "claims" (s.claims.sphincs.map sCells)))
        (B2C.fs "claim_list_digest") (mLo al (mainCounts s w)) :=
  ⟨(mainClx hk (slots_lt hr hl)).toAtEvery, (mainCsp hk (slots_lt hr hl)).toAtEvery⟩

/-- **`clx`, `csp` on every node, their ends bounded**: within `2^40` of a cursor below `2^60`, as
`MainCalleesOpenAt`'s fields `AtEveryB … (2^60) (2^40)` ask. -/
theorem mainClaimListsE {al : String → Bool} {k : ℕ} (hk : 17 ≤ k) {s : NodeStatement} {w : NodeWitness}
    (hr : NodeRelation guestBytecode guestSeed s w) (hl : DeployedLimits s w) (cover : List E) :
    AtEveryE al k "claim_list_digest" [mPtr (mainCounts s w) 0 0, gen ^ (mainCounts s w).nlx]
        (Prover.digestCells (claimListDigest xmssPublicKeyBytes s.claims.xmss)) (mainR al (mainCounts s w))
        (MainPreA al s w cover) (PopsPost (Prover.listPushes "claims" (s.claims.xmss.map xCells)))
        (B2C.fs "claim_list_digest") (mLo al (mainCounts s w)) ∧
      AtEveryE al k "claim_list_digest" [mPtr (mainCounts s w) 1 0, gen ^ (mainCounts s w).nls]
        (Prover.digestCells (claimListDigest Sphincs.PublicKey.toBytes s.claims.sphincs))
        (mainR al (mainCounts s w)) (MainPreA al s w cover)
        (PopsPost (Prover.listPushes "claims" (s.claims.sphincs.map sCells)))
        (B2C.fs "claim_list_digest") (mLo al (mainCounts s w)) :=
  ⟨mainClx hk (slots_lt hr hl), mainCsp hk (slots_lt hr hl)⟩

end
end LeanVM.Guest.Complete
