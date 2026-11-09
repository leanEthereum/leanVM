/-
  LeanVM.Guest.B1.Main.MainCoverLemmas

  `main`'s honest words, read: the claims held directly, the coverage table's word at every slot
  (its taker's mark), the claim tables' cells at every slot, the byte table; each on every memory
  holding `main`'s honest words `hLmain`, and each among them.
-/

module

public import LeanVM.Guest.B1.Main.MainGoals
public import LeanVM.Guest.B1.Main.Basic
public import LeanVM.Guest.B1.Sig.Bytes
public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Protocol.Verifier.Load
public import LeanVM.Guest.AcceptableChild

/-!
# Reading `main`'s honest words

* `idxOf_slot`: the slots are taken once each, so the taker of slot `(slotsOf p)[k]` is `k`;
* `segOf_sum`, `hMarkX_raw` … `hMarkS_child`: the marks of the raw claims and of child `c`'s
  claim `j` (`hW c + j`, after the child's leanXMSS claims for leanSPHINCS);
* `hCover_x`, `hCover_s`: the coverage table's word at each region's slot `t` (the leanSPHINCS
  region after the leanXMSS one); `hCover_takerX`, `hCover_takerS`: at the slot of taker `k`, `g`
  to `k`'s mark;
* `claimCells_eq`: a claim's four cells are `cellOf128` of its key's root and parameter and its
  message's halves;
* on `hLmain` (`hPos i`: `main`'s buffer `i`'s first word): `coverX_load` … (any taker),
  `coverX_child` … (child `c`'s claim `j`: its slot's word `g` to its mark, the table's entry
  there its claim), `tableX_claim`, `tableS_claim` (any slot), `bytes_hold`, and
  the words' regions.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.Hints (claimCells cellsOfBytes cellOfBytes)
open LeanVM.Guest.Coverage (coveragePlan)
open LeanVM.Guest.Value.Keccak (cellBytes cellsBytes)
open LeanVM.Guest.B1 (bufL)
open LeanVM.Guest.B1.Da (reads_of_memL regionL_of_mem)

@[expose] public section

/-! ## Takers and marks -/

/-- **The taker of slot `(slotsOf p)[k]` is `k`.** -/
theorem idxOf_slot {α : Type} [BEq α] [LawfulBEq α] (D R : List α) (Cs : List (List α)) {k : ℕ}
    (hk : k < (slotsOf (coveragePlan D R Cs)).length) :
    (slotsOf (coveragePlan D R Cs)).idxOf (slotsOf (coveragePlan D R Cs))[k] = k :=
  (plan_nodup D R Cs).idxOf_getElem k hk

/-- Child `c`'s claim `j`, numbered child by child, is `(c, j)`. -/
theorem segOf_sum : ∀ (ls : List ℕ) {c j : ℕ} (hc : c < ls.length), j < ls[c] →
    segOf ls ((ls.take c).sum + j) = (c, j)
  | [], _, _, hc, _ => absurd hc (by simp)
  | l :: ls, 0, j, _, hj => by
    have hj' : j < l := hj
    simp [segOf, hj']
  | l :: ls, c + 1, j, hc, hj => by
    have ih := segOf_sum ls (c := c) (j := j) (by simpa using hc) (by simpa using hj)
    have h1 : ¬ l + (ls.take c).sum + j < l := by omega
    simp only [List.take_succ_cons, List.sum_cons, segOf, h1, ↓reduceIte,
      show l + (ls.take c).sum + j - l = (ls.take c).sum + j by omega, ih]

variable (seed : Digest) (s : NodeStatement) (w : NodeWitness)

theorem hMarkX_raw {k : ℕ} (hk : k < (hRawX s w).length) : hMarkX s w k = k := by
  simp [hMarkX, hk]

theorem hMarkS_raw {k : ℕ} (hk : k < (hRawS s w).length) :
    hMarkS s w k = (hRawX s w).length + k := by
  simp [hMarkS, hk]

/-! ## The coverage table's words -/

/-- The leanXMSS and leanSPHINCS regions' sizes. -/
abbrev rX : ℕ := s.claims.xmss.length + (xPlan s w).duplicates.length
abbrev rY : ℕ := s.claims.sphincs.length + (sPlan s w).duplicates.length

theorem hCover_length : (hCover s w).length = rX s w + rY s w := by
  rw [hCover]
  simp only [List.length_append, List.length_map, List.length_range, rX, rY]

theorem hCover_x {t : ℕ} (ht : t < rX s w) :
    (hCover s w)[t]? = some (gen ^ hMarkX s w ((slotsOf (xPlan s w)).idxOf t)) := by
  rw [hCover, List.getElem?_append_left (by simpa using ht)]
  simp [List.getElem?_map, List.getElem?_range (by simpa using ht)]

theorem hCover_s {t : ℕ} (ht : t < rY s w) :
    (hCover s w)[rX s w + t]? = some (gen ^ hMarkS s w ((slotsOf (sPlan s w)).idxOf t)) := by
  rw [hCover, List.getElem?_append_right (by simp)]
  simp [List.getElem?_map, List.getElem?_range (by simpa using ht)]

theorem slotX_lt {k : ℕ} (hk : k < (slotsOf (xPlan s w)).length) : (slotsOf (xPlan s w))[k] < rX s w := by
  have := plan_lt _ _ _ _ (List.getElem_mem (l := slotsOf (xPlan s w)) hk)
  rw [List.length_append] at this
  exact this

theorem slotS_lt {k : ℕ} (hk : k < (slotsOf (sPlan s w)).length) : (slotsOf (sPlan s w))[k] < rY s w := by
  have := plan_lt _ _ _ _ (List.getElem_mem (l := slotsOf (sPlan s w)) hk)
  rw [List.length_append] at this
  exact this

/-- **The coverage word at leanXMSS taker `k`'s slot** is `g` to its mark. -/
theorem hCover_takerX {k : ℕ} (hk : k < (slotsOf (xPlan s w)).length) :
    (hCover s w)[(slotsOf (xPlan s w))[k]]? = some (gen ^ hMarkX s w k) := by
  rw [hCover_x s w (slotX_lt s w hk)]
  rw [show (slotsOf (xPlan s w)).idxOf (slotsOf (xPlan s w))[k] = k from idxOf_slot _ _ _ hk]

theorem hCover_takerS {k : ℕ} (hk : k < (slotsOf (sPlan s w)).length) :
    (hCover s w)[rX s w + (slotsOf (sPlan s w))[k]]? = some (gen ^ hMarkS s w k) := by
  rw [hCover_s s w (slotS_lt s w hk)]
  rw [show (slotsOf (sPlan s w)).idxOf (slotsOf (sPlan s w))[k] = k from idxOf_slot _ _ _ hk]

/-! ## A claim's cells -/

theorem cellOfBytes_cellBytes {x : E} (hx : IsCanonical128 x) (rest : List UInt8) :
    cellOfBytes (cellBytes x ++ rest) = x := by
  conv_rhs => rw [eq_ofLimbs_of_canonical hx]
  rw [cellOfBytes, cellBytes, List.append_assoc, kOfBytes_kBytes_append,
    List.drop_left' (length_kBytes _), kOfBytes_kBytes_append]

theorem cellsOfBytes_cellsBytes : ∀ (l : List E), (∀ x ∈ l, IsCanonical128 x) →
    cellsOfBytes (cellsBytes l) = l
  | [], _ => by simp [cellsOfBytes, cellsBytes]
  | x :: l, h => by
    have ih := cellsOfBytes_cellsBytes l fun y hy => h y (List.mem_cons_of_mem _ hy)
    have hlen : (cellBytes x).length = 16 := by simp [cellBytes, length_kBytes]
    rw [cellsOfBytes, cellsBytes, List.flatMap_cons, List.length_append, hlen,
      show (16 + (l.flatMap cellBytes).length) / 16 = (l.flatMap cellBytes).length / 16 + 1 by omega,
      List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.mul_zero, List.drop_zero, cellOfBytes_cellBytes (h x List.mem_cons_self)]
    congr 1

theorem msg_split (m : BitVec 256) :
    Sig.cellPairVal (Sig.cellOf128 (m.extractLsb' 0 128)) (Sig.cellOf128 (m.extractLsb' 128 128)) = m := by
  apply BitVec.eq_of_toNat_eq
  have hm : m.toNat < 2 ^ 256 := m.isLt
  rw [Sig.cellPairVal, BitVec.toNat_append, Sig.cellVal_cellOf128, Sig.cellVal_cellOf128,
    BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftLeft_eq, mul_comm,
    two_pow_mul_or (Nat.mod_lt _ (by positivity)), Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt (a := m.toNat / 2 ^ 128) (by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; simpa using hm)]
  exact Nat.div_add_mod _ _

/-- **A claim's four cells.** -/
theorem claimCells_eq (root parameter : BitVec 128) (message : BitVec 256) :
    claimCells root parameter message = [Sig.cellOf128 root, Sig.cellOf128 parameter,
      Sig.cellOf128 (message.extractLsb' 0 128), Sig.cellOf128 (message.extractLsb' 128 128)] := by
  conv_lhs => rw [claimCells, ← Sig.cellVal_cellOf128 root, ← Sig.cellVal_cellOf128 parameter,
    ← msg_split message, claimBytes_cells]
  exact cellsOfBytes_cellsBytes _ (by simp [Sig.isCanonical128_cellOf128])

theorem claimCells_length (root parameter : BitVec 128) (message : BitVec 256) :
    (claimCells root parameter message).length = 4 := by
  rw [claimCells_eq]; rfl

theorem length_flatMap_of {α β : Type} {f : α → List β} {w : ℕ} : ∀ (l : List α),
    (∀ a ∈ l, (f a).length = w) → (l.flatMap f).length = w * l.length
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, h a List.mem_cons_self,
      length_flatMap_of l fun b hb => h b (List.mem_cons_of_mem _ hb), List.length_cons]
    ring

/-! ## On `main`'s honest words -/

variable (fs : String → ℕ) (fp : ℕ)

/-- `main`'s buffer `i`'s first word. -/
abbrev hPos (i : ℕ) : ℕ := (mPos (hData seed s w) (fp + fs "main")).getD i 0

theorem hOwn_length : (hOwn seed s w).length = 10 := rfl

theorem hOwn_mem {i : ℕ} (hi : i < 10) :
    (hPos seed s w fs fp i, (hOwn seed s w).getD i []) ∈ hLmain fs fp seed s w := by
  refine List.mem_append_left _ ?_
  have hb : (bases (fp + fs "main") (mSizes (hData seed s w))).length = 10 := by
    rw [length_bases]; rfl
  rw [bufL, List.mem_iff_getElem]
  refine ⟨i, by rw [List.length_zip, hb, hOwn_length]; omega, ?_⟩
  rw [List.getElem_zip]
  simp only [hPos, mPos]
  rw [List.getD_eq_getElem _ _ (by rw [hb]; exact hi),
    List.getD_eq_getElem _ _ (by rw [hOwn_length]; exact hi)]

variable {seed s w fs fp}

theorem hOwn_reads {rd : Reader} (h : MemL rd (hLmain fs fp seed s w)) {i : ℕ} (hi : i < 10) :
    ReadsAt rd (gen ^ hPos seed s w fs fp i) ((hOwn seed s w).getD i []) :=
  reads_of_memL h (hOwn_mem seed s w fs fp hi)

theorem hOwn_region {i k : ℕ} (hi : i < 10) (hk : k < ((hOwn seed s w).getD i []).length) :
    RegionL (hLmain fs fp seed s w) (hPos seed s w fs fp i + k) :=
  regionL_of_mem (hOwn_mem seed s w fs fp hi) hk

/-- The coverage table's word at `t`. -/
theorem cover_load {rd : Reader} (h : MemL rd (hLmain fs fp seed s w)) {t : ℕ} {v : E}
    (ht : (hCover s w)[t]? = some v) : LoadHolds rd (gen ^ hPos seed s w fs fp 2) t v := by
  obtain ⟨htl, rfl⟩ := List.getElem?_eq_some_iff.mp ht
  exact hOwn_reads h (i := 2) (by omega) t htl

theorem cover_region {t : ℕ} (ht : t < rX s w + rY s w) :
    RegionL (hLmain fs fp seed s w) (hPos seed s w fs fp 2 + t) :=
  hOwn_region (i := 2) (by omega) (by
    show t < (hCover s w).length
    rw [hCover_length]; exact ht)

/-- **The coverage word at leanXMSS taker `k`'s slot**, read. -/
theorem coverX_load {rd : Reader} (h : MemL rd (hLmain fs fp seed s w)) {k : ℕ}
    (hk : k < (slotsOf (xPlan s w)).length) :
    LoadHolds rd (hm fs fp seed s w).a117 ((slotsOf (xPlan s w))[k]) (gen ^ hMarkX s w k) :=
  cover_load h (hCover_takerX s w hk)

/-- **The coverage word at leanSPHINCS taker `k`'s slot**, read. -/
theorem coverS_load {rd : Reader} (h : MemL rd (hLmain fs fp seed s w)) {k : ℕ}
    (hk : k < (slotsOf (sPlan s w)).length) :
    LoadHolds rd (hm fs fp seed s w).a117 (rX s w + (slotsOf (sPlan s w))[k]) (gen ^ hMarkS s w k) :=
  cover_load h (hCover_takerS s w hk)

/-- The leanXMSS table holds the claim at slot `t`. -/
theorem tableX_claim {rd : Reader} (h : MemL rd (hLmain fs fp seed s w)) {t : ℕ} {c : LeanXmssClaim}
    (ht : (s.claims.xmss ++ (xPlan s w).duplicates)[t]? = some c) :
    Sig.ClaimAt rd (gen ^ (hPos seed s w fs fp 0 + 4 * t)) (Sig.cellOf128 c.1.root)
      (Sig.cellOf128 c.1.parameter) (Sig.cellOf128 (c.2.extractLsb' 0 128))
      (Sig.cellOf128 (c.2.extractLsb' 128 128)) := by
  have hc4 : claimCells c.1.root c.1.parameter c.2 = _ := claimCells_eq _ _ _
  obtain ⟨htl, rfl⟩ := List.getElem?_eq_some_iff.mp ht
  have hr := B1.Main.readsAt_flatMap_of (w := 4) _
    (fun (c : LeanXmssClaim) _ => claimCells_length c.1.root c.1.parameter c.2)
    (hOwn_reads h (i := 0) (by omega)) t htl
  rw [← pow_add, hc4] at hr
  exact ⟨hr 0 (by simp), hr 1 (by simp), hr 2 (by simp), hr 3 (by simp)⟩

theorem tableX_region {t k : ℕ} (ht : t < rX s w) (hk : k < 4) :
    RegionL (hLmain fs fp seed s w) (hPos seed s w fs fp 0 + 4 * t + k) := by
  rw [Nat.add_assoc]
  refine hOwn_region (i := 0) (by omega) ?_
  show 4 * t + k < ((s.claims.xmss ++ (xPlan s w).duplicates).flatMap _).length
  rw [length_flatMap_of _ fun (c : LeanXmssClaim) _ => claimCells_length c.1.root c.1.parameter c.2, List.length_append]
  simp only [rX] at ht
  omega

/-- The leanSPHINCS table holds the claim at slot `t`. -/
theorem tableS_claim {rd : Reader} (h : MemL rd (hLmain fs fp seed s w)) {t : ℕ} {c : LeanSphincsClaim}
    (ht : (s.claims.sphincs ++ (sPlan s w).duplicates)[t]? = some c) :
    Sig.ClaimAt rd (gen ^ (hPos seed s w fs fp 1 + 4 * t)) (Sig.cellOf128 c.1.publicSeed)
      (Sig.cellOf128 c.1.root) (Sig.cellOf128 (c.2.extractLsb' 0 128))
      (Sig.cellOf128 (c.2.extractLsb' 128 128)) := by
  have hc4 : claimCells c.1.publicSeed c.1.root c.2 = _ := claimCells_eq _ _ _
  obtain ⟨htl, rfl⟩ := List.getElem?_eq_some_iff.mp ht
  have hr := B1.Main.readsAt_flatMap_of (w := 4) _
    (fun (c : LeanSphincsClaim) _ => claimCells_length c.1.publicSeed c.1.root c.2)
    (hOwn_reads h (i := 1) (by omega)) t htl
  rw [← pow_add, hc4] at hr
  exact ⟨hr 0 (by simp), hr 1 (by simp), hr 2 (by simp), hr 3 (by simp)⟩

theorem tableS_region {t k : ℕ} (ht : t < rY s w) (hk : k < 4) :
    RegionL (hLmain fs fp seed s w) (hPos seed s w fs fp 1 + 4 * t + k) := by
  rw [Nat.add_assoc]
  refine hOwn_region (i := 1) (by omega) ?_
  show 4 * t + k < ((s.claims.sphincs ++ (sPlan s w).duplicates).flatMap _).length
  rw [length_flatMap_of _ fun (c : LeanSphincsClaim) _ => claimCells_length c.1.publicSeed c.1.root c.2, List.length_append]
  simp only [rY] at ht
  omega

/-- The byte table. -/
theorem bytes_hold {rd : Reader} (h : MemL rd (hLmain fs fp seed s w)) :
    Sig.ByteBits rd (gen ^ hPos seed s w fs fp 3) := fun v hv => by
  have := hOwn_reads h (i := 3) (by omega) v (by simpa [hOwn] using hv)
  simpa [hOwn] using this

theorem bytes_region {v : ℕ} (hv : v < 256) :
    RegionL (hLmain fs fp seed s w) (hPos seed s w fs fp 3 + v) :=
  hOwn_region (i := 3) (by omega) (by simpa [hOwn] using hv)

end
end LeanVM.Guest.B1.Main
