/-
  LeanVM.Guest.B1.Merkle.Cap

  B1 for `verify_merkle_cap`: the template of its expansion at every cap depth, and its meaning.
-/

module

public import LeanVM.Guest.B1.Merkle.Meaning
public import LeanVM.Guest.B1.Fs.Templates

/-!
# `verify_merkle_cap` (G:1167-1210, TRIAGE #34)

With `L = 2^D` leaves, the expansion of `verify_merkle_cap__L{D}` is `mcBody L`:

* the cap's cells `2 .. 4L - 1` loaded into the values of the same numbers (node `k`'s cells are
  the values `2k`, `2k + 1`);
* the padding run at `P = 4L`: `0x01` at `P`, zeros at `P + 1 .. P + 4`, `0x80 << 56` at `P + 5`;
* the root's `KECCAK` (`mcIns`, `mcOuts`): the children's four cells, the padding, writing the
  root's two cells (`out_cells` two, the run packed at stride 2);
* node `k = 2 .. L - 1` (`mcNode`, its values from `mcBase L k`): its flag loaded, then on a zero
  flag its children's flags pinned to zero (when its children are internal, `2k < L`), else the
  `0x80` constant and the `KECCAK` of its children;
* the root's cells returned.

`mc_keccak_hash` is what one node's `KECCAK` gives (`keccak_one`), `merkle_cap_iff` the meaning at
every depth, and `verify_merkle_cap_holds` the five deployed depths.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Value.Keccak

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The template -/

/-- The `0x80` padding constant of a 64-byte message's last byte (`0x80 << 56`). -/
abbrev w63 : E := word 9223372036854775808 0 0

/-- The first value of the padding run. -/
def mcP (L : ℕ) : ℕ := 4 * L

/-- Node `k`'s `KECCAK` inputs: its children's cells, the padding run, the constant `c`. -/
def mcIns (L k c : ℕ) : List V :=
  [.n (4 * k), .n (4 * k + 1), .n (4 * k + 2), .n (4 * k + 3), .n (mcP L), .n (mcP L + 1),
    .n (mcP L + 2), .n (mcP L + 3), .n c, .n (mcP L + 1), .n (mcP L + 2), .n (mcP L + 3),
    .n (mcP L + 4)]

/-- Node `k`'s `KECCAK` outputs: its two cells. -/
def mcOuts (k : ℕ) : List V := [.n (2 * k), .n (2 * k + 1)]

/-- Node `k`'s constant's offset from its first value: after the two pins, or right after the
flag. -/
def mcOc (L k : ℕ) : ℕ := if 2 * k < L then 3 else 1

/-- Node `k`'s first value (`2 ≤ k ≤ L`; at `k = L`, the return's). -/
def mcBase (L k : ℕ) : ℕ :=
  if 2 * k < L then 4 * L + 6 + 4 * (k - 2)
  else 4 * L + 6 + 4 * (L / 2 - 2) + 2 * (k - L / 2)

/-- Node `k`'s atoms from the value `b`. -/
def mcNode (L k b : ℕ) : List Stmt :=
  [.atom (.load (.n b) (.n 1) k),
    .ite (.n b)
      (if 2 * k < L then
        [.atom (.const (.n (b + 1)) (word 0 0 0)), .atom (.load (.n (b + 1)) (.n 1) (2 * k)),
          .atom (.const (.n (b + 2)) (word 0 0 0)), .atom (.load (.n (b + 2)) (.n 1) (2 * k + 1))]
      else [])
      [.atom (.const (.n (b + mcOc L k)) w63),
        keccakA (mcIns L k (b + mcOc L k)) (mcOuts k)]]

/-- The expansion of `verify_merkle_cap` at `L` leaves. -/
def mcBody (L : ℕ) : List Stmt :=
  ((List.range (4 * L - 2)).map fun i ↦ [.atom (.load (.n (i + 2)) (.n 0) (i + 2))]).flatten ++
  [.atom (.const (.n (mcP L)) (word 1 0 0)), .atom (.const (.n (mcP L + 1)) (word 0 0 0)),
    .atom (.const (.n (mcP L + 2)) (word 0 0 0)), .atom (.const (.n (mcP L + 3)) (word 0 0 0)),
    .atom (.const (.n (mcP L + 4)) (word 0 0 0)), .atom (.const (.n (mcP L + 5)) w63),
    keccakA (mcIns L 1 (mcP L + 5)) (mcOuts 1)] ++
  ((List.range (L - 2)).map fun j ↦ mcNode L (j + 2) (mcBase L (j + 2))).flatten ++
  [.atom (.copy (.n (mcBase L L)) (.n 2)), .atom (.copy (.n (mcBase L L + 1)) (.n 3)),
    .ret [.n (mcBase L L), .n (mcBase L L + 1)]]

theorem noRet_mcNode (L k b : ℕ) : Stmt.noRetList (mcNode L k b) = true := by
  unfold mcNode; split <;> rfl

/-! ## One node's hash -/

/-- The digest of 64 bytes: `keccak([a0, a1], [b0, b1], out)` (`keccak_one`). -/
theorem pair_digest (a0 a1 b0 b1 : E) (O : Fin 13 → E)
    (hK : KeccakCellsRelation (cells13 [a0, a1, b0, b1, word 1 0 0, 0, 0, 0, w63, 0, 0, 0, 0]) false O
      false .all) :
    (O 0, O 1) = digestHalves (keccak256 (cellsBytes [a0, a1, b0, b1])) := by
  have := (keccak_one (cells := [a0, a1, b0, b1]) (len := 64) (by simp) (by decide)
    (getD_cellsBytes_of_le (by simp))
    (fun c hc ↦ by
      fin_cases c <;> simp_all [padCells, xorByte, padRead, rate, byteCell, cells13])
    (fun c hc ↦ by fin_cases c <;> simp_all [cells13]) hK).2
  rwa [List.take_of_length_le (by simp)] at this

theorem canonical_pad :
    AllCanonical [word 1 0 0, 0, 0, 0, w63, 0, 0, 0, 0] := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  have z : IsCanonical128 (0 : E) := by
    rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact z

/-- The inputs of a node's `KECCAK`, the padding run's values known. -/
theorem mcIns_map {L k c : ℕ} (hP : σ (.n (mcP L)) = word 1 0 0)
    (h1 : σ (.n (mcP L + 1)) = word 0 0 0) (h2 : σ (.n (mcP L + 2)) = word 0 0 0)
    (h3 : σ (.n (mcP L + 3)) = word 0 0 0) (h4 : σ (.n (mcP L + 4)) = word 0 0 0)
    (hc : σ (.n c) = w63) :
    (mcIns L k c).map σ = [σ (.n (4 * k)), σ (.n (4 * k + 1)), σ (.n (4 * k + 2)),
      σ (.n (4 * k + 3)), word 1 0 0, 0, 0, 0, w63, 0, 0, 0, 0] := by
  simp [mcIns, hP, h1, h2, h3, h4, hc, word_zero]

/-- **A node's `KECCAK`** hashes its children's cells into its own. -/
theorem mc_keccak_hash {L k c : ℕ} (hP : σ (.n (mcP L)) = word 1 0 0)
    (h1 : σ (.n (mcP L + 1)) = word 0 0 0) (h2 : σ (.n (mcP L + 2)) = word 0 0 0)
    (h3 : σ (.n (mcP L + 3)) = word 0 0 0) (h4 : σ (.n (mcP L + 4)) = word 0 0 0)
    (hc : σ (.n c) = w63) (hK : (Atom.keccak (mcIns L k c) (mcOuts k) false false).Holds rd σ) :
    HashesPair (σ (.n (4 * k))) (σ (.n (4 * k + 1))) (σ (.n (4 * k + 2))) (σ (.n (4 * k + 3)))
      (σ (.n (2 * k))) (σ (.n (2 * k + 1))) := by
  obtain ⟨-, -, O, hKC, hw⟩ := keccak_holds_full hK
  rw [mcIns_map hP h1 h2 h3 h4 hc] at hKC
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hKC.1 0
    · exact hKC.1 1
    · exact hKC.1 2
    · exact hKC.1 3
  · have e0 : σ (.n (2 * k)) = O 0 := hw 0 (by simp [mcOuts])
    have e1 : σ (.n (2 * k + 1)) = O 1 := hw 1 (by simp [mcOuts])
    rw [e0, e1]
    exact pair_digest _ _ _ _ _ hKC

/-- The converse: children's canonical cells and the parent's cells their digest make a node's
`KECCAK` hold. -/
theorem mc_keccak_of {L k c : ℕ} (hP : σ (.n (mcP L)) = word 1 0 0)
    (h1 : σ (.n (mcP L + 1)) = word 0 0 0) (h2 : σ (.n (mcP L + 2)) = word 0 0 0)
    (h3 : σ (.n (mcP L + 3)) = word 0 0 0) (h4 : σ (.n (mcP L + 4)) = word 0 0 0)
    (hc : σ (.n c) = w63)
    (hH : HashesPair (σ (.n (4 * k))) (σ (.n (4 * k + 1))) (σ (.n (4 * k + 2)))
      (σ (.n (4 * k + 3))) (σ (.n (2 * k))) (σ (.n (2 * k + 1)))) :
    (Atom.keccak (mcIns L k c) (mcOuts k) false false).Holds rd σ := by
  obtain ⟨hcan, hd⟩ := hH
  have hcanI : ∀ x, IsCanonical128 (cells13 [σ (.n (4 * k)), σ (.n (4 * k + 1)),
      σ (.n (4 * k + 2)), σ (.n (4 * k + 3)), word 1 0 0, 0, 0, 0, w63, 0, 0, 0, 0] x) := by
    intro x
    fin_cases x
    · exact hcan _ (by simp [cells13])
    · exact hcan _ (by simp [cells13])
    · exact hcan _ (by simp [cells13])
    · exact hcan _ (by simp [cells13])
    all_goals exact canonical_pad _ (by simp [cells13])
  have hS := pair_digest (σ (.n (4 * k))) (σ (.n (4 * k + 1))) (σ (.n (4 * k + 2)))
    (σ (.n (4 * k + 3))) _ ⟨hcanI, fun _ _ ↦ rfl⟩
  rw [← hd, Prod.mk.injEq] at hS
  refine keccak_holds_two.mpr ⟨rfl, ?_, ?_, ?_⟩
  · rw [mcIns_map hP h1 h2 h3 h4 hc]; exact hcanI
  · rw [mcIns_map hP h1 h2 h3 h4 hc]; exact hS.1.symm
  · rw [mcIns_map hP h1 h2 h3 h4 hc]; exact hS.2.symm

/-! ## One node -/

/-- What node `k`'s atoms ask, from the value `b`. -/
def McNodeOk (rd : Reader) (σ : Val) (L k b : ℕ) : Prop :=
  LoadHolds rd (σ (.n 1)) k (σ (.n b)) ∧ IsInK (σ (.n b)) ∧
    (σ (.n b) = 0 → 2 * k < L → σ (.n (b + 1)) = word 0 0 0 ∧
      LoadHolds rd (σ (.n 1)) (2 * k) (σ (.n (b + 1))) ∧ σ (.n (b + 2)) = word 0 0 0 ∧
      LoadHolds rd (σ (.n 1)) (2 * k + 1) (σ (.n (b + 2)))) ∧
    (σ (.n b) ≠ 0 → σ (.n (b + mcOc L k)) = w63 ∧
      (Atom.keccak (mcIns L k (b + mcOc L k)) (mcOuts k) false false).Holds rd σ)

theorem holds_mcNode (L k b : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (mcNode L k b) True kret ↔ McNodeOk rd σ L k b := by
  unfold mcNode McNodeOk
  by_cases h : 2 * k < L
  · simp only [h, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, keccakA, and_true, true_implies]
    rfl
  · simp only [h, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, keccakA, and_true, false_implies,
      implies_true, true_and]
    exact Iff.rfl

/-! ## The meaning -/

theorem holds_mcBody (L : ℕ) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (mcBody L) False kret ↔
      (∀ i < 4 * L - 2, LoadHolds rd (σ (.n 0)) (i + 2) (σ (.n (i + 2)))) ∧
      σ (.n (mcP L)) = word 1 0 0 ∧ σ (.n (mcP L + 1)) = word 0 0 0 ∧
      σ (.n (mcP L + 2)) = word 0 0 0 ∧ σ (.n (mcP L + 3)) = word 0 0 0 ∧
      σ (.n (mcP L + 4)) = word 0 0 0 ∧ σ (.n (mcP L + 5)) = w63 ∧
      (Atom.keccak (mcIns L 1 (mcP L + 5)) (mcOuts 1) false false).Holds rd σ ∧
      (∀ j < L - 2, McNodeOk rd σ L (j + 2) (mcBase L (j + 2))) ∧
      σ (.n (mcBase L L)) = σ (.n 2) ∧ σ (.n (mcBase L L + 1)) = σ (.n 3) ∧
      kret [σ (.n (mcBase L L)), σ (.n (mcBase L L + 1))] := by
  rw [mcBody, holdsList_append, holdsList_append, holdsList_append,
    holdsList_range_flatten _ _ (fun _ ↦ rfl), holdsList_range_flatten _ _ (fun j ↦ noRet_mcNode L (j + 2) _)]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, keccakA, holds_mcNode, and_true,
    List.map_cons, List.map_nil]

/-- The honest value at offset `o` of node `k`'s values: its flag, the pins' zeros, the
`0x80` constant. -/
def nodeVal (L : ℕ) (fl : ℕ → E) (k o : ℕ) : E :=
  if o = 0 then fl k else if o < mcOc L k then 0 else w63

/-- The honest valuation of `verify_merkle_cap`, by index. -/
def mcVal (L : ℕ) (cap flags : E) (cell fl : ℕ → E) (i : ℕ) : E :=
  if i = 0 then cap else if i = 1 then flags
  else if i < 4 * L then cell i
  else if i = 4 * L then word 1 0 0
  else if i < 4 * L + 5 then 0
  else if i = 4 * L + 5 then w63
  else if i < mcBase L (L / 2) then
    nodeVal L fl (2 + (i - (4 * L + 6)) / 4) ((i - (4 * L + 6)) % 4)
  else if i < mcBase L L then
    nodeVal L fl (L / 2 + (i - mcBase L (L / 2)) / 2) ((i - mcBase L (L / 2)) % 2)
  else cell (i - mcBase L L + 2)

theorem mcVal_node (L : ℕ) (hL : 16 ≤ L) (hL2 : L % 2 = 0) (cap flags : E) (cell fl : ℕ → E)
    {k o : ℕ} (hk : 2 ≤ k) (hkL : k < L) (ho : o < mcOc L k + 1) :
    mcVal L cap flags cell fl (mcBase L k + o) = nodeVal L fl k o := by
  have hb2 : mcBase L (L / 2) = 4 * L + 6 + 4 * (L / 2 - 2) := by
    unfold mcBase; split_ifs <;> omega
  have hbL : mcBase L L = 4 * L + 6 + 4 * (L / 2 - 2) + 2 * (L - L / 2) := by
    unfold mcBase; split_ifs <;> omega
  unfold mcVal
  rw [hb2, hbL]
  unfold mcBase mcOc at *
  by_cases h : 2 * k < L
  · simp only [h, ↓reduceIte] at ho ⊢
    rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
      ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega)]
    congr 1 <;> omega
  · simp only [h, ↓reduceIte] at ho ⊢
    rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
      ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega)]
    congr 1 <;> omega

/-- `MeaningVerifyMerkleCap` at `L = 2^D` leaves. -/
def MeaningCapL (L : ℕ) (rd : Reader) : List E → List E → Prop
  | [cap, flags], rets =>
      ∃ cell fl : ℕ → E, (∀ k, 2 ≤ k → k < 4 * L → LoadHolds rd cap k (cell k)) ∧
        (∀ k, 2 ≤ k → k < L → LoadHolds rd flags k (fl k) ∧ IsInK (fl k)) ∧
        (∀ k, 1 ≤ k → k < L → (k = 1 ∨ fl k ≠ 0) →
          HashesPair (cell (4 * k)) (cell (4 * k + 1)) (cell (4 * k + 2)) (cell (4 * k + 3))
            (cell (2 * k)) (cell (2 * k + 1))) ∧
        (∀ k, 2 ≤ k → 2 * k < L → fl k = 0 →
          LoadHolds rd flags (2 * k) 0 ∧ LoadHolds rd flags (2 * k + 1) 0) ∧
        rets = [cell 2, cell 3]
  | _, _ => False

theorem meaningCapL_iff (D : ℕ) (rd : Reader) (args rets : List E) :
    MeaningVerifyMerkleCap D rd args rets ↔ MeaningCapL (2 ^ D) rd args rets := by
  have h4L : 2 ^ (D + 2) = 4 * 2 ^ D := by rw [pow_add]; ring
  unfold MeaningVerifyMerkleCap MeaningCapL
  split <;> simp only [h4L]

/-- **`verify_merkle_cap` at `L` leaves**, for a compiled function whose body is `mcBody L`. -/
theorem merkle_cap_iffL {name : String} {f : Fn} (L : ℕ) (hL : 16 ≤ L) (hL2 : L % 2 = 0)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = mcBody L) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ MeaningCapL L rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams]
  simp only [holds_mcBody, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨σ, hp, hld, hP, h1, h2, h3, h4, h5, hroot, hnodes, hR0, hR1, hret⟩
    subst hp
    refine ⟨fun k ↦ σ (.n k), fun k ↦ σ (.n (mcBase L k)), ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk2 hk
      have := hld (k - 2) (by omega)
      rwa [Nat.sub_add_cancel hk2] at this
    · intro k hk2 hk
      obtain ⟨hl, hK, -⟩ := hnodes (k - 2) (by omega)
      rw [Nat.sub_add_cancel hk2] at hl hK
      exact ⟨hl, hK⟩
    · intro k hk1 hk hfl
      rcases Nat.lt_or_ge k 2 with hk' | hk'
      · obtain rfl : k = 1 := by omega
        exact mc_keccak_hash hP h1 h2 h3 h4 h5 hroot
      · have hfl : σ (.n (mcBase L k)) ≠ 0 := by
          rcases hfl with h | h
          · omega
          · exact h
        obtain ⟨-, -, -, hnz⟩ := hnodes (k - 2) (by omega)
        rw [Nat.sub_add_cancel hk'] at hnz
        obtain ⟨hc, hK⟩ := hnz hfl
        exact mc_keccak_hash hP h1 h2 h3 h4 hc hK
    · intro k hk2 hk hfl
      obtain ⟨-, -, hz, -⟩ := hnodes (k - 2) (by omega)
      rw [Nat.sub_add_cancel hk2] at hz
      obtain ⟨e1, l1, e2, l2⟩ := hz hfl hk
      rw [e1, word_zero] at l1
      rw [e2, word_zero] at l2
      exact ⟨l1, l2⟩
    · rw [← hret, hR0, hR1]
  · intro hm
    obtain ⟨cap, flags, rfl⟩ : ∃ cap flags, args = [cap, flags] := by
      match args, hm with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    obtain ⟨cell, fl, hcell, hfl, hhash, hpin, hret⟩ := hm
    let σ : Val := fun v ↦ mcVal L cap flags cell fl v.idx
    have ev : ∀ k, σ (.n k) = mcVal L cap flags cell fl k := fun _ ↦ rfl
    have ecell : ∀ k, 2 ≤ k → k < 4 * L → σ (.n k) = cell k := fun k h1 h2 ↦ by
      rw [ev]; unfold mcVal; rw [ite_neg' (by omega), ite_neg' (by omega), ite_pos' h2]
    have e1 : σ (.n 1) = flags := rfl
    have eP : σ (.n (mcP L)) = word 1 0 0 := by
      rw [ev]; unfold mcVal mcP
      rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' rfl]
    have eZ : ∀ i, 1 ≤ i → i < 5 → σ (.n (mcP L + i)) = word 0 0 0 := fun i h1 h2 ↦ by
      rw [ev, word_zero]; unfold mcVal mcP
      rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
        ite_pos' (by omega)]
    have e5 : σ (.n (mcP L + 5)) = w63 := by
      rw [ev]; unfold mcVal mcP
      rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
        ite_neg' (by omega), ite_pos' rfl]
    have enode : ∀ k, 2 ≤ k → k < L → ∀ o < mcOc L k + 1,
        σ (.n (mcBase L k + o)) = nodeVal L fl k o :=
      fun k h1 h2 o ho ↦ mcVal_node L hL hL2 cap flags cell fl h1 h2 ho
    have hbL : mcBase L L = 4 * L + 6 + 4 * (L / 2 - 2) +
        2 * (L - L / 2) := by
      unfold mcBase; split_ifs <;> omega
    have hb2 : mcBase L (L / 2) = 4 * L + 6 + 4 * (L / 2 - 2) := by
      unfold mcBase; split_ifs <;> omega
    have eR : ∀ i < 2, σ (.n (mcBase L L + i)) = cell (i + 2) := fun i hi ↦ by
      rw [ev]; unfold mcVal
      rw [hb2, hbL]
      rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
        ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega)]
      congr 1; omega
    have eR0 : σ (.n (mcBase L L)) = cell 2 := eR 0 (by omega)
    have eR1 : σ (.n (mcBase L L + 1)) = cell 3 := eR 1 (by omega)
    have hhashσ : ∀ k, 1 ≤ k → k < L → (k = 1 ∨ fl k ≠ 0) →
        HashesPair (σ (.n (4 * k))) (σ (.n (4 * k + 1))) (σ (.n (4 * k + 2)))
          (σ (.n (4 * k + 3))) (σ (.n (2 * k))) (σ (.n (2 * k + 1))) := fun k h1 h2 h ↦ by
      rw [ecell _ (by omega) (by omega), ecell _ (by omega) (by omega),
        ecell _ (by omega) (by omega), ecell _ (by omega) (by omega),
        ecell _ (by omega) (by omega), ecell _ (by omega) (by omega)]
      exact hhash k h1 h2 h
    refine ⟨σ, rfl, fun i hi ↦ ?_, eP, eZ 1 (by omega) (by omega), eZ 2 (by omega) (by omega),
      eZ 3 (by omega) (by omega), eZ 4 (by omega) (by omega), e5, ?_, fun j hj ↦ ?_,
      by rw [eR0, ecell 2 (by omega) (by omega)],
      by rw [eR1, ecell 3 (by omega) (by omega)], ?_⟩
    · show LoadHolds rd cap (i + 2) (σ (.n (i + 2)))
      rw [ecell (i + 2) (by omega) (by omega)]
      exact hcell _ (by omega) (by omega)
    · exact mc_keccak_of eP (eZ 1 (by omega) (by omega)) (eZ 2 (by omega) (by omega))
        (eZ 3 (by omega) (by omega)) (eZ 4 (by omega) (by omega)) e5
        (hhashσ 1 le_rfl (by omega) (Or.inl rfl))
    · set k := j + 2 with hk
      have hk2 : 2 ≤ k := by omega
      have hkL : k < L := by omega
      have hb0 : σ (.n (mcBase L k)) = fl k := by
        have := enode k hk2 hkL 0 (by omega)
        rw [Nat.add_zero] at this
        rw [this]; unfold nodeVal; rw [ite_pos' rfl]
      obtain ⟨hlf, hK⟩ := hfl k hk2 hkL
      refine ⟨by rw [e1, hb0]; exact hlf, by rw [hb0]; exact hK, fun h0 h2k ↦ ?_, fun hne ↦ ?_⟩
      · rw [hb0] at h0
        have oc3 : mcOc L k = 3 := by simp [mcOc, h2k]
        have v1 : σ (.n (mcBase L k + 1)) = 0 := by
          rw [enode k hk2 hkL 1 (by omega)]; unfold nodeVal
          rw [ite_neg' (by omega), ite_pos' (by omega)]
        have v2 : σ (.n (mcBase L k + 2)) = 0 := by
          rw [enode k hk2 hkL 2 (by omega)]; unfold nodeVal
          rw [ite_neg' (by omega), ite_pos' (by omega)]
        obtain ⟨p1, p2⟩ := hpin k hk2 h2k h0
        rw [v1, v2, word_zero, e1]
        exact ⟨rfl, p1, rfl, p2⟩
      · rw [hb0] at hne
        have hoc : 0 < mcOc L k := by unfold mcOc; split_ifs <;> omega
        have vc : σ (.n (mcBase L k + mcOc L k)) = w63 := by
          rw [enode k hk2 hkL _ (by omega)]; unfold nodeVal
          rw [ite_neg' (by omega), ite_neg' (by omega)]
        exact ⟨vc, mc_keccak_of eP (eZ 1 (by omega) (by omega)) (eZ 2 (by omega) (by omega))
          (eZ 3 (by omega) (by omega)) (eZ 4 (by omega) (by omega)) vc
          (hhashσ k (by omega) hkL (Or.inr hne))⟩
    · rw [hret, eR0, eR1]

end
end LeanVM.Guest.B1
