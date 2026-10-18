/-
  LeanVM.Guest.B1.Digest.ChildTail

  B1 for `child_claims_tail` (32 specializations; G:2827-2841; TRIAGE #64), and the block of a
  child's claim list it shares with `child_claims_window`.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimSpec

/-!
# A child's claim blocks

Block `j` of a child's claim list reads its claim at a hinted index `g^e` into this node's
table (`entries·g^(4e)`), the index range-checked below `log limit`, and marks its coverage slot
`cover·(origin·g^e)` with `marks·g^j` (`ChildReads`). `child_claims_tail__L{k}` is `k` such blocks
chained under `baseMd base`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **What a child's claim blocks read and mark**: block `j < k` takes its claim at the table
index `off j`, below `log limit`: the coverage slot `cover·(origin·g^(off j))` holds `marks·g^j`
and the table entry `entries·g^(4·off j)` holds the block's four cells. -/
def ChildReads (rd : Reader) (entries cover marks origin limit : E) (off : ℕ → ℕ) (cs : List E)
    (k : ℕ) : Prop :=
  ∀ j < k, (∃ L ≤ 2 ^ 33, limit = gen ^ L ∧ off j < L) ∧
    LoadHolds rd (cover * (origin * gen ^ off j)) 0 (marks * gen ^ j) ∧
    CellsAt rd (entries * gen ^ (4 * off j))
      [cs.getD (4 * j) 0, cs.getD (4 * j + 1) 0, cs.getD (4 * j + 2) 0, cs.getD (4 * j + 3) 0]

theorem childReads_congr {rd : Reader} {entries cover marks origin limit : E} {off off' : ℕ → ℕ}
    {cs : List E} {k : ℕ} (h : ∀ j < k, off j = off' j) :
    ChildReads rd entries cover marks origin limit off cs k ↔
      ChildReads rd entries cover marks origin limit off' cs k := by
  constructor <;> intro hR j hj <;> obtain ⟨h1, h2, h3⟩ := hR j hj
  · rw [h j hj] at h1 h2 h3; exact ⟨h1, h2, h3⟩
  · rw [← h j hj] at h1 h2 h3; exact ⟨h1, h2, h3⟩

/-- **`child_claims_tail__L{k}`**: `k` blocks read and marked as `ChildReads`, chained from the
state under `baseMd base`. -/
def Meaning_child_claims_tail (k : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  ∃ s0 s1 base entries cover marks origin limit o0 o1,
    args = [s0, s1, base, entries, cover, marks, origin, limit] ∧ rets = [o0, o1] ∧
    ∃ (off : ℕ → ℕ) (cs : List E), cs.length = 4 * k ∧
      ChildReads rd entries cover marks origin limit off cs k ∧
      ChainCells (s0, s1) (blocksOf cs) (baseMd base) k (o0, o1)

/-! ## The blocks, at value offset `o` -/

/-- `INV_GEN`. -/
abbrev wInv : E := word 9223372036854775821 0 0

/-- Block `0`, values `o + 2 .. o + 20`: its mark is `marks` itself. -/
def cBlk0 (o : ℕ) : List Atom :=
  [.hint (.witness "child_claim_index" (.stack [.n (o + 2)])), .const (.n (o + 3)) wInv,
   .mul (.n (o + 4)) (.n 7) (.n (o + 3)),
   .rangeCheck (.n (o + 2)) (.n (o + 5)) (.n (o + 6)) (.n (o + 7)) (.n (o + 4)),
   .mul (.n (o + 8)) (.n 6) (.n (o + 2)), .mul (.n (o + 9)) (.n 4) (.n (o + 8)),
   .load (.n 5) (.n (o + 9)) 0, .mul (.n (o + 10)) (.n (o + 2)) (.n (o + 2)),
   .mul (.n (o + 11)) (.n (o + 10)) (.n (o + 10)), .mul (.n (o + 12)) (.n 3) (.n (o + 11)),
   .load (.n (o + 13)) (.n (o + 12)) 0, .load (.n (o + 14)) (.n (o + 12)) 1,
   .load (.n (o + 15)) (.n (o + 12)) 2, .load (.n (o + 16)) (.n (o + 12)) 3,
   .const (.n (o + 17)) (word 64 0 0), .add (.n (o + 18)) (.n 2) (.n (o + 17)),
   .blake2s (.n (o + 13)) (.n (o + 14)) (.n (o + 15)) (.n (o + 16)) (.n o) (.n (o + 1))
     (.n (o + 19)) (.n (o + 20)) (.n (o + 18))]

/-- The read and the mark of block `j ≥ 1`, values `b .. b + 16`, `b = o + 21j`. -/
def cBlkHead (b j : ℕ) : List Atom :=
  [.hint (.witness "child_claim_index" (.stack [.n b])), .const (.n (b + 1)) wInv,
   .mul (.n (b + 2)) (.n 7) (.n (b + 1)), .rangeCheck (.n b) (.n (b + 3)) (.n (b + 4)) (.n (b + 5)) (.n (b + 2)),
   .const (.n (b + 6)) (word (2 ^ j) 0 0), .mul (.n (b + 7)) (.n 5) (.n (b + 6)),
   .mul (.n (b + 8)) (.n 6) (.n b), .mul (.n (b + 9)) (.n 4) (.n (b + 8)),
   .load (.n (b + 7)) (.n (b + 9)) 0, .mul (.n (b + 10)) (.n b) (.n b),
   .mul (.n (b + 11)) (.n (b + 10)) (.n (b + 10)), .mul (.n (b + 12)) (.n 3) (.n (b + 11)),
   .load (.n (b + 13)) (.n (b + 12)) 0, .load (.n (b + 14)) (.n (b + 12)) 1,
   .load (.n (b + 15)) (.n (b + 12)) 2, .load (.n (b + 16)) (.n (b + 12)) 3]

/-- Block `j ≥ 1` under `base + E(64(j + 1))`. -/
def cBlk (o j : ℕ) : List Atom :=
  cBlkHead (o + 21 * j) j ++
  [.const (.n (o + 21 * j + 17)) (word (64 * (j + 1)) 0 0),
   .add (.n (o + 21 * j + 18)) (.n 2) (.n (o + 21 * j + 17)),
   .blake2s (.n (o + 21 * j + 13)) (.n (o + 21 * j + 14)) (.n (o + 21 * j + 15))
     (.n (o + 21 * j + 16)) (.n (o + 21 * j - 2)) (.n (o + 21 * j - 1)) (.n (o + 21 * j + 19))
     (.n (o + 21 * j + 20)) (.n (o + 21 * j + 18))]

/-- `child_claims_tail__L{k}`'s body, `k ≥ 1`. -/
def cctBody (k : ℕ) : List Stmt :=
  (([.copy (.n 8) (.n 0), .copy (.n 9) (.n 1)] : List Atom) ++ cBlk0 8 ++
    (List.range (k - 1)).flatMap (fun i => cBlk 8 (i + 1)) ++
    ([.copy (.n (8 + 21 * k)) (.n (6 + 21 * k)), .copy (.n (9 + 21 * k)) (.n (7 + 21 * k))] :
      List Atom)).map .atom ++
  [.ret [.n (8 + 21 * k), .n (9 + 21 * k)]]

/-- `child_claims_tail__L0`'s body. -/
def cctBody0 : List Stmt :=
  ([.copy (.n 8) (.n 0), .copy (.n 9) (.n 1), .copy (.n 10) (.n 8), .copy (.n 11) (.n 9)] :
    List Atom).map .atom ++ [.ret [.n 10, .n 11]]

/-- The specializations' names, as `child_claim_list_digest` dispatches on them. -/
def cctNames : List String :=
  ["child_claims_tail__L0", "child_claims_tail__L1", "child_claims_tail__L2",
   "child_claims_tail__L3", "child_claims_tail__L4", "child_claims_tail__L5",
   "child_claims_tail__L6", "child_claims_tail__L7", "child_claims_tail__L8",
   "child_claims_tail__L9", "child_claims_tail__L10", "child_claims_tail__L11",
   "child_claims_tail__L12", "child_claims_tail__L13", "child_claims_tail__L14",
   "child_claims_tail__L15", "child_claims_tail__L16", "child_claims_tail__L17",
   "child_claims_tail__L18", "child_claims_tail__L19", "child_claims_tail__L20",
   "child_claims_tail__L21", "child_claims_tail__L22", "child_claims_tail__L23",
   "child_claims_tail__L24", "child_claims_tail__L25", "child_claims_tail__L26",
   "child_claims_tail__L27", "child_claims_tail__L28", "child_claims_tail__L29",
   "child_claims_tail__L30", "child_claims_tail__L31"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem find_child_claims_tail (k : ℕ) (hk : k < 32) :
    coreProgram.find? (cctNames.getD k "") =
      some ⟨cctNames.getD k "", [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7],
        if k = 0 then cctBody0 else cctBody k⟩ := by
  obtain ⟨j, hj⟩ : ∃ j, j = 497 + k := ⟨_, rfl⟩
  interval_cases k
  all_goals exact Program.find?_of_indexOf? (j := j) (by subst hj; decide +kernel) (by subst hj; rfl)

/-! ## The blocks, forward -/

theorem limit_of_rc {rd : Reader} (hm : MemOk rd) {x y t1 t2 limit : E}
    (h : LoadHolds rd x 0 t1 ∧ limit * wInv = x * y ∧ LoadHolds rd y 0 t2) :
    ∃ e, x = gen ^ e ∧ ∃ L ≤ 2 ^ 33, limit = gen ^ L ∧ e < L := by
  obtain ⟨e, e', he, he', hx, -, hk⟩ := rangeCheck_sound hm h
  refine ⟨e, hx, e + e' + 1, by omega, ?_, by omega⟩
  have : limit = limit * (wInv * gen) := by rw [ginv_mul_gen, mul_one]
  rw [this, ← mul_assoc, hk, pow_succ]

theorem word_two_pow {j : ℕ} (hj : j < 64) : word (2 ^ j) 0 0 = gen ^ j := by
  rw [word_eq_eOfNat, gen_pow_eq_eOfNat hj]

/-- The facts of block `0`. -/
theorem cBlk0_fwd {rd : Reader} (hm : MemOk rd) {σ : Val} {o : ℕ}
    (h : ∀ a ∈ cBlk0 o, a.Holds rd σ) :
    ∃ e, (∃ L ≤ 2 ^ 33, σ (.n 7) = gen ^ L ∧ e < L) ∧
      LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5) * gen ^ 0) ∧
      CellsAt rd (σ (.n 3) * gen ^ (4 * e))
        [σ (.n (o + 13)), σ (.n (o + 14)), σ (.n (o + 15)), σ (.n (o + 16))] ∧
      σ (.n (o + 18)) = baseMd (σ (.n 2)) 0 ∧
      CompressCells ![σ (.n (o + 13)), σ (.n (o + 14)), σ (.n (o + 15)), σ (.n (o + 16))]
        (σ (.n o)) (σ (.n (o + 1))) (σ (.n (o + 19))) (σ (.n (o + 20))) (σ (.n (o + 18))) := by
  simp only [cBlk0, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true, true_and] at h
  obtain ⟨c3, m4, rc, m8, m9, l5, m10, m11, m12, l13, l14, l15, l16, c17, a18, hc⟩ := h
  rw [m4, c3] at rc
  obtain ⟨e, hx, hL⟩ := limit_of_rc hm rc
  rw [m9, m8, hx] at l5
  rw [m12, m11, m10, pow4_eq _ e hx] at l13 l14 l15 l16
  refine ⟨e, hL, by rw [pow_zero, mul_one]; exact l5, cellsAt_four.mpr ⟨l13, l14, l15, l16⟩,
    by rw [a18, c17, baseMd, word_md], hc⟩

/-- The facts of block `j ≥ 1`. -/
theorem cBlkHead_fwd {rd : Reader} (hm : MemOk rd) {σ : Val} {b j : ℕ} (hj : j < 64)
    (h : ∀ a ∈ cBlkHead b j, a.Holds rd σ) :
    ∃ e, (∃ L ≤ 2 ^ 33, σ (.n 7) = gen ^ L ∧ e < L) ∧
      LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5) * gen ^ j) ∧
      CellsAt rd (σ (.n 3) * gen ^ (4 * e))
        [σ (.n (b + 13)), σ (.n (b + 14)), σ (.n (b + 15)), σ (.n (b + 16))] := by
  simp only [cBlkHead, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true,
    true_and] at h
  obtain ⟨c1, m2, rc, c6, m7, m8, m9, l7, m10, m11, m12, l13, l14, l15, l16⟩ := h
  rw [m2, c1] at rc
  obtain ⟨e, hx, hL⟩ := limit_of_rc hm rc
  rw [m9, m8, hx, m7, c6, word_two_pow hj] at l7
  rw [m12, m11, m10, pow4_eq _ e hx] at l13 l14 l15 l16
  exact ⟨e, hL, l7, cellsAt_four.mpr ⟨l13, l14, l15, l16⟩⟩

theorem cBlk_fwd {rd : Reader} (hm : MemOk rd) {σ : Val} {o j : ℕ} (hj : j < 64)
    (h : ∀ a ∈ cBlk o j, a.Holds rd σ) :
    ∃ e, (∃ L ≤ 2 ^ 33, σ (.n 7) = gen ^ L ∧ e < L) ∧
      LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5) * gen ^ j) ∧
      CellsAt rd (σ (.n 3) * gen ^ (4 * e))
        [σ (.n (o + 21 * j + 13)), σ (.n (o + 21 * j + 14)), σ (.n (o + 21 * j + 15)),
          σ (.n (o + 21 * j + 16))] ∧
      σ (.n (o + 21 * j + 18)) = baseMd (σ (.n 2)) j ∧
      CompressCells ![σ (.n (o + 21 * j + 13)), σ (.n (o + 21 * j + 14)), σ (.n (o + 21 * j + 15)),
          σ (.n (o + 21 * j + 16))] (σ (.n (o + 21 * j - 2))) (σ (.n (o + 21 * j - 1)))
        (σ (.n (o + 21 * j + 19))) (σ (.n (o + 21 * j + 20))) (σ (.n (o + 21 * j + 18))) := by
  rw [cBlk, List.forall_mem_append] at h
  obtain ⟨e, hL, hs, hc⟩ := cBlkHead_fwd hm hj h.1
  have h2 := h.2
  simp only [List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true] at h2
  obtain ⟨c17, a18, hb⟩ := h2
  exact ⟨e, hL, hs, hc, by rw [a18, c17, baseMd, word_md], hb⟩

/-! ## The blocks, backward -/

/-- The honest values of a block's read and mark, `b .. b + 16`. -/
def cHeadVals (σ : Val) (e L : ℕ) (t1 t2 : E) (j : ℕ) (c0 c1 c2 c3 : E) : List E :=
  [gen ^ e, wInv, σ (.n 7) * wInv, gen ^ (L - 1 - e), t1, t2, word (2 ^ j) 0 0,
   σ (.n 5) * word (2 ^ j) 0 0, σ (.n 6) * gen ^ e, σ (.n 4) * (σ (.n 6) * gen ^ e),
   gen ^ e * gen ^ e, gen ^ e * gen ^ e * (gen ^ e * gen ^ e),
   σ (.n 3) * (gen ^ e * gen ^ e * (gen ^ e * gen ^ e)), c0, c1, c2, c3]

theorem limit_mul_inv {L e : ℕ} (he : e < L) : gen ^ L * wInv = gen ^ e * gen ^ (L - 1 - e) := by
  rw [← pow_add, show L = (e + (L - 1 - e)) + 1 by omega, pow_succ, mul_assoc, mul_comm gen,
    ginv_mul_gen, mul_one]
  congr 1
  omega

theorem cBlkHead_bwd {rd : Reader} {σ : Val} {b j e L : ℕ} {t1 t2 c0 c1 c2 c3 : E} (hj : j < 64)
    (he : e < L) (hlim : σ (.n 7) = gen ^ L) (h1 : LoadHolds rd (gen ^ e) 0 t1)
    (h2 : LoadHolds rd (gen ^ (L - 1 - e)) 0 t2)
    (hs : LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5) * gen ^ j))
    (hc : CellsAt rd (σ (.n 3) * gen ^ (4 * e)) [c0, c1, c2, c3])
    (hv : ∀ r < 17, σ (.n (b + r)) = (cHeadVals σ e L t1 t2 j c0 c1 c2 c3).getD r 0) :
    ∀ a ∈ cBlkHead b j, a.Holds rd σ := by
  have hv0 := hv 0 (by omega)
  rw [Nat.add_zero] at hv0
  rw [cellsAt_four, ← pow4_eq _ e rfl] at hc
  simp only [cBlkHead, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true, hv0,
    hv 1 (by omega), hv 2 (by omega), hv 3 (by omega), hv 4 (by omega), hv 5 (by omega),
    hv 6 (by omega), hv 7 (by omega), hv 8 (by omega), hv 9 (by omega), hv 10 (by omega),
    hv 11 (by omega), hv 12 (by omega), hv 13 (by omega), hv 14 (by omega), hv 15 (by omega),
    hv 16 (by omega), cHeadVals, List.getD_cons_succ, List.getD_cons_zero, true_and]
  rw [hlim, limit_mul_inv he, word_two_pow hj]
  exact ⟨⟨h1, rfl, h2⟩, hs, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩

/-- The honest values of block `0`, `o + 2 .. o + 20`. -/
def cBlk0Vals (σ : Val) (e L : ℕ) (t1 t2 c0 c1 c2 c3 : E) (out : E × E) : List E :=
  [gen ^ e, wInv, σ (.n 7) * wInv, gen ^ (L - 1 - e), t1, t2, σ (.n 6) * gen ^ e,
   σ (.n 4) * (σ (.n 6) * gen ^ e), gen ^ e * gen ^ e, gen ^ e * gen ^ e * (gen ^ e * gen ^ e),
   σ (.n 3) * (gen ^ e * gen ^ e * (gen ^ e * gen ^ e)), c0, c1, c2, c3, word 64 0 0,
   σ (.n 2) + word 64 0 0, out.1, out.2]

theorem cBlk0_bwd {rd : Reader} {σ : Val} {o e L : ℕ} {t1 t2 c0 c1 c2 c3 : E} {out : E × E}
    (he : e < L) (hlim : σ (.n 7) = gen ^ L) (h1 : LoadHolds rd (gen ^ e) 0 t1)
    (h2 : LoadHolds rd (gen ^ (L - 1 - e)) 0 t2)
    (hs : LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5)))
    (hc : CellsAt rd (σ (.n 3) * gen ^ (4 * e)) [c0, c1, c2, c3])
    (hcc : CompressCells ![c0, c1, c2, c3] (σ (.n o)) (σ (.n (o + 1))) out.1 out.2
      (baseMd (σ (.n 2)) 0))
    (hv : ∀ r < 19, σ (.n (o + 2 + r)) = (cBlk0Vals σ e L t1 t2 c0 c1 c2 c3 out).getD r 0) :
    ∀ a ∈ cBlk0 o, a.Holds rd σ := by
  have hv' : ∀ r, 2 ≤ r → r < 21 → σ (.n (o + r)) = (cBlk0Vals σ e L t1 t2 c0 c1 c2 c3 out).getD (r - 2) 0 :=
    fun r h1 h2 => by rw [← hv (r - 2) (by omega)]; congr 2; omega
  rw [cellsAt_four, ← pow4_eq _ e rfl] at hc
  rw [baseMd, ← word_md] at hcc
  simp only [cBlk0, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true,
    hv' 2 (by omega) (by omega), hv' 3 (by omega) (by omega), hv' 4 (by omega) (by omega),
    hv' 5 (by omega) (by omega), hv' 6 (by omega) (by omega), hv' 7 (by omega) (by omega),
    hv' 8 (by omega) (by omega), hv' 9 (by omega) (by omega), hv' 10 (by omega) (by omega),
    hv' 11 (by omega) (by omega), hv' 12 (by omega) (by omega), hv' 13 (by omega) (by omega),
    hv' 14 (by omega) (by omega), hv' 15 (by omega) (by omega), hv' 16 (by omega) (by omega),
    hv' 17 (by omega) (by omega), hv' 18 (by omega) (by omega), hv' 19 (by omega) (by omega),
    hv' 20 (by omega) (by omega), Nat.reduceSub, cBlk0Vals, List.getD_cons_succ,
    List.getD_cons_zero, true_and]
  rw [hlim, limit_mul_inv he]
  exact ⟨⟨h1, rfl, h2⟩, hs, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hcc⟩

theorem cBlk_bwd {rd : Reader} {σ : Val} {o j e L : ℕ} {t1 t2 c0 c1 c2 c3 : E} {out : E × E}
    (hj : j < 64) (he : e < L) (hlim : σ (.n 7) = gen ^ L)
    (h1 : LoadHolds rd (gen ^ e) 0 t1) (h2 : LoadHolds rd (gen ^ (L - 1 - e)) 0 t2)
    (hs : LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5) * gen ^ j))
    (hc : CellsAt rd (σ (.n 3) * gen ^ (4 * e)) [c0, c1, c2, c3])
    (hcc : CompressCells ![c0, c1, c2, c3] (σ (.n (o + 21 * j - 2))) (σ (.n (o + 21 * j - 1)))
      out.1 out.2 (baseMd (σ (.n 2)) j))
    (hv : ∀ r < 17, σ (.n (o + 21 * j + r)) = (cHeadVals σ e L t1 t2 j c0 c1 c2 c3).getD r 0)
    (h17 : σ (.n (o + 21 * j + 17)) = word (64 * (j + 1)) 0 0)
    (h18 : σ (.n (o + 21 * j + 18)) = σ (.n 2) + word (64 * (j + 1)) 0 0)
    (h19 : σ (.n (o + 21 * j + 19)) = out.1) (h20 : σ (.n (o + 21 * j + 20)) = out.2) :
    ∀ a ∈ cBlk o j, a.Holds rd σ := by
  rw [cBlk, List.forall_mem_append]
  refine ⟨cBlkHead_bwd hj he hlim h1 h2 hs hc hv, ?_⟩
  simp only [List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true]
  rw [h17, h18, h19, h20, hv 13 (by omega), hv 14 (by omega), hv 15 (by omega), hv 16 (by omega)]
  rw [baseMd, ← word_md] at hcc
  exact ⟨rfl, rfl, hcc⟩

/-! ## `child_claims_tail__L{k}`, forward -/

theorem child_tail_fwd {rd : Reader} (hm : MemOk rd) (k : ℕ) (hk1 : 1 ≤ k) (hk : k < 32)
    (name : String) (args rets : List E)
    (h : Fn.Sem (coreProgram.Rel rd) rd ⟨name, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7],
      cctBody k⟩ args rets) : Meaning_child_claims_tail k rd args rets := by
  simp only [Fn.Sem, cctBody, holdsList_atoms, holdsList_ret, List.forall_mem_append,
    forall_mem_flatMap_range, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true,
    List.map_cons, List.map_nil] at h
  obtain ⟨σ, hp, ⟨⟨⟨⟨c8, c9⟩, hb0⟩, hblk⟩, c8k, c9k⟩, hr⟩ := h
  -- every block, uniformly
  have hB : ∀ j, ∃ e, j < k → ((∃ L ≤ 2 ^ 33, σ (.n 7) = gen ^ L ∧ e < L) ∧
      LoadHolds rd (σ (.n 4) * (σ (.n 6) * gen ^ e)) 0 (σ (.n 5) * gen ^ j) ∧
      CellsAt rd (σ (.n 3) * gen ^ (4 * e))
        [σ (.n (21 + 21 * j)), σ (.n (21 + 21 * j + 1)), σ (.n (21 + 21 * j + 2)),
          σ (.n (21 + 21 * j + 3))]) ∧
      σ (.n (26 + 21 * j)) = baseMd (σ (.n 2)) j ∧
      CompressCells ![σ (.n (21 + 21 * j)), σ (.n (21 + 21 * j + 1)), σ (.n (21 + 21 * j + 2)),
          σ (.n (21 + 21 * j + 3))]
        (if j = 0 then σ (.n 8) else σ (.n (6 + 21 * j)))
        (if j = 0 then σ (.n 9) else σ (.n (7 + 21 * j)))
        (σ (.n (27 + 21 * j))) (σ (.n (28 + 21 * j))) (σ (.n (26 + 21 * j))) := by
    intro j
    by_cases hj : j < k
    swap
    · exact ⟨0, fun h => absurd h hj⟩
    refine (?_ : ∃ e, _).imp fun e h _ => h
    rcases j with _ | i
    · obtain ⟨e, hL, hs, hc, hmd, hcc⟩ := cBlk0_fwd hm hb0
      exact ⟨e, ⟨hL, hs, hc⟩, hmd, hcc⟩
    · obtain ⟨e, hL, hs, hc, hmd, hcc⟩ := cBlk_fwd (o := 8) (j := i + 1) hm (by omega)
        (hblk i (by omega))
      rw [show 8 + 21 * (i + 1) + 13 = 21 + 21 * (i + 1) by ring,
        show 8 + 21 * (i + 1) + 14 = 21 + 21 * (i + 1) + 1 by ring,
        show 8 + 21 * (i + 1) + 15 = 21 + 21 * (i + 1) + 2 by ring,
        show 8 + 21 * (i + 1) + 16 = 21 + 21 * (i + 1) + 3 by ring] at hc hcc
      rw [show 8 + 21 * (i + 1) + 18 = 26 + 21 * (i + 1) by ring] at hmd hcc
      rw [show 8 + 21 * (i + 1) - 2 = 6 + 21 * (i + 1) by omega,
        show 8 + 21 * (i + 1) - 1 = 7 + 21 * (i + 1) by omega,
        show 8 + 21 * (i + 1) + 19 = 27 + 21 * (i + 1) by ring,
        show 8 + 21 * (i + 1) + 20 = 28 + 21 * (i + 1) by ring] at hcc
      exact ⟨e, ⟨hL, hs, hc⟩, hmd, by simpa using hcc⟩
  choose off hoff using hB
  have hch := chainCells_of_steps (n := k)
    (blocks := fun j => ![σ (.n (21 + 21 * j)), σ (.n (21 + 21 * j + 1)), σ (.n (21 + 21 * j + 2)),
      σ (.n (21 + 21 * j + 3))]) (md := fun j => σ (.n (26 + 21 * j)))
    (st := fun j => (if j = 0 then σ (.n 8) else σ (.n (6 + 21 * j)),
      if j = 0 then σ (.n 9) else σ (.n (7 + 21 * j))))
    (fun j hj => by
      have := (hoff j hj).2.2
      simp only [show j + 1 ≠ 0 by omega, ↓reduceIte]
      rw [show 6 + 21 * (j + 1) = 27 + 21 * j by ring, show 7 + 21 * (j + 1) = 28 + 21 * j by ring]
      exact this)
  simp only [↓reduceIte, show k ≠ 0 by omega] at hch
  set cs := (List.range (4 * k)).map (fun i => σ (.n (21 + 21 * (i / 4) + i % 4))) with hcs
  have hcsg : ∀ j r, j < k → r < 4 → cs.getD (4 * j + r) 0 = σ (.n (21 + 21 * j + r)) := by
    intro j r hj hr
    rw [hcs, List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range]
    congr 2
    omega
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
    σ (.n (8 + 21 * k)), σ (.n (9 + 21 * k)), hp.symm, hr.symm, off, cs,
    by rw [hcs, List.length_map, List.length_range], ?_, ?_⟩
  · intro j hj
    obtain ⟨⟨hL, hs, hc⟩, -⟩ := hoff j hj
    refine ⟨hL, hs, ?_⟩
    have e0 := hcsg j 0 hj (by omega)
    rw [Nat.add_zero, Nat.add_zero] at e0
    rw [e0, hcsg j 1 hj (by omega), hcsg j 2 hj (by omega), hcsg j 3 hj (by omega)]
    exact hc
  · rw [chainCells_congr (b' := fun j => ![σ (.n (21 + 21 * j)), σ (.n (21 + 21 * j + 1)),
        σ (.n (21 + 21 * j + 2)), σ (.n (21 + 21 * j + 3))]) (md' := fun j => σ (.n (26 + 21 * j)))
        (fun j hj => ?_) (fun j hj => (hoff j hj).2.1.symm), ← c8, ← c9, c8k, c9k]
    · exact hch
    · have e0 := hcsg j 0 hj (by omega)
      rw [Nat.add_zero, Nat.add_zero] at e0
      simp only [blocksOf, e0, hcsg j 1 hj (by omega), hcsg j 2 hj (by omega),
        hcsg j 3 hj (by omega)]

/-! ## `child_claims_tail__L{k}`, backward -/

section
variable (k : ℕ) (P : Val) (off : ℕ → ℕ) (L : ℕ) (T1 T2 : ℕ → E) (cs : List E)
  (S : ℕ → E × E)

/-- The honest values of block `j ≥ 1`, `b .. b + 20`. -/
def cBlkVals (j : ℕ) : List E :=
  cHeadVals P (off j) L (T1 j) (T2 j) j (cs.getD (4 * j) 0) (cs.getD (4 * j + 1) 0)
    (cs.getD (4 * j + 2) 0) (cs.getD (4 * j + 3) 0) ++
  [word (64 * (j + 1)) 0 0, P (.n 2) + word (64 * (j + 1)) 0 0, (S (j + 1)).1, (S (j + 1)).2]

/-- The honest values of `child_claims_tail__L{k}`, `k ≥ 1`. -/
def cctVals (i : ℕ) : E :=
  if i < 8 then P (.n i) else
  if (i - 8) / 21 = 0 then
    (if (i - 8) % 21 = 0 then (S 0).1 else if (i - 8) % 21 = 1 then (S 0).2 else
      (cBlk0Vals P (off 0) L (T1 0) (T2 0) (cs.getD 0 0) (cs.getD 1 0) (cs.getD 2 0) (cs.getD 3 0)
        (S 1)).getD ((i - 8) % 21 - 2) 0) else
  if (i - 8) / 21 < k then (cBlkVals P off L T1 T2 cs S ((i - 8) / 21)).getD ((i - 8) % 21) 0 else
  if (i - 8) % 21 = 0 then (S k).1 else (S k).2

theorem cctVals_param (i : ℕ) (hi : i < 8) : cctVals k P off L T1 T2 cs S i = P (.n i) := by
  simp [cctVals, hi]

theorem cctVals_st0 : cctVals k P off L T1 T2 cs S 8 = (S 0).1 ∧ cctVals k P off L T1 T2 cs S 9 = (S 0).2 := by
  constructor <;> simp [cctVals]

theorem cctVals_blk0 (r : ℕ) (hr : r < 19) :
    cctVals k P off L T1 T2 cs S (8 + 2 + r) =
      (cBlk0Vals P (off 0) L (T1 0) (T2 0) (cs.getD 0 0) (cs.getD 1 0) (cs.getD 2 0) (cs.getD 3 0)
        (S 1)).getD r 0 := by
  simp only [cctVals, show ¬(8 + 2 + r < 8) by omega, show (8 + 2 + r - 8) / 21 = 0 by omega,
    show (8 + 2 + r - 8) % 21 = r + 2 by omega, show r + 2 ≠ 0 by omega, show r + 2 ≠ 1 by omega,
    ↓reduceIte, Nat.add_sub_cancel]

theorem cctVals_blk (j r : ℕ) (hj1 : 1 ≤ j) (hj : j < k) (hr : r < 21) :
    cctVals k P off L T1 T2 cs S (8 + 21 * j + r) = (cBlkVals P off L T1 T2 cs S j).getD r 0 := by
  simp only [cctVals, show ¬(8 + 21 * j + r < 8) by omega, show (8 + 21 * j + r - 8) / 21 = j by omega,
    show (8 + 21 * j + r - 8) % 21 = r by omega, show j ≠ 0 by omega, hj, ↓reduceIte]

theorem cctVals_end : cctVals k P off L T1 T2 cs S (8 + 21 * k) = (S k).1 ∧
    cctVals k P off L T1 T2 cs S (9 + 21 * k) = (S k).2 ∧
    (1 ≤ k → cctVals k P off L T1 T2 cs S (6 + 21 * k) = (S k).1 ∧
      cctVals k P off L T1 T2 cs S (7 + 21 * k) = (S k).2) := by
  refine ⟨?_, ?_, fun hk => ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [cctVals]
    · simp only [cctVals, show ¬(8 + 21 * k < 8) by omega, show (8 + 21 * k - 8) / 21 = k by omega,
        show (8 + 21 * k - 8) % 21 = 0 by omega, show k ≠ 0 by omega, lt_irrefl, ↓reduceIte]
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [cctVals]
    · simp only [cctVals, show ¬(9 + 21 * k < 8) by omega, show (9 + 21 * k - 8) / 21 = k by omega,
        show (9 + 21 * k - 8) % 21 = 1 by omega, show k ≠ 0 by omega, lt_irrefl, ↓reduceIte,
        one_ne_zero]
  · rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · constructor <;> simp [cctVals, cBlk0Vals]
    · constructor
      · rw [show 6 + 21 * k = 8 + 21 * (k - 1) + 19 by omega,
          cctVals_blk k P off L T1 T2 cs S (k - 1) 19 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals, show k - 1 + 1 = k by omega]
      · rw [show 7 + 21 * k = 8 + 21 * (k - 1) + 20 by omega,
          cctVals_blk k P off L T1 T2 cs S (k - 1) 20 (by omega) (by omega) (by omega)]
        simp [cBlkVals, cHeadVals, show k - 1 + 1 = k by omega]

theorem cctVals_out (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ k) :
    cctVals k P off L T1 T2 cs S (6 + 21 * j) = (S j).1 ∧
      cctVals k P off L T1 T2 cs S (7 + 21 * j) = (S j).2 := by
  rcases Nat.eq_or_lt_of_le hj1 with rfl | hj2
  · constructor <;> simp [cctVals, cBlk0Vals]
  · constructor
    · rw [show 6 + 21 * j = 8 + 21 * (j - 1) + 19 by omega,
        cctVals_blk k P off L T1 T2 cs S (j - 1) 19 (by omega) (by omega) (by omega)]
      simp [cBlkVals, cHeadVals, show j - 1 + 1 = j by omega]
    · rw [show 7 + 21 * j = 8 + 21 * (j - 1) + 20 by omega,
        cctVals_blk k P off L T1 T2 cs S (j - 1) 20 (by omega) (by omega) (by omega)]
      simp [cBlkVals, cHeadVals, show j - 1 + 1 = j by omega]

end

theorem blocksOf_getD (cs : List E) (j : ℕ) :
    blocksOf cs j = ![cs.getD (4 * j) 0, cs.getD (4 * j + 1) 0, cs.getD (4 * j + 2) 0,
      cs.getD (4 * j + 3) 0] := rfl

theorem child_tail_bwd {rd : Reader} (hm : MemOk rd) (k : ℕ) (hk1 : 1 ≤ k) (hk : k < 32)
    (name : String) {s0 s1 base entries cover marks origin limit : E} (rets : List E)
    (hL : ∃ L ≤ 2 ^ 16, limit = gen ^ L)
    (h : Meaning_child_claims_tail k rd [s0, s1, base, entries, cover, marks, origin, limit] rets) :
    Fn.Sem (coreProgram.Rel rd) rd ⟨name, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7],
      cctBody k⟩ [s0, s1, base, entries, cover, marks, origin, limit] rets := by
  obtain ⟨_, _, _, _, _, _, _, _, o0, o1, hargs, rfl, off, cs, hlen, hR, hch⟩ := h
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  rcases hch with ⟨h0, -⟩ | ⟨-, h, hst, hcan, hout⟩
  · omega
  obtain ⟨L, hL16, hlim⟩ := hL
  have hoff : ∀ j < k, off j < L := fun j hj => by
    obtain ⟨⟨L', hL', hlim', ho⟩, -⟩ := hR j hj
    have := gen_pow_inj (a := L) (b := L') (by omega) (by omega) (hlim.symm.trans hlim')
    omega
  have hw : ∀ j, ∃ t1 t2, j < k → LoadHolds rd (gen ^ off j) 0 t1 ∧
      LoadHolds rd (gen ^ (L - 1 - off j)) 0 t2 := fun j => by
    by_cases hj : j < k
    · obtain ⟨t1, t2, l1, -, l2⟩ := rangeCheck_complete hm (e := off j) (e' := L - 1 - off j)
        (by have := hoff j hj; omega) (by omega)
      exact ⟨t1, t2, fun _ => ⟨l1, l2⟩⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose T1 T2 hT using hw
  set P := listVal [s0, s1, base, entries, cover, marks, origin, limit] with hP
  set S := fun j => digestScalars (chainRun h (blocksOf cs) (baseMd base) j) with hS
  have hsteps := steps_of_chainCells (h := h) hcan
  have hS0 : S 0 = (s0, s1) := by rw [hS]; exact hst.symm
  simp only [Fn.Sem, cctBody, holdsList_atoms, holdsList_ret, List.forall_mem_append,
    forall_mem_flatMap_range, List.forall_mem_cons, Atom.Holds, forall_mem_nil_iff, and_true,
    List.map_cons, List.map_nil]
  obtain ⟨e8, e8k, e6⟩ := cctVals_end k P off L T1 T2 cs S
  obtain ⟨t8, t9⟩ := cctVals_st0 k P off L T1 T2 cs S
  refine ⟨fun v => cctVals k P off L T1 T2 cs S v.idx, rfl, ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, fun i hi => ?_⟩, ?_, ?_⟩, ?_⟩
  · show cctVals k P off L T1 T2 cs S 8 = cctVals k P off L T1 T2 cs S 0
    rw [t8, hS0]; rfl
  · show cctVals k P off L T1 T2 cs S 9 = cctVals k P off L T1 T2 cs S 1
    rw [t9, hS0]; rfl
  · obtain ⟨-, hs, hc⟩ := hR 0 hk1
    rw [pow_zero, mul_one] at hs
    have hcc := hsteps 0 hk1
    rw [blocksOf_getD] at hcc
    refine cBlk0_bwd (o := 8) (out := S 1) (hoff 0 hk1) hlim (hT 0 hk1).1 (hT 0 hk1).2 hs hc ?_
      (fun r hr => cctVals_blk0 k P off L T1 T2 cs S r hr)
    show CompressCells _ (cctVals k P off L T1 T2 cs S 8) (cctVals k P off L T1 T2 cs S 9) _ _ _
    rw [t8, t9]
    exact hcc
  · obtain ⟨-, hs, hc⟩ := hR (i + 1) (by omega)
    have hcc := hsteps (i + 1) (by omega)
    rw [blocksOf_getD] at hcc
    have eb := cctVals_blk k P off L T1 T2 cs S (i + 1)
    refine cBlk_bwd (o := 8) (out := S (i + 1 + 1)) (by omega) (hoff _ (by omega)) hlim
      (hT _ (by omega)).1 (hT _ (by omega)).2 hs hc ?_ (fun r hr => ?_) ?_ ?_ ?_ ?_
    · obtain ⟨o1', o2'⟩ := cctVals_out k P off L T1 T2 cs S (i + 1) (by omega) (by omega)
      show CompressCells _ (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) - 2))
        (cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) - 1)) _ _ _
      rw [show 8 + 21 * (i + 1) - 2 = 6 + 21 * (i + 1) by omega,
        show 8 + 21 * (i + 1) - 1 = 7 + 21 * (i + 1) by omega, o1', o2']
      exact hcc
    · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + r) = _
      rw [eb r (by omega) (by omega) (by omega), cBlkVals,
        List.getD_append _ _ _ _ (by simp [cHeadVals]; omega)]
      rfl
    · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 17) = _
      rw [eb 17 (by omega) (by omega) (by omega)]
      simp [cBlkVals, cHeadVals]
    · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 18) = _
      rw [eb 18 (by omega) (by omega) (by omega)]
      simp [cBlkVals, cHeadVals]
      rfl
    · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 19) = _
      rw [eb 19 (by omega) (by omega) (by omega)]
      simp [cBlkVals, cHeadVals]
    · show cctVals k P off L T1 T2 cs S (8 + 21 * (i + 1) + 20) = _
      rw [eb 20 (by omega) (by omega) (by omega)]
      simp [cBlkVals, cHeadVals]
  · show cctVals k P off L T1 T2 cs S (8 + 21 * k) = cctVals k P off L T1 T2 cs S (6 + 21 * k)
    rw [e8, (e6 hk1).1]
  · show cctVals k P off L T1 T2 cs S (9 + 21 * k) = cctVals k P off L T1 T2 cs S (7 + 21 * k)
    rw [e8k, (e6 hk1).2]
  · show [cctVals k P off L T1 T2 cs S (8 + 21 * k), cctVals k P off L T1 T2 cs S (9 + 21 * k)] = _
    rw [e8, e8k]
    show [(S k).1, (S k).2] = [o0, o1]
    rw [show S k = (o0, o1) from hout.symm]

theorem child_tail_zero_iff (rd : Reader) (name : String) (args rets : List E) :
    Fn.Sem (coreProgram.Rel rd) rd ⟨name, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7],
      cctBody0⟩ args rets ↔ Meaning_child_claims_tail 0 rd args rets := by
  simp only [Fn.Sem, cctBody0, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  constructor
  · rintro ⟨σ, hp, h8, h9, h10, h11, hr⟩
    refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
      σ (.n 10), σ (.n 11), hp.symm, hr.symm, fun _ => 0, [], rfl,
      fun j hj => absurd hj (by omega), Or.inl ⟨rfl, ?_⟩⟩
    rw [h10, h11, h8, h9]
  · rintro ⟨s0, s1, base, entries, cover, marks, origin, limit, o0, o1, rfl, rfl, off, cs, -, -, hch⟩
    rcases hch with ⟨-, hout⟩ | ⟨h, -⟩
    · refine ⟨listVal [s0, s1, base, entries, cover, marks, origin, limit, s0, s1, s0, s1], rfl,
        rfl, rfl, rfl, rfl, ?_⟩
      simp only [Prod.mk.injEq] at hout
      show [s0, s1] = [o0, o1]
      rw [hout.1, hout.2]
    · omega

/-- **`child_claims_tail__L{k}` is sound**, `k < 32`. -/
theorem child_claims_tail_sound {rd : Reader} (hm : MemOk rd) (k : ℕ) (hk : k < 32)
    (args rets : List E) (h : coreProgram.Rel rd (cctNames.getD k "") args rets) :
    Meaning_child_claims_tail k rd args rets := by
  rw [rel_of_find (find_child_claims_tail k hk)] at h
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact (child_tail_zero_iff rd _ args rets).mp h
  · simp only [show k ≠ 0 by omega, ↓reduceIte] at h
    exact child_tail_fwd hm k hk1 hk _ args rets h

/-- **`child_claims_tail__L{k}` is complete**, `k < 32`, for a table of at most `2^16` slots. -/
theorem child_claims_tail_complete {rd : Reader} (hm : MemOk rd) (k : ℕ) (hk : k < 32)
    {s0 s1 base entries cover marks origin limit : E} (rets : List E)
    (hL : ∃ L ≤ 2 ^ 16, limit = gen ^ L)
    (h : Meaning_child_claims_tail k rd [s0, s1, base, entries, cover, marks, origin, limit] rets) :
    coreProgram.Rel rd (cctNames.getD k "") [s0, s1, base, entries, cover, marks, origin, limit]
      rets := by
  rw [rel_of_find (find_child_claims_tail k hk)]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact (child_tail_zero_iff rd _ _ rets).mpr h
  · simp only [show k ≠ 0 by omega, ↓reduceIte]
    exact child_tail_bwd hm k hk1 hk _ rets hL h

end
end LeanVM.Guest.B1.Digest
