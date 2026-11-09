/-
  LeanVM.Guest.B1.Gkr.Loop7C

  `__loop6`, completely: on a memory holding a layer's slot, its step's words, its round records
  and the next slot, an iteration's honest valuation satisfies its body; the iterations chain to
  the loop's relation.
-/

module

public import LeanVM.Guest.B1.Gkr.LayerStep
public import LeanVM.Guest.B1.Gkr.EvalC
public import LeanVM.Guest.B1.Gkr.RecsC
public import LeanVM.Guest.B1.Gkr.SpecInv
public import LeanVM.Guest.B1.Gkr.Loop29Complete
public import LeanVM.Guest.B1.Sumcheck.Gkr

/-!
# `__loop6`, completely (G:1852-1934)

An iteration at `x = g^j` from the slot of `L = 2j + sh` (`GkSlotC`, the slot's words exactly)
runs one step of two levels (`GkStepD`, read back from the walk by `gkrStep_inv`). On a memory
holding the slot, the step's words at the cursor, the round records (`RecsAt`) and the next slot,
the body evaluated forward (`lyEvL`, its `ite`s' branches in order) holds: `ly_iter`. The
regions of the body (`lyR1 .. lyR6`):

* `lyc_head`: the combiner's permutation, the first record stored, `half = g^(j/4)` and
  `parity = g^(j % 4)`;
* `lyc_rounds`: `__loop36`, `gkr_rounds__L{2r}` at `r = j % 4` (a dispatch), `gkr_rounds__L1` at
  an odd depth;
* `lyc_last`: the last record read;
* `lyc_children`: the twelve children read and absorbed;
* `lyc_check`: their check and the two new coordinates;
* `lyc_stores`: the next slot stored (`half`, `parity` through the table `k_mod_next`) and the
  next iteration called.

`ly_complete`: iterations at every `g^j`, `j < m`, give `__loop6` from `1` below `g^m`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The slot, completely -/

/-- **The slot of point length `L`, completely**: the sponge's capacity and rate cells (at most
two scalars waiting), the cursor, the values, the row holding the point, the position, `half` and
`parity`. -/
def GkSlotC (rd : Reader) (layers : E) (L : ℕ) (s : Fs) (cur : E) (st : GkrState)
    (row pos half parity : E) : Prop :=
  s.cap.length = 5 ∧ AllCanonical s.cap ∧ s.pend.length ≤ 2 ∧
    (∀ k < 5, LoadHolds rd layers (17 * L + k) (s.cap.getD k 0)) ∧
    (∀ k < 4, LoadHolds rd layers (17 * L + 13 + k) ((rateOf s.pend).getD k 0)) ∧
    LoadHolds rd layers (17 * L + 5) cur ∧ st.values.length = 3 ∧
    (∀ t < 3, LoadHolds rd layers (17 * L + 6 + t) (st.values.getD t 0)) ∧
    LoadHolds rd layers (17 * L + 9) row ∧ st.point.length = L ∧ TbReadsAt rd row st.point ∧
    LoadHolds rd layers (17 * L + 10) pos ∧ LoadHolds rd layers (17 * L + 11) half ∧
    LoadHolds rd layers (17 * L + 12) parity

theorem tb_zero_canonical : IsCanonical128 (0 : E) := by
  rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl

/-- The rate cells of at most four scalars are canonical. -/
theorem rateOf_canonical {pend : List (E × ℕ)} (h : pend.length ≤ 4) : AllCanonical (rateOf pend) := by
  rw [rateOf_eq_cells _ h]
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨p, -, hp⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (scalarCells_canonical _ _).1
    · exact (scalarCells_canonical _ _).2
  · rw [List.eq_of_mem_replicate hc]; exact tb_zero_canonical

theorem capOf_getD (S : KeccakState) {k : ℕ} (hk : k < 5) :
    (capOf S).getD k 0 = cellsOfState S false ⟨8 + k, by omega⟩ := by
  interval_cases k <;> rfl

theorem tbCapAt_getD {rd : Reader} {rec : E} {off stride : ℕ} {cap : List E}
    (h : TbCapAt rd rec off stride cap) {k : ℕ} (hk : k < 5) :
    LoadHolds rd rec (off + k * stride) (cap.getD k 0) := by
  have := h.2 k (by rw [h.1]; exact hk)
  rwa [List.getD_eq_getElem _ _ (by rw [h.1]; exact hk)]

/-! ## The evaluation list -/

/-- `__loop6`'s evaluation list: its body, each `ite`'s branches in order. -/
def lyEvL : List Stmt := flatIte lyPre

theorem ly_chk : (chk 7 lyEvL).isSome = true := by decide +kernel

/-- `__loop6`'s stores. -/
def lyS : List Atom := storesOf 7 lyEvL

/-- **The regions of the body.** The head: the combiner, the first record, `half`, `parity`. -/
def lyR1 : List Stmt :=
  [.atom (.mul (.n 7) (.n 0) (.n 0)), .atom (.mul (.n 8) (.n 2) (.n 3)),
    .atom (.load (.n 9) (.n 8) 0), .atom (.mul (.n 10) (.n 7) (.n 9)),
    .atom (.mul (.n 11) (.n 10) (.n 10)), .atom (.mul (.n 12) (.n 11) (.n 11)),
    .atom (.mul (.n 13) (.n 12) (.n 12)), .atom (.mul (.n 14) (.n 13) (.n 13)),
    .atom (.mul (.n 15) (.n 14) (.n 10)), .atom (.mul (.n 16) (.n 4) (.n 15))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (17 + k)) (.n 16) k)) ++
  (List.range 4).map (fun k ↦ .atom (.load (.n (22 + k)) (.n 16) (13 + k))) ++
  [.atom (.const (.n 26) (word 1 0 0)), .atom (.const (.n 27) (word 0 0 0)),
    .atom (.const (.n 28) (word 0 0 0)), .atom (.const (.n 29) (word 0 0 0)),
    .atom (.const (.n 30) (word 0 0 0)),
    keccakA ([.n 22, .n 23, .n 24, .n 25, .n 27, .n 28, .n 29, .n 30] ++
      (List.range 5).map fun k ↦ .n (17 + k)) (lyOuts 31)] ++
  challengeT (.n 31) (.n 32) 44 ++
  [.atom (.load (.n 51) (.n 16) 9), .atom (.load (.n 52) (.n 16) 10),
    .atom (.mul (.n 53) (.n 5) (.n 52))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (39 + k)) (.n 53) (862 * k))) ++
  [.atom (.load (.n 54) (.n 16) 5), .atom (.load (.n 54) (.n 53) 4310),
    .atom (.load (.n 55) (.n 16) 6), .atom (.load (.n 56) (.n 16) 7),
    .atom (.load (.n 57) (.n 16) 8), .atom (.mul (.n 58) (.n 50) (.n 57)),
    .atom (.add (.n 59) (.n 56) (.n 58)), .atom (.mul (.n 60) (.n 50) (.n 59)),
    .atom (.add (.n 61) (.n 55) (.n 60)), .atom (.load (.n 61) (.n 53) 5172),
    .atom (.load (.n 62) (.n 16) 11), .atom (.load (.n 63) (.n 16) 12),
    .atom (.const (.n 64) (word 1 0 0)), .atom (.add (.n 65) (.n 64) (.n 62)),
    .atom (.const (.n 66) (word 1 0 0))]

/-- The rounds. -/
def lyR2 : List Stmt :=
  [.callIf (.n 65) "__loop36" [.n 66, .n 62, .n 53, .n 51],
    .atom (.mul (.n 67) (.n 62) (.n 62)), .atom (.mul (.n 68) (.n 67) (.n 67)),
    .atom (.mul (.n 69) (.n 68) (.n 68)), .atom (.mul (.n 70) (.n 53) (.n 69)),
    .atom (.mul (.n 71) (.n 51) (.n 69)),
    .dispatch (.n 63) ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"]
      [.n 70, .n 71] [.n 72],
    .atom (.add (.n 73) (.n 10) (.n 7)),
    .ite (.n 73) [] [.atom (.mul (.n 74) (.n 53) (.n 7)), .atom (.mul (.n 75) (.n 51) (.n 7)),
      .call "gkr_rounds__L1" [.n 74, .n 75] [.n 76]]]

/-- The last record. -/
def lyR3 : List Stmt :=
  [.atom (.mul (.n 77) (.n 53) (.n 10))] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (78 + k)) (.n 77) (862 * k))) ++
  [.atom (.load (.n 83) (.n 77) 4310), .atom (.load (.n 84) (.n 77) 5172)]

/-- The children. -/
def lyR4 : List Stmt :=
  ((List.range 4).map lyEvT).flatten ++
  [keccakA (lyRate 0 ++ (List.range 5).map fun k ↦ .n (78 + k)) (lyOuts 129)] ++
  ((List.range 4).map fun i ↦ lyEvT (4 + i)).flatten ++
  [keccakA (lyRate 1 ++ lyCap 129) (lyOuts 186)] ++
  ((List.range 4).map fun i ↦ lyEvT (8 + i)).flatten

/-- The check and the new coordinates. -/
def lyR5 : List Stmt :=
  [.atom (.mul (.n 243) (.n 209) (.n 220)), .atom (.mul (.n 244) (.n 243) (.n 231)),
    .atom (.mul (.n 245) (.n 244) (.n 242)), .atom (.const (.n 246) (word 0 0 0)),
    .atom (.mul (.n 247) (.n 50) (.n 246)), .atom (.add (.n 248) (.n 245) (.n 247)),
    .atom (.mul (.n 249) (.n 152) (.n 163)), .atom (.mul (.n 250) (.n 249) (.n 174)),
    .atom (.mul (.n 251) (.n 250) (.n 185)), .atom (.mul (.n 252) (.n 50) (.n 248)),
    .atom (.add (.n 253) (.n 251) (.n 252)), .atom (.mul (.n 254) (.n 95) (.n 106)),
    .atom (.mul (.n 255) (.n 254) (.n 117)), .atom (.mul (.n 256) (.n 255) (.n 128)),
    .atom (.mul (.n 257) (.n 50) (.n 253)), .atom (.add (.n 258) (.n 256) (.n 257)),
    .atom (.assertEq (.n 84) (.n 258)),
    keccakA (lyRate 2 ++ lyCap 186) (lyOuts 259)] ++
  challengeT (.n 259) (.n 260) 272 ++
  [keccakA ([.n 27, .n 27, .n 27, .n 27, .n 27, .n 28, .n 29, .n 30] ++ lyCap 259) (lyOuts 279)] ++
  challengeT (.n 279) (.n 280) 292

/-- The next slot and the next iteration. -/
def lyR6 : List Stmt :=
  [.atom (.load (.n 278) (.n 51) 40), .atom (.load (.n 298) (.n 51) 41)] ++
  (List.range 5).map (fun k ↦ .atom (.load (.n (287 + k)) (.n 16) (34 + k))) ++
  ((List.range 4).map fun k ↦ [.atom (.const (.n (299 + k)) (word 0 0 0)),
    .atom (.load (.n (299 + k)) (.n 16) (47 + k))]).flatten ++
  [.atom (.const (.n 303) (word 4096 0 0)), .atom (.mul (.n 304) (.n 83) (.n 303)),
    .atom (.load (.n 304) (.n 16) 39)] ++
  lyVal 0 305 40 ++ lyVal 1 314 41 ++ lyVal 2 323 42 ++
  [.atom (.const (.n 332) (word 1099511627776 0 0)), .atom (.mul (.n 333) (.n 51) (.n 332)),
    .atom (.load (.n 333) (.n 16) 43), .atom (.mul (.n 334) (.n 52) (.n 10)),
    .atom (.const (.n 335) (word 2 0 0)), .atom (.mul (.n 336) (.n 334) (.n 335)),
    .atom (.load (.n 336) (.n 16) 44), .atom (.mul (.n 337) (.n 6) (.n 63)),
    .atom (.load (.n 338) (.n 337) 4), .atom (.mul (.n 339) (.n 62) (.n 338)),
    .atom (.load (.n 339) (.n 16) 45), .atom (.mul (.n 340) (.n 6) (.n 63)),
    .atom (.load (.n 341) (.n 340) 0), .atom (.load (.n 341) (.n 16) 46),
    .atom (.const (.n 342) (word 2 0 0)), .atom (.mul (.n 343) (.n 0) (.n 342)),
    .atom (.add (.n 344) (.n 343) (.n 1)), .atom (.const (.n 345) (word 2 0 0)),
    .atom (.mul (.n 346) (.n 0) (.n 345)),
    .callIf (.n 344) "__loop6" [.n 346, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]]

theorem lyPre_eq : lyPre = lyR1 ++ lyR2 ++ lyR3 ++ lyR4 ++ lyR5 ++ lyR6 :=
  tbStmtsEqb_sound (by decide +kernel)

section Eval

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- An atom of the body satisfies its equations. -/
theorem ly_good (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) (n : ℕ) (a : Atom)
    (heq : tbStmtsEqb [.atom a] ((lyPre.drop n).take 1) = true) :
    Good rd lyS (fun _ => 0) σ a :=
  good_slice hG n [.atom a] heq rfl _ List.mem_cons_self

/-- A permutation's thirteen outputs from `b`, and its capacity cells, on its equations. -/
theorem lyc_keccak {S : List Atom} {w : ℕ → E} {ins : List V} {b : ℕ}
    (hg : Good rd S w σ (.keccak ins (lyOuts b) false false))
    (hc : AllCanonical (ins.map σ)) :
    (Atom.keccak ins (lyOuts b) false false).Holds rd σ ∧
      (∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩) ∧
      (lyCap b).map σ = capOf (permOf (ins.map σ)) := by
  obtain ⟨hk, hout⟩ := keccak_good hg hc
  have hP : ∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩ := by
    intro k hk
    have := outs_eq hout ⟨k, hk⟩ (by simpa [lyOuts] using hk)
    simpa [lyOuts] using this
  refine ⟨hk, hP, ?_⟩
  simp only [lyCap, capOf, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rw [hP (8 + 0) (by omega), hP (8 + 1) (by omega), hP (8 + 2) (by omega), hP (8 + 3) (by omega),
    hP (8 + 4) (by omega)]
  rfl

/-- **The head**: the combiner's permutation over the slot's sponge, the first record stored
(its capacity, cursor and combined claim), `half` and `parity`. -/
theorem lyc_head (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {j sh : ℕ}
    (hx : σ (.n 0) = gen ^ j) (hsh : LoadHolds rd (σ (.n 2) * σ (.n 3)) 0 (gen ^ sh)) {s : Fs}
    {cur : E} {st : GkrState} {row pos half parity : E}
    (hS : GkSlotC rd (σ (.n 4)) (2 * j + sh) s cur st row pos half parity)
    (hc0 : TbCapAt rd (σ (.n 5) * pos) 0 gkCap s.squeeze.2.cap)
    (hu0 : LoadHolds rd (σ (.n 5) * pos) (5 * gkCap) cur)
    (hl0 : LoadHolds rd (σ (.n 5) * pos) (6 * gkCap) (polyEval st.values s.squeeze.1)) :
    Stmt.HoldsList C rd σ lyR1 True kret ∧ σ (.n 7) = gen ^ (2 * j) ∧
      σ (.n 10) = gen ^ (2 * j + sh) ∧ σ (.n 16) = σ (.n 4) * gen ^ (17 * (2 * j + sh)) ∧
      σ (.n 50) = s.squeeze.1 ∧ σ (.n 51) = row ∧ σ (.n 52) = pos ∧
      σ (.n 53) = σ (.n 5) * pos ∧ σ (.n 62) = half ∧ σ (.n 63) = parity ∧
      σ (.n 65) = 1 + half ∧ σ (.n 66) = 1 ∧ σ (.n 27) = 0 ∧ σ (.n 28) = 0 ∧
      σ (.n 29) = 0 ∧ σ (.n 30) = 0 := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  obtain ⟨hcl, hcan, hpl, hcap, hrate, hcur, hvl, hval, hrow, -, -, hpos, hhalf, hpar⟩ := hS
  set L := 2 * j + sh with hL
  have m7 := good_mul (g 0 (.mul (.n 7) (.n 0) (.n 0)) (by decide +kernel)) (by omega) (by omega)
  have m8 := good_mul (g 1 (.mul (.n 8) (.n 2) (.n 3)) (by decide +kernel)) (by omega) (by omega)
  rw [← m8] at hsh
  obtain ⟨e9, l9⟩ := good_read (g 2 (.load (.n 9) (.n 8) 0) (by decide +kernel))
    (by decide +kernel) hsh
  have m10 := good_mul (g 3 (.mul (.n 10) (.n 7) (.n 9)) (by decide +kernel)) (by omega) (by omega)
  have m11 := good_mul (g 4 (.mul (.n 11) (.n 10) (.n 10)) (by decide +kernel)) (by omega) (by omega)
  have m12 := good_mul (g 5 (.mul (.n 12) (.n 11) (.n 11)) (by decide +kernel)) (by omega)
    (by omega)
  have m13 := good_mul (g 6 (.mul (.n 13) (.n 12) (.n 12)) (by decide +kernel)) (by omega)
    (by omega)
  have m14 := good_mul (g 7 (.mul (.n 14) (.n 13) (.n 13)) (by decide +kernel)) (by omega)
    (by omega)
  have m15 := good_mul (g 8 (.mul (.n 15) (.n 14) (.n 10)) (by decide +kernel)) (by omega) (by omega)
  have m16 := good_mul (g 9 (.mul (.n 16) (.n 4) (.n 15)) (by decide +kernel)) (by omega) (by omega)
  have e7 : σ (.n 7) = gen ^ (2 * j) := by rw [m7, hx, ← pow_add]; ring_nf
  have e10 : σ (.n 10) = gen ^ L := by rw [m10, e7, e9, ← pow_add]
  have e16 : σ (.n 16) = σ (.n 4) * gen ^ (17 * L) := by
    rw [m16, m15, m14, m13, m12, m11, e10, ← pow_add, ← pow_add, ← pow_add, ← pow_add]; ring_nf
  have ld : ∀ k w, LoadHolds rd (σ (.n 16)) k w ↔ LoadHolds rd (σ (.n 4)) (17 * L + k) w := by
    intro k w; rw [e16, tb_loadHolds_mul_gen_pow]
  -- the slot's capacity and waiting cells
  have gcap := good_slice hG 10 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (17 + k)) (.n 16) k)) (by decide +kernel) (by decide +kernel)
  have kcap : ∀ k < 5, some (17 + k, 16, k) ∉ lyS.map loadKey := by decide +kernel
  have rcap : ∀ k < 5, σ (.n (17 + k)) = s.cap.getD k 0 ∧
      LoadHolds rd (σ (.n 16)) k (σ (.n (17 + k))) := fun k hk =>
    good_readS (gcap _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (kcap k hk)
      ((ld k _).mpr (hcap k hk))
  have grate := good_slice hG 15 ((List.range 4).map fun k ↦
    Stmt.atom (.load (.n (22 + k)) (.n 16) (13 + k))) (by decide +kernel) (by decide +kernel)
  have krate : ∀ k < 4, some (22 + k, 16, 13 + k) ∉ lyS.map loadKey := by decide +kernel
  have rrate : ∀ k < 4, σ (.n (22 + k)) = (rateOf s.pend).getD k 0 ∧
      LoadHolds rd (σ (.n 16)) (13 + k) (σ (.n (22 + k))) := fun k hk =>
    good_readS (grate _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (krate k hk)
      ((ld _ _).mpr (by rw [← Nat.add_assoc]; exact hrate k hk))
  have c26 : σ (.n 26) = word 1 0 0 := g 19 (.const (.n 26) (word 1 0 0)) (by decide +kernel)
  have c27 : σ (.n 27) = word 0 0 0 := g 20 (.const (.n 27) (word 0 0 0)) (by decide +kernel)
  have c28 : σ (.n 28) = word 0 0 0 := g 21 (.const (.n 28) (word 0 0 0)) (by decide +kernel)
  have c29 : σ (.n 29) = word 0 0 0 := g 22 (.const (.n 29) (word 0 0 0)) (by decide +kernel)
  have c30 : σ (.n 30) = word 0 0 0 := g 23 (.const (.n 30) (word 0 0 0)) (by decide +kernel)
  rw [tb_word_zero] at c27 c28 c29 c30
  -- the combiner's permutation
  have hrl : (rateOf s.pend).length = 8 := by simp [rateOf]
  have hins : (([.n 22, .n 23, .n 24, .n 25, .n 27, .n 28, .n 29, .n 30] ++
      (List.range 5).map fun k ↦ V.n (17 + k)) : List V).map σ = rateOf s.pend ++ s.cap := by
    rw [tb_eq_map_getD hrl, tb_eq_map_getD hcl]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.cons.injEq, and_true]
    refine ⟨(rrate 0 (by omega)).1, (rrate 1 (by omega)).1, (rrate 2 (by omega)).1,
      (rrate 3 (by omega)).1, ?_, ?_, ?_, ?_, (rcap 0 (by omega)).1, (rcap 1 (by omega)).1,
      (rcap 2 (by omega)).1, (rcap 3 (by omega)).1, (rcap 4 (by omega)).1⟩
    · rw [c27, rateOf_getD_four (by omega) (by omega) (by omega)]
    · rw [c28, rateOf_getD_four (by omega) (by omega) (by omega)]
    · rw [c29, rateOf_getD_four (by omega) (by omega) (by omega)]
    · rw [c30, rateOf_getD_four (by omega) (by omega) (by omega)]
  have hcanI : AllCanonical (rateOf s.pend ++ s.cap) := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact rateOf_canonical (by omega) c hc
    · exact hcan c hc
  obtain ⟨k24, hP, -⟩ := lyc_keccak (g 24 (.keccak ([.n 22, .n 23, .n 24, .n 25, .n 27, .n 28,
    .n 29, .n 30] ++ (List.range 5).map fun k ↦ .n (17 + k)) (lyOuts 31) false false)
    (by decide +kernel)) (by rw [hins]; exact hcanI)
  rw [hins] at hP
  -- the combiner
  have hco := challengeT_good (good_slice hG 25 (challengeT (.n 31) (.n 32) 44) (by decide +kernel)
    (by decide +kernel)) (by rw [hP 1 (by omega)]; exact cellsOfState_canonical _ _ _)
  have e50 : σ (.n 50) = s.squeeze.1 :=
    challengeT_value hco (hP 0 (by omega)) (hP 1 (by omega))
  -- the row, the position, the first record
  obtain ⟨e51, l51⟩ := good_read (g 33 (.load (.n 51) (.n 16) 9) (by decide +kernel))
    (by decide +kernel) ((ld 9 _).mpr hrow)
  obtain ⟨e52, l52⟩ := good_read (g 34 (.load (.n 52) (.n 16) 10) (by decide +kernel))
    (by decide +kernel) ((ld 10 _).mpr hpos)
  have m53 := good_mul (g 35 (.mul (.n 53) (.n 5) (.n 52)) (by decide +kernel)) (by omega)
    (by omega)
  rw [e52] at m53
  have s38 : ∀ k < 5, LoadHolds rd (σ (.n 53)) (862 * k) (σ (.n (39 + k))) := by
    intro k hk
    have := tbCapAt_getD hc0 hk
    rw [show 0 + k * gkCap = 862 * k by unfold gkCap; ring] at this
    rw [m53, show 39 + k = 31 + (8 + k) by omega, hP (8 + k) (by omega)]
    rwa [Fs.squeeze, capOf_getD _ hk] at this
  obtain ⟨e54, l54⟩ := good_read (g 41 (.load (.n 54) (.n 16) 5) (by decide +kernel))
    (by decide +kernel) ((ld 5 _).mpr hcur)
  have s53 : LoadHolds rd (σ (.n 53)) 4310 (σ (.n 54)) := by rw [m53, e54]; exact hu0
  obtain ⟨e55, l55⟩ := good_read (g 43 (.load (.n 55) (.n 16) 6) (by decide +kernel))
    (by decide +kernel) ((ld 6 _).mpr (hval 0 (by omega)))
  obtain ⟨e56, l56⟩ := good_read (g 44 (.load (.n 56) (.n 16) 7) (by decide +kernel))
    (by decide +kernel) ((ld 7 _).mpr (hval 1 (by omega)))
  obtain ⟨e57, l57⟩ := good_read (g 45 (.load (.n 57) (.n 16) 8) (by decide +kernel))
    (by decide +kernel) ((ld 8 _).mpr (hval 2 (by omega)))
  have m58 := good_mul (g 46 (.mul (.n 58) (.n 50) (.n 57)) (by decide +kernel)) (by omega)
    (by omega)
  have a59 : σ (.n 59) = σ (.n 56) + σ (.n 58) := g 47 (.add (.n 59) (.n 56) (.n 58))
    (by decide +kernel)
  have m60 := good_mul (g 48 (.mul (.n 60) (.n 50) (.n 59)) (by decide +kernel)) (by omega)
    (by omega)
  have a61 : σ (.n 61) = σ (.n 55) + σ (.n 60) := g 49 (.add (.n 61) (.n 55) (.n 60))
    (by decide +kernel)
  have e61 : σ (.n 61) = polyEval st.values s.squeeze.1 := by
    obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
      match st.values, hvl with
      | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
    rw [a61, m60, a59, m58, e55, e56, e57, e50, hv3]
    simp only [polyEval, List.foldr, List.getD_cons_zero, List.getD_cons_succ]
    ring
  have s60 : LoadHolds rd (σ (.n 53)) 5172 (σ (.n 61)) := by rw [m53, e61]; exact hl0
  obtain ⟨e62, l62⟩ := good_read (g 51 (.load (.n 62) (.n 16) 11) (by decide +kernel))
    (by decide +kernel) ((ld 11 _).mpr hhalf)
  obtain ⟨e63, l63⟩ := good_read (g 52 (.load (.n 63) (.n 16) 12) (by decide +kernel))
    (by decide +kernel) ((ld 12 _).mpr hpar)
  have c64 : σ (.n 64) = word 1 0 0 := g 53 (.const (.n 64) (word 1 0 0)) (by decide +kernel)
  have a65 : σ (.n 65) = σ (.n 64) + σ (.n 62) := g 54 (.add (.n 65) (.n 64) (.n 62))
    (by decide +kernel)
  have c66 : σ (.n 66) = word 1 0 0 := g 55 (.const (.n 66) (word 1 0 0)) (by decide +kernel)
  rw [tb_word_one] at c64 c66
  refine ⟨?_, e7, e10, e16, e50, e51, e52, m53, e62, e63, by rw [a65, c64, e62], c66, c27, c28,
    c29, c30⟩
  -- the region holds
  unfold lyR1
  repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨m7, m8, l9, m10, m11, m12, m13, m14, m15, m16⟩
  · exact (tb_holdsList_mapAtoms 5 _).mpr fun k hk => (rcap k hk).2
  · exact (tb_holdsList_mapAtoms 4 _).mpr fun k hk => (rrate k hk).2
  · simp only [keccakA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨c26, by rw [c27, tb_word_zero], by rw [c28, tb_word_zero], by rw [c29, tb_word_zero],
      by rw [c30, tb_word_zero], k24⟩
  · exact (holds_challengeT _ _ _ _ _).mpr ⟨hco, trivial⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨l51, l52, by rw [m53, e52]⟩
  · exact (tb_holdsList_mapAtoms 5 _).mpr fun k hk => s38 k hk
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨l54, s53, l55, l56, l57, m58, a59, m60, a61, s60, l62, l63, by rw [c64, tb_word_one],
      a65, by rw [c66, tb_word_one]⟩

theorem tb_isInK_one : IsInK (1 : E) := by simpa using tb_gen_pow_isInK 0

/-- **The rounds**: `__loop36` (`8·(j/4)` rounds), `gkr_rounds__L{2r}` at `r = j % 4` (the
dispatch on `parity = g^r`), and `gkr_rounds__L1` at an odd depth, each from its record, when the
records hold every run of consecutive rounds. -/
theorem lyc_rounds (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {j sh : ℕ}
    (hj : j < 2 ^ 30) (hsh2 : sh < 2)
    (e7 : σ (.n 7) = gen ^ (2 * j)) (e10 : σ (.n 10) = gen ^ (2 * j + sh))
    (e62 : σ (.n 62) = gen ^ (j / 4)) (e63 : σ (.n 63) = gen ^ (j % 4))
    (e65 : σ (.n 65) = 1 + gen ^ (j / 4)) (e66 : σ (.n 66) = 1)
    (hT : ∀ a k, a + k ≤ 2 * j + sh →
      TbGkrRoundsOut k rd (σ (.n 53) * gen ^ a) (σ (.n 51) * gen ^ a)) :
    Stmt.HoldsList (coreProgram.Rel rd) rd σ lyR2 True kret := by
  have m67 := good_mul (ly_good hG 57 (.mul (.n 67) (.n 62) (.n 62)) (by decide +kernel))
    (by omega) (by omega)
  have m68 := good_mul (ly_good hG 58 (.mul (.n 68) (.n 67) (.n 67)) (by decide +kernel))
    (by omega) (by omega)
  have m69 := good_mul (ly_good hG 59 (.mul (.n 69) (.n 68) (.n 68)) (by decide +kernel))
    (by omega) (by omega)
  have m70 := good_mul (ly_good hG 60 (.mul (.n 70) (.n 53) (.n 69)) (by decide +kernel))
    (by omega) (by omega)
  have m71 := good_mul (ly_good hG 61 (.mul (.n 71) (.n 51) (.n 69)) (by decide +kernel))
    (by omega) (by omega)
  have e69 : σ (.n 69) = gen ^ (8 * (j / 4)) := by
    rw [m69, m68, m67, e62, ← pow_add, ← pow_add, ← pow_add]; ring_nf
  refine holdsList_of_vsh lyR2 (by decide +kernel) (fun s hs => ?_) trivial
  simp only [lyR2, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- `__loop36`
    refine ⟨by rw [e65]; exact tb_isInK_add tb_isInK_one (tb_gen_pow_isInK _), fun hne => ?_⟩
    have hpos : 0 < j / 4 := by
      rcases Nat.eq_zero_or_pos (j / 4) with h0 | h0
      · rw [e65, h0, pow_zero, e_add_self] at hne; exact absurd rfl hne
      · exact h0
    simp only [List.map_cons, List.map_nil, e66, e62]
    exact l29_complete hpos (by omega) fun i hi => hT (8 * i) 8 (by omega)
  · exact m67
  · exact m68
  · exact m69
  · exact m70
  · exact m71
  · -- `gkr_rounds__L{2r}`, `r = j % 4`
    have gd := good_slice hG 62 [.dispatch (.n 63)
      ["gkr_rounds__L0", "gkr_rounds__L2", "gkr_rounds__L4", "gkr_rounds__L6"] [.n 70, .n 71]
      [.n 72]] (by decide +kernel) rfl _ List.mem_cons_self
    have e72 : σ (.n 72) = 0 := gd (.n 72) List.mem_cons_self
    have hr : j % 4 < 4 := Nat.mod_lt _ (by omega)
    refine ⟨j % 4, by simpa using hr, by rw [e63, gen_pow_eq_ofK], ?_⟩
    simp only [List.map_cons, List.map_nil, e72]
    rw [m70, m71, e69]
    have hR := hT (8 * (j / 4)) (2 * (j % 4)) (by omega)
    have hr4 : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega
    rcases hr4 with h | h | h | h <;> simp only [h, List.getElem_cons_zero,
      List.getElem_cons_succ] <;> rw [h] at hR
    · exact (gkr_rounds_holds.2 rd _ _).mpr rfl
    · exact (gkr_rounds_holds.1 2 (by simp [gkrRoundsCounts]) rd _ _).mpr ⟨rfl, hR⟩
    · exact (gkr_rounds_holds.1 4 (by simp [gkrRoundsCounts]) rd _ _).mpr ⟨rfl, hR⟩
    · exact (gkr_rounds_holds.1 6 (by simp [gkrRoundsCounts]) rd _ _).mpr ⟨rfl, hR⟩
  · exact ly_good hG 63 (.add (.n 73) (.n 10) (.n 7)) (by decide +kernel)
  · -- `gkr_rounds__L1` at an odd depth
    have gb := good_ite hG 64 (.n 73) [] [.atom (.mul (.n 74) (.n 53) (.n 7)),
      .atom (.mul (.n 75) (.n 51) (.n 7)), .call "gkr_rounds__L1" [.n 74, .n 75] [.n 76]]
      (by decide +kernel)
    have a73 : σ (.n 73) = σ (.n 10) + σ (.n 7) :=
      ly_good hG 63 (.add (.n 73) (.n 10) (.n 7)) (by decide +kernel)
    refine ⟨by rw [a73, e10, e7]; exact tb_isInK_add (tb_gen_pow_isInK _) (tb_gen_pow_isInK _),
      fun _ s hs => absurd hs (by simp), fun hne s hs => ?_⟩
    have hsh1 : sh = 1 := by
      by_contra h
      rw [a73, e10, e7, show sh = 0 by omega, Nat.add_zero, e_add_self] at hne
      exact hne rfl
    have m74 := good_mulS (gb (.atom (.mul (.n 74) (.n 53) (.n 7))) (by simp)) (by omega) (by omega)
    have m75 := good_mulS (gb (.atom (.mul (.n 75) (.n 51) (.n 7))) (by simp)) (by omega) (by omega)
    have e76 : σ (.n 76) = 0 :=
      gb (.call "gkr_rounds__L1" [.n 74, .n 75] [.n 76]) (by simp) (.n 76) List.mem_cons_self
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact m74
    · exact m75
    · show coreProgram.Rel rd "gkr_rounds__L1" [σ (.n 74), σ (.n 75)] [σ (.n 76)]
      rw [m74, m75, e7, e76]
      exact (gkr_rounds_holds.1 1 (by simp [gkrRoundsCounts]) rd _ _).mpr ⟨rfl, hT (2 * j) 1 (by omega)⟩

/-- **The last record**: its capacity, cursor and claim, at `rec·g^L`. -/
theorem lyc_last (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {L : ℕ}
    (e10 : σ (.n 10) = gen ^ L) {cap : List E} {cur claim : E}
    (hc : TbCapAt rd (σ (.n 53) * gen ^ L) 0 gkCap cap)
    (hu : LoadHolds rd (σ (.n 53) * gen ^ L) (5 * gkCap) cur)
    (hl : LoadHolds rd (σ (.n 53) * gen ^ L) (6 * gkCap) claim) :
    Stmt.HoldsList C rd σ lyR3 True kret ∧ (∀ k < 5, σ (.n (78 + k)) = cap.getD k 0) ∧
      σ (.n 83) = cur ∧ σ (.n 84) = claim := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have m77 := good_mul (g 65 (.mul (.n 77) (.n 53) (.n 10)) (by decide +kernel)) (by omega)
    (by omega)
  rw [e10] at m77
  have gc := good_slice hG 66 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (78 + k)) (.n 77) (862 * k))) (by decide +kernel) (by decide +kernel)
  have kc : ∀ k < 5, some (78 + k, 77, 862 * k) ∉ lyS.map loadKey := by decide +kernel
  have rc : ∀ k < 5, σ (.n (78 + k)) = cap.getD k 0 ∧
      LoadHolds rd (σ (.n 77)) (862 * k) (σ (.n (78 + k))) := fun k hk =>
    good_readS (gc _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (kc k hk)
      (by have := tbCapAt_getD hc hk
          rwa [m77, show 862 * k = 0 + k * gkCap by unfold gkCap; ring])
  obtain ⟨e83, l83⟩ := good_read (g 71 (.load (.n 83) (.n 77) 4310) (by decide +kernel))
    (by decide +kernel) (by rw [m77]; exact hu)
  obtain ⟨e84, l84⟩ := good_read (g 72 (.load (.n 84) (.n 77) 5172) (by decide +kernel))
    (by decide +kernel) (by rw [m77]; exact hl)
  refine ⟨?_, fun k hk => (rc k hk).1, e83, e84⟩
  unfold lyR3
  repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    rw [m77, e10]
  · exact (tb_holdsList_mapAtoms 5 _).mpr fun k hk => (rc k hk).2
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨l83, l84⟩

theorem lyEvT_noRet (i : ℕ) : Stmt.noRetList (lyEvT i) = true := by
  simp [lyEvT, fsNextT, fsPackT, Stmt.noRetList, Stmt.noRet]

/-- The rate cells of four children read are canonical. -/
theorem lyRate_canonical {m : ℕ}
    (hc : ∀ i < 4, (σ (.n (lyEv (4 * m + i) + 7)), σ (.n (lyEv (4 * m + i) + 9))) =
      Keccak.scalarCells (σ (.n (lyEv (4 * m + i)))) dsObserve) :
    AllCanonical ((lyRate m).map σ) := by
  intro c hc'
  simp only [lyRate, List.map_flatMap, List.mem_flatMap, List.mem_range, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hc'
  obtain ⟨i, hi, rfl | rfl⟩ := hc'
  · rw [show σ (.n (lyEv (4 * m + i) + 7)) = _ from (Prod.ext_iff.mp (hc i hi)).1]
    exact (scalarCells_canonical _ _).1
  · rw [show σ (.n (lyEv (4 * m + i) + 9)) = _ from (Prod.ext_iff.mp (hc i hi)).2]
    exact (scalarCells_canonical _ _).2

/-- **The children**: the twelve words at the last record's cursor, read, and absorbed four at a
time over the last record's capacity. -/
theorem lyc_children (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {cap : List E}
    (hcl : cap.length = 5) (hcan : AllCanonical cap)
    (e78 : ∀ k < 5, σ (.n (78 + k)) = cap.getD k 0) {ch : List E} (hch : ch.length = 12)
    (hr : TbReadsAt rd (σ (.n 83)) ch) :
    Stmt.HoldsList C rd σ lyR4 True kret ∧
      (∀ i < 12, σ (.n (lyEv i)) = ch.getD i 0 ∧ σ (.n (lyEv i + 10)) = σ (.n (lyEv i)) ∧
        FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve ∧
        (σ (.n (lyEv i + 7)), σ (.n (lyEv i + 9))) =
          Keccak.scalarCells (σ (.n (lyEv i))) dsObserve) ∧
      (lyCap 186).map σ = capOf (Fs.perm ⟨capOf (Fs.perm ⟨cap, (lyCh σ 0).map (·, dsObserve)⟩),
        (lyCh σ 1).map (·, dsObserve)⟩) := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have hni : ∀ i < 12, (lyEvT i).all notIteB = true := by decide +kernel
  have hk : ∀ i < 12, some (lyEv i, 83, i) ∉ lyS.map loadKey := by decide +kernel
  have EV : ∀ i < 12, Stmt.HoldsList C rd σ (lyEvT i) True kret ∧
      σ (.n (lyEv i)) = ch.getD i 0 ∧ σ (.n (lyEv i + 10)) = σ (.n (lyEv i)) ∧
      FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve ∧
      (σ (.n (lyEv i + 7)), σ (.n (lyEv i + 9))) =
        Keccak.scalarCells (σ (.n (lyEv i))) dsObserve := by
    intro i hi
    have gb := good_slice hG (lyPos i) (lyEvT i) (lyEvs_check i hi) (hni i hi)
    have hl : LoadHolds rd (σ (.n 83)) i (ch.getD i 0) := by
      have := hr i (by rw [hch]; exact hi)
      rwa [← List.getD_eq_getElem _ 0] at this
    obtain ⟨e0, hcells, hfs⟩ := fsNextT_good (C := C) (kret := kret)
      (fun s hs => gb s (List.mem_append_left _ hs)) (hk i hi) hl
    have cp : σ (.n (lyEv i + 10)) = σ (.n (lyEv i)) :=
      gb (.atom (.copy (.n (lyEv i + 10)) (.n (lyEv i)))) (by simp [lyEvT])
    have hok := ((holds_fsNextT _ _ _ _ _).mp hfs).1.2
    refine ⟨?_, e0, cp, hok, by rw [e0]; exact hcells⟩
    unfold lyEvT
    rw [tb_holdsList_append_noRet (by simp [fsNextT, fsPackT, Stmt.noRetList, Stmt.noRet])]
    refine ⟨hfs, ?_⟩
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact cp
  have hp : ∀ m < 3, ∀ i < 4,
      FsPackOk σ (.n (lyEv (4 * m + i))) (lyEv (4 * m + i) + 1) dsObserve :=
    fun m hm i hi => (EV (4 * m + i) (by omega)).2.2.2.1
  have hc : ∀ m < 3, ∀ i < 4, (σ (.n (lyEv (4 * m + i) + 7)), σ (.n (lyEv (4 * m + i) + 9))) =
      Keccak.scalarCells (σ (.n (lyEv (4 * m + i)))) dsObserve :=
    fun m hm i hi => (EV (4 * m + i) (by omega)).2.2.2.2
  -- the first four children's permutation
  have hS0 : ((List.range 5).map fun k ↦ V.n (78 + k)).map σ = cap := by
    rw [tb_eq_map_getD hcl, List.map_map]
    apply List.map_congr_left
    intro k hk'
    exact e78 k (List.mem_range.mp hk')
  have hcan0 : AllCanonical ((lyRate 0 ++ (List.range 5).map fun k ↦ V.n (78 + k)).map σ) := by
    rw [List.map_append, hS0]
    intro c hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact lyRate_canonical (hc 0 (by omega)) c hc'
    · exact hcan c hc'
  obtain ⟨k113, -⟩ := keccak_good (g 113 (.keccak (lyRate 0 ++ (List.range 5).map fun k ↦
    .n (78 + k)) (lyOuts 129) false false) (by decide +kernel)) hcan0
  obtain ⟨-, B0⟩ := ly_perm_block (hp 0 (by omega)) k113
  rw [hS0] at B0
  have hcan1 : AllCanonical ((lyRate 1 ++ lyCap 129).map σ) := by
    rw [List.map_append, B0]
    intro c hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact lyRate_canonical (hc 1 (by omega)) c hc'
    · exact tb_capOf_canonical _ c hc'
  obtain ⟨k154, -⟩ := keccak_good (g 154 (.keccak (lyRate 1 ++ lyCap 129) (lyOuts 186) false false)
    (by decide +kernel)) hcan1
  obtain ⟨-, B1⟩ := ly_perm_block (hp 1 (by omega)) k154
  rw [B0] at B1
  refine ⟨?_, fun i hi => (EV i hi).2, B1⟩
  unfold lyR4
  repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact (tb_holdsList_flatten_range 4 _ lyEvT_noRet).mpr fun i hi => (EV i (by omega)).1
  · simp only [keccakA, Stmt.HoldsList, Stmt.Holds, and_true]; exact k113
  · exact (tb_holdsList_flatten_range 4 _ fun i => lyEvT_noRet _).mpr
      fun i hi => (EV (4 + i) (by omega)).1
  · simp only [keccakA, Stmt.HoldsList, Stmt.Holds, and_true]; exact k154
  · exact (tb_holdsList_flatten_range 4 _ fun i => lyEvT_noRet _).mpr
      fun i hi => (EV (8 + i) (by omega)).1

/-- **The check and the two new coordinates**: the children's products check the last claim at
the combiner; the sponge after the twelve children squeezes the two coordinates and leaves the
capacity at `283 ..`. -/
theorem lyc_check (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {P1 : KeccakState}
    (cp : ∀ i < 12, σ (.n (lyEv i + 10)) = σ (.n (lyEv i)))
    (hpk : ∀ i < 12, FsPackOk σ (.n (lyEv i)) (lyEv i + 1) dsObserve)
    (hcells : ∀ i < 12, (σ (.n (lyEv i + 7)), σ (.n (lyEv i + 9))) =
      Keccak.scalarCells (σ (.n (lyEv i))) dsObserve)
    (hB1 : (lyCap 186).map σ = capOf P1)
    (hcheck : σ (.n 84) =
      polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 50)))
    (c27 : σ (.n 27) = 0) (c28 : σ (.n 28) = 0) (c29 : σ (.n 29) = 0) (c30 : σ (.n 30) = 0) :
    Stmt.HoldsList C rd σ lyR5 True kret ∧
      σ (.n 278) = challengeOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩) ∧
      σ (.n 298) = challengeOf (permOf (rateOf [] ++
        capOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩))) ∧
      ((List.range 5).map fun k ↦ σ (.n (287 + k))) = capOf (permOf (rateOf [] ++
        capOf (Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩))) := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  -- the check
  have m243 := good_mul (g 195 (.mul (.n 243) (.n 209) (.n 220)) (by decide +kernel)) (by omega)
    (by omega)
  have m244 := good_mul (g 196 (.mul (.n 244) (.n 243) (.n 231)) (by decide +kernel)) (by omega)
    (by omega)
  have m245 := good_mul (g 197 (.mul (.n 245) (.n 244) (.n 242)) (by decide +kernel)) (by omega)
    (by omega)
  have c246 : σ (.n 246) = word 0 0 0 := g 198 (.const (.n 246) (word 0 0 0)) (by decide +kernel)
  have m247 := good_mul (g 199 (.mul (.n 247) (.n 50) (.n 246)) (by decide +kernel)) (by omega)
    (by omega)
  have a248 : σ (.n 248) = σ (.n 245) + σ (.n 247) :=
    g 200 (.add (.n 248) (.n 245) (.n 247)) (by decide +kernel)
  have m249 := good_mul (g 201 (.mul (.n 249) (.n 152) (.n 163)) (by decide +kernel)) (by omega)
    (by omega)
  have m250 := good_mul (g 202 (.mul (.n 250) (.n 249) (.n 174)) (by decide +kernel)) (by omega)
    (by omega)
  have m251 := good_mul (g 203 (.mul (.n 251) (.n 250) (.n 185)) (by decide +kernel)) (by omega)
    (by omega)
  have m252 := good_mul (g 204 (.mul (.n 252) (.n 50) (.n 248)) (by decide +kernel)) (by omega)
    (by omega)
  have a253 : σ (.n 253) = σ (.n 251) + σ (.n 252) :=
    g 205 (.add (.n 253) (.n 251) (.n 252)) (by decide +kernel)
  have m254 := good_mul (g 206 (.mul (.n 254) (.n 95) (.n 106)) (by decide +kernel)) (by omega)
    (by omega)
  have m255 := good_mul (g 207 (.mul (.n 255) (.n 254) (.n 117)) (by decide +kernel)) (by omega)
    (by omega)
  have m256 := good_mul (g 208 (.mul (.n 256) (.n 255) (.n 128)) (by decide +kernel)) (by omega)
    (by omega)
  have m257 := good_mul (g 209 (.mul (.n 257) (.n 50) (.n 253)) (by decide +kernel)) (by omega)
    (by omega)
  have a258 : σ (.n 258) = σ (.n 256) + σ (.n 257) :=
    g 210 (.add (.n 258) (.n 256) (.n 257)) (by decide +kernel)
  have e258 : σ (.n 258) =
      polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 50)) := by
    rw [a258, m257, a253, m252, a248, m247, c246, tb_word_zero, m245, m244, m243, m251, m250, m249,
      m256, m255, m254,
      show σ (.n 95) = σ (.n 85) from cp 0 (by omega), show σ (.n 106) = σ (.n 96) from cp 1 (by omega),
      show σ (.n 117) = σ (.n 107) from cp 2 (by omega),
      show σ (.n 128) = σ (.n 118) from cp 3 (by omega),
      show σ (.n 152) = σ (.n 142) from cp 4 (by omega),
      show σ (.n 163) = σ (.n 153) from cp 5 (by omega),
      show σ (.n 174) = σ (.n 164) from cp 6 (by omega),
      show σ (.n 185) = σ (.n 175) from cp 7 (by omega),
      show σ (.n 209) = σ (.n 199) from cp 8 (by omega),
      show σ (.n 220) = σ (.n 210) from cp 9 (by omega),
      show σ (.n 231) = σ (.n 221) from cp 10 (by omega),
      show σ (.n 242) = σ (.n 232) from cp 11 (by omega)]
    have hc0 : lyCh σ 0 = [σ (.n 85), σ (.n 96), σ (.n 107), σ (.n 118)] := by rw [lyCh_eq]; rfl
    have hc1 : lyCh σ 1 = [σ (.n 142), σ (.n 153), σ (.n 164), σ (.n 175)] := by rw [lyCh_eq]; rfl
    have hc2 : lyCh σ 2 = [σ (.n 199), σ (.n 210), σ (.n 221), σ (.n 232)] := by rw [lyCh_eq]; rfl
    rw [hc0, hc1, hc2]
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  -- the third block's permutation
  have hp2 : ∀ i < 4, FsPackOk σ (.n (lyEv (4 * 2 + i))) (lyEv (4 * 2 + i) + 1) dsObserve :=
    fun i hi => hpk (4 * 2 + i) (by omega)
  have hcan2 : AllCanonical ((lyRate 2 ++ lyCap 186).map σ) := by
    rw [List.map_append, hB1]
    intro c hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact lyRate_canonical (fun i hi => hcells (4 * 2 + i) (by omega)) c hc'
    · exact tb_capOf_canonical _ c hc'
  obtain ⟨k212, -⟩ := keccak_good (g 212 (.keccak (lyRate 2 ++ lyCap 186) (lyOuts 259) false false)
    (by decide +kernel)) hcan2
  obtain ⟨P2, B2⟩ := ly_perm_block hp2 k212
  rw [hB1] at P2 B2
  set Q := Fs.perm ⟨capOf P1, (lyCh σ 2).map (·, dsObserve)⟩ with hQ
  -- the first coordinate
  have hco2 := challengeT_good (good_slice hG 213 (challengeT (.n 259) (.n 260) 272)
    (by decide +kernel) (by decide +kernel))
    (by rw [P2 1 (by omega)]; exact cellsOfState_canonical _ _ _)
  have e278 : σ (.n 278) = challengeOf Q := challengeT_value hco2 (P2 0 (by omega)) (P2 1 (by omega))
  -- the second
  have hz : (([.n 27, .n 27, .n 27, .n 27, .n 27, .n 28, .n 29, .n 30] ++ lyCap 259 : List V).map σ) =
      rateOf [] ++ capOf Q := by
    rw [List.map_append, B2, rateOf_eq_cells [] (by simp)]
    simp only [List.map_cons, List.map_nil, c27, c28, c29, c30]
    rfl
  have hcan3 : AllCanonical (rateOf [] ++ capOf Q) := by
    intro c hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact rateOf_canonical (by simp) c hc'
    · exact tb_capOf_canonical _ c hc'
  obtain ⟨k221, P3, B3⟩ := lyc_keccak (g 221 (.keccak ([.n 27, .n 27, .n 27, .n 27, .n 27, .n 28,
    .n 29, .n 30] ++ lyCap 259) (lyOuts 279) false false) (by decide +kernel))
    (by rw [hz]; exact hcan3)
  rw [hz] at P3 B3
  have hco3 := challengeT_good (good_slice hG 222 (challengeT (.n 279) (.n 280) 292)
    (by decide +kernel) (by decide +kernel))
    (by rw [P3 1 (by omega)]; exact cellsOfState_canonical _ _ _)
  have e298 : σ (.n 298) = challengeOf (permOf (rateOf [] ++ capOf Q)) :=
    challengeT_value hco3 (P3 0 (by omega)) (P3 1 (by omega))
  refine ⟨?_, e278, e298, ?_⟩
  · unfold lyR5
    repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp only [keccakA, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
      exact ⟨m243, m244, m245, c246, m247, a248, m249, m250, m251, m252, a253, m254, m255, m256,
        m257, a258, by rw [hcheck, ← e258, e_add_self], k212⟩
    · exact (holds_challengeT _ _ _ _ _).mpr ⟨hco2, trivial⟩
    · simp only [keccakA, Stmt.HoldsList, Stmt.Holds, and_true]; exact k221
    · exact (holds_challengeT _ _ _ _ _).mpr ⟨hco3, trivial⟩
  · rw [← B3]
    simp [lyCap]

/-- A side's new value on its equations: its four children's multilinear value at the two new
coordinates, stored at `off`. -/
theorem lyc_val (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s) {t b off : ℕ} (n : ℕ)
    (heq : tbStmtsEqb (lyVal t b off) ((lyPre.drop n).take (lyVal t b off).length) = true)
    (ht : t < 3) (hb : 298 < b) (cp : ∀ i < 12, σ (.n (lyEv i + 10)) = σ (.n (lyEv i)))
    (hl : LoadHolds rd (σ (.n 16)) off (multilinearEval (lyCh σ t) [σ (.n 278), σ (.n 298)])) :
    Stmt.HoldsList C rd σ (lyVal t b off) True kret := by
  have gb := good_slice hG n (lyVal t b off) heq (by simp [lyVal, notIteB])
  have he : ∀ i < 4, lyEv (4 * t + i) + 10 < b := by
    intro i hi; unfold lyEv; split_ifs <;> omega
  have a0 : σ (.n b) = σ (.n (lyEv (4 * t + 0) + 10)) + σ (.n (lyEv (4 * t + 1) + 10)) :=
    gb (.atom (.add (.n b) _ _)) (by simp [lyVal])
  have m1 := good_mulS (gb (.atom (.mul (.n (b + 1)) (.n 278) (.n b))) (by simp [lyVal]))
    (by omega) (by omega)
  have a2 : σ (.n (b + 2)) = σ (.n (lyEv (4 * t + 0) + 10)) + σ (.n (b + 1)) :=
    gb (.atom (.add (.n (b + 2)) _ _)) (by simp [lyVal])
  have a3 : σ (.n (b + 3)) = σ (.n (lyEv (4 * t + 2) + 10)) + σ (.n (lyEv (4 * t + 3) + 10)) :=
    gb (.atom (.add (.n (b + 3)) _ _)) (by simp [lyVal])
  have m4 := good_mulS (gb (.atom (.mul (.n (b + 4)) (.n 278) (.n (b + 3)))) (by simp [lyVal]))
    (by omega) (by omega)
  have a5 : σ (.n (b + 5)) = σ (.n (lyEv (4 * t + 2) + 10)) + σ (.n (b + 4)) :=
    gb (.atom (.add (.n (b + 5)) _ _)) (by simp [lyVal])
  have a6 : σ (.n (b + 6)) = σ (.n (b + 2)) + σ (.n (b + 5)) :=
    gb (.atom (.add (.n (b + 6)) _ _)) (by simp [lyVal])
  have m7 := good_mulS (gb (.atom (.mul (.n (b + 7)) (.n 298) (.n (b + 6)))) (by simp [lyVal]))
    (by omega) (by omega)
  have a8 : σ (.n (b + 8)) = σ (.n (b + 2)) + σ (.n (b + 7)) :=
    gb (.atom (.add (.n (b + 8)) _ _)) (by simp [lyVal])
  have e8 : σ (.n (b + 8)) = multilinearEval (lyCh σ t) [σ (.n 278), σ (.n 298)] := by
    rw [a8, m7, a6, a5, m4, a3, a2, m1, a0, cp (4 * t + 0) (by omega), cp (4 * t + 1) (by omega),
      cp (4 * t + 2) (by omega), cp (4 * t + 3) (by omega), lyCh_eq]
    simp only [multilinearEval, List.foldl, foldPairs, List.headD]
    ring_nf
  simp only [lyVal, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
  exact ⟨a0, m1, a2, a3, m4, a5, a6, m7, a8, by rw [e8]; exact hl⟩

/-- **The next slot and the next iteration**: the stores of the slot `34` words on, and the call
at `x·g` below the bound. -/
theorem lyc_stores (hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s)
    (cp : ∀ i < 12, σ (.n (lyEv i + 10)) = σ (.n (lyEv i)))
    (s40 : LoadHolds rd (σ (.n 51)) 40 (σ (.n 278)))
    (s41 : LoadHolds rd (σ (.n 51)) 41 (σ (.n 298)))
    (s34 : ∀ k < 5, LoadHolds rd (σ (.n 16)) (34 + k) (σ (.n (287 + k))))
    (s47 : ∀ k < 4, LoadHolds rd (σ (.n 16)) (47 + k) 0)
    (s39 : LoadHolds rd (σ (.n 16)) 39 (σ (.n 83) * gen ^ 12))
    (sv : ∀ t < 3, LoadHolds rd (σ (.n 16)) (40 + t)
      (multilinearEval (lyCh σ t) [σ (.n 278), σ (.n 298)]))
    (s43 : LoadHolds rd (σ (.n 16)) 43 (σ (.n 51) * gen ^ 40))
    (s44 : LoadHolds rd (σ (.n 16)) 44 (σ (.n 52) * σ (.n 10) * gen))
    {hv pv : E} (k4 : LoadHolds rd (σ (.n 6) * σ (.n 63)) 4 hv)
    (k0 : LoadHolds rd (σ (.n 6) * σ (.n 63)) 0 pv)
    (s45 : LoadHolds rd (σ (.n 16)) 45 (σ (.n 62) * hv))
    (s46 : LoadHolds rd (σ (.n 16)) 46 pv)
    (hK : IsInK (σ (.n 0) * gen + σ (.n 1)))
    (hcall : σ (.n 0) * gen + σ (.n 1) ≠ 0 →
      C "__loop6" [σ (.n 0) * gen, σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)]
        []) :
    Stmt.HoldsList C rd σ lyR6 True kret := by
  have g := fun n a heq => ly_good (rd := rd) (σ := σ) hG n a heq
  have gz := good_slice hG 237 ((List.range 4).map fun k ↦ [Stmt.atom (.const (.n (299 + k))
    (word 0 0 0)), .atom (.load (.n (299 + k)) (.n 16) (47 + k))]).flatten (by decide +kernel)
    (by decide +kernel)
  have c303 : σ (.n 303) = word 4096 0 0 := g 245 (.const (.n 303) (word 4096 0 0))
    (by decide +kernel)
  have m304 := good_mul (g 246 (.mul (.n 304) (.n 83) (.n 303)) (by decide +kernel)) (by omega)
    (by omega)
  have c332 : σ (.n 332) = word 1099511627776 0 0 :=
    g 278 (.const (.n 332) (word 1099511627776 0 0)) (by decide +kernel)
  have m333 := good_mul (g 279 (.mul (.n 333) (.n 51) (.n 332)) (by decide +kernel)) (by omega)
    (by omega)
  have m334 := good_mul (g 281 (.mul (.n 334) (.n 52) (.n 10)) (by decide +kernel)) (by omega)
    (by omega)
  have c335 : σ (.n 335) = word 2 0 0 := g 282 (.const (.n 335) (word 2 0 0)) (by decide +kernel)
  have m336 := good_mul (g 283 (.mul (.n 336) (.n 334) (.n 335)) (by decide +kernel)) (by omega)
    (by omega)
  have m337 := good_mul (g 285 (.mul (.n 337) (.n 6) (.n 63)) (by decide +kernel)) (by omega)
    (by omega)
  obtain ⟨e338, l338⟩ := good_read (g 286 (.load (.n 338) (.n 337) 4) (by decide +kernel))
    (by decide +kernel) (by rw [m337]; exact k4)
  have m339 := good_mul (g 287 (.mul (.n 339) (.n 62) (.n 338)) (by decide +kernel)) (by omega)
    (by omega)
  have m340 := good_mul (g 289 (.mul (.n 340) (.n 6) (.n 63)) (by decide +kernel)) (by omega)
    (by omega)
  obtain ⟨e341, l341⟩ := good_read (g 290 (.load (.n 341) (.n 340) 0) (by decide +kernel))
    (by decide +kernel) (by rw [m340]; exact k0)
  have c342 : σ (.n 342) = word 2 0 0 := g 292 (.const (.n 342) (word 2 0 0)) (by decide +kernel)
  have m343 := good_mul (g 293 (.mul (.n 343) (.n 0) (.n 342)) (by decide +kernel)) (by omega)
    (by omega)
  have a344 : σ (.n 344) = σ (.n 343) + σ (.n 1) :=
    g 294 (.add (.n 344) (.n 343) (.n 1)) (by decide +kernel)
  have c345 : σ (.n 345) = word 2 0 0 := g 295 (.const (.n 345) (word 2 0 0)) (by decide +kernel)
  have m346 := good_mul (g 296 (.mul (.n 346) (.n 0) (.n 345)) (by decide +kernel)) (by omega)
    (by omega)
  have w4096 : word 4096 0 0 = gen ^ 12 := by
    rw [show (4096 : ℕ) = 2 ^ 12 by norm_num, tb_word_two_pow (by norm_num)]
  have w40 : word 1099511627776 0 0 = gen ^ 40 := by
    rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)]
  unfold lyR6
  repeat rw [tb_holdsList_append_noRet (by decide +kernel)]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨s40, s41⟩
  · exact (tb_holdsList_mapAtoms 5 _).mpr fun k hk => s34 k hk
  · refine (tb_holdsList_flatten_range 4 _ fun _ => rfl).mpr fun k hk => ?_
    have c : σ (.n (299 + k)) = word 0 0 0 :=
      gz (.atom (.const (.n (299 + k)) (word 0 0 0))) (List.mem_flatten.mpr ⟨_,
        List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, List.mem_cons_self⟩)
    rw [tb_word_zero] at c
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨by rw [c, tb_word_zero], by rw [c]; exact s47 k hk⟩
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    exact ⟨c303, m304, by rw [m304, c303, w4096]; exact s39⟩
  · exact lyc_val hG 248 (by decide +kernel) (by omega) (by omega) cp (sv 0 (by omega))
  · exact lyc_val hG 258 (by decide +kernel) (by omega) (by omega) cp (sv 1 (by omega))
  · exact lyc_val hG 268 (by decide +kernel) (by omega) (by omega) cp (sv 2 (by omega))
  · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, List.map_cons, List.map_nil]
    rw [tb_word_gen] at c335 c342 c345
    refine ⟨c332, m333, by rw [m333, c332, w40]; exact s43, m334, by rw [c335, tb_word_gen], m336,
      by rw [m336, m334, c335]; exact s44, m337, l338, m339,
      by rw [m339, e338]; exact s45, m340, l341, by rw [e341]; exact s46,
      by rw [c342, tb_word_gen], m343, a344,
      by rw [c345, tb_word_gen], m346, by rw [a344, m343, c342]; exact hK, fun hne => ?_⟩
    rw [m346, c345]
    exact hcall (by rw [a344, m343, c342] at hne; exact hne)

end Eval

end
end LeanVM.Guest.B1.Tables
